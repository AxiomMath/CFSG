module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineHyp711
public import CFSG.SignalizerFunctorTheorem.Quadratic.Independence
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

@[expose] def cjOrbit (G A : Subgroup (LGL 2 V)) : Set (Subgroup (LGL 2 V)) :=
  {B | ∃ g ∈ G, B = cj g A}

theorem mem_cjOrbit_self (G A : Subgroup (LGL 2 V)) : A ∈ cjOrbit G A := by
  refine ⟨1, G.one_mem, ?_⟩
  ext x
  simp [cj]

private theorem cj_iSup₂ (g : LGL 2 V) {ι : Type*} (s : Set ι)
    (f : ι → Subgroup (LGL 2 V)) :
    cj g (⨆ i ∈ s, f i) = ⨆ i ∈ s, cj g (f i) := by
  unfold cj
  rw [Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  rw [Subgroup.map_iSup]

private theorem normal_iSup_cjOrbit {H A : Subgroup (LGL 2 V)} (hA : A ≤ H) :
    ((⨆ B ∈ cjOrbit H A, B).subgroupOf H).Normal := by
  set N : Subgroup (LGL 2 V) := ⨆ B ∈ cjOrbit H A, B with hN
  have hNle : N ≤ H := by
    rw [hN]
    refine iSup₂_le fun B hB => ?_
    obtain ⟨y, hy, rfl⟩ := hB
    exact IndepPair.cj_le_of_mem hA hy
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNle]
  have hstep : ∀ x ∈ H, cj x N ≤ N := by
    intro x hx
    rw [hN, cj_iSup₂]
    refine iSup₂_le fun B hB => ?_
    obtain ⟨y, hy, rfl⟩ := hB
    rw [← cj_mul]
    exact le_iSup₂_of_le (cj (x * y) A) ⟨x * y, H.mul_mem hx hy, rfl⟩ le_rfl
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hstep h hh (Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩)
  · intro hy
    have hmem : h⁻¹ * (h * y * h⁻¹) * h ∈ cj h⁻¹ N :=
      Subgroup.mem_map.mpr ⟨h * y * h⁻¹, hy, by simp [MulAut.conj_apply]⟩
    have hthis := hstep h⁻¹ (H.inv_mem hh) hmem
    rwa [show h⁻¹ * (h * y * h⁻¹) * h = y from by group] at hthis

theorem exists_le_cjOrbit_assumption131 (h : Assumption131 G Γ VA i)
    {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) :
    ∃ G₁ : Subgroup (LGL 2 V), G₁ ≤ G ∧ A ≤ G₁ ∧ cjOrbit G₁ A ⊆ Γ ∧
      G₁ = (⨆ B ∈ cjOrbit G₁ A, B) ∧ Assumption131 G₁ (cjOrbit G₁ A) VA i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨G₁, hG₁P, hG₁min⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup.exists_minimal_subgroup
      (fun X : Subgroup (LGL 2 V) => A ≤ X ∧ X ≤ G ∧ pCoreOf 2 X ≤ pCoreOf 2 G)
      ⟨G, h.le_G A hA, le_rfl, le_rfl⟩
  obtain ⟨hAG₁, hG₁G, hpG₁⟩ := hG₁P
  set N : Subgroup (LGL 2 V) := ⨆ B ∈ cjOrbit G₁ A, B with hN
  have hNle : N ≤ G₁ := by
    rw [hN]
    refine iSup₂_le fun B hB => ?_
    obtain ⟨y, hy, rfl⟩ := hB
    exact IndepPair.cj_le_of_mem hAG₁ hy
  have hNnormal : (N.subgroupOf G₁).Normal := by
    rw [hN]
    exact normal_iSup_cjOrbit hAG₁
  have hpN : pCoreOf 2 N ≤ pCoreOf 2 G := by
    have hle : pCoreOf 2 N ≤ G₁ :=
      (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) N).trans hNle
    have hnorm : ((pCoreOf 2 N).subgroupOf G₁).Normal :=
      pCoreOf_subgroupOf_normal hNle hNnormal
    have hp : IsPGroup 2 (pCoreOf 2 N) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) N
    exact (CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hle hnorm hp).trans hpG₁
  have hNP : A ≤ N ∧ N ≤ G ∧ pCoreOf 2 N ≤ pCoreOf 2 G :=
    ⟨by rw [hN]; exact le_iSup₂_of_le A (mem_cjOrbit_self G₁ A) le_rfl,
      hNle.trans hG₁G, hpN⟩
  have hNeq : G₁ = N := (hG₁min N hNP hNle).symm
  have hsub : cjOrbit G₁ A ⊆ Γ := by
    rintro B ⟨y, hy, rfl⟩
    exact h.invariant A hA y (hG₁G hy)
  refine ⟨G₁, hG₁G, hAG₁, hsub, hNeq.trans hN, ?_⟩
  refine
    { pos_i := h.pos_i
      le_G := fun B hB => ?_
      isElemAb := fun B hB => h.isElemAb B (hsub hB)
      invariant := fun B hB g hg => ?_
      ne_bot := fun B hB => h.ne_bot B (hsub hB)
      inf_pCore := fun B hB => ?_
      normalizer_eq := fun B hB => ?_
      disjoint := fun B hB C hC hne => h.disjoint B (hsub hB) C (hsub hC) hne
      cond2 := fun B hB C hle hr => h.cond2 B (hsub hB) C hle hr
      quadratic := fun B hB => h.quadratic B (hsub hB)
      equivariant := fun B hB g hg => h.equivariant B (hsub hB) g (hG₁G hg) }
  · obtain ⟨y, hy, rfl⟩ := hB
    exact IndepPair.cj_le_of_mem hAG₁ hy
  · obtain ⟨y, hy, rfl⟩ := hB
    exact ⟨g * y, G₁.mul_mem hg hy, (cj_mul g y A).symm⟩
  · rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ B ⊓ pCoreOf 2 G := ⟨hx.1, hpG₁ hx.2⟩
    rw [h.inf_pCore B (hsub hB), Subgroup.mem_bot] at hx'
    exact hx'
  · ext g
    constructor
    · rintro ⟨hgG₁, hgN⟩
      have hgstab : g ∈ stabilizerOf G (VA B) := by
        rw [← h.normalizer_eq B (hsub hB)]
        exact ⟨hG₁G hgG₁, hgN⟩
      exact ⟨hgG₁, hgstab.2⟩
    · rintro ⟨hgG₁, hgstab⟩
      have hgN : g ∈ Subgroup.normalizer (B : Set (LGL 2 V)) := by
        have hmem : g ∈ G ⊓ Subgroup.normalizer (B : Set (LGL 2 V)) := by
          rw [h.normalizer_eq B (hsub hB)]
          exact ⟨hG₁G hgG₁, hgstab⟩
        exact hmem.2
      exact ⟨hgG₁, hgN⟩

theorem hyp711_UAOf_of_eq_iSup {A : Subgroup (LGL 2 V)}
    (h : Assumption131 G (cjOrbit G A) VA i) (hrank : ∀ B ∈ cjOrbit G A, mRank B ≤ i)
    (hVAle : ∀ B ∈ cjOrbit G A, VA B ≤ fixSub B) (hgen : G = ⨆ B ∈ cjOrbit G A, B) :
    Hyp711 (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G) := by
  have hA : A ∈ cjOrbit G A := mem_cjOrbit_self G A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ((vHat G).subgroupOf (⊤ : Subgroup (VG G))).Normal := normal_vHat.subgroupOf _
  have hOm : ∀ W ∈ omegaSet (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G),
      W ≤ (⊤ : Subgroup (VG G)) := fun _ _ => le_top
  have htrans : ∀ B ∈ cjOrbit G A, ∀ C ∈ cjOrbit G A, ∃ g ∈ G, C = cj g B := by
    rintro B ⟨b, hbG, rfl⟩ C ⟨c, hcG, rfl⟩
    refine ⟨c * b⁻¹, G.mul_mem hcG (G.inv_mem hbG), ?_⟩
    rw [← cj_mul]
    congr 1
    group
  have hΩ := (thirteen_two_three h hrank htrans hA).1
  have hhyp7 : Hyp7 (UAOf G VA A) := hyp7_UAOf h hrank hA (hVAle A hA)
  have hK : ∀ B ∈ cjOrbit G A,
      UAOf G VA B ≤ kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G) := by
    intro B hB
    exact le_kSub (by rw [hΩ]; exact ⟨B, hB, rfl⟩)
  have hGmem : ∀ g : G,
      (SemidirectProduct.inr g : VG G) ∈ kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G) := by
    have haHat : aHat G (⨆ B ∈ cjOrbit G A, B) ≤
        kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G) := by
      have h1 : aHat G (⨆ B ∈ cjOrbit G A, B) = ⨆ B ∈ cjOrbit G A, aHat G B := by
        unfold aHat
        rw [CFSG.LieType.Ree.subgroupOf_biSup_of_le (fun B hB => h.le_G B hB)]
        rw [Subgroup.map_iSup]
        refine iSup_congr fun B => ?_
        rw [Subgroup.map_iSup]
      rw [h1]
      refine iSup₂_le fun B hB => ?_
      exact (le_sup_right : aHat G B ≤ wHat G (VA B) ⊔ aHat G B).trans (hK B hB)
    intro g
    exact haHat (mem_aHat.mpr ⟨g, by rw [← hgen]; exact g.2, rfl⟩)
  haveI : (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)).Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
      (kSub_subgroupOf_normal (V := UAOf G VA A) le_top hnorm hOm)
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  refine
    { toHyp73 :=
        { elemAbelian := hhyp7.1
          ti := hhyp7.2.2
          noncyclic := hhyp7.2.1
          abelian := (isElemAbelian_wHat (G := G) ⊤).1
          le := le_top
          normal := hnorm
          mem := by rw [hΩ]; exact ⟨A, hA, rfl⟩
          omega_le := fun _ _ => le_top
          iSub_le := iSub_le_pCoreOf_kSub le_top
          pcore_le := pCoreOf_kSub_le_pCoreOf le_top hnorm hOm
          jnormal := pCoreOf_subgroupOf_normal le_top
            (kSub_subgroupOf_normal le_top hnorm hOm) }
      oddCore := fusionOddCoreOf_eq_bot_of_charTwo charTwo_top_VG _
      transitive := ?_ }
  intro U hU
  rw [hΩ] at hU
  obtain ⟨B, hB, rfl⟩ := hU
  obtain ⟨g, hgG, rfl⟩ := hB
  refine ⟨(SemidirectProduct.inr (⟨g, hgG⟩ : G))⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ (hGmem ⟨g, hgG⟩)
  · simpa using (conjSubgroup_UAOf_inr_inv h hA ⟨g, hgG⟩).symm

end CFSG.LocalAnalysis.WeakClosure81

end
