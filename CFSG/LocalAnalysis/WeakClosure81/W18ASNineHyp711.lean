module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineComm
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem omegaSet_UAOf_zpowers (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    {a : ↥G} (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) :
    omegaSet (UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) (⊤ : Subgroup (VG G)) (vHat G) =
        UAOf G VA ''
          {B | ∃ y : ↥G, B = Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V)} ∧
      iSub (UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) (⊤ : Subgroup (VG G)) (vHat G) =
        ⨆ B ∈ {B | ∃ y : ↥G, B = Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V)},
          wHat G (VA B) := by
  have hmem : ∀ B ∈ {B | ∃ y : ↥G, B = Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V)},
      B ∈ Γ := by
    rintro B ⟨y, rfl⟩
    exact zpowers_conj_mem h ha y
  refine thirteen_two_three (Assumption131.orbit h ha) (fun A hA => hrank A (hmem A hA))
    ?_ ⟨1, by simp⟩
  rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
  refine ⟨((y' * y⁻¹ : ↥G) : LGL 2 V), (y' * y⁻¹).2, ?_⟩
  rw [cj_zpowers]
  congr 1
  simp [mul_assoc]

theorem hyp73_UAOf_zpowers (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) {U : Subgroup (VG G)}
    (hU : U = UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) :
    Hyp73 U (⊤ : Subgroup (VG G)) (vHat G) (pCoreOf 2 (kSub U (⊤ : Subgroup (VG G)) (vHat G))) := by
  subst hU
  have hhyp7 := hyp7_UAOf h hrank ha (hVAle _ ha)
  have hnorm : ((vHat G).subgroupOf (⊤ : Subgroup (VG G))).Normal := normal_vHat.subgroupOf _
  have hOm : ∀ W ∈ omegaSet (UAOf G VA (Subgroup.zpowers (a : LGL 2 V)))
      (⊤ : Subgroup (VG G)) (vHat G), W ≤ (⊤ : Subgroup (VG G)) := fun _ _ => le_top
  have hmem : UAOf G VA (Subgroup.zpowers (a : LGL 2 V)) ∈
      omegaSet (UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) (⊤ : Subgroup (VG G)) (vHat G) := by
    rw [(omegaSet_UAOf_zpowers h hrank ha).1]
    exact ⟨_, ⟨1, by simp⟩, rfl⟩
  exact
    { elemAbelian := hhyp7.1
      ti := hhyp7.2.2
      noncyclic := hhyp7.2.1
      abelian := (isElemAbelian_wHat (G := G) ⊤).1
      le := le_top
      normal := hnorm
      mem := hmem
      omega_le := hOm
      iSub_le := iSub_le_pCoreOf_kSub le_top
      pcore_le := pCoreOf_kSub_le_pCoreOf le_top hnorm hOm
      jnormal := pCoreOf_subgroupOf_normal le_top (kSub_subgroupOf_normal le_top hnorm hOm) }

theorem charTwo_top_VG : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup (VG G)) := by
  intro x hx
  obtain ⟨-, hxc⟩ := hx
  obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr x
  have hg : g = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    have hw : (SemidirectProduct.inl (Multiplicative.ofAdd w) : VG G) ∈
        pCoreOf 2 (⊤ : Subgroup (VG G)) :=
      wHat_le_pCoreOf (⊤ : Submodule (ZMod 2) V) (mem_wHat.2 ⟨w, Submodule.mem_top, rfl⟩)
    have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hw
    have hconj : (SemidirectProduct.inr g : VG G) * SemidirectProduct.inl (Multiplicative.ofAdd w) =
        SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) w)) *
          (SemidirectProduct.inr g : VG G) :=
      mul_inv_eq_iff_eq_mul.mp (inr_mul_inl_mul_inr_inv g w)
    have h2 : (SemidirectProduct.inl (Multiplicative.ofAdd w) * SemidirectProduct.inl
        (Multiplicative.ofAdd v) : VG G) * SemidirectProduct.inr g =
        (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inl
          (Multiplicative.ofAdd ((g : LGL 2 V) w)) : VG G) * SemidirectProduct.inr g := by
      calc _ = SemidirectProduct.inl (Multiplicative.ofAdd w) *
              (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g) :=
            mul_assoc _ _ _
        _ = SemidirectProduct.inl (Multiplicative.ofAdd v) *
              (SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd w)) := by
            rw [h1, mul_assoc]
        _ = _ := by rw [hconj, ← mul_assoc]
    have h3 := mul_right_cancel h2
    have h4 : Multiplicative.ofAdd w * Multiplicative.ofAdd v =
        Multiplicative.ofAdd v * Multiplicative.ofAdd ((g : LGL 2 V) w) := by
      refine SemidirectProduct.inl_injective (N := Multiplicative V) (G := G)
        (φ := CFSG.LinearAlgebra.linearAction G) ?_
      rw [map_mul, map_mul]
      exact h3
    rw [← ofAdd_add, ← ofAdd_add] at h4
    have h5 := Multiplicative.ofAdd.injective h4
    rw [add_comm] at h5
    exact (add_left_cancel h5).symm
  subst hg
  rw [map_one, mul_one]
  exact wHat_le_pCoreOf (⊤ : Submodule (ZMod 2) V) (mem_wHat.2 ⟨v, Submodule.mem_top, rfl⟩)

theorem fusionOddCoreOf_kSub_UAOf_zpowers (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) {U : Subgroup (VG G)}
    (hU : U = UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) :
    fusionOddCoreOf (kSub U (⊤ : Subgroup (VG G)) (vHat G)) = ⊥ := by
  have hnorm : ((vHat G).subgroupOf (⊤ : Subgroup (VG G))).Normal := normal_vHat.subgroupOf _
  have hOm : ∀ W ∈ omegaSet U (⊤ : Subgroup (VG G)) (vHat G), W ≤ (⊤ : Subgroup (VG G)) :=
    fun _ _ => le_top
  haveI : (kSub U (⊤ : Subgroup (VG G)) (vHat G)).Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
      (kSub_subgroupOf_normal (V := U) le_top hnorm hOm)
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  exact fusionOddCoreOf_eq_bot_of_charTwo charTwo_top_VG _

theorem normalClosure_le_comap_inr_kSub (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) {U : Subgroup (VG G)}
    (hU : U = UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) :
    Subgroup.normalClosure ({a} : Set ↥G) ≤
      (kSub U (⊤ : Subgroup (VG G)) (vHat G)).comap (SemidirectProduct.inr : ↥G →* VG G) := by
  subst hU
  have hΩ := (omegaSet_UAOf_zpowers h hrank ha).1
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro b hb
  obtain ⟨a', ha', hab⟩ := Group.mem_conjugatesOfSet_iff.mp hb
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  rw [Set.mem_singleton_iff] at ha'
  rw [ha', SetLike.mem_coe, Subgroup.mem_comap]
  refine le_kSub (U := UAOf G VA (Subgroup.zpowers ((c * a * c⁻¹ : ↥G) : LGL 2 V))) ?_ ?_
  · rw [hΩ]
    exact ⟨_, ⟨c, rfl⟩, rfl⟩
  · exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨_, Subgroup.mem_zpowers _, rfl⟩)

theorem transitive_kSub_UAOf_zpowers (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) {U : Subgroup (VG G)}
    (hU : U = UAOf G VA (Subgroup.zpowers (a : LGL 2 V)))
    (hclass : ∀ y : ↥G,
      ∃ n ∈ Subgroup.normalClosure ({a} : Set ↥G), y * a * y⁻¹ = n * a * n⁻¹) :
    ∀ W ∈ omegaSet U (⊤ : Subgroup (VG G)) (vHat G),
      ∃ k ∈ kSub U (⊤ : Subgroup (VG G)) (vHat G), W = conjSubgroup U k := by
  have hle := normalClosure_le_comap_inr_kSub h hrank ha hU
  subst hU
  have hΩ := (omegaSet_UAOf_zpowers h hrank ha).1
  intro W hW
  rw [hΩ] at hW
  obtain ⟨B, ⟨y, rfl⟩, rfl⟩ := hW
  obtain ⟨n, hn, hyn⟩ := hclass y
  refine ⟨SemidirectProduct.inr n⁻¹, ?_, ?_⟩
  · rw [map_inv]
    exact Subgroup.inv_mem _ (hle hn)
  · rw [conjSubgroup_UAOf_inr_inv h ha n, cj_zpowers, hyn]
    simp

theorem hyp711_UAOf_zpowers (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ)
    (hclass : ∀ y : ↥G,
      ∃ n ∈ Subgroup.normalClosure ({a} : Set ↥G), y * a * y⁻¹ = n * a * n⁻¹) :
    Hyp711 (UAOf G VA (Subgroup.zpowers (a : LGL 2 V))) (⊤ : Subgroup (VG G)) (vHat G) :=
  { toHyp73 := hyp73_UAOf_zpowers h hrank hVAle ha rfl
    oddCore := fusionOddCoreOf_kSub_UAOf_zpowers h hrank hVAle ha rfl
    transitive := transitive_kSub_UAOf_zpowers h hrank hVAle ha rfl hclass }

end CFSG.LocalAnalysis.WeakClosure81

end
