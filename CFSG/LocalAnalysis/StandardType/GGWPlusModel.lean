module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import CFSG.LocalAnalysis.StandardType.GGWPlusPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag TypeA

open Matrix

private noncomputable def ggAutAct {G : Type} [Group G] (H B : Subgroup G) :
    ↥(H ⊓ Subgroup.normalizer (B : Set G)) →* MulAut ↥B where
  toFun x := ggConjAut B (Subgroup.mem_inf.mp x.2).2
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply]
    simp only [Subgroup.coe_one]
    group
  map_mul' x y := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

private theorem ggAutAct_apply {G : Type} [Group G] (H B : Subgroup G)
    (x : ↥(H ⊓ Subgroup.normalizer (B : Set G))) :
    ggAutAct H B x = ggConjAut B (Subgroup.mem_inf.mp x.2).2 := rfl

private theorem ggConjAut_eq_one_iff {G : Type} [Group G] (B : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    ggConjAut B hg = 1 ↔ g ∈ Subgroup.centralizer (B : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := congrArg (fun f : MulAut ↥B => ((f ⟨b, hb⟩ : ↥B) : G)) h
    simp only [ggConjAut_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro hx
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply]
    have hb := (Subgroup.mem_centralizer_iff.mp hx) b b.2
    rw [← hb, mul_assoc, mul_inv_cancel, mul_one]

theorem ggSolvQuotLeTwo_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) (h4 : 4 ≤ Nat.card K)
    (hsec : SLHasSections d K) {Eb : Subgroup (MulAut (projectiveSL d K))}
    (hA : IsElemAbelian p Eb) (hI : (Eb : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K))
    (hr : p ^ (d - 2) ≤ Nat.card Eb) (hsc : GGTorusSelfCent p Eb) :
    GGSolvQuotLeTwo
      ((MulAut.conj : projectiveSL d K →* MulAut (projectiveSL d K)).range ⊓
        Subgroup.normalizer (Eb : Set (MulAut (projectiveSL d K))))
      (Subgroup.centralizer (Eb : Set (MulAut (projectiveSL d K)))) := by
  classical
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hperf : commutator (projectiveSL d K) = ⊤ := by
    have h1 : (commutator (SpecialLinearGroup (Fin d) K)).map (proj d K) = ⊤ := by
      rw [hperfSL, Subgroup.map_top_of_surjective _ (proj_surjective d K)]
    have h2 : (commutator (SpecialLinearGroup (Fin d) K)).map (proj d K) =
        commutator (projectiveSL d K) := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (proj_surjective d K), commutator_def]
    rw [h2] at h1
    exact h1
  have hp3 : p ^ 3 ≤ Nat.card Eb :=
    (Nat.pow_le_pow_right hp.pos (by omega : 3 ≤ d - 2)).trans hr
  obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds (d := d) (p := p) (K := K) hp hp2 hpK
    Eb hA hI hr hp3
  have hind : TypeA.inducedSub (MonoidHom.id (projectiveSL d K)) Eb = Eb := by
    ext φ
    rw [TypeA.mem_inducedSub]
    constructor
    · rintro ⟨a, ha, h⟩
      have h1 : φ = a := MulEquiv.ext (fun l => h l)
      rwa [h1]
    · intro hφ
      exact ⟨φ, hφ, fun _ => rfl⟩
  have hAI : ∀ a ∈ Eb, ∃ φa ∈ Set.range (conjAut d K),
      ∀ l : projectiveSL d K, φa ((MonoidHom.id (projectiveSL d K)) l) =
        (MonoidHom.id (projectiveSL d K)) (a l) :=
    fun a ha => ⟨a, hI ha, fun _ => rfl⟩
  have hA₀' : ∀ B : GL (Fin d) K,
      conjAut d K B ∈ TypeA.inducedSub (MonoidHom.id (projectiveSL d K)) Eb → ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0 := by
    intro B hB
    exact hA₀ B (by rwa [hind] at hB)
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    TypeANbrDvd.exists_actsDiag_model (d := d) (K := K) hperfSL hsec
      (ψ := MonoidHom.id (projectiveSL d K)) (fun x => ⟨x, rfl⟩)
      (by rw [MonoidHom.ker_id]; exact bot_le)
      hperf hAI hA₀'
  have hN : ∀ σ : Equiv.Perm (Fin d),
      NbrInnerWeylA.permConj φ' σ ∈
        Subgroup.normalizer (Eb : Set (MulAut (projectiveSL d K))) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent (d := d) (p := p) (K := K)
      hφ's hφ'ker hA.2 hsc hdiag σ
  have hAut := TypeANbrDvd.ggAutomizer_eq_range_permAut (d := d) (p := p) (K := K)
    hp hp2 hpK hφ's hφ'ker hA hsc hdiag hN
  have hInj : Function.Injective (TypeANbrDvd.permAut φ' Eb hN) :=
    TypeANbrDvd.permAut_injective (d := d) (p := p) (K := K) hp hp2 hpK (by omega : 4 ≤ d)
      hφ's hφ'ker hA hsc hdiag hN
  set Inn : Subgroup (MulAut (projectiveSL d K)) :=
    (MulAut.conj : projectiveSL d K →* MulAut (projectiveSL d K)).range with hInn
  set X : Subgroup (MulAut (projectiveSL d K)) :=
    Inn ⊓ Subgroup.normalizer (Eb : Set (MulAut (projectiveSL d K))) with hX
  set C : Subgroup (MulAut (projectiveSL d K)) :=
    Subgroup.centralizer (Eb : Set (MulAut (projectiveSL d K))) with hC
  let act : ↥X →* MulAut ↥Eb := ggAutAct Inn Eb
  have hact_apply : ∀ x : ↥X, act x = ggConjAut Eb ((Subgroup.mem_inf.mp x.2).2) :=
    fun x => ggAutAct_apply Inn Eb x
  have hact_one : ∀ x : ↥X, act x = 1 ↔ (x : MulAut (projectiveSL d K)) ∈ C := by
    intro x
    rw [hact_apply x]
    exact ggConjAut_eq_one_iff Eb (Subgroup.mem_inf.mp x.2).2
  let e : Equiv.Perm (Fin d) ≃* (TypeANbrDvd.permAut φ' Eb hN).range :=
    MonoidHom.ofInjective hInj
  let actR : ↥X →* (TypeANbrDvd.permAut φ' Eb hN).range :=
    act.codRestrict (TypeANbrDvd.permAut φ' Eb hN).range (fun x => by
      rw [hact_apply x, ← hAut]
      exact ggConjAut_mem_ggAutomizer (Subgroup.mem_inf.mp x.2).1
        (Subgroup.mem_inf.mp x.2).2)
  let ρ : ↥X →* Equiv.Perm (Fin d) := e.symm.toMonoidHom.comp actR
  have hρ : Function.Surjective ρ := by
    intro σ
    have hmem : TypeANbrDvd.permAut φ' Eb hN σ ∈ ggAutomizer Inn Eb := by
      rw [hAut]; exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
    obtain ⟨g, hgInn, hgNorm, hgform⟩ := mem_ggAutomizer_iff.mp hmem
    let x0 : ↥X := ⟨g, Subgroup.mem_inf.mpr ⟨hgInn, hgNorm⟩⟩
    refine ⟨x0, ?_⟩
    have hact_eq : act x0 = TypeANbrDvd.permAut φ' Eb hN σ := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [hact_apply x0, ggConjAut_apply]
      exact (hgform b).symm
    have hactR : actR x0 = e σ := by
      apply Subtype.ext
      change act x0 = TypeANbrDvd.permAut φ' Eb hN σ
      exact hact_eq
    show ρ x0 = σ
    rw [show ρ x0 = e.symm (actR x0) from rfl, hactR, MulEquiv.symm_apply_apply]
  have hker : ρ.ker ≤ C.subgroupOf X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    rw [← hact_one x]
    have h2 : actR x = 1 := by
      have h3 : e (ρ x) = e 1 := congrArg e hx
      rw [show ρ x = e.symm (actR x) from rfl] at h3
      simpa using h3
    have h4 := congrArg (fun y : (TypeANbrDvd.permAut φ' Eb hN).range =>
      (y : MulAut ↥Eb)) h2
    exact h4
  exact ggSolvQuotLeTwo_of_surj
    (fun Q _ f hf hQ => perm_solvable_quotient_card_le_two (by omega : 5 ≤ d) f hf hQ)
    ρ hρ hker

end CFSG.StandardType
