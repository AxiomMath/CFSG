module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis

open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_automorphism_semilinear_isomorphism even_linear_two_involution_normal_forms)

theorem mulAutCongr_conj_eq {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') (x : T) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_finset_card_four {k : Type*} [Finite k] (hk : 4 ≤ Nat.card k) :
    ∃ s : Finset k, s.card = 4 := by
  have := Fintype.ofFinite k
  have h4 : 4 ≤ (Finset.univ : Finset k).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hk
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

theorem even_linear_two_outer_involution_perfect_fixed_rigidity {D : Type} [Group D] {f : ℕ}
    (hf : 3 ≤ f) (hD : StatedClassicalModel D .PSL 2 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ e : ℕ, f = 2 * e ∧ 2 ≤ e ∧ ∃ J : Subgroup D, (∀ d ∈ J, α d = d) ∧ IsSimpleGroup J ∧
      Group.IsPerfect J ∧ (¬∀ a b : J, a * b = b * a) ∧ StatedClassicalModel J .PSL 2 2 e ∧
      {β : MulAut D | ∀ j ∈ J, β j = j} = (zpowers α : Set (MulAut D)) ∧
      ∀ P : Subgroup (MulAut D), (P : Set (MulAut D)) ⊆ {β | ∀ j ∈ J, β j = j} →
        IsPGroup 2 P → Nat.card P ≤ 2 := by
  classical
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  let φ : D ≃* coordinateG K :=
    eD.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans (pslEquivCoordinateG K))
  obtain ⟨c, hc, hcG, -⟩ :=
    linear_two_automorphism_semilinear_isomorphism K
  let Φ : MulAut D ≃* coordinateE K := (MulAut.congr φ).trans c.symm
  have hΦ : ∀ (β : MulAut D) (d : D),
      ((φ (β d) : coordinateG K) : Equiv.Perm (Omega K)) =
        (Φ β : Equiv.Perm (Omega K)) * φ d * (Φ β : Equiv.Perm (Omega K))⁻¹ := by
    intro β d
    have h := hc (Φ β) (φ d)
    rw [show c (Φ β) = MulAut.congr φ β from c.apply_symm_apply _] at h
    rw [← h, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set a : Equiv.Perm (Omega K) := (Φ α : Equiv.Perm (Omega K)) with ha
  have haE : a ∈ coordinateE K := (Φ α).2
  have ha2 : orderOf a = 2 := by
    rw [ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hα]
  have haG : a ∉ coordinateG K := by
    intro haG
    apply hαout
    have h1 : Φ α = ⟨a, ((coordinateG_le_D K).trans (coordinateD_le_E K)) haG⟩ := rfl
    have h2 : MulAut.congr φ α = MulAut.conj (⟨a, haG⟩ : coordinateG K) := by
      have h3 := hcG ⟨a, haG⟩
      rw [← h1] at h3
      rw [← h3]
      exact (c.apply_symm_apply _).symm
    refine ⟨φ.symm ⟨a, haG⟩, ?_⟩
    apply (MulAut.congr φ).injective
    rw [h2, mulAutCongr_conj_eq, φ.apply_symm_apply]
  have hNF := (even_linear_two_involution_normal_forms (K := K) hf1 hK).2.2.2.2.2.2.2.2.2 a haE
    ha2
  rcases hNF with ⟨haG', -⟩ | ⟨-, hfe, σ, hσ1, hσσ, hσx, -, -, ⟨h, hhG, hah⟩, k, hk, hkcard⟩
  · exact absurd haG' haG
  obtain ⟨e, he⟩ := hfe
  have hfe : f = 2 * e := by omega
  have he2 : 2 ≤ e := by omega
  have hfe2 : f / 2 = e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, hfe]
  have hσ' : ∀ x, σ x = x ^ 2 ^ e := fun x => by rw [hσx, hfe2]
  have hk' : ∀ x, x ∈ k ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk]
    rfl
  obtain ⟨-, hjinj, hjG, hkcard', hcent⟩ :=
    quadratic_projective_linear_two_subfield_pointwise_centralizer Nat.prime_two (by omega) hK'
      σ hσ' k hk'
  set jG : Subgroup (Equiv.Perm (Omega K)) :=
    ((coordinateG k).subgroupOf (coordinateD k)).map ((coordinateD K).subtype.comp (subfieldD k))
    with hjG_def
  have hjGG : jG ≤ coordinateG K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hjG x hx
  set Jp : Subgroup (Equiv.Perm (Omega K)) := jG.map (MulAut.conj h).toMonoidHom with hJp
  have hJpG : Jp ≤ coordinateG K := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hhG (hjGG hy)) (inv_mem hhG)
  set J : Subgroup D := (Jp.subgroupOf (coordinateG K)).map φ.symm.toMonoidHom with hJ
  have hmemJ : ∀ d : D, d ∈ J ↔ ((φ d : coordinateG K) : Equiv.Perm (Omega K)) ∈ Jp := by
    intro d
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, φ.apply_symm_apply]
      exact hx
    · intro hd
      exact ⟨φ d, hd, φ.symm_apply_apply d⟩
  have hσj : ∀ y ∈ jG, fieldExtension K σ * y * (fieldExtension K σ)⁻¹ = y := by
    intro y hy
    have h1 : fieldExtension K σ ∈
        centralizer (jG : Set (Equiv.Perm (Omega K))) ⊓ coordinateE K := by
      rw [hcent]
      exact mem_zpowers _
    have h2 := mem_centralizer_iff.mp (mem_inf.mp h1).1 y hy
    rw [← h2, mul_inv_cancel_right]
  have hαJ : ∀ d ∈ J, α d = d := by
    intro d hd
    rw [hmemJ] at hd
    obtain ⟨y, hy, hyd⟩ := hd
    apply φ.injective
    apply Subtype.ext
    rw [hΦ, ← ha, hah, ← hyd]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * fieldExtension K σ * h⁻¹ * (h * y * h⁻¹) * (h * fieldExtension K σ * h⁻¹)⁻¹ =
        h * (fieldExtension K σ * y * (fieldExtension K σ)⁻¹) * h⁻¹ := by group
      _ = h * y * h⁻¹ := by rw [hσj y hy]
  have hjinj' : Function.Injective ((coordinateD K).subtype.comp (subfieldD k)) :=
    (coordinateD K).subtype_injective.comp hjinj
  let e1 : J ≃* Jp.subgroupOf (coordinateG K) :=
    ((Jp.subgroupOf (coordinateG K)).equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm
  let e2 : Jp.subgroupOf (coordinateG K) ≃* Jp := subgroupOfEquivOfLe hJpG
  let e3 : Jp ≃* jG := (jG.equivMapOfInjective _ (MulAut.conj h).injective).symm
  let e4 : jG ≃* (coordinateG k).subgroupOf (coordinateD k) :=
    (((coordinateG k).subgroupOf (coordinateD k)).equivMapOfInjective _ hjinj').symm
  let e5 : (coordinateG k).subgroupOf (coordinateD k) ≃* coordinateG k :=
    subgroupOfEquivOfLe (coordinateG_le_D k)
  let eJ : J ≃* CFSG.GorensteinWalter.PSL2 k :=
    e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (pslEquivCoordinateG k).symm))))
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkcard', show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) he2
  obtain ⟨s4, hs4⟩ := exists_finset_card_four hk4
  obtain ⟨hnt, hsimp, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl
    (Or.inr ⟨s4, hs4⟩)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := 2) le_rfl
    (Or.inr ⟨s4, hs4⟩)
  have hJsimple : IsSimpleGroup J := eJ.isSimpleGroup
  have hJperf : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom)
    eJ.symm.surjective
  have hJnab : ¬∀ a b : J, a * b = b * a := by
    intro hab
    have h1 : commutator J = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, commutator_le]
      intro x _ y _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab x y
    have h2 := hJperf.commutator_eq_top
    rw [h1] at h2
    obtain ⟨x, y, hxy⟩ := hJsimple.exists_pair_ne
    exact hxy (by
      have hx : x ∈ (⊥ : Subgroup J) := h2 ▸ mem_top x
      have hy : y ∈ (⊥ : Subgroup J) := h2 ▸ mem_top y
      rw [mem_bot] at hx hy
      rw [hx, hy])
  have hJmodel : StatedClassicalModel J .PSL 2 2 e := by
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, k, inferInstance, inferInstance, hkcard',
      ⟨eJ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      have : (4 : ℕ) ≤ 2 ^ e := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.pow_le_pow_right (by norm_num) he2
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      have : (4 : ℕ) ≤ 2 ^ e := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.pow_le_pow_right (by norm_num) he2
      omega
  have hhE : h ∈ coordinateE K := (coordinateG_le_D K).trans (coordinateD_le_E K) hhG
  have hfix : ∀ β : MulAut D, (∀ j ∈ J, β j = j) → β ∈ zpowers α := by
    intro β hβ
    set b : Equiv.Perm (Omega K) := (Φ β : Equiv.Perm (Omega K)) with hb
    have hbE : b ∈ coordinateE K := (Φ β).2
    have hbJp : ∀ x ∈ Jp, b * x * b⁻¹ = x := by
      intro x hx
      have hxG := hJpG hx
      have hd : φ.symm ⟨x, hxG⟩ ∈ J := (hmemJ _).mpr (by rw [φ.apply_symm_apply]; exact hx)
      have h1 := hΦ β (φ.symm ⟨x, hxG⟩)
      rw [hβ _ hd, φ.apply_symm_apply] at h1
      exact h1.symm
    have hc1 : h⁻¹ * b * h ∈ centralizer (jG : Set (Equiv.Perm (Omega K))) ⊓ coordinateE K := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_,
        mul_mem (mul_mem (inv_mem hhE) hbE) hhE⟩
      have h2 := hbJp (h * y * h⁻¹) ⟨y, hy, by simp⟩
      have h3 : b * (h * y * h⁻¹) = (h * y * h⁻¹) * b := by
        calc b * (h * y * h⁻¹) = b * (h * y * h⁻¹) * b⁻¹ * b := by group
          _ = (h * y * h⁻¹) * b := by rw [h2]
      calc y * (h⁻¹ * b * h) = h⁻¹ * ((h * y * h⁻¹) * b) * h := by group
        _ = h⁻¹ * (b * (h * y * h⁻¹)) * h := by rw [h3]
        _ = h⁻¹ * b * h * y := by group
    rw [hcent] at hc1
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hc1
    have hb' : b = a ^ n := by
      rw [hah, conj_zpow, hn]
      group
    refine mem_zpowers_iff.mpr ⟨n, Φ.injective ?_⟩
    rw [map_zpow]
    apply Subtype.ext
    rw [SubgroupClass.coe_zpow, ← ha, ← hb']
  have hfixset : {β : MulAut D | ∀ j ∈ J, β j = j} = (zpowers α : Set (MulAut D)) := by
    ext β
    refine ⟨hfix β, fun hβ => ?_⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hβ
    let F : Subgroup (MulAut D) :=
      { carrier := {β | ∀ j ∈ J, β j = j}
        mul_mem' := fun {x y} hx hy j hj => by rw [MulAut.mul_apply, hy j hj, hx j hj]
        one_mem' := fun j _ => rfl
        inv_mem' := fun {x} hx j hj => by
          rw [MulAut.inv_def, MulEquiv.symm_apply_eq, hx j hj] }
    have hαF : α ∈ F := hαJ
    exact (zpowers_le.mpr hαF) hβ
  refine ⟨e, hfe, he2, J, hαJ, hJsimple, hJperf, hJnab, hJmodel, hfixset, fun P hP _ => ?_⟩
  have hPle : P ≤ zpowers α := fun x hx => by
    have := hP hx
    rw [hfixset] at this
    exact this
  have hcard : Nat.card (zpowers α) = 2 := by rw [Nat.card_zpowers, hα]
  have : Finite (zpowers α) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact (Subgroup.card_le_of_le hPle).trans hcard.le

end CFSG.LocalAnalysis
