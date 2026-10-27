module

public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Tab
public import CFSG.RankThree.PartOne.F106.NoQD32NAAbel
public import Certificates.Certificate271035

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits TauCeti CFSG.RankThree.PartOne.SEITZX Subgroup
  CFSG.LocalAnalysis.ComponentInitial

section Main


theorem f4_abelian_false
    {T : Type} [Group T] (hT : UntwistedChevalleyModel T .F4 2) {E R : Subgroup T}
    (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) : False := by
  classical
  obtain ⟨K, _, _, hX, ⟨e₀⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hT
  obtain ⟨e⟩ : Nonempty (T ≃* adjointGroup ReeTag.F4.tag K) := ⟨e₀⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hX)
  have hf : f4ThreeCert.Facts :=
    F4SylowCert.facts_of_check _ (Certificates.certificate271060 : F4ThreeRankCheck)
  have hna : f4ThreeCert.NAFacts fun i => f4ThreeCert.tabArr.getD i 0 :=
    F4SylowCert.NAFacts.of_naCheck (Certificates.certificate271035 : F4NACheck)
  have hg : ∀ i < 729, (fun i => f4ThreeCert.tabArr.getD i 0) i = f4ThreeCert.tab.getD i 0 :=
    fun i _ => F4SylowCert.tabArr_getD
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hX] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have : Finite (adjointGroup ReeTag.F4.tag K) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  let T0 := f4GTab (K := K) hf
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  have h81 : 81 ≤ Nat.card E := by
    have := card_ge_pow_four_of_normalizer_qd32 Nat.prime_three (by norm_num) hE h.normalizes ψ
      hψs hψc
    simpa using this
  have hEcube : ∀ a ∈ E, a ^ 3 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE3 : IsPGroup 3 (E.map e.toMonoidHom) := fun y => by
    obtain ⟨a, ha, hay⟩ := y.2
    have h3 : (y : adjointGroup ReeTag.F4.tag K) ^ 3 = 1 := by
      rw [← hay, ← map_pow, hEcube a ha, map_one]
    exact ⟨1, Subtype.ext h3⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgS⟩ := exists_conj_le_of_sylow (p := 3) (k := 6) T0.S T0.card
    (by rw [hG]; norm_num) _ hE3
  have hEcard : Nat.card ↥((E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective e.injective]
  have hcomm1 := map_comm_of_comm e.toMonoidHom E hEcomm
  have hcube1 := map_pow_of_pow e.toMonoidHom E 3 hEcube
  have hcomm2 := map_comm_of_comm (MulAut.conj g).toMonoidHom _ hcomm1
  have hcube2 := map_pow_of_pow (MulAut.conj g).toMonoidHom _ 3 hcube1
  have hEeq : (E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2 :=
    eq_E0_of_elemAbelian_f4 hg hf hna hgS hcomm2 hcube2 (by rw [hEcard]; exact h81)
  have hE81 : Nat.card E = 81 := by
    rw [← hEcard, hEeq]
    exact card_f4Y₂ hf _ _ _ _ hna.cardE0
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_conj e g E (f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2) hEeq
  let trz : T → Prop := fun x => trI (e x) = 0
  have hconj : ∀ n x : T, trz (n * x * n⁻¹) ↔ trz x := by
    intro n x
    simp only [trz, map_mul, map_inv, trI_conj]
  have hcount : Nat.card {x : ↥E // (x : T) ≠ 1 ∧ trz (x : T)} = 24 := by
    rw [← card_trI_E0 (K := K) hg hf hna]
    refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun x => ?_)
    have hx := hφ x
    change (x : T) ≠ 1 ∧ trz (x : T) ↔ ((φ x : ↥(f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2)) :
      adjointGroup ReeTag.F4.tag K) ≠ 1 ∧ trI ((φ x : ↥(f4Y₂ (K := K) hf f4WA f4WY2 hna.homA
        hna.homY2)) : adjointGroup ReeTag.F4.tag K) = 0
    rw [hx, trI_conj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, h2⟩
      have : e x = 1 := by simpa using h
      exact e.injective (by rw [this, map_one])
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, h2⟩
      rw [h, map_one]
      simp
  exact false_of_invariant_abelian hE h hE81 trz hconj (by norm_num) hcount

end Main

end CFSG.RankThree.PartOne.F106
