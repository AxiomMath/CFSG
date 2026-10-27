module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KG2Inner
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSL2
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec11

section G2Outer


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem four_le_card_of_cube_root {k : Type} [Field k] [Finite k] {ω : k}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : 4 ≤ Nat.card k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hu3 : (Units.mk0 ω hω0) ^ 3 = 1 := Units.ext (by simpa using hω3)
  have hu1 : Units.mk0 ω hω0 ≠ 1 := fun h => hω1 (by simpa using congrArg Units.val h)
  have hord : orderOf (Units.mk0 ω hω0) = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card kˣ := hord ▸ orderOf_dvd_natCard (Units.mk0 ω hω0)
  rw [Nat.card_units] at hdvd
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem eInvFour_G2_of_fixing (h3 : 3 ∣ Nat.card K - 1) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {Ē : Subgroup (MulAut ↥(adjointGroup .G2 K))} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) (hσE : g2FieldHom K σ ∈ Ē) :
    EInvFour ↥(adjointGroup .G2 K) Ē := by
  classical
  have hK : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK]; decide
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨c, hc⟩ := h3
    omega
  haveI := CFSG.RankThree.GF2n.Stroth80.isCyclic_ringEquiv K
  haveI : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun a b h => RingEquiv.ext (fun x => congrFun h x))
  obtain ⟨hdec, hfaith⟩ := g2_automorphism_normal_form hK3 hK4
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hconjinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  have hΦ1 : g2FieldHom K σ ≠ 1 := by
    intro h
    have := hfaith σ (by rw [h]; exact ⟨1, map_one _⟩)
    rw [this, orderOf_one] at hσ
    omega
  obtain ⟨g₀, hg₀E, hg₀a⟩ := exists_inner_of_cyclic_out (g2FieldHom K) (fun α _ => hdec α) hfaith
    hE3 hE9 hσ hσE
  have hcomm : g2FieldHom K σ * MulAut.conj g₀ = MulAut.conj g₀ * g2FieldHom K σ := by
    have := hE3.1.is_comm.comm ⟨_, hσE⟩ ⟨_, hg₀E⟩
    exact congrArg Subtype.val this
  have hfix : g2FieldHom K σ g₀ = g₀ := by
    apply hconjinj
    rw [← mul_mulAutConj_mul_inv (g2FieldHom K σ) g₀, hcomm]
    group
  have hg₀3 : g₀ ^ 3 = 1 := by
    apply hconjinj
    rw [map_pow, map_one]
    exact hE3.2 _ hg₀E
  have hg₀1 : g₀ ≠ 1 := by
    rintro rfl
    exact hg₀a (by rw [map_one]; exact Subgroup.one_mem _)
  obtain ⟨h, hh⟩ := (mem_range_g2Incl_iff hK σ g₀).mpr hfix
  have hh3 : h ^ 3 = 1 := by
    apply g2Incl_injective σ
    rw [map_pow, hh, map_one]
    exact hg₀3
  have hh1 : h ≠ 1 := by
    rintro rfl
    apply hg₀1
    rw [← hh, map_one]
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringEquiv_fixes_cube_root hσ3 hω hω1
  let ωk : fixSubfield σ := ⟨ω, (mem_fixSubfield σ).mpr hσω⟩
  have hωk : ωk ^ 2 + ωk + 1 = 0 := Subtype.ext (by simpa [ωk] using hω)
  have hωk1 : ωk ≠ 1 := fun h' => hω1 (by simpa [ωk] using congrArg Subtype.val h')
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := four_le_card_of_cube_root hωk hωk1
  have hk3 : ringChar (fixSubfield σ) ≠ 3 := by
    have : ringChar (fixSubfield σ) = 2 := ringChar.eq _ 2
    rw [this]; decide
  obtain ⟨y, hy⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds (fixSubfield σ) hk3 hk4 h hh3 hh1
  obtain ⟨ι₀, hι₀, z', hz'⟩ : ∃ ι₀ : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) →*
      ↥(adjointGroup .G2 (fixSubfield σ)), Function.Injective ι₀ ∧
      ∃ z', ι₀ z' = y * h * y⁻¹ := by
    rcases hy with hy | hy
    · obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := fixSubfield σ)
      exact ⟨(KS11Lie4Proof.g2ShortSL2 (fixSubfield σ)).subtype.comp e.toMonoidHom,
        (Subgroup.subtype_injective _).comp e.injective, e.symm ⟨_, hy⟩, by simp⟩
    · obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := fixSubfield σ)
      exact ⟨(KS11Lie4Proof.g2LongSL2 (fixSubfield σ)).subtype.comp e.toMonoidHom,
        (Subgroup.subtype_injective _).comp e.injective, e.symm ⟨_, hy⟩, by simp⟩
  have hz'3 : z' ^ 3 = 1 := by
    apply hι₀
    rw [map_pow, hz', map_one]
    rw [conj_pow, hh3]
    group
  have hz'1 : z' ≠ 1 := by
    rintro rfl
    apply hh1
    rw [map_one] at hz'
    have : h = y⁻¹ * 1 * y := by
      calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
        _ = y⁻¹ * 1 * y := by rw [← hz']
    rw [this]; group
  obtain ⟨W₀, hW₀ab, hW₀4, hW₀inv, w₀, hw₀, hw₀move⟩ := exists_four_sl2 hωk hωk1 z' hz'3 hz'1
  set ψ : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) →* ↥(adjointGroup .G2 K) :=
    (g2Incl σ).comp ι₀ with hψ
  have hψinj : Function.Injective ψ := (g2Incl_injective σ).comp hι₀
  have hψfix : ∀ w, g2FieldHom K σ (ψ w) = ψ w := fun w =>
    (mem_range_g2Incl_iff hK σ (ψ w)).mp ⟨ι₀ w, rfl⟩
  have hYfix : g2FieldHom K σ (g2Incl σ y) = g2Incl σ y :=
    (mem_range_g2Incl_iff hK σ (g2Incl σ y)).mp ⟨y, rfl⟩
  have hYg : g2Incl σ y * g₀ * (g2Incl σ y)⁻¹ = ψ z' := by
    rw [← hh, hψ, MonoidHom.comp_apply, hz', map_mul, map_mul, map_inv]
  refine eInvFour_of_fixed_four hE3 hE9 hσE hΦ1 hg₀E hg₀a hYfix
    (V := W₀.map ψ) (CFSG.Open.IsElemAbelian.map hW₀ab ψ)
    (by rw [Subgroup.card_map_of_injective hψinj, hW₀4]) ?_ ?_ ?_
  · rintro _ ⟨w, -, rfl⟩
    exact hψfix w
  · rintro _ ⟨w, hw, rfl⟩
    rw [hYg]
    exact ⟨z' * w * z'⁻¹, hW₀inv w hw, by simp⟩
  · refine ⟨ψ w₀, ⟨w₀, hw₀, rfl⟩, fun hcon => hw₀move ?_⟩
    rw [hYg] at hcon
    apply hψinj
    simpa using hcon

theorem eInvFour_G2_outer (h3 : 3 ∣ Nat.card K - 1)
    {Ē : Subgroup (MulAut ↥(adjointGroup .G2 K))} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9)
    (hout : ¬ Ē ≤ (MulAut.conj : ↥(adjointGroup .G2 K) →*
      MulAut ↥(adjointGroup .G2 K)).range) :
    EInvFour ↥(adjointGroup .G2 K) Ē := by
  have hK : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK]; decide
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨c, hc⟩ := h3
    omega
  obtain ⟨a, haE, haI⟩ := SetLike.not_le_iff_exists.mp hout
  have ha3 : a ^ 3 = 1 := hE3.2 a haE
  obtain ⟨σ, hσ3, k, hak⟩ := g2_order_three_field_descent hK3 hK4 ha3 haI
  refine eInvFour_of_map_conj (MulAut.conj k)⁻¹ ?_
  refine eInvFour_G2_of_fixing h3 hσ3 (CFSG.Open.IsElemAbelian.map hE3 _) ?_ ⟨a, haE, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hE9]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hak]
    group

theorem eInvNine_adjointG2 (h3 : 3 ∣ Nat.card K - 1) : EInvNine ↥(adjointGroup .G2 K) := by
  intro Ē hE3 hE9
  by_cases hin : Ē ≤ (MulAut.conj : ↥(adjointGroup .G2 K) →*
      MulAut ↥(adjointGroup .G2 K)).range
  · exact eInvFour_G2_inner h3 hE3 hE9 hin
  · exact eInvFour_G2_outer h3 hE3 hE9 hin

end G2Outer

section Model


theorem eInvNine_chevalleyG2 {X : Type} [Group X] {n : ℕ} (hn0 : 0 < n) (hn : Even n)
    (hX : ChevalleyExceptionalModel X .G2 2 n) : EInvNine X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX.2
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn0 hK
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact three_dvd_two_pow_sub_one hn
  exact EInvNine.of_mulEquiv (e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)) (eInvNine_adjointG2 h3)

end Model

end CFSG.RankThree.PartTwo.Sec21.Hering214
