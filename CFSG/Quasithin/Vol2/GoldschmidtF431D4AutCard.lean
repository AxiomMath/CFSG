module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.RankTwoAmalgam

theorem mulAut_conj_injective_of_center_bot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun a : MulAut X => a x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [h] at hc
  exact Subgroup.mem_bot.1 hc

theorem mulAut_conj_injective_of_equiv {Y X : Type*} [Group Y] [Group X] (e : Y ≃* X)
    (h : Function.Injective (MulAut.conj : X →* MulAut X)) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcentral : ∀ c : X, e g * c * (e g)⁻¹ = c := by
    intro c
    obtain ⟨y, rfl⟩ := e.surjective c
    have := congrArg (fun a : MulAut Y => e (a y)) hg
    simpa [MulAut.conj_apply, map_mul, map_inv] using this
  have h1 : (MulAut.conj : X →* MulAut X) (e g) = 1 := by
    ext c
    simpa [MulAut.conj_apply] using hcentral c
  exact e.injective (by rw [h (h1.trans (map_one _).symm), map_one])

theorem conj_range_index_three {Y : Type} [Group Y] [Finite Y]
    (hcard : Nat.card (MulAut Y) = 3 * Nat.card Y)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) :
    (MulAut.conj : Y →* MulAut Y).range.index = 3 := by
  have h1 := Subgroup.card_mul_index (MulAut.conj : Y →* MulAut Y).range
  have h2 : Nat.card (MulAut.conj : Y →* MulAut Y).range = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h2, hcard] at h1
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have : Nat.card Y * (MulAut.conj : Y →* MulAut Y).range.index = Nat.card Y * 3 := by
    rw [h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem mulAut_intermediate {Y : Type} [Group Y]
    (hidx : (MulAut.conj : Y →* MulAut Y).range.index = 3)
    (M : Subgroup (MulAut Y)) (hM : (MulAut.conj : Y →* MulAut Y).range ≤ M) :
    M = (MulAut.conj : Y →* MulAut Y).range ∨ M = ⊤ := by
  have h := Subgroup.relIndex_mul_index hM
  rw [hidx] at h
  have hp : Nat.Prime 3 := Nat.prime_three
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ h) with h1 | h1
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hM
  · right
    have h2 : M.index = 1 := by
      rw [h1] at h
      omega
    exact Subgroup.index_eq_one.1 h2

section Triality


theorem card_mulAut_of_lieModel_d4 (X : Type) [Group X] (h : IsLieOverTwo .trialityD4 0 1 X) :
    Nat.card (MulAut X) = 3 * Nat.card X ∧
      Function.Injective (MulAut.conj : X →* MulAut X) := by
  have h' : CFSG.Blueprint.LieModel X .trialityD4 0 2 1 := h
  rcases h' with ⟨hcl, -⟩ | ⟨-, hce, hX⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, _, hfin, hK, σ₀, hσ₀, ⟨e⟩⟩ := hX
    obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
      ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
    have hσ : ∀ c, σ c = c ^ (2 ^ 1) := hσ₀
    obtain ⟨-, -, ⟨Θ, -, hΘsurj, hΘker, -⟩, -, hcardK, -, hcenter, ⟨E⟩⟩ :=
      even_triality_exact_automorphism_normal_form (le_refl 1) K hK σ hσ
    let eXC := e.trans E
    have hinjC := mulAut_conj_injective_of_center_bot hcenter
    have hcardC : Nat.card (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        3 * Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
      have h2 : Nat.card (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ Θ.ker) = 3 := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj).toEquiv, hcardK]
      have h3 : Nat.card Θ.ker = Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
        rw [hΘker]
        exact (Nat.card_congr (MonoidHom.ofInjective hinjC).toEquiv).symm
      rw [h1, h2, h3]
    refine ⟨?_, mulAut_conj_injective_of_equiv eXC hinjC⟩
    rw [Nat.card_congr (MulAut.congr eXC).toEquiv, hcardC, Nat.card_congr eXC.toEquiv]
  · exact absurd hree (by decide)
  · exact absurd hsz (by decide)

end Triality

section D

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d4_card_aut : Nat.card (MulAut D) = 3 * Nat.card D ∧
    Function.Injective (MulAut.conj : D →* MulAut D) := by
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 D' hD'
  obtain ⟨h1, h2⟩ := card_mulAut_of_lieModel_d4 D' hD'
  refine ⟨?_, mulAut_conj_injective_of_equiv e.symm h2⟩
  rw [← Nat.card_congr (MulAut.congr e).toEquiv, h1, Nat.card_congr e.toEquiv]

include hD' in
theorem d4_card_aut_dvd : Nat.card (MulAut D) ∣ 3 * Nat.card D :=
  dvd_of_eq (d4_card_aut hD').1

include hD' in
theorem d4_conj_index : (MulAut.conj : D →* MulAut D).range.index = 3 := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  exact conj_range_index_three (d4_card_aut hD').1 (d4_card_aut hD').2

include hD' in
theorem d4_aut_intermediate (M : Subgroup (MulAut D))
    (hM : (MulAut.conj : D →* MulAut D).range ≤ M) :
    M = (MulAut.conj : D →* MulAut D).range ∨ M = ⊤ :=
  mulAut_intermediate (d4_conj_index hD') M hM

end D

end CFSG.Quasithin.D4Hex
