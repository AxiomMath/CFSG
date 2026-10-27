
module

public import CFSG.Quasithin.Vol2.KGFactU35StarBase

public import Certificates.Certificate7153
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin.H13.KGU35

open HNUnitaryBridge CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open Matrix

theorem star_of_block (y : unitarySU 5 1 F25 3) (hy5 : y ^ 5 = 1)
    (hy1 : y ≠ 1) (hyt : y * unitaryInvT f25Data = unitaryInvT f25Data * y) : Star5 y :=
  Certificates.certificate7153 y hy5 hy1 hyt

theorem star_psu {x t : unitaryPSU f25Data 3}
    (hx : orderOf x = 5) (ht : orderOf t = 2) (htx : t * x = x * t) : Star5 x := by
  set π := unitaryProj f25Data 3 with hπ
  set t₀ := unitaryInvT f25Data with ht₀
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryProj_unitaryInvT f25Data (by norm_num) ht)
  set x' := c * x * c⁻¹ with hx'
  suffices hs : Star5 x' by
    have := hs.map (MulAut.conj c⁻¹).toMonoidHom
    simpa [hx', MulAut.conj_apply, mul_assoc] using this
  have hx'5 : orderOf x' = 5 := by
    rw [hx', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hx't : π t₀ * x' = x' * π t₀ := by
    rw [← hc, hx']
    calc c * t * c⁻¹ * (c * x * c⁻¹) = c * (t * x) * c⁻¹ := by group
      _ = c * (x * t) * c⁻¹ := by rw [htx]
      _ = c * x * c⁻¹ * (c * t * c⁻¹) := by group
  obtain ⟨y₀, hy₀⟩ := unitaryProj_surjective f25Data 3 x'
  have hker : ∀ g, π g = 1 → g ∈ unitaryScalars f25Data 3 := fun g hg => by
    rw [← ker_unitaryProj f25Data 3]
    exact hg
  set z := y₀ * t₀ * y₀⁻¹ * t₀⁻¹ with hz
  have hzS : z ∈ unitaryScalars f25Data 3 := hker z (by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv, hy₀, ← hx't]
    group)
  have hzc : ∀ g, g * z = z * g := fun g =>
    Subgroup.mem_center_iff.mp (unitaryScalars_le_center f25Data 3 hzS) g
  have hz3 : z ^ 3 = 1 := pow_three_of_mem hzS
  have ht₀2 : t₀ ^ 2 = 1 := unitaryInvT_sq f25Data
  have hz2 : z ^ 2 = 1 := by
    have e1 : (y₀ * t₀ * y₀⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ht₀2, mul_one, mul_inv_cancel]
    have e2 : y₀ * t₀ * y₀⁻¹ = z * t₀ := by rw [hz]; group
    rw [e2, (Commute.mul_pow (hzc t₀).symm 2), ht₀2, mul_one] at e1
    exact e1
  have hz1 : z = 1 := by
    have : z = z ^ 3 * (z ^ 2)⁻¹ := by group
    rw [this, hz3, hz2, inv_one, mul_one]
  have hyt₀ : y₀ * t₀ = t₀ * y₀ := by
    have : y₀ * t₀ = z * (t₀ * y₀) := by rw [hz]; group
    rw [this, hz1, one_mul]
  have hx'pow : x' ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx'5])
  have hy15 : y₀ ^ 15 = 1 := by
    have h5 : π (y₀ ^ 5) = 1 := by rw [map_pow, hy₀, hx'pow]
    rw [show 15 = 5 * 3 by norm_num, pow_mul]
    exact pow_three_of_mem (hker _ h5)
  have hy : π (y₀ ^ 6) = x' := by
    rw [map_pow, hy₀, show 6 = 5 + 1 by norm_num, pow_succ, hx'pow, one_mul]
  have hy5 : (y₀ ^ 6) ^ 5 = 1 := by
    rw [← pow_mul, show 6 * 5 = 15 * 2 by norm_num, pow_mul, hy15, one_pow]
  have hy1 : y₀ ^ 6 ≠ 1 := by
    intro h1
    rw [h1, map_one] at hy
    rw [← hy, orderOf_one] at hx'5
    exact absurd hx'5 (by norm_num)
  have hyt : y₀ ^ 6 * t₀ = t₀ * y₀ ^ 6 := ((Commute.pow_left hyt₀ 6)).eq
  have := (star_of_block (y₀ ^ 6) hy5 hy1 hyt).map π
  rwa [hy] at this

theorem star_of_model {Q : Type} [Group Q]
    (hQ : StatedClassicalModel Q .PSU 3 5 1) {x t : Q} (hx : orderOf x = 5) (ht : orderOf t = 2)
    (htx : t * x = x * t) : Star5 x := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F25 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, F25.card, hK]
    norm_num
  let φ : K ≃+* F25 := FiniteField.ringEquivOfCardEq hc
  let E : Q ≃* unitaryPSU f25Data 3 :=
    e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (5 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
      (unitaryPSUEquiv f25Data (n := 3) (by norm_num)).symm)
  refine Star5.of_equiv E (star_psu (t := E t) ?_ ?_ ?_)
  · rw [MulEquiv.orderOf_eq, hx]
  · rw [MulEquiv.orderOf_eq, ht]
  · rw [← map_mul, ← map_mul, htx]

end CFSG.Quasithin.H13.KGU35
