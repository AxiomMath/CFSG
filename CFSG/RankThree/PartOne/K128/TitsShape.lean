module

public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.S12K CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne.KLR

theorem factorization_ordTits_five : (CFSG.Open.ordTits).factorization 5 = 2 := by
  have h : CFSG.Open.ordTits = 5 ^ 2 * 718848 := by norm_num [CFSG.Open.ordTits]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Tits


theorem sylowShape_five_of_tits_model {Y : Type} [Group Y] [Finite Y]
    (hY : ReeTitsModel Y .Tits 2 1) : SylowShape 5 2 1 Y := by
  classical
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hcardY := card_of_reeTitsModel_Tits hY
  obtain ⟨-, a₀, ha₀, hrel⟩ := hY
  have ha0 : a₀ = 0 := by omega
  subst ha0
  obtain ⟨K₀, _, _, hK₀, ⟨e⟩⟩ := hrel
  have hK₀' : Nat.card K₀ = 2 ^ (2 * 0 + 1) := by simpa using hK₀
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ ReeTag.F4.prime :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK₀]; rfl)
  have : Finite (ModGL ReeTag.F4.tag K₀) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K₀ 0) := Subtype.finite
  have eY : Y ≃* DerivedCentralQuotient (ReeTag.F4.reeGamma K₀ 0) :=
    e.trans (by
      rw [ReeTag.reeGamma_eq_reeFixedGroup]
      exact MulEquiv.refl _)
  have hΓcard : Nat.card (ReeTag.F4.reeGamma K₀ 0) = 35942400 := by
    have := (large_Ree_exact_native_order_and_prime_factor_exhaustion 0 K₀ hK₀').1
    rw [this]
    norm_num
  have hYcard : Nat.card Y = 17971200 := by
    rw [hcardY]
    norm_num [CFSG.Open.ordTits]
  set Γ₀ := ReeTag.F4.reeGamma K₀ 0 with hΓ₀
  let Cg : Subgroup ↥Γ₀ := commutator ↥Γ₀
  let eD : DerivedCentralQuotient Γ₀ ≃* Cg ⧸ Subgroup.center ↥Cg :=
    CFSG.LieType.BorelTits.derivedCentralQuotientEquiv Γ₀ (MulEquiv.refl ↥Γ₀)
  let eYC : Y ≃* Cg ⧸ Subgroup.center ↥Cg := eY.trans eD
  have hYC : Nat.card (Cg ⧸ Subgroup.center ↥Cg) = Nat.card Y :=
    (Nat.card_congr eYC.toEquiv).symm
  have hCZ : Nat.card Cg = Nat.card (Cg ⧸ Subgroup.center ↥Cg) * Nat.card (Subgroup.center ↥Cg) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Cg)
  have hCΓ : Nat.card Cg * Cg.index = Nat.card ↥Γ₀ := Subgroup.card_mul_index Cg
  have hZidx : Nat.card (Subgroup.center ↥Cg) * Cg.index = 2 := by
    have h1 : Nat.card Y * (Nat.card (Subgroup.center ↥Cg) * Cg.index) = Nat.card Y * 2 := by
      calc Nat.card Y * (Nat.card (Subgroup.center ↥Cg) * Cg.index)
          = (Nat.card (Cg ⧸ Subgroup.center ↥Cg) * Nat.card (Subgroup.center ↥Cg)) * Cg.index := by
            rw [hYC]
            ring
        _ = Nat.card Cg * Cg.index := by rw [hCZ]
        _ = Nat.card ↥Γ₀ := hCΓ
        _ = Nat.card Y * 2 := by rw [hΓcard, hYcard]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hmem : ∀ g : ↥Γ₀, g ^ 5 = 1 → g ∈ Cg := by
    intro g hg
    have hpow := Subgroup.pow_index_mem Cg g
    have hidx : Cg.index = 1 ∨ Cg.index = 2 := by
      have h0 : 0 < Nat.card (Subgroup.center ↥Cg) := Nat.card_pos
      have hle : Cg.index ≤ 2 := by nlinarith
      have h1 : Cg.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    rcases hidx with h | h
    · rw [h, pow_one] at hpow
      exact hpow
    · rw [h] at hpow
      have : g = ((g ^ 2)⁻¹) ^ 2 * g ^ 5 := by group
      rw [this, hg, mul_one]
      exact Cg.pow_mem (Cg.inv_mem hpow) 2
  have hZ2 : ∀ z ∈ Subgroup.center ↥Cg, z ^ 2 = 1 := by
    intro z hz
    have h2 : Nat.card (Subgroup.center ↥Cg) ∣ 2 := Dvd.intro _ hZidx
    exact orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard _ hz).trans h2)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K₀) (L := AlgebraicClosure K₀) hK₀'
  have : CharP (AlgebraicClosure K₀) 2 :=
    charP_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective 2
  have hmM : ((5 ^ 1 : ℕ) : ℤ) ∣ 2 ^ (2 * 0 + 1) + 2 ^ (0 + 1) + 1 := by norm_num
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi4p (L := AlgebraicClosure K₀) (a := 0) D.isFrob
    (m := 5 ^ 1) (by norm_num) hmM
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi4p Φ hΦ hΦF
  obtain ⟨Ψ', hΨ'⟩ := exists_injective_pi_of_rootsOfUnity_hom hp5
    (natCast_ne_zero_algebraicClosure hp5 (by norm_num)) Ψ hΨ
  have hpow5 : ∀ v : Fin 2 → Multiplicative (ZMod (5 ^ 1)), Ψ' v ^ 5 = 1 := by
    intro v
    rw [← map_pow]
    have : v ^ 5 = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      simp only [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one]
      have : ((5 : ℕ) : ZMod (5 ^ 1)) = 0 :=
        (congrArg (Nat.cast : ℕ → ZMod (5 ^ 1)) (pow_one 5).symm).trans (ZMod.natCast_self (5 ^ 1))
      rw [nsmul_eq_mul, this, zero_mul]
    rw [this, map_one]
  let Ψ'' : (Fin 2 → Multiplicative (ZMod (5 ^ 1))) →* ↥Cg :=
    Ψ'.codRestrict Cg fun v => hmem _ (hpow5 v)
  let Θ : (Fin 2 → Multiplicative (ZMod (5 ^ 1))) →* Cg ⧸ Subgroup.center ↥Cg :=
    (QuotientGroup.mk' (Subgroup.center ↥Cg)).comp Ψ''
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : Ψ'' v ∈ Subgroup.center ↥Cg := (QuotientGroup.eq_one_iff _).1 hv
    have h2 : (Ψ'' v) ^ 2 = 1 := hZ2 _ hv'
    have h5 : (Ψ'' v) ^ 5 = 1 := Subtype.ext (hpow5 v)
    have h1 : Ψ'' v = 1 := by
      have : Ψ'' v = (((Ψ'' v) ^ 2)⁻¹) ^ 2 * (Ψ'' v) ^ 5 := by group
      rw [this, h2, h5]
      simp
    have h3 : Ψ' v = 1 := congrArg Subtype.val h1
    exact (injective_iff_map_eq_one Ψ').1 hΨ' v h3
  refine sylowShape_of_injective hp5 (eYC.symm.toMonoidHom.comp Θ) (eYC.symm.injective.comp hΘ) ?_
  rw [hcardY]
  exact factorization_ordTits_five

end Tits

end CFSG.RankThree.PartOne.K128
