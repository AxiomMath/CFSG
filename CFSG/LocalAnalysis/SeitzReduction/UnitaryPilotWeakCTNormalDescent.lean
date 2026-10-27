module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

theorem exists_odd_ordTwistedA_eq {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ Open.ordTwistedA m (2 ^ f) = 2 ^ (f * (m * (m + 1) / 2)) * r :=
  (Timmesfeld.Orders.profile_ordTwistedA hm hf).two

theorem ordTwistedA_ne_ordA_two_mul {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    Open.ordTwistedA (n - 1) (2 ^ f) ≠ Open.ordA (n - 1) (2 ^ (2 * f)) := by
  intro h
  obtain ⟨r, hr, hfr⟩ := exists_odd_ordTwistedA_eq (m := n - 1) (by omega) hf
  obtain ⟨s, hs, hgs⟩ := LinearPilot.exists_odd_ordA_eq (m := n - 1) (by omega)
    (by omega : 1 ≤ 2 * f)
  have hT : 0 < (n - 1) * (n - 1 + 1) / 2 := by
    have : 1 * 2 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hexp := Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hfr.symm.trans (h.trans hgs))
  have hfT : 0 < f * ((n - 1) * (n - 1 + 1) / 2) := Nat.mul_pos (by omega) hT
  have h2 : 2 * f * ((n - 1) * (n - 1 + 1) / 2) = 2 * (f * ((n - 1) * (n - 1 + 1) / 2)) := by
    ring
  omega

theorem not_isComponent_PSU_of_mulEquiv_statedSp {X : Type} [Group X] [Finite X] {k : Type}
    [Field k] [Finite k] {f r n : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ (2 * f)) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) (hn : 3 ≤ n) {D : Subgroup X} (hD : IsComponent D)
    (hDm : LieModel D .PSU n 2 f) : False := by
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hk
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r hr
    (Or.inl (Or.inr hk4))
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp r k) hk hr ⟨MulEquiv.refl _⟩
  have : IsSimpleGroup X := (Φ.trans eProj.symm).isSimpleGroup
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  have hcard : Nat.card D = Nat.card X := by rw [hDtop, Subgroup.card_top]
  rw [LinearPilot.card_of_lieModel_PSU_two hDm, Nat.card_congr Φ.toEquiv,
    SymplecticFlag.card_statedSp r, hk] at hcard
  obtain ⟨u, hu, hDu⟩ := exists_odd_ordTwistedA_eq (m := n - 1) (by omega) hf
  have hodd : Odd (∏ j ∈ Finset.Icc 1 r, ((2 ^ (2 * f)) ^ (2 * j) - 1)) :=
    Timmesfeld.Orders.odd_prod fun j hj =>
      Timmesfeld.Orders.odd_pow_sub_one (by omega) (by simp at hj; omega)
  have h2 : (2 ^ (2 * f)) ^ (r ^ 2) = 2 ^ (2 * f * r ^ 2) := by rw [← pow_mul]
  rw [hDu, h2] at hcard
  have hexp := Timmesfeld.Orders.eq_of_two_pow_mul_odd hu hodd hcard
  have hev : 2 * ((n - 1) * (n - 1 + 1) / 2) = (n - 1) * (n - 1 + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (n - 1))
  have h3 : (n - 1) * (n - 1 + 1) / 2 = 2 * r ^ 2 := by
    have : f * ((n - 1) * (n - 1 + 1) / 2) = f * (2 * r ^ 2) := by rw [hexp]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have h4 : n - 1 + 1 = n := by omega
  rw [h4] at h3 hev
  apply LinearPilot.mul_sub_one_ne_four_mul_sq (n := n) (by omega) r
  rw [mul_comm n]
  omega

theorem not_mem_range_conj_of_isComponent_PSU {F : Type} [Field F] [Finite F] {n f : ℕ}
    (hn : 3 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ (2 * f))
    {β : MulAut (projectiveSL n F)} (hβ : β * β = 1) {C : Subgroup (fixedSubgroup β)}
    (hC : IsComponent C) (hCm : LieModel C .PSU n 2 f) :
    β ∉ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he : 1 ≤ 2 * f := by omega
  rintro ⟨z, rfl⟩
  have hZ : center (projectiveSL n F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn
  have hzz : z * z = 1 := by
    have h2 : z * z ∈ center (projectiveSL n F) := by
      rw [mem_center_iff]
      intro y
      have h3 := DFunLike.congr_fun hβ y
      rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (z * z) = z * (z * y * z⁻¹) * z⁻¹ * (z * z) := by rw [h3]
        _ = z * z * y := by group
    rw [hZ, mem_bot] at h2
    exact h2
  by_cases hz1 : z = 1
  · subst hz1
    have htop : fixedSubgroup (MulAut.conj (1 : projectiveSL n F)) = ⊤ := by
      rw [map_one]
      exact eq_top_iff.2 fun y _ => rfl
    let ε₀ : fixedSubgroup (MulAut.conj (1 : projectiveSL n F)) ≃* projectiveSL n F :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have : IsSimpleGroup (projectiveSL n F) := OutcomeLocal.isSimpleGroup_projectiveSL hn
    have : IsSimpleGroup (fixedSubgroup (MulAut.conj (1 : projectiveSL n F))) :=
      ε₀.isSimpleGroup
    have hCtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hC
    have hcard : Nat.card C = Nat.card (projectiveSL n F) := by
      rw [hCtop, Subgroup.card_top, Nat.card_congr ε₀.toEquiv]
    rw [LinearPilot.card_of_lieModel_PSU_two hCm,
      LinearPilot.natCard_projectiveSL_eq_ordA hn he hF] at hcard
    exact ordTwistedA_ne_ordA_two_mul hn hf hcard
  · have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hzz]) hz1
    let Ψ : fixedSubgroup (MulAut.conj z) ≃* centralizer ({z} : Set (projectiveSL n F)) :=
      MulEquiv.subgroupCongr (LinearPilot.fixedSubgroup_mulAut_conj_eq z)
    exact OutcomeLocal.even_linear_involution_centralizers_component_free he (by omega) hF z
      hzord _ (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hC)

theorem eq_conj_fieldAut_mul_dualAut_conj_inv_of_isComponent {F : Type} [Field F] [Finite F]
    {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ (2 * f)) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) {β : MulAut (projectiveSL n F)} (hβ : β * β = 1)
    {C : Subgroup (fixedSubgroup β)} (hC : IsComponent C) (hCm : LieModel C .PSU n 2 f) :
    ∃ H : GL (Fin n) F,
      β = conjAut n F H * (fieldAut n F σ * dualAut n F) * (conjAut n F H)⁻¹ := by
  have he : 1 ≤ 2 * f := by omega
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two he hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβi := not_mem_range_conj_of_isComponent_PSU hn hf hF hβ hC hCm
  have hβ1 : β ≠ 1 := fun h => hβi ⟨1, by rw [map_one, h]⟩
  have hβord : orderOf β = 2 := orderOf_eq_prime (by rw [sq, hβ]) hβ1
  set ν := CatalogueBLinearHigherB.nativeEquiv n F with hν
  have htrans : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F),
      MulAut.congr ν β = γ → ∃ C' : Subgroup (fixedSubgroup γ), IsComponent C' ∧
        LieModel C' .PSU n 2 f := by
    intro γ hγ
    let Ψ : fixedSubgroup β ≃* fixedSubgroup γ :=
      (fixedSubgroupCongrEquiv ν β).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))
    exact ⟨_, CFSG.LocalCores.isComponent_map_mulEquiv Ψ hC,
      LieType.CurtisTits.lieModel_of_mulEquiv (C.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
        hCm⟩
  have hordν : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F),
      MulAut.congr ν β = γ → orderOf γ = 2 := fun γ hγ => by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr ν).toMonoidHom (MulAut.congr ν).injective β).trans
      hβord
  obtain ⟨A, ρ, ε, hε, hβA⟩ := (automorphism_generation (K := F) hn).2 β
  interval_cases ε
  ·
    exfalso
    rw [pow_zero, mul_one] at hβA
    by_cases hρ : ρ = 1
    · rw [hρ, map_one, mul_one] at hβA
      have h2 : conjAut n F A ^ 2 = 1 := by rw [← hβA, sq, hβ]
      have h1 : conjAut n F A ≠ 1 := by rw [← hβA]; exact hβ1
      obtain ⟨t, -, ht⟩ := OutcomeLocal.exists_involution_eq_conjAut hn A h2 h1
      exact hβi ⟨t, by rw [hβA, ht]⟩
    · have hγ : MulAut.congr ν β = CatalogueBLinearSemilinear.semilinearAction n F A ρ := by
        rw [hβA, CatalogueBLinearHigherB.congr_semilinear]
      obtain ⟨C', hC', hC'm⟩ := htrans _ hγ
      have hsq : CatalogueBLinearSemilinear.semilinearAction n F A ρ ^ 2 = 1 := by
        rw [← hγ, ← map_pow, sq, hβ, map_one]
      obtain ⟨-, hmL, -⟩ := LinearPilot.psl_field_pComponents (by omega) he hF A ρ hρ hsq C'
        (isPComponent_two_of_isComponent hC')
      have h1 := LinearPilot.card_of_lieModel_PSL_two hmL
      have h2 := LinearPilot.card_of_lieModel_PSU_two hC'm
      rw [show 2 * f / 2 = f by omega] at h1
      exact Timmesfeld.Orders.ordA_ne_ordTwistedA (by omega) hf (by omega) hf (h1.symm.trans h2)
  ·
    rw [pow_one] at hβA
    by_cases hρ : ρ = 1
    · exfalso
      rw [hρ, map_one, mul_one] at hβA
      have hγ : MulAut.congr ν β = CatalogueBGraphForm.pureGraphAction n F A := by
        rw [hβA, CatalogueBLinearHigherB.congr_pureGraph]
      obtain ⟨C', hC', hC'm⟩ := htrans _ hγ
      rcases F4Pilot.psl_graph_cases he hF hn A (hordν _ hγ) with ⟨r, hr, -, ⟨Φ⟩⟩ | hch
      · exact not_isComponent_PSU_of_mulEquiv_statedSp hf hF hr Φ hn hC' hC'm
      · exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch C'
          (isPComponent_two_of_isComponent hC')
    ·
      have hsq : (conjAut n F A * fieldAut n F ρ * dualAut n F) ^ 2 = 1 := by
        rw [← hβA, sq, hβ]
      obtain ⟨-, hρpow, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two he hF hn A ρ hρ hsq
      obtain ⟨-, hσpow⟩ := even_and_eq_pow_of_involution he hF hσ1 hσσ
      have hρσ : ρ = σ := RingEquiv.ext fun x => by rw [hρpow, hσpow]
      exact ⟨H, by rw [hβA, hH, hρσ]⟩

theorem eq_conj_graphFieldAut_conj_inv_of_isComponent {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 3 ≤ n) {β : MulAut (projectiveSL n K)}
    (hβ : β * β = 1) {C : Subgroup (fixedSubgroup β)} (hC : IsComponent C)
    (hCm : LieModel C .PSU n 2 f) :
    ∃ H : GL (Fin n) K, β = conjAut n K H * graphFieldAut h n * (conjAut n K H)⁻¹ := by
  have := h.finite
  have hbar1 : barRingEquiv h ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    exact hc (by rw [← barRingEquiv_apply, h1]; rfl)
  exact eq_conj_fieldAut_mul_dualAut_conj_inv_of_isComponent hn h.one_le
    (by rw [h.card]) hbar1 (barRingEquiv_mul_self h) hβ hC hCm

end CFSG.SeitzReduction.UnitaryPilot
