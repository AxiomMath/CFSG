module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
public import CFSG.Adapters.LieModelUnitaryOuter
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge

public section

namespace CFSG.GGQ2Prime.PumpUpU58

open CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_u58 {X : Type} [Group X] [Finite X]
    (h : CFSG.Models.LieModel X .PSU 5 2 3) : Nat.card (Outer X) = 6 := by
  have hB : CFSG.Blueprint.LieModel X .PSU 5 2 3 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (t := .PSU) (by simp [CFSG.Blueprint.classicalTags]) h
  have hcard := CFSG.Blueprint.LieModel.card_outer_psu (X := X) hB (by norm_num) (by norm_num)
  rw [hcard]
  norm_num

@[expose] def U58OddCentralizer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Models.LieModel S .PSU 5 2 3 →
    ∀ x : S, orderOf x = 5 →
      Odd (Nat.card (Subgroup.centralizer ({x} : Set S)))

theorem no_four_of_odd_centralizer {S : Type} [Group S] [Finite S] (x : S)
    (hx : orderOf x = 5)
    (hodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set S))))
    (hout : Nat.card (Outer S) = 6)
    (Qbar : Subgroup (MulAut S)) (hQbar : Nat.card Qbar = 4)
    (hfix : ∀ q ∈ Qbar, q x = x) : False := by
  have hbot : Qbar ⊓ inner S = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    obtain ⟨hrQ, hrI⟩ := Subgroup.mem_inf.1 hr
    obtain ⟨s, hs⟩ := hrI
    have hconjx : MulAut.conj s x = x := by rw [hs]; exact hfix r hrQ
    have hmemC : s ∈ Subgroup.centralizer ({x} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hconjx
      exact mul_inv_eq_iff_eq_mul.mp hconjx
    have hdvdC : orderOf s ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) :=
      Subgroup.orderOf_dvd_natCard _ hmemC
    have hsodd : Odd (orderOf s) := hodd.of_dvd_nat hdvdC
    have hconjdvd : orderOf (MulAut.conj s) ∣ orderOf s := orderOf_map_dvd _ s
    have hr_dvd4 : orderOf r ∣ 4 := by
      rw [← hQbar]
      exact Subgroup.orderOf_dvd_natCard Qbar hrQ
    have hr_dvd_s : orderOf r ∣ orderOf s := by
      rw [← hs]
      exact hconjdvd
    have hrodd : Odd (orderOf r) := hsodd.of_dvd_nat hr_dvd_s
    have hle : orderOf r ≤ 4 := Nat.le_of_dvd (by norm_num) hr_dvd4
    have hpos : 0 < orderOf r := Nat.pos_of_dvd_of_pos hr_dvd4 (by norm_num)
    have hr1 : r = 1 := by
      interval_cases h : orderOf r
      · exact orderOf_eq_one_iff.mp h
      · exact absurd hrodd (by decide)
      · exact absurd hr_dvd4 (by norm_num)
      · exact absurd hrodd (by decide)
    exact hr1
  let φ : Qbar →* Outer S := (QuotientGroup.mk' (inner S)).comp Qbar.subtype
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have hmem2 : ((a⁻¹ * b : Qbar) : MulAut S) ∈ inner S := by
      have h1 : φ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hmem1 : ((a⁻¹ * b : Qbar) : MulAut S) ∈ Qbar := (a⁻¹ * b).2
    have hz : ((a⁻¹ * b : Qbar) : MulAut S) = 1 := by
      have hb := hbot
      rw [eq_bot_iff] at hb
      exact Subgroup.mem_bot.1 (hb (Subgroup.mem_inf.2 ⟨hmem1, hmem2⟩))
    exact Subtype.ext (inv_mul_eq_one.mp hz)
  have hdvd : Nat.card Qbar ∣ Nat.card (Outer S) := Subgroup.card_dvd_of_injective φ hφ_inj
  rw [hQbar, hout] at hdvd
  norm_num at hdvd

theorem u58_no_four_fix_u42 (hC : U58OddCentralizer)
    {K : Type} [Group K] [Finite K] (hquasi : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU 5 2 3)
    {Wk : Subgroup K} (hWk : CFSG.Models.LieModel Wk .PSU 4 2 1)
    (Q : Subgroup (MulAut K)) (hQcard : Nat.card Q = 4)
    (hQfix : ∀ q ∈ Q, ∀ w ∈ Wk, q w = w) : False := by
  haveI : Group.IsPerfect K := ⟨hquasi.1⟩
  have hconj_inj : Function.Injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hWkB : CFSG.Blueprint.LieModel Wk .PSU 4 2 1 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (t := .PSU) (by simp [CFSG.Blueprint.classicalTags]) hWk
  have hWkscm : CFSG.Open.StatedClassicalModel Wk .PSU 4 2 1 :=
    hWkB.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hWksimple : IsSimpleGroup Wk :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWkscm
  have hWkcard : Nat.card Wk = 25920 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hWkscm
  have hWkZ : Wk ⊓ Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hzWk, hzZ⟩ := Subgroup.mem_inf.1 hz
    let z' : Wk := ⟨z, hzWk⟩
    have hz'cen : z' ∈ Subgroup.center Wk := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hzZ (g : K)
    have hcenbot : Subgroup.center Wk = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Wk) with h | h
      · exact h
      · exfalso
        have hcomm : IsMulCommutative Wk := Subgroup.center_eq_top_iff.mp h
        haveI := hcomm
        have hp : (Nat.card Wk).Prime :=
          (Group.is_simple_iff_prime_card (α := Wk)).mp hWksimple
        rw [hWkcard] at hp
        norm_num at hp
    have hz'1 : z' ∈ (⊥ : Subgroup Wk) := hcenbot ▸ hz'cen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hz'1)
  let ι : Wk →* (K ⧸ Subgroup.center K) :=
    (QuotientGroup.mk' (Subgroup.center K)).comp Wk.subtype
  have hι_inj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have haZ : ((a : Wk) : K) ∈ Subgroup.center K :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 ha)
    have hmem : ((a : Wk) : K) ∈ Wk ⊓ Subgroup.center K := ⟨(a : Wk).2, haZ⟩
    rw [hWkZ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h5dvd : 5 ∣ Nat.card Wk := by rw [hWkcard]; norm_num
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Wk) 5 h5dvd
  let S := K ⧸ Subgroup.center K
  haveI : Finite S := inferInstance
  let x : S := ι w
  have hx : orderOf x = 5 := by
    have hxw := orderOf_injective ι hι_inj w
    rw [hw] at hxw
    exact hxw
  let Qbar : Subgroup (MulAut S) :=
    Q.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
  have hQbar : Nat.card Qbar = 4 := by
    have hmap := Subgroup.card_map_of_injective (K := Q)
      (f := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) hconj_inj
    rw [hQcard] at hmap
    exact hmap
  have hQfix' : ∀ q ∈ Qbar, q x = x := by
    intro q hq
    obtain ⟨q₀, hq₀Q, hq_eq⟩ := Subgroup.mem_map.1 hq
    rw [← hq_eq]
    change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient q₀
      ((QuotientGroup.mk' (Subgroup.center K)) ((w : Wk) : K)) =
      (QuotientGroup.mk' (Subgroup.center K)) ((w : Wk) : K)
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    congr 1
    exact hQfix q₀ hq₀Q (w : K) w.2
  exact no_four_of_odd_centralizer x hx (hC S hK x hx) (outer_u58 hK) Qbar hQbar hQfix'

theorem u58OddCentralizer_holds : U58OddCentralizer := by
  intro S _ _ h x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : CFSG.Blueprint.LieModel S .PSU 5 2 3 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (t := .PSU) (by simp [CFSG.Blueprint.classicalTags]) h
  obtain ⟨e₀⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.nonempty_projSU_of_lieModel hB
  let e : S ≃* CFSG.RankThree.PartTwo.KFacts.KS21.U58.SUI :=
    e₀.trans CFSG.RankThree.PartTwo.KFacts.KS21.U58.equivSUI
  have hno10 : ∀ g : S, orderOf g ≠ 10 := by
    intro g hg
    have h10 := CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.orderOf_ne_ten_SUI (e g)
    rw [e.orderOf_eq g] at h10
    exact h10 hg
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set S)) 2 (even_iff_two_dvd.mp heven)
  have hyS : orderOf ((y : S)) = 2 := by
    rw [Subgroup.orderOf_coe y, hy]
  have hcomm : Commute (y : S) x :=
    Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hmul := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hyS, hx]; decide)
  rw [hyS, hx] at hmul
  norm_num at hmul
  exact hno10 ((y : S) * x) hmul

theorem u58_no_four_fix_u42_unconditional
    {K : Type} [Group K] [Finite K] (hquasi : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU 5 2 3)
    {Wk : Subgroup K} (hWk : CFSG.Models.LieModel Wk .PSU 4 2 1)
    (Q : Subgroup (MulAut K)) (hQcard : Nat.card Q = 4)
    (hQfix : ∀ q ∈ Q, ∀ w ∈ Wk, q w = w) : False :=
  u58_no_four_fix_u42 u58OddCentralizer_holds hquasi hK hWk Q hQcard hQfix

theorem u58_pumpUp_false
    {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)} (h : CFSG.GGQ2Prime.PumpUpAut W Wk ζ ξ Q A)
    (hK : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU 5 2 3) : False :=
  u58_no_four_fix_u42_unconditional h.quasi hK h.Wk_model Q h.Q_card h.Q_fix

end CFSG.GGQ2Prime.PumpUpU58

end
