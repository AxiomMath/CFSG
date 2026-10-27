module

public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_norm_exists_subgroup_card_eight {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ Nat.card ↥P = 8 := by
  have hcard : Nat.card ↥L = 168 := card_eq_168_of_isPSL_three_two hL
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : 2 ^ 3 ∣ Nat.card ↥L := by rw [hcard]; norm_num
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 (n := 3) hdvd
  exact ⟨K.map L.subtype, Subgroup.map_subtype_le K,
    by rw [Subgroup.card_map_of_injective L.subtype_injective, hK]; norm_num⟩

theorem s16c167_norm_two_le_card_inf_fixV {V : Subgroup W} (hc : Nat.card ↥V = 8)
    {P : Subgroup (MulAut W)} (hP : Nat.card ↥P = 8) (hPV : ∀ g ∈ P, ∀ v ∈ V, g v ∈ V) :
    2 ≤ Nat.card ↥(V ⊓ fixV P) := by
  have hPs : P ≤ stabSub V := le_stabSub_of_inv hPV
  have hdvdAut : Nat.card ↥(autSub P V) ∣ 2 ^ 3 := by
    have h := card_autSub_mul hPs
    rw [hP] at h
    exact ⟨_, by rw [h]; norm_num⟩
  have hG : IsPGroup 2 ↥(autSub P V) := IsPGroup.of_card_dvd_pow hdvdAut
  have h1V : (1 : ↥V) ∈ fixV (autSub P V) := by
    rw [mem_fixV]
    intro x _
    exact map_one x
  have h1fix : (1 : ↥V) ∈ MulAction.fixedPoints ↥(autSub P V) ↥V := by
    rw [MulAction.mem_fixedPoints]
    intro x
    rw [Subgroup.smul_def]
    exact map_one (x : MulAut ↥V)
  have h2dvd : 2 ∣ Nat.card ↥V := by rw [hc]; norm_num
  obtain ⟨b, hbfix, hne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥V) h2dvd h1fix
  have hbV : b ∈ fixV (autSub P V) := by
    rw [mem_fixV]
    intro x hx
    have h := hbfix
    rw [MulAction.mem_fixedPoints] at h
    have hx' := h ⟨x, hx⟩
    rw [Subgroup.smul_def] at hx'
    rwa [MulAut.smul_def] at hx'
  have hne' : (⟨(1 : ↥V), h1V⟩ : ↥(fixV (autSub P V))) ≠ ⟨b, hbV⟩ := by
    intro h
    exact hne (Subtype.ext_iff.mp h)
  haveI : Nontrivial ↥(fixV (autSub P V)) := ⟨_, _, hne'⟩
  have h2 : 2 ≤ Nat.card ↥(fixV (autSub P V)) := by
    have := Finite.one_lt_card_iff_nontrivial.mpr
      (inferInstance : Nontrivial ↥(fixV (autSub P V)))
    omega
  rw [← map_subtype_fixV_autSub hPs, Subgroup.card_map_of_injective V.subtype_injective]
  exact h2

theorem s16c167_norm_card_inf_fixV_le_two (hW : ∀ w : W, w ^ 2 = 1) {V : Subgroup W}
    (hc : Nat.card ↥V = 8) {P : Subgroup (MulAut W)} (hP : Nat.card ↥P = 8)
    (hPV : ∀ g ∈ P, ∀ v ∈ V, g v ∈ V) (hfaith : ∀ g ∈ P, (∀ v ∈ V, g v = v) → g = 1) :
    Nat.card ↥(V ⊓ fixV P) ≤ 2 := by
  have hPs : P ≤ stabSub V := le_stabSub_of_inv hPV
  have hcent : P ⊓ centSub V = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact Subgroup.mem_bot.2 (hfaith g hg.1 hg.2)
  have hcardAut : Nat.card ↥(autSub P V) = 8 := by
    have h := card_autSub_mul hPs
    rw [hcent, Subgroup.card_bot, mul_one, hP] at h
    exact h
  have hE : CFSG.OddStandard.HigherRank.G2Three.Sec1.IsE 3 ↥V := by
    refine CFSG.OddStandard.HigherRank.YamadaG23.y7c_isE_of_isElemAbelian (G := W) (W := V)
      ⟨IsMulCommutative.of_comm (fun x y => Subtype.ext (mul_comm x.1 y.1)), fun x _ => hW x⟩ ?_
    rw [hc]; norm_num
  have h := CFSG.OddStandard.HigherRank.YamadaG23.y7c_mulAut_fix_le_two hE (autSub P V) hcardAut
  rw [← map_subtype_fixV_autSub hPs, Subgroup.card_map_of_injective V.subtype_injective]
  exact h

theorem s16c167_norm_card_inf_fixV_eq_two (hW : ∀ w : W, w ^ 2 = 1) {V : Subgroup W}
    (hc : Nat.card ↥V = 8) {P : Subgroup (MulAut W)} (hP : Nat.card ↥P = 8)
    (hPV : ∀ g ∈ P, ∀ v ∈ V, g v ∈ V) (hfaith : ∀ g ∈ P, (∀ v ∈ V, g v = v) → g = 1) :
    Nat.card ↥(V ⊓ fixV P) = 2 :=
  le_antisymm (s16c167_norm_card_inf_fixV_le_two hW hc hP hPV hfaith)
    (s16c167_norm_two_le_card_inf_fixV hc hP hPV)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
