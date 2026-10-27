module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CentralCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicOddQuotientLift

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.StandardType

variable {U Y : Type} [Group U] [Finite U] [Group Y] [Finite Y]

omit [Finite U] [Finite Y] in
private theorem sq_lift_unique (π : U →* Y) (hker : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) {a b : U} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : π a = π b) : a = b := by
  by_cases ha1 : a = 1
  · have hbker : b ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← h, ha1, map_one]
    subst ha1
    exact (CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.kernel_square_one π hodd hbker hb).symm
  · have hb1 : b ≠ 1 := by
      intro hb1
      have haker : a ∈ π.ker := by
        rw [MonoidHom.mem_ker, h, hb1, map_one]
      exact ha1 (CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.kernel_square_one π hodd haker ha)
    exact CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.involution_lifts_injective π hker hodd
      (orderOf_eq_prime ha ha1) (orderOf_eq_prime hb hb1) h

omit [Finite U] [Finite Y] in
private theorem exists_sq_lift (π : U →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {y : Y} (hy : y ^ 2 = 1) : ∃ x : U, x ^ 2 = 1 ∧ π x = y := by
  by_cases hy1 : y = 1
  · exact ⟨1, by simp, by simp [hy1]⟩
  · obtain ⟨x, hxord, hxπ⟩ :=
      CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.exists_involution_lift π hπ hker hodd
        (orderOf_eq_prime hy hy1)
    exact ⟨x, (orderOf_eq_prime_iff.mp hxord).1, hxπ⟩

theorem fourAt_map_of_odd_central_ker (π : U →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {V : Subgroup U} {r : U} (h : FourAt (⊤ : Subgroup U) V r) :
    FourAt (⊤ : Subgroup Y) (V.map π) (π r) := by
  obtain ⟨hrV, _, hVab, hVcard, hr1, hVconj⟩ := h
  have hdisj : V ⊓ π.ker = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx2 : x ^ 2 = 1 := hVab.2 x hx.1
    have hx1 : x = 1 :=
      CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.kernel_square_one π hodd hx.2 hx2
    simpa using hx1
  have hinj : Set.InjOn π (V : Set U) := by
    intro a ha b hb hab
    exact sq_lift_unique π hker hodd (hVab.2 a ha) (hVab.2 b hb) hab
  have hcardmap : Nat.card (V.map π) = Nat.card V := by
    have hcoe : ((V.map π : Subgroup Y) : Set Y) = π '' (V : Set U) := Subgroup.coe_map π V
    calc
      Nat.card (V.map π) = Nat.card (π '' (V : Set U)) := by rw [← hcoe]; rfl
      _ = Nat.card (V : Set U) := Nat.card_image_of_injOn hinj
      _ = Nat.card V := rfl
  have : Fintype V := Fintype.ofFinite V
  have : Fintype (V.map π) := Fintype.ofFinite (V.map π)
  have hcardFT : Fintype.card (V.map π) = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardmap
  have hVFT : Fintype.card V = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hVcard
  have hcard4 : Nat.card (V.map π) = 4 := by
    rw [Nat.card_eq_fintype_card, hcardFT, hVFT]
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
  refine ⟨Subgroup.mem_map_of_mem π hrV, ?_, hVab.map π, hcard4, ?_, ?_⟩
  · rw [← hrange]
    exact Subgroup.map_le_range π V
  · intro h1
    have hmem : r ∈ V ⊓ π.ker := ⟨hrV, h1⟩
    rw [hdisj] at hmem
    exact hr1 (by simpa using hmem)
  · intro y hy hy1
    obtain ⟨v, hvV, rfl⟩ := Subgroup.mem_map.mp hy
    have hv1 : v ≠ 1 := by
      intro hv1
      exact hy1 (by rw [hv1, map_one])
    obtain ⟨j, _, hvj⟩ := hVconj v hvV hv1
    refine ⟨π j, Subgroup.mem_top _, ?_⟩
    simpa only [map_mul, map_inv] using congrArg π hvj

theorem coreCommAt_map_of_odd_central_ker (π : U →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {V : Subgroup U} {r : U} (hr : r ^ 2 = 1) (h : CoreCommAt (⊤ : Subgroup U) V r) :
    CoreCommAt (⊤ : Subgroup Y) (V.map π) (π r) := by
  intro v hv y hy
  obtain ⟨vU, hvU, rfl⟩ := Subgroup.mem_map.mp hv
  have hy' : y ∈ pCoreOf 2 (Subgroup.centralizer ({π r} : Set Y)) := by
    simpa only [top_inf_eq] using hy
  rw [← map_involution_centralizer_pCoreOf_of_odd_central_ker π hπ hker hodd hr] at hy'
  obtain ⟨yU, hyU, rfl⟩ := Subgroup.mem_map.mp hy'
  have hyU' : yU ∈ pCoreOf 2 (⊤ ⊓ Subgroup.centralizer ({r} : Set U)) := by
    simpa only [top_inf_eq] using hyU
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h vU hvU yU hyU')
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  simpa only [map_mul, map_inv, map_zpow] using congrArg π hk

theorem exists_fourAt_coreCommAt_comap_of_odd_central_ker (π : U →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) {V : Subgroup Y} {r : Y}
    (hFour : FourAt (⊤ : Subgroup Y) V r) (hCore : CoreCommAt (⊤ : Subgroup Y) V r) :
    ∃ (VU : Subgroup U) (rU : U), FourAt (⊤ : Subgroup U) VU rU ∧
      CoreCommAt (⊤ : Subgroup U) VU rU ∧ VU.map π = V ∧ π rU = r := by
  obtain ⟨hrV, _, hVab, hVcard, hr1, hVconj⟩ := hFour
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hVab.2
  have hcomm_sq : ∀ a b : U, a ^ 2 = 1 → b ^ 2 = 1 → π a ∈ V → π b ∈ V →
      a * b = b * a := by
    intro a b ha hb hpa hpb
    have hconj_sq : (b * a * b⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ha, mul_one, mul_inv_cancel]
    have himg : π (b * a * b⁻¹) = π a := by
      rw [map_mul, map_mul, map_inv, hVab.comm hpb hpa]
      group
    have h := sq_lift_unique π hker hodd hconj_sq ha himg
    have h' : b * a = a * b := by
      calc b * a = (b * a * b⁻¹) * b := by group
        _ = a * b := by rw [h]
    exact h'.symm
  let VU : Subgroup U :=
    { carrier := {x | x ^ 2 = 1 ∧ π x ∈ V}
      one_mem' := by simp
      mul_mem' := by
        rintro x y ⟨hx2, hpx⟩ ⟨hy2, hpy⟩
        have hcomm : Commute x y := (commute_iff_eq x y).mpr (hcomm_sq x y hx2 hy2 hpx hpy)
        exact ⟨by rw [hcomm.mul_pow 2, hx2, hy2, mul_one],
          by simpa only [map_mul] using V.mul_mem hpx hpy⟩
      inv_mem' := by
        rintro x ⟨hx2, hpx⟩
        exact ⟨by rw [inv_pow, hx2, inv_one], by simpa using V.inv_mem hpx⟩ }
  have hVU_mem : ∀ x : U, x ∈ VU ↔ x ^ 2 = 1 ∧ π x ∈ V := fun _ => Iff.rfl
  have hVUmap : VU.map π = V := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ((hVU_mem x).mp hx).2
    · intro y hy
      obtain ⟨x, hx2, hxπ⟩ := exists_sq_lift π hπ hker hodd (hV2 y hy)
      exact Subgroup.mem_map.mpr ⟨x, (hVU_mem x).mpr ⟨hx2, by rwa [hxπ]⟩, hxπ⟩
  have hVUinj : Set.InjOn π (VU : Set U) := by
    intro a ha b hb hab
    exact sq_lift_unique π hker hodd ((hVU_mem a).mp ha).1 ((hVU_mem b).mp hb).1 hab
  have hVUcard : Nat.card VU = 4 := by
    have hcoe : ((VU.map π : Subgroup Y) : Set Y) = π '' (VU : Set U) := Subgroup.coe_map π VU
    have hc : Nat.card (VU.map π) = Nat.card VU := by
      calc
        Nat.card (VU.map π) = Nat.card (π '' (VU : Set U)) := by rw [← hcoe]; rfl
        _ = Nat.card (VU : Set U) := Nat.card_image_of_injOn hVUinj
        _ = Nat.card VU := rfl
    rw [← hc, hVUmap, hVcard]
  have hVUab : IsElemAbelian 2 VU := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact hcomm_sq x.1 y.1 ((hVU_mem x.1).mp x.2).1 ((hVU_mem y.1).mp y.2).1
        ((hVU_mem x.1).mp x.2).2 ((hVU_mem y.1).mp y.2).2
    · exact ((hVU_mem x).mp hx).1
  obtain ⟨rU, hrU2, hrUπ⟩ := exists_sq_lift π hπ hker hodd (hV2 r hrV)
  have hrUVU : rU ∈ VU := (hVU_mem rU).mpr ⟨hrU2, by rw [hrUπ]; exact hrV⟩
  have hrU1 : rU ≠ 1 := by
    intro h1
    exact hr1 (by rw [← hrUπ, h1, map_one])
  have hFourVU : FourAt (⊤ : Subgroup U) VU rU := by
    refine ⟨hrUVU, le_top, hVUab, hVUcard, hrU1, ?_⟩
    intro v hv hv1
    have hpvV : π v ∈ V := ((hVU_mem v).mp hv).2
    have hpv1 : π v ≠ 1 := by
      intro h1
      exact hv1 (CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient.kernel_square_one π hodd
        (show v ∈ π.ker from h1) ((hVU_mem v).mp hv).1)
    obtain ⟨y, _, hyconj⟩ := hVconj (π v) hpvV hpv1
    obtain ⟨j, hjπ⟩ := hπ y
    refine ⟨j, Subgroup.mem_top _, ?_⟩
    have hconj_sq : (j * rU * j⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hrU2, mul_one, mul_inv_cancel]
    have himg : π v = π (j * rU * j⁻¹) := by
      rw [map_mul, map_mul, map_inv, hjπ, hrUπ]
      exact hyconj
    exact sq_lift_unique π hker hodd ((hVU_mem v).mp hv).1 hconj_sq himg
  have hCoreVU : CoreCommAt (⊤ : Subgroup U) VU rU := by
    intro vU hvU yU hyU
    have hyU' : yU ∈ pCoreOf 2 (Subgroup.centralizer ({rU} : Set U)) := by
      simpa only [top_inf_eq] using hyU
    have hpy : π yU ∈ pCoreOf 2 (⊤ ⊓ Subgroup.centralizer ({r} : Set Y)) := by
      have hmem : π yU ∈ pCoreOf 2 (Subgroup.centralizer ({π rU} : Set Y)) := by
        rw [← map_involution_centralizer_pCoreOf_of_odd_central_ker π hπ hker hodd hrU2]
        exact Subgroup.mem_map_of_mem π hyU'
      simpa only [top_inf_eq, hrUπ] using hmem
    set c : U := vU * yU * vU⁻¹ * yU⁻¹ with hcdef
    have hπc : π c = π vU * π yU * (π vU)⁻¹ * (π yU)⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    have hpc : π c ∈ Subgroup.zpowers r := by
      rw [hπc]
      exact hCore (π vU) ((hVU_mem vU).mp hvU).2 (π yU) hpy
    have hrord : orderOf r = 2 := orderOf_eq_prime (hV2 r hrV) hr1
    have hcval : π c = 1 ∨ π c = r := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpc
      rw [← hk, ← zpow_mod_orderOf, hrord, Nat.cast_ofNat]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [h, zpow_zero]
      · right
        rw [h, zpow_one]
    set w : U := yU * vU * yU⁻¹ with hwdef
    have hw2 : w ^ 2 = 1 := by
      rw [hwdef, conj_pow, ((hVU_mem vU).mp hvU).1, mul_one, mul_inv_cancel]
    have hπw : π w = (π c)⁻¹ * π vU := by
      rw [hwdef, hπc]
      simp only [map_mul, map_inv]
      group
    have hcw : c = vU * w⁻¹ := by
      rw [hcdef, hwdef]
      group
    rcases hcval with hpc1 | hpc2
    · rw [hcw]
      have hw_eq : w = vU := by
        refine sq_lift_unique π hker hodd hw2 ((hVU_mem vU).mp hvU).1 ?_
        rw [hπw, hpc1, inv_one, one_mul]
      rw [hw_eq]
      simp
    · rw [hcw]
      have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hV2 r hrV)
      have hw_eq : w = rU * vU := by
        refine sq_lift_unique π hker hodd hw2 ?_ ?_
        · have hcomm : Commute rU vU := (commute_iff_eq rU vU).mpr
            (hcomm_sq rU vU hrU2 ((hVU_mem vU).mp hvU).1 (by rw [hrUπ]; exact hrV)
              ((hVU_mem vU).mp hvU).2)
          rw [hcomm.mul_pow 2, hrU2, ((hVU_mem vU).mp hvU).1, mul_one]
        · rw [hπw, hpc2, hrinv, map_mul, hrUπ]
      rw [hw_eq, mul_inv_rev]
      have hc_eq : vU * (vU⁻¹ * rU⁻¹) = rU⁻¹ := by group
      rw [hc_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers rU)
  exact ⟨VU, rU, hFourVU, hCoreVU, hVUmap, hrUπ⟩

end CFSG.StandardType.RCKC1
