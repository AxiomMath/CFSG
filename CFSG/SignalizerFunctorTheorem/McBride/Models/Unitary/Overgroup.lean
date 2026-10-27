module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.FixedData
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Bender
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Reduction
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Section
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.NearSolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

structure HeisenbergInput (p : ℕ) : Prop where
  centralizer_eq : ∀ P : Subgroup (PSU3 2 p), IsElemAbelian 3 P → Nat.card P = 9 →
    Subgroup.centralizer (P : Set (PSU3 2 p)) = P
  card_normalizer_dvd : ∀ P : Subgroup (PSU3 2 p), IsElemAbelian 3 P → Nat.card P = 9 →
    Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) ∣ 72
  not_normalizes : ∀ P C : Subgroup (PSU3 2 p), IsElemAbelian 3 P → Nat.card P = 9 → P ≤ C →
    C ≤ Subgroup.normalizer (P : Set (PSU3 2 p)) →
    (∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y) →
    ∀ N : Subgroup (PSU3 2 p), N ≠ ⊥ → Nat.Coprime (Nat.card N) 6 →
      ¬ C ≤ Subgroup.normalizer (N : Set (PSU3 2 p))

variable {p : ℕ} {C P : Subgroup (PSU3 2 p)}

theorem FixedData.isElemAbelian (h : FixedData C P) : IsElemAbelian 3 P :=
  ⟨Order72.isMulCommutative_of_card_nine P h.card_P, h.pow_three⟩

theorem FixedData.le_normalizer (h : FixedData C P) :
    C ≤ Subgroup.normalizer (P : Set (PSU3 2 p)) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h.normalizes c hc x hx, fun hx => ?_⟩
  have := h.normalizes c⁻¹ (C.inv_mem hc) _ hx
  simpa [mul_assoc] using this

theorem FixedData.normalizer_eq (h : FixedData C P) (inp : HeisenbergInput p) :
    Subgroup.normalizer (P : Set (PSU3 2 p)) = C := by
  have hdvd := inp.card_normalizer_dvd P h.isElemAbelian h.card_P
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  exact (Subgroup.eq_of_le_of_card_ge h.le_normalizer (by rw [h.card_C]; exact hle)).symm

theorem not_twentyseven_dvd_card_psu3 (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ 27 ∣ Nat.card (PSU3 2 p) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [card_psu3_of_odd hodd]
  exact not_twentyseven_dvd_psu3 (two_pow_mod_nine (prime_mod_six hp hp2 hp3))

theorem eq_of_le_psu3
    (hp : p.Prime) (h5 : 5 ≤ p)
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (inp : HeisenbergInput p)
    (hF : FixedData C P) {H : Subgroup (PSU3 2 p)} (hCH : C ≤ H) (hH : H ≠ ⊤) : H = C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPle : P ≤ H := hF.le.trans hCH
  have hNP : Subgroup.normalizer (P : Set (PSU3 2 p)) = C := hF.normalizer_eq inp
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hF.card_C]; norm_num)
  have hu2 : orderOf (u : PSU3 2 p) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hzp : IsPGroup 2 (Subgroup.zpowers (u : PSU3 2 p)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hSE := (bender_psu3_borel_full p hp.two_le Q).1
  have h3H : 3 ∣ Nat.card H :=
    (show 3 ∣ 72 by norm_num).trans (hF.card_C ▸ Subgroup.card_dvd_of_le hCH)
  have hHB : ¬ H ≤ Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set (PSU3 2 p)) := fun hle =>
    UnitaryFrame.not_three_dvd_card_normalizer_sylow_two hp h5 Q
      (h3H.trans (Subgroup.card_dvd_of_le hle))
  have hev : ∃ v ∈ H ⊓ Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set (PSU3 2 p)),
      orderOf v = 2 :=
    ⟨u, ⟨hCH u.2, Subgroup.le_normalizer (hQ (Subgroup.mem_zpowers _))⟩, hu2⟩
  have hSEH := fusionStronglyEmbedded_inf_subgroupOf hSE hHB hev
  rcases bender_strongly_embedded_normal_series ↥H _ hSEH with
    hS | ⟨M, N, hM, hN, hMN', -, hMo, hNo, hBender⟩
  ·
    have hP9 : Nat.card (P.subgroupOf H) = 9 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv).trans hF.card_P
    have hindex : ¬ 3 ∣ (P.subgroupOf H).index := by
      intro h3
      have hmul := (P.subgroupOf H).card_mul_index
      rw [hP9] at hmul
      apply not_twentyseven_dvd_card_psu3 hp h5
      obtain ⟨j, hj⟩ := h3
      refine (Dvd.intro j ?_).trans (Subgroup.card_subgroup_dvd_card H)
      rw [← hmul, hj]
      ring
    let P' : Sylow 3 ↥H := (IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num) :
      IsPGroup 3 (P.subgroupOf H)).toSylow hindex
    have hP'eq : (P' : Subgroup ↥H) = P.subgroupOf H := rfl
    have hC' : C.subgroupOf H = ⊤ := by
      refine eq_top_of_sylow_two_cyclic_or_quaternion (C.subgroupOf H) P' ?_ ?_ ?_ ?_ ?_ ?_ hS
      · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv).trans hF.card_C
      · rw [hP'eq]
        exact fun x hx => hF.le hx
      · rw [hP'eq]
        exact hP9
      · rw [hP'eq, ← Subgroup.subgroupOf_normalizer_eq hPle, hNP]
      · intro x t ht hxt
        have := not_three_dvd_orderOf_of_commute_involution hp h5 (x := (x : PSU3 2 p))
          (t := (t : PSU3 2 p)) (by rwa [Subgroup.orderOf_coe]) (congrArg Subtype.val hxt)
        rwa [Subgroup.orderOf_coe] at this
      · intro N' hN' hcop hCnorm
        have hCnorm' : C ≤ Subgroup.normalizer ((N'.map H.subtype : Subgroup (PSU3 2 p)) :
            Set (PSU3 2 p)) := by
          intro c hc
          have hcH : (⟨c, hCH hc⟩ : H) ∈ Subgroup.normalizer (N' : Set ↥H) := hCnorm hc
          exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hcH)
        refine inp.not_normalizes P C hF.isElemAbelian hF.card_P hF.le hF.le_normalizer hF.trans
          (N'.map H.subtype) ?_ ?_ hCnorm'
        · intro hbot
          exact hN' ((Subgroup.map_eq_bot_iff_of_injective N' H.subtype_injective).mp hbot)
        · rwa [Subgroup.card_map_of_injective H.subtype_injective]
    exact le_antisymm (fun x hx => by
      have : (⟨x, hx⟩ : H) ∈ C.subgroupOf H := by rw [hC']; trivial
      exact this) hCH
  ·
    exfalso
    obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 (n := 3)
      (by rw [hF.card_C]; norm_num)
    have hTle : T.map C.subtype ≤ C := Subgroup.map_subtype_le T
    have hTcard : Nat.card (T.map C.subtype) = 8 := by
      rw [Subgroup.card_map_of_injective C.subtype_injective, hT]
      norm_num
    obtain ⟨x, hx, hx2⟩ := hF.exists_sq_ne_one _ hTle hTcard
    apply hx2
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have hxH : (t : PSU3 2 p) ∈ H := hCH t.2
    have h1 : (t : PSU3 2 p) ^ 2 ^ 3 = 1 := by
      have hd : orderOf (t : PSU3 2 p) ∣ 2 ^ 3 := by
        have := Subgroup.orderOf_dvd_natCard T ht
        rwa [hT, ← Subgroup.orderOf_coe] at this
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have ht8 : (⟨(t : PSU3 2 p), hxH⟩ : H) ^ 2 ^ 3 = 1 := Subtype.ext (by simpa using h1)
    have := sq_eq_one_of_isBenderSection hp h5 hnear hH (M := M) (N := N) hMo hNo hBender ht8
    exact congrArg Subtype.val this

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
