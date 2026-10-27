module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3SL
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3SU

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def L143NoConfig : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionFourHyp Y → IsQuasisimple Y →
    IsPGroup 3 (Subgroup.center Y) → ∀ a w : Y, ¬ L143Config a w

@[expose] def L143RowsK : Prop :=
  (∀ (T : Type) [Group T], Nonempty (T ≃* alternatingGroup (Fin 6)) → L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* alternatingGroup (Fin 7)) → L143Rows T) ∧
    (∀ (T : Type) [Group T] [Finite T], Blueprint.ChevalleyExceptionalModel T .G2 3 1 →
      L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* projSU 4 3 1) → L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* Blueprint.NativeSporadic.M22) → L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* Blueprint.NativeSporadic.J3) → L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* Blueprint.NativeSporadic.McL) → L143Rows T) ∧
    (∀ (T : Type) [Group T], Nonempty (T ≃* Blueprint.NativeSporadic.ON) → L143Rows T)

private theorem not_l143Config_of_isSLThreeEpsAt (heig : L143EigProp) {Y : Type} [Group Y]
    {p e : ℕ} [Fact p.Prime] (hY : Sec4.IsSLThreeEpsAt Y (p ^ e)) (a w : Y) :
    ¬ L143Config a w := by
  intro h
  obtain ⟨K, _, _, ⟨-, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hY
  · exact not_l143Config_statedSL heig (φ a) (φ w) (h.map φ)
  · exact not_l143Config_statedSU heig hK (φ a) (φ w) (h.map φ)

theorem l143NoConfig_of (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (heig : L143EigProp) (hK : L143RowsK) : L143NoConfig := by
  intro Y _ _ hY hq hZ3 a w h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (Subgroup.center Y) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center Y) h.w_mem
    rwa [h.orderOf_w] at this
  have hZ : Subgroup.center Y ≠ ⊥ := fun h0 => h.w_ne (by
    have := h.w_mem
    rwa [h0, Subgroup.mem_bot] at this)
  have hodd : Odd (Nat.card (Subgroup.center Y)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ3
    rw [hn]
    exact Odd.pow (by decide)
  obtain ⟨hA6, hA7, hG2, hU43, hM22, hJ3, hMcL, hON⟩ := hK
  rcases h43 Y hY hq h3 with ⟨p, e, _, he, hpi⟩ | hX | hX | hG | hX | hX | hX | hX | hX
  · have hS : SectionFourHyp (Y ⧸ Subgroup.center Y) :=
      Sec4.Item41Narrow.sectionFourHyp_quotient_center_of_isPGroup h2 hY hq hZ3
    have hbd := Sec4.Census.two_or_le_two_of_isoLThreePi hS he hpi
    exact not_l143Config_of_isSLThreeEpsAt heig (hin.slThree Y hq hZ3 hZ p e he hbd hpi) a w h
  · exact h.false_of_rows hodd (hA6 _ hX)
  · exact h.false_of_rows hodd (hA7 _ hX)
  · exact h.false_of_rows hodd (hG2 _ hG)
  · exact h.false_of_rows hodd (hU43 _ hX)
  · exact h.false_of_rows hodd (hM22 _ hX)
  · exact h.false_of_rows hodd (hJ3 _ hX)
  · exact h.false_of_rows hodd (hMcL _ hX)
  · exact h.false_of_rows hodd (hON _ hX)

theorem L143Config.exists_of_point {Y : Type*} [Group Y] [Finite Y]
    (hZ : Nat.card (Subgroup.center Y) = 3) {x : Y} (hx3 : x ^ 3 = 1)
    (hxZ : x ∉ Subgroup.center Y)
    (hc : ∀ u : Y, u * x = x * u → u ^ 3 = 1 → u ∈ Subgroup.zpowers x ⊔ Subgroup.center Y)
    (hf : ∀ z ∈ Subgroup.center Y, ∀ g : Y, g * x * g⁻¹ = x * z → z = 1) :
    ∃ w : Y, L143Config x w := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain h0 | ⟨w, hw, hw1⟩ := (Subgroup.center Y).bot_or_exists_ne_one
  · rw [h0, Subgroup.card_bot] at hZ
    norm_num at hZ
  have hw3 : w ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center Y) hw
    rw [hZ] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hZw : Subgroup.center Y = Subgroup.zpowers w :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
      (le_of_eq (by rw [hZ, Nat.card_zpowers, orderOf_eq_prime hw3 hw1]))).symm
  refine ⟨w, ⟨hw, hw1, hw3, hx3, hxZ, fun u hux hu3 => ?_, fun g hg => hw1 (hf w hw g hg)⟩⟩
  have hu := hc u hux hu3
  rw [← SetLike.mem_coe, Subgroup.mul_normal, hZw] at hu
  obtain ⟨h, hh, n, hn, rfl⟩ := Set.mem_mul.mp hu
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hh)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hn)
  exact ⟨i, j, rfl⟩

theorem L143NoConfig.false_of_point (hN : L143NoConfig) {Y : Type} [Group Y] [Finite Y]
    (hY : SectionFourHyp Y) (hq : IsQuasisimple Y) (hZ : Nat.card (Subgroup.center Y) = 3)
    {x : Y} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center Y)
    (hc : ∀ u : Y, u * x = x * u → u ^ 3 = 1 → u ∈ Subgroup.zpowers x ⊔ Subgroup.center Y)
    (hf : ∀ z ∈ Subgroup.center Y, ∀ g : Y, g * x * g⁻¹ = x * z → z = 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := L143Config.exists_of_point hZ hx3 hxZ hc hf
  exact hN Y hY hq (IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])) x w hw

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
