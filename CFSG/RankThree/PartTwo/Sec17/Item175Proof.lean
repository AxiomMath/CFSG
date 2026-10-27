module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec17.Item175ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec17

@[expose] noncomputable def Item1511S17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1511 A (lB A) c L

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

namespace Proof175

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem setup_of_prod (h : Sec17Std G A c L Y₀)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥) :
    c ∉ L ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      ∃ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) ∧ A ≤ T ∧
        T ≤ Subgroup.normalizer (L : Set G) ∧ IsSylowOf 3 (T ⊓ L) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine_of_prod h hprod
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine h.c_pow_three
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
    (fun b hb => h.isE27.1.2 b hb.1) (fun b hb => h.commute_of_mem h.c_mem hb.1)).2
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.c_mem) inf_le_left
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [h.isE27.2, hcard])).symm
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hCL := Sec15R.centralizer_le_normalizer_L h.toSec15R h3L
  obtain ⟨T, hT, hAT⟩ := Item134SylowBarProof.exists_isSylowOf_le
    h.toSec13Data.A_le_centralizer h.isE27.isPGroup
  exact ⟨hcL, hAeq, T, hT, hAT, hT.le.trans hCL, hT.inf_of_le_normalizer h.le_centralizer_c hCL⟩

theorem item175_of_j2 (h : Sec17Std G A c L Y₀)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Item175 A c := by
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨φJ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  obtain ⟨hcL, hAeq, T, hT, hAT, hTL, hS⟩ := setup_of_prod h hprod hZ
  obtain ⟨hi, hii⟩ := sylow_facts_of_j2 hJ h.isE27 h.mem_partTwoF hAeq h.le_centralizer_c hcL
    h.toSec13Data.orderOf_eq hT hAT hTL hS
  exact item175_of_sylow h.toSec13Data.orderOf_eq h.isE27 hT hi hii

theorem item175_of_a7m22 (hA7 : KFacts.KS18A7M22) (h : Sec17Std G A c L Y₀)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Item175 A c := by
  obtain ⟨hZ, hinn, hel⟩ := a7m22_facts hA7 hL
  obtain ⟨-, hAeq, T, hT, hAT, hTL, hS⟩ := setup_of_prod h hprod hZ
  have hdec := fun x hx hx3 => exists_zpow_mul_of_pow_eq_one hZ hinn h.mem_partTwoF hAeq
    h.le_centralizer_c hT.isPGroup hAT hT.le hTL hS (x := x) hx hx3
  obtain ⟨hab, hexp⟩ := hel (T ⊓ L) inf_le_right (hT.isPGroup.to_le inf_le_left)
  have hle := inf_le_of_exponent h.mem_partTwoF hAeq hAT h.c_pow_three h.le_centralizer_c hab hexp
  obtain ⟨hi, hii⟩ := sylow_facts_of_inf_le h.isE27 h.c_mem hdec hle
  exact item175_of_sylow h.toSec13Data.orderOf_eq h.isE27 hT hi hii

theorem item175_of_lThreePi (h : Sec17Std G A c L Y₀) (h1511 : Item1511 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) : Item175 A c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := h.toSec13Data.orderOf_eq
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
  have hCle : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y₀ : Set G) :=
    le_inf hCH (hCH.trans h.normalizer_c_le)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le
    (h.toSec13Data.A_le_centralizer.trans hCle) h.isE27.isPGroup
  have hAeq : A = omegaOneThree P :=
    (h1511 p e he hiso Y₀ h.mem_y0Star.prop hMeets P hAP hP).2.2.2.2
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    obtain ⟨n, hn⟩ := hP.isPGroup ⟨x, hx⟩
    exact mem_centralizer_of_mem_normalizer hc (Subgroup.mem_inf.mp (hP.le hx)).1
      (by simpa using congrArg Subtype.val hn)
  have hPS : IsSylowOf 3 P (Subgroup.centralizer ({c} : Set G)) := hP.of_le hPC hCle
  obtain ⟨hi, hii⟩ := sylow_facts_of_eq_omegaOneThree (c := c) h.isE27 hAeq
  exact item175_of_sylow hc h.isE27 hPS hi hii

end Proof175

section Item175

variable {G : Type} [Group G] [Finite G]

theorem Proof175.prod_of_item1514 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c}) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨-, -, -, hprod, hM12⟩ | ⟨-, -, htr, -⟩ |
      ⟨-, -, -, -, hno, -⟩
  · exact ⟨hprod, hM12⟩
  · have h3 := htr.1
    rw [hΩ, Set.ncard_singleton] at h3
    omega
  · exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

open Proof175 in
theorem rank3II_17_5_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀)
    (h1511 : Item1511 A (lB A) c L) (hA7 : KFacts.KS18A7M22) : Item175 A c := by
  intro hΩ
  obtain ⟨hprod, hM12⟩ := prod_of_item1514 h h1514 hMeets hΩ
  rcases (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with hJ | ⟨p, e, hp, he, hiso⟩ |
      hA7' | hM22 | hM12'
  · exact item175_of_j2 h hprod hJ hΩ
  · have := hp
    exact item175_of_lThreePi h h1511 hMeets he hiso hΩ
  · exact item175_of_a7m22 hA7 h hprod (Or.inl hA7') hΩ
  · exact item175_of_a7m22 hA7 h hprod (Or.inr hM22) hΩ
  · exact (hM12.false hM12'.some).elim

theorem item175R_of (h169 : Item169R) (h163 : Item163R) (h164 : Item164R) (hM : Claim17MR)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h1511 : Item1511S17)
    (hA7 : KFacts.KS18A7M22) : Item175R := by
  intro G _ _ A c L hR
  obtain ⟨Y₀, h0⟩ := exists_sec17Std hR (h169 G A c L hR) (h163 G A c L hR) (h164 G A c L hR)
    (hM G A c L hR)
  exact rank3II_17_5_of h0 (h1514 G A c L Y₀ h0) (hMeets G A c L Y₀ h0) (h1511 G A c L Y₀ h0)
    hA7

end Item175

end CFSG.RankThree.PartTwo.Sec17
