module

public import CFSG.Quasithin.Background.SmithB51LnSec
public import CFSG.Quasithin.Background.B4HypCore
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix

theorem card_statedSL_four : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem card_statedSL_four_five {n : ℕ} (hn : n = 4 ∨ n = 5) :
    Nat.card ↥(StatedSL n (ZMod 2)) = 20160 ∨ Nat.card ↥(StatedSL n (ZMod 2)) = 9999360 := by
  rcases hn with rfl | rfl
  · exact Or.inl card_statedSL_four
  · exact Or.inr card_statedSL_five

theorem card_statedSL_three (K : Type) [Field K] [Fintype K] :
    Nat.card ↥(StatedSL 3 K) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 3 - 1) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_three, Nat.card_eq_fintype_card, mul_assoc]

theorem card_statedSp_two (K : Type) [Field K] [Finite K] :
    Nat.card ↥(StatedSp 2 K) = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K

theorem not_equiv_sl3 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) {n : ℕ}
    (hn : n = 4 ∨ n = 5) : ¬ Nonempty (↥(StatedSL 3 K) ≃* ↥(StatedSL n (ZMod 2))) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  have := Fintype.ofFinite K
  rw [card_statedSL_three, ← Nat.card_eq_fintype_card, hK] at hc
  have hne : m ≠ 0 := by
    rintro rfl
    have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
    omega
  have hval := card_statedSL_four_five hn
  rw [← hc] at hval
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;> norm_num at hval
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    set q := 2 ^ m
    have hq2' : 64 ≤ q ^ 2 := by nlinarith
    have hq3' : 512 ≤ q ^ 3 := by nlinarith
    have : 512 * 63 * 511 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq3' (by omega)) (by omega)
    rcases hval with hval | hval <;> omega

theorem card_sp4_ne {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) :
    (m = 1 → Nat.card ↥(StatedSp 2 K) = 720) ∧
      Nat.card ↥(StatedSp 2 K) ≠ 20160 ∧ Nat.card ↥(StatedSp 2 K) ≠ 9999360 := by
  rw [card_statedSp_two, hK]
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · interval_cases m <;> norm_num
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h3
    set q := 2 ^ m
    have hq2 : 64 ≤ q ^ 2 := by nlinarith
    have hq4 : 4096 ≤ q ^ 4 := by nlinarith
    have : 4096 * (63 * 4095) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul hq4 (Nat.mul_le_mul (by omega) (by omega))
    refine ⟨fun h => by omega, by omega, by omega⟩

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem le_ffJ_of_center_core (hB : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (hA : IsFFStarOffender G A) : L ≤ ffJ G := by
  obtain ⟨hLF, hq, -⟩ := hB
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hHG : ffJ G ≤ G := B6.ffJ_le G
  have hGH : G ≤ Subgroup.normalizer ((ffJ G) : Set (MulAut V)) := B6.le_normalizer_ffJ G
  have hqo := B1Red.isQuasisimple_to_open hq
  by_contra hLH
  have hcomm := B1Red.commute_of_normal_not_le hqo
    (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hGL (hHG hx)) l).mp hl)
    (fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hGH (hLG hl)) x).mp hx) hLH
  have hHL : ∀ x ∈ ffJ G, x = 1 := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcomm x hx l hl).symm
    have hxL : x ∈ L := hLF ▸ centralizer_quasithinGenFitting_le G ⟨hHG hx, hLF ▸ hxC⟩
    have hz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcomm x hx l l.2).symm
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.2.1
  exact ha1 (Subtype.ext (hHL a.1 (B6.le_ffJ hA a.2)))

theorem le_ffJ_of_center (hB : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hA : IsFFStarOffender G A) : L ≤ ffJ G :=
  le_ffJ_of_center_core hB.core hZ hA

theorem b42_ln (hHyp : B4Hyp G L) (hA : IsFFStarOffender G A) (hc : B42Conclusion G L A) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) :
    B42Case9 G L ∨
      (((3 / 4 : ℚ) : WithTop ℚ) ≤ qOf G ∧ (n = 5 → ((1 : ℚ) : WithTop ℚ) ≤ qOf G)) := by
  have hcardL : Nat.card ↥L = 20160 ∨ Nat.card ↥L = 9999360 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_statedSL_four_five hn
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) e
  have one : ((3 / 4 : ℚ) : WithTop ℚ) ≤ ((1 : ℚ) : WithTop ℚ) := WithTop.coe_le_coe.2 (by norm_num)
  have hq1 : qOf G = ((1 : ℚ) : WithTop ℚ) →
      B42Case9 G L ∨ (((3 / 4 : ℚ) : WithTop ℚ) ≤ qOf G ∧
        (n = 5 → ((1 : ℚ) : WithTop ℚ) ≤ qOf G)) :=
    fun hq => Or.inr ⟨hq ▸ one, fun _ => hq.ge⟩
  rcases hc with ⟨-, -, -, hq⟩ | ⟨-, ⟨m, hm⟩, -⟩ | ⟨⟨m, hm, hmL⟩, -⟩ | ⟨-, hq⟩ | ⟨-, hq⟩ |
    ⟨-, -, -, hq, -⟩ | ⟨-, -, -, -, hq, -⟩ | ⟨-, -, hq, -⟩ | h9 |
    ⟨hext, ⟨-, -, -, hq⟩ | ⟨-, -, hq⟩⟩ | ⟨-, -, -, hq, -⟩
  · exact hq1 hq
  ·
    exfalso
    obtain ⟨K, hKf, hKfin, hK, ⟨f⟩⟩ := BinaryNaturalSL.exists_equiv hm
    exact not_equiv_sl3 hK hn ⟨f.trans e⟩
  ·
    exfalso
    obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hm
    have hinj := hπ.injective_of_faithful (FFModel.nat_faithful _)
    have hJ : Nat.card ↥(ffJ G) = Nat.card ↥(StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hm1 : 1 ≤ m := by
      by_contra h0
      have : m = 0 := by omega
      subst this
      have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
      rw [hK] at this
      simp at this
    obtain ⟨h720, hne1, hne2⟩ := card_sp4_ne hK hm1
    rcases Nat.lt_or_ge 1 m with hlt | hle
    · have hJL := hmL hlt
      rw [hJL] at hJ
      rcases hcardL with h | h <;> omega
    · have hm1' : m = 1 := by omega
      have hLJ := le_ffJ_of_center hHyp hZ hA
      have hle' : Nat.card ↥L ≤ Nat.card ↥(ffJ G) := Subgroup.card_le_of_le hLJ
      rw [hJ, h720 hm1'] at hle'
      rcases hcardL with h | h <;> omega
  · exact hq1 hq
  · exact hq1 hq
  · exact hq1 hq
  · exact hq1 hq
  · exact hq1 hq
  · exact Or.inl h9
  · exact hq1 hq
  ·
    refine Or.inr ⟨hq.ge, fun h5 => ?_⟩
    exfalso
    obtain ⟨π, hπ⟩ := hext
    have hle : Nat.card ↥L ≤ Nat.card ↥(StatedSL 4 (ZMod 2)) :=
      Nat.card_le_card_of_surjective _ hπ.1
    rw [card_statedSL_four, Nat.card_congr e.toEquiv, h5, card_statedSL_five] at hle
    omega
  · exact hq1 hq

end CFSG.Quasithin.B5.Ln
