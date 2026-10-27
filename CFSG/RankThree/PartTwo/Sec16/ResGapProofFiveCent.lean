module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofCUL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fix_of_centralizer {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {b : G} {p : ℕ}
    {P : Subgroup G} (hD : Data1619 A c L b 4 p P) (h1623 : Step1623) {X : Subgroup G}
    (hXL : X ≤ L) (hX5 : Nat.card X = 5)
    {d : G} (hd : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b) (hdc : d ∉ Subgroup.zpowers c)
    {U : Subgroup G} (hUd : U ≤ Subgroup.centralizer ({d} : Set G)) (hU2 : IsPGroup 2 U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    ∀ u ∈ U, c * u * c⁻¹ = u → ∀ y ∈ X, y * u * y⁻¹ = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m', -, ⟨φL⟩⟩ := h1623 G A c L h
  have hLsimp : IsSimpleGroup ↥L := by
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 m')
    exact φL.isSimpleGroup
  have hLiso : Sec4.IsoLThreePi ↥L 2 4 :=
    Proof1617.isoLThreePi_of_isSimpleGroup hLsimp (by norm_num) hD.isZ3.2.1
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Proof1617.centralizer_le_normalizer_L h hD.isZ3
  have hdA : d ∈ A :=
    (sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr hD.mem_A)) hd
  have h9b : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    Sec13.card_zpowers_sup_zpowers_eq_nine h.isElemAbelian h.card_eq hD.mem_A h.mem_A h.ne_one
      hD.not_mem
  have h9d : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    Sec13.card_zpowers_sup_zpowers_eq_nine h.isElemAbelian h.card_eq hdA h.mem_A h.ne_one hdc
  have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤
      Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    sup_le (Subgroup.zpowers_le.mpr (by rw [sup_comm]; exact hd)) le_sup_right
  have heq : Subgroup.zpowers d ⊔ Subgroup.zpowers c =
      Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h9b, h9d])
  have hbdc : b ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c :=
    heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hCb : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer ({b} : Set G) :=
    Proof169.inf_centralizer_le_of_mem_sup hbdc
  set W := U ⊓ Subgroup.centralizer ({c} : Set G) with hW
  have hW2 : IsPGroup 2 W := hU2.to_le inf_le_left
  have hWb : W ≤ Subgroup.centralizer ({b} : Set G) := fun w hw => hCb ⟨hUd hw.1, hw.2⟩
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := hXL.trans h.le_centralizer
  have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
    Proof169.le_normalizer_inf hXU (hXc.trans Subgroup.le_normalizer)
  set W₁ := ⁅W, X⁆ with hW₁
  have hW₁W : W₁ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hcop : ¬ 5 ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : (5 : ℕ).Prime).dvd_of_dvd_pow hdvd)
    omega
  have hX5' : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by rw [hX5, pow_one])
  have hW₁X : ⁅W₁, X⁆ = W₁ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5 (by norm_num) X W
      hX5' hcop hXW
  have hW₁L : W₁ ≤ L := by
    rw [← hW₁X, Subgroup.commutator_le]
    intro w hw y hy
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL (hW₁W hw).2) y).mp (hXL hy))
      (inv_mem (hXL hy))
  have hb3 : b ^ 3 = 1 := h.isElemAbelian.2 b hD.mem_A
  have hb1 : b ≠ 1 := fun h1 => hD.not_mem (h1 ▸ Subgroup.one_mem _)
  have hW₁bot : W₁ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hwL := hW₁L hw
    have hwb := hWb (hW₁W hw)
    obtain ⟨k, hk⟩ := hW2 ⟨w, hW₁W hw⟩
    have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := ProofKSL3Two.eq_one_of_commute_two_pow (X := ↥L) (n := 4) (by norm_num)
      (by norm_num) hLiso (d := ⟨b, hD.mem_L⟩) (x := ⟨w, hwL⟩) (Subtype.ext (by simp [hb3]))
      (fun h1 => hb1 (congrArg Subtype.val h1))
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hwb)) (k := k)
      (Subtype.ext (by simp [hwk]))
    exact congrArg Subtype.val h1
  intro u hu hcu y hy
  have huc : u ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * c = (c * u * c⁻¹) * c := by rw [hcu]
      _ = c * u := by group
  have hc : ⁅u, y⁆ ∈ W₁ := Subgroup.commutator_mem_commutator ⟨hu, huc⟩ hy
  rw [hW₁bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  rw [← hc, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec16.ResGapFive
