module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem Hyp125.eight_le_card_of_bot {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    8 ≤ Nat.card V := by
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · exact hW.1.2.1
  · exact absurd rfl h0.1.1

theorem wClos_le_wClos_of_le {V : Subgroup G} (hV : IsElemAbelian 2 V) {j k : ℕ} (hjk : j ≤ k)
    (hk : k < rk ↥V) (X : Subgroup G) : E3.wClos V j X ≤ E3.wClos V k X :=
  E3.wClos_le_of_forall fun B hB => by
    obtain ⟨hBX, g, hBg, hm⟩ := hB
    exact E3.le_wClos_of_mQuot_le hV g hBX hBg (hm.le.trans hjk) hk

theorem calO2_eq_empty_of_mBarGT (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) {n : ℕ}
    (hn : n ≤ 2) (hm : MBarGT D.M ⊥ V 2) : calO2 n D.M ⊥ V = ∅ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hV2 : IsPGroup 2 V := hV.isPGroup
  refine Set.eq_empty_of_forall_notMem ?_
  rintro X ⟨g, rfl, -, ⟨I, hI, hb⟩, -, -⟩
  obtain ⟨hIX, g', hIg', hmI⟩ := hI
  have hIV : I ≤ V := hIX.trans inf_le_left
  obtain ⟨b, hbmem, hbV⟩ := SetLike.not_le_iff_exists.1 hb
  obtain ⟨⟨hbVg, hbM⟩, hbI⟩ := hbmem
  have hb2 : b * b = 1 := by
    have := (E3.isElemAbelian_conjSubgroup hV g).2 b hbVg
    simpa [pow_two] using this
  have hnc : ¬ CentralizesMod ⊥ V b := by
    intro hc
    apply hbV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := Subgroup.mem_bot.1 (hc v hv)
    have h2 : b * v * b⁻¹ = v := mul_inv_eq_one.1 h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hsq : CentralizesMod ⊥ V (b * b) := by
    intro v hv
    simp [hb2]
  have hle := hm.1 b hbM hnc hsq
  have hsub : (I : Set G) ⊆ centMod ⊥ V b := by
    intro x hx
    refine ⟨hIV hx, ?_⟩
    have hxb : x * b = b * x := Subgroup.mem_centralizer_iff.1 hbI x hx
    rw [Subgroup.mem_bot]
    calc b * x * b⁻¹ * x⁻¹ = x * b * b⁻¹ * x⁻¹ := by rw [← hxb]
      _ = 1 := by simp
  have hcard : Nat.card I ≤ Nat.card (centMod ⊥ V b) := Nat.card_mono (Set.toFinite _) hsub
  have hq : E3.mQuot V I = n := by
    rw [E3.mQuot_conj_eq hV hIV hIg', hmI]
  have hVI := E3.card_eq_two_pow_mul hV2 hIV
  rw [hq] at hVI
  have hpos : 0 < Nat.card I := Nat.card_pos
  have h2n : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 2 ^ (2 + 1) * Nat.card I ≤ 2 ^ n * Nat.card I := by
    calc 2 ^ (2 + 1) * Nat.card I ≤ 2 ^ (2 + 1) * Nat.card (centMod ⊥ V b) :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ Nat.card V := hle
      _ = 2 ^ n * Nat.card I := hVI
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
