module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveAbstract

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadFi22
public import CFSG.Monster.B.Fischer.PinnedChainBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.AGLEmbedding.KFactProofs.Fi22Five

variable {G : Type*} [Group G] [Finite G]

theorem FixedFreeFive.of_conj {x y n : G} (hD : PlaneData x y)
    (hx : n * x * n⁻¹ = x ^ 4 * y) (hy : n * y * n⁻¹ = x * y) :
    FixedFreeFive 5 G := by
  let S : Subgroup G := Subgroup.closure ({x, y} : Set G)
  obtain ⟨hE, hcard, -⟩ := hD.closure_facts
  letI : IsMulCommutative S := hE.1
  have hmemx : x ∈ S := Subgroup.subset_closure (by simp)
  have hmemy : y ∈ S := Subgroup.subset_closure (by simp)
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := S)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hpow : ∀ s ∈ S, s ^ 5 = 1 := hE.2
  have hSq : IsPGroup 5 S := IsPGroup.of_card (n := 2) (by simpa [hcard])
  have hSne : S ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card S = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  have hn : n ∈ Subgroup.normalizer (S : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · rw [hx]
      exact Subgroup.mul_mem S (Subgroup.pow_mem S hmemx 4) hmemy
    · rw [hy]
      exact Subgroup.mul_mem S hmemx hmemy
  have hσx : MulAut.conj n x = x ^ 4 * y := by
    simpa [MulAut.conj_apply] using hx
  have hσy : MulAut.conj n y = x * y := by
    simpa [MulAut.conj_apply] using hy
  have hσmem : ∀ s ∈ S, MulAut.conj n s ∈ S := by
    intro s hs
    have h := (Subgroup.mem_normalizer_iff.1 hn s).1 hs
    simpa [MulAut.conj_apply] using h
  have hσ2x : (MulAut.conj n ^ 2) x = x ^ 2 := by
    rw [pow_two]
    change MulAut.conj n (MulAut.conj n x) = x ^ 2
    rw [hσx, map_mul, map_pow, hσx, hσy]
    rw [Commute.mul_pow (Commute.pow_left hD.comm 4)]
    rw [← pow_mul]
    calc x ^ (4 * 4) * y ^ 4 * (x * y)
        = x ^ (4 * 4) * (y ^ 4 * x) * y := by group
      _ = x ^ (4 * 4) * (x * y ^ 4) * y := by rw [← Commute.pow_right hD.comm 4]
      _ = x ^ (4 * 4) * x * (y ^ 4 * y) := by group
      _ = x ^ (4 * 4 + 1) * y ^ (4 + 1) := by rw [← pow_succ, ← pow_succ]
      _ = x ^ 2 := by
        rw [show 4 * 4 + 1 = 17 by norm_num, show 4 + 1 = 5 by norm_num,
          pow_eq_pow_mod 17 hD.x_pow, show 17 % 5 = 2 by norm_num, hD.y_pow, mul_one]
  have hσ2y : (MulAut.conj n ^ 2) y = y ^ 2 := by
    rw [pow_two]
    change MulAut.conj n (MulAut.conj n y) = y ^ 2
    rw [hσy, map_mul, hσx, hσy]
    calc (x ^ 4 * y) * (x * y)
        = x ^ 4 * (y * x) * y := by group
      _ = x ^ 4 * (x * y) * y := by rw [← hD.comm]
      _ = x ^ 4 * x * (y * y) := by group
      _ = x ^ 5 * y ^ 2 := by rw [← pow_succ, pow_two]
      _ = y ^ 2 := by rw [hD.x_pow, one_mul]
  have hsq : ∀ s ∈ S, (MulAut.conj n ^ 2) s = s ^ 2 := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hσ2x
      · exact hσ2y
    | one => simp
    | mul a b haS hbS iha ihb =>
      rw [map_mul, iha, ihb]
      exact (Commute.mul_pow (hcomm a haS b hbS) 2).symm
    | inv a haS iha =>
      rw [map_inv, iha, inv_pow]
  have h4 : ∀ s ∈ S, (MulAut.conj n ^ 4) s = s⁻¹ := by
    intro s hs
    have hσ2s : (MulAut.conj n ^ 2) s = s ^ 2 := hsq s hs
    have hmem2 : (MulAut.conj n ^ 2) s ∈ S := by
      have h1 : MulAut.conj n s ∈ S := hσmem s hs
      have h2 : MulAut.conj n (MulAut.conj n s) ∈ S := hσmem (MulAut.conj n s) h1
      simpa [pow_two] using h2
    have h4eq : (MulAut.conj n ^ 4) s =
        (MulAut.conj n ^ 2) ((MulAut.conj n ^ 2) s) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
      rfl
    rw [h4eq, hsq ((MulAut.conj n ^ 2) s) hmem2, hσ2s, ← pow_mul]
    rw [show 2 * 2 = 4 by norm_num]
    have h5 : s ^ 5 = 1 := hpow s hs
    have h45 : s ^ 4 * s = 1 := by
      rw [← pow_succ, show 4 + 1 = 5 by norm_num, h5]
    exact eq_inv_iff_mul_eq_one.mpr h45
  refine ⟨S, hSq, hSne, hcomm, n, hn, ?_⟩
  intro k hk0 hk5 s hs hfix
  have hfixσ : (MulAut.conj n ^ k) s = s := by
    calc (MulAut.conj n ^ k) s = MulAut.conj (n ^ k) s := by rw [map_pow]
      _ = n ^ k * s * (n ^ k)⁻¹ := by rw [MulAut.conj_apply]
      _ = s := hfix
  interval_cases k
  · have h1 : (MulAut.conj n ^ 1) s = s := hfixσ
    have hσs : MulAut.conj n s = s := by simpa using h1
    have hs2 : s ^ 2 = s := by
      rw [← hsq s hs]
      rw [pow_two]
      change MulAut.conj n (MulAut.conj n s) = s
      rw [hσs, hσs]
    apply mul_left_cancel (a := s)
    simpa [pow_two] using hs2
  · have h2 : (MulAut.conj n ^ 2) s = s := hfixσ
    have hs2 : s ^ 2 = s := by rw [← hsq s hs]; exact h2
    apply mul_left_cancel (a := s)
    simpa [pow_two] using hs2
  · have h3 : (MulAut.conj n ^ 3) s = s := hfixσ
    have h4s : (MulAut.conj n ^ 4) s = s⁻¹ := h4 s hs
    have h4' : (MulAut.conj n ^ 4) s = MulAut.conj n s := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ']
      change MulAut.conj n ((MulAut.conj n ^ 3) s) = MulAut.conj n s
      rw [h3]
    have hσs : MulAut.conj n s = s⁻¹ := by rw [← h4', h4s]
    have hs2 : (MulAut.conj n ^ 2) s = s := by
      rw [pow_two]
      change MulAut.conj n (MulAut.conj n s) = s
      rw [hσs, map_inv, hσs, inv_inv]
    have hs2' : s ^ 2 = s := by rw [← hsq s hs]; exact hs2
    apply mul_left_cancel (a := s)
    simpa [pow_two] using hs2'
  · have h4s : (MulAut.conj n ^ 4) s = s := hfixσ
    have hsinv : s⁻¹ = s := by rw [← h4 s hs, h4s]
    have hs2 : s ^ 2 = 1 := by
      rw [pow_two]
      exact (inv_eq_iff_mul_eq_one).mp hsinv
    have h6 : s ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hs2, one_pow]
    have h6' : s ^ 6 = s := by
      rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, hpow s hs, one_mul, pow_one]
    exact h6'.symm.trans h6

theorem fixedFreeFive_fi22
    {L : Type} [Group L] (hs : IsSimpleGroup L) (hL : CFSG.AGLEmbedding.IsFi22 L) :
    FixedFreeFive 5 L := by
  obtain ⟨x, y, _, n₂, hD, -, -, hx, hy⟩ :=
    CFSG.AGLEmbedding.KFactProofs.SmallBad.Fi22.fi22_norm_data
  have hP : FixedFreeFive 5 CFSG.Monster.B.Fischer.fi22P :=
    FixedFreeFive.of_conj hD hx hy
  have hN : FixedFreeFive 5 CFSG.Blueprint.NativeSporadic.Fi22 :=
    @FixedFreeFive.of_mulEquiv 5 CFSG.Monster.B.Fischer.fi22P
      CFSG.Blueprint.NativeSporadic.Fi22 _ _ CFSG.Monster.B.Fischer.fi22PermEquiv.symm hP
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_fi22 hs hL
  exact @FixedFreeFive.of_mulEquiv 5 CFSG.Blueprint.NativeSporadic.Fi22 L _ _ e.symm hN

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
