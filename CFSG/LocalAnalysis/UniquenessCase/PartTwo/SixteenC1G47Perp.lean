module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16c1_perp_polarQ_map {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    {C : Subgroup (MulAut W)} (hCQ : QuadInvariant Q C) {φ : MulAut W} (hφ : φ ∈ C)
    (x y : W) : polarQ Q (φ x) (φ y) = polarQ Q x y := by
  unfold polarQ
  rw [← map_mul, hCQ φ hφ, hCQ φ hφ, hCQ φ hφ]

private theorem s16c1_perp_polarQ_one {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsQuadF2 Q) (z : W) : polarQ Q z 1 = 0 := by
  have h : polarQ Q z (1 * 1) = polarQ Q z 1 + polarQ Q z 1 := hQ.2 z 1 1
  rw [mul_one] at h
  exact (by decide : ∀ a : ZMod 2, a = a + a → a = 0) _ h

private def s16c1_perpHom {W : Type*} [CommGroup W] {Q : W → ZMod 2} (hQ : IsQuadF2 Q)
    (z : W) : W →* Multiplicative (ZMod 2) where
  toFun y := Multiplicative.ofAdd (polarQ Q z y)
  map_one' := by
    rw [ofAdd_eq_one]
    exact s16c1_perp_polarQ_one hQ z
  map_mul' a b := by
    rw [← ofAdd_add, hQ.2 z a b]

private theorem s16c1_perpHom_mem_ker {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsQuadF2 Q) (z y : W) :
    y ∈ (s16c1_perpHom hQ z).ker ↔ polarQ Q z y = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

private theorem s16c1_perpHom_card {W : Type*} [CommGroup W] [Finite W] {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (hW64 : Nat.card W = 64) {z : W} (hz1 : z ≠ 1) :
    Nat.card (s16c1_perpHom hQ.1 z).ker = 32 := by
  set f : W →* Multiplicative (ZMod 2) := s16c1_perpHom hQ.1 z with hf
  have hfapply : ∀ y : W, f y = Multiplicative.ofAdd (polarQ Q z y) := fun _ => rfl
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 2))]
    exact Nat.card_zmod 2
  have hrange_ne : f.range ≠ ⊥ := by
    obtain ⟨y, hy⟩ := hQ.2 z hz1
    have hy1 : f y ≠ 1 := by
      rw [hfapply y]
      exact fun h => hy (ofAdd_eq_one.mp h)
    intro hbot
    have hmem : f y ∈ f.range := ⟨y, rfl⟩
    rw [hbot] at hmem
    exact hy1 (Subgroup.mem_bot.mp hmem)
  haveI : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨by rw [hcardM]; norm_num⟩
  have hrange_top : f.range = ⊤ := by
    rcases f.range.eq_bot_or_eq_top_of_prime_card with h | h
    · exact absurd h hrange_ne
    · exact h
  have hindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker f, hrange_top, Subgroup.card_top, hcardM]
  have hcm := Subgroup.card_mul_index f.ker
  rw [hindex, hW64] at hcm
  omega

theorem s16c1_perp_le_of_stable {W : Type*} [CommGroup W] [Finite W] {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (hW : ∀ w : W, w * w = 1) (hW64 : Nat.card W = 64)
    {C : Subgroup (MulAut W)} (hCQ : QuadInvariant Q C) {z : W} (hz1 : z ≠ 1)
    (hzC : ∀ φ ∈ C, φ z = z)
    (hIrr : ∀ S : Subgroup W, StableUnder C S →
      Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 32 ∨ Nat.card S = 64)
    {U : Subgroup W} (hU : StableUnder C U) (hUcard : 64 ≤ 2 * Nat.card U) :
    ∀ y : W, polarQ Q z y = 0 → y ∈ U := by
  classical
  set f : W →* Multiplicative (ZMod 2) := s16c1_perpHom hQ.1 z with hf
  set P : Subgroup W := f.ker with hP
  have hPmem_ker : ∀ y : W, y ∈ f.ker ↔ polarQ Q z y = 0 := by
    intro y
    rw [hf]
    exact s16c1_perpHom_mem_ker hQ.1 z y
  have hPmem : ∀ y : W, y ∈ P ↔ polarQ Q z y = 0 := by
    intro y
    rw [hP]
    exact hPmem_ker y
  have hcardP : Nat.card P = 32 := by
    rw [hP, hf]
    exact s16c1_perpHom_card hQ hW64 hz1
  have hPstable : StableUnder C P := by
    unfold StableUnder
    intro φ hφ y hy
    rw [hPmem y] at hy
    rw [hPmem (φ y)]
    calc polarQ Q z (φ y) = polarQ Q (φ z) (φ y) := by rw [hzC φ hφ]
      _ = polarQ Q z y := s16c1_perp_polarQ_map hCQ hφ z y
      _ = 0 := hy
  set K : Subgroup W := U ⊓ P with hK
  have hKstable : StableUnder C K := by
    unfold StableUnder
    intro φ hφ x hx
    rw [hK, Subgroup.mem_inf] at hx ⊢
    exact ⟨hU φ hφ x hx.1, hPstable φ hφ x hx.2⟩
  have hPindex : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hW64, hcardP] at h
    omega
  have hUindex : U.index ≤ 2 := by
    have h := Subgroup.card_mul_index U
    rw [hW64] at h
    have hle : Nat.card U * U.index ≤ Nat.card U * 2 := by
      rw [h, Nat.mul_comm (Nat.card U) 2]
      exact hUcard
    exact Nat.le_of_mul_le_mul_left hle Nat.card_pos
  have hKindex : K.index ≤ 4 := by
    have hle : K.index ≤ U.index * P.index := by
      rw [hK]
      exact Subgroup.index_inf_le
    rw [hPindex] at hle
    calc K.index ≤ U.index * 2 := hle
      _ ≤ 2 * 2 := Nat.mul_le_mul hUindex le_rfl
      _ = 4 := by norm_num
  have hKleP : K ≤ P := by
    rw [hK]
    exact inf_le_right
  have hKcard : Nat.card K = 32 := by
    have hmem := hIrr K hKstable
    have hle32 : Nat.card K ≤ Nat.card P := Subgroup.card_le_of_le hKleP
    rw [hcardP] at hle32
    have hge16 : 16 ≤ Nat.card K := by
      have h := Subgroup.card_mul_index K
      rw [hW64] at h
      have hle : Nat.card K * K.index ≤ Nat.card K * 4 := Nat.mul_le_mul le_rfl hKindex
      rw [h] at hle
      omega
    rcases hmem with h | h | h | h <;> omega
  have hKeq : K = P :=
    Subgroup.eq_of_le_of_card_ge (H := K) (K := P) hKleP (by rw [hKcard, hcardP])
  have hinf : U ⊓ P = P := by
    rw [← hK]
    exact hKeq
  intro y hy
  exact (inf_eq_right.mp hinf) ((hPmem y).mpr hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
