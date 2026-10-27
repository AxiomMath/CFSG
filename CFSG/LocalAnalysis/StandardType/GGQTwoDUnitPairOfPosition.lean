module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitPos
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPairAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private lemma qtwoDU5_swap_eq_of_pair_eq_pop {n : ℕ} {a b c d : Fin n} (hab : a ≠ b)
    (h : ({a, b} : Finset (Fin n)) = {c, d}) : Equiv.swap a b = Equiv.swap c d := by
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset (Fin n)) := by rw [← h]; simp
    simpa using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset (Fin n)) := by rw [← h]; simp
    simpa using this
  rcases ha with hac | had <;> rcases hb with hbc | hbd
  · exact absurd (hac.trans hbc.symm) hab
  · rw [hac, hbd]
  · rw [had, hbc]
    exact Equiv.swap_comm d c
  · exact absurd (had.trans hbd.symm) hab

private lemma qtwoDU5_coords_pop {p : ℕ} {B Bs X : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs))
    (hε : ∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
      ((((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
        ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹)
    {r r' : MulAut ↥Bs}
    {a₁ b₁ c₁ d₁ x y z : Fin n} (hab₁ : a₁ ≠ b₁) (hcd₁ : c₁ ≠ d₁)
    (hr_eq : r = ((ε (Equiv.swap a₁ b₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hr'_eq : r' = ((ε (Equiv.swap c₁ d₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxy_eq : ({a₁, b₁} : Finset (Fin n)) = {x, y})
    (hyz_eq : ({c₁, d₁} : Finset (Fin n)) = {y, z}) :
    ggRankTwoIn X Bs r r' = (coordBlockSU K 2 1 {x, y, z}).map ψ := by
  have hK : Nat.card K = 4 := by
    rw [h.card]; norm_num
  have hsw1 : Equiv.swap a₁ b₁ = Equiv.swap x y :=
    qtwoDU5_swap_eq_of_pair_eq_pop hab₁ hxy_eq
  have hsw2 : Equiv.swap c₁ d₁ = Equiv.swap y z :=
    qtwoDU5_swap_eq_of_pair_eq_pop hcd₁ hyz_eq
  have hr_xy : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap x y)) * (s : G) * (ψ (ggPermSU (Equiv.swap x y)))⁻¹ := by
    intro s
    have h1 := hε (Equiv.swap x y) s
    have hrx : r = ((ε (Equiv.swap x y) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
      rw [hr_eq, hsw1]
    rw [hrx]
    simpa only [Equiv.swap_inv] using h1
  have hr_yz : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap y z)) * (s : G) * (ψ (ggPermSU (Equiv.swap y z)))⁻¹ := by
    intro s
    have h1 := hε (Equiv.swap y z) s
    have hr'y : r' = ((ε (Equiv.swap y z) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
      rw [hr'_eq, hsw2]
    rw [hr'y]
    simpa only [Equiv.swap_inv] using h1
  rw [← hrange]
  exact ggQTwoDUnit_rankTwoIn_eq h hK hd hxy hyz hxz hr_xy hr_yz

private lemma qtwoDU5_finish_pop {p : ℕ} {B Bs X : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (h : GGNSLocalHyp p B Bs K 1 n ψ)
    {r r' : MulAut ↥Bs} (h6 : Nat.card ↥(ggRankOneIn X Bs r) = 6)
    {a₁ b₁ c₁ d₁ x y z : Fin n}
    (hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 1 n a₁ b₁).map ψ)
    (hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 1 n c₁ d₁).map ψ)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxy_eq : ({a₁, b₁} : Finset (Fin n)) = {x, y})
    (hyz_eq : ({c₁, d₁} : Finset (Fin n)) = {y, z})
    (hrank : ggRankTwoIn X Bs r r' = (coordBlockSU K 2 1 {x, y, z}).map ψ) :
    UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn X Bs r r')
      (ggRankOneIn X Bs r) (ggRankOneIn X Bs r') := by
  have hW := ggQTwoDUnit_stdPair ψ h.ker (by omega : 3 ≤ n) hxy hyz hxz
  have e1 : (ggSuPairBlock K 2 1 n x y).map ψ = ggRankOneIn X Bs r := by
    rw [ggMUP1_suPairBlock_congr (K := K) (p := 2) (f := 1) (n := n)
      (a := x) (b := y) (c := a₁) (d := b₁) hxy_eq.symm, ← hrS]
  have e2 : (ggSuPairBlock K 2 1 n y z).map ψ = ggRankOneIn X Bs r' := by
    rw [ggMUP1_suPairBlock_congr (K := K) (p := 2) (f := 1) (n := n)
      (a := y) (b := z) (c := c₁) (d := d₁) hyz_eq.symm, ← hr'S]
  rw [← hrank, e1, e2] at hW
  refine ggPhanNSAPairAux_stdPair_of_card (K := K) (f := 1) (K' := GaloisField 2 2)
    (f' := 1) h.card ?_ hW ?_
  · rw [natCard_galoisField_two_two]; norm_num
  · rw [show (2 : ℕ) ^ 1 * ((2 ^ 1) ^ 2 - 1) = 6 by norm_num]
    exact h6

theorem ggQTwoDUnit_pair_of_position {p : ℕ} {B Bs X : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (h : GGNSLocalHyp p B Bs K f n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs))
    (hε : ∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
      ((((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
        ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹)
    (hεrefl : ∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hεlevi : ∀ a b : Fin n, a ≠ b →
      ggRankOneIn X Bs ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggSuPairBlock K 2 f n a b).map ψ)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r)
    (hrA' : r' ∈ ggAutomizer X Bs) (hr' : GGIsReflection p r') (hnc : r * r' ≠ r' * r)
    (h6 : Nat.card ↥(ggRankOneIn X Bs r) = 6) :
    UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn X Bs r r')
      (ggRankOneIn X Bs r) (ggRankOneIn X Bs r') := by
  classical
  obtain ⟨a₁, b₁, hab₁, hr_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hεrefl hrA hr
  obtain ⟨c₁, d₁, hcd₁, hr'_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hεrefl hrA' hr'
  have hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ := by
    rw [hr_eq]; exact hεlevi a₁ b₁ hab₁
  have hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ := by
    rw [hr'_eq]; exact hεlevi c₁ d₁ hcd₁
  have hnc_swap : Equiv.swap a₁ b₁ * Equiv.swap c₁ d₁ ≠
      Equiv.swap c₁ d₁ * Equiv.swap a₁ b₁ := by
    intro hswap
    apply hnc
    have h3 := congrArg (fun π : Equiv.Perm (Fin n) =>
      ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) hswap
    simp only [map_mul, Subgroup.coe_mul] at h3
    rw [← hr_eq, ← hr'_eq] at h3
    exact h3
  obtain ⟨x, y, z, hxy, hyz, hxz, hxy_eq, hyz_eq⟩ :=
    ggMUP1_share3 hab₁ hcd₁ hnc_swap
  have h6' : Nat.card ↥((ggSuPairBlock K 2 f n a₁ b₁).map ψ) = 6 := by
    rw [← hrS]; exact h6
  have hf : f = 1 := ggQTwoDUnit_f_eq_one h hab₁ h6'
  subst f
  have hrank := qtwoDU5_coords_pop h hrange hd ε hε hab₁ hcd₁ hr_eq hr'_eq hxy hyz hxz
    hxy_eq hyz_eq
  exact qtwoDU5_finish_pop h h6 hrS hr'S hxy hyz hxz hxy_eq hyz_eq hrank

end CFSG.StandardType.QTwo

end
