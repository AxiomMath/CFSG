module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GRank
public import CFSG.Quasithin.H13.NQCatParabolicSL3
public import CFSG.Quasithin.EmptyFaithful.S146yL3Par

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

namespace S15223P4.G

theorem not_three_dvd_pow_two_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h5 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h5]
  omega

theorem eq_one_of_pow_three {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : Odd n)
    (hF : Fintype.card F = 2 ^ n) {u : Fˣ} (hu : u ^ 3 = 1) : u = 1 := by
  have hcop : Nat.Coprime 3 (Nat.card Fˣ) := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_pow_two_sub_one hn)
  have h2 : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
  have := pow_gcd_eq_one.mpr ⟨hu, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem eq_one_of_mem_solvable {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 < n)
    (hodd : Odd n) (hF : Fintype.card F = 2 ^ n)
    {Y P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hPY : P ≤ Y)
    (hP : IsSylowTwoOf P ⊤) (hY : Group.IsSolvable ↥Y)
    {y : Matrix.SpecialLinearGroup (Fin 3) F} (hy : y ∈ Y) (hy3 : y ^ 3 = 1) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hV : IsSylowTwoOf (unitriangular 3 F) ⊤ := hP₀ ▸ isSylowTwoOf_top_of_sylow P₀
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_isSylowTwoOf hP hV
  have hU : unitriangular 3 F ≤ Y.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono hPY
  have hsolv : Group.IsSolvable ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    CFSG.QuasithinUnique.Setup.X6.map_isSolvable_equiv (MulAut.conj g) Y hY
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    have h4 : 4 ≤ Finset.univ.card (α := F) := by
      rw [Finset.card_univ, hF]
      calc 4 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hB := H13.NQCat.SL3.le_upperTriangular_of_isSolvable hK4 hU hsolv
  have hyB : (MulAut.conj g) y ∈ upperTriangular 3 F := hB ⟨y, hy, rfl⟩
  set b : ↥(upperTriangular 3 F) := ⟨(MulAut.conj g) y, hyB⟩ with hb
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    change ((MulAut.conj g) y) ^ 3 = 1
    rw [← map_pow, hy3, map_one])
  have hd : diagHomLin 3 F b = 1 := by
    funext i
    have h1 : (diagHomLin 3 F b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    exact eq_one_of_pow_three hodd hF (congrFun h1 i)
  have hker : b ∈ (diagHomLin 3 F).ker := hd
  rw [ker_diagHomLin] at hker
  have hyV : (MulAut.conj g) y ∈ unitriangular 3 F := hker
  have h1 : (MulAut.conj g) y = 1 :=
    S15223P4.G.eq_one_of_isPGroup_two_of_pow_three hV.isPGroup hyV (by
      rw [← map_pow, hy3, map_one])
  exact (MulAut.conj g).injective (by rw [h1, map_one])

theorem eq_one_of_mem_solvable_of_equiv {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 < n)
    (hodd : Odd n) (hF : Fintype.card F = 2 ^ n) {Q : Type} [Group Q] [Finite Q]
    (φ : Q ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) {Y P : Subgroup Q} (hPY : P ≤ Y)
    (hP2 : IsPGroup 2 P) (hPodd : ¬ 2 ∣ P.index) (hY : Group.IsSolvable ↥Y) {y : Q} (hy : y ∈ Y)
    (hy3 : y ^ 3 = 1) : y = 1 := by
  set ψ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm with hψ
  have hP : IsSylowTwoOf (P.map ψ.toMonoidHom) ⊤ := by
    refine ⟨le_top, hP2.map ψ.toMonoidHom, ?_⟩
    have h1 : ((P.map ψ.toMonoidHom).subgroupOf ⊤).index = P.index :=
      (Subgroup.relIndex_top_right _).trans (Subgroup.index_map_equiv P ψ)
    rwa [h1]
  have h := eq_one_of_mem_solvable hn hodd hF (Subgroup.map_mono hPY) hP
    (CFSG.QuasithinUnique.Setup.X6.map_isSolvable_equiv ψ Y hY) ⟨y, hy, rfl⟩
    (by rw [← map_pow, hy3, map_one])
  exact ψ.injective (h.trans (map_one ψ).symm)

end S15223P4.G

end CFSG.Quasithin
