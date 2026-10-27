module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoOdd
public import CFSG.Walter.PSL2Facts.FieldAut

public section

namespace CFSG.Walter.W67

namespace JROut

open CFSG.GorensteinWalter CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

theorem le_center_of_card_dvd_two {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal]
    (h : Nat.card N ∣ 2) : N ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  have hcard : Nat.card N = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact absurd (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp h1 ▸ hz)) hz1
    · exact h2
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hcard
  have h1 : (⟨z, hz⟩ : N) = y := hy _ fun h => hz1 (congrArg Subtype.val h)
  have h2 : (⟨g * z * g⁻¹, hc⟩ : N) = y := hy _ fun h => hz1 (by
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    rw [mul_inv_eq_one, mul_eq_left] at h'
    exact h')
  have hz' : g * z * g⁻¹ = z := congrArg Subtype.val (h2.trans h1.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hz']

theorem isCyclic_of_card_dvd_two {G : Type*} [Group G] (h : Nat.card G ∣ 2) : IsCyclic G := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime (Nat.card G)) := ⟨h2 ▸ Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl

theorem isCyclic_of_ker_le_center {G Q : Type*} [Group G] [Finite G] [Group Q] [IsCyclic Q]
    (f : G →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    [IsCyclic f.ker] (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card Q)) : IsCyclic G := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.ker)
  obtain ⟨g, rfl⟩ := hf q
  obtain ⟨d, hd⟩ : Nat.card Q ∣ orderOf g := hq ▸ orderOf_map_dvd f g
  have hpos : 0 < orderOf g := orderOf_pos g
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    omega
  have hb : orderOf (g ^ d) = Nat.card Q := by
    rw [orderOf_pow' g hd0, hd, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
  have ha : orderOf (z : G) = Nat.card f.ker := by rw [Subgroup.orderOf_coe, hz]
  have hcomm : Commute (z : G) (g ^ d) := (Subgroup.mem_center_iff.mp (hker z.2) (g ^ d)).symm
  have hcard : Nat.card G = Nat.card f.ker * Nat.card Q := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h1
    rw [h1, mul_comm]
  refine isCyclic_of_orderOf_eq_card ((z : G) * g ^ d) ?_
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; exact hcop), ha, hb, hcard]

theorem card_diagonalHom_range_dvd_two (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : Nat.card (diagonalHom K).range ∣ 2 := by
  rw [← Subgroup.index_ker]
  have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ≤
      (diagonalHom K).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (pGammaL2PSLRange K)
      (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, rfl⟩
  have h2 := Subgroup.index_dvd_of_le hle
  rwa [pgl2_psl2Range_index_eq_two K hK] at h2

theorem isCyclic_semilinearQuotient {p n : ℕ} [Fact p.Prime] (hp : Odd p) (hn : Odd n) :
    IsCyclic (SemilinearQuotient (GaloisField p n)) := by
  set F := GaloisField p n
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by decide)
  have hK : IsOddPrimePower (Nat.card F) :=
    ⟨p, n, Fact.out, hp, Nat.one_le_iff_ne_zero.mpr hn0, GaloisField.card p n hn0⟩
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) fun e f hef => by
      ext x
      exact congrFun hef x
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PGammaL2 F) :=
    Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) fun x y hxy =>
      SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  have hdvd : Nat.card (quotientFieldProjection F).ker ∣ 2 := by
    rw [quotientFieldProjection_ker F]
    exact card_diagonalHom_range_dvd_two F hK
  have : IsCyclic (quotientFieldProjection F).ker := isCyclic_of_card_dvd_two hdvd
  have hodd : Odd (Nat.card (F ≃+* F)) := by
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F ≃+* F)
    rw [← hσ]
    exact Odd.of_dvd_nat hn (card_fixedSubfield_galoisField hn0 σ).1
  refine isCyclic_of_ker_le_center (quotientFieldProjection F)
    (quotientFieldProjection_surjective F) (le_center_of_card_dvd_two hdvd) ?_
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · rw [h1]
    exact Nat.coprime_one_left _
  · rw [h2]
    exact Nat.coprime_two_left.mpr hodd

theorem isCyclic_outer_psl2 {p n : ℕ} [Fact p.Prime] (hp : Odd p) (hn : Odd n)
    (h3 : 3 < p ^ n) : IsCyclic (Outer (PSL2 (GaloisField p n))) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by decide)
  have hK : IsOddPrimePower (Nat.card (GaloisField p n)) :=
    ⟨p, n, Fact.out, hp, Nat.one_le_iff_ne_zero.mpr hn0, GaloisField.card p n hn0⟩
  have : IsCyclic (SemilinearQuotient (GaloisField p n)) := isCyclic_semilinearQuotient hp hn
  exact (odd_outerEquivSemilinearQuotient _ hK
    (by rw [GaloisField.card p n hn0]; exact h3)).isCyclic.mp inferInstance

theorem isCyclic_outer_of_equiv {K : Type*} [Group K] {p n : ℕ} [Fact p.Prime]
    (e : K ≃* PSL(2, GaloisField p n)) (hp : Odd p) (hn : Odd n) (h3 : 3 < p ^ n) :
    IsCyclic (Outer K) :=
  (equivalence e).isCyclic.mpr (isCyclic_outer_psl2 hp hn h3)

end JROut

end CFSG.Walter.W67
