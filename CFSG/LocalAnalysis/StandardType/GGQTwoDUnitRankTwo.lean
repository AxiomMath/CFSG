module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSep
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux4
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeOdd

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2]

private lemma qtwoDU3_block_le_centralizer {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    (coordBlockSU K 2 f {a, b, c}).map ψ ≤
      ψ.range ⊓ Subgroup.centralizer
        (((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G)) : Set G) := by
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨⟨A, rfl⟩, ?_⟩
  intro s hs
  obtain ⟨hsr, hsr'⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hsr
  rw [← hts]
  have ht' : r t = t := ht
  have ht'' : r' t = t := by
    obtain ⟨t', _, hts'⟩ := Subgroup.mem_map.mp hsr'
    have hsame : t' = t := Subtype.ext (hts'.trans hts.symm)
    rwa [← hsame]
  obtain ⟨g, ⟨d, hdg⟩, hunit, hact⟩ := hd (t : G) t.2
  have hda : d a = d b :=
    ggNSPosPB_diag_eq h hd a b hab r hr ht' ⟨d, hdg⟩ ⟨hunit, hact⟩ d hdg
  have hdb : d b = d c :=
    ggNSPosPB_diag_eq h hd b c hbc r' hr' ht'' ⟨d, hdg⟩ ⟨hunit, hact⟩ d hdg
  have hdconst : ∀ i ∈ ({a, b, c} : Finset (Fin n)),
      ∀ j ∈ ({a, b, c} : Finset (Fin n)), d i = d j := by
    intro i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · rfl
    · exact hda
    · exact hda.trans hdb
    · exact hda.symm
    · rfl
    · exact hdb
    · exact (hda.trans hdb).symm
    · exact hdb.symm
    · rfl
  obtain ⟨y, hy, hyact⟩ := hact A
  have hcomm : g * A = A * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hdg]
    exact diagonal_mul_comm_of_mem_coordBlockSU hA hdconst
  have hyA : y = A := by
    apply Subtype.ext
    rw [hy, hcomm]
    group
  rw [hyA] at hyact
  exact mul_inv_eq_iff_eq_mul.mp hyact

theorem ggQTwoDUnit_rankTwoIn_le {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    ggRankTwoIn ψ.range Bs r r' ≤ (coordBlockSU K 2 f {a, b, c}).map ψ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hT : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩
  rw [ggRankTwoIn, ggOTwoPrime, Subgroup.closure_le]
  rintro y ⟨hy, k, hyk⟩
  obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hyR
  have hx2 : x ^ (2 ^ k) ∈ Subgroup.center (Su K 2 f n) :=
    h.ker (by rw [MonoidHom.mem_ker, map_pow, hyk])
  have hcop : Nat.Coprime p (2 ^ k) :=
    (h.prime.coprime_iff_not_dvd).mpr fun hdvd =>
      h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
        (h.prime.dvd_of_dvd_pow hdvd))
  have hoff : ∀ i j, i ≠ j →
      ¬ (i ∈ ({a, b, c} : Finset (Fin n)) ∧ j ∈ ({a, b, c} : Finset (Fin n))) →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij hnot
    obtain ⟨t, d, htd, hdp, hconst, hdij⟩ :=
      ggQTwoDUnit_exists_sep3 (K := K) (f := f) (n := n) h.odd h.dvd h.card hT hij hnot
    have hda : d a = d b := hconst a (by simp) b (by simp)
    have hdb : d b = d c := hconst b (by simp) c (by simp)
    have htHyp : ψ t ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r' :=
      Subgroup.mem_inf.mpr
        ⟨ggNSPosPB2_map_mem_hyperplane h hd a b hab r hr htd hdp hda,
         ggNSPosPB2_map_mem_hyperplane h hd b c hbc r' hr' htd hdp hdb⟩
    have hyt : ψ x * ψ t = ψ t * ψ x :=
      (Subgroup.mem_centralizer_iff.mp hyC (ψ t) htHyp).symm
    have htp : t ^ p = 1 := ggNSPosPB2_pow_eq_one_of_diag htd hdp
    have hxt := ggNSPosPB2_comm_of_centralizer (k := k) h.ker htp hyt hcop hx2
    exact ggNSPosPB2_entry_eq_zero htd hdij hxt
  have hdiag : ∀ e, e ∉ ({a, b, c} : Finset (Fin n)) →
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) e e) ^ (2 ^ f + 1) = 1 := by
    intro e he
    have hconj := ((mem_SUid (σ := unitaryInvolution K 2 f)).mp x.2).2
    have h := congrFun (congrFun hconj e) e
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single e] at h
    · rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, unitaryInvolution_apply] at h
      rw [pow_succ]
      exact h
    · intro m _ hm
      rw [hoff m e hm (fun hh => he hh.2), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ e) h'
  have hyq : (ψ x) ^ (2 ^ f + 1) ∈ (coordBlockSU K 2 f {a, b, c}).map ψ :=
    ⟨x ^ (2 ^ f + 1), ggQTwoDUnit_pow_mem_coordBlockSU hoff hdiag, map_pow ψ x (2 ^ f + 1)⟩
  have hf1 : 1 ≤ f := by
    by_contra hf
    push Not at hf
    have hf0 : f = 0 := by omega
    subst hf0
    have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (by simpa using h.dvd)
    exact h.odd hp2'
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop2 : Nat.Coprime (2 ^ f + 1) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  have hbez : ((2 ^ f + 1 : ℕ) : ℤ) * Nat.gcdA (2 ^ f + 1) (2 ^ k) +
      ((2 ^ k : ℕ) : ℤ) * Nat.gcdB (2 ^ f + 1) (2 ^ k) = 1 := by
    have hh := Nat.gcd_eq_gcd_ab (2 ^ f + 1) (2 ^ k)
    rw [hcop2.gcd_eq_one] at hh
    exact_mod_cast hh.symm
  have hy' : (ψ x ^ (2 ^ f + 1)) ^ (Nat.gcdA (2 ^ f + 1) (2 ^ k)) *
        (ψ x ^ (2 ^ k)) ^ (Nat.gcdB (2 ^ f + 1) (2 ^ k)) = ψ x := by
    rw [← zpow_natCast (ψ x) (2 ^ f + 1), ← zpow_natCast (ψ x) (2 ^ k), ← _root_.zpow_mul,
      ← _root_.zpow_mul, ← _root_.zpow_add, hbez, zpow_one]
  rw [← hy']
  exact mul_mem (zpow_mem hyq _) (by rw [hyk, _root_.one_zpow]; exact one_mem _)

theorem ggQTwoDUnit_le_rankTwoIn {n : ℕ} {ψ : Su K 2 1 n →* G}
    (h : GGNSLocalHyp p B Bs K 1 n ψ) (hK : Nat.card K = 4)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    (coordBlockSU K 2 1 {a, b, c}).map ψ ≤ ggRankTwoIn ψ.range Bs r r' := by
  have hT : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩
  have hgen := qTwoChartTwoThree_oTwoPrime_coordBlockSU (F0 := K) hK
    (J := ({a, b, c} : Finset (Fin n))) (by omega) (by omega)
  have hgen' : coordBlockSU K 2 1 ({a, b, c} : Finset (Fin n)) ≤
      Subgroup.closure {A : Su K 2 1 n | A ∈ coordBlockSU K 2 1 {a, b, c} ∧
        ∃ k : ℕ, A ^ (2 ^ k) = 1} := by
    have h1 : coordBlockSU K 2 1 ({a, b, c} : Finset (Fin n)) ≤
        qTwoOTwoPrime (coordBlockSU K 2 1 {a, b, c}) := le_of_eq hgen.symm
    exact h1
  have hYle := qtwoDU3_block_le_centralizer h hd hab hbc hac hr hr'
  rw [ggRankTwoIn]
  calc (coordBlockSU K 2 1 {a, b, c}).map ψ
      ≤ (Subgroup.closure {A : Su K 2 1 n | A ∈ coordBlockSU K 2 1 {a, b, c} ∧
          ∃ k : ℕ, A ^ (2 ^ k) = 1}).map ψ := Subgroup.map_mono hgen'
    _ = Subgroup.closure (ψ '' {A : Su K 2 1 n | A ∈ coordBlockSU K 2 1 {a, b, c} ∧
          ∃ k : ℕ, A ^ (2 ^ k) = 1}) := MonoidHom.map_closure ψ _
    _ ≤ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer
          ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G)) := by
        refine (Subgroup.closure_le (ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer
          ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G)))).mpr ?_
        rintro z ⟨A, ⟨hA, k, hA2⟩, rfl⟩
        exact Subgroup.subset_closure
          ⟨hYle ⟨A, hA, rfl⟩, k, by rw [← map_pow, hA2, map_one]⟩

theorem ggQTwoDUnit_rankTwoIn_eq {n : ℕ} {ψ : Su K 2 1 n →* G}
    (h : GGNSLocalHyp p B Bs K 1 n ψ) (hK : Nat.card K = 4)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    ggRankTwoIn ψ.range Bs r r' = (coordBlockSU K 2 1 {a, b, c}).map ψ :=
  le_antisymm (ggQTwoDUnit_rankTwoIn_le h hd hab hbc hac hr hr')
    (ggQTwoDUnit_le_rankTwoIn h hK hd hab hbc hac hr hr')

end CFSG.StandardType.QTwo

end

