module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux
public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

noncomputable def ggNSPosPB2_diagSU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (d : Fin n → K) (hdet : ∏ k, d k = 1)
    (hunit : ∀ k, unitaryInvolution K 2 f (d k) * d k = 1) : Su K 2 f n :=
  let hne : (Matrix.diagonal d).det ≠ 0 := by rw [Matrix.det_diagonal, hdet]; exact one_ne_zero
  let B : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) hne
  have hB : (B : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hconj : conjTr (unitaryInvolution K 2 f) (Matrix.diagonal d) =
      Matrix.diagonal (fun k => unitaryInvolution K 2 f (d k)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
    · simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), map_zero]
  ⟨B, (mem_SUid (σ := unitaryInvolution K 2 f) (n := n) (B := B)).mpr
      ⟨by rw [hB, Matrix.det_diagonal, hdet], by
        rw [hB, hconj, Matrix.diagonal_mul_diagonal,
          show (fun k => unitaryInvolution K 2 f (d k) * d k) = fun _ => 1 from
            funext (fun k => hunit k), Matrix.diagonal_one]⟩⟩

@[simp] theorem ggNSPosPB2_diagSU_coe {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (d : Fin n → K) (hdet : ∏ k, d k = 1)
    (hunit : ∀ k, unitaryInvolution K 2 f (d k) * d k = 1) :
    (((ggNSPosPB2_diagSU d hdet hunit : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem ggNSPosPB2_permSU_mem_block {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (a b : Fin n) :
    ggPermSU (Equiv.swap a b) ∈ ggSuPairBlock K 2 f n a b := by
  intro i j hij
  have hcoe : (((ggPermSU (Equiv.swap a b) : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (Equiv.swap a b).permMatrix K := rfl
  rw [hcoe, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_some_iff]
  rcases hij with ⟨hi, hib⟩ | ⟨hj, hjb⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hi hib]
  · have hsj : Equiv.swap a b j = j := Equiv.swap_apply_of_ne_of_ne hj hjb
    by_cases h : Equiv.swap a b i = j
    · have hij' : i = j := by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, hsj] at this
      rw [if_pos h, if_pos hij']
    · rw [if_neg h, if_neg (fun hij' => h (by rw [hij', hsj]))]

theorem ggNSPosPB2_diag_comm_perm {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (a b : Fin n) (d : Fin n → K) (hda : d a = d b) :
    Matrix.diagonal d * (Equiv.swap a b).permMatrix K =
      (Equiv.swap a b).permMatrix K * Matrix.diagonal d :=
  ggNSPosPB_diag_comm_block (K := K) (f := f) (n := n) (a := a) (b := b) (A := _) hda
    (ggNSPosPB2_permSU_mem_block (K := K) (f := f) (n := n) a b)

theorem ggNSPosPB2_diag_comm_perm_GL {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (a b : Fin n) {t : Su K 2 f n} {d : Fin n → K}
    (htd : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hda : d a = d b) :
    ggPermSU (Equiv.swap a b) * t = t * ggPermSU (Equiv.swap a b) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, htd]
  have hcoe : (((ggPermSU (Equiv.swap a b) : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (Equiv.swap a b).permMatrix K := rfl
  rw [hcoe]
  exact (ggNSPosPB2_diag_comm_perm (f := f) a b d hda).symm

theorem ggNSPosPB2_exists_notMem {n : ℕ} (hn : 4 ≤ n) (s : Finset (Fin n)) (hs : s.card ≤ 3) :
    ∃ k, k ∉ s := by
  by_contra h
  push Not at h
  have : s = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [this, Finset.card_univ, Fintype.card_fin] at hs
  omega

private theorem ggNSPosPB2_sum_single {n : ℕ} (m : Fin n) (c : ℕ) :
    (∑ x, (Pi.single (M := fun _ => ℕ) m c) x) = c := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro x _ hx; simp [Pi.single_eq_of_ne hx]
  · intro h; exact absurd (Finset.mem_univ m) h

private theorem ggNSPosPB2_add_sub_one (p : ℕ) (hp : 1 ≤ p) : 1 + (p - 1) = p := by
  rw [add_comm, Nat.sub_add_cancel hp]

theorem ggNSPosPB2_exists_sep {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {p : ℕ}
    [Fact p.Prime]
    (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f + 1) (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {i j : Fin n} (hij : i ≠ j)
    (hnot : ¬ (i = a ∧ j = b) ∧ ¬ (i = b ∧ j = a)) :
    ∃ t : Su K 2 f n, ∃ d : Fin n → K,
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d ∧
      (∀ k, d k ^ p = 1) ∧ d a = d b ∧ d i ≠ d j := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcard]
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    rw [e]
    exact Dvd.dvd.mul_right hpf _
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζp : (ζ : K) ^ p = 1 := by
    have h : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hζq : (ζ : K) ^ (2 ^ f + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpf
    rw [hc, pow_mul, hζp, one_pow]
  set Sz : Finset (Fin n) := {a, b} with hSz
  have hScard : Sz.card = 2 := by simp [hSz, hab]
  have hnotS : ¬ (i ∈ Sz ∧ j ∈ Sz) := by
    rintro ⟨hi, hj⟩
    simp only [hSz, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with hj | hj
    · exact hij hj.symm
    · exact hnot.1 ⟨rfl, hj⟩
    · exact hnot.2 ⟨rfl, hj⟩
    · exact hij hj.symm
  have key : ∃ v : Fin n → ℕ, v a = v b ∧ (∑ x, v x) = p ∧ v i % p ≠ v j % p := by
    by_cases hiS : i ∈ Sz
    · have hjS : j ∉ Sz := fun hjS => hnotS ⟨hiS, hjS⟩
      obtain ⟨k, hk⟩ := ggNSPosPB2_exists_notMem hn (Sz ∪ {j}) (by
        have h1 := Finset.card_union_le Sz ({j} : Finset (Fin n))
        rw [hScard, Finset.card_singleton] at h1
        omega)
      have hkS : k ∉ Sz := fun h => hk (Finset.mem_union_left _ h)
      have hkj : k ≠ j := fun h =>
        hk (by rw [h]; exact Finset.mem_union_right _ (Finset.mem_singleton_self j))
      have ha : a ∈ Sz := by simp [hSz]
      have hb : b ∈ Sz := by simp [hSz]
      have haj : a ≠ j := fun h => hjS (h ▸ ha)
      have hak : a ≠ k := fun h => hkS (h ▸ ha)
      have hbj : b ≠ j := fun h => hjS (h ▸ hb)
      have hbk : b ≠ k := fun h => hkS (h ▸ hb)
      have hik : i ≠ k := fun h => hkS (h ▸ hiS)
      refine ⟨Pi.single (M := fun _ => ℕ) j 1 + Pi.single (M := fun _ => ℕ) k (p - 1),
        ?_, ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.single_eq_of_ne haj, Pi.single_eq_of_ne hak,
          Pi.single_eq_of_ne hbj, Pi.single_eq_of_ne hbk, add_zero]
      · have hsum : (∑ x : Fin n,
              (Pi.single (M := fun _ => ℕ) j 1 + Pi.single (M := fun _ => ℕ) k (p - 1)) x : ℕ) =
            (∑ x, Pi.single (M := fun _ => ℕ) j 1 x) +
              ∑ x, Pi.single (M := fun _ => ℕ) k (p - 1) x := Finset.sum_add_distrib
        rw [hsum, ggNSPosPB2_sum_single, ggNSPosPB2_sum_single]
        exact ggNSPosPB2_add_sub_one p (le_of_lt hp1)
      · have hvj : (Pi.single (M := fun _ => ℕ) j 1 +
            Pi.single (M := fun _ => ℕ) k (p - 1)) j = 1 := by
          simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hkj), zero_add, add_zero]
        have hvi : (Pi.single (M := fun _ => ℕ) j 1 +
            Pi.single (M := fun _ => ℕ) k (p - 1)) i = 0 := by
          simp only [Pi.add_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik, add_zero]
        rw [hvi, hvj, Nat.zero_mod, Nat.mod_eq_of_lt hp1]
        exact Nat.zero_ne_one
    · by_cases hjS : j ∈ Sz
      · have hiS' : i ∉ Sz := hiS
        obtain ⟨k, hk⟩ := ggNSPosPB2_exists_notMem hn (Sz ∪ {i}) (by
          have h1 := Finset.card_union_le Sz ({i} : Finset (Fin n))
          rw [hScard, Finset.card_singleton] at h1
          omega)
        have hkS : k ∉ Sz := fun h => hk (Finset.mem_union_left _ h)
        have hki : k ≠ i := fun h =>
          hk (by rw [h]; exact Finset.mem_union_right _ (Finset.mem_singleton_self i))
        have ha : a ∈ Sz := by simp [hSz]
        have hb : b ∈ Sz := by simp [hSz]
        have hai : a ≠ i := fun h => hiS' (h ▸ ha)
        have hak : a ≠ k := fun h => hkS (h ▸ ha)
        have hbi : b ≠ i := fun h => hiS' (h ▸ hb)
        have hbk : b ≠ k := fun h => hkS (h ▸ hb)
        have hjk : j ≠ k := fun h => hkS (h ▸ hjS)
        refine ⟨Pi.single (M := fun _ => ℕ) i 1 + Pi.single (M := fun _ => ℕ) k (p - 1),
          ?_, ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne hak,
            Pi.single_eq_of_ne hbi, Pi.single_eq_of_ne hbk, add_zero]
        · have hsum : (∑ x : Fin n,
                (Pi.single (M := fun _ => ℕ) i 1 + Pi.single (M := fun _ => ℕ) k (p - 1)) x : ℕ) =
              (∑ x, Pi.single (M := fun _ => ℕ) i 1 x) +
                ∑ x, Pi.single (M := fun _ => ℕ) k (p - 1) x := Finset.sum_add_distrib
          rw [hsum, ggNSPosPB2_sum_single, ggNSPosPB2_sum_single]
          exact ggNSPosPB2_add_sub_one p (le_of_lt hp1)
        · have hvj : (Pi.single (M := fun _ => ℕ) i 1 +
              Pi.single (M := fun _ => ℕ) k (p - 1)) j = 0 := by
            simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hjk,
              add_zero]
          have hvi : (Pi.single (M := fun _ => ℕ) i 1 +
              Pi.single (M := fun _ => ℕ) k (p - 1)) i = 1 := by
            simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hki),
              add_zero]
          rw [hvi, hvj, Nat.zero_mod, Nat.mod_eq_of_lt hp1]
          exact Nat.one_ne_zero
      · have hiS' : i ∉ Sz := hiS
        have hjS' : j ∉ Sz := hjS
        have ha : a ∈ Sz := by simp [hSz]
        have hb : b ∈ Sz := by simp [hSz]
        have hai : a ≠ i := fun h => hiS' (h ▸ ha)
        have haj : a ≠ j := fun h => hjS' (h ▸ ha)
        have hbi : b ≠ i := fun h => hiS' (h ▸ hb)
        have hbj : b ≠ j := fun h => hjS' (h ▸ hb)
        refine ⟨Pi.single (M := fun _ => ℕ) i 1 + Pi.single (M := fun _ => ℕ) j (p - 1),
          ?_, ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj,
            Pi.single_eq_of_ne hbi, Pi.single_eq_of_ne hbj, add_zero]
        · have hsum : (∑ x : Fin n,
                (Pi.single (M := fun _ => ℕ) i 1 + Pi.single (M := fun _ => ℕ) j (p - 1)) x : ℕ) =
              (∑ x, Pi.single (M := fun _ => ℕ) i 1 x) +
                ∑ x, Pi.single (M := fun _ => ℕ) j (p - 1) x := Finset.sum_add_distrib
          rw [hsum, ggNSPosPB2_sum_single, ggNSPosPB2_sum_single]
          exact ggNSPosPB2_add_sub_one p (le_of_lt hp1)
        · have hvj : (Pi.single (M := fun _ => ℕ) i 1 +
              Pi.single (M := fun _ => ℕ) j (p - 1)) j = p - 1 := by
            simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add, add_zero]
          have hvi : (Pi.single (M := fun _ => ℕ) i 1 +
              Pi.single (M := fun _ => ℕ) j (p - 1)) i = 1 := by
            simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
              add_zero]
          rw [hvi, hvj, Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
          intro h
          have hp3 : 3 ≤ p := by
            rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
            · exact absurd h2 hp2
            · omega
          omega
  obtain ⟨v, hva, hsum, hvij⟩ := key
  have hdet : ∏ k, (ζ : K) ^ (v k) = 1 := by
    rw [Finset.prod_pow_eq_pow_sum, hsum, hζp]
  have hunit : ∀ k, unitaryInvolution K 2 f ((ζ : K) ^ (v k)) * (ζ : K) ^ (v k) = 1 := by
    intro k
    rw [unitaryInvolution_apply, ← pow_mul, ← pow_add]
    rw [show v k * 2 ^ f + v k = v k * (2 ^ f + 1) by ring]
    rw [mul_comm (v k) (2 ^ f + 1), pow_mul, hζq, one_pow]
  refine ⟨ggNSPosPB2_diagSU (f := f) (fun k => (ζ : K) ^ (v k)) hdet hunit,
    fun k => (ζ : K) ^ (v k), ggNSPosPB2_diagSU_coe _ hdet hunit, ?_, ?_, ?_⟩
  · intro k
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  · show (ζ : K) ^ (v a) = (ζ : K) ^ (v b)
    rw [hva]
  · intro h
    apply hvij
    have h2 : ζ ^ (v i) = ζ ^ (v j) := Units.ext h
    have h3 := (pow_inj_mod (x := ζ)).mp h2
    rwa [hζo] at h3

end CFSG.StandardType

end
