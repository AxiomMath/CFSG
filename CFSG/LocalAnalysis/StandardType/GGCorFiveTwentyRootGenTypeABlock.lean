module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeAModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepCases
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

open scoped commutatorElement

section Block

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem eq_one_of_mem_coordBlockSL_of_mem_scalars {J : Finset (Fin d)} {m : Fin d} (hm : m ∉ J)
    {s : SpecialLinearGroup (Fin d) K} (hs : s ∈ coordBlockSL K J) (hz : s ∈ scalars d K) :
    s = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  have h1 := mem_coordBlockSL_iff.mp hs m m (Or.inl hm)
  rw [ite_eq_left rfl, hc, scalar_apply, diagonal_apply_eq] at h1
  ext i j
  rw [hc, h1, map_one]
  rfl

private theorem exists_ne_three (hd : 4 ≤ d) (a b c : Fin d) :
    ∃ m : Fin d, m ≠ a ∧ m ≠ b ∧ m ≠ c := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin d))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 : ({a, b, c} : Finset (Fin d)).card ≤ 3 := Finset.card_le_three
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2⟩

omit [CharP K 2] in
private theorem exists_diag_separating (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({k, l} : Finset (Fin d)) ≠ {i, j}) :
    ∃ t : Fin d → K, (∀ x, t x ^ p = 1) ∧ (∏ x, t x) = 1 ∧ t i = t j ∧ t k ≠ t l := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have key : ∀ m : Fin d, m ≠ i → m ≠ j → ∃ t : Fin d → K, (∀ x, t x ^ p = 1) ∧
      (∏ x, t x) = 1 ∧ t i = ζ ∧ t j = ζ ∧ ∀ x, x ≠ i → x ≠ j → x ≠ m → t x = 1 := by
    intro m hmi hmj
    refine ⟨fun x => ggPairVec i m ζ x * ggPairVec j m ζ x, fun x => ?_, ?_, ?_, ?_,
      fun x hxi hxj hxm => ?_⟩
    · rw [mul_pow, pow_ggPairVec (k := i) (l := m) hζ.pow_eq_one x,
        pow_ggPairVec (k := j) (l := m) hζ.pow_eq_one x, mul_one]
    · rw [Finset.prod_mul_distrib, prod_ggPairVec ζ hζ0, prod_ggPairVec ζ hζ0, mul_one]
    · simp [ggPairVec_apply, hij, hmi.symm]
    · simp [ggPairVec_apply, hij.symm, hmj.symm]
    · simp [ggPairVec_apply, hxi, hxj, hxm]
  by_cases hk : k ∈ ({i, j} : Finset (Fin d)) <;> by_cases hl : l ∈ ({i, j} : Finset (Fin d))
  · exact absurd (Finset.eq_of_subset_of_card_le
      (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hk
        · exact hl)
      (by rw [Finset.card_pair hij, Finset.card_pair hkl])) hne
  · have hli : l ≠ i := fun h => hl (by rw [h]; simp)
    have hlj : l ≠ j := fun h => hl (by rw [h]; simp)
    obtain ⟨m, hmi, hmj, hml⟩ := exists_ne_three hd i j l
    obtain ⟨t, ht, hprod, hti, htj, htm⟩ := key m hmi hmj
    have htk : t k = ζ := by
      rcases (by simpa using hk : k = i ∨ k = j) with h | h
      · rw [h, hti]
      · rw [h, htj]
    refine ⟨t, ht, hprod, hti.trans htj.symm, ?_⟩
    rw [htk, htm l hli hlj hml.symm]
    exact hζ1
  · have hki : k ≠ i := fun h => hk (by rw [h]; simp)
    have hkj : k ≠ j := fun h => hk (by rw [h]; simp)
    obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hd i j k
    obtain ⟨t, ht, hprod, hti, htj, htm⟩ := key m hmi hmj
    have htl : t l = ζ := by
      rcases (by simpa using hl : l = i ∨ l = j) with h | h
      · rw [h, hti]
      · rw [h, htj]
    refine ⟨t, ht, hprod, hti.trans htj.symm, ?_⟩
    rw [htl, htm k hki hkj hmk.symm]
    exact hζ1.symm
  · have hki : k ≠ i := fun h => hk (by rw [h]; simp)
    have hkj : k ≠ j := fun h => hk (by rw [h]; simp)
    have hli : l ≠ i := fun h => hl (by rw [h]; simp)
    have hlj : l ≠ j := fun h => hl (by rw [h]; simp)
    refine ⟨ggPairVec k l ζ, fun x => pow_ggPairVec (k := k) (l := l) hζ.pow_eq_one x,
      prod_ggPairVec ζ hζ0, ?_, ?_⟩
    · simp [ggPairVec_apply, hki.symm, hli.symm, hkj.symm, hlj.symm]
    · have htk : ggPairVec k l ζ k = ζ := by simp [ggPairVec_apply, hkl]
      have htl : ggPairVec k l ζ l = ζ⁻¹ := by simp [ggPairVec_apply, hkl.symm]
      rw [htk, htl]
      exact hζinv

omit [CharP K 2] in
theorem entry_eq_zero_of_mem_pairCent (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({k, l} : Finset (Fin d)) ≠ {i, j}) {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ pairCent p K i j) : (s : Matrix (Fin d) (Fin d) K) k l = 0 := by
  obtain ⟨t, htpow, hprod, hti, htk⟩ := exists_diag_separating hp hp2 hpK hd hij hkl hne
  let D : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal t, by rw [Matrix.det_diagonal]; exact hprod⟩
  have hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t := rfl
  have hDmem : D ∈ {D : SpecialLinearGroup (Fin d) K | ∃ t' : Fin d → K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal t' ∧ t' i = t' j ∧ ∀ x, t' x ^ p = 1} :=
    ⟨t, rfl, hti, htpow⟩
  have hcomm : D * s = s * D := Subgroup.mem_centralizer_iff.mp hs D hDmem
  exact (commute_diagonal_iff (s := s) (D := D) hD).mp hcomm.symm k l htk

omit [CharP K 2] in
private theorem compIndicator_comm_of_mem_pairCent (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) {i j : Fin d} (hij : i ≠ j)
    {c : SpecialLinearGroup (Fin d) K} (hc : c ∈ pairCent p K i j) :
    compIndicator K ({i, j} : Finset (Fin d)) * (c : Matrix (Fin d) (Fin d) K) =
      (c : Matrix (Fin d) (Fin d) K) * compIndicator K ({i, j} : Finset (Fin d)) := by
  ext a b
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases ha : a ∈ ({i, j} : Finset (Fin d)) <;>
    by_cases hb : b ∈ ({i, j} : Finset (Fin d))
  · simp [ha, hb]
  · rw [ite_eq_left ha, ite_eq_right hb]
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    have hne : ({a, b} : Finset (Fin d)) ≠ {i, j} := fun h => hb (h ▸ by simp)
    rw [entry_eq_zero_of_mem_pairCent hp hp2 hpK hd hij hab hne hc]
  · rw [ite_eq_right ha, ite_eq_left hb]
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    have hne : ({a, b} : Finset (Fin d)) ≠ {i, j} := fun h => ha (h ▸ by simp)
    rw [entry_eq_zero_of_mem_pairCent hp hp2 hpK hd hij hab hne hc]
  · simp [ha, hb]

omit [Finite K] [CharP K 2] in
private theorem diag2n_mem_coordBlockSL {J : Finset (Fin d)} {i j : Fin d} (hij : i ≠ j)
    (hi : i ∈ J) (hj : j ∈ J) {a : K} (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha ∈ coordBlockSL K J := by
  rw [mem_coordBlockSL_iff]
  intro r s hrs
  rw [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply]
  by_cases h : r = s
  · have hrJ : r ∉ J := by
      rcases hrs with h1 | h1
      · exact h1
      · rwa [← h] at h1
    have hri : r ≠ i := fun hri => hrJ (by rw [hri]; exact hi)
    have hrj : r ≠ j := fun hrj => hrJ (by rw [hrj]; exact hj)
    rw [ite_eq_left h, ite_eq_left h]
    simp [hri, hrj]
  · rw [ite_eq_right h, ite_eq_right h]

omit [Finite K] [CharP K 2] in
private theorem diag2n_pow_eq_one {i j : Fin d} (hij : i ≠ j) {a : K} (ha : a ≠ 0)
    {n : ℕ} (han : a ^ n = 1) :
    Matrix.SpecialLinearGroup.diag2n hij a ha ^ n = 1 := by
  apply Subtype.ext
  ext r s
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply,
    Matrix.diagonal_apply, Pi.pow_apply]
  by_cases hrs : r = s
  · rw [ite_eq_left hrs, ite_eq_left hrs]
    by_cases hri : r = i
    · rw [ite_eq_left hri]
      exact han
    · rw [ite_eq_right hri]
      by_cases hrj : r = j
      · rw [ite_eq_left hrj, inv_pow, han, inv_one]
      · rw [ite_eq_right hrj, one_pow]
  · rw [ite_eq_right hrs, ite_eq_right hrs]

omit [Finite K] [CharP K 2] in
private theorem diag2n_eq_mul {i j m : Fin d} (hij : i ≠ j) (him : i ≠ m) (hmj : m ≠ j) {c : K}
    (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij c hc =
      Matrix.SpecialLinearGroup.diag2n him c hc * Matrix.SpecialLinearGroup.diag2n hmj c hc := by
  apply Subtype.ext
  ext r s
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.SpecialLinearGroup.diag2n_coe, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · rw [ite_eq_left hrs, ite_eq_left hrs]
    by_cases hri : r = i
    · subst hri
      simp [him, hij]
    · by_cases hrj : r = j
      · subst hrj
        simp [hri, hmj.symm]
      · by_cases hrm : r = m
        · subst hrm
          simp [hri, hrj, inv_mul_cancel₀ hc]
        · simp [hri, hrj, hrm]
  · rw [ite_eq_right hrs, ite_eq_right hrs]

private theorem exists_notMem_pair (hd : 3 ≤ d) (i j : Fin d) :
    ∃ m : Fin d, m ∉ ({i, j} : Finset (Fin d)) := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ ({i, j} : Finset (Fin d)) :=
    fun m _ => h m
  have hle : d ≤ ({i, j} : Finset (Fin d)).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h2 : ({i, j} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
  omega

private theorem pair_ne_of_notMem {i j m : Fin d} (hm : m ∉ ({i, j} : Finset (Fin d))) :
    ({i, m} : Finset (Fin d)) ≠ {i, j} ∧ ({m, j} : Finset (Fin d)) ≠ {i, j} := by
  constructor <;>
  · intro h
    have hmij : m ∈ ({i, j} : Finset (Fin d)) := by
      rw [← h]; simp
    exact hm hmij

omit [Finite K] in
theorem permSL_mem_coordBlockSL {i j : Fin d} :
    permSL (Equiv.swap i j) ∈ coordBlockSL K ({i, j} : Finset (Fin d)) := by
  rw [mem_coordBlockSL_iff]
  intro a b hab
  rw [coe_permSL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rcases hab with ha | hb
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    rw [Equiv.swap_apply_of_ne_of_ne ha.1 ha.2]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    have hb' : Equiv.swap i j b = b := Equiv.swap_apply_of_ne_of_ne hb.1 hb.2
    have hiff : (Equiv.swap i j a = b) ↔ (a = b) := by
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap i j) h
        rw [Equiv.swap_apply_self i j a, hb'] at h2
        exact h2
      · intro h
        rw [h, hb']
    by_cases hab' : a = b
    · rw [ite_eq_left (hiff.mpr hab'), ite_eq_left hab']
    · rw [ite_eq_right (fun h => hab' (hiff.mp h)), ite_eq_right hab']

omit [Finite K] [CharP K 2] in
theorem iSup_coordBlockSL_pairs (hd : 3 ≤ d) (i₀ j₀ : Fin d) :
    (⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j ∧ ({i, j} : Finset (Fin d)) ≠ {i₀, j₀}),
      coordBlockSL K ({i, j} : Finset (Fin d))) = ⊤ := by
  let S : Subgroup (SpecialLinearGroup (Fin d) K) :=
    ⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j ∧ ({i, j} : Finset (Fin d)) ≠ {i₀, j₀}),
      coordBlockSL K ({i, j} : Finset (Fin d))
  change S = ⊤
  have hSmem : ∀ {i j : Fin d} (_ : i ≠ j) (_ : ({i, j} : Finset (Fin d)) ≠ {i₀, j₀}),
      coordBlockSL K ({i, j} : Finset (Fin d)) ≤ S := by
    intro i j hij hne x hx
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem ⟨hij, hne⟩ hx))
  have hmid : ∀ {i j : Fin d}, ({i, j} : Finset (Fin d)) = {i₀, j₀} →
      ∃ m : Fin d, i ≠ m ∧ m ≠ j ∧ ({i, m} : Finset (Fin d)) ≠ {i₀, j₀} ∧
        ({m, j} : Finset (Fin d)) ≠ {i₀, j₀} := by
    intro i j hne'
    obtain ⟨m, hm'⟩ := exists_notMem_pair hd i j
    have hm := hm'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact ⟨m, Ne.symm hm.1, hm.2, hne' ▸ (pair_ne_of_notMem hm').1,
      hne' ▸ (pair_ne_of_notMem hm').2⟩
  have hcomm : ∀ x y : SpecialLinearGroup (Fin d) K, x ∈ S → y ∈ S → ⁅x, y⁆ ∈ S := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
  have htrans : ∀ (i j : Fin d) (hij : i ≠ j) (a : K),
      Matrix.SpecialLinearGroup.transvection hij a ∈ S := by
    intro i j hij a
    by_cases hne : ({i, j} : Finset (Fin d)) = {i₀, j₀}
    · obtain ⟨m, him, hmj, hne_im, hne_mj⟩ := hmid hne
      have hx := hSmem him hne_im (SLRep.transvection_mem_coordBlockSL (by simp) (by simp) him a)
      have hy := hSmem hmj hne_mj (SLRep.transvection_mem_coordBlockSL (by simp) (by simp) hmj 1)
      have hc := hcomm _ _ hx hy
      rwa [Matrix.SpecialLinearGroup.commutatorElement_transvection him hmj hij a 1,
        mul_one] at hc
    · exact hSmem hij hne (SLRep.transvection_mem_coordBlockSL (by simp) (by simp) hij a)
  have hdiag : ∀ (i j : Fin d) (hij : i ≠ j) {c : K} (hc : c ≠ 0),
      Matrix.SpecialLinearGroup.diag2n hij c hc ∈ S := by
    intro i j hij c hc
    by_cases hne : ({i, j} : Finset (Fin d)) = {i₀, j₀}
    · obtain ⟨m, him, hmj, hne_im, hne_mj⟩ := hmid hne
      rw [diag2n_eq_mul hij him hmj hc]
      exact S.mul_mem (hSmem him hne_im (diag2n_mem_coordBlockSL him (by simp) (by simp) hc))
        (hSmem hmj hne_mj (diag2n_mem_coordBlockSL hmj (by simp) (by simp) hc))
    · exact hSmem hij hne (diag2n_mem_coordBlockSL hij (by simp) (by simp) hc)
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Subgroup.eq_top_iff']
  intro M
  exact Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun x => x ∈ S) M
    hdiag htrans (fun A B hA hB => S.mul_mem hA hB)

omit [Finite K] [CharP K 2] in
theorem coordBlockSL_erase_sup_eq_top (hd : 3 ≤ d) {i j : Fin d} (hij : i ≠ j) :
    coordBlockSL K (Finset.univ.erase i) ⊔ coordBlockSL K (Finset.univ.erase j) = ⊤ := by
  have hmono : ∀ {J J' : Finset (Fin d)}, J ⊆ J' →
      coordBlockSL K J ≤ coordBlockSL K J' := by
    intro J J' hJJ' g hg
    rw [mem_coordBlockSL_iff] at hg ⊢
    intro r s hrs
    exact hg r s (by
      rcases hrs with hr | hs
      · exact Or.inl fun hrJ => hr (hJJ' hrJ)
      · exact Or.inr fun hsJ => hs (hJJ' hsJ))
  apply top_le_iff.mp
  rw [← iSup_coordBlockSL_pairs (K := K) hd i j]
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  rintro ⟨-, hne⟩
  have hpair : ({a, b} : Finset (Fin d)) ⊆ Finset.univ.erase i ∨
      ({a, b} : Finset (Fin d)) ⊆ Finset.univ.erase j := by
    by_cases hai : a = i
    · right
      have hbj : b ≠ j := by
        intro hbj
        exact hne (by rw [hai, hbj])
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxa | hxb
      · rw [hxa, hai]
        exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
      · rw [hxb]
        exact Finset.mem_erase.mpr ⟨hbj, Finset.mem_univ _⟩
    · by_cases hbi : b = i
      · right
        have haj : a ≠ j := by
          intro haj
          exact hne (by rw [hbi, haj, Finset.pair_comm])
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxa | hxb
        · rw [hxa]
          exact Finset.mem_erase.mpr ⟨haj, Finset.mem_univ _⟩
        · rw [hxb, hbi]
          exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
      · left
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hai, Finset.mem_univ x⟩
        · exact Finset.mem_erase.mpr ⟨hbi, Finset.mem_univ x⟩
  rcases hpair with hsub | hsub
  · exact (hmono hsub).trans le_sup_left
  · exact (hmono hsub).trans le_sup_right

omit [Finite K] in
theorem map_conj_permSL_coordBlockSL_erase [CharP K 2] {i j : Fin d} (hij : i ≠ j) :
    (coordBlockSL K (Finset.univ.erase i)).map
      (MulAut.conj (permSL (Equiv.swap i j))).toMonoidHom =
      coordBlockSL K (Finset.univ.erase j) := by
  have hconj (x : SpecialLinearGroup (Fin d) K) (a b : Fin d) :
      (((permSL (Equiv.swap i j) * x * (permSL (Equiv.swap i j))⁻¹ :
          SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) a b) =
        (x : Matrix (Fin d) (Fin d) K) (Equiv.swap i j a) (Equiv.swap i j b) := by
    rw [permSL_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_permSL, coe_permSL, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      submatrix_submatrix, Equiv.Perm.inv_def, Equiv.symm_symm]
    rfl
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_coordBlockSL_iff] at hx ⊢
    intro a b hab
    change (((permSL (Equiv.swap i j) * x * (permSL (Equiv.swap i j))⁻¹ :
      SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) a b) = _
    rw [hconj]
    have hmem : (Equiv.swap i j a) ∉ Finset.univ.erase i ∨
        (Equiv.swap i j b) ∉ Finset.univ.erase i := by
      rcases hab with ha | hb
      · left
        have haj : a = j := by simpa using ha
        rw [haj]
        simp
      · right
        have hbj : b = j := by simpa using hb
        rw [hbj]
        simp
    simpa only [Equiv.apply_eq_iff_eq] using
      hx (Equiv.swap i j a) (Equiv.swap i j b) hmem
  · intro y hy
    rw [mem_coordBlockSL_iff] at hy
    refine Subgroup.mem_map.mpr
      ⟨(permSL (Equiv.swap i j))⁻¹ * y * permSL (Equiv.swap i j), ?_, ?_⟩
    · rw [mem_coordBlockSL_iff]
      intro a b hab
      have hPP : (permSL (Equiv.swap i j) : SpecialLinearGroup (Fin d) K)⁻¹ =
          permSL (Equiv.swap i j) := by
        rw [permSL_inv, Equiv.swap_inv]
      have hx_eq : (permSL (Equiv.swap i j))⁻¹ * y * permSL (Equiv.swap i j) =
          permSL (Equiv.swap i j) * y * (permSL (Equiv.swap i j))⁻¹ := by
        rw [hPP]
      rw [hx_eq]
      change (((permSL (Equiv.swap i j) * y * (permSL (Equiv.swap i j))⁻¹ :
        SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) a b) = _
      rw [hconj]
      have hmem : (Equiv.swap i j a) ∉ Finset.univ.erase j ∨
          (Equiv.swap i j b) ∉ Finset.univ.erase j := by
        rcases hab with ha | hb
        · left
          have hai : a = i := by simpa using ha
          rw [hai]
          simp
        · right
          have hbi : b = i := by simpa using hb
          rw [hbi]
          simp
      simpa only [Equiv.apply_eq_iff_eq] using
        hy (Equiv.swap i j a) (Equiv.swap i j b) hmem
    · change (MulAut.conj (permSL (Equiv.swap i j)))
        ((permSL (Equiv.swap i j))⁻¹ * y * permSL (Equiv.swap i j)) = y
      rw [MulAut.conj_apply]
      group

omit [Finite K] in
theorem coordBlockSL_erase_sup_conj_eq_top [CharP K 2] (hd : 3 ≤ d) {i j : Fin d}
    (hij : i ≠ j) :
    coordBlockSL K (Finset.univ.erase i) ⊔
      (coordBlockSL K (Finset.univ.erase i)).map
        (MulAut.conj (permSL (Equiv.swap i j))).toMonoidHom = ⊤ := by
  rw [map_conj_permSL_coordBlockSL_erase (K := K) hij]
  exact coordBlockSL_erase_sup_eq_top (K := K) hd hij

section Pair

variable {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
  {A : Subgroup (MulAut L')}

omit [Finite K] [Finite L'] in
theorem conj_permSL_comm_conj_iff (hpd : Nat.Coprime p d)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (i j : Fin d) {D : SpecialLinearGroup (Fin d) K}
    {t : Fin d → K} (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (hDp : D ^ p = 1) :
    MulAut.conj (φ (permSL (Equiv.swap i j))) * MulAut.conj (φ D) =
      MulAut.conj (φ D) * MulAut.conj (φ (permSL (Equiv.swap i j))) ↔ t i = t j := by
  set P : SpecialLinearGroup (Fin d) K := permSL (Equiv.swap i j) with hP
  constructor
  · intro h
    have hconj : MulAut.conj (φ P) * MulAut.conj (φ D) * (MulAut.conj (φ P))⁻¹ =
        MulAut.conj (φ D) := by
      rw [h]
      group
    have hacts : GGActsBy φ (MulAut.conj (φ D)) D := ggActsBy_conj_phi φ D
    have hacts' : GGActsBy φ (MulAut.conj (φ D)) (P * D * P⁻¹) := by
      rw [← hconj]
      exact (ggActsBy_conj_phi φ D).conj P
    have hD' : ((P * D * P⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (t ∘ Equiv.swap i j) := by
      rw [hP]
      exact coe_permSL_conj hD (Equiv.swap i j)
    have ht : ∀ x, t x ^ p = 1 := fun x => pow_eq_one_of_diagonal hD hDp x
    have ht' : ∀ x, (t ∘ Equiv.swap i j) x ^ p = 1 := fun x =>
      pow_eq_one_of_diagonal hD hDp (Equiv.swap i j x)
    have hteq : t = t ∘ Equiv.swap i j :=
      GGActsBy.diag_eq hφker hpd (Fin.pos i) hD hD' ht ht' hacts hacts'
    have h := congrFun hteq i
    simpa [Function.comp_apply, Equiv.swap_apply_left] using h
  · intro hti
    have hcomp : t ∘ Equiv.swap i j = t := by
      funext x
      rw [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1]
        exact hti.symm
      · rw [h2]
        exact hti
      · rfl
    have hPDP : P * D * P⁻¹ = D := by
      apply Subtype.ext
      rw [hP, coe_permSL_conj hD (Equiv.swap i j), hcomp]
      exact hD.symm
    have hPD : P * D = D * P := by
      calc P * D = P * D * P⁻¹ * P := by group
        _ = D * P := by rw [hPDP]
    simp only [← map_mul, hPD]

omit [Finite K] [Finite L'] in
theorem ggHypCent_permSL_eq (hpd : Nat.Coprime p d) (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (hM : IsDiagTorusModel p φ A) (i j : Fin d) :
    ggHypCent A (φ (permSL (Equiv.swap i j))) = (pairCent p K i j).map φ := by
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  constructor
  · intro hl
    unfold ggHypCent at hl
    simp only [Subgroup.mem_iInf, mem_ggFix] at hl
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    unfold pairCent
    rw [Subgroup.mem_centralizer_iff]
    intro D' hD'mem
    obtain ⟨t', hD't, ht'ij, ht'p⟩ := hD'mem
    have hD'p : D' ^ p = 1 := pow_eq_one_of_pow_diagonal hD't ht'p
    have hcomm := (conj_permSL_comm_conj_iff hpd hφker i j hD't hD'p).mpr ht'ij
    have hmem : MulAut.conj (φ D') ∈ A :=
      (hM _).mpr ⟨D', ⟨t', hD't⟩, hD'p, rfl⟩
    have hfix : MulAut.conj (φ D') (φ s) = φ s :=
      hl (MulAut.conj (φ D')) ⟨hmem, hcomm⟩
    have hfix' : φ (D' * s * D'⁻¹) = φ s := by
      rw [← ggActsBy_conj_phi φ D' s]
      exact hfix
    have hcent := mem_centralizer_of_apply_eq hφker hpd hD'p hfix'
    exact (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
  · intro hl
    unfold ggHypCent
    simp only [Subgroup.mem_iInf]
    intro a ha
    rw [mem_ggFix]
    obtain ⟨haA, hcomm⟩ := ha
    obtain ⟨D, ⟨t, hDt⟩, hDp, haeq⟩ := (hM a).mp haA
    obtain ⟨s', hs', hφs'⟩ := Subgroup.mem_map.mp hl
    have htij : t i = t j := by
      have h := hcomm
      rw [haeq] at h
      exact (conj_permSL_comm_conj_iff hpd hφker i j hDt hDp).mp h
    have hDmem : D ∈ {D : SpecialLinearGroup (Fin d) K | ∃ t : Fin d → K,
        (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ t i = t j ∧ ∀ k, t k ^ p = 1} :=
      ⟨t, hDt, htij, fun k => pow_eq_one_of_diagonal hDt hDp k⟩
    have hDs' : D * s' = s' * D := Subgroup.mem_centralizer_iff.mp hs' D hDmem
    rw [haeq]
    calc MulAut.conj (φ D) (φ s) = MulAut.conj (φ D) (φ s') := by rw [hφs']
      _ = φ s' := by
          rw [ggActsBy_conj_phi φ D s', hDs']
          congr 1
          group
      _ = φ s := hφs'

omit [CharP K 2] [Finite L'] in
theorem isComponentOf_coordBlockSL_pair (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (h4 : 4 ≤ Nat.card K) (hd : 4 ≤ d) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {i j : Fin d} (hij : i ≠ j) :
    IsComponentOf ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ)
      ((pairCent p K i j).map φ) := by
  set C := pairCent p K i j with hC
  set J₀ := coordBlockSL K ({i, j} : Finset (Fin d)) with hJ₀
  have hJ₀C : J₀ ≤ C := by
    intro s hs
    rw [hJ₀] at hs
    rw [hC]
    unfold pairCent
    refine Subgroup.mem_centralizer_iff.mpr fun D hD => ?_
    obtain ⟨t, hDt, hti, -⟩ := hD
    refine ((commute_diagonal_iff (s := s) (D := D) hDt).mpr ?_).symm
    intro a b hab
    have hnotboth : a ∉ ({i, j} : Finset (Fin d)) ∨ b ∉ ({i, j} : Finset (Fin d)) := by
      by_contra h
      push Not at h
      obtain ⟨ha, hb⟩ := h
      rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hab rfl
      · exact hab hti
      · exact hab hti.symm
      · exact hab rfl
    have habne : a ≠ b := fun h => hab (by rw [h])
    rw [mem_coordBlockSL_iff.mp hs a b hnotboth, ite_eq_right habne]
  have hJn : ∀ c ∈ C, ∀ x ∈ J₀, c * x * c⁻¹ ∈ J₀ := by
    intro c hc x hx
    rw [hC] at hc
    rw [hJ₀] at hx ⊢
    exact conj_mem_coordBlockSL
      (compIndicator_comm_of_mem_pairCent hp hp2 hpK hd hij hc) hx
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin d))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
      omega)
  have hinj : ∀ x ∈ J₀, φ x = 1 → x = 1 := by
    intro x hx h1
    rw [hJ₀] at hx
    exact eq_one_of_mem_coordBlockSL_of_mem_scalars hm hx (hφker x h1)
  have hq : CFSG.IsQuasisimple J₀ := by
    rw [hJ₀]
    exact isQuasisimple_coordBlockSL (k := K) (J := ({i, j} : Finset (Fin d)))
      (by rw [Finset.card_pair hij]) h4
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple (J₀.map φ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJF : J₀.map φ ≤ C.map φ := Subgroup.map_mono hJ₀C
  have hJn' : ((J₀.map φ).subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc j hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

omit [CharP K 2] [Finite L'] in
theorem dvd_card_coordBlockSL_pair (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {i j : Fin d} (hij : i ≠ j) :
    p ∣ Nat.card ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set D₁ : SpecialLinearGroup (Fin d) K := Matrix.SpecialLinearGroup.diag2n hij ζ hζ0 with hD1
  have hD1_mem : D₁ ∈ coordBlockSL K ({i, j} : Finset (Fin d)) := by
    rw [hD1]
    exact diag2n_mem_coordBlockSL hij (by simp) (by simp) hζ0
  have hD1_pow : D₁ ^ p = 1 := by
    rw [hD1]
    exact diag2n_pow_eq_one hij hζ0 hζ.pow_eq_one
  have hD1_ne_one : D₁ ≠ 1 := by
    intro h
    have hii : (D₁ : Matrix (Fin d) (Fin d) K) i i = 1 := by rw [h]; simp
    rw [hD1, Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply_eq] at hii
    simp at hii
    exact hζ1 hii
  have hφD1_ne : φ D₁ ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := exists_notMem_pair hd i j
    exact hD1_ne_one (eq_one_of_mem_coordBlockSL_of_mem_scalars hm hD1_mem (hφker D₁ h))
  have hD1φ_pow : (φ D₁) ^ p = 1 := by rw [← map_pow, hD1_pow, map_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : φ D₁ ∈ (coordBlockSL K ({i, j} : Finset (Fin d))).map φ := ⟨D₁, hD1_mem, rfl⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [orderOf_eq_prime hD1φ_pow hφD1_ne] at hdvd

end Pair

end Block

end CFSG.StandardType.TypeA

end
