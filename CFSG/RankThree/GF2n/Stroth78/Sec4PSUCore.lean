module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreGroup
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUF4

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4PSU

open Matrix CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Fischer.Classification.Unitary
open CFSG.SeitzReduction.LinearPilot (blockMatrix blockMatrix_apply blockMatrix_mul det_blockMatrix)
open CFSG.Blueprint.Fischer (K)
open CFSG.Fischer (F4)
open scoped commutatorElement

theorem hK : UnitaryFieldData 2 1 K := unitaryFieldDataOfCard card_K

theorem bar_apply_K (c : K) : hK.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

noncomputable abbrev toK {ι : Type*} (M : Matrix ι ι F4) : Matrix ι ι K := M.map eF4

theorem toK_mul {ι : Type*} [Fintype ι] (M N : Matrix ι ι F4) :
    toK (M * N) = toK M * toK N :=
  Matrix.map_mul (f := eF4.toRingHom)

theorem toK_one {ι : Type*} [Fintype ι] [DecidableEq ι] : toK (1 : Matrix ι ι F4) = 1 :=
  Matrix.map_one (f := eF4.toRingHom) eF4.map_zero eF4.map_one

theorem toK_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι F4}
    (hM : (M.map (· ^ 2))ᵀ * M = 1) : ((toK M).map hK.bar)ᵀ * toK M = 1 := by
  have e : (toK M).map hK.bar = toK (M.map (· ^ 2)) := by
    ext a b
    simp [toK, bar_apply_K, map_pow]
  rw [e, ← Matrix.transpose_map, ← toK_mul, hM, toK_one]

theorem det_toK {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F4) :
    (toK M).det = eF4 M.det :=
  (RingHom.map_det eF4.toRingHom M).symm

theorem swapZeroOne_eq_permMatrix :
    swapZeroOne = (Equiv.swap (0 : Fin 3) 1).permMatrix F4 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapZeroOne, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_def]

theorem toK_permMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    toK (σ.permMatrix F4) = σ.permMatrix K := by
  ext a b
  simp only [toK, Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

section Embed

variable {n : ℕ} (I : Finset (Fin n)) (e : Fin 3 ≃ I)

@[expose] noncomputable def emb3 (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin n) (Fin n) K :=
  blockMatrix I (reindex e e M)

theorem emb3_mul (M N : Matrix (Fin 3) (Fin 3) K) :
    emb3 I e (M * N) = emb3 I e M * emb3 I e N := by
  rw [emb3, emb3, emb3, ← blockMatrix_mul, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv]

theorem det_emb3 (M : Matrix (Fin 3) (Fin 3) K) : (emb3 I e M).det = M.det := by
  rw [emb3, det_blockMatrix, det_reindex_self]

theorem emb3_unitary {M : Matrix (Fin 3) (Fin 3) K} (hM : (M.map hK.bar)ᵀ * M = 1) :
    ((emb3 I e M).map hK.bar)ᵀ * emb3 I e M = 1 :=
  blockMatrix_unitary hK I (reindex_unitary hK e hM)

@[expose] noncomputable def emb3SU (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hM : (M.map hK.bar)ᵀ * M = 1) : unitarySU 2 1 K n :=
  ofSL hK ⟨emb3 I e M, by rw [det_emb3, hdet]⟩ (emb3_unitary I e hM)

theorem coe_emb3SU (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hM : (M.map hK.bar)ᵀ * M = 1) :
    (((emb3SU I e M hdet hM : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      emb3 I e M :=
  rfl

theorem emb3SU_mem_unitaryBlock {L : Finset (Fin n)} (hIL : I ⊆ L)
    (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1) (hM : (M.map hK.bar)ᵀ * M = 1) :
    emb3SU I e M hdet hM ∈ unitaryBlock hK L := by
  intro r c hrc
  change emb3 I e M r c = (1 : Matrix (Fin n) (Fin n) K) r c
  rw [emb3, blockMatrix_apply, dif_neg]
  rintro ⟨hr, hc⟩
  rcases hrc with hr' | hc'
  · exact hr' (hIL hr)
  · exact hc' (hIL hc)

theorem emb3_permMatrix (σ : Equiv.Perm (Fin 3)) :
    emb3 I e (σ.permMatrix K) = (σ.extendDomain e).permMatrix K := by
  ext r c
  rw [emb3, blockMatrix_apply]
  by_cases hrc : r ∈ I ∧ c ∈ I
  · obtain ⟨hr, hc⟩ := hrc
    rw [dif_pos ⟨hr, hc⟩, reindex_apply, submatrix_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    rw [Equiv.Perm.extendDomain_apply_subtype σ e hr]
    have hiff : σ (e.symm ⟨r, hr⟩) = e.symm ⟨c, hc⟩ ↔ (e (σ (e.symm ⟨r, hr⟩)) : Fin n) = c := by
      constructor
      · intro h1
        rw [h1, Equiv.apply_symm_apply]
      · intro h1
        apply e.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h1
    by_cases h1 : σ (e.symm ⟨r, hr⟩) = e.symm ⟨c, hc⟩
    · rw [if_pos h1, if_pos (hiff.1 h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.2 h2))]
  · rw [dif_neg hrc]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    by_cases hr : r ∈ I
    · have hc : c ∉ I := fun hc => hrc ⟨hr, hc⟩
      have hne : r ≠ c := fun h' => hc (h' ▸ hr)
      rw [one_apply_ne hne, if_neg]
      intro h'
      apply hc
      rw [← h', Equiv.Perm.extendDomain_apply_subtype σ e hr]
      exact Subtype.mem _
    · rw [Equiv.Perm.extendDomain_apply_not_subtype σ e hr, one_apply]

end Embed

theorem extendDomain_swap_zero_one {n : ℕ} {I : Finset (Fin n)} (e : Fin 3 ≃ I) :
    (Equiv.swap (0 : Fin 3) 1).extendDomain e = Equiv.swap (e 0 : Fin n) (e 1) := by
  have hinj : Function.Injective (fun y : Fin 3 => (e y : Fin n)) :=
    fun a b hab => e.injective (Subtype.ext hab)
  ext x
  by_cases hx : x ∈ I
  · rw [Equiv.Perm.extendDomain_apply_subtype _ e hx]
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    have hxy : x = (e y : Fin n) := by rw [hy]
    have hs : e.symm ⟨x, hx⟩ = y := by rw [← hy, Equiv.symm_apply_apply]
    rw [hs, hxy, hinj.swap_apply]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ e hx, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' => hx (h' ▸ (e 0).2)
    · exact fun h' => hx (h' ▸ (e 1).2)

section Swap

variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

theorem aK_unitary : ((toK swapCommA).map hK.bar)ᵀ * toK swapCommA = 1 :=
  toK_unitary swapCommA_unitary

theorem bK_unitary : ((toK swapCommB).map hK.bar)ᵀ * toK swapCommB = 1 :=
  toK_unitary swapCommB_unitary

theorem det_aK : (toK swapCommA).det = 1 := by
  rw [det_toK, det_swapCommA, map_one]

theorem det_bK : (toK swapCommB).det = 1 := by
  rw [det_toK, det_swapCommB, map_one]

theorem toK_swapComm :
    toK swapCommA * toK swapCommB =
      (Equiv.swap (0 : Fin 3) 1).permMatrix K * (toK swapCommB * toK swapCommA) := by
  rw [← toK_permMatrix, ← swapZeroOne_eq_permMatrix, ← toK_mul, ← toK_mul, ← toK_mul,
    swapCommA_mul_swapCommB, Matrix.mul_assoc]

theorem exists_swap_mem_commutator (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) :
    ∃ u ∈ ({i, j}ᶜ : Finset (Fin n)), ∃ w ∈ ({i, j}ᶜ : Finset (Fin n)), u ≠ w ∧
      permSU hK (Equiv.swap u w) ∈
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆ := by
  obtain ⟨I, hIJ, hI⟩ := Finset.exists_subset_card_eq hJ
  set e : Fin 3 ≃ I := (I.equivFinOfCardEq hI).symm
  set A := emb3SU I e (toK swapCommA) det_aK aK_unitary
  set B := emb3SU I e (toK swapCommB) det_bK bK_unitary
  have hA : A ∈ Subgroup.centralizer {tvTransSU hK hij} :=
    unitaryBlock_le_centralizer_tvTransSU hK hij (emb3SU_mem_unitaryBlock I e hIJ _ _ _)
  have hB : B ∈ Subgroup.centralizer {tvTransSU hK hij} :=
    unitaryBlock_le_centralizer_tvTransSU hK hij (emb3SU_mem_unitaryBlock I e hIJ _ _ _)
  refine ⟨e 0, hIJ (e 0).2, e 1, hIJ (e 1).2, fun h => ?_, ?_⟩
  · have := e.injective (Subtype.ext h)
    exact absurd this (by decide)
  · have hcomm : ⁅A, B⁆ = permSU hK (Equiv.swap (e 0 : Fin n) (e 1)) := by
      apply commutatorElement_eq_of_mul_eq
      apply eq_of_coe_eq
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, coe_emb3SU, coe_emb3SU, coe_permSU, ← emb3_mul, toK_swapComm, emb3_mul,
        emb3_mul, emb3_permMatrix, extendDomain_swap_zero_one]
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hA hB

end Swap

section Block

variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

@[expose] noncomputable def blockHom :
    ↥(Subgroup.centralizer {tvTransSU hK hij}) →* GL ({i, j}ᶜ : Finset (Fin n)) K where
  toFun g :=
    ⟨tvBlock i j (((g : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      tvBlock i j ((((g⁻¹ : ↥(Subgroup.centralizer {tvTransSU hK hij})) : unitarySU 2 1 K n) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      by
        rw [← tvBlock_mul_of_mem_centralizer hK hij g.2 (g⁻¹).2, ← Subgroup.coe_mul,
          mul_inv_cancel, Subgroup.coe_one, Subgroup.coe_one, Units.val_one, tvBlock_one],
      by
        rw [← tvBlock_mul_of_mem_centralizer hK hij (g⁻¹).2 g.2, ← Subgroup.coe_mul,
          inv_mul_cancel, Subgroup.coe_one, Subgroup.coe_one, Units.val_one, tvBlock_one]⟩
  map_one' := Units.ext (by
    change tvBlock i j (((1 : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Subgroup.coe_one, Units.val_one, tvBlock_one])
  map_mul' g g' := Units.ext (tvBlock_mul_of_mem_centralizer hK hij g.2 g'.2)

theorem eq_one_of_pow_two_pow_eq_one {μ : K} (hμ : μ ≠ 0) {k : ℕ} (hk : μ ^ 2 ^ k = 1) :
    μ = 1 := by
  have h3 : μ ^ 3 = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have := FiniteField.pow_card_sub_one_eq_one μ hμ
    rwa [show Fintype.card K = 4 by rw [← Nat.card_eq_fintype_card, card_K]; rfl] at this
  have hu : IsUnit μ := isUnit_iff_ne_zero.mpr hμ
  have hd3 : orderOf μ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf μ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf μ = 1 := Nat.eq_one_of_dvd_coprimes hcop hd3 hd2
  exact orderOf_eq_one_iff.mp h1

theorem fix_tvVec_of_pow_two_pow_eq_one {g : unitarySU 2 1 K n}
    (hg : g ∈ Subgroup.centralizer {tvTransSU hK hij}) {k : ℕ} (hgk : g ^ 2 ^ k = 1) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = tvVec i j ∧
      tvVec i j ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvVec i j := by
  obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff hK hij).1 hg
  have hμ0 : μ ≠ 0 := (inv_mulVec_tvVec hij h1).1
  have hpow : ∀ m : ℕ, (((g ^ m : unitarySU 2 1 K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = μ ^ m • tvVec i j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, h1,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hμ : μ ^ 2 ^ k = 1 := by
    have e := hpow (2 ^ k)
    rw [hgk, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at e
    have e2 := congrFun e i
    rw [Pi.smul_apply, tvVec_left hij, smul_eq_mul, mul_one] at e2
    exact e2.symm
  have hμ1 := eq_one_of_pow_two_pow_eq_one hμ0 hμ
  subst hμ1
  exact ⟨by rw [h1, one_smul], by rw [h2, one_smul]⟩

end Block

section Irred

variable {n : ℕ} {i j : Fin n}

theorem norm_K_eq_cube (c : K) : hK.norm c = c ^ 3 := by
  rw [UnitaryFieldData.norm, bar_apply_K]
  ring

theorem tvBlock_diagonal (d : Fin n → K) :
    tvBlock i j (diagonal d) = diagonal (fun a : ({i, j}ᶜ : Finset (Fin n)) => d a) := by
  ext a b
  rw [tvBlock_apply]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ (fun h => hab (Subtype.ext h)), diagonal_apply_ne _ hab]

theorem perm_mem_compl {c : Equiv.Perm (Fin n)} (hci : c i = i) (hcj : c j = j)
    {a : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) : c a ∈ ({i, j}ᶜ : Finset (Fin n)) := by
  refine mem_compl_of_ne (fun h => ne_left_of_mem_compl ha ?_)
    (fun h => ne_right_of_mem_compl ha ?_)
  · rw [← hci] at h
    exact c.injective h
  · rw [← hcj] at h
    exact c.injective h

theorem tvBlock_permMatrix_mulVec {c : Equiv.Perm (Fin n)} (hci : c i = i) (hcj : c j = j)
    (x : ({i, j}ᶜ : Finset (Fin n)) → K) (a : ({i, j}ᶜ : Finset (Fin n))) :
    (tvBlock i j (c.permMatrix K) *ᵥ x) a = x ⟨c a, perm_mem_compl hci hcj a.2⟩ := by
  rw [mulVec, dotProduct, Finset.sum_eq_single ⟨c a, perm_mem_compl hci hcj a.2⟩]
  · simp [tvBlock_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro b _ hb
    have : c a ≠ b := fun h => hb (Subtype.ext h.symm)
    simp [tvBlock_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

@[expose] noncomputable def dKL (k l : Fin n) : Fin n → K :=
  Pi.mulSingle k ω * Pi.mulSingle l (ω ^ 2)

theorem diagKL_spec {k l : Fin n} (hkl : k ≠ l) :
    (∀ a, hK.norm (dKL k l a) = 1) ∧ ∏ a, dKL k l a = 1 ∧ dKL k l k = ω ∧ dKL k l l = ω ^ 2 ∧
      ∀ a, a ≠ k → a ≠ l → dKL k l a = 1 := by
  set d := dKL k l with hd
  have hdk : d k = ω := by
    simp only [hd, dKL, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hkl, mul_one]
  have hdl : d l = ω ^ 2 := by
    simp only [hd, dKL, Pi.mul_apply, Pi.mulSingle_eq_of_ne hkl.symm, Pi.mulSingle_eq_same,
      one_mul]
  have hdo : ∀ a, a ≠ k → a ≠ l → d a = 1 := fun a hak hal => by
    simp only [hd, dKL, Pi.mul_apply, Pi.mulSingle_eq_of_ne hak, Pi.mulSingle_eq_of_ne hal,
      mul_one]
  refine ⟨fun a => ?_, ?_, hdk, hdl, hdo⟩
  · rw [norm_K_eq_cube]
    by_cases hak : a = k
    · rw [hak, hdk, omega_cube]
    · by_cases hal : a = l
      · rw [hal, hdl, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, omega_cube, one_pow]
      · rw [hdo a hak hal, one_pow]
  · simp only [hd, dKL, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← pow_succ', omega_cube]

@[expose] noncomputable def dSU {k l : Fin n} (hkl : k ≠ l) : unitarySU 2 1 K n :=
  diagSU hK (dKL k l) (diagKL_spec hkl).1 (diagKL_spec hkl).2.1

theorem coe_dSU {k l : Fin n} (hkl : k ≠ l) :
    (((dSU hkl : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (dKL k l) :=
  rfl

theorem dSU_mem_unitaryBlock {I : Finset (Fin n)} {k l : Fin n} (hkl : k ≠ l) (hk : k ∈ I)
    (hl : l ∈ I) : dSU hkl ∈ unitaryBlock hK I :=
  diagSU_mem_unitaryBlock hK _ _ _ fun a ha =>
    (diagKL_spec hkl).2.2.2.2 a (fun h => ha (h ▸ hk)) (fun h => ha (h ▸ hl))

theorem swap_mul_swap_apply_of_ne {k l p a : Fin n} (hak : a ≠ k) (hal : a ≠ l) (hap : a ≠ p) :
    (Equiv.swap k l * Equiv.swap k p) a = a := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hak hap,
    Equiv.swap_apply_of_ne_of_ne hak hal]

theorem swap_mul_swap_fix {k l p : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hp : p ∈ ({i, j}ᶜ : Finset (Fin n))) :
    (Equiv.swap k l * Equiv.swap k p) i = i ∧ (Equiv.swap k l * Equiv.swap k p) j = j :=
  ⟨swap_mul_swap_apply_of_ne (ne_left_of_mem_compl hk).symm (ne_left_of_mem_compl hl).symm
      (ne_left_of_mem_compl hp).symm,
    swap_mul_swap_apply_of_ne (ne_right_of_mem_compl hk).symm (ne_right_of_mem_compl hl).symm
      (ne_right_of_mem_compl hp).symm⟩

theorem eq_top_of_torus_threeCycle_invariant (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    (S : Submodule K (({i, j}ᶜ : Finset (Fin n)) → K)) (hS : S ≠ ⊥)
    (hD : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), k ≠ l →
      ∀ x ∈ S, diagonal (fun a : ({i, j}ᶜ : Finset (Fin n)) => dKL k l a) *ᵥ x ∈ S)
    (hC : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)),
      ∀ p ∈ ({i, j}ᶜ : Finset (Fin n)), k ≠ l → k ≠ p → l ≠ p →
      ∀ x ∈ S, tvBlock i j ((Equiv.swap k l * Equiv.swap k p).permMatrix K) *ᵥ x ∈ S) :
    S = ⊤ := by
  classical
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx0
  obtain ⟨l, hl, hlk⟩ := Finset.exists_mem_ne (by omega : 1 < ({i, j}ᶜ : Finset (Fin n)).card)
    (k : Fin n)
  obtain ⟨-, -, hdk, hdl, hdo⟩ := diagKL_spec (fun h => hlk h.symm)
  set d : Fin n → K := dKL (k : Fin n) l with hd
  have hDS := hD k k.2 l hl (fun h => hlk h.symm)
  set D := diagonal (fun a : ({i, j}ᶜ : Finset (Fin n)) => d a) with hDdef
  have hy : D *ᵥ (D *ᵥ x) + (1 + ω ^ 2) • (D *ᵥ x) + ω ^ 2 • x ∈ S :=
    S.add_mem (S.add_mem (hDS _ (hDS _ hxS)) (S.smul_mem _ (hDS _ hxS))) (S.smul_mem _ hxS)
  have key : ∀ t u : K, t * (t * u) + (1 + ω ^ 2) * (t * u) + ω ^ 2 * u =
      (t + 1) * (t + ω ^ 2) * u := fun t u => by ring
  have hyk : D *ᵥ (D *ᵥ x) + (1 + ω ^ 2) • (D *ᵥ x) + ω ^ 2 • x =
      (ω ^ 2 * x k) • Pi.single k 1 := by
    ext a
    simp only [hDdef, Pi.add_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul]
    rw [key]
    by_cases hak : a = k
    · subst hak
      rw [Pi.single_eq_same, mul_one, hdk]
      have h1 : ω + ω ^ 2 = 1 := by rw [omega_sq, ← add_assoc, add_self_K, zero_add]
      rw [h1, mul_one, ← omega_sq]
    · rw [Pi.single_eq_of_ne hak, mul_zero]
      by_cases hal : (a : Fin n) = l
      · rw [hal, hdl, add_self_K, mul_zero, zero_mul]
      · rw [hdo a (fun h => hak (Subtype.ext h)) hal, add_self_K, zero_mul, zero_mul]
  have hek : (Pi.single k 1 : ({i, j}ᶜ : Finset (Fin n)) → K) ∈ S := by
    have hc0 : ω ^ 2 * x k ≠ 0 := mul_ne_zero (pow_ne_zero 2 omega_ne_zero) hk
    have := S.smul_mem (ω ^ 2 * x k)⁻¹ (hyk ▸ hy)
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hall : ∀ l' : ({i, j}ᶜ : Finset (Fin n)), (Pi.single l' 1 : _ → K) ∈ S := by
    intro l'
    by_cases hl' : l' = k
    · rw [hl']
      exact hek
    · have hk' : (k : Fin n) ≠ l' := fun h => hl' (Subtype.ext h).symm
      have hcardk : 1 < (({i, j}ᶜ : Finset (Fin n)).erase k).card := by
        rw [Finset.card_erase_of_mem k.2]
        omega
      obtain ⟨p, hp, hpl⟩ := Finset.exists_mem_ne hcardk (l' : Fin n)
      have hpk : p ≠ k := Finset.ne_of_mem_erase hp
      have hpJ : p ∈ ({i, j}ᶜ : Finset (Fin n)) := Finset.mem_of_mem_erase hp
      have hkp : (k : Fin n) ≠ p := fun h => hpk h.symm
      have hlp : (l' : Fin n) ≠ p := fun h => hpl h.symm
      set c : Equiv.Perm (Fin n) := Equiv.swap (k : Fin n) l' * Equiv.swap (k : Fin n) p
      obtain ⟨hci, hcj⟩ := swap_mul_swap_fix k.2 l'.2 hpJ
      have hcl : c l' = k := by
        simp only [c, Equiv.Perm.mul_apply]
        rw [Equiv.swap_apply_of_ne_of_ne hk'.symm hlp, Equiv.swap_apply_right]
      have hmem := hC k k.2 l' l'.2 p hpJ hk' hkp hlp _ hek
      convert hmem using 1
      ext a
      rw [tvBlock_permMatrix_mulVec hci hcj, Pi.single_apply, Pi.single_apply]
      have hiff : (⟨c a, perm_mem_compl hci hcj a.2⟩ : ({i, j}ᶜ : Finset (Fin n))) = k ↔
          a = l' := by
        constructor
        · intro h
          apply Subtype.ext
          apply c.injective
          rw [hcl]
          exact congrArg Subtype.val h
        · intro h
          subst h
          exact Subtype.ext hcl
      by_cases hal : a = l'
      · rw [if_pos hal, if_pos (hiff.2 hal)]
      · rw [if_neg hal, if_neg (fun h => hal (hiff.1 h))]
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ a, y a • (Pi.single a 1 : ({i, j}ᶜ : Finset (Fin n)) → K) := by
    ext b
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact S.sum_mem fun a _ => S.smul_mem _ (hall a)

end Irred

section TwoSub

variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

theorem permSU_mem_unitaryBlock {c : Equiv.Perm (Fin n)} (hci : c i = i) (hcj : c j = j) :
    permSU hK c ∈ unitaryBlock hK ({i, j}ᶜ : Finset (Fin n)) := by
  intro r c' hrc
  change (c.permMatrix K) r c' = (1 : Matrix (Fin n) (Fin n) K) r c'
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, one_apply]
  have hfix : ∀ a, a ∉ ({i, j}ᶜ : Finset (Fin n)) → c a = a := fun a ha => by
    rcases eq_or_eq_or_mem_compl i j a with h | h | h
    · rw [h, hci]
    · rw [h, hcj]
    · exact absurd h ha
  rcases hrc with hr | hc
  · rw [hfix r hr]
  · by_cases h : c r = c'
    · have : r = c' := by
        have := hfix c' hc
        rw [← this] at h
        exact c.injective h
      rw [if_pos h, if_pos this]
    · have : r ≠ c' := fun e => h (by rw [e, hfix c' hc])
      rw [if_neg h, if_neg this]

theorem le_tvRadical_of_isPGroup (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    {P : Subgroup (unitarySU 2 1 K n)} (hPC : P ≤ Subgroup.centralizer {tvTransSU hK hij})
    (hP2 : IsPGroup 2 P)
    (hD : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ hkl : k ≠ l,
      dSU hkl ∈ Subgroup.normalizer (P : Set (unitarySU 2 1 K n)))
    (hC : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)),
      ∀ p ∈ ({i, j}ᶜ : Finset (Fin n)), k ≠ l → k ≠ p → l ≠ p →
      permSU hK (Equiv.swap k l * Equiv.swap k p) ∈
        Subgroup.normalizer (P : Set (unitarySU 2 1 K n))) :
    P ≤ tvRadical hK hij := by
  classical
  set C₀ := Subgroup.centralizer {tvTransSU hK hij} with hC₀
  set blk : unitarySU 2 1 K n → Matrix ({i, j}ᶜ : Finset (Fin n)) ({i, j}ᶜ : Finset (Fin n)) K :=
    fun g => tvBlock i j (((g : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hblk
  set ρ : ↥P →* GL ({i, j}ᶜ : Finset (Fin n)) K := (blockHom hij).comp (Subgroup.inclusion hPC)
  have hρ : ∀ g : ↥P, ((ρ g : GL ({i, j}ᶜ : Finset (Fin n)) K) :
      Matrix ({i, j}ᶜ : Finset (Fin n)) ({i, j}ᶜ : Finset (Fin n)) K) = blk g := fun g => rfl
  let S : Submodule K (({i, j}ᶜ : Finset (Fin n)) → K) :=
    { carrier := {x | ∀ g ∈ P, blk g *ᵥ x = x}
      add_mem' := fun {x y} hx hy g hg => by rw [Matrix.mulVec_add, hx g hg, hy g hg]
      zero_mem' := fun g _ => Matrix.mulVec_zero _
      smul_mem' := fun c x hx g hg => by rw [Matrix.mulVec_smul, hx g hg] }
  have hG2 : IsPGroup 2 ρ.range := hP2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hcard : 2 ∣ Nat.card (({i, j}ᶜ : Finset (Fin n)) → K) := by
    rw [Nat.card_fun, card_K]
    have hpos : 0 < Nat.card ({i, j}ᶜ : Finset (Fin n)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      omega
    exact Dvd.dvd.pow (by norm_num) hpos.ne'
  obtain ⟨b, hb, hb0⟩ := hG2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (({i, j}ᶜ : Finset (Fin n)) → K) hcard (a := 0) (fun g => by
      change (((g : GL ({i, j}ᶜ : Finset (Fin n)) K) :
        Matrix ({i, j}ᶜ : Finset (Fin n)) ({i, j}ᶜ : Finset (Fin n)) K)) *ᵥ 0 = 0
      exact Matrix.mulVec_zero _)
  have hbS : b ∈ S := fun g hg => by
    have := hb ⟨ρ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩
    change ((ρ ⟨g, hg⟩ : GL ({i, j}ᶜ : Finset (Fin n)) K) :
      Matrix ({i, j}ᶜ : Finset (Fin n)) ({i, j}ᶜ : Finset (Fin n)) K) *ᵥ b = b at this
    rwa [hρ] at this
  have hSne : S ≠ ⊥ := by
    intro hbot
    have := hbS
    rw [hbot, Submodule.mem_bot] at this
    exact hb0 this.symm
  have hinv : ∀ t ∈ C₀, t ∈ Subgroup.normalizer (P : Set (unitarySU 2 1 K n)) →
      ∀ x ∈ S, blk t *ᵥ x ∈ S := by
    intro t htC htN x hx g hg
    have hg' : t⁻¹ * g * t ∈ P := by
      have htN' := Subgroup.inv_mem _ htN
      have := (Subgroup.mem_normalizer_iff.1 htN' g).1 hg
      simpa [mul_assoc] using this
    have hgC : g ∈ C₀ := hPC hg
    have e1 : g * t = t * (t⁻¹ * g * t) := by group
    rw [Matrix.mulVec_mulVec]
    change (tvBlock i j (((g : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        tvBlock i j (((t : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ x =
      tvBlock i j (((t : unitarySU 2 1 K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x
    rw [← tvBlock_mul_of_mem_centralizer hK hij hgC htC, e1,
      tvBlock_mul_of_mem_centralizer hK hij htC (hPC hg'), ← Matrix.mulVec_mulVec]
    congr 1
    exact hx _ hg'
  have hStop : S = ⊤ := by
    refine eq_top_of_torus_threeCycle_invariant hJ S hSne ?_ ?_
    · intro k hk l hl hkl x hx
      have htC : dSU hkl ∈ C₀ :=
        unitaryBlock_le_centralizer_tvTransSU hK hij (dSU_mem_unitaryBlock hkl hk hl)
      have := hinv _ htC (hD k hk l hl hkl) x hx
      simp only [hblk, coe_dSU, tvBlock_diagonal] at this
      exact this
    · intro k hk l hl p hp hkl hkp hlp x hx
      obtain ⟨hci, hcj⟩ := swap_mul_swap_fix hk hl hp
      have htC : permSU hK (Equiv.swap k l * Equiv.swap k p) ∈ C₀ :=
        unitaryBlock_le_centralizer_tvTransSU hK hij (permSU_mem_unitaryBlock hci hcj)
      have := hinv _ htC (hC k hk l hl p hp hkl hkp hlp) x hx
      simp only [hblk, coe_permSU] at this
      exact this
  intro g hg
  have hblock : tvBlock i j (((g : unitarySU 2 1 K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    have hall : ∀ x, blk g *ᵥ x = x := fun x => by
      have hx : x ∈ S := by rw [hStop]; trivial
      exact hx g hg
    ext a b
    have := congrFun (hall (Pi.single b 1)) a
    rw [mulVec_single_one, Matrix.col_apply] at this
    change blk g a b = _
    rw [this, one_apply, Pi.single_apply]
  obtain ⟨k, hk⟩ := hP2 ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨h1, h2⟩ := fix_tvVec_of_pow_two_pow_eq_one hij (hPC hg) hk'
  exact (mem_tvRadical hK).2 ⟨h1, h2, hblock⟩

end TwoSub

end CFSG.RankThree.GF2n.Stroth78.Sec4PSU
