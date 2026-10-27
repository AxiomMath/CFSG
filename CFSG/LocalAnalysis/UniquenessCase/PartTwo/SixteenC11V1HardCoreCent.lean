module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

private instance s16c11_v1_coreMod_commGroup (n : ℕ) : CommGroup ↥(G6.coreMod n) :=
  { (inferInstance : Group ↥(G6.coreMod n)) with
    mul_comm := fun a b => Subtype.ext (mul_comm (a : G6.PermMod n) (b : G6.PermMod n)) }

private theorem s16c11_v1_permAct_allOnes (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    G6.permAct n σ (G6.allOnes n) = G6.allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  rfl

private theorem s16c11_v1_permAct_of_mem_zpowers_allOnes {n : ℕ} {x : G6.PermMod n}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) (σ : Equiv.Perm (Fin n)) :
    G6.permAct n σ x = x := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, s16c11_v1_permAct_allOnes]
  rfl

private theorem s16c11_v1_coreAct_of_mem_natKer {n : ℕ} {k : ↥(G6.coreMod n)}
    (hk : k ∈ G6.natKer n) (σ : Equiv.Perm (Fin n)) : G6.coreAct n σ k = k := by
  apply Subtype.ext
  rw [G6.coreAct_coe]
  exact s16c11_v1_permAct_of_mem_zpowers_allOnes (Subgroup.mem_comap.mp hk) σ

private theorem s16c11_v1_toAdd_coreHeart_coreAct (n : ℕ) (σ : Equiv.Perm (Fin n))
    (m : ↥(G6.coreMod n)) :
    Multiplicative.toAdd (coreHeart n (G6.coreAct n σ m)) =
      altAct σ (Multiplicative.toAdd (coreHeart n m)) :=
  toAdd_coreHeart_permAct σ m

theorem s16c11_v1_coreA_fixed {n : ℕ} (hn : 3 ≤ n) {m : ↥(G6.coreMod n)}
    (h : ∀ a ∈ alternatingGroup (Fin n), G6.coreAct n a m = m) : m ∈ G6.natKer n := by
  have hconst : ∀ i j : Fin n, Multiplicative.toAdd (m : G6.PermMod n) i =
      Multiplicative.toAdd (m : G6.PermMod n) j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      have hcard : ({i, j} : Finset (Fin n)).card < Fintype.card (Fin n) := by
        have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        simp only [Fintype.card_fin]
        omega
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩
    set σ : Equiv.Perm (Fin n) := Equiv.swap i j * Equiv.swap j k with hσdef
    have hσA : σ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, hσdef, map_mul, Equiv.Perm.sign_swap hij,
        Equiv.Perm.sign_swap hkj.symm]
      decide
    have hσi : σ i = j := by
      simp only [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hki.symm,
        Equiv.swap_apply_left]
    have h1 : Multiplicative.toAdd (m : G6.PermMod n) (σ⁻¹ j) =
        Multiplicative.toAdd (m : G6.PermMod n) j := by
      have := congrArg (fun x : ↥(G6.coreMod n) =>
        Multiplicative.toAdd (x : G6.PermMod n) j) (h σ hσA)
      simpa only [G6.coreAct_coe, G6.permAct_apply] using this
    have h2 : σ⁻¹ j = i := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hσi.symm
    rw [h2] at h1
    exact h1
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, ∀ i, Multiplicative.toAdd (m : G6.PermMod n) i = c :=
    ⟨_, fun i => hconst i i0⟩
  rcases zmod_two_cases c with hc0 | hc1
  · change (m : G6.PermMod n) ∈ Subgroup.zpowers (G6.allOnes n)
    have hm1 : (m : G6.PermMod n) = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp [hc i, hc0]
    rw [hm1]
    exact Subgroup.one_mem _
  · change (m : G6.PermMod n) ∈ Subgroup.zpowers (G6.allOnes n)
    have hmA : (m : G6.PermMod n) = G6.allOnes n := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [hc i, hc1]
      rfl
    rw [hmA]
    exact Subgroup.mem_zpowers _

private noncomputable def s16c11_v1_pairCM (n : ℕ) (i j : Fin n) : ↥(G6.coreMod n) :=
  (C124.coreEvenEquiv n).symm (Multiplicative.ofAdd (pairEW i j))

private theorem s16c11_v1_pairCM_coord (n : ℕ) (i j p : Fin n) :
    Multiplicative.toAdd ((s16c11_v1_pairCM n i j : ↥(G6.coreMod n)) : G6.PermMod n) p =
      (if p = i then 1 else 0) + (if p = j then 1 else 0) := by
  have h := C124.coreEvenEquiv_coord (n := n) (s16c11_v1_pairCM n i j) p
  rw [s16c11_v1_pairCM] at h ⊢
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  rw [← h, pairEW_apply]

private theorem s16c11_v1_toAdd_coreEvenEquiv_coreAct (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ↥(G6.coreMod n)) :
    Multiplicative.toAdd (C124.coreEvenEquiv n (G6.coreAct n σ x)) =
      evenWeightPerm σ (Multiplicative.toAdd (C124.coreEvenEquiv n x)) := by
  apply Subtype.ext
  funext i
  rw [C124.coreEvenEquiv_coord, G6.coreAct_coe, G6.permAct_apply, evenWeightPerm_apply,
    C124.coreEvenEquiv_coord]

private theorem s16c11_v1_coreAct_pairCM (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    G6.coreAct n σ (s16c11_v1_pairCM n i j) = s16c11_v1_pairCM n (σ i) (σ j) := by
  apply (C124.coreEvenEquiv n).injective
  apply Multiplicative.toAdd.injective
  rw [s16c11_v1_toAdd_coreEvenEquiv_coreAct]
  simp only [s16c11_v1_pairCM, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    evenWeightPerm_pairEW]

private theorem s16c11_v1_pairEW_add (n : ℕ) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    pairEW i j + pairEW j k = (pairEW i k : CFSG.QuasithinUnique.evenWeight n) := by
  apply Subtype.ext
  funext p
  show ((pairEW i j : CFSG.QuasithinUnique.evenWeight n) : Fin n → ZMod 2) p +
      ((pairEW j k : CFSG.QuasithinUnique.evenWeight n) : Fin n → ZMod 2) p =
      ((pairEW i k : CFSG.QuasithinUnique.evenWeight n) : Fin n → ZMod 2) p
  rw [pairEW_apply, pairEW_apply, pairEW_apply]
  split_ifs <;> decide

private theorem s16c11_v1_pairEW_add_self (n : ℕ) (i j : Fin n) :
    pairEW i j + pairEW i j = (0 : CFSG.QuasithinUnique.evenWeight n) := by
  apply Subtype.ext
  funext p
  show ((pairEW i j : CFSG.QuasithinUnique.evenWeight n) : Fin n → ZMod 2) p +
      ((pairEW i j : CFSG.QuasithinUnique.evenWeight n) : Fin n → ZMod 2) p = 0
  exact CharTwo.add_self_eq_zero _

private theorem s16c11_v1_pairCM_mul (n : ℕ) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    s16c11_v1_pairCM n i j * s16c11_v1_pairCM n j k = s16c11_v1_pairCM n i k := by
  apply (C124.coreEvenEquiv n).injective
  rw [map_mul]
  simp only [s16c11_v1_pairCM, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd]
  exact s16c11_v1_pairEW_add n hij hjk hik

private theorem s16c11_v1_pairCM_mul_self (n : ℕ) (i j : Fin n) :
    s16c11_v1_pairCM n i j * s16c11_v1_pairCM n i j = 1 := by
  apply (C124.coreEvenEquiv n).injective
  rw [map_mul, map_one]
  simp only [s16c11_v1_pairCM, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_one]
  exact s16c11_v1_pairEW_add_self n i j

private theorem s16c11_v1_eq_top_of_pairCM_mem {n : ℕ}
    {M : Subgroup ↥(G6.coreMod n)}
    (h : ∀ i j : Fin n, i ≠ j → s16c11_v1_pairCM n i j ∈ M) : M = ⊤ := by
  suffices key : ∀ k, ∀ m : ↥(G6.coreMod n),
      (Finset.univ.filter fun p => Multiplicative.toAdd (m : G6.PermMod n) p = 1).card = k →
      m ∈ M from eq_top_iff.mpr fun m _ => key _ m rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hmk
    by_cases hm1 : m = 1
    · rw [hm1]
      exact M.one_mem
    obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd (m : G6.PermMod n) i = 1 := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hm1 (by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext p
        rcases zmod_two_cases (Multiplicative.toAdd (m : G6.PermMod n) p) with h | h
        · rw [h]; rfl
        · exact absurd h (hcon p))
    have hsum : ∑ p, Multiplicative.toAdd (m : G6.PermMod n) p = 0 :=
      G6.mem_coreMod.mp m.2
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ Multiplicative.toAdd (m : G6.PermMod n) j = 1 := by
      by_contra hcon
      rw [not_exists] at hcon
      have hs : ∑ p, Multiplicative.toAdd (m : G6.PermMod n) p =
          Multiplicative.toAdd (m : G6.PermMod n) i :=
        Finset.sum_eq_single i (fun p _ hp => by
          rcases zmod_two_cases (Multiplicative.toAdd (m : G6.PermMod n) p) with h | h
          · exact h
          · exact absurd ⟨hp, h⟩ (hcon p)) (by simp)
      rw [hs, hi] at hsum
      exact absurd hsum (by decide)
    set m' := m * s16c11_v1_pairCM n i j with hm'def
    have hm_eq : m = m' * s16c11_v1_pairCM n i j := by
      rw [hm'def, mul_assoc, s16c11_v1_pairCM_mul_self, mul_one]
    have hcoord : ∀ p, Multiplicative.toAdd (m' : G6.PermMod n) p =
        Multiplicative.toAdd (m : G6.PermMod n) p +
          (if p = i then 1 else 0) + (if p = j then 1 else 0) := by
      intro p
      have hcoe : ((m * s16c11_v1_pairCM n i j : ↥(G6.coreMod n)) : G6.PermMod n) =
          (m : G6.PermMod n) * (s16c11_v1_pairCM n i j : G6.PermMod n) := rfl
      rw [hm'def, hcoe, toAdd_mul, Pi.add_apply, s16c11_v1_pairCM_coord]
      ac_rfl
    have hmi : Multiplicative.toAdd (m' : G6.PermMod n) i = 0 := by
      rw [hcoord i, hi, if_pos rfl, if_neg hji.symm]
      decide
    have hmj : Multiplicative.toAdd (m' : G6.PermMod n) j = 0 := by
      rw [hcoord j, hj, if_neg hji, if_pos rfl]
      decide
    have hlt : (Finset.univ.filter fun p =>
        Multiplicative.toAdd (m' : G6.PermMod n) p = 1).card < k := by
      rw [← hmk]
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        by_cases hpi : p = i
        · subst hpi
          rw [hmi] at hp
          exact absurd hp (by decide)
        · by_cases hpj : p = j
          · subst hpj
            rw [hmj] at hp
            exact absurd hp (by decide)
          · rw [hcoord p, if_neg hpi, if_neg hpj] at hp
            simpa using hp
      · intro hsub
        have hmem := hsub (show i ∈ Finset.univ.filter
            (fun p => Multiplicative.toAdd (m : G6.PermMod n) p = 1) by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rw [hmi] at hmem
        exact absurd hmem (by decide)
    rw [hm_eq]
    exact M.mul_mem (ih _ hlt m' rfl) (h i j hji.symm)

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive in
theorem s16c11_v1_coreA_invariant_hom {n : ℕ} (hn : 4 ≤ n) {M : Type} [Group M]
    (ε : ↥(G6.coreMod n) →* M)
    (h : ∀ a ∈ alternatingGroup (Fin n), ∀ m, ε (G6.coreAct n a m) = ε m) : ε = 1 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let j0 : Fin n := ⟨1, by omega⟩
  let k0 : Fin n := ⟨2, by omega⟩
  have hi0j0 : i0 ≠ j0 := by simp [i0, j0]
  have hj0k0 : j0 ≠ k0 := by simp [j0, k0]
  have hi0k0 : i0 ≠ k0 := by simp [i0, k0]
  have hpair : ∀ i j : Fin n, i ≠ j →
      ε (s16c11_v1_pairCM n i j) = ε (s16c11_v1_pairCM n i0 j0) := by
    intro i j hij
    obtain ⟨σ, hσ, hσi, hσj⟩ := exists_even_pair hn hi0j0 hij
    have h1 : ε (s16c11_v1_pairCM n i0 j0) = ε (s16c11_v1_pairCM n i j) := by
      have hσinv := h σ hσ (s16c11_v1_pairCM n i0 j0)
      rw [s16c11_v1_coreAct_pairCM n σ i0 j0, hσi, hσj] at hσinv
      exact hσinv.symm
    exact h1.symm
  have hcjk : ε (s16c11_v1_pairCM n j0 k0) = ε (s16c11_v1_pairCM n i0 j0) :=
    hpair j0 k0 hj0k0
  have hcik : ε (s16c11_v1_pairCM n i0 k0) = ε (s16c11_v1_pairCM n i0 j0) :=
    hpair i0 k0 hi0k0
  have hprod : ε (s16c11_v1_pairCM n i0 j0) * ε (s16c11_v1_pairCM n j0 k0) =
      ε (s16c11_v1_pairCM n i0 k0) := by
    rw [← map_mul, s16c11_v1_pairCM_mul n hi0j0 hj0k0 hi0k0]
  have hmul : ε (s16c11_v1_pairCM n i0 j0) * ε (s16c11_v1_pairCM n i0 j0) =
      ε (s16c11_v1_pairCM n i0 j0) := by
    calc ε (s16c11_v1_pairCM n i0 j0) * ε (s16c11_v1_pairCM n i0 j0)
        = ε (s16c11_v1_pairCM n i0 j0) * ε (s16c11_v1_pairCM n j0 k0) := by rw [hcjk]
      _ = ε (s16c11_v1_pairCM n i0 j0 * s16c11_v1_pairCM n j0 k0) := (map_mul _ _ _).symm
      _ = ε (s16c11_v1_pairCM n i0 k0) := by rw [s16c11_v1_pairCM_mul n hi0j0 hj0k0 hi0k0]
      _ = ε (s16c11_v1_pairCM n i0 j0) := hcik
  have hbase : ε (s16c11_v1_pairCM n i0 j0) = 1 := by
    have h1 : ε (s16c11_v1_pairCM n i0 j0) * ε (s16c11_v1_pairCM n i0 j0) =
        ε (s16c11_v1_pairCM n i0 j0) * 1 := by rw [mul_one, hmul]
    exact mul_left_cancel h1
  have hker : ε.ker = ⊤ := by
    refine s16c11_v1_eq_top_of_pairCM_mem (n := n) ?_
    intro i j hij
    rw [MonoidHom.mem_ker, hpair i j hij, hbase]
  refine MonoidHom.ext fun m => ?_
  have hm : m ∈ ε.ker := by rw [hker]; exact Subgroup.mem_top m
  exact MonoidHom.mem_ker.mp hm

private theorem s16c11_v1_coreHeart_ker {n : ℕ} (hn : 0 < n) :
    (coreHeart n).ker = G6.natKer n := by
  ext m
  rw [MonoidHom.mem_ker, coreHeart_eq_one_iff hn]
  change m ∈ (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) ↔
    (m : G6.PermMod n) ∈ Subgroup.zpowers (G6.allOnes n)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_left m.2

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive in
theorem s16c11_v1_coreHeart_induced {n : ℕ} (hn : 0 < n) (g : MulAut ↥(G6.coreMod n))
    (hg : (G6.natKer n).map g.toMonoidHom = G6.natKer n) :
    ∃ γ : altHeart n ≃+ altHeart n, ∀ m, Multiplicative.toAdd (coreHeart n (g m)) =
      γ (Multiplicative.toAdd (coreHeart n m)) := by
  classical
  set K : Subgroup ↥(G6.coreMod n) := G6.natKer n with hKdef
  have hKker : (coreHeart n).ker = K := by rw [hKdef]; exact s16c11_v1_coreHeart_ker hn
  have hgle : K ≤ K.comap g.toMonoidHom := by
    intro m hm
    rw [Subgroup.mem_comap, ← hg]
    exact Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
  let e : (↥(G6.coreMod n) ⧸ K) ≃* Multiplicative (altHeart n) :=
    (QuotientGroup.quotientMulEquivOfEq hKker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (coreHeart n) (coreHeart_surjective n))
  have he_mk : ∀ m, e (QuotientGroup.mk m) = coreHeart n m := by
    intro m
    rfl
  let φ : ↥(G6.coreMod n) →* Multiplicative (altHeart n) := (coreHeart n).comp g.toMonoidHom
  have hle : K ≤ φ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    change coreHeart n (g m) = 1
    have hgm : g m ∈ (coreHeart n).ker := by
      rw [hKker]
      exact Subgroup.mem_comap.mp (hgle hm)
    exact MonoidHom.mem_ker.mp hgm
  let Φ : (↥(G6.coreMod n) ⧸ K) →* Multiplicative (altHeart n) := QuotientGroup.lift K φ hle
  have hΦ_mk : ∀ m, Φ (QuotientGroup.mk m) = coreHeart n (g m) := by
    intro m
    rfl
  let ĝ : (↥(G6.coreMod n) ⧸ K) ≃* (↥(G6.coreMod n) ⧸ K) :=
    QuotientGroup.congr K K g hg
  have hĝ_mk : ∀ m, ĝ (QuotientGroup.mk m) = QuotientGroup.mk (g m) := by
    intro m
    rfl
  let γMul : Multiplicative (altHeart n) ≃* Multiplicative (altHeart n) :=
    e.symm.trans (ĝ.trans e)
  have hγMul : ∀ m, γMul (coreHeart n m) = coreHeart n (g m) := by
    intro m
    have h1 : e.symm (coreHeart n m) = QuotientGroup.mk m := by
      rw [← he_mk m, MulEquiv.symm_apply_apply]
    simp only [γMul, MulEquiv.trans_apply]
    rw [h1, hĝ_mk, he_mk (g m)]
  refine ⟨(AddEquiv.toMultiplicative).symm γMul, fun m => ?_⟩
  change Multiplicative.toAdd (coreHeart n (g m)) =
    Multiplicative.toAdd (γMul (Multiplicative.ofAdd (Multiplicative.toAdd (coreHeart n m))))
  rw [ofAdd_toAdd, hγMul m]

theorem s16c11_v1_coreAct_centralizer {n : ℕ} (hn : 5 ≤ n)
    (v : MulAut ↥(G6.coreMod n))
    (hv : ∀ σ : ↥(alternatingGroup (Fin n)), ∀ x : ↥(G6.coreMod n),
      v (G6.coreAct n (σ : Equiv.Perm (Fin n)) x) =
        G6.coreAct n (σ : Equiv.Perm (Fin n)) (v x)) : v = 1 := by
  classical
  have hvK : ∀ k ∈ G6.natKer n, v k ∈ G6.natKer n := by
    intro k hk
    refine s16c11_v1_coreA_fixed (n := n) (by omega) (m := v k) ?_
    intro σ hσ
    rw [← hv ⟨σ, hσ⟩ k, s16c11_v1_coreAct_of_mem_natKer hk σ]
  have hvinvK : ∀ k ∈ G6.natKer n, v⁻¹ k ∈ G6.natKer n := by
    intro k hk
    refine s16c11_v1_coreA_fixed (n := n) (by omega) (m := v⁻¹ k) ?_
    intro σ hσ
    apply v.injective
    show v (G6.coreAct n (σ : Equiv.Perm (Fin n)) (v⁻¹ k)) = v (v⁻¹ k)
    rw [hv ⟨σ, hσ⟩ (v⁻¹ k), MulAut.apply_inv_self ↥(G6.coreMod n) v k,
      s16c11_v1_coreAct_of_mem_natKer hk σ]
  have hKmap : (G6.natKer n).map v.toMonoidHom = G6.natKer n := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hvK k hk
    · intro k hk
      exact Subgroup.mem_map.mpr
        ⟨v⁻¹ k, hvinvK k hk, MulAut.apply_inv_self ↥(G6.coreMod n) v k⟩
  obtain ⟨γ, hγ⟩ := s16c11_v1_coreHeart_induced (n := n) (by omega) v hKmap
  have hcomm : ∀ σ ∈ alternatingGroup (Fin n), ∀ y : altHeart n,
      γ.toAddMonoidHom (altAct σ y) = altAct σ (γ.toAddMonoidHom y) := by
    intro σ hσ y
    obtain ⟨m, hm⟩ := coreHeart_surjective n (Multiplicative.ofAdd y)
    have hy : y = Multiplicative.toAdd (coreHeart n m) := by
      rw [hm, toAdd_ofAdd]
    rw [hy]
    change γ (altAct σ (Multiplicative.toAdd (coreHeart n m))) =
      altAct σ (γ (Multiplicative.toAdd (coreHeart n m)))
    rw [← s16c11_v1_toAdd_coreHeart_coreAct (n := n) σ m, ← hγ (G6.coreAct n σ m), ← hγ m,
      ← s16c11_v1_toAdd_coreHeart_coreAct (n := n) σ (v m), hv ⟨σ, hσ⟩ m]
  have hγid : γ.toAddMonoidHom = AddMonoidHom.id (altHeart n) := by
    rcases altHeart_endo_eq_zero_or_id hn γ.toAddMonoidHom hcomm with h0 | hid
    · exfalso
      haveI : Nontrivial (altHeart n) := altHeart_nontrivial (n := n) (by omega)
      obtain ⟨y, hy⟩ := exists_ne (0 : altHeart n)
      have hy0 : γ y = 0 := by
        have := congrArg (fun f : altHeart n →+ altHeart n => f y) h0
        simpa using this
      have h0y : γ (0 : altHeart n) = 0 := map_zero γ
      exact hy (γ.injective (by rw [hy0, h0y]))
    · exact hid
  have hfix : ∀ m, Multiplicative.toAdd (coreHeart n (v m)) =
      Multiplicative.toAdd (coreHeart n m) := by
    intro m
    rw [hγ m]
    have hx : γ (Multiplicative.toAdd (coreHeart n m)) =
        Multiplicative.toAdd (coreHeart n m) := by
      have := congrArg (fun f : altHeart n →+ altHeart n =>
        f (Multiplicative.toAdd (coreHeart n m))) hγid
      simpa using this
    exact hx
  have hεK : ∀ m : ↥(G6.coreMod n), v m * m⁻¹ ∈ G6.natKer n := by
    intro m
    have hcore : coreHeart n (v m * m⁻¹) = 1 := by
      have hvm : coreHeart n (v m) = coreHeart n m :=
        Multiplicative.toAdd.injective (hfix m)
      rw [map_mul, map_inv, hvm, mul_inv_cancel]
    have hker : v m * m⁻¹ ∈ (coreHeart n).ker := MonoidHom.mem_ker.mpr hcore
    rw [s16c11_v1_coreHeart_ker (by omega)] at hker
    exact hker
  let ε : ↥(G6.coreMod n) →* ↥(G6.coreMod n) :=
    { toFun := fun m => v m * m⁻¹
      map_one' := by
        show v 1 * (1 : ↥(G6.coreMod n))⁻¹ = 1
        rw [map_one, inv_one, mul_one]
      map_mul' := fun m₁ m₂ => by
        show v (m₁ * m₂) * (m₁ * m₂)⁻¹ = (v m₁ * m₁⁻¹) * (v m₂ * m₂⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hεinv : ∀ a ∈ alternatingGroup (Fin n), ∀ m,
      ε (G6.coreAct n a m) = ε m := by
    intro a ha m
    change v (G6.coreAct n a m) * (G6.coreAct n a m)⁻¹ = v m * m⁻¹
    rw [hv ⟨a, ha⟩ m, ← map_inv (G6.coreAct n a) m, ← map_mul (G6.coreAct n a)]
    exact s16c11_v1_coreAct_of_mem_natKer (hεK m) a
  have hε1 : ε = 1 := s16c11_v1_coreA_invariant_hom (n := n) (by omega) ε hεinv
  refine MulEquiv.ext fun m => ?_
  have hm : ε m = 1 := by rw [hε1]; rfl
  have hvm : v m * m⁻¹ = 1 := by simpa [ε] using hm
  exact mul_inv_eq_one.mp hvm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
