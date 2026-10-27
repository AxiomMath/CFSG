module

public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord

public section

namespace CFSG.GGQ2Prime

open Module CFSG.StandardType CFSG.StandardType.TypeAReflOver

theorem typeA_fix_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card V = p ^ (n + 1))
    (hinv : ∃ C : Fin (n + 1) → Fin (n + 1) → ZMod p,
      ∀ i k, ∑ j, cartanA (p := p) i j * C j k = if i = k then 1 else 0)
    (s : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (hrefl : ∀ i, IsLinRefl (s i))
    (hdistinct : ∀ i j, i ≠ j → s i ≠ s j)
    (hcomm : ∀ i j : Fin (n + 1), i.val + 2 ≤ j.val → s i * s j = s j * s i)
    (hbraid : ∀ i j : Fin (n + 1), i.val + 1 = j.val → s i * s j * s i = s j * s i * s j) :
    ∀ v : V, (∀ i, s i v = v) → v = 0 := by
  classical
  haveI : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp2⟩
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  choose h f hf hrepr using hrefl
  have hrepr' : ∀ i, s i = reflection (hf i) := fun i => LinearEquiv.ext fun v => by
    rw [hrepr i v, reflection_apply]
  have hne2 : ∀ i j : Fin (n + 1), i ≠ j → reflection (hf i) ≠ reflection (hf j) := by
    intro i j hij h'
    exact hdistinct i j hij (by rw [hrepr' i, hrepr' j, h'])
  have hcomm2 : ∀ i j : Fin (n + 1), i.val + 2 ≤ j.val →
      reflection (hf i) * reflection (hf j) = reflection (hf j) * reflection (hf i) := by
    intro i j hij
    rw [← hrepr' i, ← hrepr' j]
    exact hcomm i j hij
  have hbraid2 : ∀ i j : Fin (n + 1), i.val + 1 = j.val →
      reflection (hf i) * reflection (hf j) * reflection (hf i) =
        reflection (hf j) * reflection (hf i) * reflection (hf j) := by
    intro i j hij
    rw [← hrepr' i, ← hrepr' j]
    exact hbraid i j hij
  have hzero : ∀ i j : Fin (n + 1), i ≠ j →
      ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) → f j (h i) = 0 := by
    intro i j hij hfar
    have hfar2 : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by
      have hval : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
      omega
    rcases hfar2 with hcell | hcell
    · have hc := hcomm2 i j hcell
      have hind := linearIndependent_of_commute (hf i) (hf j) (hne2 i j hij) hc
      exact reflection_cross_eq_zero_of_commute (hf j) (hf i)
        (LinearIndependent.pair_symm_iff.mp hind.1)
        (NeZero.ne 2) hc.symm
    · have hc := hcomm2 j i hcell
      have hind := linearIndependent_of_commute (hf j) (hf i) (hne2 j i hij.symm) hc
      exact reflection_cross_eq_zero_of_commute (hf j) (hf i) hind.1 (NeZero.ne 2) hc
  have hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1 := by
    intro i
    have hbraid_rt := hbraid2 i.castSucc i.succ (by rw [Fin.val_castSucc, Fin.val_succ])
    by_cases hright : i.val + 2 ≤ n
    · set k : Fin (n + 1) := ⟨i.val + 2, by omega⟩ with hk
      have hkv : k.val = i.val + 2 := rfl
      have hcomm_rk : reflection (hf i.castSucc) * reflection (hf k) =
          reflection (hf k) * reflection (hf i.castSucc) := by
        refine hcomm2 i.castSucc k ?_
        rw [hkv, Fin.val_castSucc]
      have hne_rk : reflection (hf i.castSucc) ≠ reflection (hf k) := by
        refine hne2 i.castSucc k ?_
        intro hh
        have := congrArg Fin.val hh
        rw [hkv, Fin.val_castSucc] at this
        omega
      have hbraid_tk : reflection (hf i.succ) * reflection (hf k) * reflection (hf i.succ) =
          reflection (hf k) * reflection (hf i.succ) * reflection (hf k) := by
        refine hbraid2 i.succ k ?_
        rw [hkv, Fin.val_succ]
      have hind := linearIndependent_of_braid_of_commute (hf i.castSucc) (hf i.succ) (hf k)
        hbraid_rt hcomm_rk hne_rk hbraid_tk
      exact reflection_cross_mul_eq_one_of_braid (hf i.castSucc) (hf i.succ) hind.1 hbraid_rt
    · have hleft : i.val = n - 1 := by
        have := i.isLt
        omega
      set k : Fin (n + 1) := ⟨i.val - 1, by omega⟩ with hk
      have hkv : k.val = i.val - 1 := rfl
      have hcomm_rk : reflection (hf i.succ) * reflection (hf k) =
          reflection (hf k) * reflection (hf i.succ) := by
        refine (hcomm2 k i.succ ?_).symm
        rw [hkv, Fin.val_succ]
        omega
      have hne_rk : reflection (hf i.succ) ≠ reflection (hf k) := by
        refine hne2 i.succ k ?_
        intro hh
        have := congrArg Fin.val hh
        rw [hkv, Fin.val_succ] at this
        omega
      have hbraid_tk : reflection (hf i.castSucc) * reflection (hf k) *
          reflection (hf i.castSucc) =
          reflection (hf k) * reflection (hf i.castSucc) * reflection (hf k) := by
        refine (hbraid2 k i.castSucc ?_).symm
        rw [hkv, Fin.val_castSucc]
        omega
      have hind := linearIndependent_of_braid_of_commute (hf i.succ) (hf i.castSucc) (hf k)
        hbraid_rt.symm hcomm_rk hne_rk hbraid_tk
      have hprod := reflection_cross_mul_eq_one_of_braid (hf i.succ) (hf i.castSucc) hind.1
        hbraid_rt.symm
      rwa [mul_comm]
  have hc : ∀ i, reflScale (p := p) f h i ≠ 0 := reflScale_ne_zero f h hcross
  have hcol : ∀ i j : Fin (n + 1),
      cartanA (p := p) i j = scaledCoroot f h j (scaledRoot f h i) :=
    cartanA_eq_scaledCoroot f h hf hc hcross hzero
  set M : V →ₗ[ZMod p] (Fin (n + 1) → ZMod p) := evalMap f h with hM
  have hsurj : Function.Surjective M := by
    obtain ⟨C, hC⟩ := hinv
    intro w
    refine ⟨∑ j, (∑ k, C j k * w k) • scaledRoot f h j, ?_⟩
    funext i
    rw [hM, evalMap_apply, map_sum]
    simp_rw [map_smul, smul_eq_mul, ← hcol]
    have key : ∀ j, (∑ k, C j k * w k) * cartanA (p := p) j i =
        ∑ k, cartanA (p := p) i j * C j k * w k := fun j => by
      rw [Finset.sum_mul, cartanA_comm]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [key]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hC]
    simp
  have hinj : Function.Injective M := by
    have hc2 : Nat.card V ≤ Nat.card (Fin (n + 1) → ZMod p) := by
      rw [hcard, Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    exact (Function.Surjective.bijective_of_nat_card_le hsurj hc2).1
  intro v hv
  apply hinj
  rw [map_zero]
  funext i
  rw [hM, evalMap_apply, Pi.zero_apply]
  have h1 : f i v • h i = 0 := by
    have := hrepr i v
    rw [hv i] at this
    exact (sub_eq_self.mp this.symm)
  have hh : h i ≠ 0 := fun h0 => by
    have := hf i
    rw [h0, map_zero] at this
    exact (NeZero.ne (2 : ZMod p)) this.symm
  have h2 : f i v = 0 := (smul_eq_zero.mp h1).resolve_right hh
  simp [scaledCoroot, h2]

@[expose] def cartanA6InvF3 : Fin (5 + 1) → Fin (5 + 1) → ZMod 3 :=
  ![![0, 2, 1, 0, 2, 1], ![2, 1, 2, 0, 1, 2], ![1, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 1],
    ![2, 1, 0, 2, 1, 2], ![1, 2, 0, 1, 2, 0]]

theorem cartanA6_mul_inv (i k : Fin (5 + 1)) :
    ∑ j, cartanA (p := 3) (n := 5) i j * cartanA6InvF3 j k = if i = k then 1 else 0 := by
  revert i k
  decide

@[expose] noncomputable def sumZeroCoords {p : ℕ} :
    (Fin (5 + 1) → ZMod p) →ₗ[ZMod p] (Fin (5 + 1 + 1) → ZMod p) where
  toFun v j := (if h : j.val < 5 + 1 then v ⟨j.val, h⟩ else 0) - ∑ k, v k
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> abel
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    split_ifs <;> ring

theorem sumZeroCoords_castSucc {p : ℕ} (v : Fin (5 + 1) → ZMod p) (i : Fin (5 + 1)) :
    sumZeroCoords v i.castSucc = v i - ∑ k, v k := by
  change (if h : (i.castSucc : Fin (5 + 1 + 1)).val < 5 + 1 then v ⟨_, h⟩ else 0) - _ = _
  rw [dif_pos (by simp)]
  rfl

theorem sumZeroCoords_last {p : ℕ} (v : Fin (5 + 1) → ZMod p) :
    sumZeroCoords v (Fin.last (5 + 1)) = -∑ k, v k := by
  change (if h : (Fin.last (5 + 1)).val < 5 + 1 then v ⟨_, h⟩ else 0) - _ = _
  rw [dif_neg (by simp), zero_sub]

theorem six_nsmul_of_three {p : ℕ} (h3 : (3 : ZMod p) = 0) (x : ZMod p) :
    (5 + 1 : ℕ) • x = 0 := by
  rw [nsmul_eq_mul]
  have : ((5 + 1 : ℕ) : ZMod p) = 0 := by
    have e : ((5 + 1 : ℕ) : ZMod p) = 2 * 3 := by push_cast; ring
    rw [e, h3, mul_zero]
  rw [this, zero_mul]

theorem sumZeroCoords_sum {p : ℕ} (h3 : (3 : ZMod p) = 0)
    (v : Fin (5 + 1) → ZMod p) : ∑ j, sumZeroCoords v j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [sumZeroCoords_castSucc, sumZeroCoords_last, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ,
    Fintype.card_fin, six_nsmul_of_three h3]
  abel

theorem sumZeroCoords_injective {p : ℕ} :
    Function.Injective (sumZeroCoords (p := p)) := by
  intro v w hvw
  have hS : ∑ k, v k = ∑ k, w k := by
    have := congrFun hvw (Fin.last (5 + 1))
    rw [sumZeroCoords_last, sumZeroCoords_last] at this
    exact neg_injective this
  funext i
  have := congrFun hvw i.castSucc
  rw [sumZeroCoords_castSucc, sumZeroCoords_castSucc, hS, sub_left_inj] at this
  exact this

theorem sumZeroCoords_coordPerm {p : ℕ} (i : Fin 5) (v : Fin (5 + 1) → ZMod p) :
    sumZeroCoords (coordPerm p 5 (Equiv.swap i.castSucc i.succ) v) =
      fun j => sumZeroCoords v (Equiv.swap i.castSucc.castSucc i.succ.castSucc j) := by
  have hS : ∑ k, coordPerm p 5 (Equiv.swap i.castSucc i.succ) v k = ∑ k, v k := by
    simp only [coordPerm_apply, Equiv.symm_swap]
    exact Equiv.sum_comp (Equiv.swap i.castSucc i.succ) v
  funext j
  induction j using Fin.lastCases with
  | last =>
      have h1 : Equiv.swap i.castSucc.castSucc i.succ.castSucc (Fin.last (5 + 1)) =
          Fin.last (5 + 1) := by
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · exact (Fin.castSucc_lt_last _).ne'
        · exact (Fin.castSucc_lt_last _).ne'
      rw [h1, sumZeroCoords_last, sumZeroCoords_last, hS]
  | cast k =>
      have h1 : Equiv.swap i.castSucc.castSucc i.succ.castSucc k.castSucc =
          (Equiv.swap i.castSucc i.succ k).castSucc := by
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        simp only [Fin.castSucc_inj]
        split_ifs <;> rfl
      rw [h1, sumZeroCoords_castSucc, sumZeroCoords_castSucc, hS, coordPerm_apply, Equiv.symm_swap]

theorem sumZeroCoords_kRefl {p : ℕ} (h3 : (3 : ZMod p) = 0)
    (v : Fin (5 + 1) → ZMod p) :
    sumZeroCoords (kRefl p 5 v) =
      fun j => sumZeroCoords v (Equiv.swap (Fin.last 5).castSucc (Fin.last (5 + 1)) j) := by
  set e : Fin (5 + 1) → ZMod p := Pi.single (Fin.last 5) 1 with he
  have hk : ∀ k, kRefl p 5 v k = v k - v (Fin.last 5) * (e k + 1) := by
    intro k
    rw [kRefl_apply, he]
    simp only [kRoot, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
  have hsum_e : ∑ k, e k = 1 := by
    rw [he, Finset.sum_pi_single']
    simp
  have hS : ∑ k, kRefl p 5 v k = ∑ k, v k - v (Fin.last 5) := by
    simp only [hk, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hsum_e,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, six_nsmul_of_three h3, add_zero,
      mul_one]
  have he5 : e (Fin.last 5) = 1 := by rw [he, Pi.single_eq_same]
  have hel : ∀ l : Fin 5, e l.castSucc = 0 := fun l => by
    rw [he]
    exact Pi.single_eq_of_ne (Fin.castSucc_lt_last l).ne 1
  funext j
  induction j using Fin.lastCases with
  | last =>
      rw [Equiv.swap_apply_right, sumZeroCoords_last, hS, sumZeroCoords_castSucc]
      ring
  | cast k =>
      induction k using Fin.lastCases with
      | last =>
          rw [Equiv.swap_apply_left, sumZeroCoords_last, sumZeroCoords_castSucc, hS, hk, he5]
          ring
      | cast l =>
          have h1 : Equiv.swap (Fin.last 5).castSucc (Fin.last (5 + 1)) l.castSucc.castSucc =
              l.castSucc.castSucc := by
            refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
            · intro h
              exact (Fin.castSucc_lt_last l).ne (Fin.castSucc_injective _ h)
            · exact (Fin.castSucc_lt_last _).ne
          rw [h1, sumZeroCoords_castSucc, sumZeroCoords_castSucc, hS, hk, hel]
          ring

theorem sumZeroCoords_const {p : ℕ} (h3 : (3 : ZMod p) = 0) (a : ZMod p) :
    sumZeroCoords (fun _ => a) = fun j => if j = Fin.last (5 + 1) then 0 else a := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      rw [sumZeroCoords_last, if_pos rfl]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, six_nsmul_of_three h3,
        neg_zero]
  | cast k =>
      rw [sumZeroCoords_castSucc, if_neg (Fin.castSucc_lt_last k).ne]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, six_nsmul_of_three h3,
        sub_zero]

end CFSG.GGQ2Prime
