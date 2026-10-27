module

public import CFSG.Quasithin.SteinbergBNA7DeletedModule
public import CFSG.Quasithin.SteinbergBNA7TreePath
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.Quasithin.SteinbergBN

@[expose] def pathMat (n : ℕ) (i j : Fin n) : ZMod 2 :=
  if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

@[expose] def altVec (n : ℕ) : Fin n → ZMod 2 := fun i => if (i : ℕ) % 2 = 0 then 1 else 0

section Pairing

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem pair_lc (B : LinearMap.BilinForm (ZMod 2) M) {n : ℕ} (b : Fin n → M)
    (z z' : Fin n → ZMod 2) :
    B (Fintype.linearCombination (ZMod 2) b z) (Fintype.linearCombination (ZMod 2) b z') =
      ∑ i, ∑ j, z i * z' j * B (b i) (b j) := by
  simp only [Fintype.linearCombination_apply, LinearMap.BilinForm.sum_left,
    LinearMap.BilinForm.sum_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pair_lc_single (B : LinearMap.BilinForm (ZMod 2) M) {n : ℕ} (b : Fin n → M)
    (z : Fin n → ZMod 2) (j : Fin n) :
    B (Fintype.linearCombination (ZMod 2) b z) (b j) = ∑ i, z i * B (b i) (b j) := by
  simp only [Fintype.linearCombination_apply, LinearMap.BilinForm.sum_left,
    LinearMap.BilinForm.smul_left]

theorem pair_eq_pathMat {B : LinearMap.BilinForm (ZMod 2) M} (hB : B.IsAlt) {n : ℕ}
    {b : Fin n → M} (hb : pairGraph hB b = SimpleGraph.pathGraph n) (i j : Fin n) :
    B (b i) (b j) = pathMat n i j := by
  apply zmod_two_eq_of_iff
  rw [← pairGraph_adj hB, hb, SimpleGraph.pathGraph_adj, pathMat]
  split_ifs with h
  · exact iff_of_true h rfl
  · exact iff_of_false h (by decide)

theorem lc_eq_zero_iff {B : LinearMap.BilinForm (ZMod 2) M} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} {b : Fin n → M}
    (hspan : Submodule.span (ZMod 2) (Set.range b) = ⊤)
    (hb : pairGraph hB b = SimpleGraph.pathGraph n) (z : Fin n → ZMod 2) :
    Fintype.linearCombination (ZMod 2) b z = 0 ↔ ∀ j, ∑ i, z i * pathMat n i j = 0 := by
  constructor
  · intro h j
    have := pair_lc_single B b z j
    rw [h, map_zero, LinearMap.zero_apply] at this
    simp only [pair_eq_pathMat hB hb] at this
    exact this.symm
  · intro h
    refine eq_of_pairing_eq hnd hspan fun j => ?_
    rw [pair_lc_single, map_zero, LinearMap.zero_apply]
    simp only [pair_eq_pathMat hB hb]
    exact h j

end Pairing

section Relations

variable {n : ℕ}

theorem sum_mul_single_castSucc (z : Fin n → ZMod 2) (k : Fin (n + 1)) :
    ∑ i : Fin n, z i * (Pi.single i.castSucc (1 : ZMod 2) : Fin (n + 1) → ZMod 2) k =
      if h : (k : ℕ) < n then z ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · have hk : (⟨k, h⟩ : Fin n).castSucc = k := Fin.ext rfl
      rw [hk, Pi.single_eq_same, mul_one]
    · intro i _ hi
      have : i.castSucc ≠ k := fun e => hi (Fin.ext (by
        have := congrArg Fin.val e
        simpa using this))
      rw [Pi.single_eq_of_ne' this, mul_zero]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : i.castSucc ≠ k := fun e => h (by rw [← e]; exact i.castSucc_lt_last)
    rw [Pi.single_eq_of_ne' this, mul_zero]

theorem sum_mul_single_succ (z : Fin n → ZMod 2) (k : Fin (n + 1)) :
    ∑ i : Fin n, z i * (Pi.single i.succ (1 : ZMod 2) : Fin (n + 1) → ZMod 2) k =
      if h : 1 ≤ (k : ℕ) then z ⟨k - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · have hk : (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ = k := Fin.ext (by simp; omega)
      rw [hk, Pi.single_eq_same, mul_one]
    · intro i _ hi
      have : i.succ ≠ k := fun e => hi (Fin.ext (by
        have := congrArg Fin.val e
        simp at this ⊢
        omega))
      rw [Pi.single_eq_of_ne' this, mul_zero]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : i.succ ≠ k := fun e => h (by rw [← e]; simp)
    rw [Pi.single_eq_of_ne' this, mul_zero]

theorem sum_pathVec_apply (z : Fin n → ZMod 2) (k : Fin (n + 1)) :
    (∑ i, z i • pathVec i) k = (if h : (k : ℕ) < n then z ⟨k, h⟩ else 0) +
      (if h : 1 ≤ (k : ℕ) then z ⟨k - 1, by omega⟩ else 0) := by
  rw [Finset.sum_apply]
  simp only [pathVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    sum_mul_single_castSucc, sum_mul_single_succ]

theorem lc_pathW (z : Fin n → ZMod 2) :
    Fintype.linearCombination (ZMod 2) (pathW (n := n)) z =
      Submodule.Quotient.mk (∑ i, z i • pathDelta i) := by
  rw [Fintype.linearCombination_apply]
  have e : ∀ i, z i • pathW i = (radSub (n + 1)).mkQ (z i • pathDelta i) := fun i => rfl
  simp only [e, ← map_sum]
  rfl

theorem lc_pathW_eq_zero_iff (hn : 1 ≤ n) (z : Fin n → ZMod 2) :
    Fintype.linearCombination (ZMod 2) (pathW (n := n)) z = 0 ↔
      z = 0 ∨ (n % 2 = 1 ∧ z = altVec n) := by
  rw [lc_pathW, Submodule.Quotient.mk_eq_zero, mem_radSub, Submodule.coe_sum]
  simp only [Submodule.coe_smul, pathDelta]
  rw [mem_span_onesV_iff]
  constructor
  · rintro (h | h)
    · left
      funext j
      rw [← prefixL_sum_pathVec z j, h, map_zero, Pi.zero_apply]
    · right
      have hz : ∀ k : ℕ, (hk : k < n) → z ⟨k, hk⟩ = altVec n ⟨k, hk⟩ := by
        intro k
        induction k with
        | zero =>
          intro hk
          have h0 := congrFun h 0
          rw [sum_pathVec_apply] at h0
          simp [hk, onesV] at h0
          simp [altVec, h0]
        | succ k ih =>
          intro hk
          have h1 := congrFun h ⟨k + 1, by omega⟩
          rw [sum_pathVec_apply] at h1
          simp only [hk, show 1 ≤ k + 1 by omega, dite_true, onesV, Nat.add_sub_cancel] at h1
          rw [ih (by omega)] at h1
          simp only [altVec] at h1 ⊢
          split_ifs at h1 ⊢ <;> first | omega | simpa using h1
      have hzalt : z = altVec n := funext fun j => hz j j.2
      refine ⟨?_, hzalt⟩
      have hl := congrFun h (Fin.last n)
      rw [sum_pathVec_apply] at hl
      simp only [Fin.val_last, lt_irrefl, dite_false, zero_add, hn, dite_true, onesV] at hl
      rw [hzalt, altVec] at hl
      simp only at hl
      split_ifs at hl with h2
      · omega
      · exact absurd hl (by decide)
  · rintro (rfl | ⟨hodd, rfl⟩)
    · left
      simp
    · right
      funext k
      rw [sum_pathVec_apply]
      have hk := k.2
      simp only [onesV, altVec]
      split_ifs <;> first | omega | decide

end Relations

section Main

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem congrLinearEquiv_transv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {B : LinearMap.BilinForm (ZMod 2) W} (hβ : β.IsAlt) (hB : B.IsAlt) (ψ : V ≃ₗ[ZMod 2] W)
    (hψ : ∀ x y, B (ψ x) (ψ y) = β x y) (u : V) :
    LinearMap.GeneralLinearGroup.congrLinearEquiv ψ (transv hβ u) = transv hB (ψ u) := by
  refine Units.ext (LinearMap.ext fun w => ?_)
  rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  change ψ ((transv hβ u : V →ₗ[ZMod 2] V) (ψ.symm w)) = (transv hB (ψ u) : W →ₗ[ZMod 2] W) w
  rw [transv_apply, transv_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
  congr 2
  rw [← hψ, LinearEquiv.apply_symm_apply]

theorem path_module_core (hβ : β.IsAlt) (hnd : β.Nondegenerate) {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → V) (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤)
    (hpath : pairGraph hβ a = SimpleGraph.pathGraph n) :
    ∃ ψ : V ≃ₗ[ZMod 2] deletedW (n + 1), (∀ x y, wForm (n + 1) (ψ x) (ψ y) = β x y) ∧
      (∀ i, ψ (a i) = pathW i) ∧
      ∀ z, Fintype.linearCombination (ZMod 2) a z = 0 ↔ z = 0 ∨ (n % 2 = 1 ∧ z = altVec n) := by
  let L := Fintype.linearCombination (ZMod 2) a
  let M := Fintype.linearCombination (ZMod 2) (pathW (n := n))
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  have hM : Function.Surjective M := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_pathW]
  have hker : LinearMap.ker L = LinearMap.ker M := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.mem_ker, lc_eq_zero_iff hβ hnd hspan hpath,
      lc_eq_zero_iff (wForm_isAlt _) (wForm_nondegenerate _) span_pathW pairGraph_pathW]
  let ψ : V ≃ₗ[ZMod 2] deletedW (n + 1) :=
    (L.quotKerEquivOfSurjective hL).symm ≪≫ₗ (Submodule.quotEquivOfEq _ _ hker) ≪≫ₗ
      (M.quotKerEquivOfSurjective hM)
  have hψL : ∀ z, ψ (L z) = M z := by
    intro z
    have h1 : (L.quotKerEquivOfSurjective hL).symm (L z) = Submodule.Quotient.mk z :=
      (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [ψ, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨ψ, fun x y => ?_, fun i => ?_, fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hL x
    obtain ⟨z', rfl⟩ := hL y
    rw [hψL, hψL, pair_lc, pair_lc]
    simp only [pair_eq_pathMat (wForm_isAlt _) pairGraph_pathW, pair_eq_pathMat hβ hpath]
  · have h1 : a i = L (Pi.single i 1) := by
      rw [Fintype.linearCombination_apply_single, one_smul]
    have h2 : pathW i = M (Pi.single i 1) := by
      rw [Fintype.linearCombination_apply_single, one_smul]
    rw [h1, hψL, ← h2]
  · have h1 : L z = 0 ↔ M z = 0 := by
      rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, hker]
    rw [h1]
    exact lc_pathW_eq_zero_iff (by omega) z

theorem finrank_of_path [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n → V) (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤)
    (hpath : pairGraph hβ a = SimpleGraph.pathGraph n) :
    Module.finrank (ZMod 2) V = if n % 2 = 0 then n else n - 1 := by
  obtain ⟨-, -, -, hrel⟩ := path_module_core hβ hnd hn a hspan hpath
  let L := Fintype.linearCombination (ZMod 2) a
  have hL : LinearMap.range L = ⊤ := by
    rw [Fintype.range_linearCombination, hspan]
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [hL, finrank_top, Module.finrank_fin_fun] at h
  split_ifs with hpar
  · have hk : LinearMap.ker L = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [LinearMap.mem_ker] at hz
      rcases (hrel z).1 hz with h' | h'
      · exact h'
      · omega
    rw [hk, finrank_bot] at h
    omega
  · have halt : altVec n ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, by omega⟩
      simp [altVec] at this
    have hk : LinearMap.ker L = Submodule.span (ZMod 2) {altVec n} := by
      ext z
      rw [LinearMap.mem_ker, hrel, Submodule.mem_span_singleton]
      constructor
      · rintro (rfl | ⟨-, rfl⟩)
        · exact ⟨0, zero_smul _ _⟩
        · exact ⟨1, one_smul _ _⟩
      · rintro ⟨c, rfl⟩
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · exact Or.inl (zero_smul _ _)
        · exact Or.inr ⟨by omega, one_smul _ _⟩
    rw [hk, finrank_span_singleton halt] at h
    omega

theorem path_module_group (hβ : β.IsAlt) {n : ℕ} (a : Fin n → V)
    (ψ : V ≃ₗ[ZMod 2] deletedW (n + 1)) (hψ : ∀ x y, wForm (n + 1) (ψ x) (ψ y) = β x y)
    (hψa : ∀ i, ψ (a i) = pathW i) :
    (∀ i, LinearMap.GeneralLinearGroup.congrLinearEquiv ψ (transv hβ (a i)) =
      wRep (n + 1) (Equiv.swap i.castSucc i.succ)) ∧
    (Subgroup.closure (Set.range fun i => transv hβ (a i))).map
      (LinearMap.GeneralLinearGroup.congrLinearEquiv ψ).toMonoidHom = (wRep (n + 1)).range := by
  have hgen : ∀ i, LinearMap.GeneralLinearGroup.congrLinearEquiv ψ (transv hβ (a i)) =
      wRep (n + 1) (Equiv.swap i.castSucc i.succ) := fun i => by
    rw [congrLinearEquiv_transv hβ (wForm_isAlt _) ψ hψ, hψa, wRep_swap]
  refine ⟨hgen, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, MonoidHom.range_eq_map,
    ← Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, MulEquiv.coe_toMonoidHom, hgen]

end Main

section Small

theorem card_gl_of_finrank_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (h : Module.finrank (ZMod 2) W = 2) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) W) = 6 := by
  let e : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h, Module.finrank_fin_fun])
  rw [Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)).toEquiv,
    Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem finrank_deletedW_three : Module.finrank (ZMod 2) (deletedW (2 + 1)) = 2 := by
  have h := finrank_of_path (wForm_isAlt (2 + 1)) (wForm_nondegenerate (2 + 1)) le_rfl
    (pathW (n := 2)) span_pathW pairGraph_pathW
  rw [h]
  rfl

theorem finrank_deletedW_four : Module.finrank (ZMod 2) (deletedW (3 + 1)) = 2 := by
  have h := finrank_of_path (wForm_isAlt (3 + 1)) (wForm_nondegenerate (3 + 1)) (by norm_num)
    (pathW (n := 3)) span_pathW pairGraph_pathW
  rw [h]
  rfl

theorem wRep_four_range : (wRep 4).range = ⊤ := by
  have hker : Nat.card (wRep 4).ker = 4 := by
    let S : Finset (Equiv.Perm (Fin 4)) := {1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2}
    have e : (wRep 4).ker ≃ S := Equiv.subtypeEquivRight fun σ => by
      rw [MonoidHom.mem_ker, wRep_four_eq_one_iff]
      simp [S]
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    rfl
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hidx := (wRep 4).ker.card_mul_index
  rw [hker, h24, Subgroup.index_ker] at hidx
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (deletedW 4)) :=
    Nat.finite_of_card_ne_zero (by rw [card_gl_of_finrank_two finrank_deletedW_four]; norm_num)
  apply Subgroup.eq_top_of_card_eq
  rw [card_gl_of_finrank_two finrank_deletedW_four]
  omega

theorem gl_deletedW_four_equiv :
    Nonempty (LinearMap.GeneralLinearGroup (ZMod 2) (deletedW 4) ≃* Equiv.Perm (Fin 3)) := by
  have hinj := wRep_injective (m := 3) (by norm_num) (by norm_num)
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (deletedW 3)) :=
    Nat.finite_of_card_ne_zero (by rw [card_gl_of_finrank_two finrank_deletedW_three]; norm_num)
  have hbij : Function.Bijective (wRep 3) := hinj.bijective_of_nat_card_le (by
    rw [card_gl_of_finrank_two finrank_deletedW_three, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide)
  let e43 : deletedW (3 + 1) ≃ₗ[ZMod 2] deletedW (2 + 1) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_deletedW_four, finrank_deletedW_three])
  exact ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv e43).trans
    (MulEquiv.ofBijective (wRep 3) hbij).symm⟩

end Small

section Node

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem actual_transvection_path_fully_deleted_module [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (hβ : β.IsAlt) (hnd : β.Nondegenerate) {n : ℕ} (hn : 2 ≤ n) (a : Fin n → V)
    (ha0 : ∀ i, a i ≠ 0) (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤)
    (hpath : pairGraph hβ a = SimpleGraph.pathGraph n) :
    (∃ ψ : V ≃ₗ[ZMod 2] deletedW (n + 1), (∀ x y, wForm (n + 1) (ψ x) (ψ y) = β x y) ∧
      (∀ i, ψ (a i) = pathW i) ∧
      (∀ i, LinearMap.GeneralLinearGroup.congrLinearEquiv ψ (transv hβ (a i)) =
        wRep (n + 1) (Equiv.swap i.castSucc i.succ)) ∧
      (Subgroup.closure (Set.range fun i => transv hβ (a i))).map
        (LinearMap.GeneralLinearGroup.congrLinearEquiv ψ).toMonoidHom = (wRep (n + 1)).range) ∧
    (Even n → Module.finrank (ZMod 2) V = n) ∧ (Odd n → Module.finrank (ZMod 2) V = n - 1) ∧
    (Even n → LinearIndependent (ZMod 2) a) ∧
    (Odd n → ∀ c : Fin n → ZMod 2, ∑ i, c i • a i = 0 ↔ c = 0 ∨ c = altVec n) ∧
    (∀ m, 3 ≤ m → m ≠ 4 → Function.Injective (wRep m)) ∧
    (∀ σ : Equiv.Perm (Fin 4), wRep 4 σ = 1 ↔ σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
      σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2) ∧
    (wRep 4).range = ⊤ ∧
    Nonempty (LinearMap.GeneralLinearGroup (ZMod 2) (deletedW 4) ≃* Equiv.Perm (Fin 3)) ∧
    ∃ m', 3 ≤ m' ∧ (n + 1 = 4 → m' = 3) ∧ (n + 1 ≠ 4 → m' = n + 1) ∧
      ∃ ψ' : V ≃ₗ[ZMod 2] deletedW m', (∀ x y, wForm m' (ψ' x) (ψ' y) = β x y) ∧
        (Subgroup.closure (Set.range fun i => transv hβ (a i))).map
          (LinearMap.GeneralLinearGroup.congrLinearEquiv ψ').toMonoidHom = (wRep m').range ∧
        Function.Injective (wRep m') := by
  obtain ⟨ψ, hψ, hψa, hrel⟩ := path_module_core hβ hnd hn a hspan hpath
  obtain ⟨hgen, himg⟩ := path_module_group hβ a ψ hψ hψa
  have hdim := finrank_of_path hβ hnd hn a hspan hpath
  refine ⟨⟨ψ, hψ, hψa, hgen, himg⟩, fun he => ?_, fun ho => ?_, fun he => ?_, fun ho c => ?_,
    fun m hm3 hm4 => wRep_injective hm3 hm4, wRep_four_eq_one_iff, wRep_four_range,
    gl_deletedW_four_equiv, ?_⟩
  · rw [hdim, ite_eq_left (Nat.even_iff.1 he)]
  · rw [hdim, ite_eq_right (by rw [Nat.odd_iff] at ho; omega)]
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rcases (hrel g).1 (by rw [Fintype.linearCombination_apply]; exact hg) with h | ⟨h, -⟩
    · rw [h, Pi.zero_apply]
    · exact absurd h (by rw [Nat.even_iff] at he; omega)
  · rw [← Fintype.linearCombination_apply, hrel]
    have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    simp [h1]
  · by_cases h4 : n + 1 = 4
    · obtain rfl : n = 3 := by omega
      have h02 : a 2 = a 0 := by
        have h := (hrel (altVec 3)).2 (Or.inr ⟨rfl, rfl⟩)
        rw [Fintype.linearCombination_apply, Fin.sum_univ_three] at h
        simp [altVec] at h
        have h' : a 0 = -a 2 := eq_neg_of_add_eq_zero_left h
        rw [h']
        exact (neg_eq_of_add_eq_zero_left (zmod_two_add_self (a 2))).symm
      let b : Fin 2 → V := ![a 0, a 1]
      have hbspan : Submodule.span (ZMod 2) (Set.range b) = ⊤ := by
        rw [eq_top_iff, ← hspan]
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨0, h02.symm⟩
      have h01 : β (a 0) (a 1) = 1 := by
        rw [pair_eq_pathMat hβ hpath]
        decide
      have hbpath : pairGraph hβ b = SimpleGraph.pathGraph 2 := by
        ext i j
        rw [pairGraph_adj, SimpleGraph.pathGraph_adj]
        fin_cases i <;> fin_cases j <;>
          simp [b, hβ.self_eq_zero, h01, isAlt_apply_comm hβ (a 1) (a 0)]
      obtain ⟨ψ', hψ', hψ'b, -⟩ := path_module_core hβ hnd le_rfl b hbspan hbpath
      obtain ⟨-, himg'⟩ := path_module_group hβ b ψ' hψ' hψ'b
      have hcl : Subgroup.closure (Set.range fun i => transv hβ (a i)) =
          Subgroup.closure (Set.range fun i => transv hβ (b i)) := by
        congr 1
        ext g
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨0, by simp [b, h02]⟩
        · rintro ⟨i, rfl⟩
          fin_cases i
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
      refine ⟨3, le_rfl, fun _ => rfl, fun h => absurd rfl h, ψ', hψ', ?_,
        wRep_injective le_rfl (by norm_num)⟩
      rw [hcl]
      exact himg'
    · exact ⟨n + 1, by omega, fun h => absurd h h4, fun _ => rfl, ψ, hψ, himg,
        wRep_injective (by omega) h4⟩

end Node

end CFSG.Quasithin.SteinbergBN
