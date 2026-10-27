module

public import CFSG.Quasithin.SteinbergBNA7Transvection
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Hasse

public noncomputable section

namespace CFSG.Quasithin.SteinbergBN

section Deleted

variable (m : ℕ)

@[expose] def sumL : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Fintype.linearCombination (ZMod 2) fun _ => (1 : ZMod 2)

theorem sumL_apply (x : Fin m → ZMod 2) : sumL m x = ∑ i, x i := by
  simp [sumL, Fintype.linearCombination_apply]

@[expose] def deltaSub : Submodule (ZMod 2) (Fin m → ZMod 2) := LinearMap.ker (sumL m)

theorem mem_deltaSub {x : Fin m → ZMod 2} : x ∈ deltaSub m ↔ ∑ i, x i = 0 := by
  rw [deltaSub, LinearMap.mem_ker, sumL_apply]

@[expose] def onesV : Fin m → ZMod 2 := fun _ => 1

@[expose] def radSub : Submodule (ZMod 2) (deltaSub m) :=
  (Submodule.span (ZMod 2) {onesV m}).comap (deltaSub m).subtype

abbrev deletedW : Type := deltaSub m ⧸ radSub m

@[expose] def dotForm : LinearMap.BilinForm (ZMod 2) (Fin m → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (x y : Fin m → ZMod 2) : dotForm m x y = ∑ i, x i * y i := rfl

theorem dotForm_comm (x y : Fin m → ZMod 2) : dotForm m x y = dotForm m y x := by
  simp only [dotForm_apply, mul_comm]

theorem dotForm_single_left (i : Fin m) (y : Fin m → ZMod 2) :
    dotForm m (Pi.single i 1) y = y i := by
  rw [dotForm_apply, Finset.sum_eq_single i (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

variable {m} in
theorem mem_radSub {x : deltaSub m} :
    x ∈ radSub m ↔ (x : Fin m → ZMod 2) ∈ Submodule.span (ZMod 2) {onesV m} :=
  Iff.rfl

variable {m} in
theorem dotForm_eq_zero_of_mem_span_ones {x y : Fin m → ZMod 2} (hx : x ∈ deltaSub m)
    (hy : y ∈ Submodule.span (ZMod 2) {onesV m}) : dotForm m x y = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [mem_deltaSub] at hx
  simp only [dotForm_apply, Pi.smul_apply, onesV, smul_eq_mul, mul_one]
  rw [← Finset.sum_mul, hx, zero_mul]

@[expose] def deltaForm : LinearMap.BilinForm (ZMod 2) (deltaSub m) :=
  (dotForm m).compl₁₂ (deltaSub m).subtype (deltaSub m).subtype

theorem radSub_le_ker_flip : radSub m ≤ LinearMap.ker (deltaForm m).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  ext x
  exact dotForm_eq_zero_of_mem_span_ones x.2 hr

theorem radSub_le_ker_liftQ_flip :
    radSub m ≤ LinearMap.ker ((radSub m).liftQ (deltaForm m).flip (radSub_le_ker_flip m)).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  change dotForm m r x = 0
  rw [dotForm_comm]
  exact dotForm_eq_zero_of_mem_span_ones x.2 hr

@[expose] def wForm : LinearMap.BilinForm (ZMod 2) (deletedW m) :=
  (radSub m).liftQ ((radSub m).liftQ (deltaForm m).flip (radSub_le_ker_flip m)).flip
    (radSub_le_ker_liftQ_flip m)

theorem wForm_mk (x y : deltaSub m) :
    wForm m (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = dotForm m x y := rfl

theorem wForm_isAlt : (wForm m).IsAlt := by
  intro w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  change dotForm m x x = 0
  have hx := (mem_deltaSub m).1 x.2
  rw [dotForm_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize (x : Fin m → ZMod 2) i = c
  revert c
  decide

theorem single_add_single_mem (i j : Fin m) :
    Pi.single i 1 + Pi.single j 1 ∈ deltaSub m := by
  rw [mem_deltaSub]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

theorem wForm_separatingLeft (w : deletedW m) (hw : ∀ w', wForm m w w' = 0) : w = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [Submodule.Quotient.mk_eq_zero, mem_radSub]
  have hpair : ∀ i j : Fin m, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h := hw (Submodule.Quotient.mk ⟨_, single_add_single_mem m i j⟩)
      rw [wForm_mk, dotForm_comm, map_add, LinearMap.add_apply, dotForm_single_left,
        dotForm_single_left] at h
      have h2 : (x : Fin m → ZMod 2) i = -(x : Fin m → ZMod 2) j := eq_neg_of_add_eq_zero_left h
      rwa [ZMod.neg_eq_self_mod_two] at h2
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : (x : Fin 0 → ZMod 2) = 0 := funext fun i => i.elim0
    rw [this]
    exact Submodule.zero_mem _
  · refine Submodule.mem_span_singleton.2 ⟨(x : Fin m → ZMod 2) ⟨0, hm⟩, funext fun i => ?_⟩
    simp only [Pi.smul_apply, onesV, smul_eq_mul, mul_one]
    exact hpair _ _

theorem wForm_nondegenerate : (wForm m).Nondegenerate := by
  refine ⟨wForm_separatingLeft m, fun w hw => wForm_separatingLeft m w fun w' => ?_⟩
  rw [isAlt_apply_comm (wForm_isAlt m)]
  exact hw w'

@[expose] def permL (σ : Equiv.Perm (Fin m)) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) σ.symm

theorem permL_apply (σ : Equiv.Perm (Fin m)) (x : Fin m → ZMod 2) (i : Fin m) :
    permL m σ x i = x (σ.symm i) := rfl

theorem permL_mem_deltaSub (σ : Equiv.Perm (Fin m)) {x : Fin m → ZMod 2}
    (hx : x ∈ deltaSub m) : permL m σ x ∈ deltaSub m := by
  rw [mem_deltaSub] at hx ⊢
  simp only [permL_apply]
  rw [Equiv.sum_comp σ.symm x, hx]

theorem permL_onesV (σ : Equiv.Perm (Fin m)) : permL m σ (onesV m) = onesV m := rfl

@[expose] def deltaEnd (σ : Equiv.Perm (Fin m)) : deltaSub m →ₗ[ZMod 2] deltaSub m :=
  (permL m σ).restrict fun _ hx => permL_mem_deltaSub m σ hx

theorem deltaEnd_coe (σ : Equiv.Perm (Fin m)) (x : deltaSub m) :
    (deltaEnd m σ x : Fin m → ZMod 2) = permL m σ x := rfl

theorem radSub_le_comap_deltaEnd (σ : Equiv.Perm (Fin m)) :
    radSub m ≤ (radSub m).comap (deltaEnd m σ) := by
  intro r hr
  rw [Submodule.mem_comap, mem_radSub, deltaEnd_coe]
  have hr' : (r : Fin m → ZMod 2) ∈ Submodule.span (ZMod 2) {onesV m} := hr
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hr'
  rw [← hc, map_smul, permL_onesV]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

@[expose] def wEndFun (σ : Equiv.Perm (Fin m)) : deletedW m →ₗ[ZMod 2] deletedW m :=
  (radSub m).mapQ (radSub m) (deltaEnd m σ) (radSub_le_comap_deltaEnd m σ)

@[expose] def wEnd : Equiv.Perm (Fin m) →* Module.End (ZMod 2) (deletedW m) where
  toFun := wEndFun m
  map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    change Submodule.Quotient.mk (deltaEnd m 1 x) = Submodule.Quotient.mk x
    congr 1)
  map_mul' σ τ := Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    change Submodule.Quotient.mk (deltaEnd m (σ * τ) x) =
      Submodule.Quotient.mk (deltaEnd m σ (deltaEnd m τ x))
    congr 1)

@[expose] def wRep : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) (deletedW m) :=
  (wEnd m).toHomUnits

theorem wRep_apply_mk (σ : Equiv.Perm (Fin m)) (x : deltaSub m) :
    (wRep m σ : deletedW m →ₗ[ZMod 2] deletedW m) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (deltaEnd m σ x) := rfl

theorem wRep_eq_one_iff (σ : Equiv.Perm (Fin m)) :
    wRep m σ = 1 ↔ ∀ x ∈ deltaSub m, permL m σ x - x ∈ Submodule.span (ZMod 2) {onesV m} := by
  constructor
  · intro h x hx
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (deletedW m) =>
      (g : deletedW m →ₗ[ZMod 2] deletedW m) (Submodule.Quotient.mk ⟨x, hx⟩)) h
    simp only [wRep_apply_mk, Units.val_one, Module.End.one_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    exact h1
  · intro h
    refine Units.ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (deltaEnd m σ x) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    exact h x x.2

end Deleted

section Path

variable {n : ℕ}

@[expose] def pathVec (i : Fin n) : Fin (n + 1) → ZMod 2 :=
  Pi.single i.castSucc 1 + Pi.single i.succ 1

theorem pathVec_mem (i : Fin n) : pathVec i ∈ deltaSub (n + 1) :=
  single_add_single_mem _ _ _

@[expose] def pathDelta (i : Fin n) : deltaSub (n + 1) := ⟨pathVec i, pathVec_mem i⟩

@[expose] def pathW (i : Fin n) : deletedW (n + 1) := Submodule.Quotient.mk (pathDelta i)

theorem dotForm_pathVec (i j : Fin n) :
    dotForm (n + 1) (pathVec i) (pathVec j) =
      if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 := by
  rw [pathVec, map_add, LinearMap.add_apply, dotForm_single_left, dotForm_single_left, pathVec]
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | omega | decide

theorem wForm_pathW (i j : Fin n) :
    wForm (n + 1) (pathW i) (pathW j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 :=
  dotForm_pathVec i j

theorem pairGraph_pathW :
    pairGraph (wForm_isAlt (n + 1)) (pathW (n := n)) = SimpleGraph.pathGraph n := by
  ext i j
  rw [pairGraph_adj, SimpleGraph.pathGraph_adj, wForm_pathW]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

@[expose] def prefixL (j : Fin n) : (Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Fintype.linearCombination (ZMod 2) fun k : Fin (n + 1) => if (k : ℕ) ≤ j then (1 : ZMod 2) else 0

theorem prefixL_pathVec (i j : Fin n) : prefixL j (pathVec i) = if i = j then 1 else 0 := by
  rw [pathVec, map_add, prefixL, Fintype.linearCombination_apply_single,
    Fintype.linearCombination_apply_single, one_smul, one_smul]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> first | omega | decide

theorem prefixL_sum_pathVec (z : Fin n → ZMod 2) (j : Fin n) :
    prefixL j (∑ i, z i • pathVec i) = z j := by
  simp only [map_sum, map_smul, prefixL_pathVec, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem finrank_deltaSub : Module.finrank (ZMod 2) (deltaSub (n + 1)) = n := by
  have hsurj : Function.Surjective (sumL (n + 1)) := fun c => ⟨Pi.single 0 c, by
    rw [sumL_apply, Finset.sum_pi_single']
    simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (sumL (n + 1))
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun]
    at h
  rw [deltaSub]
  omega

theorem span_pathDelta : Submodule.span (ZMod 2) (Set.range (pathDelta (n := n))) = ⊤ := by
  let Z := Fintype.linearCombination (ZMod 2) (pathDelta (n := n))
  have hinj : Function.Injective Z := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [Submodule.mem_bot]
    funext j
    have h1 := congrArg (fun y : deltaSub (n + 1) => prefixL j (y : Fin (n + 1) → ZMod 2)) hz
    simp only [Z, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul,
      ZeroMemClass.coe_zero, map_zero] at h1
    rw [← prefixL_sum_pathVec z j]
    exact h1
  rw [← Fintype.range_linearCombination]
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun, finrank_deltaSub]

theorem span_pathW : Submodule.span (ZMod 2) (Set.range (pathW (n := n))) = ⊤ := by
  have h : Set.range (pathW (n := n)) = (radSub (n + 1)).mkQ '' Set.range (pathDelta (n := n)) := by
    rw [← Set.range_comp]
    rfl
  rw [h, ← Submodule.map_span, span_pathDelta, Submodule.map_top, Submodule.range_mkQ]

theorem permL_swap {m : ℕ} (a b : Fin m) (hab : a ≠ b) (x : Fin m → ZMod 2) :
    permL m (Equiv.swap a b) x = x + dotForm m (Pi.single a 1 + Pi.single b 1) x •
      (Pi.single a 1 + Pi.single b 1) := by
  funext k
  rw [map_add, LinearMap.add_apply, dotForm_single_left, dotForm_single_left, permL_apply,
    Equiv.symm_swap]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hka : k = a
  · subst hka
    rw [Equiv.swap_apply_left, ite_eq_right hab]
    simp only [ite_true, add_zero, mul_one]
    rw [← add_assoc, zmod_two_add_self, zero_add]
  · by_cases hkb : k = b
    · subst hkb
      rw [Equiv.swap_apply_right, ite_eq_right hka]
      simp only [ite_true, zero_add, mul_one]
      rw [add_comm (x a) (x k), ← add_assoc, zmod_two_add_self, zero_add]
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb, ite_eq_right hka, ite_eq_right hkb]
      simp

theorem wRep_swap (i : Fin n) :
    wRep (n + 1) (Equiv.swap i.castSucc i.succ) = transv (wForm_isAlt (n + 1)) (pathW i) := by
  refine Units.ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
  change Submodule.Quotient.mk (deltaEnd (n + 1) (Equiv.swap i.castSucc i.succ) x) =
    Submodule.Quotient.mk x + wForm (n + 1) (pathW i) (Submodule.Quotient.mk x) • pathW i
  rw [pathW, wForm_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  rw [deltaEnd_coe, permL_swap _ _ (Fin.castSucc_lt_succ (i := i)).ne]
  rfl

end Path

section Faithful

variable {m : ℕ}

theorem mem_span_onesV_iff {y : Fin m → ZMod 2} :
    y ∈ Submodule.span (ZMod 2) {onesV m} ↔ y = 0 ∨ y = onesV m := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem wRep_injective (hm3 : 3 ≤ m) (hm4 : m ≠ 4) : Function.Injective (wRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix := (wRep_eq_one_iff m σ).1 hσ
  have hpair : ∀ i j : Fin m, i ≠ j →
      permL m σ (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
    intro i j hij
    have hx := single_add_single_mem m i j
    rcases mem_span_onesV_iff.1 (hfix _ hx) with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      rcases (show m = 3 ∨ 5 ≤ m by omega) with h3 | h5
      · subst h3
        have hy := (deltaSub 3).sub_mem (permL_mem_deltaSub 3 σ hx) hx
        rw [h, mem_deltaSub] at hy
        exact absurd hy (by decide)
      · obtain ⟨k, hk⟩ : ∃ k : Fin m, k ∉ ({i, j, σ i, σ j} : Finset (Fin m)) := by
          by_contra hcon
          push Not at hcon
          have hle : (Finset.univ : Finset (Fin m)) ⊆ {i, j, σ i, σ j} := fun k _ => hcon k
          have := Finset.card_le_card hle
          rw [Finset.card_univ, Fintype.card_fin] at this
          have h4 := Finset.card_le_four (a := i) (b := j) (c := σ i) (d := σ j)
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        obtain ⟨hki, hkj, hkσi, hkσj⟩ := hk
        have h1 := congrFun h k
        simp only [Pi.sub_apply, permL_apply, Pi.add_apply, Pi.single_apply, onesV] at h1
        have e1 : σ.symm k ≠ i := fun e => hkσi (by rw [← e, Equiv.apply_symm_apply])
        have e2 : σ.symm k ≠ j := fun e => hkσj (by rw [← e, Equiv.apply_symm_apply])
        rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right hki, ite_eq_right hkj] at h1
        exact absurd h1 (by decide)
  refine Equiv.ext fun i => ?_
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin m, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    have hcard : 1 < (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 hcard
    exact ⟨j, k, (Finset.ne_of_mem_erase hj).symm, (Finset.ne_of_mem_erase hk).symm, hjk⟩
  have hmem : ∀ j : Fin m, i ≠ j → σ i = i ∨ σ i = j := by
    intro j hij
    have h1 := congrFun (hpair i j hij) (σ i)
    simp only [permL_apply, Equiv.symm_apply_apply, Pi.add_apply, Pi.single_apply, ite_true,
      hij, ite_false, add_zero] at h1
    by_contra hcon
    push Not at hcon
    rw [ite_eq_right hcon.1, ite_eq_right hcon.2] at h1
    exact absurd h1 (by decide)
  rcases hmem j hij with h | h
  · exact h
  · rcases hmem k hik with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hjk

theorem wRep_four_eq_one_iff (σ : Equiv.Perm (Fin 4)) :
    wRep 4 σ = 1 ↔ σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
      σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2 := by
  rw [wRep_eq_one_iff]
  have e : ∀ x : Fin 4 → ZMod 2, permL 4 σ x = fun i => x (σ.symm i) := fun x => rfl
  simp only [mem_span_onesV_iff, mem_deltaSub, e]
  revert σ
  decide

end Faithful

end CFSG.Quasithin.SteinbergBN

