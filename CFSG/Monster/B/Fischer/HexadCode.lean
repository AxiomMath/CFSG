module

public import CFSG.Monster.B.Fischer.DesignRecognition
public import CFSG.Monster.B.Fischer.Bits22

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.Classical.Plane
  CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def permRep : Representation (ZMod 2) (Equiv.Perm X₀) V₀ where
  toFun σ := LinearMap.funLeft (ZMod 2) (ZMod 2) σ.symm
  map_one' := rfl
  map_mul' _ _ := rfl

theorem permRep_apply (σ : Equiv.Perm X₀) (v : V₀) (i : X₀) :
    permRep σ v i = v (σ.symm i) := rfl

theorem permRep_e (σ : Equiv.Perm X₀) (i : X₀) : permRep σ (e i) = e (σ i) := by
  funext j
  simp only [permRep_apply, e, Pi.single_apply, Equiv.symm_apply_eq]

@[expose] noncomputable def rho₀ : Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 V₀ :=
  permRep.comp (psiX.comp CFSG.Blueprint.NativeSporadic.M22.subtype)

theorem rho₀_apply (g : CFSG.Blueprint.NativeSporadic.M22) (v : V₀) :
    rho₀ g v = permRep (psiX g) v := rfl

theorem psiX_symm_apply (g : Equiv.Perm (Fin 22)) (i : X₀) :
    (((psiX g).symm i : X₀) : Fin 24) = (psiHom g).symm i := rfl

theorem permRep_blockVec (g : Equiv.Perm (Fin 22)) (B : Finset (Fin 24)) :
    permRep (psiX g) (blockVec B) = blockVec (B.map (psiHom g).toEmbedding) := by
  funext i
  rw [permRep_apply, blockVec_apply, blockVec_apply, psiX_symm_apply]
  by_cases h : (psiHom g).symm (i : Fin 24) ∈ B
  · simp [h, Finset.mem_map_equiv]
  · simp [h, Finset.mem_map_equiv]

@[expose] noncomputable def psiP
    (g : CFSG.Blueprint.NativeSporadic.M22) : Ppair :=
  ⟨psiM g, P0_le_Ppair (range_psiM ▸ ⟨g, rfl⟩)⟩

theorem pPerm_psiP
    (g : CFSG.Blueprint.NativeSporadic.M22) : pPerm (psiP g) = psiHom g := rfl

theorem map_mem_ℬ₀
    (g : CFSG.Blueprint.NativeSporadic.M22) {B : Finset (Fin 24)}
    (hB : B ∈ ℬ₀) : B.map (psiHom g).toEmbedding ∈ ℬ₀ :=
  (map_mem_ℬ₀_iff (psiP g) (block_spec hB).1).2 hB

theorem E₀_invariant
    (g : CFSG.Blueprint.NativeSporadic.M22) : E₀ ≤ E₀.comap (rho₀ g) := by
  rw [E₀, Submodule.span_le]
  rintro _ ⟨B, hB, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, rho₀_apply, permRep_blockVec]
  exact Submodule.subset_span ⟨_, map_mem_ℬ₀ g hB, rfl⟩

@[expose] noncomputable def rhoE :
    Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 (V₀ ⧸ E₀) :=
  rho₀.quotient E₀ E₀_invariant

theorem rhoE_mkQ
    (g : CFSG.Blueprint.NativeSporadic.M22) (v : V₀) :
    rhoE g (E₀.mkQ v) = E₀.mkQ (rho₀ g v) := rfl

@[expose] def pivE (l : ℕ) : ℕ := [5, 9, 11, 13, 15, 16, 17, 18, 19, 20, 21].getD l 0

@[expose] def rowE (l : ℕ) : ℕ :=
  [63, 963, 3276, 12495, 54671, 87067, 147863, 282898, 541841, 1069129, 2115017].getD l 0

@[expose] def coefE (l : ℕ) : ℕ :=
  [1, 2, 2097788, 2097784, 764, 2105908, 2105536, 2105472, 8300, 512, 2097916].getD l 0

@[expose] def blockRow (j : ℕ) : ℕ := blockMasks.getD j 0 >>> 2

theorem isEchelon_E : IsEchelon 11 pivE rowE := by
  unfold IsEchelon
  decide +kernel

theorem red_blockMasks : ∀ b ∈ blockMasks, red 11 pivE rowE (b >>> 2) = 0 := by decide +kernel

theorem blockMasks_shift_lt : ∀ b ∈ blockMasks, b >>> 2 < 2 ^ 22 := by decide +kernel

theorem rowE_eq : ∀ l < 11, rowE l = xorSel (coefE l).testBit blockRow 77 := by decide +kernel

theorem blockVec_blockRow {j : ℕ} (hj : j < 77) : vecOf (blockRow j) ∈ E₀ := by
  have hmem : blockMasks.getD j 0 ∈ blockMasks := by
    rw [List.getD_eq_getElem _ _ (by rw [length_blockMasks]; exact hj)]
    exact List.getElem_mem _
  rw [blockRow, ← blockVec_ofMask]
  refine Submodule.subset_span ⟨_, ?_, rfl⟩
  rw [Finset.mem_coe, ℬ₀_eq, ℬ₀list, List.mem_toFinset]
  exact List.mem_map_of_mem hmem

theorem blockVec_mem_spanE {B : Finset (Fin 24)} (hB : B ∈ ℬ₀) :
    blockVec B ∈ spanRows 11 rowE := by
  rw [ℬ₀_eq, ℬ₀list, List.mem_toFinset] at hB
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
  rw [blockVec_ofMask]
  exact (vecOf_mem_span_iff isEchelon_E (blockMasks_shift_lt b hb)).2 (red_blockMasks b hb)

theorem rowE_mem_E₀ (l : Fin 11) : vecOf (rowE l) ∈ E₀ := by
  rw [rowE_eq l l.2, vecOf_xorSel]
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · exact blockVec_blockRow j.2
  · exact Submodule.zero_mem _

theorem E₀_eq : E₀ = spanRows 11 rowE := by
  refine le_antisymm ?_ ?_
  · rw [E₀, Submodule.span_le]
    rintro _ ⟨B, hB, rfl⟩
    exact blockVec_mem_spanE hB
  · rw [spanRows, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact rowE_mem_E₀ l

theorem finrank_E₀ : Module.finrank (ZMod 2) E₀ = 11 := by
  rw [E₀_eq, finrank_spanRows isEchelon_E]

theorem vecOf_mem_E₀_iff {m : ℕ} (hm : m < 2 ^ 22) : vecOf m ∈ E₀ ↔ red 11 pivE rowE m = 0 := by
  rw [E₀_eq]
  exact vecOf_mem_span_iff isEchelon_E hm

@[expose] def genA (t : ℕ) : ℕ :=
  [8, 11, 9, 10, 4, 5, 14, 21, 0, 2, 3, 1, 15, 20, 6, 12, 16, 17, 18, 19, 13, 7].getD t 0

@[expose] def genB (t : ℕ) : ℕ :=
  [13, 4, 16, 11, 14, 3, 19, 15, 1, 9, 10, 21, 18, 2, 8, 17, 0, 20, 12, 6, 7, 5].getD t 0

theorem genA_spec : ∀ t : Fin 22, ((psiHom m22gA (coordAt t : Fin 24)) : ℕ) = genA t + 2 := by
  rw [psi_m22gA]
  decide +kernel

theorem genB_spec : ∀ t : Fin 22, ((psiHom m22gB (coordAt t : Fin 24)) : ℕ) = genB t + 2 := by
  rw [psi_m22gB]
  decide +kernel

theorem genA_lt : ∀ t : Fin 22, genA t < 22 := by decide

theorem genB_lt : ∀ t : Fin 22, genB t < 22 := by decide

theorem psiX_coordAt {g : Equiv.Perm (Fin 22)} {gen : ℕ → ℕ}
    (hspec : ∀ t : Fin 22, ((psiHom g (coordAt t : Fin 24)) : ℕ) = gen t + 2)
    (hlt : ∀ t : Fin 22, gen t < 22) (t : Fin 22) :
    psiX g (coordAt t) = coordAt ⟨gen t, hlt t⟩ := by
  apply Subtype.ext; apply Fin.ext
  rw [psiX_apply, hspec t]
  rfl

theorem rho₀_vecOf {g : CFSG.Blueprint.NativeSporadic.M22} {gen : ℕ → ℕ}
    (hspec : ∀ t : Fin 22, ((psiHom g (coordAt t : Fin 24)) : ℕ) = gen t + 2)
    (hlt : ∀ t : Fin 22, gen t < 22) (m : ℕ) :
    rho₀ g (vecOf m) = vecOf (xorSel m.testBit (fun t => 2 ^ gen t) 22) := by
  refine map_vecOf (rho₀ g) vecOf vecOf_xor vecOf_zero (fun t => ?_) m
  rw [vecOf_two_pow, rho₀_apply, permRep_e, psiX_coordAt hspec hlt t]
  exact (vecOf_two_pow ⟨gen t, hlt t⟩).symm

theorem rho₀_a_vecOf (m : ℕ) :
    rho₀ m22a (vecOf m) = vecOf (xorSel m.testBit (fun t => 2 ^ genA t) 22) :=
  rho₀_vecOf (g := m22a) genA_spec genA_lt m

theorem rho₀_b_vecOf (m : ℕ) :
    rho₀ m22b (vecOf m) = vecOf (xorSel m.testBit (fun t => 2 ^ genB t) 22) :=
  rho₀_vecOf (g := m22b) genB_spec genB_lt m

@[expose] def freeE (t : ℕ) : ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14].getD t 0

@[expose] def spreadE (n : ℕ) : ℕ := xorSel n.testBit (fun t => 2 ^ freeE t) 11

@[expose] def fixesE (gen : ℕ → ℕ) (n : ℕ) : Bool :=
  red 11 pivE rowE (xorSel (spreadE n).testBit (fun t => 2 ^ gen t) 22 ^^^ spreadE n) == 0

set_option maxRecDepth 10000 in
theorem fixed_check : ∀ n < 2048, (fixesE genA n && fixesE genB n) = (n == 0 || n == 949) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem red_spreadE : ∀ n < 2048, red 11 pivE rowE (spreadE n) = 0 → n = 0 := by decide +kernel

theorem spreadE_lt : ∀ n, spreadE n < 2 ^ 22 :=
  fun n => xorSel_lt _ (fun t => by
    have : freeE t < 22 := by
      unfold freeE
      rcases Nat.lt_or_ge t 11 with h | h
      · interval_cases t <;> decide
      · rw [List.getD_eq_default _ _ (by simp; omega)]; decide
    exact Nat.pow_lt_pow_right (by norm_num) this) _

theorem spreadE_xor (n n' : ℕ) : spreadE (n ^^^ n') = spreadE n ^^^ spreadE n' := by
  rw [spreadE, spreadE, spreadE, ← xorSel_xor]
  congr 1
  funext t
  rw [Nat.testBit_xor]

theorem spreadE_949 :
    spreadE 949 = 2 ^ 0 ^^^ 2 ^ 2 ^^^ 2 ^ 4 ^^^ 2 ^ 6 ^^^ 2 ^ 8 ^^^ 2 ^ 10 ^^^ 2 ^ 12 := by
  decide +kernel

theorem v₀_eq : v₀ = vecOf (spreadE 949) := by
  rw [spreadE_949]
  simp only [vecOf_xor]
  have h0 : vecOf (2 ^ 0) = e (coordAt 0) := vecOf_two_pow 0
  have h2 : vecOf (2 ^ 2) = e (coordAt 2) := vecOf_two_pow 2
  have h4 : vecOf (2 ^ 4) = e (coordAt 4) := vecOf_two_pow 4
  have h6 : vecOf (2 ^ 6) = e (coordAt 6) := vecOf_two_pow 6
  have h8 : vecOf (2 ^ 8) = e (coordAt 8) := vecOf_two_pow 8
  have h10 : vecOf (2 ^ 10) = e (coordAt 10) := vecOf_two_pow 10
  have h12 : vecOf (2 ^ 12) = e (coordAt 12) := vecOf_two_pow 12
  rw [h0, h2, h4, h6, h8, h10, h12]
  rfl

theorem gen_xor_lt {gen : ℕ → ℕ} (hlt : ∀ t : Fin 22, gen t < 22) (m : ℕ) :
    xorSel m.testBit (fun t => 2 ^ gen t) 22 < 2 ^ 22 := by
  have key : ∀ n ≤ 22, xorSel m.testBit (fun t => 2 ^ gen t) n < 2 ^ 22 := by
    intro n hn
    induction n with
    | zero => exact Nat.two_pow_pos 22
    | succ n ih =>
      rw [xorSel]
      refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) (hlt ⟨n, by omega⟩)
      · exact Nat.two_pow_pos 22
  exact key 22 le_rfl

theorem rhoE_fix_iff
    {g : CFSG.Blueprint.NativeSporadic.M22} {gen : ℕ → ℕ}
    (hspec : ∀ t : Fin 22, ((psiHom g (coordAt t : Fin 24)) : ℕ) = gen t + 2)
    (hlt : ∀ t : Fin 22, gen t < 22) (n : ℕ) :
    rhoE g (E₀.mkQ (vecOf (spreadE n))) = E₀.mkQ (vecOf (spreadE n)) ↔
      red 11 pivE rowE (xorSel (spreadE n).testBit (fun t => 2 ^ gen t) 22 ^^^ spreadE n) = 0 := by
  rw [rhoE_mkQ, rho₀_vecOf hspec hlt, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, ← vecOf_mem_E₀_iff (Nat.xor_lt_two_pow (gen_xor_lt hlt _)
      (spreadE_lt n)), vecOf_xor, sub_eq_add_neg, ZModModule.neg_eq_self]

theorem mkQ_spreadE_injective :
    Function.Injective fun n : Fin 2048 => E₀.mkQ (vecOf (spreadE n)) := by
  intro n n' h
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  rw [sub_eq_add_neg, ZModModule.neg_eq_self, ← vecOf_xor, ← spreadE_xor,
    vecOf_mem_E₀_iff (spreadE_lt _)] at h
  have hx : (n : ℕ) ^^^ n' < 2048 := Nat.xor_lt_two_pow (n := 11) n.2 n'.2
  have h0 := red_spreadE _ hx h
  apply Fin.ext
  have := congrArg (· ^^^ (n' : ℕ)) h0
  simpa [Nat.xor_assoc] using this

theorem natCard_quotient_E₀ : Nat.card (V₀ ⧸ E₀) = 2048 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h := Submodule.finrank_quotient_add_finrank E₀
  rw [finrank_E₀, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_X₀] at h
  rw [show Module.finrank (ZMod 2) (V₀ ⧸ E₀) = 11 by omega]
  norm_num

theorem exists_spreadE (q : V₀ ⧸ E₀) : ∃ n < 2048, E₀.mkQ (vecOf (spreadE n)) = q := by
  have hbij := mkQ_spreadE_injective.bijective_of_nat_card_le (by
    rw [natCard_quotient_E₀, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨n, hn⟩ := hbij.2 q
  exact ⟨n, n.2, hn⟩

theorem fixed_of_gens
    {q : V₀ ⧸ E₀} (ha : rhoE m22a q = q) (hb : rhoE m22b q = q)
    (g : CFSG.Blueprint.NativeSporadic.M22) : rhoE g q = q := by
  have hg : g ∈ Subgroup.closure ({m22a, m22b} : Set CFSG.Blueprint.NativeSporadic.M22) := by
    rw [closure_pair_eq_top m22_eq]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => rw [map_one]; rfl
  | mul x y _ _ hx hy => rw [map_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem mkQ_v₀_ne_zero : E₀.mkQ v₀ ≠ 0 := by
  rw [v₀_eq, Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    vecOf_mem_E₀_iff (spreadE_lt _)]
  decide +kernel

theorem invariants_rhoE :
    rhoE.invariants = Submodule.span (ZMod 2) {E₀.mkQ v₀} := by
  have hv₀ : ∀ g, rhoE g (E₀.mkQ v₀) = E₀.mkQ v₀ := by
    refine fixed_of_gens ?_ ?_ <;> rw [v₀_eq]
    · exact (rhoE_fix_iff (g := m22a) genA_spec genA_lt 949).2 (by decide +kernel)
    · exact (rhoE_fix_iff (g := m22b) genB_spec genB_lt 949).2 (by decide +kernel)
  refine le_antisymm (fun q hq => ?_) ?_
  · obtain ⟨n, hn, rfl⟩ := exists_spreadE q
    have hq' := (Representation.mem_invariants _ _).1 hq
    have h1 := (rhoE_fix_iff (g := m22a) genA_spec genA_lt n).1 (hq' m22a)
    have h2 := (rhoE_fix_iff (g := m22b) genB_spec genB_lt n).1 (hq' m22b)
    have hfc := fixed_check n hn
    have hA : fixesE genA n = true := by simp only [fixesE, h1, beq_self_eq_true]
    have hB : fixesE genB n = true := by simp only [fixesE, h2, beq_self_eq_true]
    rw [hA, hB, Bool.true_and] at hfc
    have h' : n = 0 ∨ n = 949 := by
      have := hfc.symm
      simpa only [Bool.or_eq_true, beq_iff_eq] using this
    rcases h' with rfl | rfl
    · rw [show spreadE 0 = 0 from rfl, vecOf_zero, map_zero]
      exact Submodule.zero_mem _
    · rw [← v₀_eq]
      exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (Representation.mem_invariants _ _).2 hv₀

theorem v₀_not_mem_E₀ : v₀ ∉ E₀ := fun h =>
  mkQ_v₀_ne_zero ((Submodule.Quotient.mk_eq_zero _).2 h)

theorem finrank_sup_span_singleton {u : V₀} (hu : u ∉ E₀) :
    Module.finrank (ZMod 2) ↥(E₀ ⊔ Submodule.span (ZMod 2) {u}) = 12 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ E₀.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq E₀ (Submodule.span (ZMod 2) {u})
  have hdisj : E₀ ⊓ Submodule.span (ZMod 2) {u} = ⊥ :=
    disjoint_iff.1 ((Submodule.disjoint_span_singleton' hu0).2 hu)
  rw [hdisj, finrank_bot, add_zero, finrank_E₀, finrank_span_singleton hu0] at h
  exact h

theorem finrank_K₀ : Module.finrank (ZMod 2) K₀ = 12 :=
  finrank_sup_span_singleton v₀_not_mem_E₀

theorem E₀_le_K₀ : E₀ ≤ K₀ := le_sup_left

theorem rhoE_v₀
    (g : CFSG.Blueprint.NativeSporadic.M22) : rhoE g (E₀.mkQ v₀) = E₀.mkQ v₀ := by
  have hmem : E₀.mkQ v₀ ∈ rhoE.invariants := by
    rw [invariants_rhoE]
    exact Submodule.mem_span_singleton_self _
  exact (Representation.mem_invariants _ _).1 hmem g

theorem rho₀_v₀_sub_mem
    (g : CFSG.Blueprint.NativeSporadic.M22) : rho₀ g v₀ - v₀ ∈ E₀ := by
  have := rhoE_v₀ g
  rw [rhoE_mkQ, Submodule.mkQ_apply, Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.eq _).1 this

theorem K₀_invariant
    (g : CFSG.Blueprint.NativeSporadic.M22) : K₀ ≤ K₀.comap (rho₀ g) := by
  rw [K₀, sup_le_iff]
  constructor
  · exact (E₀_invariant g).trans (Submodule.comap_mono le_sup_left)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]
    have h2 : rho₀ g v₀ = (rho₀ g v₀ - v₀) + v₀ := by abel
    rw [h2]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (rho₀_v₀_sub_mem g))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

@[expose] noncomputable def rhoW :
    Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 W₀ :=
  rho₀.quotient K₀ K₀_invariant

theorem rhoW_mkQ
    (g : CFSG.Blueprint.NativeSporadic.M22) (v : V₀) :
    rhoW g (K₀.mkQ v) = K₀.mkQ (rho₀ g v) := rfl

theorem finrank_W₀ : Module.finrank (ZMod 2) W₀ = 10 := by
  show Module.finrank (ZMod 2) (V₀ ⧸ K₀) = 10
  have h := Submodule.finrank_quotient_add_finrank K₀
  rw [finrank_K₀, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_X₀] at h
  omega

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem eq_K₀
    {U : Submodule (ZMod 2) V₀} (hEU : E₀ ≤ U)
    (h12 : Module.finrank (ZMod 2) U = 12)
    (hinv : ∀ g : CFSG.Blueprint.NativeSporadic.M22, U ≤ U.comap (rho₀ g)) : U = K₀ := by
  obtain ⟨u, huU, huE⟩ : ∃ u ∈ U, u ∉ E₀ := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (fun x hx => h x hx : U ≤ E₀)
    rw [h12, finrank_E₀] at this
    omega
  have hU : E₀ ⊔ Submodule.span (ZMod 2) {u} = U :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hEU ((Submodule.span_singleton_le_iff_mem _ _).2 huU))
      (by rw [finrank_sup_span_singleton huE, h12])
  have hfix : ∀ g, rhoE g (E₀.mkQ u) = E₀.mkQ u := by
    intro g
    have hgu : rho₀ g u ∈ E₀ ⊔ Submodule.span (ZMod 2) {u} := hU ▸ hinv g huU
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hgu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rcases zmod2_cases c with rfl | rfl
    · exfalso
      rw [zero_smul, add_zero] at hxy
      apply huE
      have := E₀_invariant g⁻¹ (hxy ▸ hx)
      rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] at this
    · rw [one_smul] at hxy
      rw [rhoE_mkQ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hxy,
        add_sub_cancel_right]
      exact hx
  have hmem : E₀.mkQ u ∈ Submodule.span (ZMod 2) {E₀.mkQ v₀} := by
    rw [← invariants_rhoE]
    exact (Representation.mem_invariants _ _).2 hfix
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rcases zmod2_cases c with rfl | rfl
  · exfalso
    rw [zero_smul] at hc
    exact huE ((Submodule.Quotient.mk_eq_zero _).1 hc.symm)
  · rw [one_smul, Submodule.mkQ_apply, Submodule.mkQ_apply] at hc
    have hvu : v₀ - u ∈ E₀ := (Submodule.Quotient.eq _).1 hc
    have hv₀U : v₀ ∈ U := by
      have : v₀ = (v₀ - u) + u := by abel
      rw [this]
      exact U.add_mem (hEU hvu) huU
    have hK : K₀ ≤ U := sup_le hEU ((Submodule.span_singleton_le_iff_mem _ _).2 hv₀U)
    exact (Submodule.eq_of_le_of_finrank_eq hK (by rw [finrank_K₀, h12])).symm

theorem hammingNorm_vecOf (m : ℕ) : hammingNorm (vecOf m) = popc 22 m := by
  rw [← hammingNorm_bvec]
  unfold hammingNorm
  refine Finset.card_bij (fun i _ => pos i)
    (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩)
    (fun i _ j _ h => by rw [← coordAt_pos i, ← coordAt_pos j, h]) (fun t ht => ?_)
  refine ⟨coordAt t, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, pos_coordAt t⟩
  change bvec 22 m (pos (coordAt t)) ≠ 0
  rw [pos_coordAt]
  exact (Finset.mem_filter.1 ht).2

theorem hammingNorm_v₀ : hammingNorm v₀ = 7 := by
  rw [v₀_eq, hammingNorm_vecOf]
  decide +kernel

theorem MOG_derived_hexad_code_unique_invariant_extension :
    (∀ g : CFSG.Blueprint.NativeSporadic.M22, ∀ i, rho₀ g (e i) = e (psiX g i)) ∧
    (∀ g : CFSG.Blueprint.NativeSporadic.M22, E₀ ≤ E₀.comap (rho₀ g)) ∧
    Module.finrank (ZMod 2) E₀ = 11 ∧
    rhoE.invariants = Submodule.span (ZMod 2) {E₀.mkQ v₀} ∧ E₀.mkQ v₀ ≠ 0 ∧
    (∀ g : CFSG.Blueprint.NativeSporadic.M22, K₀ ≤ K₀.comap (rho₀ g)) ∧ E₀ ≤ K₀ ∧
    Module.finrank (ZMod 2) K₀ = 12 ∧
    (∀ U : Submodule (ZMod 2) V₀, E₀ ≤ U → Module.finrank (ZMod 2) U = 12 →
      (∀ g : CFSG.Blueprint.NativeSporadic.M22, U ≤ U.comap (rho₀ g)) → U = K₀) ∧
    Module.finrank (ZMod 2) W₀ = 10 ∧ hammingNorm v₀ = 7 ∧ Odd (hammingNorm v₀) :=
  ⟨fun g i => permRep_e _ i, E₀_invariant, finrank_E₀, invariants_rhoE, mkQ_v₀_ne_zero,
    K₀_invariant, E₀_le_K₀, finrank_K₀, fun _ hEU h12 hinv => eq_K₀ hEU h12 hinv, finrank_W₀,
    hammingNorm_v₀, by rw [hammingNorm_v₀]; decide⟩

end CFSG.Monster.B.Fischer
