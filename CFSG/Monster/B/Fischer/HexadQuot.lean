module

public import CFSG.Monster.B.Fischer.HexadStab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.Classical.Plane
  CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def B₀X : Set X₀ := {i | (i : Fin 24) ∈ B₀}

@[expose] noncomputable def U₀ : Submodule (ZMod 2) W₀ :=
  Submodule.span (ZMod 2) ((fun i => K₀.mkQ (e i)) '' B₀X)

abbrev Q₀ : Type := W₀ ⧸ U₀

@[expose] noncomputable def K₀B : Submodule (ZMod 2) V₀ :=
  K₀ ⊔ Submodule.span (ZMod 2) (e '' B₀X)

theorem U₀_eq_map : U₀ = (Submodule.span (ZMod 2) (e '' B₀X)).map K₀.mkQ := by
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem K₀_le_K₀B : K₀ ≤ K₀B := le_sup_left

theorem U₀_eq_map_K₀B : U₀ = K₀B.map K₀.mkQ := by
  rw [U₀_eq_map, K₀B, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

theorem comap_U₀ : U₀.comap K₀.mkQ = K₀B := by
  rw [U₀_eq_map, Submodule.comap_map_mkQ]
  rfl

@[expose] noncomputable def qmk : V₀ →ₗ[ZMod 2] Q₀ := U₀.mkQ ∘ₗ K₀.mkQ

theorem qmk_apply (v : V₀) : qmk v = U₀.mkQ (K₀.mkQ v) := rfl

theorem qmk_eq_zero_iff (v : V₀) : qmk v = 0 ↔ v ∈ K₀B := by
  rw [qmk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← comap_U₀,
    Submodule.mem_comap]

theorem qmk_eq_iff (v w : V₀) : qmk v = qmk w ↔ v + w ∈ K₀B := by
  rw [← sub_eq_zero, ← map_sub, qmk_eq_zero_iff, sub_eq_add_neg, ZModModule.neg_eq_self]

@[expose] def pivQ (l : ℕ) : ℕ :=
  [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21].getD l 0

@[expose] def rowQ (l : ℕ) : ℕ :=
  [1, 2, 4, 8, 16, 32, 960, 3264, 5440, 9600, 49344, 82240, 147840, 279616, 541824, 1066240,
    2115008].getD l 0

@[expose] def genQ (j : ℕ) : ℕ := if j < 11 then rowE j else if j = 11 then 5461 else 2 ^ (j - 12)

@[expose] def coefQ (l : ℕ) : ℕ :=
  [4096, 8192, 16384, 32768, 65536, 126977, 12290, 49156, 88064, 108552, 108560, 59424, 94272,
    30848, 69888, 117248, 37888].getD l 0

theorem isEchelon_Q : IsEchelon 17 pivQ rowQ := by
  unfold IsEchelon
  decide +kernel

theorem rowQ_eq : ∀ l < 17, rowQ l = xorSel (coefQ l).testBit genQ 18 := by decide +kernel

theorem red_genQ : ∀ j < 18, red 17 pivQ rowQ (genQ j) = 0 := by decide +kernel

theorem genQ_lt : ∀ j < 18, genQ j < 2 ^ 22 := by decide +kernel

theorem v₀_eq_vecOf : v₀ = vecOf 5461 := by
  rw [v₀_eq]
  congr 1

theorem e_mem_K₀B {i : X₀} (hi : i ∈ B₀X) : e i ∈ K₀B :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem pos_lt_six {i : X₀} (hi : i ∈ B₀X) : (pos i : ℕ) < 6 := by
  obtain ⟨⟨j, hj⟩, hjX⟩ := i
  change (⟨j, hj⟩ : Fin 24) ∈ B₀ at hi
  simp only [pos]
  revert hi
  simp only [B₀, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem genQ_mem_K₀B {j : ℕ} (hj : j < 18) : vecOf (genQ j) ∈ K₀B := by
  unfold genQ
  split_ifs with h1 h2
  · exact K₀_le_K₀B (E₀_le_K₀ (rowE_mem_E₀ ⟨j, h1⟩))
  · rw [← v₀_eq_vecOf]
    exact K₀_le_K₀B (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · have ht : j - 12 < 22 := by omega
    have := vecOf_two_pow ⟨j - 12, ht⟩
    simp only at this
    rw [this]
    refine e_mem_K₀B ?_
    change ((coordAt ⟨j - 12, ht⟩ : X₀) : Fin 24) ∈ B₀
    have h6 : j - 12 < 6 := by omega
    simp only [coordAt, B₀, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega

theorem K₀B_eq : K₀B = spanRows 17 rowQ := by
  refine le_antisymm ?_ ?_
  · rw [K₀B, K₀, sup_le_iff, sup_le_iff, E₀_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [spanRows, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      show vecOf (rowE l) ∈ spanRows 17 rowQ
      have e : rowE l = genQ l := by simp [genQ, l.2]
      rw [e]
      exact (vecOf_mem_span_iff isEchelon_Q (genQ_lt l (by omega))).2 (red_genQ l (by omega))
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, v₀_eq_vecOf]
      exact (vecOf_mem_span_iff isEchelon_Q (genQ_lt 11 (by omega))).2 (red_genQ 11 (by omega))
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have h6 := pos_lt_six hi
      rw [← coordAt_pos i, ← vecOf_two_pow]
      have := red_genQ (pos i + 12) (by omega)
      have e12 : genQ (pos i + 12) = 2 ^ (pos i : ℕ) := by
        simp [genQ, show ¬((pos i : ℕ) + 12 < 11) by omega, show (pos i : ℕ) + 12 ≠ 11 by omega]
      rw [e12] at this
      exact (vecOf_mem_span_iff isEchelon_Q (Nat.pow_lt_pow_right (by norm_num) (pos i).2)).2
        this
  · rw [spanRows, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show vecOf (rowQ l) ∈ K₀B
    rw [rowQ_eq l l.2, vecOf_xorSel]
    refine Submodule.sum_mem _ fun j _ => ?_
    split_ifs
    · exact genQ_mem_K₀B j.2
    · exact Submodule.zero_mem _

theorem finrank_K₀B : Module.finrank (ZMod 2) K₀B = 17 := by
  rw [K₀B_eq, finrank_spanRows isEchelon_Q]

theorem vecOf_mem_K₀B_iff {m : ℕ} (hm : m < 2 ^ 22) : vecOf m ∈ K₀B ↔ red 17 pivQ rowQ m = 0 := by
  rw [K₀B_eq]
  exact vecOf_mem_span_iff isEchelon_Q hm

theorem finrank_U₀ : Module.finrank (ZMod 2) U₀ = 5 := by
  let f : K₀B →ₗ[ZMod 2] W₀ := K₀.mkQ ∘ₗ K₀B.subtype
  have hrange : LinearMap.range f = U₀ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, U₀_eq_map_K₀B]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) = 12 := by
    have : LinearMap.ker f = K₀.comap K₀B.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rw [this, (Submodule.comapSubtypeEquivOfLe K₀_le_K₀B).finrank_eq, finrank_K₀]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, finrank_K₀B] at h
  omega

theorem finrank_Q₀ : Module.finrank (ZMod 2) Q₀ = 5 := by
  show Module.finrank (ZMod 2) (W₀ ⧸ U₀) = 5
  have h := Submodule.finrank_quotient_add_finrank U₀
  rw [finrank_U₀, finrank_W₀] at h
  omega

theorem natCard_Q₀ : Nat.card Q₀ = 32 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_Q₀]
  norm_num

@[expose] def freeQ (t : ℕ) : ℕ := [6, 7, 8, 10, 14].getD t 0

@[expose] def spreadQ (m : ℕ) : ℕ := xorSel m.testBit (fun t => 2 ^ freeQ t) 5

@[expose] noncomputable def qv (m : ℕ) : Q₀ := qmk (vecOf (spreadQ m))

theorem spreadQ_lt : ∀ m, spreadQ m < 2 ^ 22 :=
  fun m => xorSel_lt _ (fun t => by
    have : freeQ t < 22 := by
      unfold freeQ
      rcases Nat.lt_or_ge t 5 with h | h
      · interval_cases t <;> decide
      · rw [List.getD_eq_default _ _ (by simp; omega)]; decide
    exact Nat.pow_lt_pow_right (by norm_num) this) _

theorem spreadQ_xor (a b : ℕ) : spreadQ (a ^^^ b) = spreadQ a ^^^ spreadQ b := by
  rw [spreadQ, spreadQ, spreadQ, ← xorSel_xor]
  congr 1
  funext t
  rw [Nat.testBit_xor]

theorem qv_xor (a b : ℕ) : qv (a ^^^ b) = qv a + qv b := by
  rw [qv, qv, qv, spreadQ_xor, vecOf_xor, map_add]

theorem qv_zero : qv 0 = 0 := by
  rw [qv, show spreadQ 0 = 0 from rfl, vecOf_zero, map_zero]

theorem red_spreadQ : ∀ m < 32, red 17 pivQ rowQ (spreadQ m) = 0 → m = 0 := by decide +kernel

theorem qv_eq_zero_iff {m : ℕ} (hm : m < 32) : qv m = 0 ↔ m = 0 := by
  constructor
  · intro h
    rw [qv, qmk_eq_zero_iff, vecOf_mem_K₀B_iff (spreadQ_lt m)] at h
    exact red_spreadQ m hm h
  · rintro rfl
    exact qv_zero

theorem qv_inj {m m' : ℕ} (hm : m < 32) (hm' : m' < 32) (h : qv m = qv m') : m = m' := by
  have hx : m ^^^ m' < 32 := Nat.xor_lt_two_pow (n := 5) hm hm'
  have h0 : qv (m ^^^ m') = 0 := by
    rw [qv_xor, h, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have := (qv_eq_zero_iff hx).1 h0
  have := congrArg (· ^^^ m') this
  simpa [Nat.xor_assoc] using this

theorem qv_bijective : Function.Bijective fun m : Fin 32 => qv m :=
  Function.Injective.bijective_of_nat_card_le (f := fun m : Fin 32 => qv m)
    (fun a b h => Fin.ext (qv_inj a.2 b.2 h))
    (by rw [natCard_Q₀, Nat.card_eq_fintype_card, Fintype.card_fin])

theorem qv_surj (q : Q₀) : ∃ m < 32, qv m = q := by
  obtain ⟨m, hm⟩ := qv_bijective.2 q
  exact ⟨m, m.2, hm⟩

@[expose] noncomputable def qEquiv : Fin 32 ≃ Q₀ := Equiv.ofBijective _ qv_bijective

theorem qEquiv_apply (m : Fin 32) : qEquiv m = qv m := rfl

@[expose] noncomputable def bQ' (t : Fin 5) : Q₀ := qv (2 ^ (t : ℕ))

theorem spreadQ_two_pow : ∀ t < 5, spreadQ (2 ^ t) = 2 ^ freeQ t := by decide +kernel

theorem qv_eq_sum (m : ℕ) : qv m = ∑ t : Fin 5, if m.testBit t then bQ' t else 0 := by
  rw [qv, spreadQ, vecOf_xorSel, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · rw [bQ', qv, spreadQ_two_pow t t.2]
  · exact map_zero _

theorem span_bQ' : Submodule.span (ZMod 2) (Set.range bQ') = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨m, -, rfl⟩ := qv_surj q
  rw [qv_eq_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  split_ifs
  · exact Submodule.subset_span ⟨t, rfl⟩
  · exact Submodule.zero_mem _

@[expose] noncomputable def bQ : Module.Basis (Fin 5) (ZMod 2) Q₀ :=
  basisOfTopLeSpanOfCardEqFinrank bQ' span_bQ'.ge (by rw [Fintype.card_fin, finrank_Q₀])

theorem bQ_eq (t : Fin 5) : bQ t = bQ' t := by
  rw [bQ, coe_basisOfTopLeSpanOfCardEqFinrank]

@[expose] def basisCoord : Fin 5 → Fin 24 := ![8, 9, 10, 12, 16]

theorem basisCoord_mem : ∀ t, basisCoord t ∈ X₀ := by decide

theorem bQ_apply (t : Fin 5) :
    bQ t = U₀.mkQ (K₀.mkQ (e ⟨basisCoord t, basisCoord_mem t⟩)) := by
  rw [bQ_eq, bQ', qv, ← qmk_apply]
  congr 1
  have h1 : spreadQ (2 ^ (t : ℕ)) = 2 ^ freeQ t := spreadQ_two_pow t t.2
  have h2 : freeQ t < 22 := by revert t; decide
  rw [h1, vecOf_two_pow ⟨freeQ t, h2⟩]
  congr 1
  apply Subtype.ext
  apply Fin.ext
  revert t
  decide

theorem qv_eq_sum_bQ (m : ℕ) : qv m = ∑ t : Fin 5, if m.testBit t then bQ t else 0 := by
  simp only [bQ_eq]
  exact qv_eq_sum m

@[expose] noncomputable def rhoWB :
    Representation (ZMod 2) KB W₀ := rhoW.comp KB.subtype

theorem psiHom_mem_B₀ {k : CFSG.Blueprint.NativeSporadic.M22} (hk : k ∈ KB) {i : Fin 24}
    (hi : i ∈ B₀) : psiHom k i ∈ B₀ := by
  rw [mem_KB] at hk
  rw [← hk]
  exact Finset.mem_map_of_mem _ hi

theorem U₀_invariant
    (k : KB) : U₀ ≤ U₀.comap (rhoWB k) := by
  rw [U₀, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  change rhoW k (K₀.mkQ (e i)) ∈ U₀
  rw [rhoW_mkQ, rho₀_apply, permRep_e]
  exact Submodule.subset_span ⟨_, psiHom_mem_B₀ k.2 hi, rfl⟩

@[expose] noncomputable def rhoQ :
    Representation (ZMod 2) KB Q₀ :=
  rhoWB.quotient U₀ U₀_invariant

theorem rhoQ_qmk
    (k : KB) (v : V₀) : rhoQ k (qmk v) = qmk (rho₀ k v) := rfl

@[expose] def gKB : Fin 3 → KB := ![⟨g₁, g₁_mem_KB⟩, ⟨g₂, g₂_mem_KB⟩, ⟨g₃, g₃_mem_KB⟩]

@[expose] def genG (i : ℕ) (t : ℕ) : ℕ :=
  if i = 0 then genG₁ t else if i = 1 then genG₂ t else genG₃ t

@[expose] def matQ (i t : ℕ) : ℕ :=
  ([[11, 8, 7, 2, 16], [7, 4, 2, 8, 21], [8, 2, 25, 1, 13]].getD i []).getD t 0

@[expose] def linQ (i m : ℕ) : ℕ := xorSel m.testBit (matQ i) 5

theorem genG_spec : ∀ i : Fin 3, ∀ t : Fin 22,
    ((psiHom (gKB i : CFSG.Blueprint.NativeSporadic.M22) (coordAt t : Fin 24)) : ℕ) =
      genG i t + 2 := by
  intro i t
  match i with
  | 0 => exact genG₁_spec t
  | 1 => exact genG₂_spec t
  | 2 => exact genG₃_spec t

theorem genG_lt : ∀ i : Fin 3, ∀ t : Fin 22, genG i t < 22 := by decide

theorem matQ_check : ∀ i < 3, ∀ m < 32,
    red 17 pivQ rowQ (xorSel (spreadQ m).testBit (fun t => 2 ^ genG i t) 22 ^^^
      spreadQ (linQ i m)) = 0 := by
  decide +kernel

theorem perm_xor_lt (i : Fin 3) (m : ℕ) :
    xorSel m.testBit (fun t => 2 ^ genG i t) 22 < 2 ^ 22 :=
  gen_xor_lt (genG_lt i) m

theorem rhoQ_qv
    (i : Fin 3) {m : ℕ} (hm : m < 32) : rhoQ (gKB i) (qv m) = qv (linQ i m) := by
  rw [qv, rhoQ_qmk, rho₀_vecOf (g := (gKB i : CFSG.Blueprint.NativeSporadic.M22)) (genG_spec i)
    (genG_lt i), qv, qmk_eq_iff, ← vecOf_xor,
    vecOf_mem_K₀B_iff (Nat.xor_lt_two_pow (perm_xor_lt i _) (spreadQ_lt _))]
  exact matQ_check i i.2 m hm

theorem linQ_lt : ∀ i < 3, ∀ m < 32, linQ i m < 32 := by decide +kernel

theorem linQ_two_pow : ∀ i < 3, ∀ t < 5, linQ i (2 ^ t) = matQ i t := by decide +kernel

theorem two_pow_lt_32 : ∀ t : Fin 5, 2 ^ (t : ℕ) < 32 := by decide

theorem rhoQ_bQ
    (i : Fin 3) (t : Fin 5) :
    rhoQ (gKB i) (bQ t) = ∑ s : Fin 5, if (matQ i t).testBit s then bQ s else 0 := by
  rw [bQ_eq, bQ', rhoQ_qv i (two_pow_lt_32 t),
    linQ_two_pow i i.2 t t.2, qv_eq_sum_bQ]

theorem linQ_fix : ∀ m < 32, linQ 0 m = m → linQ 1 m = m → linQ 2 m = m → m = 0 := by
  decide +kernel

theorem invariants_rhoQ :
    rhoQ.invariants = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Submodule.mem_bot]
  obtain ⟨m, hm, rfl⟩ := qv_surj q
  have hfix : ∀ i : Fin 3, linQ i m = m := fun i =>
    qv_inj (linQ_lt i i.2 m hm) hm (by
      rw [← rhoQ_qv i hm]
      exact (Representation.mem_invariants _ _).1 hq (gKB i))
  rw [linQ_fix m hm (hfix 0) (hfix 1) (hfix 2), qv_zero]

end CFSG.Monster.B.Fischer
