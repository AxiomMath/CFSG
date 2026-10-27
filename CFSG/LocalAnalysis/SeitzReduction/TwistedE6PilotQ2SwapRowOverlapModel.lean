module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi

set_option maxRecDepth 100000 in
theorem matRoot_chain_check_ovl : ∀ a m b : Fin 6, a ≠ m → m ≠ b → a ≠ b →
    matRoot a m ≠ matRoot m b ∧ matRoot a m ≠ -matRoot m b ∧
      matRoot a m + matRoot m b = matRoot a b := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem matRoot_swap_ovl : ∀ a b : Fin 6, matRoot b a = -matRoot a b := by
  decide +kernel

section Dictionary

variable {K : Type} [Field K]

theorem realize_transvection_adj_ovl (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b)
    (hadj : b.val = a.val + 1 ∨ a.val = b.val + 1) (c : K) :
    realize h2 (SpecialLinearGroup.transvection hab c) =
      pinnedX TwistTag.E6.tag K (matRoot a b) c := by
  rcases hadj with h | h
  · obtain ⟨t, rfl, rfl⟩ : ∃ t : Fin 5, t.castSucc = a ∧ t.succ = b :=
      ⟨⟨a.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp [h])⟩
    rw [matRoot_adjacent, pinnedX_single]
    exact realize_x h2 t c
  · obtain ⟨t, rfl, rfl⟩ : ∃ t : Fin 5, t.succ = a ∧ t.castSucc = b :=
      ⟨⟨b.val, by omega⟩, Fin.ext (by simp [h]), Fin.ext rfl⟩
    rw [matRoot_adjacent_neg, pinnedX_neg_single]
    exact realize_y h2 t c

theorem realize_transvection_ovl_aux (h2 : (2 : K) = 0) : ∀ (d : ℕ) {a b : Fin 6} (hab : a ≠ b),
    (b.val = a.val + d + 1 ∨ a.val = b.val + d + 1) → ∀ c : K,
      realize h2 (SpecialLinearGroup.transvection hab c) =
        pinnedX TwistTag.E6.tag K (matRoot a b) c := by
  intro d
  induction d with
  | zero =>
    intro a b hab hd c
    exact realize_transvection_adj_ovl h2 hab (by omega) c
  | succ d ih =>
    intro a b hab hd c
    rcases hd with hd | hd
    · obtain ⟨m, hm⟩ : ∃ m : Fin 6, m.val = b.val - 1 := ⟨⟨b.val - 1, by omega⟩, rfl⟩
      have ham : a ≠ m := fun h => by subst h; omega
      have hmb : m ≠ b := fun h => by subst h; omega
      obtain ⟨h1, h1', h3⟩ := matRoot_chain_check_ovl a m b ham hmb hab
      have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection ham hmb hab c 1
      rw [mul_one] at hc
      rw [← hc, map_commutatorElement, ih ham (Or.inl (by omega)) c,
        realize_transvection_adj_ovl h2 hmb (Or.inl (by omega)) 1,
        commutator_pinnedX_of_two h2 (isRoot_matRoot ham) (isRoot_matRoot hmb) h1 h1'
          (by rw [h3]; exact isRoot_matRoot hab), h3, mul_one]
    · obtain ⟨m, hm⟩ : ∃ m : Fin 6, m.val = a.val - 1 := ⟨⟨a.val - 1, by omega⟩, rfl⟩
      have ham : a ≠ m := fun h => by subst h; omega
      have hmb : m ≠ b := fun h => by subst h; omega
      obtain ⟨h1, h1', h3⟩ := matRoot_chain_check_ovl a m b ham hmb hab
      have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection ham hmb hab c 1
      rw [mul_one] at hc
      rw [← hc, map_commutatorElement, realize_transvection_adj_ovl h2 ham (Or.inr (by omega)) c,
        ih hmb (Or.inr (by omega)) 1,
        commutator_pinnedX_of_two h2 (isRoot_matRoot ham) (isRoot_matRoot hmb) h1 h1'
          (by rw [h3]; exact isRoot_matRoot hab), h3, mul_one]

theorem realize_transvection_ovl (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b) (c : K) :
    realize h2 (SpecialLinearGroup.transvection hab c) =
      pinnedX TwistTag.E6.tag K (matRoot a b) c := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' := Fin.lt_def.1 h
    exact realize_transvection_ovl_aux h2 (b.val - a.val - 1) hab (Or.inl (by omega)) c
  · have h' := Fin.lt_def.1 h
    exact realize_transvection_ovl_aux h2 (a.val - b.val - 1) hab (Or.inr (by omega)) c

end Dictionary

@[expose] def ovlPt (p : Fin 3) : Fin 6 := Fin.castLE (by norm_num) p

@[expose] def ovlSet (p : Fin 3) : Finset (Fin 6) :=
  ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6))ᶜ

@[expose] def ovlIdx (p : Fin 3) : Fin 4 → Fin 6 :=
  (![![1, 2, 3, 4], ![0, 2, 3, 5], ![0, 1, 4, 5]] : Fin 3 → Fin 4 → Fin 6) p

@[expose] def ovlPos (p : Fin 3) : Fin 6 → Fin 4 :=
  (![![0, 0, 1, 2, 3, 0], ![0, 0, 1, 2, 0, 3], ![0, 1, 0, 0, 2, 3]] : Fin 3 → Fin 6 → Fin 4) p

theorem ovl_check : ∀ p : Fin 3, (∀ t, ovlIdx p t ∈ ovlSet p) ∧
    (∀ t, ovlPos p (ovlIdx p t) = t) ∧ (∀ x ∈ ovlSet p, ovlIdx p (ovlPos p x) = x) ∧
    (∀ t, ovlIdx p (Fin.rev t) = Fin.rev (ovlIdx p t)) ∧
    (∀ x, x ∈ ovlSet p → Fin.rev x ∈ ovlSet p) ∧ ovlPt p ∉ ovlSet p ∧
    Fin.rev (ovlPt p) ∉ ovlSet p ∧ ovlPt p ≠ Fin.rev (ovlPt p) := by
  decide

theorem ovlIdx_eq_rev_iff : ∀ (p : Fin 3) (s t : Fin 4),
    ovlIdx p t = Fin.rev (ovlIdx p s) ↔ t = Fin.rev s := by
  decide

@[expose] def ovlEquiv (p : Fin 3) : Fin 4 ≃ ↥(ovlSet p) where
  toFun t := ⟨ovlIdx p t, (ovl_check p).1 t⟩
  invFun x := ovlPos p x
  left_inv t := (ovl_check p).2.1 t
  right_inv x := Subtype.ext ((ovl_check p).2.2.1 x x.2)

section Embed

variable {K : Type} [Field K]

@[expose] noncomputable def ovlEmbed (p : Fin 3) :
    SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 6) K :=
  (LinearPilot.blockEmbed (ovlSet p)).comp
    (LinearPilot.reindexSpecialLinear (K := K) (ovlEquiv p)).toMonoidHom

theorem ovlEmbed_apply (p : Fin 3) (A : SpecialLinearGroup (Fin 4) K) (x y : Fin 6) :
    (ovlEmbed p A : Matrix (Fin 6) (Fin 6) K) x y =
      if x ∈ ovlSet p ∧ y ∈ ovlSet p then (A : Matrix (Fin 4) (Fin 4) K) (ovlPos p x) (ovlPos p y)
      else (1 : Matrix (Fin 6) (Fin 6) K) x y := by
  change LinearPilot.blockMatrix (ovlSet p)
    ((LinearPilot.reindexSpecialLinear (K := K) (ovlEquiv p) A :
      SpecialLinearGroup ↥(ovlSet p) K) : Matrix ↥(ovlSet p) ↥(ovlSet p) K) x y = _
  rw [LinearPilot.blockMatrix_apply]
  by_cases h : x ∈ ovlSet p ∧ y ∈ ovlSet p
  · rw [dite_eq_left h, ite_eq_left h]
    rfl
  · rw [dite_eq_right h, ite_eq_right h]

theorem ovlEmbed_injective (p : Fin 3) : Function.Injective (ovlEmbed (K := K) p) :=
  (LinearPilot.blockEmbed_injective (ovlSet p)).comp
    (LinearPilot.reindexSpecialLinear (K := K) (ovlEquiv p)).injective

theorem range_ovlEmbed (p : Fin 3) :
    (ovlEmbed (K := K) p).range = LinearPilot.blockSpecialLinear (ovlSet p) := by
  rw [ovlEmbed, MonoidHom.range_comp, MonoidHom.range_eq_top.2
    (LinearPilot.reindexSpecialLinear (K := K) (ovlEquiv p)).surjective, ← MonoidHom.range_eq_map,
    LinearPilot.range_blockEmbed]

theorem transpose_mul_rev_mul_apply_ovl {n : ℕ} (N M : Matrix (Fin n) (Fin n) K) (x y : Fin n) :
    (Nᵀ * (Matrix.of fun i j : Fin n => if j = Fin.rev i then (1 : K) else 0) * M) x y =
      ∑ w, N (Fin.rev w) x * M w y := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev w)]
  · simp [Fin.rev_rev]
  · intro z _ hz
    have : ¬ (w = Fin.rev z) := fun h => hz (by rw [h, Fin.rev_rev])
    simp [this]
  · simp

theorem sum_eq_sum_ovlIdx {M : Type*} [AddCommMonoid M] (p : Fin 3) (f : Fin 6 → M)
    (hf : ∀ w, w ∉ ovlSet p → f w = 0) : ∑ w, f w = ∑ u : Fin 4, f (ovlIdx p u) := by
  rw [← Finset.sum_subset (Finset.subset_univ (ovlSet p)) (fun w _ hw => hf w hw),
    ← Finset.sum_coe_sort (ovlSet p)]
  exact (Fintype.sum_equiv (ovlEquiv p) _ _ fun u => rfl).symm

theorem antiId_ovlIdx (p : Fin 3) (s t : Fin 4) :
    antiId K (ovlIdx p s) (ovlIdx p t) = CFSG.LieType.Universal.Unitary.antidiag 4 s t := by
  simp only [antiId, CFSG.LieType.Universal.Unitary.antidiag, Matrix.of_apply]
  by_cases h : t = Fin.rev s
  · rw [ite_eq_left ((ovlIdx_eq_rev_iff p s t).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((ovlIdx_eq_rev_iff p s t).1 h')), ite_eq_right h]

theorem ovlEmbed_mem_unitarySL_iff (p : Fin 3) {σ : K →+* K} (A : SpecialLinearGroup (Fin 4) K) :
    ovlEmbed p A ∈ unitarySL σ ↔
      ((A : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * CFSG.LieType.Universal.Unitary.antidiag 4 *
        (A : Matrix (Fin 4) (Fin 4) K) = CFSG.LieType.Universal.Unitary.antidiag 4 := by
  obtain ⟨hmem, hpos, hidx, hrev, hSrev, -, -, -⟩ := ovl_check p
  rw [mem_unitarySL_iff]
  have hM := ovlEmbed_apply p A
  generalize (ovlEmbed p A : Matrix (Fin 6) (Fin 6) K) = M at hM ⊢
  generalize (A : Matrix (Fin 4) (Fin 4) K) = B at hM ⊢
  have hMo : ∀ x y, ¬(x ∈ ovlSet p ∧ y ∈ ovlSet p) →
      M x y = (1 : Matrix (Fin 6) (Fin 6) K) x y := fun x y h => by rw [hM, ite_eq_right h]
  have hMS : ∀ s t, M (ovlIdx p s) (ovlIdx p t) = B s t := fun s t => by
    rw [hM, ite_eq_left ⟨hmem s, hmem t⟩, hpos, hpos]
  have hrevS : ∀ x, x ∉ ovlSet p → Fin.rev x ∉ ovlSet p := fun x hx h => hx (by
    simpa using hSrev _ h)
  have hJ : antiId K = Matrix.of fun i j : Fin 6 => if j = Fin.rev i then (1 : K) else 0 := rfl
  have hJ4 : (CFSG.LieType.Universal.Unitary.antidiag 4 : Matrix (Fin 4) (Fin 4) K) =
      Matrix.of fun i j : Fin 4 => if j = Fin.rev i then (1 : K) else 0 := rfl
  have hblock : ∀ s t, ((M.map σ)ᵀ * antiId K * M) (ovlIdx p s) (ovlIdx p t) =
      ((B.map σ)ᵀ * CFSG.LieType.Universal.Unitary.antidiag 4 * B : Matrix (Fin 4) (Fin 4) K)
        s t := by
    intro s t
    rw [hJ, hJ4, transpose_mul_rev_mul_apply_ovl, transpose_mul_rev_mul_apply_ovl,
      sum_eq_sum_ovlIdx p]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [Matrix.map_apply, Matrix.map_apply, ← hrev, hMS, hMS]
    · intro w hw
      rw [hMo w _ (fun h => hw h.1), Matrix.one_apply_ne (fun h => hw (by rw [h]; exact hmem t)),
        mul_zero]
  have hoff : ∀ x y, ¬(x ∈ ovlSet p ∧ y ∈ ovlSet p) →
      ((M.map σ)ᵀ * antiId K * M) x y = antiId K x y := by
    intro x y hxy
    rw [hJ, transpose_mul_rev_mul_apply_ovl]
    by_cases hx : x ∈ ovlSet p
    · have hy : y ∉ ovlSet p := fun hy => hxy ⟨hx, hy⟩
      rw [Finset.sum_eq_single y]
      · have hyx : Fin.rev y ≠ x := fun h => hrevS y hy (by rw [h]; exact hx)
        rw [Matrix.map_apply, hMo _ _ (fun h => hrevS y hy h.1), Matrix.one_apply_ne hyx, map_zero,
          zero_mul, Matrix.of_apply, ite_eq_right (fun h => hy (by rw [h]; exact hSrev x hx))]
      · intro w _ hw
        rw [hMo w y (fun h => hy h.2), Matrix.one_apply_ne hw, mul_zero]
      · simp
    · rw [Finset.sum_eq_single (Fin.rev x)]
      · rw [Fin.rev_rev, Matrix.map_apply, hMo x x (fun h => hx h.1), Matrix.one_apply_eq,
          map_one, one_mul, hMo _ y (fun h => hrevS x hx h.1), Matrix.one_apply, Matrix.of_apply]
        by_cases h : Fin.rev x = y
        · rw [ite_eq_left h, ite_eq_left h.symm]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
      · intro w _ hw
        rw [Matrix.map_apply, hMo (Fin.rev w) x (fun h => hx h.2),
          Matrix.one_apply_ne (fun h => hw (by rw [← h, Fin.rev_rev])), map_zero, zero_mul]
      · simp
  constructor
  · intro h
    ext s t
    rw [← hblock, h, antiId_ovlIdx]
  · intro h
    ext x y
    by_cases hxy : x ∈ ovlSet p ∧ y ∈ ovlSet p
    · rw [← hidx x hxy.1, ← hidx y hxy.2, hblock, h, antiId_ovlIdx]
    · exact hoff x y hxy

end Embed

section SU

open CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] (σ' : K ≃+* K)

@[expose] def suToSL4 : SU σ' 4 →* SpecialLinearGroup (Fin 4) K where
  toFun A := ⟨((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), A.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem suToSL4_injective : Function.Injective (suToSL4 σ') := fun _ _ h =>
  Subtype.ext (Units.ext (congrArg Subtype.val h))

@[expose] noncomputable def ovlSU (p : Fin 3) : SU σ' 4 →* SpecialLinearGroup (Fin 6) K :=
  (ovlEmbed p).comp (suToSL4 σ')

theorem range_ovlSU (p : Fin 3) {σ : K →+* K} (hσ : ∀ c, σ c = σ' c) :
    (ovlSU σ' p).range = unitarySL σ ⊓ LinearPilot.blockSpecialLinear (ovlSet p) := by
  have hmap : ∀ B : Matrix (Fin 4) (Fin 4) K, B.map σ = B.map σ' := fun B => by
    ext i j
    exact hσ _
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    refine ⟨(ovlEmbed_mem_unitarySL_iff p _).2 ?_, ?_⟩
    · obtain ⟨-, hiso⟩ := A.2
      change ((((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map σ)ᵀ * antidiag 4 *
        ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = antidiag 4
      rw [hmap]
      exact hiso
    · rw [← range_ovlEmbed p]
      exact ⟨_, rfl⟩
  · rintro M ⟨hMu, hMb⟩
    rw [← range_ovlEmbed p] at hMb
    obtain ⟨B, rfl⟩ := hMb
    have hiso := (ovlEmbed_mem_unitarySL_iff p B).1 hMu
    rw [hmap] at hiso
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL B, B.2, hiso⟩, ?_⟩
    change ovlEmbed p (suToSL4 σ' _) = ovlEmbed p B
    congr 1

end SU

section Simple

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_SU_four_eq_bot_ovl (hK : Nat.card K = (2 ^ 1) ^ 2) :
    center (SU (unitaryInvolution K 2 1) 4) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (exists_wittMatrix hK 4).choose with hP
  set e := (conjEquiv P (exists_wittMatrix hK 4).choose_spec).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)) with he
  have hZ := (isQuasisimple_statedSU_of_card hK (n := 4) (by norm_num) (by decide)).2
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ center (StatedSU 4 (2 ^ 1) K) := by
    rw [← map_center_mulEquiv e]
    exact ⟨z, hz, rfl⟩
  have hcoe : ((e z : StatedSU 4 (2 ^ 1) K) : GL (Fin 4) K) =
      P * (z : GL (Fin 4) K) * P⁻¹ := rfl
  rw [hZ, Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar, hcoe, conj_mem_center_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hez
  obtain ⟨u, hu⟩ := hez
  obtain ⟨hdet, hiso⟩ := z.2
  have hzm : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) (u : K) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hzm, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have h3 : (u : K) ^ 2 * (u : K) = 1 := by
    have h1 := congrFun (congrFun hiso 0) 3
    rw [hzm] at h1
    simp only [conjTr, Matrix.scalar_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.diagonal_apply, antidiag, Matrix.of_apply] at h1
    simpa [Fin.sum_univ_four, unitaryInvolution_apply, Fin.rev, frobenius_def] using h1
  have hu1 : (u : K) = 1 := by
    calc (u : K) = (u : K) ^ 4 * ((u : K) ^ 2 * (u : K))⁻¹ := by
          field_simp [u.ne_zero]
      _ = 1 := by rw [hdet, h3, inv_one, one_mul]
  rw [mem_bot]
  apply Subtype.ext
  apply Units.ext
  rw [hzm, hu1, Matrix.scalar_apply, Matrix.diagonal_one]
  rfl

theorem isSimpleGroup_SU_four_ovl (hK : Nat.card K = (2 ^ 1) ^ 2) :
    IsSimpleGroup (SU (unitaryInvolution K 2 1) 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hs, -⟩ := isQuasisimple_SU hK (n := 4) (by norm_num) (by decide)
  have e : SU (unitaryInvolution K 2 1) 4 ≃*
      SU (unitaryInvolution K 2 1) 4 ⧸ center (SU (unitaryInvolution K 2 1) 4) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_SU_four_eq_bot_ovl hK).symm))
  exact e.isSimpleGroup

theorem isPerfect_SU_four_ovl (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Group.IsPerfect (SU (unitaryInvolution K 2 1) 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isQuasisimple_SU hK (n := 4) (by norm_num) (by decide)).1

end Simple

section Lift

variable {K : Type} [Field K]

theorem transvection_rev_mem_unitarySL_ovl {σ : K →+* K} (h2 : (2 : K) = 0) {a b : Fin 6}
    (hab : a ≠ b) (hb : b = Fin.rev a) {c : K} (hc : σ c = c) :
    SpecialLinearGroup.transvection hab c ∈ unitarySL σ := by
  subst hb
  rw [mem_unitarySL_iff_unitaryTwist]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (SpecialLinearGroup.transvection hab c)) = _
  rw [map_transvection, hc, graphSL_transvection h2]
  apply Subtype.ext
  simp only [SpecialLinearGroup.transvection_coe, Fin.rev_rev]

theorem transvection_mul_rev_mem_unitarySL_ovl {σ : K →+* K} (h2 : (2 : K) = 0)
    (hσσ : ∀ c, σ (σ c) = c) {a b : Fin 6} (hab : a ≠ b) (s : K) :
    SpecialLinearGroup.transvection hab s *
        SpecialLinearGroup.transvection (fun h => hab (Fin.rev_injective h).symm) (σ s) ∈
      unitarySL σ := by
  rw [mem_unitarySL_iff_unitaryTwist]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (SpecialLinearGroup.transvection hab s *
    SpecialLinearGroup.transvection (fun h => hab (Fin.rev_injective h).symm) (σ s))) = _
  rw [map_mul, map_mul, map_transvection, map_transvection, hσσ, graphSL_transvection h2,
    graphSL_transvection h2]
  have hb : b ≠ Fin.rev b := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  have ha : Fin.rev a ≠ a := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  have e : SpecialLinearGroup.transvection
      (fun h => (fun h => hab (Fin.rev_injective h).symm) (Fin.rev_injective h).symm) s =
      SpecialLinearGroup.transvection hab s := by
    congr 1 <;> simp
  rw [e]
  exact (Matrix.SpecialLinearGroup.commute_transvection _ _ hb ha s (σ s)).eq.symm

theorem ker_realize_le_center_ovl (h2 : (2 : K) = 0) :
    (realize h2).ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
  intro B hB
  obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 B).1 hB
  exact Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨l, by
    rw [Fintype.card_fin, show (6 : ℕ) = 3 * 2 by rfl, pow_mul, hl3, one_pow], hl.symm⟩

theorem realize_ovlEmbed_injective (h2 : (2 : K) = 0) (p : Fin 3) :
    Function.Injective ((realize h2).comp (ovlEmbed (K := K) p)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hk : ovlEmbed p A ∈ (realize h2).ker := hA
  obtain ⟨l, -, hl⟩ := (mem_ker_realize h2 _).1 hk
  have h1 := congrFun (congrFun hl (ovlPt p)) (ovlPt p)
  rw [ovlEmbed_apply, ite_eq_right (fun h => (ovl_check p).2.2.2.2.2.1 h.1),
    Matrix.one_apply_eq, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  apply ovlEmbed_injective p
  rw [map_one]
  apply Subtype.ext
  rw [hl, ← h1, Matrix.SpecialLinearGroup.coe_one]
  exact map_one _

theorem le_centralizer_comap_of_perfect_ovl {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hker : f.ker ≤ center G) {Q : Subgroup G} (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ centralizer (((centralizer ((Q.map f : Subgroup H) : Set H)).comap f : Subgroup G) :
      Set G) := by
  refine LinearPilot.le_centralizer_of_commutator_le_center_of_perfect hQ ?_
  rw [Subgroup.commutator_le]
  intro q hq j hj
  apply hker
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mem_centralizer_iff.1 hj (f q) ⟨q, hq, rfl⟩

end Lift

set_option maxRecDepth 100000 in
theorem perp_roots_check_ovl : ∀ p : Fin 3, ∀ β ∈ rootFinset TwistTag.E6.tag,
    CFSG.LieType.Steinberg.Adjoint.iform e6HighestRoot β = 0 →
    CFSG.LieType.Steinberg.Adjoint.iform (matRoot (ovlPt p) (Fin.rev (ovlPt p))) β = 0 →
      ∃ a b : Fin 6, a ≠ b ∧ a ∈ ovlSet p ∧ b ∈ ovlSet p ∧ matRoot a b = β := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rho_matRoot_check_ovl : ∀ a b : Fin 6,
    permLattice TwistTag.E6.perm (matRoot a b) = matRoot (Fin.rev b) (Fin.rev a) ∧
      (a ≠ b → (matRoot (Fin.rev b) (Fin.rev a) = matRoot a b ↔ b = Fin.rev a)) := by
  decide +kernel

end CFSG.SeitzReduction.TwistedE6Pilot
