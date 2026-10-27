module

public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.OddTranspositions.O4PairTenGenerate
public import CFSG.OddTranspositions.O4PairTenGraph

public section

noncomputable section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

@[expose] def leftY (i : Fin 10) : FixK :=
  ⟨(y i).left, by
    have hx : psl2FieldAut K25 frob25 ((y i).left) = (y i).left := by
      rw [left_y i, ← pslEquiv_aut_apply]
      exact congrArg pslEquiv (x_fixed i)
    exact hx.symm⟩

theorem leftY_val (i : Fin 10) : ((leftY i : FixK) : PSL2 K25) = pslEquiv (x i) :=
  left_y i

theorem leftY_injective : Function.Injective leftY := by
  intro i j hij
  have hx : pslEquiv (x i) = pslEquiv (x j) := by
    rw [← leftY_val i, ← leftY_val j]
    exact congrArg Subtype.val hij
  exact x_injective (pslEquiv.injective hx)

theorem y_right (i : Fin 10) : (y i).right = frob25 := by
  rw [y, SemidirectProduct.mk_eq_inl_mul_inr, map_mul, psigmaL2Equiv_inl, psigmaL2Equiv_inr,
    ringAutConjMulEquiv_frob25t]
  simp [SemidirectProduct.mul_right]

theorem y_eq_mk (i : Fin 10) : y i = SemidirectProduct.mk ((y i).left) frob25 := by
  rw [← y_right i, SemidirectProduct.mk_eq_inl_mul_inr,
    SemidirectProduct.inl_left_mul_inr_right]

theorem y_eq_mk_left (i : Fin 10) :
    y i = SemidirectProduct.mk ((leftY i : FixK) : PSL2 K25) frob25 := by
  rw [y_eq_mk i]
  rfl

theorem commute_mk_frob25_iff {p q : PSL2 K25}
    (hp : psl2FieldAut K25 frob25 p = p) (hq : psl2FieldAut K25 frob25 q = q) :
    Commute (SemidirectProduct.mk p frob25 : PSigmaL225)
      (SemidirectProduct.mk q frob25) ↔ Commute p q := by
  have hmul : (SemidirectProduct.mk p frob25 : PSigmaL225) *
        SemidirectProduct.mk q frob25 = SemidirectProduct.mk (p * q) 1 := by
    ext <;> simp [hq, frob25_mul_self]
  have hmul' : (SemidirectProduct.mk q frob25 : PSigmaL225) *
        SemidirectProduct.mk p frob25 = SemidirectProduct.mk (q * p) 1 := by
    ext <;> simp [hp, frob25_mul_self]
  rw [commute_iff_eq, commute_iff_eq, hmul, hmul']
  constructor
  · intro h
    exact congrArg SemidirectProduct.left h
  · intro h
    rw [h]

theorem commute_leftY_iff_y (i j : Fin 10) :
    Commute (leftY i) (leftY j) ↔ Commute (y i) (y j) := by
  have hsub : Commute (leftY i) (leftY j) ↔
      Commute ((leftY i : FixK) : PSL2 K25) ((leftY j : FixK) : PSL2 K25) := by
    constructor
    · intro h
      exact congrArg (fun x : FixK => (x : PSL2 K25)) h
    · intro h
      exact Subtype.ext h
  rw [hsub, ← commute_mk_frob25_iff (leftY i).2.symm (leftY j).2.symm,
    y_eq_mk_left i, y_eq_mk_left j]

@[expose] def pairOf : Fin 10 → Finset (Fin 5)
  | 0 => {0, 1}
  | 1 => {2, 3}
  | 2 => {2, 4}
  | 3 => {0, 4}
  | 4 => {1, 4}
  | 5 => {3, 4}
  | 6 => {0, 3}
  | 7 => {1, 3}
  | 8 => {0, 2}
  | 9 => {1, 2}

@[expose] def star (p : Fin 5) : Finset (Fin 10) :=
  match p with
  | 0 => {0, 3, 6, 8}
  | 1 => {0, 4, 7, 9}
  | 2 => {1, 2, 8, 9}
  | 3 => {1, 5, 6, 7}
  | 4 => {2, 3, 4, 5}

theorem mem_star_iff (p : Fin 5) (i : Fin 10) : i ∈ star p ↔ p ∈ pairOf i := by
  revert p i
  decide +kernel

theorem star_card (p : Fin 5) : (star p).card = 4 := by
  fin_cases p <;> decide +kernel

theorem star_unique_common :
    (∀ p q : Fin 5, p ≠ q → (star p ∩ star q).card = 1) ∧
      (∀ i : Fin 10, (Finset.univ.filter (fun p : Fin 5 => i ∈ star p)).card = 2) := by
  decide +kernel

private def indexOfPair (s : Finset (Fin 5)) : Fin 10 :=
  if s = {0, 1} then 0
  else if s = {2, 3} then 1
  else if s = {2, 4} then 2
  else if s = {0, 4} then 3
  else if s = {1, 4} then 4
  else if s = {3, 4} then 5
  else if s = {0, 3} then 6
  else if s = {1, 3} then 7
  else if s = {0, 2} then 8
  else if s = {1, 2} then 9
  else 0

private def conjPair (t s : Finset (Fin 5)) : Finset (Fin 5) :=
  if s = t ∨ Disjoint s t then s else (t \ s) ∪ (s \ t)

private def conjIndexBy (i j : Fin 10) : Fin 10 :=
  indexOfPair (conjPair (pairOf i) (pairOf j))

@[expose] def starSwap : Fin 10 → Equiv.Perm (Fin 5)
  | 0 => Equiv.swap 0 1
  | 1 => Equiv.swap 2 3
  | 2 => Equiv.swap 2 4
  | 3 => Equiv.swap 0 4
  | 4 => Equiv.swap 1 4
  | 5 => Equiv.swap 3 4
  | 6 => Equiv.swap 0 3
  | 7 => Equiv.swap 1 3
  | 8 => Equiv.swap 0 2
  | 9 => Equiv.swap 1 2

private theorem commX_iff_pair (i j : Fin 10) :
    (X i * X j = X j * X i ∨ X i * X j = -(X j * X i)) ↔
      i = j ∨ Disjoint (pairOf i) (pairOf j) := by
  revert i j
  decide +kernel

theorem commute_leftY_iff_pair (i j : Fin 10) :
    Commute (leftY i) (leftY j) ↔ i = j ∨ Disjoint (pairOf i) (pairOf j) := by
  rw [commute_leftY_iff_y, commY_iff, commute_x_iff]
  exact commX_iff_pair i j

theorem pairwise_not_commute_star (p : Fin 5) :
    ∀ i ∈ star p, ∀ j ∈ star p, i ≠ j → ¬ Commute (leftY i) (leftY j) := by
  intro i hi j hj hij hc
  have hpi : p ∈ pairOf i := (mem_star_iff p i).mp hi
  have hpj : p ∈ pairOf j := (mem_star_iff p j).mp hj
  have hdisj : Disjoint (pairOf i) (pairOf j) :=
    ((commute_leftY_iff_pair i j).mp hc).resolve_left hij
  have hp : p ∈ pairOf i ∩ pairOf j := by
    rw [Finset.mem_inter]
    exact ⟨hpi, hpj⟩
  exact (Finset.not_disjoint_iff_nonempty_inter.mpr ⟨p, hp⟩) hdisj

private theorem star_maximal_check (S : Finset (Fin 10)) (hcard : S.card = 4)
    (hpw : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ Disjoint (pairOf i) (pairOf j)) :
    S = star 0 ∨ S = star 1 ∨ S = star 2 ∨ S = star 3 ∨ S = star 4 := by
  revert S
  decide +kernel

theorem eq_star_of_pairwise_not_commute (S : Finset (Fin 10)) (hcard : S.card = 4)
    (hpw : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ Commute (leftY i) (leftY j)) :
    S = star 0 ∨ S = star 1 ∨ S = star 2 ∨ S = star 3 ∨ S = star 4 := by
  refine star_maximal_check S hcard ?_
  intro i hi j hj hij hdisj
  exact hpw i hi j hj hij ((commute_leftY_iff_pair i j).mpr (Or.inr hdisj))

theorem star_injective : Function.Injective star := by
  intro p q hpq
  by_contra hne
  have h1 := star_unique_common.1 p q hne
  rw [hpq, Finset.inter_self, star_card] at h1
  omega

private instance instDecidablePredIsSwapQZ :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ.IsSwap) :=
  fun σ => decidable_of_iff (∃ x y : Fin 5, x ≠ y ∧ σ = Equiv.swap x y) Iff.rfl

theorem range_starSwap : Set.range starSwap = CFSG.GroupTheory.transpositions := by
  change Set.range starSwap = {τ : Equiv.Perm (Fin 5) | τ.IsSwap}
  ext τ
  revert τ
  decide +kernel

theorem closure_transpositions :
    Subgroup.closure (CFSG.GroupTheory.transpositions : Set (Equiv.Perm (Fin 5))) = ⊤ :=
  Equiv.Perm.closure_isSwap

private theorem left_inl_conj (k : PSL2 K25) (x : PSigmaL225) :
    (SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹).left =
      k * x.left * ((psl2FieldAut K25) x.right k)⁻¹ := by
  rw [← map_inv]
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, mul_assoc]

theorem conj_left_y_mem_range (k : FixK) (i : Fin 10) :
    ∃ j : Fin 10, k * leftY i * k⁻¹ = leftY j := by
  classical
  let g : PSigmaL225 := SemidirectProduct.inl (k : PSL2 K25)
  have hk : psl2FieldAut K25 frob25 ((k : FixK) : PSL2 K25) = (k : FixK) := k.2.symm
  have hyv : (y i).left = ((leftY i : FixK) : PSL2 K25) := by
    rw [left_y i, leftY_val i]
  have hg_comm_base : Commute g (SemidirectProduct.inr frob25 : PSigmaL225) := by
    show g * SemidirectProduct.inr frob25 = SemidirectProduct.inr frob25 * g
    apply SemidirectProduct.ext
    · change (k : PSL2 K25) * psl2FieldAut K25 (1 : K25 ≃+* K25) 1 =
        1 * psl2FieldAut K25 frob25 ((k : FixK) : PSL2 K25)
      simp [hk]
    · simp [g]
  have hmem : g * y i * g⁻¹ ∈ class65 := by
    have hy := y_mem_class65 i
    rw [mem_class65_iff] at hy ⊢
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    refine isConj_iff.mpr ⟨g * c, ?_⟩
    calc
      (g * c) * SemidirectProduct.inr frob25 * (g * c)⁻¹ =
          g * (c * SemidirectProduct.inr frob25 * c⁻¹) * g⁻¹ := by group
      _ = g * y i * g⁻¹ := by rw [hc]
  have hcomm : Commute (g * y i * g⁻¹) (SemidirectProduct.inr frob25) := by
    have h := (y_commute_base i).conj g
    have hgb : g * SemidirectProduct.inr frob25 * g⁻¹ =
        (SemidirectProduct.inr frob25 : PSigmaL225) := by
      rw [hg_comm_base.eq, mul_assoc, mul_inv_cancel, mul_one]
    rwa [hgb] at h
  have hmem_insert : g * y i * g⁻¹ ∈
      insert (SemidirectProduct.inr frob25) (Set.range y) := by
    rw [← commuting_class65_eq]
    exact ⟨hmem, hcomm⟩
  have hleft_calc : (g * y i * g⁻¹).left =
      (k : PSL2 K25) * ((leftY i : FixK) : PSL2 K25) * ((k : PSL2 K25))⁻¹ := by
    rw [show g * y i * g⁻¹ = SemidirectProduct.inl (k : PSL2 K25) * y i *
        (SemidirectProduct.inl (k : PSL2 K25))⁻¹ from rfl]
    rw [left_inl_conj, y_right, hyv, hk]
  rcases Set.mem_insert_iff.mp hmem_insert with hbase | hrange
  · exfalso
    have hleft : (k : PSL2 K25) * ((leftY i : FixK) : PSL2 K25) *
        ((k : PSL2 K25))⁻¹ = 1 := by
      have h := congrArg SemidirectProduct.left hbase
      rw [hleft_calc] at h
      simpa using h
    have hleftY1 : leftY i = 1 := by
      apply Subtype.ext
      have hcalc : ((leftY i : FixK) : PSL2 K25) =
          (k : PSL2 K25)⁻¹ * ((k : PSL2 K25) * ((leftY i : FixK) : PSL2 K25) *
            ((k : PSL2 K25))⁻¹) * (k : PSL2 K25) := by
        group
      rw [hcalc, hleft]
      simp
    obtain ⟨p, hip⟩ : ∃ p : Fin 5, i ∈ star p := by
      have hcard := star_unique_common.2 i
      have hpos : 0 < (Finset.univ.filter (fun p : Fin 5 => i ∈ star p)).card := by
        omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      exact ⟨p, (Finset.mem_filter.mp hp).2⟩
    obtain ⟨j, hjp, hji⟩ := Finset.exists_mem_ne (by rw [star_card p]; norm_num) i
    have hnc := pairwise_not_commute_star p i hip j hjp hji.symm
    rw [hleftY1] at hnc
    exact hnc (Commute.one_left (leftY j))
  · obtain ⟨j, hj⟩ := hrange
    refine ⟨j, Subtype.ext ?_⟩
    have hleft := congrArg SemidirectProduct.left hj
    rw [hleft_calc] at hleft
    change (k : PSL2 K25) * ((leftY i : FixK) : PSL2 K25) * ((k : PSL2 K25))⁻¹ =
      (y j).left
    exact hleft.symm

noncomputable def conjIndex (k : FixK) (i : Fin 10) : Fin 10 :=
  Classical.choose (conj_left_y_mem_range k i)

private theorem conjIndex_spec (k : FixK) (i : Fin 10) :
    k * leftY i * k⁻¹ = leftY (conjIndex k i) :=
  Classical.choose_spec (conj_left_y_mem_range k i)

private theorem conjIndex_mul (k l : FixK) (i : Fin 10) :
    conjIndex (k * l) i = conjIndex k (conjIndex l i) := by
  apply leftY_injective
  rw [← conjIndex_spec (k * l) i, ← conjIndex_spec k (conjIndex l i),
    ← conjIndex_spec l i]
  group

private theorem conjIndex_one (i : Fin 10) : conjIndex 1 i = i := by
  apply leftY_injective
  rw [← conjIndex_spec 1 i]
  simp

private theorem conjIndex_inv_left (k : FixK) (i : Fin 10) :
    conjIndex k⁻¹ (conjIndex k i) = i := by
  have h := conjIndex_mul k⁻¹ k i
  rw [inv_mul_cancel, conjIndex_one] at h
  exact h.symm

private theorem conjIndex_injective (k : FixK) : Function.Injective (conjIndex k) := by
  intro i j hij
  have h := congrArg (conjIndex k⁻¹) hij
  rwa [conjIndex_inv_left, conjIndex_inv_left] at h

private theorem X_conj_spec (i j : Fin 10) :
    X (conjIndexBy i j) = X i * X j * (X i)⁻¹ ∨
      X (conjIndexBy i j) = -(X i * X j * (X i)⁻¹) := by
  revert i j
  decide +kernel

private theorem leftY_conj_eq (i j : Fin 10) :
    leftY i * leftY j * (leftY i)⁻¹ = leftY (conjIndexBy i j) := by
  apply Subtype.ext
  change ((leftY i : FixK) : PSL2 K25) * ((leftY j : FixK) : PSL2 K25) *
      (((leftY i : FixK) : PSL2 K25))⁻¹ =
    ((leftY (conjIndexBy i j) : FixK) : PSL2 K25)
  rw [leftY_val i, leftY_val j, leftY_val (conjIndexBy i j)]
  rw [← pslEquiv.map_mul, ← pslEquiv.map_inv, ← pslEquiv.map_mul]
  rw [pslEquiv.apply_eq_iff_eq]
  change CFSG.PSL2Table.mk (X i) * CFSG.PSL2Table.mk (X j) *
      (CFSG.PSL2Table.mk (X i))⁻¹ = CFSG.PSL2Table.mk (X (conjIndexBy i j))
  rw [← map_mul, ← map_inv, ← map_mul]
  exact (CFSG.PSL2Table.mk_eq_mk_iff _ _).mpr (X_conj_spec i j)

private theorem conjIndex_leftY (i j : Fin 10) :
    conjIndex (leftY i) j = conjIndexBy i j := by
  apply leftY_injective
  rw [← conjIndex_spec (leftY i) j]
  exact leftY_conj_eq i j

private theorem image_star_exists (k : FixK) (p : Fin 5) :
    ∃ q : Fin 5, (star p).image (conjIndex k) = star q := by
  have hcard : ((star p).image (conjIndex k)).card = 4 := by
    rw [Finset.card_image_of_injOn (conjIndex_injective k).injOn, star_card p]
  have hpw : ∀ i ∈ (star p).image (conjIndex k),
      ∀ j ∈ (star p).image (conjIndex k), i ≠ j → ¬ Commute (leftY i) (leftY j) := by
    intro i hi j hj hij
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    have hab : a ≠ b := fun h => hij (by rw [h])
    have hnc := pairwise_not_commute_star p a ha b hb hab
    have hconj : Commute (leftY (conjIndex k a)) (leftY (conjIndex k b)) ↔
        Commute (leftY a) (leftY b) := by
      rw [← conjIndex_spec k a, ← conjIndex_spec k b]
      exact Commute.conj_iff k
    intro hc
    exact hnc (hconj.mp hc)
  rcases eq_star_of_pairwise_not_commute ((star p).image (conjIndex k)) hcard hpw with
    h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩

private noncomputable def starIndex (k : FixK) (p : Fin 5) : Fin 5 :=
  Classical.choose (image_star_exists k p)

private theorem starIndex_spec (k : FixK) (p : Fin 5) :
    (star p).image (conjIndex k) = star (starIndex k p) :=
  Classical.choose_spec (image_star_exists k p)

private theorem starIndex_one (p : Fin 5) : starIndex 1 p = p := by
  apply star_injective
  rw [← starIndex_spec 1 p]
  have hid : conjIndex (1 : FixK) = id := funext conjIndex_one
  rw [hid, Finset.image_id]

private theorem starIndex_mul (k l : FixK) (p : Fin 5) :
    starIndex (k * l) p = starIndex k (starIndex l p) := by
  apply star_injective
  rw [← starIndex_spec (k * l) p, ← starIndex_spec k (starIndex l p),
    ← starIndex_spec l p, Finset.image_image]
  rw [show conjIndex (k * l) = conjIndex k ∘ conjIndex l from
    funext (conjIndex_mul k l)]

private theorem starIndex_inv_left (k : FixK) (p : Fin 5) :
    starIndex k⁻¹ (starIndex k p) = p := by
  have h := starIndex_mul k⁻¹ k p
  rw [inv_mul_cancel, starIndex_one] at h
  exact h.symm

private theorem starIndex_inv_right (k : FixK) (p : Fin 5) :
    starIndex k (starIndex k⁻¹ p) = p := by
  have h := starIndex_mul k k⁻¹ p
  rw [mul_inv_cancel, starIndex_one] at h
  exact h.symm

private theorem starIndex_injective (k : FixK) : Function.Injective (starIndex k) := by
  intro p q hpq
  have h := congrArg (starIndex k⁻¹) hpq
  rwa [starIndex_inv_left, starIndex_inv_left] at h

private theorem starIndex_surjective (k : FixK) : Function.Surjective (starIndex k) := by
  intro q
  exact ⟨starIndex k⁻¹ q, starIndex_inv_right k q⟩

private theorem starIndex_bijective (k : FixK) : Function.Bijective (starIndex k) :=
  ⟨starIndex_injective k, starIndex_surjective k⟩

private noncomputable def actFixKFun (k : FixK) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (starIndex k) (starIndex_bijective k)

noncomputable def actFixK : FixK →* Equiv.Perm (Fin 5) where
  toFun := actFixKFun
  map_one' := by
    ext p
    simp [actFixKFun, starIndex_one]
  map_mul' k l := by
    ext p
    simp [actFixKFun, starIndex_mul]

@[simp] private theorem actFixK_apply (k : FixK) (p : Fin 5) :
    actFixK k p = starIndex k p := rfl

private theorem star_image_conjIndexBy (i : Fin 10) (p : Fin 5) :
    (star p).image (conjIndexBy i) = star (starSwap i p) := by
  revert i p
  decide +kernel

private theorem actFixK_left_y_apply (i : Fin 10) (p : Fin 5) :
    actFixK (leftY i) p = starSwap i p := by
  have h1 : (star p).image (conjIndex (leftY i)) = star (actFixK (leftY i) p) := by
    simpa [actFixK_apply] using starIndex_spec (leftY i) p
  have hfun : conjIndex (leftY i) = conjIndexBy i := funext (conjIndex_leftY i)
  rw [hfun] at h1
  rw [star_image_conjIndexBy] at h1
  exact (star_injective h1).symm

theorem actFixK_left_y (i : Fin 10) :
    actFixK (leftY i) = starSwap i := by
  apply Equiv.ext
  intro p
  exact actFixK_left_y_apply i p

theorem actFixK_surjective : Function.Surjective actFixK := by
  have hsubset : CFSG.GroupTheory.transpositions ⊆ Set.range actFixK := by
    intro τ hτ
    rw [← range_starSwap] at hτ
    obtain ⟨i, rfl⟩ := hτ
    exact ⟨leftY i, actFixK_left_y i⟩
  have hclosure : Subgroup.closure (CFSG.GroupTheory.transpositions : Set (Equiv.Perm (Fin 5))) ≤
      actFixK.range := by
    rw [Subgroup.closure_le]
    intro τ hτ
    exact hsubset hτ
  rw [closure_transpositions] at hclosure
  exact MonoidHom.range_eq_top.mp (eq_top_iff.mpr hclosure)

theorem fixK_equiv_s5 :
    ∃ e : FixK ≃* Equiv.Perm (Fin 5),
      e '' Set.range leftY = CFSG.GroupTheory.transpositions := by
  haveI : Finite FixK :=
    Finite.of_injective (fun x : FixK => (x : PSL2 K25)) Subtype.coe_injective
  have hcard : Nat.card FixK = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [card_FixK, Nat.card_perm, Nat.card_fin]
    norm_num
  have hbij : Function.Bijective actFixK :=
    actFixK_surjective.bijective_of_nat_card_le (le_of_eq hcard)
  refine ⟨MulEquiv.ofBijective actFixK hbij, ?_⟩
  have himg : (MulEquiv.ofBijective actFixK hbij : FixK → Equiv.Perm (Fin 5)) ''
      Set.range leftY = Set.range starSwap := by
    change (actFixK : FixK → Equiv.Perm (Fin 5)) '' Set.range leftY = Set.range starSwap
    rw [← Set.range_comp]
    congr 1
    funext i
    exact actFixK_left_y i
  rw [himg, range_starSwap]

theorem not_isSolvable_FixK : ¬ Group.IsSolvable FixK := by
  intro hsol
  haveI : Group.IsSolvable FixK := hsol
  obtain ⟨e, -⟩ := fixK_equiv_s5
  exact Equiv.Perm.not_isSolvable_fin_5
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.OddTranspositions.QZ
