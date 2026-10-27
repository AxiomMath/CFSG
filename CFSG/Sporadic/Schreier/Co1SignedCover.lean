module

public import CFSG.Sporadic.Schreier.Co1SignedMono
public import CFSG.Sporadic.Schreier.Co1ElemThreeSigned
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public import Certificates.Certificate2146
public import Certificates.Certificate3086
public import Certificates.Certificate16017

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem isMono_σ : ∀ i, IsMono (σMat i) ∧ IsMono (σInvMat i) := by decide +kernel

theorem isMono_neg_one : IsMono (-1 : Mat12) ∧ ∀ j, lineMap (-1 : Mat12) j = j := by
  decide +kernel

theorem σ_rows_mem : ∀ i k, R *ᵥ (σMat i *ᵥ R k) = 0 ∧ R *ᵥ (σInvMat i *ᵥ R k) = 0 := by
  decide +kernel

theorem neg_rows_mem : ∀ k, R *ᵥ ((-1 : Mat12) *ᵥ R k) = 0 := by decide +kernel

@[expose] noncomputable def coordBij : Equiv.Perm (Fin 12) :=
  Equiv.ofBijective (fun c => Fin.ofNat 12 (Data.coordBij.getD c.val 0)) (by decide +kernel)

theorem coordBij_apply : ∀ c : Fin 12,
    (coordBij c : ℕ) = [0, 1, 2, 3, 4, 7, 11, 6, 5, 10, 9, 8].getD c.val 0 := by
  decide +kernel

theorem lineMap_σ_coordBij : ∀ c : Fin 12, lineMap (σMat 0) (coordBij c) = coordBij (m12gA c) ∧
    lineMap (σMat 1) (coordBij c) = coordBij (m12gB c) := by
  decide +kernel

theorem m12_not_comm : m12gA * m12gB ≠ m12gB * m12gA := by decide +kernel

theorem diagonal_neg_one : Matrix.diagonal (-1 : Fin 12 → ZMod 3) = -1 := by decide +kernel

theorem sign_check : ∀ b : Fin 6 → ZMod 3, (∀ j, (b ᵥ* R) j ≠ 0) →
    (∀ k, R *ᵥ ((b ᵥ* R) * R k) = 0) → b ᵥ* R = 1 ∨ b ᵥ* R = -1 :=
  Certificates.certificate2146

@[expose] def letterIdx (l : ℕ) : Fin 2 := if l = 1 then 0 else 1

@[expose] noncomputable def nsWord : GL12 := (Data.nonsplitWord.map fun l => σ (letterIdx l)).prod

theorem signedMatrix_mul (p q : Fin 12 → Fin 12) (ε δ : Fin 12 → ZMod 3) :
    signedMatrix p ε * signedMatrix q δ = signedMatrix (p ∘ q) fun j => ε (q j) * δ j := by
  ext i j
  simp only [Matrix.mul_apply, signedMatrix, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (q j)]
  · simp only [↓reduceIte]
    split_ifs <;> simp
  · intro k _ hk
    simp [hk]
  · simp

@[expose] def signedProd : List ℕ → (Fin 12 → Fin 12) × (Fin 12 → ZMod 3)
  | [] => (id, fun _ => 1)
  | l :: ls => (liftPerm (letterIdx l) ∘ (signedProd ls).1,
      fun j => liftSign (letterIdx l) ((signedProd ls).1 j) * (signedProd ls).2 j)

theorem signedMatrix_id_one : signedMatrix id (fun _ => 1) = 1 := by
  ext i j
  simp [signedMatrix, Matrix.one_apply]

theorem word_prod_eq (w : List ℕ) : (w.map fun l => σMat (letterIdx l)).prod =
    signedMatrix (signedProd w).1 (signedProd w).2 := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, signedProd, signedMatrix_id_one]
  | cons l ls ih =>
    rw [List.map_cons, List.prod_cons, ih, signedProd, σMat, signedMatrix_mul]

theorem nsWord_sq_check : signedMatrix ((signedProd Data.nonsplitWord).1 ∘
    (signedProd Data.nonsplitWord).1) (fun j => (signedProd Data.nonsplitWord).2
      ((signedProd Data.nonsplitWord).1 j) * (signedProd Data.nonsplitWord).2 j) = -1 := by
  decide +kernel

theorem Q_induction (P : GL12 → Prop) (h1 : P 1) (hmul : ∀ x y, P x → P y → P (x * y))
    (hσ : ∀ i, P (σ i)) (hσinv : ∀ i, P (σ i)⁻¹) (hneg : P (-1)) : ∀ g ∈ Q, P g := by
  intro g hg
  replace hg : g ∈ Submonoid.closure
      (({σ 0, σ 1, -1} : Set GL12) ∪ ({σ 0, σ 1, -1} : Set GL12)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hσ 0, hσ 1, hneg]
    · rw [Set.mem_inv] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · rw [← inv_inv x, h]; exact hσinv 0
      · rw [← inv_inv x, h]; exact hσinv 1
      · rw [← inv_inv x, h, inv_neg_one]; exact hneg
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem σ_val (i : Fin 2) : ((σ i : GL12) : Mat12) = σMat i := rfl

theorem σ_inv_val (i : Fin 2) : (((σ i)⁻¹ : GL12) : Mat12) = σInvMat i := rfl

theorem neg_one_val : ((-1 : GL12) : Mat12) = -1 := rfl

theorem Q_isMono : ∀ g ∈ Q, IsMono (g : Mat12) := by
  apply Q_induction
  · rw [Units.val_one]; exact isMono_one.1
  · intro x y hx hy
    rw [Units.val_mul]
    exact (hx.mul hy).1
  · intro i; rw [σ_val]; exact (isMono_σ i).1
  · intro i; rw [σ_inv_val]; exact (isMono_σ i).2
  · rw [neg_one_val]; exact isMono_neg_one.1

theorem mulVec_mem_T {M : Mat12} (h : ∀ k, R *ᵥ (M *ᵥ R k) = 0) :
    ∀ v ∈ T, M *ᵥ v ∈ T := by
  intro v hv
  unfold T at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact (mem_T_iff_mulVec _).mpr (h k)
  | zero => rw [mulVec_zero]; exact T.zero_mem
  | add x y _ _ hx hy => rw [mulVec_add]; exact T.add_mem hx hy
  | smul c x _ hx => rw [mulVec_smul]; exact T.smul_mem c hx

theorem Q_preserves_T : ∀ g ∈ Q, ∀ v ∈ T, (g : Mat12) *ᵥ v ∈ T := by
  apply Q_induction (fun g => ∀ v ∈ T, (g : Mat12) *ᵥ v ∈ T)
  · intro v hv; rwa [Units.val_one, one_mulVec]
  · intro x y hx hy v hv
    rw [Units.val_mul, ← mulVec_mulVec]
    exact hx _ (hy v hv)
  · intro i; rw [σ_val]; exact mulVec_mem_T fun k => (σ_rows_mem i k).1
  · intro i; rw [σ_inv_val]; exact mulVec_mem_T fun k => (σ_rows_mem i k).2
  · rw [neg_one_val]; exact mulVec_mem_T neg_rows_mem

@[expose] def qPerm : Q →* Equiv.Perm (Fin 12) := monoPerm Q Q_isMono

theorem qPerm_apply (g : Q) (j : Fin 12) : qPerm g j = lineMap ((g : GL12) : Mat12) j := rfl

theorem qPerm_pattern (g : Q) (i j : Fin 12) :
    ((g : GL12) : Mat12) i j ≠ 0 ↔ i = qPerm g j :=
  Q_isMono g g.2 j i

theorem σ_mem_Q (i : Fin 2) : σ i ∈ Q := by
  apply Subgroup.subset_closure
  fin_cases i
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem neg_one_mem_Q : (-1 : GL12) ∈ Q :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem qPerm_neg_one : qPerm ⟨-1, neg_one_mem_Q⟩ = 1 := by
  refine Equiv.ext fun j => ?_
  change lineMap ((-1 : GL12) : Mat12) j = j
  rw [neg_one_val]
  exact isMono_neg_one.2 j

theorem qPerm_σ0 : qPerm ⟨σ 0, σ_mem_Q 0⟩ = MulAut.conj coordBij m12gA := by
  refine Equiv.ext fun j => ?_
  have h : coordBij (coordBij⁻¹ j) = j := Equiv.apply_symm_apply coordBij j
  rw [MulAut.conj_apply, Equiv.Perm.mul_apply (coordBij * m12gA),
    Equiv.Perm.mul_apply coordBij m12gA]
  conv_lhs => rw [← h]
  exact (lineMap_σ_coordBij _).1

theorem qPerm_σ1 : qPerm ⟨σ 1, σ_mem_Q 1⟩ = MulAut.conj coordBij m12gB := by
  refine Equiv.ext fun j => ?_
  have h : coordBij (coordBij⁻¹ j) = j := Equiv.apply_symm_apply coordBij j
  rw [MulAut.conj_apply, Equiv.Perm.mul_apply (coordBij * m12gB),
    Equiv.Perm.mul_apply coordBij m12gB]
  conv_lhs => rw [← h]
  exact (lineMap_σ_coordBij _).2

@[expose] noncomputable def m12Conj : Subgroup (Equiv.Perm (Fin 12)) :=
  NativeSporadic.M12.map (MulAut.conj coordBij).toMonoidHom

theorem m12Conj_eq : m12Conj = Subgroup.closure {MulAut.conj coordBij m12gA,
    MulAut.conj coordBij m12gB} := by
  unfold m12Conj
  rw [m12_eq, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem range_qPerm : qPerm.range = m12Conj := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    rw [m12Conj_eq]
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [show (⟨σ 0, _⟩ : Q) = ⟨σ 0, σ_mem_Q 0⟩ from rfl, qPerm_σ0]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [show (⟨σ 1, _⟩ : Q) = ⟨σ 1, σ_mem_Q 1⟩ from rfl, qPerm_σ1]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [show (⟨-1, _⟩ : Q) = ⟨-1, neg_one_mem_Q⟩ from rfl, qPerm_neg_one]
        exact Subgroup.one_mem _
    | one =>
      rw [show (⟨1, _⟩ : Q) = 1 from rfl, map_one qPerm]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      rw [show (⟨x * y, _⟩ : Q) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul qPerm]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
      rw [show (⟨x⁻¹, _⟩ : Q) = (⟨x, hx⟩ : Q)⁻¹ from rfl, map_inv qPerm]
      exact Subgroup.inv_mem _ ih
  · rw [m12Conj_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨σ 0, σ_mem_Q 0⟩, qPerm_σ0⟩
    · exact ⟨⟨σ 1, σ_mem_Q 1⟩, qPerm_σ1⟩

theorem diag_mem_T {g : Mat12} (hg : IsMono g) (h1 : ∀ j, lineMap g j = j)
    (hT : ∀ v ∈ T, g *ᵥ v ∈ T) : g = 1 ∨ g = -1 := by
  have hgd := hg.eq_diagonal h1
  have hmul : ∀ v, g *ᵥ v = (fun j => g j j) * v := by
    intro v
    conv_lhs => rw [hgd]
    funext j
    rw [mulVec_diagonal]
    rfl
  have hdT : (fun j => g j j) ∈ T := by
    have := hT _ ones_mem_T
    have e : (fun j => g j j) * (fun _ => (1 : ZMod 3)) = fun j => g j j :=
      funext fun j => mul_one (g j j)
    rw [hmul, e] at this
    exact this
  obtain ⟨b, hb⟩ := (mem_T_iff _).mp hdT
  have hfull : ∀ j, (b ᵥ* R) j ≠ 0 := by
    intro j
    rw [hb]
    have := hg.ne_zero j
    rwa [h1] at this
  have hrows : ∀ k, R *ᵥ ((b ᵥ* R) * R k) = 0 := by
    intro k
    rw [← mem_T_iff_mulVec, hb, ← hmul]
    exact hT _ (Submodule.subset_span ⟨k, rfl⟩)
  rcases sign_check b hfull hrows with h | h
  · have hd1 : (fun j => g j j) = 1 := by rw [← hb, h]
    left
    rw [hgd, hd1]
    exact Matrix.diagonal_one
  · have hd1 : (fun j => g j j) = -1 := by rw [← hb, h]
    right
    rw [hgd, hd1, diagonal_neg_one]

theorem qPerm_eq_one_iff (g : Q) : qPerm g = 1 ↔ (g : GL12) = 1 ∨ (g : GL12) = -1 := by
  constructor
  · intro h
    have h1 : ∀ j, lineMap ((g : GL12) : Mat12) j = j := fun j => by
      rw [← qPerm_apply, h, Equiv.Perm.one_apply]
    rcases diag_mem_T (Q_isMono g g.2) h1 (Q_preserves_T g g.2) with h' | h'
    · exact Or.inl (Units.ext (by rw [h', Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h', neg_one_val]))
  · rintro (h | h)
    · rw [show g = 1 from Subtype.ext h, map_one qPerm]
    · rw [show g = ⟨-1, neg_one_mem_Q⟩ from Subtype.ext h, qPerm_neg_one]

theorem one_ne_neg_one : (1 : GL12) ≠ -1 := by
  intro h
  have := congrArg (fun g : GL12 => (g : Mat12) 0 0) h
  simp only [Units.val_one, neg_one_val] at this
  revert this
  decide

theorem card_ker_qPerm : Nat.card qPerm.ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨⟨-1, neg_one_mem_Q⟩, MonoidHom.mem_ker.mpr qPerm_neg_one⟩,
    fun h => one_ne_neg_one ?_, ?_⟩
  · exact congrArg (fun x : qPerm.ker => ((x : Q) : GL12)) h
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (qPerm_eq_one_iff x).mp (MonoidHom.mem_ker.mp hx) with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext h)

theorem card_m12Conj : Nat.card m12Conj = 95040 := by
  unfold m12Conj
  rw [Subgroup.card_map_of_injective (MulAut.conj coordBij).injective, card_M12]

theorem card_Q : Nat.card Q = 190080 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup qPerm.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange qPerm).toEquiv, range_qPerm, card_m12Conj,
    card_ker_qPerm]

theorem m12_simple : IsSimpleGroup NativeSporadic.M12 := fam_m12_simplicity.2.2

theorem m12ab_ne : m12a * m12b ≠ m12b * m12a := by
  intro h
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
  exact m12_not_comm h'

theorem m12_center_eq_bot : Subgroup.center NativeSporadic.M12 = ⊥ := by
  have := m12_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center NativeSporadic.M12) with h | h
  · exact h
  · exfalso
    have hc : m12a ∈ Subgroup.center NativeSporadic.M12 := h ▸ Subgroup.mem_top _
    exact m12ab_ne (Subgroup.mem_center_iff.mp hc m12b).symm

theorem m12_commutator_eq_top : commutator NativeSporadic.M12 = ⊤ := by
  have := m12_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator NativeSporadic.M12) with h | h
  · exfalso
    have hc := (commutator_eq_bot_iff _).mp h
    exact m12ab_ne (hc.is_comm.comm m12a m12b)
  · exact h

theorem m12Conj_central {z : Equiv.Perm (Fin 12)} (hz : z ∈ m12Conj)
    (h : ∀ x ∈ m12Conj, x * z = z * x) : z = 1 := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  have hyc : (⟨y, hy⟩ : NativeSporadic.M12) ∈ Subgroup.center NativeSporadic.M12 := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have := h _ (Subgroup.mem_map_of_mem _ hx)
    rw [← map_mul, ← map_mul] at this
    exact (MulAut.conj coordBij).injective this
  rw [m12_center_eq_bot, Subgroup.mem_bot] at hyc
  have : y = 1 := congrArg Subtype.val hyc
  rw [this, map_one]

theorem m12Conj_commutator : ⁅m12Conj, m12Conj⁆ = m12Conj := by
  unfold m12Conj
  rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator, m12_commutator_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem neg_one_comm (g : GL12) : g * (-1) = (-1) * g := by
  rw [mul_neg_one, neg_one_mul]

theorem mem_center_Q_iff (g : Q) :
    g ∈ Subgroup.center Q ↔ (g : GL12) = 1 ∨ (g : GL12) = -1 := by
  constructor
  · intro hg
    rw [← qPerm_eq_one_iff]
    apply m12Conj_central (by rw [← range_qPerm]; exact ⟨g, rfl⟩)
    intro x hx
    rw [← range_qPerm] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul qPerm, ← map_mul qPerm, Subgroup.mem_center_iff.mp hg y]
  · rintro (h | h)
    · rw [show g = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
      exact neg_one_comm _

theorem nsWord_mem : nsWord ∈ Q := by
  unfold nsWord
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
  exact σ_mem_Q _

theorem nsWord_val : (nsWord : Mat12) =
    signedMatrix (signedProd Data.nonsplitWord).1 (signedProd Data.nonsplitWord).2 := by
  rw [← word_prod_eq]
  unfold nsWord
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  rfl

theorem nsWord_sq : nsWord ^ 2 = -1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, neg_one_val, pow_two, nsWord_val, signedMatrix_mul]
  exact nsWord_sq_check

theorem not_exists_section : ¬ ∃ s : qPerm.range →* Q, ∀ x, qPerm (s x) = x := by
  rintro ⟨s, hs⟩
  let w : Q := ⟨nsWord, nsWord_mem⟩
  let m : qPerm.range := ⟨qPerm w, w, rfl⟩
  have hw2' : w ^ 2 = ⟨-1, neg_one_mem_Q⟩ :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact nsWord_sq)
  have hm2 : m ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change qPerm w ^ 2 = 1
    rw [← map_pow qPerm, hw2', qPerm_neg_one]
  have hu2 : s m ^ 2 = 1 := by rw [← map_pow s, hm2, map_one s]
  have hk : qPerm ((s m)⁻¹ * w) = 1 := by
    rw [map_mul qPerm, map_inv qPerm, hs m]
    exact inv_mul_cancel (qPerm w)
  have hw2 : (w : GL12) ^ 2 = 1 := by
    rcases (qPerm_eq_one_iff _).mp hk with h | h
    · have h' : (s m)⁻¹ * w = 1 := Subtype.ext h
      have : w = s m := (inv_mul_eq_one.mp h').symm
      rw [this, ← SubgroupClass.coe_pow, hu2, OneMemClass.coe_one]
    · have h' : (s m)⁻¹ * w = ⟨-1, neg_one_mem_Q⟩ := Subtype.ext h
      have : w = s m * ⟨-1, neg_one_mem_Q⟩ := by rw [← h', mul_inv_cancel_left]
      have hval : (w : GL12) = (s m : GL12) * (-1) :=
        (congrArg Subtype.val this).trans (Subgroup.coe_mul Q _ _)
      rw [hval, (Commute.neg_one_right _).mul_pow, neg_one_sq, mul_one,
        ← SubgroupClass.coe_pow, hu2, OneMemClass.coe_one]
  exact one_ne_neg_one (hw2.symm.trans nsWord_sq)

theorem commutator_Q : commutator Q = ⊤ := by
  have hmap : (commutator Q).map qPerm = qPerm.range := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_qPerm,
      m12Conj_commutator]
  have hneg : (⟨-1, neg_one_mem_Q⟩ : Q) ∈ commutator Q := by
    by_contra hn
    apply not_exists_section
    let f₀ : commutator Q →* Equiv.Perm (Fin 12) := qPerm.comp (commutator Q).subtype
    let f : commutator Q →* qPerm.range := f₀.codRestrict qPerm.range fun x => ⟨x, rfl⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h1 : qPerm ((x : Q)⁻¹ * y) = 1 := by
          have := congrArg Subtype.val hxy
          change qPerm (x : Q) = qPerm (y : Q) at this
          rw [map_mul qPerm, map_inv qPerm, this, inv_mul_cancel]
        rcases (qPerm_eq_one_iff _).mp h1 with h | h
        · apply Subtype.ext
          have : (x : Q)⁻¹ * y = 1 := Subtype.ext h
          exact inv_mul_eq_one.mp this
        · exfalso
          apply hn
          have : (x : Q)⁻¹ * y = ⟨-1, neg_one_mem_Q⟩ := Subtype.ext h
          rw [← this]
          exact (commutator Q).mul_mem ((commutator Q).inv_mem x.2) y.2
      · rintro ⟨y, hy⟩
        rw [← hmap] at hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hx⟩, rfl⟩
    refine ⟨(commutator Q).subtype.comp (MulEquiv.ofBijective f hf).symm.toMonoidHom,
      fun y => ?_⟩
    exact congrArg Subtype.val ((MulEquiv.ofBijective f hf).apply_symm_apply y)
  rw [eq_top_iff]
  intro g _
  have hg : qPerm g ∈ (commutator Q).map qPerm := by
    rw [hmap]
    exact ⟨g, rfl⟩
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hg
  have hk : qPerm (c⁻¹ * g) = 1 := by
    rw [map_mul qPerm, map_inv qPerm, hcg, inv_mul_cancel]
  have hg' : g = c * (c⁻¹ * g) := by rw [mul_inv_cancel_left]
  rw [hg']
  refine (commutator Q).mul_mem hc ?_
  rcases (qPerm_eq_one_iff _).mp hk with h | h
  · rw [show c⁻¹ * g = 1 from Subtype.ext h]
    exact (commutator Q).one_mem
  · rw [show c⁻¹ * g = ⟨-1, neg_one_mem_Q⟩ from Subtype.ext h]
    exact hneg

end CFSG.Sporadic.Co1Schreier
