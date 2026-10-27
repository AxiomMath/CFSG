module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Natural

variable {n : ℕ} {F : Type} [Field F]

theorem one_add_vecMulVec_mulVec (u φ v : Fin n → F) :
    (1 + Matrix.vecMulVec u φ) *ᵥ v = v + (φ ⬝ᵥ v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem single_dotProduct_smul_single {i j : Fin n} (hij : i ≠ j) (c : F) :
    Pi.single j (1 : F) ⬝ᵥ (c • Pi.single i (1 : F)) = 0 := by
  rw [single_dotProduct, one_mul, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero]

@[expose] noncomputable def slElTrans {i j : Fin n} (hij : i ≠ j) (c : F) : ↥(StatedSL n F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (1 + Matrix.vecMulVec (c • Pi.single i (1 : F)) (Pi.single j (1 : F)) :
        Matrix (Fin n) (Fin n) F) (by
        rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
          single_dotProduct_smul_single hij, add_zero]
        exact one_ne_zero),
    Subgroup.subset_closure (by
      show Matrix.det (1 + Matrix.vecMulVec (c • Pi.single i (1 : F)) (Pi.single j (1 : F)) :
        Matrix (Fin n) (Fin n) F) = 1
      rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
        single_dotProduct_smul_single hij, add_zero])⟩

theorem mulVec_slElTrans {i j : Fin n} (hij : i ≠ j) (c : F) (v : Fin n → F) :
    (((slElTrans hij c : ↥(StatedSL n F)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v =
      v + Pi.single i (c * v j) := by
  show (1 + Matrix.vecMulVec (c • Pi.single i (1 : F)) (Pi.single j (1 : F)) :
    Matrix (Fin n) (Fin n) F) *ᵥ v = _
  rw [one_add_vecMulVec_mulVec, single_dotProduct, one_mul]
  congr 1
  ext k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

theorem exists_fin_ne_of_two_le (hn : 2 ≤ n) (k : Fin n) : ∃ j : Fin n, j ≠ k := by
  by_cases h0 : (k : ℕ) = 0
  · exact ⟨⟨1, by omega⟩, fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega⟩
  · exact ⟨⟨0, by omega⟩, fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega⟩

theorem eq_top_of_slMulVec_mem (hn : 2 ≤ n) {S : AddSubgroup (Fin n → F)}
    (hS : ∀ g : ↥(StatedSL n F), ∀ v ∈ S,
      (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ S)
    {v : Fin n → F} (hv : v ∈ S) (hne : v ≠ 0) : S = ⊤ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hne' : ∀ j, j ≠ i → ∀ t : F, Pi.single j t ∈ S := by
    intro j hji t
    have h := S.sub_mem (hS (slElTrans hji (t / v i)) v hv) hv
    rwa [mulVec_slElTrans, add_sub_cancel_left, div_mul_cancel₀ _ hi] at h
  have hall : ∀ k (t : F), Pi.single k t ∈ S := by
    intro k t
    by_cases hk : k = i
    · subst hk
      obtain ⟨j, hj⟩ := exists_fin_ne_of_two_le hn k
      have h1 := hne' j hj 1
      have h := S.sub_mem (hS (slElTrans (Ne.symm hj) t) _ h1) h1
      rwa [mulVec_slElTrans, add_sub_cancel_left, Pi.single_eq_same, mul_one] at h
    · exact hne' k hk t
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact AddSubgroup.sum_mem _ fun k _ => hall k (w k)

theorem exists_smul_of_comm_sl (hn : 2 ≤ n) (φ : (Fin n → F) →+ (Fin n → F))
    (hφ : ∀ g : ↥(StatedSL n F), ∀ v,
      φ (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) =
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ φ v) :
    ∃ q : F, ∀ v, φ v = q • v := by
  classical
  have ht : ∀ {i j : Fin n} (hij : i ≠ j) (c : F) (v : Fin n → F),
      φ (v + Pi.single i (c * v j)) = φ v + Pi.single i (c * φ v j) := by
    intro i j hij c v
    have h := hφ (slElTrans hij c) v
    rwa [mulVec_slElTrans, mulVec_slElTrans] at h
  have hdiag : ∀ k (c : F), ∀ j, j ≠ k → φ (Pi.single k c) j = 0 := by
    intro k c j hjk
    obtain ⟨i, hij⟩ := exists_fin_ne_of_two_le hn j
    have h := ht hij 1 (Pi.single k c)
    rw [Pi.single_eq_of_ne hjk, mul_zero, Pi.single_zero, add_zero, one_mul] at h
    have h2 := congrArg (fun w => w i) h
    simp only [Pi.add_apply, Pi.single_eq_same, left_eq_add] at h2
    exact h2
  have hform : ∀ k (c : F), φ (Pi.single k c) = Pi.single k (φ (Pi.single k c) k) := by
    intro k c
    ext j
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [Pi.single_eq_of_ne hjk, hdiag k c j hjk]
  have hcross : ∀ i j (hij : i ≠ j) (c : F),
      φ (Pi.single i c) = Pi.single i (c * φ (Pi.single j 1) j) := by
    intro i j hij c
    have h := ht hij c (Pi.single j 1)
    rw [Pi.single_eq_same, mul_one, map_add, add_right_inj] at h
    exact h
  obtain ⟨j₀, -⟩ := exists_fin_ne_of_two_le hn ⟨0, by omega⟩
  set q := φ (Pi.single j₀ 1) j₀ with hq
  have hall : ∀ k (c : F), φ (Pi.single k c) = Pi.single k (c * q) := by
    intro k c
    by_cases hk : k = j₀
    · subst hk
      obtain ⟨i, hi⟩ := exists_fin_ne_of_two_le hn k
      have h1 := hcross i k hi 1
      rw [one_mul] at h1
      have h2 := hcross k i (Ne.symm hi) c
      rw [h2, h1, Pi.single_eq_same, hq]
    · exact hcross k j₀ hk c
  refine ⟨q, fun v => ?_⟩
  rw [← Finset.univ_sum_single v, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hall]
  ext j
  by_cases hj : j = k
  · subst hj
    simp [mul_comm]
  · simp [Pi.single_eq_of_ne hj]

end Natural

variable {G : Type} [Group G]

@[expose] def IsNatEigSection (K : Subgroup G) (x : G) {n : ℕ} {F : Type} [Field F]
    (α₀ : ↥K →* ↥(StatedSL n F)) (C₁ C₂ : Subgroup G) (a : F) : Prop :=
  ∃ β : ↥C₂ →* Multiplicative (Fin n → F), Function.Surjective β ∧
    (∀ c : ↥C₂, β c = 1 ↔ (c : G) ∈ C₁) ∧
    (∀ (k : ↥K) (c c' : ↥C₂), (c' : G) = k * c * (k : G)⁻¹ →
      Multiplicative.toAdd (β c') =
        (((α₀ k : ↥(StatedSL n F)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
          Multiplicative.toAdd (β c)) ∧
    ∀ c c' : ↥C₂, (c' : G) = x * c * x⁻¹ →
      Multiplicative.toAdd (β c') = a • Multiplicative.toAdd (β c)

@[expose] def IsLabFactor (Y K : Subgroup G) (x : G) {n : ℕ} {F : Type} [Field F]
    (α₀ : ↥K →* ↥(StatedSL n F)) (C S : Subgroup G) (e : Option F) : Prop :=
  C < S ∧ S ≤ Subgroup.normalizer (C : Set G) ∧ Y ≤ Subgroup.normalizer (C : Set G) ∧
    Y ≤ Subgroup.normalizer (S : Set G) ∧
    (∀ J : Subgroup G, C ≤ J → J ≤ S → S ≤ Subgroup.normalizer (J : Set G) →
      Y ≤ Subgroup.normalizer (J : Set G) → J = C ∨ J = S) ∧
    e.elim (∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ C) (fun a => IsNatEigSection K x α₀ C S a)

@[expose] def IsLabSeries (Y K : Subgroup G) (x : G) {n : ℕ} {F : Type} [Field F]
    (α₀ : ↥K →* ↥(StatedSL n F)) : Subgroup G → List (Subgroup G × Option F) → Subgroup G → Prop
  | C, [], D => C = D
  | C, p :: l, D => IsLabFactor Y K x α₀ C p.1 p.2 ∧ IsLabSeries Y K x α₀ p.1 l D

@[expose] def labMultiset {F : Type} (l : List (Subgroup G × Option F)) : Multiset F :=
  (l.filterMap Prod.snd : List F)

theorem labMultiset_nil {F : Type} : labMultiset ([] : List (Subgroup G × Option F)) = 0 := rfl

theorem labMultiset_cons {F : Type} (p : Subgroup G × Option F) (l : List (Subgroup G × Option F)) :
    labMultiset (p :: l) = (p.2.elim 0 fun a => {a}) + labMultiset l := by
  obtain ⟨S, e⟩ := p
  cases e with
  | none => simp [labMultiset]
  | some a => simp [labMultiset]

theorem labMultiset_append {F : Type} (l₁ l₂ : List (Subgroup G × Option F)) :
    labMultiset (l₁ ++ l₂) = labMultiset l₁ + labMultiset l₂ := by
  simp [labMultiset, List.filterMap_append]

section Series

variable {Y K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F] {α₀ : ↥K →* ↥(StatedSL n F)}

theorem isLabSeries_nil {C D : Subgroup G} :
    IsLabSeries Y K x α₀ C ([] : List (Subgroup G × Option F)) D ↔ C = D := Iff.rfl

theorem isLabSeries_cons {C D : Subgroup G} {p : Subgroup G × Option F}
    {l : List (Subgroup G × Option F)} :
    IsLabSeries Y K x α₀ C (p :: l) D ↔
      IsLabFactor Y K x α₀ C p.1 p.2 ∧ IsLabSeries Y K x α₀ p.1 l D := Iff.rfl

theorem isLabSeries_singleton {C S : Subgroup G} {e : Option F}
    (h : IsLabFactor Y K x α₀ C S e) : IsLabSeries Y K x α₀ C [(S, e)] S :=
  ⟨h, rfl⟩

theorem IsLabSeries.append {C D E : Subgroup G} {l₁ l₂ : List (Subgroup G × Option F)}
    (h₁ : IsLabSeries Y K x α₀ C l₁ D) (h₂ : IsLabSeries Y K x α₀ D l₂ E) :
    IsLabSeries Y K x α₀ C (l₁ ++ l₂) E := by
  induction l₁ generalizing C with
  | nil =>
    have hCD : C = D := h₁
    subst hCD
    exact h₂
  | cons p l ih => exact ⟨h₁.1, ih h₁.2⟩

theorem IsLabSeries.le {C D : Subgroup G} {l : List (Subgroup G × Option F)}
    (h : IsLabSeries Y K x α₀ C l D) : C ≤ D := by
  induction l generalizing C with
  | nil =>
    have hCD : C = D := h
    exact hCD.le
  | cons p l ih => exact h.1.1.le.trans (ih h.2)

omit [Field F] in
theorem labMultiset_eq_zero_of_forall {l : List (Subgroup G × Option F)}
    (h : ∀ p ∈ l, p.2 = none) : labMultiset l = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [labMultiset_cons, h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

end Series

section NatEig

variable {K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F] {α₀ : ↥K →* ↥(StatedSL n F)}
  {C₁ C₂ : Subgroup G}

theorem IsNatEigSection.eq_or_eq {a : F} (h : IsNatEigSection K x α₀ C₁ C₂ a) (hn : 2 ≤ n)
    (hα : Function.Surjective α₀) (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) {J : Subgroup G}
    (hCJ : C₁ ≤ J) (hJC : J ≤ C₂) (hKJ : K ≤ Subgroup.normalizer (J : Set G)) :
    J = C₁ ∨ J = C₂ := by
  obtain ⟨β, hβs, hβk, hβK, -⟩ := h
  by_cases hJ : J ≤ C₁
  · exact Or.inl (le_antisymm hJ hCJ)
  right
  obtain ⟨j, hjJ, hjC⟩ := Set.not_subset.mp hJ
  let T : AddSubgroup (Fin n → F) :=
    { carrier := {v | ∃ c : ↥C₂, (c : G) ∈ J ∧ Multiplicative.toAdd (β c) = v}
      add_mem' := by
        rintro v v' ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
        exact ⟨c * c', J.mul_mem hc hc', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, J.one_mem, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro v ⟨c, hc, rfl⟩
        exact ⟨c⁻¹, J.inv_mem hc, by rw [map_inv, toAdd_inv]⟩ }
  have hTinv : ∀ g : ↥(StatedSL n F), ∀ v ∈ T,
      (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ T := by
    rintro g v ⟨c, hc, rfl⟩
    obtain ⟨k, rfl⟩ := hα g
    have hkc : (k : G) * c * (k : G)⁻¹ ∈ C₂ :=
      (Subgroup.mem_normalizer_iff.mp (hKC k.2) _).mp c.2
    exact ⟨⟨_, hkc⟩, (Subgroup.mem_normalizer_iff.mp (hKJ k.2) _).mp hc,
      hβK k c ⟨_, hkc⟩ rfl⟩
  have hjT : Multiplicative.toAdd (β ⟨j, hJC hjJ⟩) ∈ T := ⟨⟨j, hJC hjJ⟩, hjJ, rfl⟩
  have hj0 : Multiplicative.toAdd (β ⟨j, hJC hjJ⟩) ≠ 0 := by
    intro h0
    apply hjC
    exact (hβk _).mp (Multiplicative.toAdd.injective (h0.trans toAdd_one.symm))
  have hT := eq_top_of_slMulVec_mem hn hTinv hjT hj0
  refine le_antisymm hJC fun c hc => ?_
  have hcT : Multiplicative.toAdd (β ⟨c, hc⟩) ∈ T := by
    rw [hT]
    exact AddSubgroup.mem_top _
  obtain ⟨c', hc'J, hc'⟩ := hcT
  have h1 : β (c'⁻¹ * ⟨c, hc⟩) = 1 := by
    rw [map_mul, map_inv, Multiplicative.toAdd.injective hc', inv_mul_cancel]
  have h2 := (hβk _).mp h1
  have h3 : c = (c' : G) * ((c'⁻¹ * ⟨c, hc⟩ : ↥C₂) : G) := by
    simp
  rw [h3]
  exact J.mul_mem hc'J (hCJ h2)

theorem IsNatEigSection.not_centralized {a : F} (h : IsNatEigSection K x α₀ C₁ C₂ a)
    (hn : 2 ≤ n) (hα : Function.Surjective α₀) (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) :
    ¬ ∀ k ∈ K, ∀ s ∈ C₂, k * s * k⁻¹ * s⁻¹ ∈ C₁ := by
  intro hc
  obtain ⟨β, hβs, hβk, hβK, -⟩ := h
  obtain ⟨j, -⟩ := exists_fin_ne_of_two_le hn ⟨0, by omega⟩
  obtain ⟨i, hij⟩ := exists_fin_ne_of_two_le hn j
  obtain ⟨c, hc'⟩ := hβs (Multiplicative.ofAdd (Pi.single j 1))
  obtain ⟨k, hk⟩ := hα (slElTrans hij 1)
  have hkc : (k : G) * c * (k : G)⁻¹ ∈ C₂ :=
    (Subgroup.mem_normalizer_iff.mp (hKC k.2) _).mp c.2
  have h1 := hβK k c ⟨_, hkc⟩ rfl
  rw [hk, hc', toAdd_ofAdd, mulVec_slElTrans, Pi.single_eq_same, mul_one] at h1
  have h2 : β (⟨_, hkc⟩ * c⁻¹) = 1 :=
    (hβk _).mpr (hc k k.2 c c.2)
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  have h3 := congrArg Multiplicative.toAdd h2
  rw [h1, hc', toAdd_ofAdd, add_eq_left] at h3
  have h4 := congrArg (fun w => w i) h3
  simp only [Pi.single_eq_same, Pi.zero_apply] at h4
  exact one_ne_zero h4

theorem IsNatEigSection.eig_unique {a b : F} (ha : IsNatEigSection K x α₀ C₁ C₂ a)
    (hb : IsNatEigSection K x α₀ C₁ C₂ b) (hn : 2 ≤ n) (hα : Function.Surjective α₀)
    (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) (hxC : x ∈ Subgroup.normalizer (C₂ : Set G)) :
    a = b := by
  obtain ⟨β₁, hβ₁s, hβ₁k, hβ₁K, hβ₁x⟩ := ha
  obtain ⟨β₂, -, hβ₂k, hβ₂K, hβ₂x⟩ := hb
  have hker : β₁.ker ≤ β₂.ker := fun c hc =>
    (hβ₂k c).mpr ((hβ₁k c).mp hc)
  set φ₀ := (MonoidHom.liftOfRightInverse β₁ (Function.surjInv hβ₁s)
    (Function.rightInverse_surjInv hβ₁s)) ⟨β₂, hker⟩ with hφ₀
  have hφ₀β : ∀ c, φ₀ (β₁ c) = β₂ c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨β₂, hker⟩ c
  let φ : (Fin n → F) →+ (Fin n → F) :=
    { toFun := fun v => Multiplicative.toAdd (φ₀ (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add, toAdd_mul] }
  have hφβ : ∀ c, φ (Multiplicative.toAdd (β₁ c)) = Multiplicative.toAdd (β₂ c) := fun c => by
    show Multiplicative.toAdd (φ₀ (Multiplicative.ofAdd (Multiplicative.toAdd (β₁ c)))) = _
    rw [ofAdd_toAdd, hφ₀β]
  have hφcomm : ∀ g : ↥(StatedSL n F), ∀ v,
      φ (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) =
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ φ v := by
    intro g v
    obtain ⟨k, rfl⟩ := hα g
    obtain ⟨c, hc⟩ := hβ₁s (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (β₁ c) := by rw [hc, toAdd_ofAdd]
    have hkc : (k : G) * c * (k : G)⁻¹ ∈ C₂ :=
      (Subgroup.mem_normalizer_iff.mp (hKC k.2) _).mp c.2
    rw [hv, ← hβ₁K k c ⟨_, hkc⟩ rfl, hφβ, hφβ, hβ₂K k c ⟨_, hkc⟩ rfl]
  obtain ⟨q, hq⟩ := exists_smul_of_comm_sl hn φ hφcomm
  obtain ⟨j, -⟩ := exists_fin_ne_of_two_le hn ⟨0, by omega⟩
  obtain ⟨c, hc⟩ := hβ₁s (Multiplicative.ofAdd (Pi.single j 1))
  have hxc : x * c * x⁻¹ ∈ C₂ := (Subgroup.mem_normalizer_iff.mp hxC _).mp c.2
  have h1 := hφβ ⟨_, hxc⟩
  rw [hβ₁x c ⟨_, hxc⟩ rfl, hβ₂x c ⟨_, hxc⟩ rfl, hq, ← hφβ c, hq, hc, toAdd_ofAdd] at h1
  have h2 := congrArg (fun w => w j) h1
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
  have hq0 : q ≠ 0 := by
    intro hq0
    have h3 := hφβ c
    rw [hq, hq0, zero_smul] at h3
    have h4 : β₂ c = 1 := Multiplicative.toAdd.injective (h3.symm.trans toAdd_one.symm)
    have h5 := (hβ₁k c).mpr ((hβ₂k c).mp h4)
    rw [hc] at h5
    have h6 := congrArg (fun w : Multiplicative (Fin n → F) => Multiplicative.toAdd w j) h5
    simp only [toAdd_ofAdd, Pi.single_eq_same, toAdd_one, Pi.zero_apply] at h6
    exact one_ne_zero h6
  exact mul_left_cancel₀ hq0 (h2.trans (mul_comm b q))

end NatEig

theorem IsLabFactor.label_unique {Y K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F]
    {α₀ : ↥K →* ↥(StatedSL n F)} {C S : Subgroup G} {e₁ e₂ : Option F}
    (h₁ : IsLabFactor Y K x α₀ C S e₁) (h₂ : IsLabFactor Y K x α₀ C S e₂) (hKY : K ≤ Y)
    (hxY : x ∈ Y) (hn : 2 ≤ n) (hα : Function.Surjective α₀) : e₁ = e₂ := by
  have hKS : K ≤ Subgroup.normalizer (S : Set G) := hKY.trans h₁.2.2.2.1
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := h₁.2.2.2.1 hxY
  obtain ⟨-, -, -, -, -, he₁⟩ := h₁
  obtain ⟨-, -, -, -, -, he₂⟩ := h₂
  cases e₁ with
  | none =>
    cases e₂ with
    | none => rfl
    | some b => exact absurd he₁ (IsNatEigSection.not_centralized he₂ hn hα hKS)
  | some a =>
    cases e₂ with
    | none => exact absurd he₂ (IsNatEigSection.not_centralized he₁ hn hα hKS)
    | some b => exact congrArg some (he₁.eig_unique he₂ hn hα hKS hxS)

@[expose] def OperatorJHNatEig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (x : G) (n : ℕ) (F : Type) [Field F]
    (α₀ : ↥K →* ↥(StatedSL n F)), K ≤ Y → x ∈ Y → 2 ≤ n → Function.Surjective α₀ →
    ∀ (C D : Subgroup G) (l : List (Subgroup G × Option F)), IsLabSeries Y K x α₀ C l D →
      (∀ l' : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l' D →
        labMultiset l' = labMultiset l) ∧
      ∀ E : Subgroup G, C ≤ E → E ≤ D → E ≤ Subgroup.normalizer (C : Set G) →
        D ≤ Subgroup.normalizer (E : Set G) → Y ≤ Subgroup.normalizer (E : Set G) →
        ∃ l₁ l₂ : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l₁ E ∧
          IsLabSeries Y K x α₀ E l₂ D ∧ labMultiset l₁ + labMultiset l₂ = labMultiset l

end CFSG.Quasithin
