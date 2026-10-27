module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEnd

namespace CFSG
end CFSG
open CFSG

namespace CFSG.Theory.Representation

open _root_.Representation
open scoped MonoidAlgebra
open scoped TensorProduct

/-
**Kind**: Theorem
**Name**: Jacobson Density Theorem
**Note**: G, Theorem 3.6.2
**Stmt**:
Let $F$ be a field.
Let $A$ be an algebra over $F$.
Let $V$ be a finite dimensional vector space over $F$.
Let $A$ represent faithfully and irreducibly on $V$.
If $\End_{A}(V) = F$.
Then A is isomorphic to the algebra $\End_{F}(V)$ of all linear transformations on V.
-/

/-- The algebra homomorphism sending an element of `A` to its action on `V`. -/
@[expose]
public def jacobson_density_mapping
    (F : Type*) [Field F]
    (A : Type*) [Ring A] [Algebra F A]
    (V : Type*) [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower F A V] :
  A →ₐ[F] Module.End F V := {
    toFun := fun a ↦ {
      toFun := fun v ↦ a • v
      map_add' := fun x y ↦ smul_add a x y
      map_smul' := fun m x ↦ smul_comm a m x
    }
    map_one' := by
      ext v
      simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    map_mul' := fun x y => by
      ext v
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, mul_smul]
    map_zero' := by
      ext v
      simp only [zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
    map_add' := fun x y => by
      ext v
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, add_smul]
    commutes' := fun f => by
      ext v
      simp only [algebraMap_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply]
  }

public theorem simple_of_jacobson_density_surjective
    {F : Type*} [Field F]
    {A : Type*} [Ring A] [Algebra F A]
    {V : Type*} [AddCommGroup V] [inst : Nontrivial V] [Module F V]
    [FiniteDimensional F V] [Module A V] [IsScalarTower F A V]
    (hs : Function.Surjective (jacobson_density_mapping F A V)) :
    IsSimpleModule A V := by
  rw [isSimpleModule_iff, isSimpleOrder_iff]
  constructor
  · obtain ⟨x, y, hxy⟩ := inst.exists_pair_ne
    rw [nontrivial_iff]
    use ⊤, ⊥
    rw [← SetLike.coe_ne_coe]
    simp only [Submodule.top_coe, Submodule.bot_coe, ne_eq]
    contrapose hxy
    have (v : V) : v ∈ ({0} : Set V) := hxy.symm ▸ Set.mem_univ v
    simp only [Set.mem_singleton_iff] at this
    rw [this x, this y]
  · have {s : Submodule A V} (h : s ≠ ⊥) : s = ⊤ := by
      obtain ⟨v, hmem, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      rw [Submodule.eq_top_iff']
      intro w
      by_cases! hw : w = 0
      · exact hw ▸ Submodule.zero_mem s
      let : DecidableEq V := Classical.typeDecidableEq V
      let b := Module.Basis.extend (LinearIndepOn.singleton hv) (K := F)
      let b' := Module.Basis.extend (LinearIndepOn.singleton hw) (K := F)
      let A : Module.End F V := (b.linearMap b') (⟨w, by apply Module.Basis.subset_extend; rfl⟩, ⟨v, by apply Module.Basis.subset_extend; rfl⟩)
      have h : A v = w := by
        have : b ⟨v, by apply Module.Basis.subset_extend; rfl⟩ = v := by
          rw [Module.Basis.coe_extend]
        rw [← this, Module.Basis.linearMap_apply_apply]
        simp only [↓reduceIte]
        rw [Module.Basis.coe_extend]
      obtain ⟨a, ha⟩ := hs A
      have : w = a • v  := by
        rw [← h, ← ha]
        rfl
      rw [this]
      exact Submodule.smul_of_tower_mem s a hmem
    tauto

public theorem surjective_of_jacobson_density_surjective
    {F : Type*} [Field F]
    {A : Type*} [Ring A] [Algebra F A]
    {V : Type*} [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower F A V]
    (hs : Function.Surjective (jacobson_density_mapping F A V)) :
    Function.Surjective (algebraMap F (Module.End A V)) := by
  intro T
  by_cases! h : ¬ Nontrivial V
  · use 0
    ext v
    rw [not_nontrivial_iff_subsingleton] at h
    exact h.allEq _ _
  have : Nontrivial (Module.Dual F V) := Module.instNontrivialDual F
  have h : ∃ f : Module.Dual F V, f ≠ 0 := exists_ne 0
  obtain ⟨f, hf⟩ := h
  have : ∃ x : V, f x  ≠ 0 := by
    contrapose! hf
    exact LinearMap.ext hf
  obtain ⟨x, hx⟩ := this
  use (f x)⁻¹ * f (T x)
  ext v
  let S : Module.End F V := {
    toFun := fun x => (f x) • v
    map_add' := fun y z ↦ by rw [map_add, add_smul]
    map_smul' := fun m y ↦ by rw [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul]
  }
  have : T (S x) = S (T x) := by
    obtain ⟨S', hS'⟩ := hs S
    have (v : V) : S v = S' • v := by
      rw [← hS']
      rfl
    rw [this, map_smul, this]
  have : T ((f x) • v) = (f (T x)) • v := this
  rw [Module.algebraMap_end_apply, mul_smul, ← this]
  simp only [LinearMap.map_smul_of_tower, ne_eq, hx, not_false_eq_true, inv_smul_smul₀]

public theorem jacobson_density_surjective
    {F : Type*} [Field F]
    {A : Type*} [Ring A] [Algebra F A]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Module A V] [IsScalarTower F A V] [inst : IsSimpleModule A V]
    (hs : Function.Surjective (algebraMap F (Module.End A V))) :
    Function.Surjective (jacobson_density_mapping F A V) := by
  let p : ℕ → Prop := fun n ↦ (W : Submodule F V) → (hdim : Module.finrank F W = n) →
    ∀ u ∉ W, ∃ x : A, (∀ w ∈ W, x • w = 0) ∧ (x • u ≠ 0)
  have (k : ℕ) : p k := by
    apply Nat.strong_induction_on
    intro n hm W hdim u hu
    by_cases! h : n = 0
    · use 1
      refine ⟨fun w hw ↦ ?_, ?_⟩
      all_goals rw [one_smul]
      · rw [h, finrank_zero_iff_forall_zero] at hdim
        exact (AddSubmonoid.mk_eq_zero W.toAddSubmonoid).mp (hdim ⟨w, hw⟩)
      · by_contra h
        rw [h] at hu
        exact hu (zero_mem W)
    let b := Module.Basis.ofVectorSpace F W
    set ι := Module.Basis.ofVectorSpaceIndex F W
    let : Nat.card ι ≠ 0 := by
      rw [← Module.finrank_eq_nat_card_basis b, hdim]
      exact h
    let hne : Nonempty ι := (Nat.card_ne_zero.mp this).1
    let i : ι := Nonempty.some hne
    let U := Submodule.span F {(b j : V) | j ≠ i}
    let N : Ideal A := {
      carrier := {f | ∀ u ∈ U, f • (u : V) = 0}
      add_mem' := by
        intro f₁ f₂ hf₁ hf₂
        simp only [Set.mem_ofPred_eq] at ⊢ hf₁ hf₂
        intro w hw
        rw [add_smul, hf₁ w hw, hf₂ w hw, zero_add]
      zero_mem' := by simp only [Set.mem_ofPred_eq, zero_smul, implies_true]
      smul_mem' := by
        intro f₁ f₂ hf
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at ⊢ hf
        intro w hw
        rw[mul_smul, hf w hw, smul_zero]
    }
    let ιi : Set ι := Set.univ \ {i}
    let j := W.subtype ∘ b
    have hj : {(b j : V) | j ≠ i} = j '' ιi := by
      ext x
      simp_all only [ne_eq, Subtype.exists, Set.mem_ofPred_eq, Submodule.coe_subtype,
        Function.comp_apply, Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
        true_and, p, ι, i, j, ιi]
    have : LinearIndependent F j := by
      rw [LinearMap.linearIndependent_iff]
      · exact Module.Basis.linearIndependent b
      · exact Submodule.ker_subtype W
    have hi : (b i : V) ∉ U := by
      rw [linearIndependent_iff_notMem_span] at this
      unfold U
      rw [hj]
      exact this i
    have hU : Module.finrank F U = n - 1 := by
      let ι' := {j : ι // j ≠ i}
      let v : ι' → V := W.subtype ∘ (b ∘ Subtype.val)
      let : Fintype ι' := Fintype.ofFinite ι'
      let hli : LinearIndependent F v := by
        rw [LinearMap.linearIndependent_iff _ (Submodule.ker_subtype W)]
        apply LinearIndependent.comp (Module.Basis.linearIndependent b)
        exact Subtype.val_injective
      have : Submodule.span F (Set.range v) = U := by
        unfold U v
        congr
        subst hdim
        ext x
        simp_all only [Submodule.coe_subtype, ne_eq, Subtype.exists, Function.comp_apply,
          Set.mem_range, exists_prop, Set.mem_image, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and, ι, j, p, i, ιi, U, ι']
      rw [← this, finrank_span_eq_card hli, ← hdim, Module.finrank_eq_nat_card_basis b, ← Fintype.card_eq_nat_card, Fintype.card_subtype_compl (fun j => j = i)]
      exact
        Eq.rec (motive := fun a e_a ↦ ∀ (a_1 a_2 : ℕ), a_1 = a_2 → Fintype.card ↑ι - a_1 = a - a_2)
          (fun a a_1 e_a ↦ e_a ▸ Eq.refl (Fintype.card ↑ι - a)) (Eq.refl (Fintype.card ↑ι))
          (Fintype.card { x // x = i }) 1
          ((fun α [Fintype α] ↦ Eq.refl (Fintype.card α)) { x // x = i })
    have hap (v : V) : ∃ y ∈ N, y • (b i) = v := by
      let Nv : Submodule A V := {
        carrier := {f • (b i)| f ∈ N}
        add_mem' := by
          intro v₁ v₂ hv₁ hv₂
          simp only [Set.mem_ofPred_eq] at ⊢ hv₁ hv₂
          obtain ⟨f₁, hf₁1, hf₁2⟩ := hv₁
          obtain ⟨f₂, hf₂1, hf₂2⟩ := hv₂
          exact ⟨f₁ + f₂, ⟨(Submodule.add_mem_iff_left N hf₂1).mpr hf₁1, by rw [add_smul, hf₁2, hf₂2]⟩⟩
        zero_mem' := ⟨0, by simp only [zero_mem, zero_smul, and_self]⟩
        smul_mem' := by
          intro f' v' hv'
          simp only [Set.mem_ofPred_eq] at ⊢ hv'
          obtain ⟨f, hf1, hf2⟩ := hv'
          exact ⟨f' * f, Ideal.mul_mem_left N f' hf1, by rw [mul_smul, hf2]⟩
      }
      have : Nv ≠ ⊥ := by
        refine (Submodule.ne_bot_iff Nv).mpr ?_
        simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
          ne_eq, exists_exists_and_eq_and, Nv]
        exact hm (n - 1) (Nat.sub_one_lt h) U hU (b i) hi
      have : Nv = ⊤ := (inst.eq_bot_or_eq_top Nv).resolve_left this
      have : v ∈ Nv := this ▸ Submodule.mem_top
      exact this
    let Tf := fun x ↦ Classical.choose (hap x) • u
    have hN (v : V) (h0 : ∀ y ∈ N, y • v = 0) : v ∈ U := by
      contrapose! h0
      exact hm (n - 1) (Nat.sub_one_lt h) U hU v h0
    have hle : U ≤ W := by
      rw [Submodule.span_le]
      intro v hv
      obtain ⟨a, _, rfl⟩ := hv
      exact Subtype.coe_prop (b a)
    contrapose! hu
    have huni (y : A) (hy : y ∈ N) (x : V) (hy2 : y • (b i : V) = x) : y • u = Tf x := by
      unfold Tf
      obtain ⟨hy', hy'2⟩ :=  Classical.choose_spec (hap x)
      set y' := Classical.choose (hap x)
      rw [← sub_left_inj (a := y' • u), sub_self, ← sub_smul]
      apply hu
      intro v hv
      have : U ⊔ (Submodule.span F ({(b i : V)} : Set V)) = W := by
        apply le_antisymm
        · rw [sup_le_iff]
          constructor
          · exact hle
          · rw [Submodule.span_le]
            intro v hv
            obtain ⟨a, _, rfl⟩ := hv
            exact Subtype.coe_prop (b i)
        · intro v hv
          rw [← Submodule.span_union]
          have : {(b j : V) | j ≠ i} ∪ {(b i : V)} = W.subtype '' { b j  | j : ι } := by
            have : {(b j : V) | j ≠ i} = W.subtype '' {b j | j ≠ i} := by
              apply le_antisymm
              · intro x hx
                obtain ⟨j, hj1, hj2⟩ := hx
                refine ⟨b j, ?_, Nonempty.elim hne fun _ ↦ hj2⟩
                use j
              · intro x hx
                obtain ⟨j, ⟨j', hj'1, hj'2⟩, hj⟩ := hx
                use j', hj'1
                rw [hj'2, ← hj]
                rfl
            rw [this]
            have : {(b i : V)} = W.subtype '' {b i} := by
              exact Eq.symm Set.image_singleton
            rw [this]
            have : {b j | j : ι} = {b j | j ≠ i} ∪ {b i} := by
              apply le_antisymm
              · intro x hx
                simp only [Subtype.exists, Set.mem_ofPred_eq, ne_eq, Set.union_singleton,
                  Set.mem_insert_iff] at ⊢ hx
                obtain ⟨a, ha1, ha2, ha3⟩ := hx
                rw [or_iff_not_imp_left]
                intro hx
                refine ⟨a, ha1, (Set.mem_of_subset_of_mem (fun t a ↦ a) ha2), ?_, ha3⟩
                contrapose hx
                rw [← ha3, hx]
              · intro x hx
                rw [Set.mem_union] at hx
                rcases hx with h | h
                · obtain ⟨j, _, h⟩ := h
                  use j, h
                · simp only [Set.mem_singleton_iff] at h
                  use i, h.symm
            rw [this]
            exact Eq.symm (Set.image_union ⇑W.subtype {x | ∃ j, j ≠ i ∧ b j = x} {b i})
          rw [this]
          rw [Submodule.span_image (Submodule.subtype W)]
          simp only [Subtype.exists, Submodule.mem_map, Submodule.subtype_apply, exists_and_right,
            exists_eq_right]
          use hv
          have : {x | ∃ a, ∃ (b_1 : a ∈ W) (b_2 : ⟨a, b_1⟩ ∈ ι), b ⟨⟨a, b_1⟩, b_2⟩ = x} = Set.range b := by
            apply le_antisymm
            · intro x hx
              simp only [Set.mem_range, Subtype.exists]
              exact hx
            · intro x hx
              simp only [Set.mem_range, Subtype.exists] at hx
              exact hx
          rw [this]
          exact Module.Basis.mem_span b ⟨v, (Iff.of_eq (Eq.refl (v ∈ W))).mpr hv⟩
      have : v ∈ U ⊔ (Submodule.span F ({(b i : V)} : Set V)) := by
        rw [this]
        exact (Submodule.mem_toAddSubgroup W).mp hv
      rw [Submodule.mem_sup] at this
      obtain ⟨u, hu, w, hw, hadd⟩ := this
      rw [Submodule.mem_span_singleton] at hw
      obtain ⟨k, hk⟩ := hw
      rw [← hadd, smul_add, sub_smul, sub_smul, hy , hy', ← hk, smul_comm,  hy2, smul_comm,
        hy'2, sub_self, sub_self, zero_add]
      all_goals exact hu
    let T : Module.End A V := {
      toFun := Tf
      map_add' := by
        intro v₁ v₂
        obtain ⟨hf₁, hf₁'⟩ :=  Classical.choose_spec (hap v₁)
        set f₁ := Classical.choose (hap v₁)
        obtain ⟨hf₂, hf₂'⟩ :=  Classical.choose_spec (hap v₂)
        set f₂ := Classical.choose (hap v₂)
        rw [← huni f₁ hf₁ v₁ hf₁', ← huni f₂ hf₂ v₂ hf₂', ← add_smul]
        apply (huni (f₁ + f₂) ((Submodule.add_mem_iff_left N hf₂).mpr hf₁) (v₁ + v₂) ?_).symm
        rw [add_smul, hf₁', hf₂']
      map_smul' := by
        intro g v
        obtain ⟨hf, hf'⟩ :=  Classical.choose_spec (hap v)
        set f := Classical.choose (hap v)
        rw [RingHom.id_apply, ← huni f hf v hf', ← mul_smul]
        apply (huni (g * f) (Ideal.mul_mem_left N g hf) (g •  v) ?_).symm
        rw [mul_smul, hf']
    }
    obtain ⟨k, hk⟩ := hs T
    have (y : A) (hy : y ∈ N) : y • u = T (y • (b i : V)) := huni y hy (y • (b i : V)) rfl
    rw [← hk] at this
    simp only [LinearMap.map_smul_of_tower, Module.algebraMap_end_apply] at this
    have (y : A) (hy : y ∈ N) : y • (u - k • (b i : V)) = 0 := by
      rw[smul_sub, this y hy, sub_self]
    apply hN at this
    apply hle at this
    apply (Submodule.sub_mem_iff_left W this).mp
    rw [← sub_add, sub_self, zero_add]
    apply Submodule.smul_mem
    exact Submodule.coe_mem (b i)
  have hap (W : Submodule F V) : ∀ u ∉ W, ∀ v : V, ∃ y : A, (∀ w ∈ W, y • w = 0) ∧ (y • u = v) := by
    intro u hu v
    obtain ⟨x, hx1, hx2⟩ := this (Module.finrank F W) W rfl u hu
    let I : Submodule A V := {
      carrier := {(z * x) • u | z : A}
      add_mem' := by
        intro v₁ v₂ hv₁ hv₂
        rw [Set.mem_ofPred_eq] at hv₁ hv₂ ⊢
        obtain ⟨z₁, hz₁⟩ := hv₁
        obtain ⟨z₂, hz₂⟩ := hv₂
        exact ⟨z₁ + z₂, by rw [add_mul, add_smul, hz₁, hz₂]⟩
      zero_mem' := ⟨0, by rw [zero_mul, zero_smul]⟩
      smul_mem' := by
        intro a v hv
        rw [Set.mem_ofPred_eq] at hv ⊢
        obtain ⟨z, hz⟩ := hv
        use a * z
        rw [mul_assoc, mul_smul, hz]
    }
    have : I ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨x • u, ⟨1, by rw [one_mul]⟩, hx2⟩
    have : I = ⊤ := (inst.eq_bot_or_eq_top I).resolve_left this
    have : v ∈ I := this ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := this
    refine ⟨a * x, fun w hw ↦ ?_, ha⟩
    rw [mul_smul, hx1, smul_zero]
    exact hw
  intro f
  let b := Module.Basis.ofVectorSpace F V
  set ι := Module.Basis.ofVectorSpaceIndex F V
  let W : ι → Submodule F V := fun i ↦ Submodule.span F {b j | j ≠ i}
  have (i : ι) : b i ∉ W i := by
    have := Module.Basis.linearIndependent b
    rw [linearIndependent_iff_notMem_span] at this
    have he : {b j | j ≠ i}  = b '' (Set.univ \ {i}) := by
      ext x
      simp_all only [ne_eq, Module.Basis.self_mem_span_image, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true, implies_true,
        Subtype.exists, Set.mem_ofPred_eq, Set.mem_image, true_and, p, ι]
    unfold W
    rw [he]
    exact this i
  let y : ι → A := fun i ↦ Classical.choose (hap (W i) (b i) (this i) (f (b i)))
  have hy (i : ι) : (∀ w ∈ W i, (y i) • w = 0) ∧ (y i) • b i = f (b i) :=
    Classical.choose_spec (hap (W i) (b i) (this i) (f (b i)))
  use ∑ i : ι, y i
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (Module.Basis.span_eq b)]
  simp only [jacobson_density_mapping, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Subtype.forall, Set.mem_range, Subtype.exists,
    forall_exists_index]
  intro _ i' hi rfl
  set i : ι := ⟨i', hi⟩
  rw [Finset.sum_smul]
  have : (fun (j : ι) ↦ y j • b i) = Finsupp.single i (f (b i)) := by
    ext j
    by_cases! h : (i = j)
    · rw [h, Finsupp.single_eq_same, (hy j).2]
    · have : b i ∈ W j := by
        apply Submodule.subset_span
        simp only [ne_eq, Subtype.exists, Set.mem_ofPred_eq]
        exact ⟨i.1, i.2, by simp only [Subtype.coe_eta, h, not_false_eq_true, and_self]⟩
      rw [(hy j).1 (b i) this]
      exact (Finsupp.single_eq_of_ne h.symm).symm
  rw [this]
  simp only [Finsupp.univ_sum_single_apply]


public theorem _root_.AlgebraicClosure.jacobson_density_condition
    {F : Type*} [Field F] [IsAlgClosed F]
    {A : Type*} [Ring A] [Algebra F A]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Module A V] [IsScalarTower F A V] [IsSimpleModule A V] :
    Function.Surjective (algebraMap F (Module.End A V)) := by
  let : DecidableEq (Module.End A V) := Classical.typeDecidableEq (Module.End A V)
  let : DivisionRing (Module.End A V) := Module.End.instDivisionRing
  let : FiniteDimensional F (Module.End F V) := Module.IsNoetherian.finite F (Module.End F V)
  let : FiniteDimensional F (Module.End A V) :=
    let f : Module.End A V →ₗ[F] Module.End F V := {
      toFun := fun g => g
      map_add' := fun x y ↦ LinearMap.restrictScalars_add x y
      map_smul' := fun m x ↦ LinearMap.restrictScalars_smul m x
    }
    have h : Function.Injective f := fun g h he => by
      ext v
      have : f g v = f h v := by rw [he]
      exact this
    FiniteDimensional.of_injective f h
  let D := (Module.End A V)
  intro d
  let L := Algebra.adjoin F {d}
  let d' : L := ⟨d, Algebra.self_mem_adjoin_singleton F d⟩
  let L' := Algebra.adjoin F {d'}
  have : L'.IsAlgebraic := by
    rw [Algebra.isAlgebraic_adjoin_singleton_iff]
    exact Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (IsAlgebraic.of_finite F d)
  let := Algebra.IsIntegral.of_finite F ↥L'
  obtain ⟨a, ha⟩ := (@IsAlgClosed.algebraMap_bijective_of_isIntegral F L' _ _ _ _ _ _).2 ⟨d', Algebra.self_mem_adjoin_singleton F d'⟩
  use a
  calc
  (algebraMap F (Module.End A V)) a = (algebraMap F L') a := by rfl
  _ = _ := by rw [ha]

public theorem jacobson_density_surjective_isAlgClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {A : Type*} [Ring A] [Algebra F A]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Module A V] [IsScalarTower F A V] [IsSimpleModule A V] :
    Function.Surjective (jacobson_density_mapping F A V) :=
  jacobson_density_surjective AlgebraicClosure.jacobson_density_condition


set_option backward.isDefEq.respectTransparency false in
public theorem adjoin_univ_iff_surjective
    {F : Type*} [Field F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    Algebra.adjoin F (Set.range ρ) = ⊤ ↔
    Function.Surjective ⇑(jacobson_density_mapping F F[G] ρ.asModule) := by
  have : Algebra.adjoin F (Set.range ρ) = ⊤ ↔ Algebra.adjoin F (Set.range ρ) =
      (Set.univ : Set (Module.End F V)) :=
    Iff.symm (StrictMono.apply_eq_top_iff fun ⦃a b⦄ a_1 ↦ a_1)
  rw [this]
  refine ⟨fun hs f => ?_, fun hs => ?_⟩
  · let f' := ρ.asModuleEquiv.symm.comp (f.comp ρ.asModuleEquiv.toLinearMap)
    have h : f' ∈ (Set.univ : Set (Module.End F V)) := Set.mem_univ f'
    rw [← hs] at h
    simp only [SetLike.mem_coe] at h
    rw [Algebra.mem_adjoin_iff] at h
    have : (g' : Module.End F ρ.asModule) → g' ∈ Subring.closure (Set.range ⇑(algebraMap F (ρ.asModule →ₗ[F] ρ.asModule)) ∪ Set.range ⇑ρ) → ∃ x : F[G], ∀ v : ρ.asModule, x • v = g' v := by
      apply Subring.closure_induction
      · intro x hx
        simp only [Set.mem_union, Set.mem_range] at hx
        rcases hx with hx | hx
        · obtain ⟨y, hy⟩ := hx
          rw[← hy]
          use MonoidAlgebra.single 1 y
          intro v
          simp only [single_smul, map_one, Module.End.one_apply, Module.algebraMap_end_apply]
          rfl
        · obtain ⟨y, hy⟩ := hx
          rw[← hy]
          use MonoidAlgebra.single y 1
          intro v
          simp only [single_smul, one_smul]
          rfl
      · exact ⟨0, by simp only [zero_smul, LinearMap.zero_apply, implies_true]⟩
      · exact ⟨1, by simp only [one_smul, Module.End.one_apply, implies_true]⟩
      · intro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
        use a + b
        intro _
        rw [add_smul, ha, hb, LinearMap.add_apply]
      · intro x hx ⟨a, ha⟩
        use -a
        intro _
        rw [neg_smul, ha, LinearMap.neg_apply]
      · intro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
        use a * b
        intro _
        rw [mul_smul, hb, ha, Module.End.mul_apply]
    obtain ⟨x, hx⟩ := this f' h
    exact ⟨x, LinearMap.ext hx⟩
  · refine Set.eq_univ_iff_forall.mpr (fun f => ?_)
    simp only [SetLike.mem_coe]
    let f' := ρ.asModuleEquiv.symm.comp (f.comp ρ.asModuleEquiv.toLinearMap)
    let π : F[G] →ₗ[F] Module.End F ρ.asModule := {
      toFun := fun x => {
        toFun := fun v => x • v
        map_add' := fun y z ↦ DistribMulAction.smul_add x y z
        map_smul' := fun m y ↦ smul_comm x m y
      }
      map_add' := fun x y => by
        ext v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, add_smul]
      map_smul' := fun r x => by
        ext v
        simp only [smul_assoc, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply]
    }
    obtain ⟨x, hx⟩ := hs f'
    have hx : π x = f':= by
      rw [← hx]
      rfl
    have : f = ρ.asModuleEquiv ∘ₗ π x ∘ₗ ρ.asModuleEquiv.symm.toLinearMap := by
      rw [hx]
      rfl
    rw [this]
    let π' : F[G] →ₗ[F] Module.End F V := {
      toFun := fun x => ρ.asModuleEquiv.comp ((π x).comp ρ.asModuleEquiv.symm.toLinearMap)
      map_add' := fun x y => by
        ext v
        simp only [map_add, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.add_apply]
      map_smul' := fun r x => by
        ext v
        simp only [map_smul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.smul_apply, RingHom.id_apply]
    }
    let p : F[G] → Prop := fun x => π' x ∈ Algebra.adjoin F (Set.range ⇑ρ)
    apply MonoidAlgebra.induction_linear (motive := p) x
    · simp only [map_zero, zero_mem, p, π']
    · intro x y hx hy
      simp only [map_add, hx, hy, add_mem, p]
    · intro g r
      unfold p
      have : π' (MonoidAlgebra.single g r) = r • (ρ g) := by
        ext v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, single_smul, LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, map_smul,
          LinearMap.smul_apply, π', π]
        rfl
      rw [this]
      apply Subalgebra.smul_mem
      apply Algebra.mem_adjoin_of_mem
      exact Set.mem_range_self g

set_option backward.isDefEq.respectTransparency false in
public theorem irreducible_of_jacobson_density_surjective
    {F : Type*} [Field F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [inst : Nontrivial V] [Module F V]
    [inst' : FiniteDimensional F V](ρ : Representation F G V)
    (hs : Algebra.adjoin F (Set.range ρ) = ⊤) :
    IsIrreducible ρ := by
  let : Nontrivial ρ.asModule := inst
  let : FiniteDimensional F ρ.asModule := inst'
  rw [irreducible_iff_isSimpleModule_asModule]
  apply simple_of_jacobson_density_surjective (F := F)
  exact (adjoin_univ_iff_surjective ρ).mp hs

public theorem algebraMap_surj_iff_surj
    {F : Type*} [Field F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    Function.Surjective (algebraMap F (Module.End F[G] ρ.asModule)) ↔
    Function.Surjective (algebraMap F (End ρ)) := by
  refine ⟨fun h f ↦ ?_, fun h f ↦ ?_⟩
  · obtain ⟨r, hr⟩ := h (RepMap.equivLinearMapAsModule ρ ρ f)
    use r
    ext v
    have : (RepMap.equivLinearMapAsModule ρ ρ f) v = f v := rfl
    rw [← hr] at this
    exact this
  · obtain ⟨r, hr⟩ := h <| (RepMap.equivLinearMapAsModule ρ ρ).symm f
    use r
    ext v
    have : (RepMap.equivLinearMapAsModule ρ ρ).symm f v = f v := rfl
    rw [← hr] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
public theorem jacobson_density_surjective_rep
    {F : Type*} [Field F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V] [inst' :FiniteDimensional F V]
    (ρ : Representation F G V) [inst : IsIrreducible ρ]
    (hs : Function.Surjective (algebraMap F (End ρ))) :
    Algebra.adjoin F (Set.range ρ) = ⊤ := by
  let := (irreducible_iff_isSimpleModule_asModule ρ).mp inst
  let : FiniteDimensional F ρ.asModule := inst'
  rw [adjoin_univ_iff_surjective]
  rw [← algebraMap_surj_iff_surj] at hs
  exact jacobson_density_surjective hs

set_option backward.isDefEq.respectTransparency false in
public theorem jacobson_density_surjective_isAlgClosed_rep
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V] [inst' :FiniteDimensional F V]
    (ρ : Representation F G V) [inst : IsIrreducible ρ] :
    Algebra.adjoin F (Set.range ρ) = ⊤ := by
  let := (irreducible_iff_isSimpleModule_asModule ρ).mp inst
  let : FiniteDimensional F ρ.asModule := inst'
  rw [adjoin_univ_iff_surjective]
  exact jacobson_density_surjective_isAlgClosed

set_option backward.isDefEq.respectTransparency false in
public theorem surjective_of_jacobson_density_surjective_rep
    {F : Type*} [Field F]
    {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hs : Algebra.adjoin F (Set.range ρ) = ⊤) :
    Function.Surjective (algebraMap F (End ρ)) := by
  rw [adjoin_univ_iff_surjective] at hs
  rw [← algebraMap_surj_iff_surj]
  exact surjective_of_jacobson_density_surjective hs
