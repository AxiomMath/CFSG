module

public import CFSG.RankThree.Lattice.SteinbergBIE6QplusData
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFourStab

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 Matrix

@[expose] def e6SimpleOrbit (J : Set (Fin Tag.E6.rank)) (j : Fin Tag.E6.rank) :
    Set (Fin Tag.E6.rank → ℤ) :=
  {β | ∃ k : ℕ, β = (e6Delta J)^[k] (Pi.single j 1)}

@[expose] def e6Orbits (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) :
    Set (Set (Fin Tag.E6.rank → ℤ)) :=
  {O | ∃ j : Fin Tag.E6.rank, Pi.single j 1 ∈ e6Xi J i₀ ∧ O = e6SimpleOrbit J j}

@[expose] def e6RelWeyl (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) :
    Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure (setReflection '' e6Orbits J i₀)

@[expose] def e6RelLength (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank)
    (w : WeylGroup Tag.E6) : ℕ :=
  sInf {n | ∃ l : List (WeylGroup Tag.E6), l.length = n ∧
    (∀ x ∈ l, x ∈ setReflection '' e6Orbits J i₀) ∧ l.prod = w}

@[expose] def e6RootOrbit (J : Set (Fin Tag.E6.rank)) (α : Fin Tag.E6.rank → ℤ) :
    Set (Fin Tag.E6.rank → ℤ) :=
  {β | ∃ k : ℕ, β = (e6Delta J)^[k] α}

section Delta

variable (m : Fin 15)

theorem e6Delta_qp_add (x y : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (x + y) = e6Delta (e6QpSupport m) x + e6Delta (e6QpSupport m) y := by
  rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_add]

theorem e6Delta_qp_sub (x y : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (x - y) = e6Delta (e6QpSupport m) x - e6Delta (e6QpSupport m) y := by
  rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_sub]

theorem e6Delta_qp_neg (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (-x) = -e6Delta (e6QpSupport m) x := by
  rw [e6Delta_qp, e6Delta_qp, Matrix.mulVec_neg]

theorem e6Delta_qp_zsmul (c : ℤ) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (c • x) = c • e6Delta (e6QpSupport m) x := by
  rw [e6Delta_qp, e6Delta_qp, Matrix.mulVec_smul]

theorem iform_permLattice_e6Rho (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice e6Rho x) (permLattice e6Rho y) = iform x y := by
  have hB : ∀ i j, Tag.E6.symmetrizedCartan (e6Rho i) (e6Rho j) =
      Tag.E6.symmetrizedCartan i j := fun i j => by
    rw [symmetrizedCartan_E6]
    exact TwistTag.cartan_perm TwistTag.E6 i j
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp e6Rho (fun i => ∑ j, x (e6Rho.symm i) * Tag.E6.symmetrizedCartan i j *
    y (e6Rho.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e6Rho (fun j => x (e6Rho.symm (e6Rho i)) *
    Tag.E6.symmetrizedCartan (e6Rho i) j * y (e6Rho.symm j))]
  simp [hB]

theorem iform_e6Delta (J : Set (Fin Tag.E6.rank)) (x y : Fin Tag.E6.rank → ℤ) :
    iform (e6Delta J x) (e6Delta J y) = iform x y := by
  rw [e6Delta, e6Delta, ← neg_one_smul ℤ (e6Longest J • permLattice e6Rho x),
    ← neg_one_smul ℤ (e6Longest J • permLattice e6Rho y), iform_smul_left, iform_smul_right,
    iform_smul, iform_permLattice_e6Rho]
  ring

theorem e6Delta_qp_single {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6Delta (e6QpSupport m) (Pi.single j 1) = Pi.single (e6QpPerm m j) 1 := by
  rw [e6Delta_qp]
  exact (e6QpPerm_check m).2 j hj

theorem e6QpPerm_mem_iff (j : Fin Tag.E6.rank) :
    j ∈ e6QpSupport m ↔ e6QpPerm m j ∈ e6QpSupport m :=
  (e6QpPerm_check m).1 j

theorem single_one_inj {a b : Fin Tag.E6.rank}
    (h : (Pi.single a 1 : Fin Tag.E6.rank → ℤ) = Pi.single b 1) : a = b := by
  by_contra hab
  have h' := congrFun h a
  simp [hab] at h'

theorem e6QpPerm_perm_of_mem {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6QpPerm m (e6QpPerm m j) = j := by
  have h := e6Delta_qp_involutive m (Pi.single j 1)
  rw [e6Delta_qp_single m hj, e6Delta_qp_single m ((e6QpPerm_mem_iff m j).1 hj)] at h
  exact single_one_inj h

end Delta

section Components

variable (m : Fin 15)

theorem e6Delta_eq_permLattice {x : Fin Tag.E6.rank → ℤ}
    (hx : ∀ i, i ∉ e6QpSupport m → x i = 0) :
    e6Delta (e6QpSupport m) x = permLattice (e6QpPerm m) x := by
  rw [e6Delta_qp]
  set M := toMat Tag.E6.rank (e6QpDeltaList m)
  have hcol : ∀ j ∈ e6QpSupport m, ∀ k, M k j = if k = e6QpPerm m j then 1 else 0 :=
    fun j hj k => by
      have h := congrFun ((e6QpPerm_check m).2 j hj) k
      rw [Matrix.mulVec_single_one] at h
      have h' : M k j = (Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) k := h
      rw [h', Pi.single_apply]
  funext k
  simp only [Matrix.mulVec, dotProduct, permLattice, Function.comp_apply]
  rw [Finset.sum_eq_single ((e6QpPerm m).symm k)]
  · by_cases hk : (e6QpPerm m).symm k ∈ e6QpSupport m
    · rw [hcol _ hk, Equiv.apply_symm_apply]
      simp
    · rw [hx _ hk, mul_zero]
  · intro j _ hj
    by_cases hjJ : j ∈ e6QpSupport m
    · have hne : k ≠ e6QpPerm m j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
      rw [hcol j hjJ]
      simp [hne]
    · rw [hx j hjJ, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cartan_symm_E6 (a b : Fin Tag.E6.rank) : Tag.E6.cartan b a = Tag.E6.cartan a b := by
  have h := symmetrizedCartan_symm Tag.E6 a b
  rw [symmetrizedCartan_E6] at h
  exact h.symm

theorem iform_single_single_E6' (a b : Fin Tag.E6.rank) :
    iform (Pi.single a 1 : Fin Tag.E6.rank → ℤ) (Pi.single b 1) = Tag.E6.cartan a b := by
  rw [iform_single_left]
  have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
  simp [hd, Pi.single_apply]

theorem cartan_e6QpPerm {a b : Fin Tag.E6.rank} (ha : a ∈ e6QpSupport m)
    (hb : b ∈ e6QpSupport m) :
    Tag.E6.cartan (e6QpPerm m a) (e6QpPerm m b) = Tag.E6.cartan a b := by
  rw [← iform_single_single_E6', ← iform_single_single_E6', ← e6Delta_qp_single m ha,
    ← e6Delta_qp_single m hb, iform_e6Delta]

theorem e6JAdj_symm {J : Set (Fin Tag.E6.rank)} {a b : Fin Tag.E6.rank} (h : e6JAdj J a b) :
    e6JAdj J b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [cartan_symm_E6]; exact h.2.2.2⟩

theorem e6JAdj_e6QpPerm {a b : Fin Tag.E6.rank} (h : e6JAdj (e6QpSupport m) a b) :
    e6JAdj (e6QpSupport m) (e6QpPerm m a) (e6QpPerm m b) :=
  ⟨(e6QpPerm_mem_iff m a).1 h.1, (e6QpPerm_mem_iff m b).1 h.2.1,
    fun e => h.2.2.1 ((e6QpPerm m).injective e),
    by rw [cartan_e6QpPerm m h.1 h.2.1]; exact h.2.2.2⟩

theorem mem_e6JComponent_self (J : Set (Fin Tag.E6.rank)) (i : Fin Tag.E6.rank) :
    i ∈ e6JComponent J i :=
  Relation.ReflTransGen.refl

theorem mem_of_mem_e6JComponent {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hi : i ∈ J) (hj : j ∈ e6JComponent J i) : j ∈ J := by
  induction hj with
  | refl => exact hi
  | tail _ h _ => exact h.2.1

theorem e6JComponent_tail {J : Set (Fin Tag.E6.rank)} {i j k : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) (h : e6JAdj J j k) : k ∈ e6JComponent J i :=
  Relation.ReflTransGen.tail hj h

theorem e6JComponent_symm {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) : i ∈ e6JComponent J j := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.head (e6JAdj_symm h) ih

theorem e6JComponent_eq {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) : e6JComponent J j = e6JComponent J i := by
  ext k
  constructor
  · intro hk
    exact Relation.ReflTransGen.trans hj hk
  · intro hk
    exact Relation.ReflTransGen.trans (e6JComponent_symm hj) hk

theorem e6QpPerm_mem_e6JComponent {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent (e6QpSupport m) i) :
    e6QpPerm m j ∈ e6JComponent (e6QpSupport m) (e6QpPerm m i) := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (e6JAdj_e6QpPerm m h)

theorem e6JComponent_eq_of_adj {i i' a b : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m)
    (hi' : i' ∈ e6QpSupport m) (ha : a ∈ e6JComponent (e6QpSupport m) i)
    (hb : b ∈ e6JComponent (e6QpSupport m) i') (h : a = b ∨ Tag.E6.cartan a b ≠ 0) :
    e6JComponent (e6QpSupport m) i = e6JComponent (e6QpSupport m) i' := by
  have hbi : b ∈ e6JComponent (e6QpSupport m) i := by
    by_cases hab : a = b
    · exact hab ▸ ha
    · have h' := h.resolve_left hab
      exact e6JComponent_tail ha ⟨mem_of_mem_e6JComponent hi ha,
        mem_of_mem_e6JComponent hi' hb, hab, h'⟩
  rw [← e6JComponent_eq hbi]
  exact e6JComponent_eq hb

end Components

section Xi

variable (m : Fin 15)

theorem isRoot_e6Delta (J : Set (Fin Tag.E6.rank)) {x : Fin Tag.E6.rank → ℤ}
    (hx : IsRoot Tag.E6 x) : IsRoot Tag.E6 (e6Delta J x) :=
  IsRoot.neg (IsRoot.smul (IsRoot.permLattice (fun i j => TwistTag.cartan_perm TwistTag.E6 i j) hx)
    _)

theorem e6Delta_qp_iterate (k : ℕ) (x : Fin Tag.E6.rank → ℤ) :
    (e6Delta (e6QpSupport m))^[k] x = if Even k then x else e6Delta (e6QpSupport m) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hk : Even k
    · rw [ite_eq_left hk, ite_eq_right (Nat.not_even_iff_odd.2 hk.add_one)]
    · rw [ite_eq_right hk, ite_eq_left (Nat.not_odd_iff_even.1 fun h => hk (by
        rcases h with ⟨r, hr⟩
        exact ⟨r, by omega⟩)), e6Delta_qp_involutive]

theorem mem_parabolicRoots_of_support {S : Set (Fin Tag.E6.rank)} {x : Fin Tag.E6.rank → ℤ}
    (hx : x ∈ parabolicRoots Tag.E6 S) {k : Fin Tag.E6.rank} (hk : x k ≠ 0) : k ∈ S := by
  by_contra h
  exact hk (hx.2 k h)

theorem e6Delta_image_parabolicRoots {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m) :
    e6Delta (e6QpSupport m) '' parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) i₀) =
      parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m i₀)) := by
  have key : ∀ {a : Fin Tag.E6.rank}, a ∈ e6QpSupport m → ∀ x ∈ parabolicRoots Tag.E6
      (e6JComponent (e6QpSupport m) a), e6Delta (e6QpSupport m) x ∈
        parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m a)) := by
    intro a ha x hx
    have hxJ : ∀ i, i ∉ e6QpSupport m → x i = 0 := fun i hi =>
      hx.2 i fun hic => hi (mem_of_mem_e6JComponent ha hic)
    refine ⟨isRoot_e6Delta _ hx.1, fun k hk => ?_⟩
    rw [e6Delta_eq_permLattice m hxJ, permLattice, Function.comp_apply]
    by_contra hne
    have hmem := mem_parabolicRoots_of_support hx hne
    have := e6QpPerm_mem_e6JComponent m hmem
    rw [Equiv.apply_symm_apply] at this
    exact hk this
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact key hi₀ x hx
  · intro hy
    have hπ := (e6QpPerm_mem_iff m i₀).1 hi₀
    have h := key hπ y hy
    rw [e6QpPerm_perm_of_mem m hi₀] at h
    exact ⟨_, h, e6Delta_qp_involutive m y⟩

theorem e6Xi_eq {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m) :
    e6Xi (e6QpSupport m) i₀ = parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) i₀) ∪
      parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m i₀)) := by
  rw [← e6Delta_image_parabolicRoots m hi₀]
  ext y
  simp only [e6Xi, Set.mem_iUnion, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨k, x, hx, rfl⟩
    rw [e6Delta_qp_iterate]
    split_ifs
    · exact Or.inl hx
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (hy | ⟨x, hx, rfl⟩)
    · exact ⟨0, y, hy, rfl⟩
    · exact ⟨1, x, hx, rfl⟩

theorem reflect_mem_parabolicRoots_component {a b j : Fin Tag.E6.rank} (ha : a ∈ e6QpSupport m)
    (hb : b ∈ e6QpSupport m) (hj : j ∈ e6JComponent (e6QpSupport m) a) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) b)) :
    reflect Tag.E6 j γ ∈ parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) b) := by
  by_cases hK : e6JComponent (e6QpSupport m) a = e6JComponent (e6QpSupport m) b
  · refine ⟨(isRoot_reflect_iff j).2 hγ.1, fun i hi => ?_⟩
    have hij : i ≠ j := fun h => hi (hK ▸ h ▸ hj)
    rw [reflect_apply_of_ne j hij]
    exact hγ.2 i hi
  · have hc : ∑ k, Tag.E6.cartan j k * γ k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : γ k = 0
      · rw [hk, mul_zero]
      · have hkb := mem_parabolicRoots_of_support hγ hk
        by_cases hjk : Tag.E6.cartan j k = 0
        · rw [hjk, zero_mul]
        · exact absurd (e6JComponent_eq_of_adj m ha hb hj hkb (Or.inr hjk)) hK
    have : reflect Tag.E6 j γ = γ := by
      rw [reflect, hc, zero_smul, sub_zero]
    rw [this]
    exact hγ

end Xi

@[expose] def e6XiOrth (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) : Prop :=
  ∀ α ∈ e6Xi J i₀, ∀ k : ℕ, (e6Delta J)^[k] α ≠ α → iform α ((e6Delta J)^[k] α) = 0

section Orbits

variable (m : Fin 15)

theorem single_mem_parabolicRoots_iff {S : Set (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank} :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 S ↔ j ∈ S := by
  constructor
  · intro h
    exact mem_parabolicRoots_of_support h (by simp)
  · intro h
    exact ⟨isRoot_single Tag.E6 j, fun i hi => by
      have : i ≠ j := fun e => hi (e ▸ h)
      simp [this]⟩

theorem mem_e6QpSupport_of_single_mem_e6Xi {i₀ j : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) : j ∈ e6QpSupport m := by
  rw [e6Xi_eq m hi₀, Set.mem_union, single_mem_parabolicRoots_iff,
    single_mem_parabolicRoots_iff] at hj
  rcases hj with h | h
  · exact mem_of_mem_e6JComponent hi₀ h
  · exact mem_of_mem_e6JComponent ((e6QpPerm_mem_iff m i₀).1 hi₀) h

theorem e6RootOrbit_qp_eq (x : Fin Tag.E6.rank → ℤ) :
    e6RootOrbit (e6QpSupport m) x = {x, e6Delta (e6QpSupport m) x} := by
  ext y
  simp only [e6RootOrbit, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [e6Delta_qp_iterate]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem e6SimpleOrbit_qp_eq {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6SimpleOrbit (e6QpSupport m) j = {Pi.single j 1, Pi.single (e6QpPerm m j) 1} := by
  have h := e6RootOrbit_qp_eq m (Pi.single j 1)
  rw [e6Delta_qp_single m hj] at h
  exact h

theorem e6Delta_reflect {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m)
    (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (reflect Tag.E6 j x) =
      reflect Tag.E6 (e6QpPerm m j) (e6Delta (e6QpSupport m) x) := by
  have hc : ∀ (a : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ),
      ∑ k, Tag.E6.cartan a k * y k = iform (Pi.single a 1) y := fun a y => by
    rw [iform_single_left]
    have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
    rw [hd, one_mul]
  rw [reflect, reflect, e6Delta_qp_sub, e6Delta_qp_zsmul, e6Delta_qp_single m hj, hc, hc,
    ← e6Delta_qp_single m hj, iform_e6Delta]

theorem iform_single_single_e6QpPerm_of_orth {i₀ j : Fin Tag.E6.rank}
    (hi₀ : i₀ ∈ e6QpSupport m) (horth : e6XiOrth (e6QpSupport m) i₀)
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (hne : e6QpPerm m j ≠ j) :
    Tag.E6.cartan j (e6QpPerm m j) = 0 := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have h := horth _ hj 1 (by
    rw [Function.iterate_one, e6Delta_qp_single m hjJ]
    exact fun e => hne (single_one_inj e))
  rw [Function.iterate_one, e6Delta_qp_single m hjJ, iform_single_single_E6'] at h
  exact h

theorem setReflection_e6SimpleOrbit {i₀ j : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
    (horth : e6XiOrth (e6QpSupport m) i₀) (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    setReflection (e6SimpleOrbit (e6QpSupport m) j) =
      if e6QpPerm m j = j then simple Tag.E6 j
      else simple Tag.E6 j * simple Tag.E6 (e6QpPerm m j) := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  rw [e6SimpleOrbit_qp_eq m hjJ]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, hπ, Set.pair_eq_singleton]
    rw [setReflection_eq_list_prod (Set.finite_singleton _) (Set.pairwise_singleton _ _)
      (l := [Pi.single j 1]) (List.nodup_singleton _) (fun β => by simp)]
    simp [simple_eq_rootReflection]
  · rw [ite_eq_right hπ]
    have hc := iform_single_single_e6QpPerm_of_orth m hi₀ horth hj hπ
    have hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (e6QpPerm m j) 1 :=
      fun e => hπ (single_one_inj e).symm
    have hcomm : Commute (rootReflection (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
        (rootReflection (Pi.single (e6QpPerm m j) 1)) :=
      commute_rootReflection_of_iform_eq_zero (isRoot_single _ _) (isRoot_single _ _)
        (by rw [iform_single_single_E6']; exact hc)
    rw [setReflection_eq_list_prod ((Set.finite_singleton _).insert _)
      (Set.pairwise_pair.2 fun _ => ⟨hcomm, hcomm.symm⟩)
      (l := [Pi.single j 1, Pi.single (e6QpPerm m j) 1]) (by simp [hne]) (fun β => by simp)]
    simp [simple_eq_rootReflection]

end Orbits

@[expose] def e6OrbitRefl (m : Fin 15) (j : Fin Tag.E6.rank) : WeylGroup Tag.E6 :=
  if e6QpPerm m j = j then simple Tag.E6 j else simple Tag.E6 j * simple Tag.E6 (e6QpPerm m j)

section OrbitRefl

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ horth in
theorem setReflection_eq_e6OrbitRefl {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    setReflection (e6SimpleOrbit (e6QpSupport m) j) = e6OrbitRefl m j :=
  setReflection_e6SimpleOrbit m hi₀ horth hj

theorem e6OrbitRefl_smul (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    e6OrbitRefl m j • x =
      if e6QpPerm m j = j then reflect Tag.E6 j x
      else reflect Tag.E6 j (reflect Tag.E6 (e6QpPerm m j) x) := by
  rw [e6OrbitRefl]
  split_ifs
  · rw [simple_smul]
  · rw [mul_smul, simple_smul, simple_smul]

theorem reflect_single_of_cartan_eq_zero {a b : Fin Tag.E6.rank} (h : Tag.E6.cartan a b = 0) :
    reflect Tag.E6 a (Pi.single b 1) = Pi.single b 1 := by
  have hs : ∑ k, Tag.E6.cartan a k * (Pi.single b 1 : Fin Tag.E6.rank → ℤ) k = 0 := by
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp [h]
  rw [reflect, hs, zero_smul, sub_zero]

theorem reflect_comm_of_cartan_eq_zero {a b : Fin Tag.E6.rank} (h : Tag.E6.cartan a b = 0)
    (x : Fin Tag.E6.rank → ℤ) :
    reflect Tag.E6 a (reflect Tag.E6 b x) = reflect Tag.E6 b (reflect Tag.E6 a x) := by
  have h' : Tag.E6.cartan b a = 0 := by rw [cartan_symm_E6]; exact h
  simp only [reflect]
  have e1 : ∑ k, Tag.E6.cartan a k * (x - (∑ l, Tag.E6.cartan b l * x l) •
      (Pi.single b 1 : Fin Tag.E6.rank → ℤ)) k = ∑ k, Tag.E6.cartan a k * x k := by
    simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, h]
  have e2 : ∑ k, Tag.E6.cartan b k * (x - (∑ l, Tag.E6.cartan a l * x l) •
      (Pi.single a 1 : Fin Tag.E6.rank → ℤ)) k = ∑ k, Tag.E6.cartan b k * x k := by
    simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, h']
  rw [e1, e2]
  abel

include hi₀ horth in
theorem cartan_e6QpPerm_eq_zero {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (hne : e6QpPerm m j ≠ j) :
    Tag.E6.cartan j (e6QpPerm m j) = 0 :=
  iform_single_single_e6QpPerm_of_orth m hi₀ horth hj hne

include hi₀ horth in
theorem e6OrbitRefl_smul_single {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    e6OrbitRefl m j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = -Pi.single j 1 ∧
      e6OrbitRefl m j • (Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) =
        -Pi.single (e6QpPerm m j) 1 := by
  rw [e6OrbitRefl_smul, e6OrbitRefl_smul]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, ite_eq_left hπ, hπ, reflect_single_self]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hπ, ite_eq_right hπ]
    have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ
    have hc' : Tag.E6.cartan (e6QpPerm m j) j = 0 := by rw [cartan_symm_E6]; exact hc
    rw [reflect_single_of_cartan_eq_zero hc', reflect_single_self, reflect_single_self]
    refine ⟨rfl, ?_⟩
    rw [show -(Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) =
      (-1 : ℤ) • Pi.single (e6QpPerm m j) 1 by simp]
    rw [show reflect Tag.E6 j ((-1 : ℤ) • Pi.single (e6QpPerm m j) 1) =
      (-1 : ℤ) • reflect Tag.E6 j (Pi.single (e6QpPerm m j) 1) by
        rw [← reflMat_mulVec, ← reflMat_mulVec, Matrix.mulVec_smul],
      reflect_single_of_cartan_eq_zero hc]

include hi₀ horth in
theorem e6OrbitRefl_smul_e6Delta {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (x : Fin Tag.E6.rank → ℤ) :
    e6OrbitRefl m j • e6Delta (e6QpSupport m) x =
      e6Delta (e6QpSupport m) (e6OrbitRefl m j • x) := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hπJ := (e6QpPerm_mem_iff m j).1 hjJ
  rw [e6OrbitRefl_smul, e6OrbitRefl_smul]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, ite_eq_left hπ, e6Delta_reflect m hjJ, hπ]
  · rw [ite_eq_right hπ, ite_eq_right hπ, e6Delta_reflect m hjJ, e6Delta_reflect m hπJ,
      e6QpPerm_perm_of_mem m hjJ]
    exact reflect_comm_of_cartan_eq_zero (cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ) _

theorem e6OrbitRefl_mul_self (j : Fin Tag.E6.rank) (hc : e6QpPerm m j ≠ j →
    Tag.E6.cartan j (e6QpPerm m j) = 0) : e6OrbitRefl m j * e6OrbitRefl m j = 1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, e6OrbitRefl_smul, e6OrbitRefl_smul, one_smul]
  split_ifs with hπ
  · rw [reflect_reflect]
  · rw [reflect_comm_of_cartan_eq_zero (hc hπ), reflect_reflect, reflect_reflect]

theorem e6OrbitRefl_smul_apply_of_ne (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ)
    {i : Fin Tag.E6.rank} (hij : i ≠ j) (hiπ : i ≠ e6QpPerm m j) :
    (e6OrbitRefl m j • x) i = x i := by
  rw [e6OrbitRefl_smul]
  split_ifs
  · exact reflect_apply_of_ne j hij x
  · rw [reflect_apply_of_ne j hij, reflect_apply_of_ne _ hiπ]

include hi₀ in
theorem e6OrbitRefl_smul_mem_e6Xi {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) : e6OrbitRefl m j • γ ∈ e6Xi (e6QpSupport m) i₀ := by
  have hπ₀ := (e6QpPerm_mem_iff m i₀).1 hi₀
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hπJ := (e6QpPerm_mem_iff m j).1 hjJ
  have hcomp : ∀ k, Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ →
      ∃ a ∈ e6QpSupport m, k ∈ e6JComponent (e6QpSupport m) a := fun k hk => by
    rw [e6Xi_eq m hi₀, Set.mem_union, single_mem_parabolicRoots_iff,
      single_mem_parabolicRoots_iff] at hk
    rcases hk with h | h
    · exact ⟨i₀, hi₀, h⟩
    · exact ⟨_, hπ₀, h⟩
  have hπj : Pi.single (e6QpPerm m j) 1 ∈ e6Xi (e6QpSupport m) i₀ := by
    rw [← e6Delta_qp_single m hjJ]
    rw [e6Xi_eq m hi₀] at hj ⊢
    rcases hj with h | h
    · right
      rw [← e6Delta_image_parabolicRoots m hi₀]
      exact ⟨_, h, rfl⟩
    · left
      rw [← e6Delta_image_parabolicRoots m hi₀] at h
      obtain ⟨y, hy, hye⟩ := h
      rw [← hye, e6Delta_qp_involutive]
      exact hy
  have hrefl : ∀ k, Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ → ∀ y ∈ e6Xi (e6QpSupport m) i₀,
      reflect Tag.E6 k y ∈ e6Xi (e6QpSupport m) i₀ := fun k hk y hy => by
    obtain ⟨a, ha, hka⟩ := hcomp k hk
    rw [e6Xi_eq m hi₀] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (reflect_mem_parabolicRoots_component m ha hi₀ hka hy)
    · exact Or.inr (reflect_mem_parabolicRoots_component m ha hπ₀ hka hy)
  rw [e6OrbitRefl_smul]
  split_ifs
  · exact hrefl j hj γ hγ
  · exact hrefl j hj _ (hrefl _ hπj γ hγ)

end OrbitRefl

section RelWeyl

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

@[expose] def IsE6OrbitGen (m : Fin 15) (i₀ : Fin Tag.E6.rank) (r : WeylGroup Tag.E6) : Prop :=
  ∃ j, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ ∧ r = e6OrbitRefl m j

include hi₀ horth in
theorem setReflection_image_e6Orbits :
    setReflection '' e6Orbits (e6QpSupport m) i₀ = {r | IsE6OrbitGen m i₀ r} := by
  ext r
  constructor
  · rintro ⟨O, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, setReflection_eq_e6OrbitRefl m hi₀ horth hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, setReflection_eq_e6OrbitRefl m hi₀ horth hj⟩

include hi₀ horth in
theorem IsE6OrbitGen.mul_self {r : WeylGroup Tag.E6} (hr : IsE6OrbitGen m i₀ r) : r * r = 1 := by
  obtain ⟨j, hj, rfl⟩ := hr
  exact e6OrbitRefl_mul_self m j (cartan_e6QpPerm_eq_zero m hi₀ horth hj)

include hi₀ horth in
theorem exists_list_of_mem_e6RelWeyl {w : WeylGroup Tag.E6}
    (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    ∃ l : List (WeylGroup Tag.E6), (∀ x ∈ l, IsE6OrbitGen m i₀ x) ∧ l.prod = w := by
  rw [e6RelWeyl, setReflection_image_e6Orbits m hi₀ horth] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x], by simpa using hx, by simp⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl', rfl⟩ := hy
    exact ⟨l ++ l', fun z hz => (List.mem_append.1 hz).elim (hl z) (hl' z), List.prod_append⟩
  | inv x _ hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨l.reverse, fun z hz => hl z (List.mem_reverse.1 hz), ?_⟩
    have hinv : List.map (fun x => x⁻¹) l = l := by
      conv_rhs => rw [← List.map_id l]
      exact List.map_congr_left fun z hz =>
        inv_eq_of_mul_eq_one_right ((hl z hz).mul_self m hi₀ horth)
    rw [List.prod_inv_reverse, hinv]

include hi₀ horth in
theorem IsE6OrbitGen.mem {r : WeylGroup Tag.E6} (hr : IsE6OrbitGen m i₀ r) :
    r ∈ e6RelWeyl (e6QpSupport m) i₀ := by
  refine Subgroup.subset_closure ?_
  rw [setReflection_image_e6Orbits m hi₀ horth]
  exact hr

include hi₀ horth in
theorem list_prod_mem_e6RelWeyl {l : List (WeylGroup Tag.E6)}
    (hl : ∀ x ∈ l, IsE6OrbitGen m i₀ x) : l.prod ∈ e6RelWeyl (e6QpSupport m) i₀ := by
  refine Subgroup.list_prod_mem _ fun x hx => Subgroup.subset_closure ?_
  rw [setReflection_image_e6Orbits m hi₀ horth]
  exact hl x hx

include hi₀ horth in
theorem e6RelWeyl_props {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    (∀ γ ∈ e6Xi (e6QpSupport m) i₀, w • γ ∈ e6Xi (e6QpSupport m) i₀) ∧
    (∀ x, w • e6Delta (e6QpSupport m) x = e6Delta (e6QpSupport m) (w • x)) ∧
    ∀ (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank),
      Pi.single i 1 ∉ e6Xi (e6QpSupport m) i₀ → (w • x) i = x i := by
  obtain ⟨l, hl, rfl⟩ := exists_list_of_mem_e6RelWeyl m hi₀ horth hw
  clear hw
  induction l with
  | nil => exact ⟨fun γ hγ => by simpa using hγ, fun x => by simp, fun x i _ => by simp⟩
  | cons r l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    obtain ⟨j, hj, rfl⟩ := hl r List.mem_cons_self
    have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
    refine ⟨fun γ hγ => ?_, fun x => ?_, fun x i hi => ?_⟩
    · rw [List.prod_cons, mul_smul]
      exact e6OrbitRefl_smul_mem_e6Xi m hi₀ hj (h1 γ hγ)
    · rw [List.prod_cons, mul_smul, mul_smul, h2, e6OrbitRefl_smul_e6Delta m hi₀ horth hj]
    · have hij : i ≠ j := fun e => hi (e ▸ hj)
      have hiπ : i ≠ e6QpPerm m j := by
        rintro rfl
        apply hi
        rw [← e6Delta_qp_single m hjJ]
        rw [e6Xi_eq m hi₀] at hj ⊢
        rcases hj with h | h
        · right
          rw [← e6Delta_image_parabolicRoots m hi₀]
          exact ⟨_, h, rfl⟩
        · left
          rw [← e6Delta_image_parabolicRoots m hi₀] at h
          obtain ⟨y, hy, hye⟩ := h
          rw [← hye, e6Delta_qp_involutive]
          exact hy
      rw [List.prod_cons, mul_smul, e6OrbitRefl_smul_apply_of_ne m j _ hij hiπ, h3 x i hi]

include hi₀ horth in
theorem exists_height_neg_of_mem_e6RelWeyl {w : WeylGroup Tag.E6}
    (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) (hne : w ≠ 1) :
    ∃ j, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ ∧
      height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 := by
  by_contra! h
  apply hne
  have hw' := inv_mem hw
  have h3 := (e6RelWeyl_props m hi₀ horth hw').2.2
  refine inv_eq_one.1 (eq_one_of_forall_height_pos fun i => ?_)
  have hr := IsRoot.smul (isRoot_single Tag.E6 i) w⁻¹
  by_cases hi : Pi.single i 1 ∈ e6Xi (e6QpSupport m) i₀
  · exact lt_of_le_of_ne (h i hi) hr.height_ne_zero.symm
  · have hc : (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) i = 1 := by
      rw [h3 _ i hi]
      simp
    rcases IsRoot.height_pos_or_neg hr with hp | hn
    · exact hp
    · have := ((IsRoot.height_neg_iff hr).1 hn) i
      omega

end RelWeyl

open _root_.Classical in
@[expose] def e6XiPos (m : Fin 15) (i₀ : Fin Tag.E6.rank) : Finset (Fin Tag.E6.rank → ℤ) :=
  (rootFinset Tag.E6).filter fun γ => γ ∈ e6Xi (e6QpSupport m) i₀ ∧ 0 < height γ

open _root_.Classical in
@[expose] def e6XiWt (m : Fin 15) (γ : Fin Tag.E6.rank → ℤ) : ℕ :=
  if e6Delta (e6QpSupport m) γ = γ then 2 else 1

open _root_.Classical in
@[expose] def e6XiS (m : Fin 15) (i₀ : Fin Tag.E6.rank) (w : WeylGroup Tag.E6) : ℕ :=
  ∑ γ ∈ e6XiPos m i₀, if height (w • γ) < 0 then e6XiWt m γ else 0

section Weights

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ in
theorem isRoot_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    IsRoot Tag.E6 γ := by
  rw [e6Xi_eq m hi₀] at hγ
  rcases hγ with h | h
  · exact h.1
  · exact h.1

include hi₀ in
theorem support_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    ∀ i, i ∉ e6QpSupport m → γ i = 0 := by
  have hπ₀ := (e6QpPerm_mem_iff m i₀).1 hi₀
  rw [e6Xi_eq m hi₀] at hγ
  intro i hi
  rcases hγ with h | h
  · exact h.2 i fun hc => hi (mem_of_mem_e6JComponent hi₀ hc)
  · exact h.2 i fun hc => hi (mem_of_mem_e6JComponent hπ₀ hc)

include hi₀ in
theorem neg_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    -γ ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hγ ⊢
  rcases hγ with h | h
  · exact Or.inl ⟨IsRoot.neg h.1, fun i hi => by simp [h.2 i hi]⟩
  · exact Or.inr ⟨IsRoot.neg h.1, fun i hi => by simp [h.2 i hi]⟩

include hi₀ in
theorem e6Delta_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    e6Delta (e6QpSupport m) γ ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hγ ⊢
  rcases hγ with h | h
  · right
    rw [← e6Delta_image_parabolicRoots m hi₀]
    exact ⟨_, h, rfl⟩
  · left
    rw [← e6Delta_image_parabolicRoots m hi₀] at h
    obtain ⟨y, hy, hye⟩ := h
    rw [← hye, e6Delta_qp_involutive]
    exact hy

include hi₀ in
theorem height_e6Delta_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) : height (e6Delta (e6QpSupport m) γ) = height γ := by
  rw [e6Delta_eq_permLattice m (support_of_mem_e6Xi m hi₀ hγ), height_permLattice]

include hi₀ in
theorem mem_e6XiPos {γ : Fin Tag.E6.rank → ℤ} :
    γ ∈ e6XiPos m i₀ ↔ γ ∈ e6Xi (e6QpSupport m) i₀ ∧ 0 < height γ := by
  classical
  rw [e6XiPos, Finset.mem_filter, mem_rootFinset]
  exact ⟨fun h => h.2, fun h => ⟨isRoot_of_mem_e6Xi m hi₀ h.1, h⟩⟩

theorem e6XiWt_neg (γ : Fin Tag.E6.rank → ℤ) : e6XiWt m (-γ) = e6XiWt m γ := by
  classical
  simp only [e6XiWt, e6Delta_qp_neg, neg_inj]

include hi₀ horth in
theorem e6XiWt_smul {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀)
    (γ : Fin Tag.E6.rank → ℤ) : e6XiWt m (w • γ) = e6XiWt m γ := by
  classical
  simp only [e6XiWt, ← (e6RelWeyl_props m hi₀ horth hw).2.1, smul_left_cancel_iff]

include hi₀ horth in
theorem height_inv_smul_e6QpPerm {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀)
    {j : Fin Tag.E6.rank} (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    height (w⁻¹ • (Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ)) =
      height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hw' := inv_mem hw
  rw [← e6Delta_qp_single m hjJ, (e6RelWeyl_props m hi₀ horth hw').2.1,
    height_e6Delta_of_mem_e6Xi m hi₀ ((e6RelWeyl_props m hi₀ horth hw').1 _ hj)]

include hi₀ in
theorem single_e6QpPerm_mem_e6Xi {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    Pi.single (e6QpPerm m j) 1 ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [← e6Delta_qp_single m (mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj)]
  exact e6Delta_mem_e6Xi m hi₀ hj

theorem sum_e6XiWt_orbit (j : Fin Tag.E6.rank) (hj : j ∈ e6QpSupport m) :
    ∑ β ∈ ({Pi.single j 1, Pi.single (e6QpPerm m j) 1} : Finset (Fin Tag.E6.rank → ℤ)),
      e6XiWt m β = 2 := by
  classical
  by_cases hπ : e6QpPerm m j = j
  · rw [hπ, Finset.pair_eq_singleton, Finset.sum_singleton, e6XiWt, e6Delta_qp_single m hj, hπ,
      ite_eq_left rfl]
  · have hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (e6QpPerm m j) 1 :=
      fun e => hπ (single_one_inj e).symm
    rw [Finset.sum_pair hne, e6XiWt, e6XiWt, e6Delta_qp_single m hj,
      e6Delta_qp_single m ((e6QpPerm_mem_iff m j).1 hj), e6QpPerm_perm_of_mem m hj,
      ite_eq_right hne.symm, ite_eq_right hne]

include hi₀ horth in
theorem height_e6OrbitRefl_smul_pos {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) (hpos : 0 < height γ) (h1 : γ ≠ Pi.single j 1)
    (h2 : γ ≠ Pi.single (e6QpPerm m j) 1) : 0 < height (e6OrbitRefl m j • γ) := by
  have hr := isRoot_of_mem_e6Xi m hi₀ hγ
  rw [e6OrbitRefl_smul]
  split_ifs with hπ
  · exact height_reflect_pos hr hpos h1
  · have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ
    have hc' : Tag.E6.cartan (e6QpPerm m j) j = 0 := by rw [cartan_symm_E6]; exact hc
    have hr' := (isRoot_reflect_iff (e6QpPerm m j)).2 hr
    refine height_reflect_pos hr' (height_reflect_pos hr hpos h2) fun e => h1 ?_
    rw [← reflect_reflect Tag.E6 (e6QpPerm m j) γ, e, reflect_single_of_cartan_eq_zero hc']

end Weights

section Step

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ horth in
theorem e6XiS_step {j : Fin Tag.E6.rank} (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀)
    {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    (0 < height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) →
      e6XiS m i₀ (e6OrbitRefl m j * w) = e6XiS m i₀ w + 2) ∧
    (height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 →
      e6XiS m i₀ (e6OrbitRefl m j * w) + 2 = e6XiS m i₀ w) := by
  classical
  set R := e6OrbitRefl m j with hRdef
  set O : Finset (Fin Tag.E6.rank → ℤ) := {Pi.single j 1, Pi.single (e6QpPerm m j) 1} with hO
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hπj := single_e6QpPerm_mem_e6Xi m hi₀ hj
  obtain ⟨hR1, hR2⟩ := e6OrbitRefl_smul_single m hi₀ horth hj
  have hheq := height_inv_smul_e6QpPerm m hi₀ horth hw hj
  have hw' := inv_mem hw
  have hWΞ := (e6RelWeyl_props m hi₀ horth hw).1
  have hWΞ' := (e6RelWeyl_props m hi₀ horth hw').1
  have hmemO : ∀ β, β ∈ O ↔ β = Pi.single j 1 ∨ β = Pi.single (e6QpPerm m j) 1 := fun β => by
    simp [O]
  have hOΞ : ∀ β ∈ O, β ∈ e6Xi (e6QpSupport m) i₀ := fun β hβ => by
    rcases (hmemO β).1 hβ with rfl | rfl
    exacts [hj, hπj]
  have hRO : ∀ β ∈ O, R • β = -β := fun β hβ => by
    rcases (hmemO β).1 hβ with rfl | rfl
    exacts [hR1, hR2]
  have hhO : ∀ β ∈ O, height β = 1 := fun β hβ => by
    rcases (hmemO β).1 hβ with rfl | rfl <;> exact height_single _
  have hsign : ∀ β ∈ O, height (w⁻¹ • β) = height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
    fun β hβ => by
      rcases (hmemO β).1 hβ with rfl | rfl
      · rfl
      · exact hheq
  have hpt : ∀ β ∈ e6Xi (e6QpSupport m) i₀, β ∉ O → -β ∉ O →
      (height (R • β) < 0 ↔ height β < 0) := fun β hβ h1 h2 => by
    have hr := isRoot_of_mem_e6Xi m hi₀ hβ
    rcases IsRoot.height_pos_or_neg hr with hp | hn
    · have := height_e6OrbitRefl_smul_pos m hi₀ horth hj hβ hp (fun e => h1 (by simp [O, e]))
        (fun e => h1 (by simp [O, e]))
      rw [← hRdef] at this
      exact ⟨fun h => by omega, fun h => by omega⟩
    · have hnβ := neg_mem_e6Xi m hi₀ hβ
      have hp' : 0 < height (-β) := by rw [height_neg]; omega
      have := height_e6OrbitRefl_smul_pos m hi₀ horth hj hnβ hp' (fun e => h2 (by simp [O, e]))
        (fun e => h2 (by simp [O, e]))
      rw [← hRdef, smul_neg, height_neg] at this
      exact ⟨fun _ => hn, fun _ => by omega⟩
  have hS : ∀ v : WeylGroup Tag.E6, e6XiS m i₀ v =
      ∑ γ ∈ e6XiPos m i₀, if height (v • γ) < 0 then e6XiWt m γ else 0 := fun v => rfl
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · have hposO : ∀ β ∈ O, 0 < height (w⁻¹ • β) := fun β hβ => by rw [hsign β hβ]; exact hpos
    have hpw : ∀ γ ∈ e6XiPos m i₀, (if height ((R * w) • γ) < 0 then e6XiWt m γ else 0) =
        (if height (w • γ) < 0 then e6XiWt m γ else 0) +
          (if w • γ ∈ O then e6XiWt m γ else 0) := fun γ hγ => by
      obtain ⟨hγΞ, hγp⟩ := (mem_e6XiPos m hi₀).1 hγ
      have hβΞ := hWΞ γ hγΞ
      rw [mul_smul]
      by_cases h1 : w • γ ∈ O
      · rw [hRO _ h1, height_neg, hhO _ h1, ite_eq_left h1]
        simp
      · by_cases h2 : -(w • γ) ∈ O
        · exfalso
          have := hposO _ h2
          rw [smul_neg, inv_smul_smul, height_neg] at this
          omega
        · rw [ite_eq_right h1, add_zero]
          simp only [hpt _ hβΞ h1 h2]
    have hbij : ∑ γ ∈ e6XiPos m i₀, (if w • γ ∈ O then e6XiWt m γ else 0) = 2 := by
      rw [← Finset.sum_filter, ← sum_e6XiWt_orbit m j hjJ]
      refine Finset.sum_nbij' (fun γ => w • γ) (fun β => w⁻¹ • β) ?_ ?_ ?_ ?_ ?_
      · intro γ hγ
        exact (Finset.mem_filter.1 hγ).2
      · intro β hβ
        refine Finset.mem_filter.2 ⟨(mem_e6XiPos m hi₀).2 ⟨hWΞ' β (hOΞ β hβ), hposO β hβ⟩, ?_⟩
        rw [smul_inv_smul]
        exact hβ
      · intro γ _
        exact inv_smul_smul w γ
      · intro β _
        exact smul_inv_smul w β
      · intro γ _
        exact (e6XiWt_smul m hi₀ horth hw γ).symm
    rw [hS, hS, Finset.sum_congr rfl hpw, Finset.sum_add_distrib, hbij]
  · have hnegO : ∀ β ∈ O, height (w⁻¹ • β) < 0 := fun β hβ => by rw [hsign β hβ]; exact hneg
    have hpw : ∀ γ ∈ e6XiPos m i₀, (if height ((R * w) • γ) < 0 then e6XiWt m γ else 0) +
        (if -(w • γ) ∈ O then e6XiWt m γ else 0) =
          (if height (w • γ) < 0 then e6XiWt m γ else 0) := fun γ hγ => by
      obtain ⟨hγΞ, hγp⟩ := (mem_e6XiPos m hi₀).1 hγ
      have hβΞ := hWΞ γ hγΞ
      rw [mul_smul]
      by_cases h1 : w • γ ∈ O
      · exfalso
        have := hnegO _ h1
        rw [inv_smul_smul] at this
        omega
      · by_cases h2 : -(w • γ) ∈ O
        · have hRw : R • (w • γ) = -(w • γ) := by
            have h := hRO _ h2
            rw [smul_neg, neg_inj] at h
            exact h
          have hh := hhO _ h2
          rw [height_neg] at hh
          rw [hRw, ite_eq_left h2, height_neg, ite_eq_right (by omega), ite_eq_left (by omega),
            zero_add]
        · rw [ite_eq_right h2, add_zero]
          simp only [hpt _ hβΞ h1 h2]
    have hbij : ∑ γ ∈ e6XiPos m i₀, (if -(w • γ) ∈ O then e6XiWt m γ else 0) = 2 := by
      rw [← Finset.sum_filter, ← sum_e6XiWt_orbit m j hjJ]
      refine Finset.sum_nbij' (fun γ => -(w • γ)) (fun β => w⁻¹ • (-β)) ?_ ?_ ?_ ?_ ?_
      · intro γ hγ
        exact (Finset.mem_filter.1 hγ).2
      · intro β hβ
        refine Finset.mem_filter.2 ⟨(mem_e6XiPos m hi₀).2 ⟨hWΞ' _ (neg_mem_e6Xi m hi₀ (hOΞ β hβ)),
          ?_⟩, ?_⟩
        · rw [smul_neg, height_neg]
          have := hnegO β hβ
          omega
        · rw [smul_inv_smul, neg_neg]
          exact hβ
      · intro γ _
        simp
      · intro β _
        simp
      · intro γ _
        rw [e6XiWt_neg, e6XiWt_smul m hi₀ horth hw]
    rw [hS, hS, ← Finset.sum_congr rfl hpw, Finset.sum_add_distrib, hbij]

end Step

section LengthFormula

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ in
theorem e6XiS_one : e6XiS m i₀ 1 = 0 := by
  classical
  refine Finset.sum_eq_zero fun γ hγ => ?_
  have := ((mem_e6XiPos m hi₀).1 hγ).2
  rw [one_smul, ite_eq_right (by omega)]

include hi₀ horth in
theorem e6XiS_list_prod_le {l : List (WeylGroup Tag.E6)} (hl : ∀ x ∈ l, IsE6OrbitGen m i₀ x) :
    e6XiS m i₀ l.prod ≤ 2 * l.length := by
  induction l with
  | nil => rw [List.prod_nil, e6XiS_one m hi₀]; simp
  | cons r l ih =>
    have hl' : ∀ x ∈ l, IsE6OrbitGen m i₀ x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨j, hj, rfl⟩ := hl r List.mem_cons_self
    have hw := list_prod_mem_e6RelWeyl m hi₀ horth hl'
    obtain ⟨hA, hB⟩ := e6XiS_step m hi₀ horth hj hw
    have ih' := ih hl'
    rw [List.prod_cons, List.length_cons]
    have hr := IsRoot.smul (isRoot_single Tag.E6 j) l.prod⁻¹
    rcases IsRoot.height_pos_or_neg hr with hp | hn
    · rw [hA hp]; omega
    · have := hB hn; omega

include hi₀ horth in
theorem exists_list_e6XiS {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    ∃ l : List (WeylGroup Tag.E6), (∀ x ∈ l, IsE6OrbitGen m i₀ x) ∧ l.prod = w ∧
      2 * l.length = e6XiS m i₀ w := by
  induction hS : e6XiS m i₀ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h1 : w = 1
    · subst h1
      rw [e6XiS_one m hi₀] at hS
      exact ⟨[], by simp, rfl, by simp [← hS]⟩
    · obtain ⟨j, hj, hneg⟩ := exists_height_neg_of_mem_e6RelWeyl m hi₀ horth hw h1
      have hstep := (e6XiS_step m hi₀ horth hj hw).2 hneg
      have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m j) := ⟨j, hj, rfl⟩
      have hRw : e6OrbitRefl m j * w ∈ e6RelWeyl (e6QpSupport m) i₀ :=
        mul_mem (hgen.mem m hi₀ horth) hw
      obtain ⟨l, hl, hlp, hll⟩ := ih (e6XiS m i₀ (e6OrbitRefl m j * w)) (by omega) hRw rfl
      refine ⟨e6OrbitRefl m j :: l, fun x hx => ?_, ?_, ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hgen
        · exact hl x hx
      · rw [List.prod_cons, hlp, ← mul_assoc, hgen.mul_self m hi₀ horth, one_mul]
      · rw [List.length_cons]
        omega

include hi₀ horth in
theorem e6RelLength_eq {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    e6RelLength (e6QpSupport m) i₀ w = e6XiS m i₀ w / 2 := by
  obtain ⟨l, hl, hlp, hll⟩ := exists_list_e6XiS m hi₀ horth hw
  have hgen := setReflection_image_e6Orbits m hi₀ horth
  have hmem : e6XiS m i₀ w / 2 ∈ {n | ∃ l : List (WeylGroup Tag.E6), l.length = n ∧
      (∀ x ∈ l, x ∈ setReflection '' e6Orbits (e6QpSupport m) i₀) ∧ l.prod = w} :=
    ⟨l, by omega, fun x hx => by rw [hgen]; exact hl x hx, hlp⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro n ⟨l', rfl, hl', rfl⟩
  have := e6XiS_list_prod_le m hi₀ horth (l := l') fun x hx => by
    have := hl' x hx
    rw [hgen] at this
    exact this
  omega

include hi₀ horth in
theorem e6RelLength_e6OrbitRefl_mul {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) {w : WeylGroup Tag.E6}
    (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    (0 < height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) →
      e6RelLength (e6QpSupport m) i₀ (e6OrbitRefl m j * w) =
        e6RelLength (e6QpSupport m) i₀ w + 1) ∧
    (height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 →
      e6RelLength (e6QpSupport m) i₀ (e6OrbitRefl m j * w) + 1 =
        e6RelLength (e6QpSupport m) i₀ w) := by
  have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m j) := ⟨j, hj, rfl⟩
  have hRw : e6OrbitRefl m j * w ∈ e6RelWeyl (e6QpSupport m) i₀ :=
    mul_mem (hgen.mem m hi₀ horth) hw
  obtain ⟨hA, hB⟩ := e6XiS_step m hi₀ horth hj hw
  rw [e6RelLength_eq m hi₀ horth hw, e6RelLength_eq m hi₀ horth hRw]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hA h]
    omega
  · have := hB h
    omega

end LengthFormula

section Folded

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

theorem cartan_nonpos_E6 (a b : Fin Tag.E6.rank) : a ≠ b → Tag.E6.cartan a b ≤ 0 := by
  fin_cases a <;> fin_cases b <;> decide

theorem reflTransGen_swap_of_symm {α : Type*} {r : α → α → Prop} (h : ∀ {a b}, r a b → r b a)
    {x y : α} (hxy : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (h hbc) ih

theorem height_reflect_eq_E6 (t : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    height (reflect Tag.E6 t v) = height v - ∑ l, Tag.E6.cartan t l * v l := by
  simp only [reflect, height, Pi.sub_apply, Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply]

theorem e6SimpleOrbit_e6QpPerm {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6SimpleOrbit (e6QpSupport m) (e6QpPerm m j) = e6SimpleOrbit (e6QpSupport m) j := by
  rw [e6SimpleOrbit_qp_eq m ((e6QpPerm_mem_iff m j).1 hj), e6SimpleOrbit_qp_eq m hj,
    e6QpPerm_perm_of_mem m hj, Set.pair_comm]

theorem mem_e6Orbits_iff {O : Set (Fin Tag.E6.rank → ℤ)} :
    O ∈ e6Orbits (e6QpSupport m) i₀ ↔
      ∃ j, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ ∧ O = e6SimpleOrbit (e6QpSupport m) j :=
  Iff.rfl

include hi₀ horth in
theorem e6RelLength_mul {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ e6Orbits (e6QpSupport m) i₀)
    {w : WeylGroup Tag.E6} (hw : w ∈ e6RelWeyl (e6QpSupport m) i₀) :
    (e6RelLength (e6QpSupport m) i₀ (setReflection O * w) =
        e6RelLength (e6QpSupport m) i₀ w + 1 ↔ ∀ β ∈ O, 0 < height (w⁻¹ • β)) ∧
      (e6RelLength (e6QpSupport m) i₀ (setReflection O * w) =
          e6RelLength (e6QpSupport m) i₀ w + 1 ∨
        e6RelLength (e6QpSupport m) i₀ (setReflection O * w) + 1 =
          e6RelLength (e6QpSupport m) i₀ w) := by
  obtain ⟨j, hj, rfl⟩ := hO
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  rw [setReflection_eq_e6OrbitRefl m hi₀ horth hj]
  obtain ⟨hA, hB⟩ := e6RelLength_e6OrbitRefl_mul m hi₀ horth hj hw
  have hheq := height_inv_smul_e6QpPerm m hi₀ horth hw hj
  have hall : (∀ β ∈ e6SimpleOrbit (e6QpSupport m) j, 0 < height (w⁻¹ • β)) ↔
      0 < height (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    rw [e6SimpleOrbit_qp_eq m hjJ]
    constructor
    · intro h
      exact h _ (Set.mem_insert _ _)
    · rintro h β (rfl | rfl)
      · exact h
      · rw [hheq]
        exact h
  rw [hall]
  have hr := IsRoot.smul (isRoot_single Tag.E6 j) w⁻¹
  rcases IsRoot.height_pos_or_neg hr with hp | hn
  · exact ⟨⟨fun _ => hp, fun _ => hA hp⟩, Or.inl (hA hp)⟩
  · have := hB hn
    exact ⟨⟨fun h => by omega, fun h => absurd h (by omega)⟩, Or.inr this⟩

include hi₀ in
theorem e6Orbits_connected {O O' : Set (Fin Tag.E6.rank → ℤ)}
    (hO : O ∈ e6Orbits (e6QpSupport m) i₀) (hO' : O' ∈ e6Orbits (e6QpSupport m) i₀) :
    Relation.ReflTransGen (fun A B => A ∈ e6Orbits (e6QpSupport m) i₀ ∧
      B ∈ e6Orbits (e6QpSupport m) i₀ ∧ ∃ β ∈ A, ∃ β' ∈ B, iform β β' ≠ 0) O O' := by
  have hπ₀ := (e6QpPerm_mem_iff m i₀).1 hi₀
  have hred : ∀ {O : Set (Fin Tag.E6.rank → ℤ)}, O ∈ e6Orbits (e6QpSupport m) i₀ →
      ∃ a ∈ e6JComponent (e6QpSupport m) i₀, O = e6SimpleOrbit (e6QpSupport m) a := by
    rintro O ⟨j, hj, rfl⟩
    have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
    rw [e6Xi_eq m hi₀, Set.mem_union, single_mem_parabolicRoots_iff,
      single_mem_parabolicRoots_iff] at hj
    rcases hj with h | h
    · exact ⟨j, h, rfl⟩
    · refine ⟨e6QpPerm m j, ?_, (e6SimpleOrbit_e6QpPerm m hjJ).symm⟩
      have := e6QpPerm_mem_e6JComponent m h
      rwa [e6QpPerm_perm_of_mem m hi₀] at this
  have hmemC : ∀ a ∈ e6JComponent (e6QpSupport m) i₀,
      e6SimpleOrbit (e6QpSupport m) a ∈ e6Orbits (e6QpSupport m) i₀ := fun a ha =>
    ⟨a, by rw [e6Xi_eq m hi₀]; exact Or.inl (single_mem_parabolicRoots_iff.2 ha), rfl⟩
  have hstep : ∀ a b, a ∈ e6JComponent (e6QpSupport m) i₀ → e6JAdj (e6QpSupport m) a b →
      Relation.ReflTransGen (fun A B => A ∈ e6Orbits (e6QpSupport m) i₀ ∧
        B ∈ e6Orbits (e6QpSupport m) i₀ ∧ ∃ β ∈ A, ∃ β' ∈ B, iform β β' ≠ 0)
        (e6SimpleOrbit (e6QpSupport m) a) (e6SimpleOrbit (e6QpSupport m) b) := fun a b ha hab =>
    Relation.ReflTransGen.single ⟨hmemC a ha, hmemC b (e6JComponent_tail ha hab),
      Pi.single a 1, ⟨0, rfl⟩, Pi.single b 1, ⟨0, rfl⟩,
      by rw [iform_single_single_E6']; exact hab.2.2.2⟩
  have hfrom : ∀ a ∈ e6JComponent (e6QpSupport m) i₀,
      Relation.ReflTransGen (fun A B => A ∈ e6Orbits (e6QpSupport m) i₀ ∧
        B ∈ e6Orbits (e6QpSupport m) i₀ ∧ ∃ β ∈ A, ∃ β' ∈ B, iform β β' ≠ 0)
        (e6SimpleOrbit (e6QpSupport m) i₀) (e6SimpleOrbit (e6QpSupport m) a) := by
    intro a ha
    induction ha with
    | refl => exact Relation.ReflTransGen.refl
    | tail hb hbc ih => exact ih.trans (hstep _ _ hb hbc)
  have hsymm : ∀ {A B : Set (Fin Tag.E6.rank → ℤ)}, (A ∈ e6Orbits (e6QpSupport m) i₀ ∧
      B ∈ e6Orbits (e6QpSupport m) i₀ ∧ ∃ β ∈ A, ∃ β' ∈ B, iform β β' ≠ 0) →
      (B ∈ e6Orbits (e6QpSupport m) i₀ ∧ A ∈ e6Orbits (e6QpSupport m) i₀ ∧
        ∃ β ∈ B, ∃ β' ∈ A, iform β β' ≠ 0) := fun ⟨hA, hB, β, hβ, β', hβ', h⟩ =>
    ⟨hB, hA, β', hβ', β, hβ, by rw [iform_comm]; exact h⟩
  obtain ⟨a, ha, rfl⟩ := hred hO
  obtain ⟨b, hb, rfl⟩ := hred hO'
  have h1 := hfrom a ha
  have h2 := hfrom b hb
  exact (reflTransGen_swap_of_symm hsymm h1).trans h2

theorem sum_cartan_mul_eq_iform (a : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ) :
    ∑ k, Tag.E6.cartan a k * y k = iform (Pi.single a 1) y := by
  rw [iform_single_left]
  have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
  rw [hd, one_mul]

include hi₀ in
theorem single_mem_e6Xi_of_ne_zero {x : Fin Tag.E6.rank → ℤ} (hx : x ∈ e6Xi (e6QpSupport m) i₀)
    {k : Fin Tag.E6.rank} (hk : x k ≠ 0) : Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (single_mem_parabolicRoots_iff.2 (mem_parabolicRoots_of_support h hk))
  · exact Or.inr (single_mem_parabolicRoots_iff.2 (mem_parabolicRoots_of_support h hk))

include hi₀ horth in
theorem e6RelLength_braid {O O' : Set (Fin Tag.E6.rank → ℤ)}
    (hO : O ∈ e6Orbits (e6QpSupport m) i₀) (hO' : O' ∈ e6Orbits (e6QpSupport m) i₀)
    (hne : O ≠ O') (hadj : ∃ β ∈ O, ∃ β' ∈ O', iform β β' ≠ 0) :
    e6RelLength (e6QpSupport m) i₀ (setReflection O * setReflection O' * setReflection O) = 3 := by
  obtain ⟨j, hj, rfl⟩ := hO
  obtain ⟨k, hk, rfl⟩ := hO'
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hkJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hk
  have hadj' : Tag.E6.cartan k j ≠ 0 ∨ Tag.E6.cartan (e6QpPerm m k) j ≠ 0 := by
    obtain ⟨β, hβ, β', hβ', h⟩ := hadj
    rw [e6SimpleOrbit_qp_eq m hjJ] at hβ
    rw [e6SimpleOrbit_qp_eq m hkJ] at hβ'
    have hd : ∀ a b : Fin Tag.E6.rank, a ∈ e6QpSupport m → b ∈ e6QpSupport m →
        iform (Pi.single (e6QpPerm m a) 1 : Fin Tag.E6.rank → ℤ) (Pi.single (e6QpPerm m b) 1) =
          iform (Pi.single a 1) (Pi.single b 1) := fun a b ha hb => by
      rw [← e6Delta_qp_single m ha, ← e6Delta_qp_single m hb, iform_e6Delta]
    have hπk := (e6QpPerm_mem_iff m k).1 hkJ
    rcases hβ with rfl | rfl <;> rcases hβ' with rfl | rfl
    · left
      rw [iform_single_single_E6'] at h
      rwa [cartan_symm_E6]
    · right
      rw [iform_single_single_E6'] at h
      rwa [cartan_symm_E6]
    · right
      rw [show (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = Pi.single (e6QpPerm m (e6QpPerm m k)) 1 by
        rw [e6QpPerm_perm_of_mem m hkJ], hd j _ hjJ hπk, iform_single_single_E6'] at h
      rwa [cartan_symm_E6]
    · left
      rw [hd j k hjJ hkJ, iform_single_single_E6'] at h
      rwa [cartan_symm_E6]
  rw [setReflection_eq_e6OrbitRefl m hi₀ horth hj, setReflection_eq_e6OrbitRefl m hi₀ horth hk]
  have hgr : IsE6OrbitGen m i₀ (e6OrbitRefl m j) := ⟨j, hj, rfl⟩
  have hgr' : IsE6OrbitGen m i₀ (e6OrbitRefl m k) := ⟨k, hk, rfl⟩
  have hr := hgr.mem m hi₀ horth
  have hr' := hgr'.mem m hi₀ horth
  have hrinv : (e6OrbitRefl m j)⁻¹ = e6OrbitRefl m j :=
    inv_eq_of_mul_eq_one_right (hgr.mul_self m hi₀ horth)
  have hrinv' : (e6OrbitRefl m k)⁻¹ = e6OrbitRefl m k :=
    inv_eq_of_mul_eq_one_right (hgr'.mul_self m hi₀ horth)
  have hkO : (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 ∧
      (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (e6QpPerm m j) 1 := by
    constructor
    · intro e
      apply hne
      rw [single_one_inj e]
    · intro e
      apply hne
      rw [single_one_inj e, e6SimpleOrbit_e6QpPerm m hjJ]
  have hjO' : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single k 1 ∧
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (e6QpPerm m k) 1 := by
    constructor
    · intro e
      apply hne
      rw [single_one_inj e]
    · intro e
      apply hne
      rw [single_one_inj e, e6SimpleOrbit_e6QpPerm m hkJ]
  have h0 : e6RelLength (e6QpSupport m) i₀ 1 = 0 := by
    rw [e6RelLength_eq m hi₀ horth (one_mem _), e6XiS_one m hi₀]
  have h1 : e6RelLength (e6QpSupport m) i₀ (e6OrbitRefl m j) = 1 := by
    have := (e6RelLength_e6OrbitRefl_mul m hi₀ horth hj (one_mem _)).1 (by simp)
    rwa [mul_one, h0] at this
  have h2 : e6RelLength (e6QpSupport m) i₀ (e6OrbitRefl m k * e6OrbitRefl m j) = 2 := by
    have hpos : 0 < height ((e6OrbitRefl m j)⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) := by
      rw [hrinv]
      exact height_e6OrbitRefl_smul_pos m hi₀ horth hj hk (by simp) hkO.1 hkO.2
    rw [(e6RelLength_e6OrbitRefl_mul m hi₀ horth hk hr).1 hpos, h1]
  have hmem := e6OrbitRefl_smul_mem_e6Xi m hi₀ hk hj
  have hpos' : 0 < height (e6OrbitRefl m k • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
    height_e6OrbitRefl_smul_pos m hi₀ horth hk hj (by simp) hjO'.1 hjO'.2
  have hkj : k ≠ j := fun e => hjO'.1 (by rw [e])
  have hπkj : e6QpPerm m k ≠ j := fun e => hjO'.2 (by rw [e])
  have hn1 := cartan_nonpos_E6 k j hkj
  have hn2 := cartan_nonpos_E6 (e6QpPerm m k) j hπkj
  have hht : 2 ≤ height (e6OrbitRefl m k • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    have hs : ∀ a, ∑ l, Tag.E6.cartan a l * (Pi.single j 1 : Fin Tag.E6.rank → ℤ) l =
        Tag.E6.cartan a j := fun a => by simp [Pi.single_apply]
    rw [e6OrbitRefl_smul]
    split_ifs with hπ
    · rw [height_reflect_eq_E6, height_single, hs]
      rcases hadj' with h | h
      · omega
      · rw [hπ] at h
        omega
    · have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hk hπ
      have hs2 : ∑ l, Tag.E6.cartan k l *
          reflect Tag.E6 (e6QpPerm m k) (Pi.single j 1) l = Tag.E6.cartan k j := by
        rw [reflect, hs]
        simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, hc]
      rw [height_reflect_eq_E6, height_reflect_eq_E6, height_single, hs, hs2]
      rcases hadj' with h | h <;> omega
  have hne1 : e6OrbitRefl m k • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 :=
    fun e => by rw [e, height_single] at hht; omega
  have hne2 : e6OrbitRefl m k • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠
      Pi.single (e6QpPerm m j) 1 := fun e => by rw [e, height_single] at hht; omega
  have hpos3 : 0 < height ((e6OrbitRefl m k * e6OrbitRefl m j)⁻¹ •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    rw [_root_.mul_inv_rev, hrinv, hrinv', mul_smul]
    exact height_e6OrbitRefl_smul_pos m hi₀ horth hj hmem hpos' hne1 hne2
  rw [mul_assoc, (e6RelLength_e6OrbitRefl_mul m hi₀ horth hj (mul_mem hr' hr)).1 hpos3, h2]

include hi₀ horth in
theorem exists_smul_e6Orbit_eq {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    ∃ w ∈ e6RelWeyl (e6QpSupport m) i₀, ∃ O ∈ e6Orbits (e6QpSupport m) i₀,
      (w • ·) '' O = e6RootOrbit (e6QpSupport m) γ := by
  have himg : ∀ {j : Fin Tag.E6.rank}, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ →
      ∀ x, (e6OrbitRefl m j • ·) '' e6RootOrbit (e6QpSupport m) x =
        e6RootOrbit (e6QpSupport m) (e6OrbitRefl m j • x) := fun hj x => by
    rw [e6RootOrbit_qp_eq, e6RootOrbit_qp_eq, Set.image_pair,
      e6OrbitRefl_smul_e6Delta m hi₀ horth hj]
  have hcomp : ∀ (a b : WeylGroup Tag.E6) (S : Set (Fin Tag.E6.rank → ℤ)),
      ((a * b) • ·) '' S = (a • ·) '' ((b • ·) '' S) := fun a b S => by
    rw [Set.image_image]
    congr 1
    funext x
    rw [mul_smul]
  have hpos : ∀ n : ℕ, ∀ γ ∈ e6Xi (e6QpSupport m) i₀, height γ = n → 0 < height γ →
      ∃ w ∈ e6RelWeyl (e6QpSupport m) i₀, ∃ O ∈ e6Orbits (e6QpSupport m) i₀,
        (w • ·) '' O = e6RootOrbit (e6QpSupport m) γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hγ hn hp
      by_cases hs : ∃ j, γ = Pi.single j 1
      · obtain ⟨j, rfl⟩ := hs
        refine ⟨1, one_mem _, e6SimpleOrbit (e6QpSupport m) j, ⟨j, hγ, rfl⟩, ?_⟩
        ext x
        simp [e6SimpleOrbit, e6RootOrbit]
      · simp only [not_exists] at hs
        have hγr := isRoot_of_mem_e6Xi m hi₀ hγ
        have hδγ := e6Delta_mem_e6Xi m hi₀ hγ
        have hδr := isRoot_of_mem_e6Xi m hi₀ hδγ
        have hγnn := (IsRoot.height_pos_iff hγr).1 hp
        have hδnn := (IsRoot.height_pos_iff hδr).1
          (by rw [height_e6Delta_of_mem_e6Xi m hi₀ hγ]; exact hp)
        set q := γ + e6Delta (e6QpSupport m) γ with hq
        have hq0 : q ≠ 0 := fun h => by
          have h1 : height q = height γ + height γ := by
            rw [hq, height_add, height_e6Delta_of_mem_e6Xi m hi₀ hγ]
          have h2 : height (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [height]
          rw [h, h2] at h1
          omega
        have hexp : iform q q = ∑ k, q k * iform (Pi.single k 1) q := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← sum_cartan_mul_eq_iform, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [symmetrizedCartan_E6]
          ring
        obtain ⟨k, hk⟩ : ∃ k, 0 < q k * iform (Pi.single k 1) q := by
          by_contra! h
          have := iform_self_pos hq0
          rw [hexp] at this
          exact absurd (Finset.sum_nonpos fun k _ => h k) (not_le.2 this)
        have hqk : 0 ≤ q k := by rw [hq, Pi.add_apply]; linarith [hγnn k, hδnn k]
        have hqk' : 0 < q k := lt_of_le_of_ne hqk fun e => by rw [← e, zero_mul] at hk; omega
        have hik : 0 < iform (Pi.single k 1) q := pos_of_mul_pos_right hk hqk
        have hkΞ : Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ := by
          by_cases hγk : γ k = 0
          · refine single_mem_e6Xi_of_ne_zero m hi₀ hδγ fun e => ?_
            rw [hq, Pi.add_apply, hγk, e, add_zero] at hqk'
            exact lt_irrefl 0 hqk'
          · exact single_mem_e6Xi_of_ne_zero m hi₀ hγ hγk
        have hkJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hkΞ
        have hπkJ := (e6QpPerm_mem_iff m k).1 hkJ
        have hsplit : iform (Pi.single k 1) q = iform (Pi.single k 1) γ +
            iform (Pi.single (e6QpPerm m k) 1) γ := by
          rw [hq, iform_add_right]
          congr 1
          rw [show (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
            e6Delta (e6QpSupport m) (Pi.single (e6QpPerm m k) 1) by
              rw [e6Delta_qp_single m hπkJ, e6QpPerm_perm_of_mem m hkJ], iform_e6Delta]
        have hdec : height (e6OrbitRefl m k • γ) < height γ := by
          rw [e6OrbitRefl_smul]
          split_ifs with hπ
          · rw [height_reflect_eq_E6, sum_cartan_mul_eq_iform]
            rw [hπ] at hsplit
            omega
          · have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hkΞ hπ
            rw [height_reflect_eq_E6, height_reflect_eq_E6, sum_cartan_mul_eq_iform,
              sum_cartan_mul_eq_iform, reflect, iform_sub_right, iform_smul_right,
              iform_single_single_E6', hc, mul_zero, sub_zero]
            omega
        have hrΞ := e6OrbitRefl_smul_mem_e6Xi m hi₀ hkΞ hγ
        have hrp := height_e6OrbitRefl_smul_pos m hi₀ horth hkΞ hγ hp (hs k) (hs _)
        obtain ⟨w, hw, O, hO, hwO⟩ := ih (height (e6OrbitRefl m k • γ)).toNat (by omega)
          (e6OrbitRefl m k • γ) hrΞ (by omega) hrp
        have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m k) := ⟨k, hkΞ, rfl⟩
        refine ⟨e6OrbitRefl m k * w, mul_mem (hgen.mem m hi₀ horth) hw, O, hO, ?_⟩
        rw [hcomp, hwO, himg hkΞ, ← mul_smul, hgen.mul_self m hi₀ horth, one_smul]
  have hr := isRoot_of_mem_e6Xi m hi₀ hγ
  rcases IsRoot.height_pos_or_neg hr with hp | hn
  · exact hpos (height γ).toNat γ hγ (by omega) hp
  · have hnγ := neg_mem_e6Xi m hi₀ hγ
    obtain ⟨w, hw, O, hO, hwO⟩ := hpos (height (-γ)).toNat (-γ) hnγ
      (by rw [height_neg]; omega) (by rw [height_neg]; omega)
    obtain ⟨j, hj, rfl⟩ := hO
    have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
    have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m j) := ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := e6OrbitRefl_smul_single m hi₀ horth hj
    refine ⟨w * e6OrbitRefl m j, mul_mem hw (hgen.mem m hi₀ horth), _, ⟨j, hj, rfl⟩, ?_⟩
    rw [hcomp, e6SimpleOrbit_qp_eq m hjJ, Set.image_pair, h1, h2, Set.image_pair, smul_neg,
      smul_neg]
    rw [e6SimpleOrbit_qp_eq m hjJ, Set.image_pair, e6RootOrbit_qp_eq, e6Delta_qp_neg] at hwO
    rw [e6RootOrbit_qp_eq]
    have := congrArg (fun S : Set (Fin Tag.E6.rank → ℤ) => (fun x => -x) '' S) hwO
    simpa [Set.image_pair] using this

end Folded

end CFSG.RankThree.Lattice
