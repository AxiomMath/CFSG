module

public import CFSG.LocalAnalysis.ZStar.CharacterContradiction
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG

namespace ZStar.Helpers

@[expose] def commutatorClosure (G : Type*) [Group G] (t : G) : Subgroup G :=
  Subgroup.normalClosure (Set.range fun g : G => g * t * g⁻¹ * t⁻¹)

instance commutatorClosure_normal (G : Type*) [Group G] (t : G) :
    (commutatorClosure G t).Normal :=
  Subgroup.normalClosure_normal

theorem commutator_mem_commutatorClosure (G : Type*) [Group G] (t g : G) :
    g * t * g⁻¹ * t⁻¹ ∈ commutatorClosure G t := by
  exact Subgroup.subset_normalClosure (Set.mem_range_self g)

abbrev GroupAlgebraTwo (G : Type*) [Group G] := MonoidAlgebra (ZMod 2) G

theorem single_mul_apply_mul (G : Type*) [Group G]
    (x a : G) (e : GroupAlgebraTwo G) :
    (MonoidAlgebra.single x 1 * e).coeff (x * a) = e.coeff a := by
  simp

@[expose] def algebraStabilizer (G : Type*) [Group G] (e : GroupAlgebraTwo G) : Subgroup G where
  carrier := {g | MonoidAlgebra.single g 1 * e = e}
  one_mem' := by
    change MonoidAlgebra.single 1 1 * e = e
    ext g
    simp
  mul_mem' := by
    intro a b ha hb
    change MonoidAlgebra.single a 1 * e = e at ha
    change MonoidAlgebra.single b 1 * e = e at hb
    change MonoidAlgebra.single (a * b) 1 * e = e
    calc
      MonoidAlgebra.single (a * b) 1 * e =
          (MonoidAlgebra.single a 1 * MonoidAlgebra.single b 1) * e := by
            rw [MonoidAlgebra.single_mul_single]
            simp
      _ = MonoidAlgebra.single a 1 * (MonoidAlgebra.single b 1 * e) :=
        mul_assoc _ _ _
      _ = e := by rw [hb, ha]
  inv_mem' := by
    intro a ha
    change MonoidAlgebra.single a 1 * e = e at ha
    change MonoidAlgebra.single a⁻¹ 1 * e = e
    calc
      MonoidAlgebra.single a⁻¹ 1 * e =
          MonoidAlgebra.single a⁻¹ 1 * (MonoidAlgebra.single a 1 * e) := by
            rw [ha]
      _ = (MonoidAlgebra.single a⁻¹ 1 * MonoidAlgebra.single a 1) * e := by
        rw [mul_assoc]
      _ = e := by
        rw [MonoidAlgebra.single_mul_single]
        ext g
        simp

private theorem algebraStabilizer_normal (G : Type*) [Group G] (e : GroupAlgebraTwo G)
    (he : ∀ g : G, MonoidAlgebra.single g 1 * e = e * MonoidAlgebra.single g 1) :
    (algebraStabilizer G e).Normal := by
  constructor
  intro n hn g
  change MonoidAlgebra.single n 1 * e = e at hn
  change MonoidAlgebra.single (g * n * g⁻¹) 1 * e = e
  calc
    MonoidAlgebra.single (g * n * g⁻¹) 1 * e =
        (MonoidAlgebra.single g 1 * MonoidAlgebra.single n 1 *
          MonoidAlgebra.single g⁻¹ 1) * e := by
            rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
            simp
    _ = MonoidAlgebra.single g 1 * MonoidAlgebra.single n 1 *
          (MonoidAlgebra.single g⁻¹ 1 * e) := by simp only [mul_assoc]
    _ = MonoidAlgebra.single g 1 * MonoidAlgebra.single n 1 *
          (e * MonoidAlgebra.single g⁻¹ 1) := by rw [he]
    _ = MonoidAlgebra.single g 1 * (MonoidAlgebra.single n 1 * e) *
          MonoidAlgebra.single g⁻¹ 1 := by simp only [mul_assoc]
    _ = MonoidAlgebra.single g 1 * e * MonoidAlgebra.single g⁻¹ 1 := by rw [hn]
    _ = e * (MonoidAlgebra.single g 1 * MonoidAlgebra.single g⁻¹ 1) := by
      rw [he]
      simp only [mul_assoc]
    _ = e := by
      rw [MonoidAlgebra.single_mul_single]
      ext x
      simp

private theorem commutator_mem_algebraStabilizer (G : Type*) [Group G]
    (t g : G) (e : GroupAlgebraTwo G)
    (he : ∀ x : G, MonoidAlgebra.single x 1 * e = e * MonoidAlgebra.single x 1)
    (hte : MonoidAlgebra.single (g * t * g⁻¹) 1 * e =
      MonoidAlgebra.single t 1 * e) :
    g * t * g⁻¹ * t⁻¹ ∈ algebraStabilizer G e := by
  change MonoidAlgebra.single (g * t * g⁻¹ * t⁻¹) 1 * e = e
  calc
    MonoidAlgebra.single (g * t * g⁻¹ * t⁻¹) 1 * e =
        (MonoidAlgebra.single (g * t * g⁻¹) 1 *
          MonoidAlgebra.single t⁻¹ 1) * e := by
            rw [MonoidAlgebra.single_mul_single]
            simp
    _ = MonoidAlgebra.single (g * t * g⁻¹) 1 *
          (MonoidAlgebra.single t⁻¹ 1 * e) := by simp only [mul_assoc]
    _ = MonoidAlgebra.single (g * t * g⁻¹) 1 *
          (e * MonoidAlgebra.single t⁻¹ 1) := by rw [he]
    _ = (MonoidAlgebra.single (g * t * g⁻¹) 1 * e) *
          MonoidAlgebra.single t⁻¹ 1 := by simp only [mul_assoc]
    _ = (MonoidAlgebra.single t 1 * e) * MonoidAlgebra.single t⁻¹ 1 := by rw [hte]
    _ = MonoidAlgebra.single t 1 * (e * MonoidAlgebra.single t⁻¹ 1) := by
      simp only [mul_assoc]
    _ = MonoidAlgebra.single t 1 * (MonoidAlgebra.single t⁻¹ 1 * e) := by
      rw [he]
    _ = (MonoidAlgebra.single t 1 * MonoidAlgebra.single t⁻¹ 1) * e := by
      simp only [mul_assoc]
    _ = e := by
      rw [MonoidAlgebra.single_mul_single]
      ext x
      simp

@[expose] def augmentationTwo (G : Type*) [Group G] [Fintype G] (e : GroupAlgebraTwo G) : ZMod 2 :=
  ∑ g : G, e.coeff g

@[expose] noncomputable def augmentationHom (G : Type*) [Group G] :
    GroupAlgebraTwo G →ₐ[ZMod 2] ZMod 2 :=
  (MonoidAlgebra.lift (ZMod 2) (ZMod 2) G) (1 : G →* ZMod 2)

theorem augmentationHom_apply (G : Type*) [Group G] [Fintype G]
    (e : GroupAlgebraTwo G) : augmentationHom G e = augmentationTwo G e := by
  classical
  rw [augmentationHom, MonoidAlgebra.lift_apply, augmentationTwo]
  calc
    e.coeff.sum (fun a b => b • (1 : G →* ZMod 2) a) =
        ∑ a : G, e.coeff a • (1 : G →* ZMod 2) a := by
          apply Finsupp.sum_fintype
          intro i
          simp
    _ = ∑ a : G, e.coeff a := by simp

@[expose] def IsGroupCentral (G : Type*) [Group G] (e : GroupAlgebraTwo G) : Prop :=
  ∀ g : G, MonoidAlgebra.single g 1 * e = e * MonoidAlgebra.single g 1

theorem isGroupCentral_one (G : Type*) [Group G] :
    IsGroupCentral G (1 : GroupAlgebraTwo G) := by
  intro g
  simp

theorem IsGroupCentral.mul (G : Type*) [Group G] {a b : GroupAlgebraTwo G}
    (ha : IsGroupCentral G a) (hb : IsGroupCentral G b) : IsGroupCentral G (a * b) := by
  intro g
  calc
    MonoidAlgebra.single g 1 * (a * b) =
        (MonoidAlgebra.single g 1 * a) * b := by rw [mul_assoc]
    _ = (a * MonoidAlgebra.single g 1) * b := by rw [ha]
    _ = a * (MonoidAlgebra.single g 1 * b) := by rw [mul_assoc]
    _ = a * (b * MonoidAlgebra.single g 1) := by rw [hb]
    _ = (a * b) * MonoidAlgebra.single g 1 := by rw [mul_assoc]

theorem IsGroupCentral.one_sub (G : Type*) [Group G] {a : GroupAlgebraTwo G}
    (ha : IsGroupCentral G a) : IsGroupCentral G (1 - a) := by
  intro g
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  rw [ha g]

theorem IsGroupCentral.commute (G : Type*) [Group G] {a : GroupAlgebraTwo G}
    (ha : IsGroupCentral G a) (b : GroupAlgebraTwo G) : Commute a b := by
  apply MonoidAlgebra.induction_on b
  · intro g
    change a * MonoidAlgebra.single g 1 = MonoidAlgebra.single g 1 * a
    exact (ha g).symm
  · intro x y hx hy
    exact hx.add_right hy
  · intro r x hx
    exact hx.smul_right r

private theorem isGroupCentral_list_prod (G : Type*) [Group G]
    (l : List (GroupAlgebraTwo G)) (hl : ∀ a ∈ l, IsGroupCentral G a) :
    IsGroupCentral G l.prod := by
  induction l with
  | nil => exact isGroupCentral_one G
  | cons a l ih =>
      rw [List.prod_cons]
      exact IsGroupCentral.mul G (hl a (by simp))
        (ih (by
          intro b hb
          exact hl b (by simp [hb])))

theorem one_sub_idempotent {R : Type*} [Ring R] {a : R} (ha : a * a = a) :
    (1 - a) * (1 - a) = 1 - a := by
  calc
    (1 - a) * (1 - a) = 1 - a - a + a * a := by noncomm_ring
    _ = 1 - a := by rw [ha]; abel

private theorem mul_idempotent_of_commute {R : Type*} [Semigroup R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (hab : Commute a b) :
    (a * b) * (a * b) = a * b := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [← hab.eq]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = a * b := by rw [ha, hb]

private theorem groupCentral_list_prod_idempotent (G : Type*) [Group G]
    (l : List (GroupAlgebraTwo G))
    (hc : ∀ a ∈ l, IsGroupCentral G a)
    (hi : ∀ a ∈ l, a * a = a) : l.prod * l.prod = l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.prod_cons]
      apply mul_idempotent_of_commute
      · exact hi a (by simp)
      · exact ih
          (by
            intro b hb
            exact hc b (by simp [hb]))
          (by
            intro b hb
            exact hi b (by simp [hb]))
      · exact (hc a (by simp)).commute G l.prod

private theorem list_prod_mul_eq_zero_of_mem {R : Type*} [Ring R]
    (l : List R) (f z : R) (hz : z ∈ l) (hcomm : ∀ a ∈ l, Commute a f)
    (hzf : z * f = 0) : l.prod * f = 0 := by
  induction l with
  | nil => simp at hz
  | cons a l ih =>
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · have hp : Commute l.prod f := Commute.list_prod_left l f (by
          intro b hb
          exact hcomm b (by simp [hb]))
        calc
          (z :: l).prod * f = z * (l.prod * f) := by simp only [List.prod_cons, mul_assoc]
          _ = z * (f * l.prod) := by rw [hp.eq]
          _ = (z * f) * l.prod := by rw [mul_assoc]
          _ = 0 := by rw [hzf, zero_mul]
      · calc
          (a :: l).prod * f = a * (l.prod * f) := by simp only [List.prod_cons, mul_assoc]
          _ = 0 := by
            rw [ih hz (by
              intro b hb
              exact hcomm b (by simp [hb]))]
            exact mul_zero a

@[expose] def IsAugmentationZeroCentralIdempotent (G : Type*) [Group G]
    (e : GroupAlgebraTwo G) : Prop :=
  IsGroupCentral G e ∧ e * e = e ∧ augmentationHom G e = 0

@[expose] noncomputable def principalBlockCandidate (G : Type*) [Group G] [Fintype G] :
    GroupAlgebraTwo G := by
  classical
  letI : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  exact (((Finset.univ : Finset (GroupAlgebraTwo G)).filter
    (IsAugmentationZeroCentralIdempotent G)).toList.map (fun f => 1 - f)).prod

theorem principalBlockCandidate_central (G : Type*) [Group G] [Fintype G] :
    IsGroupCentral G (principalBlockCandidate G) := by
  classical
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  unfold principalBlockCandidate
  apply isGroupCentral_list_prod
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨f, hf, rfl⟩ := ha
  apply IsGroupCentral.one_sub
  have hf' : f ∈ (Finset.univ : Finset (GroupAlgebraTwo G)).filter
      (IsAugmentationZeroCentralIdempotent G) := by
    simpa using hf
  exact (Finset.mem_filter.mp hf').2.1

private theorem augmentationHom_list_prod_eq_one (G : Type*) [Group G]
    (l : List (GroupAlgebraTwo G))
    (hl : ∀ a ∈ l, augmentationHom G a = 1) :
    augmentationHom G l.prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.prod_cons, map_mul, hl a (by simp), ih]
      · simp
      · intro b hb
        exact hl b (by simp [hb])

theorem principalBlockCandidate_augmentation (G : Type*) [Group G] [Fintype G] :
    augmentationTwo G (principalBlockCandidate G) = 1 := by
  classical
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  rw [← augmentationHom_apply]
  unfold principalBlockCandidate
  apply augmentationHom_list_prod_eq_one
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨f, hf, rfl⟩ := ha
  have hf' : f ∈ (Finset.univ : Finset (GroupAlgebraTwo G)).filter
      (IsAugmentationZeroCentralIdempotent G) := by
    simpa using hf
  have hzero := (Finset.mem_filter.mp hf').2.2.2
  rw [map_sub, map_one, hzero]
  simp

theorem principalBlockCandidate_idempotent (G : Type*) [Group G] [Fintype G] :
    principalBlockCandidate G * principalBlockCandidate G = principalBlockCandidate G := by
  classical
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  unfold principalBlockCandidate
  apply groupCentral_list_prod_idempotent
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    apply IsGroupCentral.one_sub
    have hf' : f ∈ (Finset.univ : Finset (GroupAlgebraTwo G)).filter
        (IsAugmentationZeroCentralIdempotent G) := by
      simpa using hf
    exact (Finset.mem_filter.mp hf').2.1
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    apply one_sub_idempotent
    have hf' : f ∈ (Finset.univ : Finset (GroupAlgebraTwo G)).filter
        (IsAugmentationZeroCentralIdempotent G) := by
      simpa using hf
    exact (Finset.mem_filter.mp hf').2.2.1

theorem principalBlockCandidate_annihilates (G : Type*) [Group G] [Fintype G]
    (f : GroupAlgebraTwo G) (hf : IsAugmentationZeroCentralIdempotent G f) :
    principalBlockCandidate G * f = 0 := by
  classical
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  unfold principalBlockCandidate
  apply list_prod_mul_eq_zero_of_mem
    (z := (1 - f : GroupAlgebraTwo G))
  · rw [List.mem_map]
    refine ⟨f, ?_, rfl⟩
    simp [hf]
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact (hf.1.commute G (1 - b)).symm
  · rw [sub_mul, one_mul, hf.2.1, sub_self]

private theorem algebraStabilizer_odd (G : Type*) [Group G] [Fintype G]
    (e : GroupAlgebraTwo G) (haug : augmentationTwo G e = 1) :
    Odd (Nat.card (algebraStabilizer G e)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card (algebraStabilizer G e) := even_iff_two_dvd.mp heven
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' (G := algebraStabilizer G e) 2 hdvd
  have hxne : (x : G) ≠ 1 := by
    intro hx
    have : x = 1 := Subtype.ext hx
    subst x
    simp at hxord
  have hxsq : (x : G) * (x : G) = 1 := by
    have hpow := pow_orderOf_eq_one x
    rw [hxord] at hpow
    simpa [pow_two] using congrArg Subtype.val hpow
  have hcoeff (a : G) : e.coeff ((x : G) * a) = e.coeff a := by
    have hxmem : MonoidAlgebra.single (x : G) 1 * e = e := x.property
    have h := congrArg (fun z : GroupAlgebraTwo G => z.coeff ((x : G) * a)) hxmem
    simpa using h.symm
  have hzero : augmentationTwo G e = 0 := by
    classical
    have hsum := Finset.sum_involution
      (s := Finset.univ) (f := fun a : G => e.coeff a)
      (fun a _ => (x : G) * a)
      (by
        intro a ha
        rw [hcoeff]
        exact CharTwo.add_self_eq_zero _)
      (by
        intro a ha hnonzero hfix
        apply hxne
        apply mul_right_cancel (b := a)
        simpa using hfix)
      (by simp)
      (by
        intro a ha
        rw [← mul_assoc]
        rw [hxsq, one_mul])
    simpa [augmentationTwo] using hsum
  rw [haug] at hzero
  exact one_ne_zero hzero

theorem zStar_of_groupAlgebraWitness (G : Type*) [Group G] [Fintype G] (t : G)
    (e : GroupAlgebraTwo G)
    (he : ∀ x : G, MonoidAlgebra.single x 1 * e = e * MonoidAlgebra.single x 1)
    (haug : augmentationTwo G e = 1)
    (hte : ∀ g : G, MonoidAlgebra.single (g * t * g⁻¹) 1 * e =
      MonoidAlgebra.single t 1 * e) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  refine ⟨algebraStabilizer G e, algebraStabilizer_normal G e he,
    algebraStabilizer_odd G e haug, ?_⟩
  intro g
  exact commutator_mem_algebraStabilizer G t g e he (hte g)

end ZStar.Helpers

end CFSG
