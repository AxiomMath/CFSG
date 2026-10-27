module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Sporadic.SchreierLemmas

structure SchreierWordChain (X : Type*) (r : ℕ) where
  strongCount : ℕ
  le_strongCount : r ≤ strongCount
  strong : Fin strongCount → FreeGroup (Fin r)
  strong_original : ∀ i : Fin r, strong (Fin.castLE le_strongCount i) = FreeGroup.of i
  baseCount : ℕ
  base : Fin baseCount → X
  orbit : Fin baseCount → Finset X
  transversal : Fin baseCount → X → FreeGroup (Fin r)

namespace SchreierWordChain

variable {X : Type*} {r : ℕ} (C : SchreierWordChain X r) (p : Fin r → Equiv.Perm X)

@[expose] def levelSet (i : ℕ) : Set (Fin C.strongCount) :=
  {j | ∀ l : Fin C.baseCount, l.val < i → FreeGroup.lift p (C.strong j) (C.base l) = C.base l}

@[expose] def levelSubgroup (i : ℕ) : Subgroup (FreeGroup (Fin r)) :=
  Subgroup.closure (C.strong '' C.levelSet p i)

@[expose] def residue (i : ℕ) (u : FreeGroup (Fin r)) : FreeGroup (Fin r) :=
  ((List.finRange C.baseCount).filter fun l => decide (i < l.val)).foldl
    (fun v l => (C.transversal l (FreeGroup.lift p v (C.base l)))⁻¹ * v) u

@[expose] def schreierElement (i : Fin C.baseCount) (x : X) (j : Fin C.strongCount) :
    FreeGroup (Fin r) :=
  (C.transversal i (FreeGroup.lift p (C.strong j) x))⁻¹ * C.strong j * C.transversal i x

theorem levelSubgroup_anti {i i' : ℕ} (h : i ≤ i') :
    C.levelSubgroup p i' ≤ C.levelSubgroup p i :=
  Subgroup.closure_mono (Set.image_mono fun _ hj l hl => hj l (lt_of_lt_of_le hl h))

theorem exists_residue_eq
    (htrans : ∀ (l : Fin C.baseCount) (x : X), C.transversal l x ∈ C.levelSubgroup p l)
    (i : ℕ) (u : FreeGroup (Fin r)) :
    ∃ t ∈ C.levelSubgroup p (i + 1), C.residue p i u = t⁻¹ * u := by
  have key : ∀ (L : List (Fin C.baseCount)), (∀ l ∈ L, i < l.val) → ∀ v,
      ∃ t ∈ C.levelSubgroup p (i + 1), L.foldl
        (fun v l => (C.transversal l (FreeGroup.lift p v (C.base l)))⁻¹ * v) v = t⁻¹ * v := by
    intro L
    induction L with
    | nil => exact fun _ v => ⟨1, one_mem _, by simp⟩
    | cons l L ih =>
      intro hL v
      obtain ⟨t, ht, he⟩ := ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
        ((C.transversal l (FreeGroup.lift p v (C.base l)))⁻¹ * v)
      refine ⟨C.transversal l (FreeGroup.lift p v (C.base l)) * t,
        mul_mem (C.levelSubgroup_anti p (hL l List.mem_cons_self) (htrans _ _)) ht, ?_⟩
      rw [List.foldl_cons, he]
      group
  obtain ⟨t, ht, he⟩ := key _ (fun l hl => of_decide_eq_true (List.mem_filter.1 hl).2) u
  exact ⟨t, ht, he⟩

theorem inv_mem_of_forall_mem {O : Finset X} {f : Equiv.Perm X} (hf : ∀ y ∈ O, f y ∈ O)
    {y : X} (hy : y ∈ O) : f⁻¹ y ∈ O := by
  obtain ⟨x, hx, hxy⟩ := Finset.surj_on_of_inj_on_of_card_le (s := O) (t := O)
    (fun x _ => f x) (fun x hx => hf x hx) (fun _ _ _ _ h => f.injective h) le_rfl y hy
  have : f⁻¹ (f x) = x := Equiv.Perm.inv_eq_iff_eq.2 rfl
  rw [hxy, this]
  exact hx

theorem mem_closure_schreier (I : Fin C.baseCount) (hb : C.base I ∈ C.orbit I)
    (horbit : ∀ x ∈ C.orbit I, ∀ j ∈ C.levelSet p I,
      FreeGroup.lift p (C.strong j) x ∈ C.orbit I)
    (htrans : ∀ x, C.transversal I x ∈ C.levelSubgroup p I)
    (htb : FreeGroup.lift p (C.transversal I (C.base I)) (C.base I) = C.base I)
    {w : FreeGroup (Fin r)} (hw : w ∈ C.levelSubgroup p I)
    (hwb : FreeGroup.lift p w (C.base I) = C.base I) :
    w ∈ Subgroup.closure {u | ∃ x ∈ C.orbit I, ∃ j ∈ C.levelSet p I,
      u = C.schreierElement p I x j} := by
  set E := {u | ∃ x ∈ C.orbit I, ∃ j ∈ C.levelSet p I, u = C.schreierElement p I x j}
  set t := C.transversal I
  set π := FreeGroup.lift p
  have tele : ∀ w ∈ C.levelSubgroup p I, (∀ y ∈ C.orbit I, π w y ∈ C.orbit I) ∧
      ∀ y ∈ C.orbit I, (t (π w y))⁻¹ * w * t y ∈ Subgroup.closure E := by
    intro w hw
    induction hw using Subgroup.closure_induction'' with
    | mem s hs =>
      obtain ⟨j, hj, rfl⟩ := hs
      exact ⟨fun y hy => horbit y hy j hj, fun y hy =>
        Subgroup.subset_closure ⟨y, hy, j, hj, rfl⟩⟩
    | inv_mem s hs =>
      obtain ⟨j, hj, rfl⟩ := hs
      have hinv : ∀ y ∈ C.orbit I, π (C.strong j)⁻¹ y ∈ C.orbit I := fun y hy => by
        rw [map_inv]
        exact inv_mem_of_forall_mem (fun y hy => horbit y hy j hj) hy
      refine ⟨hinv, fun y hy => ?_⟩
      set x := π (C.strong j)⁻¹ y
      have hx : π (C.strong j) x = y := by
        simp only [x, map_inv]
        exact Equiv.Perm.eq_inv_iff_eq.1 rfl
      have hmem : C.schreierElement p I x j ∈ Subgroup.closure E :=
        Subgroup.subset_closure ⟨x, hinv y hy, j, hj, rfl⟩
      have e : (t (π (C.strong j)⁻¹ y))⁻¹ * (C.strong j)⁻¹ * t y =
          (C.schreierElement p I x j)⁻¹ := by
        simp only [schreierElement]
        change (t x)⁻¹ * (C.strong j)⁻¹ * t y = ((t (π (C.strong j) x))⁻¹ * C.strong j * t x)⁻¹
        rw [hx]
        group
      rw [e]
      exact inv_mem hmem
    | one => exact ⟨fun y hy => by simpa using hy, fun y _ => by simp⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact h₁.1 _ (h₂.1 y hy)
      · have e : (t (π (w₁ * w₂) y))⁻¹ * (w₁ * w₂) * t y =
            ((t (π w₁ (π w₂ y)))⁻¹ * w₁ * t (π w₂ y)) * ((t (π w₂ y))⁻¹ * w₂ * t y) := by
          rw [map_mul, Equiv.Perm.mul_apply]
          group
        rw [e]
        exact mul_mem (h₁.2 _ (h₂.1 y hy)) (h₂.2 y hy)
  have h1 := (tele w hw).2 _ hb
  rw [hwb] at h1
  have h2 := (tele _ (htrans (C.base I))).2 _ hb
  rw [htb, inv_mul_cancel, one_mul] at h2
  have e : w = t (C.base I) * ((t (C.base I))⁻¹ * w * t (C.base I)) * (t (C.base I))⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem h2 h1) (inv_mem h2)

theorem lift_mem_of_eval_eq_one {G : Type*} [Group G] (c : Fin r → G) (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) (hbase : ∀ i, C.base i ∈ C.orbit i)
    (horbit : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift p (C.strong j) x ∈ C.orbit i)
    (htrans : ∀ (i : Fin C.baseCount) x, C.transversal i x ∈ C.levelSubgroup p i)
    (htrans_base : ∀ i, FreeGroup.lift p (C.transversal i (C.base i)) (C.base i) = C.base i)
    (hsift : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift p (C.residue p i (C.schreierElement p i x j)) = 1)
    (hsiftZ : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift c (C.residue p i (C.schreierElement p i x j)) ∈ Z)
    (htermZ : ∀ j ∈ C.levelSet p C.baseCount, FreeGroup.lift c (C.strong j) ∈ Z)
    (w : FreeGroup (Fin r)) (hw : FreeGroup.lift p w = 1) : FreeGroup.lift c w ∈ Z := by
  set π := FreeGroup.lift p
  set σ := FreeGroup.lift c
  have hcentral : ∀ z ∈ Z, ∀ g : G, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 (hZ hz) g
  have claim : ∀ m i, i + m = C.baseCount → ∀ w ∈ C.levelSubgroup p i, π w = 1 → σ w ∈ Z := by
    intro m
    induction m with
    | zero =>
      rintro i hi w hw -
      rw [add_zero] at hi
      subst hi
      induction hw using Subgroup.closure_induction with
      | mem s hs =>
        obtain ⟨j, hj, rfl⟩ := hs
        exact htermZ j hj
      | one => rw [map_one]; exact one_mem _
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      | inv x _ hx => rw [map_inv]; exact inv_mem hx
    | succ m ih =>
      intro i hi w hw hπw
      have hik : i < C.baseCount := by omega
      set I : Fin C.baseCount := ⟨i, hik⟩
      let M : Subgroup (FreeGroup (Fin r)) :=
        { carrier := {w | ∃ w' ∈ C.levelSubgroup p (i + 1), π w' = π w ∧ (σ w')⁻¹ * σ w ∈ Z}
          one_mem' := ⟨1, one_mem _, rfl, by simp [one_mem]⟩
          mul_mem' := by
            rintro a b ⟨a', ha', hπa, hσa⟩ ⟨b', hb', hπb, hσb⟩
            refine ⟨a' * b', mul_mem ha' hb', by rw [map_mul, map_mul, hπa, hπb], ?_⟩
            have e : (σ (a' * b'))⁻¹ * σ (a * b) =
                (σ b')⁻¹ * ((σ a')⁻¹ * σ a) * σ b := by
              rw [map_mul, map_mul]
              group
            rw [e, hcentral _ hσa, mul_assoc]
            exact mul_mem hσa hσb
          inv_mem' := by
            rintro a ⟨a', ha', hπa, hσa⟩
            refine ⟨a'⁻¹, inv_mem ha', by rw [map_inv, map_inv, hπa], ?_⟩
            have e : (σ a'⁻¹)⁻¹ * σ a⁻¹ = σ a' * ((σ a')⁻¹ * σ a)⁻¹ * (σ a')⁻¹ := by
              rw [map_inv, map_inv]
              group
            rw [e, hcentral _ (inv_mem hσa), mul_assoc, mul_inv_cancel, mul_one]
            exact inv_mem hσa }
      have hE : {u | ∃ x ∈ C.orbit I, ∃ j ∈ C.levelSet p I, u = C.schreierElement p I x j} ⊆
          (M : Set (FreeGroup (Fin r))) := by
        rintro u ⟨x, hx, j, hj, rfl⟩
        obtain ⟨t, ht, he⟩ := C.exists_residue_eq p htrans i (C.schreierElement p I x j)
        have h1 := hsift I x hx j hj
        have h2 := hsiftZ I x hx j hj
        change π (C.residue p i _) = 1 at h1
        change σ (C.residue p i _) ∈ Z at h2
        rw [he, map_mul, map_inv] at h1 h2
        exact ⟨t, ht, (inv_mul_eq_one.1 h1), h2⟩
      have hwM : w ∈ M := (Subgroup.closure_le M).2 hE
        (C.mem_closure_schreier p I (hbase I) (horbit I) (htrans I) (htrans_base I) hw
          (by rw [hπw]; rfl))
      obtain ⟨w', hw', hπ', hσ⟩ := hwM
      have hw'Z := ih (i + 1) (by omega) w' hw' (hπ'.trans hπw)
      have e : σ w = σ w' * ((σ w')⁻¹ * σ w) := by group
      rw [e]
      exact mul_mem hw'Z hσ
  have htop : C.levelSubgroup p 0 = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← FreeGroup.closure_range_of]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨Fin.castLE C.le_strongCount i, fun l hl => ?_,
      C.strong_original i⟩
    exact absurd hl (Nat.not_lt_zero _)
  exact claim C.baseCount 0 (zero_add _) w (htop ▸ Subgroup.mem_top w) hw

end SchreierWordChain

theorem central_Schreier_lift {X : Type*} {r : ℕ} (p : Fin r → Equiv.Perm X)
    {G : Type*} [Group G] (c : Fin r → G) (hG : Subgroup.closure (Set.range c) = ⊤)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (C : SchreierWordChain X r)
    (hbase : ∀ i, C.base i ∈ C.orbit i)
    (horbit : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift p (C.strong j) x ∈ C.orbit i)
    (htrans : ∀ (i : Fin C.baseCount) x, C.transversal i x ∈ C.levelSubgroup p i)
    (htrans_base : ∀ i, FreeGroup.lift p (C.transversal i (C.base i)) (C.base i) = C.base i)
    (hsift : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift p (C.residue p i (C.schreierElement p i x j)) = 1)
    (hsiftZ : ∀ i, ∀ x ∈ C.orbit i, ∀ j ∈ C.levelSet p i,
      FreeGroup.lift c (C.residue p i (C.schreierElement p i x j)) ∈ Z)
    (htermZ : ∀ j ∈ C.levelSet p C.baseCount, FreeGroup.lift c (C.strong j) ∈ Z) :
    ∃ f : Subgroup.closure (Set.range p) →* G ⧸ Z, Function.Surjective f ∧
      (∀ i, f ⟨p i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = ((c i : G) : G ⧸ Z)) ∧
      (IsSimpleGroup (Subgroup.closure (Set.range p)) → (∃ i, c i ∉ Z) →
        Function.Bijective f) := by
  set π := FreeGroup.lift p
  set σ := FreeGroup.lift c
  have hker : ∀ w, π w = 1 → σ w ∈ Z :=
    C.lift_mem_of_eval_eq_one p c Z hZ hbase horbit htrans htrans_base hsift hsiftZ htermZ
  let μ : FreeGroup (Fin r) →* G ⧸ Z := (QuotientGroup.mk' Z).comp σ
  have hrange : π.range = Subgroup.closure (Set.range p) := FreeGroup.range_lift_eq_closure
  have hle : π.rangeRestrict.ker ≤ μ.ker := by
    intro w hw
    rw [MonoidHom.ker_rangeRestrict] at hw
    exact (QuotientGroup.eq_one_iff _).2 (hker w hw)
  let f₀ : π.range →* G ⧸ Z := π.rangeRestrict.liftOfRightInverse
    (Function.surjInv π.rangeRestrict_surjective)
    (Function.rightInverse_surjInv π.rangeRestrict_surjective) ⟨μ, hle⟩
  have hf₀ : ∀ w, f₀ (π.rangeRestrict w) = μ w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨μ, hle⟩ w
  let f : Subgroup.closure (Set.range p) →* G ⧸ Z :=
    f₀.comp (MulEquiv.subgroupCongr hrange.symm).toMonoidHom
  have hf : ∀ w, f ⟨π w, hrange ▸ ⟨w, rfl⟩⟩ = μ w := fun w => hf₀ w
  have hfp : ∀ i, f ⟨p i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = ((c i : G) : G ⧸ Z) := by
    intro i
    have := hf (FreeGroup.of i)
    simp only [π, FreeGroup.lift_apply_of] at this
    rw [this]
    simp [μ, σ, FreeGroup.lift_apply_of]
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hg : g ∈ σ.range := by
      rw [FreeGroup.range_lift_eq_closure, hG]
      exact Subgroup.mem_top g
    obtain ⟨w, rfl⟩ := hg
    exact ⟨⟨π w, hrange ▸ ⟨w, rfl⟩⟩, hf w⟩
  refine ⟨f, hsurj, hfp, fun hsimple ⟨i, hi⟩ => ⟨?_, hsurj⟩⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).1 h
  · exfalso
    have hmem : (⟨p i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : Subgroup.closure (Set.range p)) ∈
        f.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hfp] at hmem
    exact hi ((QuotientGroup.eq_one_iff _).1 hmem)

end CFSG.Sporadic.SchreierLemmas
