module

public import CFSG.Monster.Existence.StdOdd.P5

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Monster.Existence.StdOdd.P5

section Calculus

variable {G : Type*} [Group G]

@[expose] def ConjAmb (ψ : Multiplicative E5 →* G) (x : G) (g : GL5) : Prop :=
  ∀ a : E5, x * ψ (Multiplicative.ofAdd a) * x⁻¹ =
    ψ (Multiplicative.ofAdd ((g : M5).mulVec a))

variable {ψ : Multiplicative E5 →* G}

theorem ConjAmb.one : ConjAmb ψ (1 : G) 1 := fun a => by simp

theorem ConjAmb.mul {x y : G} {g h : GL5} (hx : ConjAmb ψ x g) (hy : ConjAmb ψ y h) :
    ConjAmb ψ (x * y) (g * h) := fun a => by
  have e : x * y * ψ (Multiplicative.ofAdd a) * (x * y)⁻¹ =
      x * (y * ψ (Multiplicative.ofAdd a) * y⁻¹) * x⁻¹ := by group
  rw [e, hy a, hx, Units.val_mul, Matrix.mulVec_mulVec]

theorem ConjAmb.inv {x : G} {g : GL5} (hx : ConjAmb ψ x g) : ConjAmb ψ x⁻¹ g⁻¹ := fun a => by
  have h1 := hx (((g⁻¹ : GL5) : M5).mulVec a)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    at h1
  rw [← h1]
  group

theorem ConjAmb.of_mem (b : Multiplicative E5) : ConjAmb ψ (ψ b) 1 := fun a => by
  rw [← map_mul, ← map_inv, ← map_mul]
  simp [mul_comm]

theorem ConjAmb.unique (hψ : Function.Injective ψ) {x : G} {g g' : GL5} (h : ConjAmb ψ x g)
    (h' : ConjAmb ψ x g') : g = g' := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro a
  have := (h a).symm.trans (h' a)
  exact Multiplicative.ofAdd.injective (hψ this)

theorem ConjAmb.of_basis (x : G) (g : GL5)
    (h : ∀ j : Fin 5, x * ψ (Multiplicative.ofAdd (Pi.single j 1)) * x⁻¹ =
      ψ (Multiplicative.ofAdd ((g : M5).mulVec (Pi.single j 1)))) : ConjAmb ψ x g := by
  let S : AddSubgroup E5 :=
    { carrier := {a | x * ψ (Multiplicative.ofAdd a) * x⁻¹ =
        ψ (Multiplicative.ofAdd ((g : M5).mulVec a))}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [ofAdd_add, map_mul, Matrix.mulVec_add, ofAdd_add, map_mul, ← ha, ← hb]
        group
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [ofAdd_neg, map_inv, Matrix.mulVec_neg, ofAdd_neg, map_inv, ← ha]
        group }
  have hS : ∀ a : E5, a ∈ S := by
    intro a
    have ha : a = ∑ j, (a j).val • (Pi.single j (1 : ZMod 3) : E5) := by
      ext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [hj.symm]
      · simp
    rw [ha]
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.nsmul_mem _ (h j) _
  exact hS

end Calculus

section Words

variable {G : Type*} [Group G]

@[expose] def Wd (tA tB : G) (w : List (Fin 2)) : G := (w.map ![tA, tB]).prod

theorem Wd_nil (tA tB : G) : Wd tA tB [] = 1 := rfl

theorem Wd_cons (tA tB : G) (c : Fin 2) (w : List (Fin 2)) :
    Wd tA tB (c :: w) = ![tA, tB] c * Wd tA tB w := by
  simp [Wd]

theorem ConjAmb.Wd {ψ : Multiplicative E5 →* G} {tA tB : G} (hA : ConjAmb ψ tA genA)
    (hB : ConjAmb ψ tB genB) (w : List (Fin 2)) : ConjAmb ψ (Wd tA tB w) (wordProd w) := by
  induction w with
  | nil => exact ConjAmb.one
  | cons c w ih =>
    rw [Wd_cons, wordProd, List.map_cons, List.prod_cons, ← wordProd]
    refine ConjAmb.mul ?_ ih
    fin_cases c
    · exact hA
    · exact hB

end Words

section Main

variable {G : Type*} [Group G]

theorem exists_mul_Wd_of_mem_closure (ψ : Multiplicative E5 →* G) (tA tB : G)
    (hA : ConjAmb ψ tA genA) (hB : ConjAmb ψ tB genB) (hA3 : tA ^ 3 = 1) (hB3 : tB ^ 3 = 1)
    (htA : ∀ j : Fin 81, Wd tA tB (pw j) * tA = Wd tA tB (pw (ra j)))
    (htB : ∀ j : Fin 81, Wd tA tB (pw j) * tB = Wd tA tB (pw (rb j)))
    (hW0 : Wd tA tB (pw 0) = 1) {t : G} (ht : t ∈ Subgroup.closure (Set.range ψ ∪ {tA, tB})) :
    ∃ (a : E5) (j : Fin 81), t = ψ (Multiplicative.ofAdd a) * Wd tA tB (pw j) := by
  let X : G → Prop := fun x =>
    ∃ (a : E5) (j : Fin 81), x = ψ (Multiplicative.ofAdd a) * Wd tA tB (pw j)
  have hXψ : ∀ x, X x → ∀ b : E5, X (x * ψ (Multiplicative.ofAdd b)) := by
    rintro x ⟨a, j, rfl⟩ b
    have h := ConjAmb.Wd hA hB (pw j) b
    refine ⟨a + (wordProd (pw j) : M5).mulVec b, j, ?_⟩
    rw [ofAdd_add, map_mul, mul_assoc, mul_assoc]
    congr 1
    rw [← h]
    group
  have hXA : ∀ x, X x → X (x * tA) := by
    rintro x ⟨a, j, rfl⟩
    exact ⟨a, ra j, by rw [mul_assoc, htA]⟩
  have hXB : ∀ x, X x → X (x * tB) := by
    rintro x ⟨a, j, rfl⟩
    exact ⟨a, rb j, by rw [mul_assoc, htB]⟩
  have hinvA : tA⁻¹ = tA * tA := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, ← pow_two, ← pow_succ]
    exact hA3
  have hinvB : tB⁻¹ = tB * tB := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, ← pow_two, ← pow_succ]
    exact hB3
  have key : X t := by
    induction ht using Subgroup.closure_induction_right with
    | one => exact ⟨0, 0, by simp [hW0]⟩
    | mul_right x hx y hy ih =>
      rcases hy with ⟨b, rfl⟩ | hy
      · rw [← ofAdd_toAdd b]
        exact hXψ x ih _
      · rcases hy with rfl | rfl
        · exact hXA x ih
        · exact hXB x ih
    | mul_inv_cancel x hx y hy ih =>
      rcases hy with ⟨b, rfl⟩ | hy
      · rw [← map_inv, ← ofAdd_toAdd b, ← ofAdd_neg]
        exact hXψ x ih _
      · rcases hy with rfl | rfl
        · rw [hinvA, ← mul_assoc]
          exact hXA _ (hXA x ih)
        · rw [hinvB, ← mul_assoc]
          exact hXB _ (hXB x ih)
  exact key

theorem exists_isExt_of_split
    (ψ : Multiplicative E5 →* G) (hψ : Function.Injective ψ)
    (tA tB : G) (hA : ConjAmb ψ tA genA) (hB : ConjAmb ψ tB genB)
    (hA3 : tA ^ 3 = 1) (hB3 : tB ^ 3 = 1)
    (htA : ∀ j : Fin 81, Wd tA tB (pw j) * tA = Wd tA tB (pw (ra j)))
    (htB : ∀ j : Fin 81, Wd tA tB (pw j) * tB = Wd tA tB (pw (rb j)))
    (hW0 : Wd tA tB (pw 0) = 1) :
    ∃ (T : Subgroup G) (E : Subgroup T) (ι : E ≃* Multiplicative E5) (ρ : T →* GL5),
      IsExt Pbar E ι ρ ∧ ∀ x : Multiplicative E5, (((ι.symm x : E) : T) : G) = ψ x := by
  classical
  set T : Subgroup G := Subgroup.closure (Set.range ψ ∪ {tA, tB}) with hT
  have hψT : ∀ b, ψ b ∈ T := fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)
  have htAT : tA ∈ T := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have htBT : tB ∈ T := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  let E : Subgroup T := ψ.range.subgroupOf T
  let φ : Multiplicative E5 →* E :=
    (ψ.codRestrict T hψT).codRestrict E fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨b, rfl⟩
  have hφ : ∀ b, (((φ b : E) : T) : G) = ψ b := fun b => rfl
  have hφinj : Function.Injective φ := fun x y h => hψ (by rw [← hφ, ← hφ, h])
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨b, hb⟩ := (Subgroup.mem_subgroupOf.mp e.2 : ((e : T) : G) ∈ ψ.range)
    exact ⟨b, Subtype.ext (Subtype.ext (by rw [hφ, hb]))⟩
  let ι : E ≃* Multiplicative E5 := (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm
  have hι : ∀ e : E, ψ (ι e) = ((e : T) : G) := by
    intro e
    have h := (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).apply_symm_apply e
    have h' : (((φ (ι e) : E) : T) : G) = ((e : T) : G) := by
      rw [show φ (ι e) = e from h]
    rw [hφ] at h'
    exact h'
  have hιsymm : ∀ x : Multiplicative E5, (((ι.symm x : E) : T) : G) = ψ x := fun x => rfl
  have hact_amb : ∀ t ∈ T, ∃ g ∈ Pbar, ConjAmb ψ t g := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | hx
      · exact ⟨1, one_mem _, ConjAmb.of_mem b⟩
      · rcases hx with rfl | rfl
        · exact ⟨genA, genA_mem, hA⟩
        · exact ⟨genB, genB_mem, hB⟩
    | one => exact ⟨1, one_mem _, ConjAmb.one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, hxg⟩ := hx
      obtain ⟨h, hh, hyh⟩ := hy
      exact ⟨g * h, mul_mem hg hh, hxg.mul hyh⟩
    | inv x _ hx =>
      obtain ⟨g, hg, hxg⟩ := hx
      exact ⟨g⁻¹, inv_mem hg, hxg.inv⟩
  have hsurj_amb : ∀ g ∈ Pbar, ∃ t ∈ T, ConjAmb ψ t g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨tA, htAT, hA⟩
      · exact ⟨tB, htBT, hB⟩
    | one => exact ⟨1, one_mem _, ConjAmb.one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨s, hs, hys⟩ := hy
      exact ⟨t * s, mul_mem ht hs, hxt.mul hys⟩
    | inv x _ hx =>
      obtain ⟨t, ht, hxt⟩ := hx
      exact ⟨t⁻¹, inv_mem ht, hxt.inv⟩
  have hE : E.Normal := by
    refine ⟨fun e he t => ?_⟩
    obtain ⟨b, hb⟩ := (Subgroup.mem_subgroupOf.mp he : ((e : T) : G) ∈ ψ.range)
    obtain ⟨g, -, hg⟩ := hact_amb t.1 t.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Multiplicative.ofAdd ((g : M5).mulVec (Multiplicative.toAdd b)), ?_⟩
    have := hg (Multiplicative.toAdd b)
    rw [ofAdd_toAdd, hb] at this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this.symm
  have hconj : ∀ (t : T) (g : GL5), ConjAmb ψ (t : G) g → ∀ e : E,
      ivec E ι ⟨t * e * t⁻¹, hE.conj_mem _ e.2 t⟩ = (g : M5).mulVec (ivec E ι e) := by
    intro t g h e
    have h1 : ψ (Multiplicative.ofAdd (ivec E ι e)) = ((e : T) : G) := by
      have := hι e
      simpa [ivec] using this
    have h2 := h (ivec E ι e)
    rw [h1] at h2
    have h3 : ψ (ι ⟨t * e * t⁻¹, hE.conj_mem _ e.2 t⟩) =
        ψ (Multiplicative.ofAdd ((g : M5).mulVec (ivec E ι e))) := by
      rw [hι]
      exact h2
    have h4 := hψ h3
    show Multiplicative.toAdd (ι _) = _
    rw [h4]
    rfl
  have hker : ∀ t : T, ConjAmb ψ (t : G) 1 → (t : G) ∈ ψ.range := by
    intro t h1
    obtain ⟨a, j, hta⟩ := exists_mul_Wd_of_mem_closure ψ tA tB hA hB hA3 hB3 htA htB hW0 t.2
    have h2 : ConjAmb ψ (t : G) (1 * pm j) := by
      rw [hta]
      exact (ConjAmb.of_mem _).mul (ConjAmb.Wd hA hB (pw j))
    have h3 : (1 : GL5) = 1 * pm j := h1.unique hψ h2
    have h4 : pm j = 1 := by rw [one_mul] at h3; exact h3.symm
    have h5 : j = 0 := pm_injective (h4.trans pm_zero.symm)
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    rw [hta, h5, hW0, mul_one]
  choose ρf hρP hρA using fun t : T => hact_amb t.1 t.2
  have hρ1 : ρf 1 = 1 := by
    refine (hρA 1).unique hψ ?_
    rw [Subgroup.coe_one]
    exact ConjAmb.one
  have hρm : ∀ t t' : T, ρf (t * t') = ρf t * ρf t' := fun t t' => by
    refine (hρA (t * t')).unique hψ ?_
    rw [Subgroup.coe_mul]
    exact (hρA t).mul (hρA t')
  let ρ : T →* GL5 := ⟨⟨ρf, hρ1⟩, hρm⟩
  have hρ : ∀ t, ρ t = ρf t := fun _ => rfl
  refine ⟨T, E, ι, ρ, ⟨hE, fun t e => ?_, ?_, ?_⟩, hιsymm⟩
  · rw [hρ]
    exact hconj t _ (hρA t) e
  · ext t
    rw [MonoidHom.mem_ker, hρ]
    constructor
    · intro h1
      have h2 : ConjAmb ψ (t : G) 1 := by rw [← h1]; exact hρA t
      exact Subgroup.mem_subgroupOf.mpr (hker t h2)
    · intro ht
      obtain ⟨b, hb⟩ := (Subgroup.mem_subgroupOf.mp ht : (t : G) ∈ ψ.range)
      refine (hρA t).unique hψ ?_
      rw [← hb]
      exact ConjAmb.of_mem b
  · ext g
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      rw [hρ]
      exact hρP t
    · intro hg
      obtain ⟨t, ht, h⟩ := hsurj_amb g hg
      exact ⟨⟨t, ht⟩, by rw [hρ]; exact (hρA ⟨t, ht⟩).unique hψ h⟩

end Main

end CFSG.Monster.Existence.StdOdd.Cert
