module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

namespace G11

theorem mem_permCore_iff_sum_eq_zero {n : ℕ} {x : Fin n → ZMod 2} :
    x ∈ permCore n ↔ ∑ i, x i = 0 := Iff.rfl

theorem permAct_smul_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : ZMod 2) (x : Fin n → ZMod 2) :
    permAct σ (a • x) = a • permAct σ x := rfl

theorem permCore_five_endo_scalar
    (T : ↥(permCore 5) →ₗ[ZMod 2] ↥(permCore 5))
    (hT : ∀ σ : ↥(alternatingGroup (Fin 5)), ∀ y y' : ↥(permCore 5),
      (y' : Fin 5 → ZMod 2) = permAct (σ : Equiv.Perm (Fin 5)) (y : Fin 5 → ZMod 2) →
      (T y' : Fin 5 → ZMod 2) = permAct (σ : Equiv.Perm (Fin 5)) (T y : Fin 5 → ZMod 2)) :
    ∃ a : ZMod 2, ∀ y, T y = a • y := by
  have hu : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) ∈ permCore 5 := by
    rw [mem_permCore_iff_sum_eq_zero]; decide
  have hσ1 : (Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hσ2 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have f1 : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) =
      permAct (Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4) ![1, 1, 0, 0, 0] := by decide
  have f2 : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) =
      permAct (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ![1, 1, 0, 0, 0] := by decide
  have h1 := hT ⟨_, hσ1⟩ ⟨_, hu⟩ ⟨_, hu⟩ f1
  have h2 := hT ⟨_, hσ2⟩ ⟨_, hu⟩ ⟨_, hu⟩ f2
  set w : Fin 5 → ZMod 2 := (T ⟨_, hu⟩ : Fin 5 → ZMod 2) with hw
  have hwsum : ∑ i, w i = 0 := (T ⟨_, hu⟩).2
  have e1 : w 3 = w 2 := congrFun h1 3
  have e2 : w 4 = w 3 := congrFun h1 4
  have e3 : w 1 = w 0 := congrFun h2 1
  have e2' : w 4 = w 2 := e2.trans e1
  have hsum : w 0 + w 1 + w 2 + w 3 + w 4 = 0 := by
    rw [← Fin.sum_univ_five]; exact hwsum
  rw [e2', e1, e3] at hsum
  have key : ∀ a c : ZMod 2, a + a + c + c + c = 0 → c = 0 := by decide
  have hw2 : w 2 = 0 := key _ _ hsum
  have hwv : w = (w 0) • (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) := by
    funext i
    fin_cases i <;> simp [e1, e2', e3, hw2]
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, (T ⟨_, hu⟩ : Fin 5 → ZMod 2) =
      a • (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) := ⟨w 0, hwv⟩
  have hz : ∀ τ : Equiv.Perm (Fin 5), τ ∈ alternatingGroup (Fin 5) →
      ∀ (v : Fin 5 → ZMod 2) (hv : v ∈ permCore 5),
        v = permAct τ ![1, 1, 0, 0, 0] → T ⟨v, hv⟩ = a • ⟨v, hv⟩ := by
    intro τ hτ v hv hvτ
    apply Subtype.ext
    rw [hT ⟨τ, hτ⟩ ⟨_, hu⟩ ⟨v, hv⟩ hvτ, ha, permAct_smul_eq]
    show a • permAct τ ![1, 1, 0, 0, 0] = a • v
    rw [hvτ]
  have hz0 := hz (Equiv.swap 1 4 * Equiv.swap 2 3)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide) ![1, 0, 0, 0, 1]
    (by rw [mem_permCore_iff_sum_eq_zero]; decide) (by decide)
  have hz1 := hz (Equiv.swap 0 4 * Equiv.swap 2 3)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide) ![0, 1, 0, 0, 1]
    (by rw [mem_permCore_iff_sum_eq_zero]; decide) (by decide)
  have hz2 := hz (Equiv.swap 0 2 * Equiv.swap 1 4)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide) ![0, 0, 1, 0, 1]
    (by rw [mem_permCore_iff_sum_eq_zero]; decide) (by decide)
  have hz3 := hz (Equiv.swap 0 3 * Equiv.swap 1 4)
    (by rw [Equiv.Perm.mem_alternatingGroup]; decide) ![0, 0, 0, 1, 1]
    (by rw [mem_permCore_iff_sum_eq_zero]; decide) (by decide)
  refine ⟨a, fun y => ?_⟩
  have hy : ∑ i, (y : Fin 5 → ZMod 2) i = 0 := y.2
  rw [Fin.sum_univ_five] at hy
  have hy4 : (y : Fin 5 → ZMod 2) 4 =
      (y : Fin 5 → ZMod 2) 0 + (y : Fin 5 → ZMod 2) 1 + (y : Fin 5 → ZMod 2) 2 +
        (y : Fin 5 → ZMod 2) 3 := by
    revert hy
    generalize (y : Fin 5 → ZMod 2) 0 = p0
    generalize (y : Fin 5 → ZMod 2) 1 = p1
    generalize (y : Fin 5 → ZMod 2) 2 = p2
    generalize (y : Fin 5 → ZMod 2) 3 = p3
    generalize (y : Fin 5 → ZMod 2) 4 = p4
    revert p0 p1 p2 p3 p4
    decide
  have hyz : y = (y : Fin 5 → ZMod 2) 0 •
        (⟨![1, 0, 0, 0, 1], by rw [mem_permCore_iff_sum_eq_zero]; decide⟩ : ↥(permCore 5)) +
      (y : Fin 5 → ZMod 2) 1 •
        (⟨![0, 1, 0, 0, 1], by rw [mem_permCore_iff_sum_eq_zero]; decide⟩ : ↥(permCore 5)) +
      (y : Fin 5 → ZMod 2) 2 •
        (⟨![0, 0, 1, 0, 1], by rw [mem_permCore_iff_sum_eq_zero]; decide⟩ : ↥(permCore 5)) +
      (y : Fin 5 → ZMod 2) 3 •
        (⟨![0, 0, 0, 1, 1], by rw [mem_permCore_iff_sum_eq_zero]; decide⟩ : ↥(permCore 5)) := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [hy4]
  rw [hyz]
  simp only [map_add, map_smul, hz0, hz1, hz2, hz3]
  module

private noncomputable def permCoreProj : ↥(permCore 5) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun y := fun i => (y : Fin 5 → ZMod 2) i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem permCoreProj_bijective : Function.Bijective permCoreProj := by
  have key : ∀ p0 p1 p2 p3 p4 : ZMod 2, p0 + p1 + p2 + p3 + p4 = 0 →
      p4 = p0 + p1 + p2 + p3 := by decide
  constructor
  · intro y y' h
    apply Subtype.ext
    have hy : ∑ i, (y : Fin 5 → ZMod 2) i = 0 := y.2
    have hy' : ∑ i, (y' : Fin 5 → ZMod 2) i = 0 := y'.2
    rw [Fin.sum_univ_five] at hy hy'
    have h0 : (y : Fin 5 → ZMod 2) 0 = (y' : Fin 5 → ZMod 2) 0 := congrFun h 0
    have h1 : (y : Fin 5 → ZMod 2) 1 = (y' : Fin 5 → ZMod 2) 1 := congrFun h 1
    have h2 : (y : Fin 5 → ZMod 2) 2 = (y' : Fin 5 → ZMod 2) 2 := congrFun h 2
    have h3 : (y : Fin 5 → ZMod 2) 3 = (y' : Fin 5 → ZMod 2) 3 := congrFun h 3
    have h4 := key _ _ _ _ _ hy
    have h4' := key _ _ _ _ _ hy'
    funext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · show (y : Fin 5 → ZMod 2) 4 = (y' : Fin 5 → ZMod 2) 4
      rw [h4, h4', h0, h1, h2, h3]
  · intro a
    refine ⟨⟨![a 0, a 1, a 2, a 3, a 0 + a 1 + a 2 + a 3], ?_⟩, ?_⟩
    · rw [mem_permCore_iff_sum_eq_zero, Fin.sum_univ_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      generalize a 0 = p0
      generalize a 1 = p1
      generalize a 2 = p2
      generalize a 3 = p3
      revert p0 p1 p2 p3
      decide
    · funext i
      fin_cases i <;> rfl

private noncomputable def permCoreEquiv : ↥(permCore 5) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearEquiv.ofBijective permCoreProj permCoreProj_bijective

theorem finrank_permCore_five : Module.finrank (ZMod 2) ↥(permCore 5) = 4 := by
  rw [permCoreEquiv.finrank_eq]
  simp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem IsA5Module.finrank_eq {L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (h : IsA5Module L I) : Module.finrank (ZMod 2) I = 4 := by
  obtain ⟨_, ψ, _⟩ := h
  rw [ψ.finrank_eq, finrank_permCore_five]

theorem IsA5Module.fixes_of_commute {L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hA5 : IsA5Module L I) (hinv : Invariant L I) {c : GLV V} (hcI : ∀ v ∈ I, c v ∈ I)
    (hc : ∀ l ∈ L, ∀ v ∈ I, c (l v) = l (c v)) : ∀ v ∈ I, c v = v := by
  have hfin := hA5.finrank_eq
  obtain ⟨φ, ψ, hψ⟩ := hA5
  let cI : ↥I →ₗ[ZMod 2] ↥I := (c : V →ₗ[ZMod 2] V).restrict hcI
  let T : ↥(permCore 5) →ₗ[ZMod 2] ↥(permCore 5) := ψ.toLinearMap ∘ₗ cI ∘ₗ ψ.symm.toLinearMap
  have hT : ∀ i : ↥I, T (ψ i) = ψ ⟨c i, hcI i i.2⟩ := by
    intro i
    simp only [T, cI, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨a, ha⟩ := permCore_five_endo_scalar T (by
    intro σ y y' hyy'
    obtain ⟨γ, rfl⟩ := φ.surjective σ
    obtain ⟨i, rfl⟩ := ψ.surjective y
    obtain ⟨j, rfl⟩ := ψ.surjective y'
    have hγi : (γ : GLV V) i ∈ I := hinv γ γ.2 i i.2
    have hj : j = ⟨(γ : GLV V) i, hγi⟩ := by
      apply ψ.injective
      apply Subtype.ext
      rw [hyy', hψ γ i ⟨(γ : GLV V) i, hγi⟩ rfl]
    subst hj
    have hcγ : c ((γ : GLV V) i) = (γ : GLV V) (c i) := hc γ γ.2 i i.2
    have e : (⟨c ((γ : GLV V) i), hcI _ hγi⟩ : ↥I) =
        ⟨(γ : GLV V) (c i), hinv γ γ.2 _ (hcI i i.2)⟩ := Subtype.ext hcγ
    rw [hT, hT, ← hψ γ ⟨c i, hcI i i.2⟩ ⟨(γ : GLV V) (c i), hinv γ γ.2 _ (hcI i i.2)⟩ rfl]
    exact congrArg (fun z : ↥I => ((ψ z : ↥(permCore 5)) : Fin 5 → ZMod 2)) e)
  have hcv : ∀ v (hv : v ∈ I), c v = a • v := by
    intro v hv
    have h1 : ψ ⟨c v, hcI v hv⟩ = a • ψ ⟨v, hv⟩ := (hT ⟨v, hv⟩).symm.trans (ha _)
    have h2 : (⟨c v, hcI v hv⟩ : ↥I) = a • ⟨v, hv⟩ := by
      apply ψ.injective
      rw [h1, map_smul]
    exact congrArg Subtype.val h2
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfin
    omega
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with h0 | h1
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    apply hv0
    have : c v = 0 := by rw [hcv v hv, h0, zero_smul]
    exact c.injective (by rw [this, map_zero])
  · intro v hv
    rw [hcv v hv, h1, one_smul]

end G11

end CFSG.Quasithin
