module

public import CFSG.LieType.Universal.Spin.Forms

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CliffordAlgebra QuadraticMap

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem cliffMap_star (f : Q →qᵢ Q) (x : CliffordAlgebra Q) :
    star (CliffordAlgebra.map f x) = CliffordAlgebra.map f (star x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, star_algebraMap, AlgHom.commutes]
  | ι m => rw [CliffordAlgebra.map_apply_ι, star_ι, star_ι, map_neg, CliffordAlgebra.map_apply_ι]
  | mul a b ha hb => rw [map_mul, star_mul, star_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, star_add, star_add, map_add, ha, hb]

theorem cliffMap_mem_even (f : Q →qᵢ Q) {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) :
    CliffordAlgebra.map f x ∈ evenOdd Q 0 := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q _ _) ih

theorem cliffMap_lipschitz (f : Q →qᵢ Q) {u : (CliffordAlgebra Q)ˣ} (hu : u ∈ lipschitzGroup Q) :
    Units.map (CliffordAlgebra.map f).toMonoidHom u ∈ lipschitzGroup Q := by
  have key : lipschitzGroup Q ≤ (lipschitzGroup Q).comap (Units.map (CliffordAlgebra.map f).toMonoidHom) := by
    unfold lipschitzGroup
    rw [Subgroup.closure_le]
    rintro u ⟨m, hm⟩
    refine Subgroup.subset_closure ⟨f m, ?_⟩
    show (ι Q) (f m) = ↑(Units.map (CliffordAlgebra.map f).toMonoidHom u)
    rw [Units.coe_map]
    show (ι Q) (f m) = (CliffordAlgebra.map f) ↑u
    rw [← hm, CliffordAlgebra.map_apply_ι]
  exact key hu

theorem cliffMap_mem_spinGroup (f : Q →qᵢ Q) {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) :
    CliffordAlgebra.map f x ∈ spinGroup Q := by
  rw [spinGroup.mem_iff] at hx ⊢
  obtain ⟨hp, he⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [pinGroup.mem_iff] at hp ⊢
    obtain ⟨⟨u, hu, rfl⟩, hun⟩ := hp
    refine ⟨⟨Units.map (CliffordAlgebra.map f).toMonoidHom u, cliffMap_lipschitz f hu, ?_⟩, ?_⟩
    · simp
    · rw [Unitary.mem_iff] at hun ⊢
      obtain ⟨h1, h2⟩ := hun
      refine ⟨?_, ?_⟩
      · rw [cliffMap_star, ← map_mul, h1, map_one]
      · rw [cliffMap_star, ← map_mul, h2, map_one]
  · have he' : x ∈ evenOdd Q 0 := he
    exact cliffMap_mem_even f he'

@[expose] def spinMapOfIso (f : Q →qᵢ Q) : spinGroup Q →* spinGroup Q where
  toFun x := ⟨CliffordAlgebra.map f x, cliffMap_mem_spinGroup f x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem coe_spinMapOfIso (f : Q →qᵢ Q) (x : spinGroup Q) :
    ((spinMapOfIso f x : spinGroup Q) : CliffordAlgebra Q) = CliffordAlgebra.map f x := rfl

theorem cliffMap_cliffMap (f : Q →qᵢ Q) (hf : ∀ v, f (f v) = v) (x : CliffordAlgebra Q) :
    CliffordAlgebra.map f (CliffordAlgebra.map f x) = x := by
  have h : f.comp f = QuadraticMap.Isometry.id Q := by
    ext v
    exact hf v
  have h2 : (CliffordAlgebra.map f).comp (CliffordAlgebra.map f) = AlgHom.id K (CliffordAlgebra Q) := by
    rw [CliffordAlgebra.map_comp_map, h, CliffordAlgebra.map_id]
  exact congrArg (fun g : CliffordAlgebra Q →ₐ[K] CliffordAlgebra Q => g x) h2

@[expose] def spinAutOfInvol (f : Q →qᵢ Q) (hf : ∀ v, f (f v) = v) : spinGroup Q ≃* spinGroup Q :=
  MonoidHom.toMulEquiv (spinMapOfIso f) (spinMapOfIso f)
    (MonoidHom.ext fun x => Subtype.ext (cliffMap_cliffMap f hf x))
    (MonoidHom.ext fun x => Subtype.ext (cliffMap_cliffMap f hf x))

@[simp] theorem coe_spinAutOfInvol (f : Q →qᵢ Q) (hf : ∀ v, f (f v) = v) (x : spinGroup Q) :
    ((spinAutOfInvol f hf x : spinGroup Q) : CliffordAlgebra Q) = CliffordAlgebra.map f x := rfl

end Generic

section Swap

open CFSG.LieType.Universal.Spin

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def swapLin (i₀ : Fin n) : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap (Sum.inl i₀) (Sum.inr i₀))

theorem swapLin_apply (i₀ : Fin n) (v : Fin n ⊕ Fin n → K) (a : Fin n ⊕ Fin n) :
    swapLin n K i₀ v a = v (Equiv.swap (Sum.inl i₀) (Sum.inr i₀) a) := rfl

theorem quadPlus_swapLin (i₀ : Fin n) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (swapLin n K i₀ v) = quadPlus n K v := by
  rw [quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [swapLin_apply, swapLin_apply]
  by_cases hi : i = i₀
  · rw [hi]
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
  · have h1 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := fun h => hi (Sum.inl_injective h)
    have h2 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := Sum.inr_ne_inl
    have h3 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := Sum.inl_ne_inr
    have h4 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := fun h => hi (Sum.inr_injective h)
    rw [Equiv.swap_apply_of_ne_of_ne h1 h3, Equiv.swap_apply_of_ne_of_ne h2 h4]

@[expose] def swapIso (i₀ : Fin n) : quadPlus n K →qᵢ quadPlus n K where
  toLinearMap := (swapLin n K i₀ : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))
  map_app' := quadPlus_swapLin n K i₀

theorem swapIso_apply (i₀ : Fin n) (v : Fin n ⊕ Fin n → K) :
    swapIso n K i₀ v = swapLin n K i₀ v := rfl

theorem swapIso_swapIso (i₀ : Fin n) (v : Fin n ⊕ Fin n → K) :
    swapIso n K i₀ (swapIso n K i₀ v) = v := by
  funext a
  simp only [swapIso_apply, swapLin_apply, Equiv.swap_apply_self]

@[expose] def graphSpin (i₀ : Fin n) : spinGroup (quadPlus n K) ≃* spinGroup (quadPlus n K) :=
  spinAutOfInvol (swapIso n K i₀) (swapIso_swapIso n K i₀)

end Swap

end CFSG.RankThree.GF2n.Smith81.D6Spin
