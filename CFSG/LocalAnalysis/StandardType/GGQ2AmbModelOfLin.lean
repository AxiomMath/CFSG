module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

section LinInv

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

@[expose] def ggLinInv (ι : Additive E ≃+ V) (T : V ≃ₗ[ZMod p] V) : MulAut E :=
  MulEquiv.toAdditive.symm (ι.trans (T.toAddEquiv.trans ι.symm))

theorem ggLin_ggLinInv (ι : Additive E ≃+ V) (T : V ≃ₗ[ZMod p] V) :
    ggLin (p := p) ι (ggLinInv ι T) = T := by
  refine LinearEquiv.ext fun v => ?_
  simp [ggLin_apply, ggLinInv]

theorem ggLin_surjective (ι : Additive E ≃+ V) : Function.Surjective (ggLin (p := p) ι) :=
  fun T => ⟨ggLinInv ι T, ggLin_ggLinInv ι T⟩

theorem ggLinInv_eq_iff (ι : Additive E ≃+ V) (T : V ≃ₗ[ZMod p] V) (φ : MulAut E) :
    ggLinInv ι T = φ ↔ ggLin (p := p) ι φ = T := by
  constructor
  · rintro rfl
    exact ggLin_ggLinInv ι T
  · intro h
    apply ggLin_injective (p := p) ι
    rw [ggLin_ggLinInv, h]

theorem eq_closure_ggLinInv_of_map_eq (ι : Additive E ≃+ V) {A : Subgroup (MulAut E)}
    {S : Set (V ≃ₗ[ZMod p] V)} (h : A.map (ggLin (p := p) ι) = Subgroup.closure S) :
    A = Subgroup.closure (ggLinInv ι '' S) := by
  apply Subgroup.map_injective (ggLin_injective (p := p) ι)
  rw [h, MonoidHom.map_closure, Set.image_image]
  simp only [ggLin_ggLinInv, Set.image_id']

theorem mem_ggFixedSubmodule_closure_iff (hp2 : p ≠ 2) (ι : Additive E ≃+ V) {κ : Type*}
    (φ : κ → MulAut E) (h : κ → V) (α : κ → Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) (hdiag : ∀ i, α i (h i) = 2)
    (S : Set κ) (v : V) :
    v ∈ ggFixedSubmodule (p := p) ι (Subgroup.closure (φ '' S)) ↔ ∀ i ∈ S, α i v = 0 := by
  rw [mem_ggFixedSubmodule_iff]
  constructor
  · intro hv i hi
    have hfix : ggLin (p := p) ι (φ i) v = v := hv _ (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    rw [hlin, sub_eq_self] at hfix
    have hh : h i ≠ 0 := by
      intro h0
      apply zmod_two_ne_zero hp2
      rw [← hdiag i, h0, map_zero]
    exact (smul_eq_zero.mp hfix).resolve_right hh
  · intro hv ψ hψ
    induction hψ using Subgroup.closure_induction with
    | mem ψ hψ =>
      obtain ⟨i, hi, rfl⟩ := hψ
      rw [hlin, hv i hi, zero_smul, sub_zero]
    | one => simp
    | mul ψ χ _ _ hψ hχ =>
      rw [map_mul, LinearEquiv.mul_apply, hχ, hψ]
    | inv ψ _ hψ =>
      calc ggLin (p := p) ι ψ⁻¹ v = ggLin (p := p) ι ψ⁻¹ (ggLin (p := p) ι ψ v) := by rw [hψ]
        _ = v := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

end LinInv

section Models

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}

namespace GGQ2Lin

@[expose] noncomputable def simpleAut (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V) (k : Λ.ι) : MulAut ↥Bs :=
  ggLinInv ι (Λ.simpleRefl k)

theorem ggLin_simpleAut (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V) (k : Λ.ι) (w : Λ.V) :
    ggLin (p := p) ι (Λ.simpleAut ι k) w = w - Λ.root k w • Λ.coroot k := by
  rw [simpleAut, ggLin_ggLinInv]
  exact Module.reflection_apply w (Λ.root_coroot_self k)

theorem closure_simpleAut_eq (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V) {A : Subgroup (MulAut ↥Bs)}
    {S : Set Λ.ι} (h : A.map (ggLin (p := p) ι) = Λ.parab S) :
    A = Subgroup.closure (Λ.simpleAut ι '' S) := by
  rw [eq_closure_ggLinInv_of_map_eq ι h, Set.image_image]
  rfl

theorem mem_ggFixedSubmodule_simpleAut_iff (hp2 : p ≠ 2) (Λ : GGQ2Lin p)
    (ι : Additive ↥Bs ≃+ Λ.V) (S : Set Λ.ι) (v : Λ.V) :
    v ∈ ggFixedSubmodule (p := p) ι (Subgroup.closure (Λ.simpleAut ι '' S)) ↔
      ∀ k ∈ S, Λ.root k v = 0 :=
  mem_ggFixedSubmodule_closure_iff hp2 ι (Λ.simpleAut ι) Λ.coroot Λ.root (Λ.ggLin_simpleAut ι)
    Λ.root_coroot_self S v

theorem simpleAut_apply_of_root_eq_zero (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V) (k : Λ.ι)
    (b : ↥Bs) (hb : Λ.root k (ι (Additive.ofMul b)) = 0) : Λ.simpleAut ι k b = b := by
  rw [ggLin_fix_iff (p := p) ι, ggLin_simpleAut, hb, zero_smul, sub_zero]

theorem ggFixedSubmodule_eq_span (hp2 : p ≠ 2) (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V)
    {A : Subgroup (MulAut ↥Bs)} {S : Set Λ.ι} (h : A.map (ggLin (p := p) ι) = Λ.parab S)
    (u : Λ.V) (hfix : ∀ v, (∀ k ∈ S, Λ.root k v = 0) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    ggFixedSubmodule (p := p) ι A = Submodule.span (ZMod p) {u} := by
  ext v
  rw [Λ.closure_simpleAut_eq ι h, Λ.mem_ggFixedSubmodule_simpleAut_iff hp2 ι S v, hfix]

@[expose] noncomputable def toAmbModel (hp2 : p ≠ 2) (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V)
    (hx : x ∈ Bs) (hy : y ∈ Bs) {L H : Subgroup G}
    (hL : (ggAutomizer L Bs).map (ggLin (p := p) ι) = Λ.parab {k | k ≠ Λ.a})
    (ha : Λ.simpleRefl Λ.a ∈ (ggAutomizer H Bs).map (ggLin (p := p) ι))
    (hfix : ∀ v, (∀ k ∈ {k | k ≠ Λ.a}, Λ.root k v = 0) ↔
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)})
    (hyJ : ∀ k, k ≠ Λ.a → k ≠ Λ.b → Λ.root k (ι (Additive.ofMul ⟨y, hy⟩)) = 0) :
    GGQTwoAmbModel p Bs x y L H where
  ι := Λ.ι
  coxeter := Λ.coxeter
  cartan := Λ.cartan
  V := Λ.V
  model := ι
  hx := hx
  hy := hy
  simple := Λ.simpleAut ι
  coroot := Λ.coroot
  root := Λ.root
  a := Λ.a
  b := Λ.b
  a_ne_b := Λ.a_ne_b
  a_leaf := Λ.a_leaf
  isWeyl := Λ.isWeyl
  isCartan := Λ.isCartan
  pairing := Λ.pairing
  simple_apply := Λ.ggLin_simpleAut ι
  automizer_L := Λ.closure_simpleAut_eq ι hL
  simple_a_mem := by
    obtain ⟨φ, hφ, hφa⟩ := Subgroup.mem_map.mp ha
    rwa [simpleAut, (ggLinInv_eq_iff ι _ φ).mpr hφa]
  fixed_x := Λ.ggFixedSubmodule_eq_span hp2 ι hL _ hfix
  y_fixed_J k hka hkb := Λ.simpleAut_apply_of_root_eq_zero ι k _ (hyJ k hka hkb)

@[expose] noncomputable def toModel (hp2 : p ≠ 2) (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V)
    (hx : x ∈ Bs) (hy : y ∈ Bs) {D L J K : Subgroup G}
    (hL : (ggAutomizer L Bs).map (ggLin (p := p) ι) = Λ.parab {k | k ≠ Λ.a})
    (hK : (ggAutomizer K Bs).map (ggLin (p := p) ι) = Λ.parab {k | k ≠ Λ.b})
    (hfixx : ∀ v, (∀ k ∈ {k | k ≠ Λ.a}, Λ.root k v = 0) ↔
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)})
    (hfixy : ∀ v, (∀ k ∈ {k | k ≠ Λ.b}, Λ.root k v = 0) ↔
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨y, hy⟩)}) :
    GGQTwoModel p Bs x y D L J K where
  ι := Λ.ι
  coxeter := Λ.coxeter
  cartan := Λ.cartan
  V := Λ.V
  model := ι
  hx := hx
  hy := hy
  simple := Λ.simpleAut ι
  coroot := Λ.coroot
  root := Λ.root
  a := Λ.a
  b := Λ.b
  a_ne_b := Λ.a_ne_b
  a_leaf := Λ.a_leaf
  isWeyl := Λ.isWeyl
  isCartan := Λ.isCartan
  pairing := Λ.pairing
  simple_apply := Λ.ggLin_simpleAut ι
  automizer_L := Λ.closure_simpleAut_eq ι hL
  automizer_K := Λ.closure_simpleAut_eq ι hK
  fixed_x := Λ.ggFixedSubmodule_eq_span hp2 ι hL _ hfixx
  fixed_y := Λ.ggFixedSubmodule_eq_span hp2 ι hK _ hfixy

theorem exists_ambModel (hp2 : p ≠ 2) (Λ : GGQ2Lin p) (ι : Additive ↥Bs ≃+ Λ.V)
    (hx : x ∈ Bs) (hy : y ∈ Bs) {L H : Subgroup G}
    (hL : (ggAutomizer L Bs).map (ggLin (p := p) ι) = Λ.parab {k | k ≠ Λ.a})
    (ha : Λ.simpleRefl Λ.a ∈ (ggAutomizer H Bs).map (ggLin (p := p) ι))
    (hfix : ∀ v, (∀ k ∈ {k | k ≠ Λ.a}, Λ.root k v = 0) ↔
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)})
    (hyJ : ∀ k, k ≠ Λ.a → k ≠ Λ.b → Λ.root k (ι (Additive.ofMul ⟨y, hy⟩)) = 0)
    (hB : Λ.Basis) (hdet : ((Λ.cartan.det : ℤ) : ZMod p) ≠ 0)
    (hdetA : ((Λ.cartan.submatrix (fun i : {k // k ≠ Λ.a} => (i : Λ.ι))
      (fun i : {k // k ≠ Λ.a} => (i : Λ.ι))).det : ZMod p) ≠ 0) :
    ∃ M : GGQTwoAmbModel p Bs x y L H, GGQTwoAmbBasis M ∧
      ((M.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
      ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0 :=
  ⟨Λ.toAmbModel hp2 ι hx hy hL ha hfix hyJ, hB, hdet, hdetA⟩

end GGQ2Lin

theorem mem_map_ggAutomizer_sup {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {L K : Subgroup G} {T : V ≃ₗ[ZMod p] V}
    (hT : T ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ⊔
      (ggAutomizer K Bs).map (ggLin (p := p) ι)) :
    T ∈ (ggAutomizer (L ⊔ K) Bs).map (ggLin (p := p) ι) :=
  sup_le (Subgroup.map_mono (ggAutomizer_mono Bs le_sup_left))
    (Subgroup.map_mono (ggAutomizer_mono Bs le_sup_right)) hT

end Models

end CFSG.StandardType

end
