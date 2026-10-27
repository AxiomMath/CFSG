module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.MS93.S46SL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin.MS93.S46 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Comm

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(2, F) V)

@[expose] def sl2Comm (S : Set SL(2, F)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ g ∈ S, ∃ v, w = ρ g v - v}

theorem sub_mem_sl2Comm {S : Set SL(2, F)} {g : SL(2, F)} (hg : g ∈ S) (v : V) :
    ρ g v - v ∈ sl2Comm ρ S :=
  Submodule.subset_span ⟨g, hg, v, rfl⟩

@[expose] def sl2OddComm : Submodule (ZMod 2) V := sl2Comm ρ {g | Odd (orderOf g)}

theorem sub_mem_sl2OddComm {g : SL(2, F)} (hg : Odd (orderOf g)) (v : V) :
    ρ g v - v ∈ sl2OddComm ρ :=
  sub_mem_sl2Comm ρ hg v

theorem dual_apply_apply (g : SL(2, F)) (f : Module.Dual (ZMod 2) V) (v : V) :
    ρ.dual g f v = f (ρ g⁻¹ v) := by
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]

theorem sl2Fix_dual_eq {S : Set SL(2, F)} (hS : ∀ g ∈ S, g⁻¹ ∈ S) :
    sl2Fix ρ.dual S = (sl2Comm ρ S).dualAnnihilator := by
  ext f
  rw [mem_sl2Fix, Submodule.mem_dualAnnihilator]
  constructor
  · intro hf w hw
    have hle : sl2Comm ρ S ≤ LinearMap.ker f := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, hg, v, rfl⟩
      have h1 := LinearMap.congr_fun (hf g⁻¹ (hS g hg)) v
      rw [dual_apply_apply, inv_inv] at h1
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, h1, sub_self]
    exact hle hw
  · intro hf g hg
    refine LinearMap.ext fun v => ?_
    rw [dual_apply_apply]
    have h1 := hf _ (sub_mem_sl2Comm ρ (hS g hg) v)
    rwa [map_sub, sub_eq_zero] at h1

end Comm

section Count

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_mul_card_dualAnnihilator (W : Submodule (ZMod 2) V) :
    Nat.card W * Nat.card W.dualAnnihilator = Nat.card V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W.dualAnnihilator),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), ← pow_add,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]

theorem card_dual_eq : Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Subspace.dual_finrank_eq]

end Count

section Pairing

variable {F : Type*} [Field F]

theorem symp_mulVec_left [CharP F 2] (g : SL(2, F)) (u w : Fin 2 → F) :
    ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 0 * w 1 +
        ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1 * w 0 =
      u 0 * (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 1 +
        u 1 * (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * u 1 * w 1 +
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 * u 0 * w 0) * h2

theorem exists_addMonoidHom_zmod_two_ne_zero [CharP F 2] :
    ∃ (ℓ : F →+ ZMod 2) (c : F), ℓ c ≠ 0 := by
  let _ : Module (ZMod 2) F := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) F, f 1 ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (1 : F)).mp h)
  exact ⟨f.toAddMonoidHom, 1, hf⟩

theorem eq_zero_of_symp (ℓ : F →+ ZMod 2) {c : F} (hc : ℓ c ≠ 0) {u : Fin 2 → F}
    (hu : ∀ w : Fin 2 → F, ℓ (u 0 * w 1 + u 1 * w 0) = 0) : u = 0 := by
  have h0 : u 0 = 0 := by
    by_contra h
    have h1 := hu ![0, c / u 0]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, add_zero,
      mul_div_cancel₀ _ h] at h1
    exact hc h1
  have h1 : u 1 = 0 := by
    by_contra h
    have h2 := hu ![c / u 1, 0]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add,
      mul_div_cancel₀ _ h] at h2
    exact hc h2
  funext i
  fin_cases i
  · exact h0
  · exact h1

end Pairing

section Main

variable {F : Type*} [Field F] [Fintype F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) SL(2, F) V)

theorem natural_of_sl2Comm {n : ℕ} (hF : Fintype.card F = 2 ^ n) (X : Subgroup SL(2, F))
    (hX : IsPGroup 2 X) (hXc : Nat.card X = Nat.card F)
    (hoff : Nat.card (sl2Comm ρ (X : Set SL(2, F))) ≤ Nat.card F) :
    (∀ g : SL(2, F), Odd (orderOf g) → ∀ v, ρ g v = v) ∨
    ∃ γ : (Fin 2 → F) →+ V, Function.Injective γ ∧
      (∀ (g : SL(2, F)) (u : Fin 2 → F),
        γ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) = ρ g (γ u)) ∧
      ∀ v, v ∈ sl2OddComm ρ ↔ ∃ u, γ u = v := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  have hXinv : ∀ g ∈ (X : Set SL(2, F)), g⁻¹ ∈ (X : Set SL(2, F)) := fun g hg => X.inv_mem hg
  have hOinv : ∀ g ∈ {g : SL(2, F) | Odd (orderOf g)}, g⁻¹ ∈ {g : SL(2, F) | Odd (orderOf g)} :=
    fun g (hg : Odd (orderOf g)) => show Odd (orderOf g⁻¹) by rwa [orderOf_inv]
  have hOdd : sl2OddFix ρ.dual = (sl2OddComm ρ).dualAnnihilator := sl2Fix_dual_eq ρ hOinv
  have hsep : ∀ a b : V, (∀ f : Module.Dual (ZMod 2) V, f a = f b) → a = b := by
    intro a b h
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
    intro f
    rw [map_sub, h f, sub_self]
  have hoff' : Nat.card (Module.Dual (ZMod 2) V) ≤
      Nat.card F * Nat.card (sl2Fix ρ.dual (X : Set SL(2, F))) := by
    rw [sl2Fix_dual_eq ρ hXinv, card_dual_eq, ← card_mul_card_dualAnnihilator]
    exact Nat.mul_le_mul_right _ hoff
  rcases natural_of_sl2Fix ρ.dual hF X hX hXc hoff' with htop | ⟨φ, hφs, hφeq, hφker⟩
  · left
    intro g hg v
    refine hsep _ _ fun f => ?_
    have hf : f ∈ sl2OddFix ρ.dual := htop ▸ Submodule.mem_top
    rw [hOdd] at hf
    have h1 := (Submodule.mem_dualAnnihilator f).mp hf _ (sub_mem_sl2OddComm ρ hg v)
    rwa [map_sub, sub_eq_zero] at h1
  right
  obtain ⟨ℓ, c, hc⟩ := exists_addMonoidHom_zmod_two_ne_zero (F := F)
  let ω : (Fin 2 → F) → (Fin 2 → F) →+ ZMod 2 := fun u =>
    ℓ.comp ((AddMonoidHom.mulLeft (u 0)).comp (Pi.evalAddMonoidHom (fun _ => F) 1) +
      (AddMonoidHom.mulLeft (u 1)).comp (Pi.evalAddMonoidHom (fun _ => F) 0))
  have hω : ∀ u w, ω u w = ℓ (u 0 * w 1 + u 1 * w 0) := fun u w => rfl
  let e : (Fin 2 → F) →+ Module.Dual (ZMod 2) (Module.Dual (ZMod 2) V) :=
    { toFun := fun u => ((ω u).comp φ).toZModLinearMap 2
      map_zero' := LinearMap.ext fun f => by
        change ω 0 (φ f) = 0
        rw [hω]
        simp
      map_add' := fun u u' => LinearMap.ext fun f => by
        change ω (u + u') (φ f) = ω u (φ f) + ω u' (φ f)
        rw [hω, hω, hω, ← map_add]
        congr 1
        simp only [Pi.add_apply]
        ring }
  let γ : (Fin 2 → F) →+ V :=
    (Module.evalEquiv (ZMod 2) V).symm.toLinearMap.toAddMonoidHom.comp e
  have hγ : ∀ u f, f (γ u) = ω u (φ f) := fun u f =>
    Module.apply_evalEquiv_symm_apply (ZMod 2) V f (e u)
  have hγinj : Function.Injective γ := by
    refine (injective_iff_map_eq_zero γ).mpr fun u hu => ?_
    refine eq_zero_of_symp ℓ hc fun w => ?_
    obtain ⟨f, rfl⟩ := hφs w
    rw [← hω, ← hγ, hu, map_zero]
  have hγmem : ∀ u, γ u ∈ sl2OddComm ρ := by
    intro u
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := sl2OddComm ρ),
      Submodule.mem_dualCoannihilator]
    intro f hf
    rw [← hOdd, ← hφker] at hf
    rw [hγ, hf, hω]
    simp
  refine ⟨γ, hγinj, fun g u => hsep _ _ fun f => ?_, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · have h1 : f (ρ g (γ u)) = ρ.dual g⁻¹ f (γ u) := by rw [dual_apply_apply, inv_inv]
    rw [h1, hγ, hγ, hφeq, hω, hω, symp_mulVec_left]
  ·
    have hker : Nat.card (sl2OddComm ρ).dualAnnihilator = Nat.card φ.ker :=
      Nat.card_congr (Equiv.subtypeEquivRight fun f => by
        rw [AddMonoidHom.mem_ker, hφker, hOdd])
    have h1 := card_mul_card_dualAnnihilator (sl2OddComm ρ)
    have h2 := φ.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hφs, AddSubgroup.card_top,
      card_dual_eq] at h2
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    have hW : Nat.card (sl2OddComm ρ) = Nat.card (Fin 2 → F) := by
      rw [hker] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, ← h2, mul_comm])
    have hle : γ.range ≤ (sl2OddComm ρ).toAddSubgroup := by
      rintro _ ⟨u, rfl⟩
      exact hγmem u
    have hge : Nat.card (sl2OddComm ρ).toAddSubgroup ≤ Nat.card γ.range := by
      have h3 : Nat.card γ.range = Nat.card (Fin 2 → F) := Nat.card_range_of_injective hγinj
      rw [h3, ← hW]
      rfl
    have heq := AddSubgroup.eq_of_le_of_card_ge hle hge
    have hv' : v ∈ γ.range := by
      rw [heq]
      exact hv
    exact hv'
  · rintro ⟨u, rfl⟩
    exact hγmem u

end Main

end CFSG.Quasithin.MS93.S46R
