module

public import CFSG.Quasithin.Background.FFC5Fox
public import CFSG.Quasithin.Background.FFC5Coh3
public import CFSG.Quasithin.Background.FFC4Five

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin.JonesParshall

section S5

@[expose] def sum5 : (Fin 5 → ZMod 2) →+ ZMod 2 where
  toFun x := ∑ i, x i
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

@[expose] def E5sub : AddSubgroup (Fin 5 → ZMod 2) := AddMonoidHom.ker sum5

theorem mem_E5sub {x : Fin 5 → ZMod 2} : x ∈ E5sub ↔ ∑ i, x i = 0 := AddMonoidHom.mem_ker

@[expose] def E5 : Type := ↥E5sub

instance : AddCommGroup E5 := AddSubgroup.toAddCommGroup E5sub

instance : DecidablePred (· ∈ E5sub) := fun x => decidable_of_iff (∑ i, x i = 0) mem_E5sub.symm

instance : DecidableEq E5 := inferInstanceAs (DecidableEq ↥E5sub)

instance : Fintype E5 := inferInstanceAs (Fintype ↥E5sub)

@[expose] def permE (σ : Equiv.Perm (Fin 5)) (x : E5) : E5 :=
  ⟨fun i => x.1 (σ⁻¹ i), by
    have h : ∑ i, x.1 i = 0 := mem_E5sub.1 x.2
    rw [mem_E5sub, ← h]
    exact Equiv.sum_comp σ⁻¹ x.1⟩

@[expose] def muE : Equiv.Perm (Fin 5) →* AddMonoid.End E5 where
  toFun σ := AddMonoidHom.mk' (permE σ) (fun _ _ => rfl)
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

@[expose] def gens5 : Fin 2 → Equiv.Perm (Fin 5) := ![Equiv.swap 0 1, finRotate 5]

@[expose] def rels5 : List (List (Fin 2)) :=
  [[0, 0], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1]]

theorem rels5_spec : ∀ r ∈ rels5, wordEval gens5 r = 1 := by decide +kernel

theorem sol5 : ∀ v₀ v₁ : E5, (∀ r ∈ rels5, foxEval muE gens5 ![v₀, v₁] r = 0) →
    ∃ m, v₀ = muE (gens5 0) m - m ∧ v₁ = muE (gens5 1) m - m := by decide +kernel

theorem closure_gens5 : Subgroup.closure (Set.range gens5) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 5)
    (isCycle_finRotate_of_le (by norm_num)) (by simp) 0
  have h2 : Set.range gens5 = {finRotate 5, Equiv.swap 0 (finRotate 5 0)} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · right
        show Equiv.swap 0 1 = Equiv.swap 0 (finRotate 5 0)
        rfl
      · left
        rfl
    · rintro (rfl | rfl)
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  rw [h2]
  exact h

theorem Z1A_muE_le_B1A : Z1A muE ≤ B1A muE :=
  Z1A_le_B1A_of_fox muE closure_gens5 rels5_spec sol5

end S5

section Transport

variable {V : Type} [CommGroup V]

theorem sym5_h1_vanish {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (h : (FFModel.symDn 5).Realizes L W ⊥) : ∀ f ∈ Z1A (muW hLW), f ∈ B1A (muW hLW) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨f₀, hfs, hfk, hfe⟩ := RealizesVia.secMap symDn_ker_five hπ
  have hf₀i : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  let val : ↥W → (Fin 5 → ZMod 2) := fun u =>
    fun i => Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ u : ↥(FFModel.symDn 5).sec) :
      (FFModel.symDn 5).Amb)) i
  have hsec : ∀ u : ↥W, ∑ i, val u i = 0 := fun u => (f₀ u).2
  let θ₀ : Additive ↥W →+ E5 :=
    { toFun := fun w => ⟨val (Additive.toMul w), mem_E5sub.2 (hsec _)⟩
      map_zero' := by
        apply Subtype.ext
        funext i
        show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ 1 : ↥(FFModel.symDn 5).sec) :
          (FFModel.symDn 5).Amb)) i = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        apply Subtype.ext
        funext i
        show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ (Additive.toMul x * Additive.toMul y) :
          ↥(FFModel.symDn 5).sec) : (FFModel.symDn 5).Amb)) i = _
        rw [map_mul]
        rfl }
  have hθi : Function.Injective θ₀ := by
    intro x y hxy
    have h1 : ∀ i, val (Additive.toMul x) i = val (Additive.toMul y) i := fun i =>
      congrFun (congrArg Subtype.val hxy) i
    have h2 : f₀ (Additive.toMul x) = f₀ (Additive.toMul y) := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      exact h1 i
    exact Additive.toMul.injective (hf₀i h2)
  have hθs : Function.Surjective θ₀ := by
    intro e
    have hm : (show G6.PermMod 5 from Multiplicative.ofAdd e.1) ∈ (FFModel.symDn 5).sec := mem_E5sub.1 e.2
    obtain ⟨u, hu⟩ := hfs ⟨_, hm⟩
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    funext i
    show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ u : ↥(FFModel.symDn 5).sec) :
      (FFModel.symDn 5).Amb)) i = e.1 i
    rw [hu]
    rfl
  let θ : Additive ↥W ≃+ E5 := AddEquiv.ofBijective θ₀ ⟨hθi, hθs⟩
  have hθ : ∀ σ w, θ (muW hLW (π σ) w) = muE σ (θ w) := by
    intro σ w
    apply Subtype.ext
    funext i
    have hu : ((π σ : ↥L) : MulAut V) ((Additive.toMul w : ↥W) : V) ∈ W :=
      hLW _ (π σ).2 _ (Additive.toMul w).2
    have h1 := hfe σ (Additive.toMul w) hu
    show Multiplicative.toAdd (show G6.PermMod 5 from ((f₀ (Additive.toMul (muW hLW (π σ) w)) :
      ↥(FFModel.symDn 5).sec) : (FFModel.symDn 5).Amb)) i = _
    rw [muW_apply, h1]
    rfl
  intro f hf
  have hf' := pullback_mem_Z1A hLW π muE θ hθ hf
  exact mem_B1A_of_pullback hLW π hπ.1 muE θ hθ (Z1A_muE_le_B1A hf')

end Transport

end FFC

end CFSG.Quasithin
