module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegBasic

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

theorem permDeg_prod_le (A B : Type*) [Group A] [Group B] [Finite A] [Finite B] :
    permDeg (A × B) ≤ permDeg A + permDeg B := by
  obtain ⟨fA, hfA⟩ := exists_injective_permDeg (H := A)
  obtain ⟨fB, hfB⟩ := exists_injective_permDeg (H := B)
  let F : A × B →* Equiv.Perm (Fin (permDeg A) ⊕ Fin (permDeg B)) :=
    (Equiv.Perm.sumCongrHom _ _).comp (fA.prodMap fB)
  have hF : Function.Injective F :=
    Equiv.Perm.sumCongrHom_injective.comp (Prod.map_injective.mpr ⟨hfA, hfB⟩)
  simpa using permDeg_le_of_injective F hF

theorem permDeg_eq_zero_of_subsingleton (H : Type*) [Group H] [Subsingleton H] :
    permDeg H = 0 := by
  have : permDeg H ≤ Nat.card (Fin 0) :=
    permDeg_le_of_injective (1 : H →* Equiv.Perm (Fin 0)) (fun a b _ => Subsingleton.elim a b)
  simpa using this

theorem permDeg_le_of_ker_eq {G Q Ω : Type*} [Group G] [Group Q] [Finite Ω] (π : G →* Q)
    (hπ : Function.Surjective π) (f : G →* Equiv.Perm Ω) (h : f.ker = π.ker) :
    permDeg Q ≤ Nat.card Ω := by
  let e : Q ≃* G ⧸ f.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq h.symm)
  exact permDeg_le_of_injective ((QuotientGroup.kerLift f).comp e.toMonoidHom)
    ((QuotientGroup.kerLift_injective f).comp e.injective)

@[expose] def restrictHom {G Ω : Type*} [Group G] (f : G →* Equiv.Perm Ω) (B : Set Ω)
    (hB : ∀ g x, f g x ∈ B ↔ x ∈ B) : G →* Equiv.Perm B where
  toFun g := (f g).subtypePerm (fun x => hB g x)
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun x => Subtype.ext (by
    show f (g * h) x = f g (f h x)
    rw [map_mul]
    rfl)

theorem restrictHom_apply {G Ω : Type*} [Group G] (f : G →* Equiv.Perm Ω) (B : Set Ω)
    (hB : ∀ g x, f g x ∈ B ↔ x ∈ B) (g : G) (x : B) :
    (restrictHom f B hB g x : Ω) = f g x := rfl

theorem mem_ker_restrictHom {G Ω : Type*} [Group G] (f : G →* Equiv.Perm Ω) (B : Set Ω)
    (hB : ∀ g x, f g x ∈ B ↔ x ∈ B) (g : G) :
    g ∈ (restrictHom f B hB).ker ↔ ∀ x ∈ B, f g x = x := by
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  constructor
  · intro h x hx
    have := congrArg Subtype.val (h ⟨x, hx⟩)
    simpa [restrictHom_apply] using this
  · intro h x
    exact Subtype.ext (by simpa [restrictHom_apply] using h x x.2)

theorem card_add_card_compl {Ω : Type*} [Finite Ω] (O : Set Ω) :
    Nat.card O + Nat.card (Oᶜ : Set Ω) = Nat.card Ω := by
  classical
  rw [← Nat.card_sum]
  exact (Nat.card_congr (Equiv.Set.sumCompl O)).symm.symm

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
