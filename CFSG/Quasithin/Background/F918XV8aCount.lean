module

public import CFSG.Quasithin.Background.F918X0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

theorem eq_of_forall_inv_mul_mem_center {S : Type*} [Group S] [Group.IsPerfect S]
    {σ₁ σ₂ : MulAut S} (h : ∀ g : S, (σ₁ g)⁻¹ * σ₂ g ∈ Subgroup.center S) : σ₁ = σ₂ := by
  let δ : S →* Subgroup.center S :=
    { toFun := fun g => ⟨(σ₁ g)⁻¹ * σ₂ g, h g⟩
      map_one' := by ext; simp
      map_mul' := fun g g' => by
        ext
        have hc := Subgroup.mem_center_iff.mp (h g) (σ₁ g')⁻¹
        change (σ₁ (g * g'))⁻¹ * σ₂ (g * g') = ((σ₁ g)⁻¹ * σ₂ g) * ((σ₁ g')⁻¹ * σ₂ g')
        calc (σ₁ (g * g'))⁻¹ * σ₂ (g * g')
            = (σ₁ g')⁻¹ * ((σ₁ g)⁻¹ * σ₂ g) * σ₂ g' := by rw [map_mul, map_mul]; group
          _ = ((σ₁ g)⁻¹ * σ₂ g) * (σ₁ g')⁻¹ * σ₂ g' := by rw [hc]
          _ = ((σ₁ g)⁻¹ * σ₂ g) * ((σ₁ g')⁻¹ * σ₂ g') := by group }
  ext g
  have h1 : δ g = 1 := Abelianization.commutator_subset_ker δ Group.IsPerfect.mem_commutator
  have h2 : (σ₁ g)⁻¹ * σ₂ g = 1 := congrArg Subtype.val h1
  exact inv_mul_eq_one.mp h2

theorem card_mulAut_le_of_isHat {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card (MulAut X) ≤ 1440 := by
  obtain ⟨hq, -, ⟨e⟩⟩ := h
  have : Group.IsPerfect X := hq.1
  let f : MulAut X → MulAut (X ⧸ Subgroup.center X) := fun β =>
    QuotientGroup.congr _ _ β (Subgroup.map_center_eq β)
  have hf : Function.Injective f := by
    intro β γ hβγ
    refine eq_of_forall_inv_mul_mem_center fun g => ?_
    have h1 := congrArg (fun φ : MulAut (X ⧸ Subgroup.center X) => φ (QuotientGroup.mk g)) hβγ
    simp only [f, QuotientGroup.congr_mk] at h1
    exact QuotientGroup.eq.mp h1
  have : Finite (MulAut (X ⧸ Subgroup.center X)) := MulEquiv.finite_left
  calc Nat.card (MulAut X) ≤ Nat.card (MulAut (X ⧸ Subgroup.center X)) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_congr (MulAut.congr e).toEquiv
    _ = 1440 := CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6

theorem twoClassMod_of_perm_family {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    [Finite (MulAut ↥L)] (hcard : Nat.card (MulAut ↥L) ≤ 1440)
    (f : Equiv.Perm (Fin 6) → MulAut ↥L) (hf : Function.Injective f)
    (hr : ∀ σ, f σ ∈ realized L) : TwoClassMod L := by
  apply twoClassMod_of_card
  have h1 : Nat.card (Equiv.Perm (Fin 6)) ≤ Nat.card (realized L) :=
    Nat.card_le_card_of_injective (fun σ => (⟨f σ, hr σ⟩ : realized L))
      (fun a b hab => hf (congrArg Subtype.val hab))
  have h2 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  omega

end CFSG.Quasithin.F918X
