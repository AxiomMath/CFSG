module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CardZvSq
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
  CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G] [Finite G]

theorem card_mul_le_card_sup_of_inf_eq_bot {A B : Subgroup G} (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card (A ⊔ B : Subgroup G) := by
  let f : A × B → (A ⊔ B : Subgroup G) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
    have h1 : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [hab']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * (a : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [h, Subgroup.mem_bot] at h2
    have ha : (a : G) = (a' : G) := by
      calc (a : G) = (a' : G) * ((a' : G)⁻¹ * (a : G)) := by group
        _ = (a' : G) := by rw [h2, mul_one]
    have hb : (b : G) = (b' : G) := by
      rw [ha] at hab'
      exact mul_left_cancel hab'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  calc Nat.card A * Nat.card B = Nat.card (A × B) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (A ⊔ B : Subgroup G) := Nat.card_le_card_of_injective f hf

theorem Zv_sup_eq_and_inf_eq_bot {H M S : Subgroup G} (hA : F53Amalgam H M S) {α β γ : Geo H M}
    (hα : vtype α = true)
    (_hb : bAt α = bMin H M) (hβ : β ∈ nbrs α) (hγ : γ ∈ nbrs α) (hne : β ≠ γ)
    (hz : Zv β ≤ centerOf (stab β)) :
    Zv β ⊔ Zv γ = Zv α ∧ Zv β ⊓ Zv γ = ⊥ := by
  have hαβ : (graph (H ⊔ M) H M).Adj α β := hβ
  have hαγ : (graph (H ⊔ M) H M).Adj α γ := hγ
  have hadjβ : α ∈ nbrs β := hαβ.symm
  have hadjγ : α ∈ nbrs γ := hαγ.symm
  have hvβ : vtype β = false := by
    have h := vtype_ne_of_adj hαβ
    rw [hα] at h
    cases hv : vtype β
    · rfl
    · exact absurd hv.symm h
  have hvγ : vtype γ = false := by
    have h := vtype_ne_of_adj hαγ
    rw [hα] at h
    cases hv : vtype γ
    · rfl
    · exact absurd hv.symm h
  have hzγ : Zv γ ≤ centerOf (stab γ) := by
    have h1 : Zv γ = quasithinOmegaOneCenter (stab γ) :=
      Zv_central_of_conj hA (hvβ.trans hvγ.symm) (Zv_eq_omegaOneCenter_of_central hA hz)
    rw [h1]
    exact omegaOneCenter_le_centerOf_self _
  obtain ⟨hZβeq, hZβα⟩ := Zv_eq_omegaOneCenter_inf hA hadjβ hz
  obtain ⟨hZγeq, hZγα⟩ := Zv_eq_omegaOneCenter_inf hA hadjγ hzγ
  have hinf : Zv β ⊓ Zv γ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxβ, hxγ⟩ := hx
    have hcβ : ∀ y ∈ (stab α ⊓ stab β : Subgroup G), y * x = x * y := by
      have h := hxβ
      rw [← Zv_inf_centralizer_edge_eq hA hαβ hz] at h
      exact fun y hy => Subgroup.mem_centralizer_iff.mp h.2 y hy
    have hcγ : ∀ y ∈ (stab α ⊓ stab γ : Subgroup G), y * x = x * y := by
      have h := hxγ
      rw [← Zv_inf_centralizer_edge_eq hA hαγ hzγ] at h
      exact fun y hy => Subgroup.mem_centralizer_iff.mp h.2 y hy
    have hxα : x ∈ stab α := by
      have h2 : x ∈ (stab β ⊓ stab α : Subgroup G) := by
        have h := hxβ
        rw [hZβeq] at h
        exact (omegaOneCenter_le_centerOf_self _ h).1
      exact h2.2
    have hcen : ∀ y ∈ stab α, y * x = x * y := by
      intro y hy
      have hsup : stab α ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← sup_edges_eq_stab hA hα hβ hγ hne]
        refine sup_le ?_ ?_
        · intro z hz'
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact (hcβ z hz').symm
        · intro z hz'
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact (hcγ z hz').symm
      have := Subgroup.mem_centralizer_iff.mp (hsup hy) x (Set.mem_singleton x)
      exact this.symm
    have hxcen : x ∈ centerOf (stab α) :=
      ⟨hxα, Subgroup.mem_centralizer_iff.mpr (fun y hy => hcen y hy)⟩
    rw [centerOf_eq_bot_of_Zv_central hA hadjβ hz, Subgroup.mem_bot] at hxcen
    exact hxcen
  have hsup : Zv β ⊔ Zv γ ≤ Zv α := sup_le hZβα hZγα
  have hcardβγ : Nat.card (Zv γ) = Nat.card (Zv β) := by
    have h1 := card_Zv_eq_sq hA hα hαβ hz
    have h2 := card_Zv_eq_sq hA hα hαγ hzγ
    have h3 : Nat.card (Zv β) ^ 2 = Nat.card (Zv γ) ^ 2 := h1.symm.trans h2
    exact (Nat.pow_left_injective (by norm_num)) h3.symm
  have hcard : Nat.card (Zv α) ≤ Nat.card (Zv β ⊔ Zv γ : Subgroup G) := by
    have hlow := card_mul_le_card_sup_of_inf_eq_bot hinf
    rw [hcardβγ] at hlow
    rw [card_Zv_eq_sq hA hα hαβ hz, pow_two]
    exact hlow
  exact ⟨Subgroup.eq_of_le_of_card_ge hsup hcard, hinf⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
