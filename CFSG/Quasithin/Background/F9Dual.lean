module

public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.F9Pairing

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem conj_eq_of_mem_V₁ (h : HypF91 T V L V₁ Vp H) {k c : G} (hk : k ∈ H)
    (hc : c ∈ V₁) : k * c * k⁻¹ = c := by
  have := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer hk) c hc
  rw [← this]; group

theorem commutator_mem_V₁ (h : HypF91 T V L V₁ Vp H) {x u : G} (hx : x ∈ pCoreOf 2 H)
    (hu : u ∈ conjClosure Vp H) : x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
  have := V₁.inv_mem (h.commutator_conjClosure_le u hu x hx)
  have e : (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
  rwa [e] at this

theorem commutator_mul_left (h : HypF91 T V L V₁ Vp H) {x₁ x₂ u : G}
    (hx₁ : x₁ ∈ pCoreOf 2 H) (hx₂ : x₂ ∈ pCoreOf 2 H) (hu : u ∈ conjClosure Vp H) :
    (x₁ * x₂) * u * (x₁ * x₂)⁻¹ * u⁻¹ =
      (x₁ * u * x₁⁻¹ * u⁻¹) * (x₂ * u * x₂⁻¹ * u⁻¹) := by
  have h1 := h.commutator_mem_V₁ hx₁ hu
  have h2 := h.commutator_mem_V₁ hx₂ hu
  have hc := h.conj_eq_of_mem_V₁ (pCoreOf_le 2 H hx₁) h2
  have hcomm := isElemAbelian_comm (isElemAbelian_mono h.elemAbelian h.V₁_le_V) h1 h2
  calc (x₁ * x₂) * u * (x₁ * x₂)⁻¹ * u⁻¹
      = (x₁ * (x₂ * u * x₂⁻¹ * u⁻¹) * x₁⁻¹) * (x₁ * u * x₁⁻¹ * u⁻¹) := by group
    _ = (x₂ * u * x₂⁻¹ * u⁻¹) * (x₁ * u * x₁⁻¹ * u⁻¹) := by rw [hc]
    _ = (x₁ * u * x₁⁻¹ * u⁻¹) * (x₂ * u * x₂⁻¹ * u⁻¹) := hcomm.symm

theorem commutator_mul_right (h : HypF91 T V L V₁ Vp H) {x u₁ u₂ : G}
    (hx : x ∈ pCoreOf 2 H) (hu₁ : u₁ ∈ conjClosure Vp H) (hu₂ : u₂ ∈ conjClosure Vp H) :
    x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹ =
      (x * u₁ * x⁻¹ * u₁⁻¹) * (x * u₂ * x⁻¹ * u₂⁻¹) := by
  have h2 := h.commutator_mem_V₁ hx hu₂
  have hu₁H : u₁ ∈ H := pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf hu₁)
  have hc := h.conj_eq_of_mem_V₁ hu₁H h2
  calc x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹
      = (x * u₁ * x⁻¹ * u₁⁻¹) * (u₁ * (x * u₂ * x⁻¹ * u₂⁻¹) * u₁⁻¹) := by group
    _ = (x * u₁ * x⁻¹ * u₁⁻¹) * (x * u₂ * x⁻¹ * u₂⁻¹) := by rw [hc]

theorem commutator_conj (h : HypF91 T V L V₁ Vp H) {k x u : G} (hk : k ∈ H)
    (hx : x ∈ pCoreOf 2 H) (hu : u ∈ conjClosure Vp H) :
    (k * x * k⁻¹) * (k * u * k⁻¹) * (k * x * k⁻¹)⁻¹ * (k * u * k⁻¹)⁻¹ =
      x * u * x⁻¹ * u⁻¹ := by
  have hc := h.conj_eq_of_mem_V₁ hk (h.commutator_mem_V₁ hx hu)
  rw [← hc]; group

theorem F97_surj (h : HypF91 T V L V₁ Vp H) (hU : IsElemAbelian 2 (conjClosure Vp H))
    (f : ↥(conjClosure Vp H) →* ↥V₁)
    (hf : ∀ u : ↥(conjClosure Vp H), (∀ x ∈ pCoreOf 2 H, x * (u : G) = (u : G) * x) → f u = 1) :
    ∃ x ∈ pCoreOf 2 H, ∀ u : ↥(conjClosure Vp H), (f u : G) = x * u * x⁻¹ * u⁻¹ := by
  have hV₁ : IsElemAbelian 2 V₁ := isElemAbelian_mono h.elemAbelian h.V₁_le_V
  let _ : CommGroup ↥(conjClosure Vp H) := commGroupOfElemAbelian hU
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥(conjClosure Vp H), u ^ 2 = 1 := fun u => Subtype.ext (by
    simpa using hU.2 u u.2)
  let β : ↥(pCoreOf 2 H) → ↥(conjClosure Vp H) → ↥V₁ := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, h.commutator_mem_V₁ x.2 u.2⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (h.commutator_mul_left x₁.2 x₂.2 u.2)
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (h.commutator_mul_right x.2 u₁.2 u₂.2)
  have hsurj := (pairing_dual hB h.card_V₁ (pairingToHom β h1 h2)).1 f (fun u hu => hf u (by
    intro x hx
    have := congrArg Subtype.val (hu ⟨x, hx⟩)
    have h3 : x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1 := this
    calc x * (u : G) = (x * (u : G) * x⁻¹ * (u : G)⁻¹) * (u : G) * x := by group
      _ = (u : G) * x := by rw [h3]; group))
  obtain ⟨x, hx⟩ := hsurj
  refine ⟨x, x.2, fun u => ?_⟩
  have := congrArg (fun φ : ↥(conjClosure Vp H) →* ↥V₁ => ((φ u : ↥V₁) : G)) hx
  simpa [pairingToHom, β] using this.symm

theorem F97_card_mul (h : HypF91 T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H)) :
    Nat.card (pCoreOf 2 H) *
        Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) =
      Nat.card (conjClosure Vp H) *
        Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) := by
  have hV₁ : IsElemAbelian 2 V₁ := isElemAbelian_mono h.elemAbelian h.V₁_le_V
  let _ : CommGroup ↥(conjClosure Vp H) := commGroupOfElemAbelian hU
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥(conjClosure Vp H), u ^ 2 = 1 := fun u => Subtype.ext (by
    simpa using hU.2 u u.2)
  let β : ↥(pCoreOf 2 H) → ↥(conjClosure Vp H) → ↥V₁ := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, h.commutator_mem_V₁ x.2 u.2⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (h.commutator_mul_left x₁.2 x₂.2 u.2)
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (h.commutator_mul_right x.2 u₁.2 u₂.2)
  have key := card_mul_card_radical_eq hB h.card_V₁ β h1 h2
  have hcomm : ∀ (x u : G), x * u * x⁻¹ * u⁻¹ = 1 ↔ x * u = u * x := fun x u => by
    constructor
    · intro e
      calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
        _ = u * x := by rw [e]; group
    · intro e
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [e]
        _ = 1 := by group
  have c1 : Nat.card {b : ↥(conjClosure Vp H) // ∀ a, β a b = 1} =
      Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
    refine Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := congrArg Subtype.val (b.2 ⟨x, hx⟩)
          exact (hcomm x b.1).mp this⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * b.1⁻¹ = 1
          exact (hcomm a b.1).mpr (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have c2 : Nat.card {a : ↥(pCoreOf 2 H) // ∀ b, β a b = 1} =
      Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, Subgroup.mem_centralizer_iff.mpr fun u hu => by
          have := congrArg Subtype.val (a.2 ⟨u, hu⟩)
          exact ((hcomm a.1 u).mp this).symm⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => Subtype.ext (by
          show (a.1 : G) * b * (a.1 : G)⁻¹ * (b : G)⁻¹ = 1
          exact (hcomm a.1 b).mpr (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2).symm)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [c1, c2] at key
  exact key

theorem F97_relIndex (h : HypF91 T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H)) :
    (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)).relIndex (pCoreOf 2 H) =
      (conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex
        (conjClosure Vp H) := by
  have key := h.F97_card_mul hU
  have e1 := Subgroup.relIndex_mul_card (pCoreOf 2 H ⊓ Subgroup.centralizer
    (conjClosure Vp H : Set G)) (pCoreOf 2 H)
  have e2 := Subgroup.relIndex_mul_card (conjClosure Vp H ⊓ Subgroup.centralizer
    (pCoreOf 2 H : Set G)) (conjClosure Vp H)
  have hQC : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hZ : conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ conjClosure Vp H :=
    inf_le_left
  rw [inf_eq_left.mpr hQC] at e1
  rw [inf_eq_left.mpr hZ] at e2
  have p1 : 0 < Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) :=
    Nat.card_pos
  have p2 : 0 < Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) :=
    Nat.card_pos
  rw [← e1, ← e2] at key
  have : (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)).relIndex
        (pCoreOf 2 H) *
      (Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) *
        Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))) =
      (conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex
        (conjClosure Vp H) *
      (Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) *
        Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))) := by
    calc _ = _ := by ring
      _ = _ := key
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos p1 p2) this

end HypF91

end Fin

end CFSG.Quasithin
