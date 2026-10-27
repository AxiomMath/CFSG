module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Close

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def Stmt5_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      Nonempty (G ≃* ↥NativeSporadic.M23)

@[expose] def M23CloseData (G : Type) [Group G] : Prop :=
  ∃ (Gx I : Subgroup G) (t : G) (a b c d : Fin 23) (habcd : [a, b, c, d].Nodup)
    (β : Gx ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd))
    (ζ : I ≃* quadStab ↥NativeSporadic.M23 a b c d),
    t ∈ I ∧ t ∉ Gx ∧ t * t ∈ Gx ∧ Gx ⊔ I = ⊤ ∧
    Gx ≤ Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx) ⊔ I ⊓ Gx ∧
    I ≤ I ⊓ Gx ⊔ Subgroup.zpowers t ∧
    (∀ i : I, (i : G) ∈ Gx ↔
      (ζ i : ↥NativeSporadic.M23) ∈ stabilizer ↥NativeSporadic.M23 (xbar habcd)) ∧
    (∀ (i : I) (hi : (i : G) ∈ Gx), (β ⟨i, hi⟩ : ↥NativeSporadic.M23) = ζ i) ∧
    (∀ g : Gx, (g : G) ∈ stabilizer G ((t : G) : G ⧸ Gx) ↔
      (β g : ↥NativeSporadic.M23) ∈ stabilizer ↥NativeSporadic.M23 (ybar habcd)) ∧
    (∀ i : I, (i : G) ∈
        stabilizer G ({((1 : G) : G ⧸ Gx), ((t : G) : G ⧸ Gx)} : Set (G ⧸ Gx)) ↔
      (ζ i : ↥NativeSporadic.M23) ∈
        stabilizer ↥NativeSporadic.M23 ({xbar habcd, ybar habcd} : Set (Pair (Fin 23)))) ∧
    ∀ α : ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)) ≃* ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)),
      (∀ k : ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)), (k : G) ∈ I → α k = k) →
        α = MulEquiv.refl _

@[expose] def Stmt5_2_11_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → M23CloseData G

theorem nonempty_mulEquiv_m23_of_m23CloseData
    {G : Type} [Group G] (h : M23CloseData G) :
    Nonempty (G ≃* ↥NativeSporadic.M23) := by
  obtain ⟨Gx, I, t, a, b, c, d, habcd, β, ζ, htI, htGx, htt, hgen, hGx, hI, hζx, hβζ, hβy, hζy,
    haut⟩ := h
  exact nonempty_mulEquiv_m23_of_closeData habcd htI htGx htt hgen hGx hI β ζ hζx hβζ hβy hζy
    haut

theorem stmt5_2_10_of
    (h : Stmt5_2_11_22) : Stmt5_2_10 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  exact nonempty_mulEquiv_m23_of_m23CloseData (h G T M L V H B D L₂ n hyp hM23)

end CFSG.Quasithin.H13
