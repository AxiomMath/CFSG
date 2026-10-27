module

public import CFSG.Quasithin.H13.A6S4V1
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def InW2 (x : P6) : Prop := x = 1 ∨ x = dv 0 1 ∨ x = dv 2 3 ∨ x = e0123

instance : DecidablePred InW2 := fun x => by unfold InW2; infer_instance

@[expose] def InW3 (x : P6) : Prop := Multiplicative.toAdd x 4 = 0

instance : DecidablePred InW3 := fun x => by unfold InW3; infer_instance

@[expose] def W2sub : Subgroup ↥W4 where
  carrier := {y | InW2 (y : P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW2 a → InW2 b → InW2 (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW2 a → InW2 a⁻¹ := by decide +kernel
    exact key _ ha)

@[expose] def W3sub : Subgroup ↥W4 where
  carrier := {y | InW3 (y : P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW3 a → InW3 b → InW3 (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW3 a → InW3 a⁻¹ := by decide +kernel
    exact key _ ha)

theorem card_W2sub : Nat.card ↥W2sub = 4 := by
  have : Fintype.card {y : ↥W4 // InW2 (y : P6)} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_W3sub : Nat.card ↥W3sub = 8 := by
  have : Fintype.card {y : ↥W4 // InW3 (y : P6)} = 8 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem D_preserves : ∀ σ : Perm (Fin 6), InD6 σ → (∀ x : P6, InW2 x → InW2 (act4f σ x)) ∧
    ∀ x : P6, InW4 x → InW3 x → InW3 (act4f σ x) := by
  decide +kernel

theorem W_chain : InW2 e0123 ∧ ∀ x : P6, InW2 x → InW3 x := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem card_pre (Y : Subgroup ↥W4) : Nat.card ↥(S.pre Y) = Nat.card ↥Y := by
  rw [Setting4.pre, Subgroup.card_map_of_injective V.subtype_injective,
    Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective (f := S.frame.ψ.symm.toMonoidHom) S.frame.ψ.symm.injective]

@[expose] noncomputable def V2 : Subgroup G := S.pre W2sub

@[expose] noncomputable def V3 : Subgroup G := S.pre W3sub

theorem card_V2 : Nat.card ↥S.V2 = 4 := by rw [V2, S.card_pre, card_W2sub]

theorem card_V3 : Nat.card ↥S.V3 = 8 := by rw [V3, S.card_pre, card_W3sub]

theorem V2_le_V : S.V2 ≤ V := Subgroup.map_subtype_le _

theorem V3_le_V : S.V3 ≤ V := Subgroup.map_subtype_le _

theorem V2_le_V3 : S.V2 ≤ S.V3 := by
  intro x hx
  obtain ⟨h, hY⟩ := S.mem_pre.1 hx
  exact S.mem_pre.2 ⟨h, W_chain.2 _ hY⟩

theorem V1_le_V2 : fsuV1 T V ≤ S.V2 := by
  intro x hx
  rcases S.mem_V1_iff.1 hx with rfl | rfl
  · exact Subgroup.one_mem _
  · refine S.mem_pre.2 ⟨S.z_mem_V, ?_⟩
    show InW2 ((S.frame.ψ ⟨S.z, S.z_mem_V⟩ : ↥W4) : P6)
    rw [S.psi_z]
    exact W_chain.1

theorem T_le_normalizer_pre {Y : Subgroup ↥W4}
    (hY : ∀ σ : Perm (Fin 6), InD6 σ → ∀ y : ↥W4, y ∈ Y → act4 σ y ∈ Y) :
    T ≤ Subgroup.normalizer (S.pre Y : Set G) := by
  intro t ht
  have hY' : ∀ (g : ↥(Subgroup.normalizer (V : Set G))), (g : G) ∈ T → ∀ x : G,
      x ∈ S.pre Y → (g : G) * x * (g : G)⁻¹ ∈ S.pre Y := by
    intro g hg x hx
    obtain ⟨hxV, hxY⟩ := S.mem_pre.1 hx
    refine S.mem_pre.2 ⟨(Subgroup.mem_normalizer_iff.mp g.2 x).mp hxV, ?_⟩
    rw [S.psi_conj g ⟨x, hxV⟩]
    exact hY _ (S.frame.T_D g hg) _ hxY
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hY' ⟨t, S.frame.T_le ht⟩ ht x
  · intro hx
    have h := hY' ⟨t, S.frame.T_le ht⟩⁻¹ (T.inv_mem ht) _ hx
    simp only [InvMemClass.coe_inv, inv_inv] at h
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rwa [e] at h

theorem T_le_normalizer_V2 : T ≤ Subgroup.normalizer (S.V2 : Set G) :=
  S.T_le_normalizer_pre fun σ hσ _ hy => (D_preserves σ hσ).1 _ hy

theorem T_le_normalizer_V3 : T ≤ Subgroup.normalizer (S.V3 : Set G) :=
  S.T_le_normalizer_pre fun σ hσ y hy => (D_preserves σ hσ).2 _ y.2 hy

omit S in
@[expose] noncomputable def L1 (_ : Setting4 G T L V) : Subgroup G := L₁Of L (fsuV1 T V)

@[expose] noncomputable def L2 : Subgroup G := oTwoRes (L ⊓ Subgroup.normalizer (S.V2 : Set G))

@[expose] noncomputable def G1 : Subgroup G := Subgroup.centralizer ({S.z} : Set G)

@[expose] def Hz : Set (Subgroup G) :=
  {H | InH (S.L1 ⊔ T) H ∧ H ≤ S.G1 ∧ ¬ H ≤ Subgroup.normalizer (L : Set G)}

@[expose] noncomputable def UH (H : Subgroup G) : Subgroup G := conjClosure S.V3 H

end Setting4

end CFSG.Quasithin.H13.A6
