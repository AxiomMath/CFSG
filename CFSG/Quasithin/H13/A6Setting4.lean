module

public import CFSG.Quasithin.H13.A6Model4
public import CFSG.Quasithin.H13.A6Setting134
public import CFSG.Quasithin.H13.A6Statements

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

structure Frame4 (T L V : Subgroup G) where
  L_le : L ≤ Subgroup.normalizer (V : Set G)
  T_le : T ≤ Subgroup.normalizer (V : Set G)
  ψ : ↥V ≃* ↥W4
  ρ : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6)
  equiv : ∀ (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V),
    ψ (conjAct V g v) = act4 (ρ g) (ψ v)
  image_L : ∀ σ : Perm (Fin 6),
    (∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L ∧ ρ g = σ) ↔
      σ ∈ alternatingGroup (Fin 6)
  T_D : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD6 (ρ g)
  DA_T : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ

structure Setting4 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) where
  h13 : QTH13 G T L
  irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  zv : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  T_le_NL : T ≤ Subgroup.normalizer (L : Set G)
  maximal : quasithinIsMaximalLocal T L
  uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G))
  V_le_T : V ≤ T
  fsu : FSU G T L V
  a6 : IsA6On L V
  centralQuot : A6CentralQuotient L
  frame : Frame4 T L V

namespace Setting4

variable [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem psi_conj (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    S.frame.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      act4 (S.frame.ρ g) (S.frame.ψ v) := by
  rw [← S.frame.equiv]
  congr 1

theorem conj_eq_iff (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    (g : G) * v * (g : G)⁻¹ = v ↔ act4 (S.frame.ρ g) (S.frame.ψ v) = S.frame.ψ v := by
  rw [← S.psi_conj]
  constructor
  · intro h
    congr 1
    exact Subtype.ext h
  · intro h
    have := congrArg Subtype.val (S.frame.ψ.injective h)
    simpa using this

@[expose] noncomputable def pre (Y : Subgroup ↥W4) : Subgroup G :=
  (Y.comap S.frame.ψ.toMonoidHom).map V.subtype

theorem mem_pre {Y : Subgroup ↥W4} {x : G} :
    x ∈ S.pre Y ↔ ∃ h : x ∈ V, S.frame.ψ ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem card_V : Nat.card V = 16 := by
  rw [Nat.card_congr S.frame.ψ.toEquiv]
  have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem isPGroup_V : IsPGroup 2 V :=
  IsPGroup.of_card (n := 4) (by rw [S.card_V]; norm_num)

end Setting4

end CFSG.Quasithin.H13.A6
