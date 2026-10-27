module

public import CFSG.Quasithin.H13.A6S4Defs
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.A6NotU33

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem comm_W3 : ∀ σ : Perm (Fin 6), InD6 σ → ∀ x : P6, InW4 x → InW3 (x * act4f σ x) := by
  decide +kernel

@[expose] def CommWit (y : P6) : Prop :=
  ∃ x : P6, InW4 x ∧ ∃ σ : Perm (Fin 6), InD6 σ ∧ Equiv.Perm.sign σ = 1 ∧ y = act4f σ x * x

instance (y : P6) : Decidable (CommWit y) := by unfold CommWit; infer_instance

theorem W3_comm : ∀ y : P6, InW4 y → InW3 y → CommWit y := by
  decide +kernel

theorem sq_W4 : ∀ x : P6, x * x = 1 := by decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem inv_eq_self {v : G} (hv : v ∈ V) : v⁻¹ = v := by
  have h : (⟨v, hv⟩ : ↥V) * ⟨v, hv⟩ = 1 := by
    apply S.frame.ψ.injective
    rw [map_mul, map_one]
    exact Subtype.ext (sq_W4 _)
  have := congrArg Subtype.val h
  exact inv_eq_of_mul_eq_one_left this

theorem v3_eq : v3 T L V = S.V3 := by
  rw [v3, S.zv, sup_bot_eq]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv t ht
    have hconj := S.psi_conj ⟨t, S.frame.T_le ht⟩ ⟨v, hv⟩
    have hvinv : v⁻¹ ∈ V := V.inv_mem hv
    have htv : t * v⁻¹ * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.frame.T_le ht) _).mp hvinv
    have hvt : v * t * v⁻¹ * t⁻¹ ∈ V := by
      have : v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
      rw [this]
      exact V.mul_mem hv htv
    refine S.mem_pre.2 ⟨hvt, ?_⟩
    have heq : (⟨v * t * v⁻¹ * t⁻¹, hvt⟩ : ↥V) = ⟨v, hv⟩ * ⟨t * v * t⁻¹,
        (Subgroup.mem_normalizer_iff.mp (S.frame.T_le ht) v).mp hv⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [S.inv_eq_self hv]
      group
    show InW3 ((S.frame.ψ ⟨v * t * v⁻¹ * t⁻¹, hvt⟩ : ↥W4) : P6)
    rw [heq, map_mul, hconj, Subgroup.coe_mul, act4_coe]
    exact comm_W3 _ (S.frame.T_D _ ht) _ (S.frame.ψ ⟨v, hv⟩).2
  · intro y hy
    obtain ⟨hyV, hyW⟩ := S.mem_pre.1 hy
    obtain ⟨x, hxW, σ, hσD, hσs, hxy⟩ := W3_comm _ (S.frame.ψ ⟨y, hyV⟩).2 hyW
    obtain ⟨t, htT, rfl⟩ := S.frame.DA_T σ hσD (Equiv.Perm.mem_alternatingGroup.2 hσs)
    set v : ↥V := S.frame.ψ.symm ⟨x, hxW⟩ with hv
    have hψv : S.frame.ψ v = ⟨x, hxW⟩ := S.frame.ψ.apply_symm_apply _
    have hconj := S.psi_conj t v
    have hy' : y = (t : G) * v * (t : G)⁻¹ * v := by
      have h1 : S.frame.ψ ⟨y, hyV⟩ = S.frame.ψ (⟨(t : G) * v * (t : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp t.2 v).mp v.2⟩ * v) := by
        rw [map_mul, hconj, hψv]
        apply Subtype.ext
        rw [Subgroup.coe_mul, act4_coe]
        exact hxy
      have := congrArg Subtype.val (S.frame.ψ.injective h1)
      simpa using this
    rw [hy']
    have hc : (t : G) * v * (t : G)⁻¹ * v = (t : G) * v * (t : G)⁻¹ * (v : G)⁻¹ := by
      rw [S.inv_eq_self v.2]
    rw [hc, ← Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator htT v.2

theorem isV2 : IsV2 T V S.V2 :=
  ⟨S.V1_le_V2, S.V2_le_V, S.T_le_normalizer_V2, S.card_V2⟩

theorem not_iso_a5 : IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨f⟩ := S.a6
  have h1 := Nat.card_congr (f.symm.trans e).toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h1
  exact absurd h1 (by decide)

theorem lemma13_5_4 (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (X : Subgroup G)
    (hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆) (hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2) :
    let I₂ := conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G))
    Subgroup.normalizer (S.V2 : Set G) ≤ Subgroup.normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (g1 T V) ∧ I₂ ⊓ Subgroup.centralizer (S.V2 : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pRank 3 (Subgroup.centralizer (S.V2 : Set G)) ≤ 1 ∧
      Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      ⁅V, Subgroup.centralizer (S.V3 : Set G)⁆ ≤ fsuV1 T V ∧
      ¬ pCoreOf 2 (g1 T V) ≤ Subgroup.centralizer (S.V2 : Set G) := by
  intro I₂
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ :=
    h13315 G T L V S.V2 X I₂ S.h13 S.irr S.zv S.isV2 S.not_iso_a5 hX₁ hX₂ rfl
  obtain ⟨h9', h10'⟩ := h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3
  exact ⟨h1, h2, h3, h4, h5, h8, h9', h10' S.not_lieModel_psu33,
    h13314 G T L V S.V2 S.h13 S.irr S.zv S.isV2 S.not_iso_a5⟩

end Setting4

end CFSG.Quasithin.H13.A6
