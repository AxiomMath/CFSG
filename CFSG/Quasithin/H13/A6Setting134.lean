module

public import CFSG.Quasithin.H13.A6Model
public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Quasithin

@[expose] def InD6 (σ : Perm (Fin 6)) : Prop :=
  (σ 4 : ℕ) / 2 = 2 ∧ (σ 5 : ℕ) / 2 = 2 ∧ (σ 0 : ℕ) / 2 = (σ 1 : ℕ) / 2

instance : DecidablePred InD6 := fun σ =>
  inferInstanceAs (Decidable ((σ 4 : ℕ) / 2 = 2 ∧ (σ 5 : ℕ) / 2 = 2 ∧
    (σ 0 : ℕ) / 2 = (σ 1 : ℕ) / 2))

variable {G : Type} [Group G]

structure Frame5 (T L V : Subgroup G) where
  L_le : L ≤ Subgroup.normalizer (V : Set G)
  T_le : T ≤ Subgroup.normalizer (V : Set G)
  ψ : ↥V ≃* ↥(G6.coreMod 6)
  ρ : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6)
  equiv : ∀ (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V),
    ψ (conjAct V g v) = G6.coreAct 6 (ρ g) (ψ v)
  image_L : ∀ σ : Perm (Fin 6),
    (∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L ∧ ρ g = σ) ↔
      σ ∈ alternatingGroup (Fin 6)
  T_D : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD6 (ρ g)
  DA_T : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ

structure Setting134 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) where
  h13 : QTH13 G T L
  irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  zv : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥
  T_le_NL : T ≤ Subgroup.normalizer (L : Set G)
  maximal : quasithinIsMaximalLocal T L
  uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G))
  V_le_T : V ≤ T
  fsu : FSU G T L V
  frame : Frame5 T L V

namespace Setting134

variable [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem psi_conj (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    S.frame.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      G6.coreAct 6 (S.frame.ρ g) (S.frame.ψ v) := by
  rw [← S.frame.equiv]
  congr 1

theorem conj_eq_iff (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    (g : G) * v * (g : G)⁻¹ = v ↔
      G6.coreAct 6 (S.frame.ρ g) (S.frame.ψ v) = S.frame.ψ v := by
  rw [← S.psi_conj]
  constructor
  · intro h
    congr 1
    exact Subtype.ext h
  · intro h
    have := congrArg Subtype.val (S.frame.ψ.injective h)
    simpa using this

@[expose] noncomputable def pre (Y : Subgroup ↥(G6.coreMod 6)) : Subgroup G :=
  (Y.comap S.frame.ψ.toMonoidHom).map V.subtype

theorem mem_pre {Y : Subgroup ↥(G6.coreMod 6)} {x : G} :
    x ∈ S.pre Y ↔ ∃ h : x ∈ V, S.frame.ψ ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem pre_le_V (Y : Subgroup ↥(G6.coreMod 6)) : S.pre Y ≤ V := Subgroup.map_subtype_le _

theorem card_V : Nat.card V = 32 := by
  rw [Nat.card_congr S.frame.ψ.toEquiv]
  have : Fintype.card {x : P6 // x ∈ G6.coreMod 6} = 32 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]

theorem isPGroup_V : IsPGroup 2 V :=
  IsPGroup.of_card (n := 5) (by rw [S.card_V]; norm_num)

@[expose] noncomputable def zV : G :=
  (S.frame.ψ.symm ⟨G6.allOnes 6, allOnes_mem_core⟩ : G)

theorem zV_mem_V : S.zV ∈ V := (S.frame.ψ.symm _).2

theorem psi_zV : S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ = ⟨G6.allOnes 6, allOnes_mem_core⟩ :=
  S.frame.ψ.apply_symm_apply _

theorem conj_zV (g : ↥(Subgroup.normalizer (V : Set G))) :
    (g : G) * S.zV * (g : G)⁻¹ = S.zV :=
  (S.conj_eq_iff g ⟨S.zV, S.zV_mem_V⟩).2 (by
    rw [S.psi_zV]
    exact Subtype.ext (by rw [G6.coreAct_coe]; exact permAct_allOnes _))

theorem mem_centralizer_L_iff (v : ↥V) :
    (v : G) ∈ Subgroup.centralizer (L : Set G) ↔ v = 1 ∨ v = ⟨S.zV, S.zV_mem_V⟩ := by
  constructor
  · intro hv
    have hfix : ∀ σ ∈ alternatingGroup (Fin 6),
        G6.permAct 6 σ (S.frame.ψ v : P6) = S.frame.ψ v := by
      intro σ hσ
      obtain ⟨g, hgL, rfl⟩ := (S.frame.image_L σ).2 hσ
      have hc : (g : G) * v * (g : G)⁻¹ = v := by
        rw [Subgroup.mem_centralizer_iff.mp hv (g : G) hgL, mul_inv_cancel_right]
      have := congrArg Subtype.val ((S.conj_eq_iff g v).1 hc)
      rwa [G6.coreAct_coe] at this
    obtain ⟨c1, c2, c3, c4⟩ := three_cycles_mem
    rcases fixed_three_cycles _ (hfix _ c1) (hfix _ c2) (hfix _ c3) (hfix _ c4) with h | h
    · left
      apply S.frame.ψ.injective
      rw [map_one]
      exact Subtype.ext h
    · right
      apply S.frame.ψ.injective
      rw [S.psi_zV]
      exact Subtype.ext h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := S.conj_zV ⟨l, S.frame.L_le hl⟩
      calc l * S.zV = l * S.zV * l⁻¹ * l := by group
        _ = S.zV * l := by rw [this]

theorem mem_ZV_iff {x : G} :
    x ∈ V ⊓ Subgroup.centralizer (L : Set G) ↔ x = 1 ∨ x = S.zV := by
  constructor
  · rintro ⟨hxV, hxC⟩
    rcases (S.mem_centralizer_L_iff ⟨x, hxV⟩).1 hxC with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact ⟨S.zV_mem_V, (S.mem_centralizer_L_iff ⟨S.zV, S.zV_mem_V⟩).2 (Or.inr rfl)⟩

theorem zV_ne_one : S.zV ≠ 1 := by
  intro h
  have h1 : (⟨S.zV, S.zV_mem_V⟩ : ↥V) = 1 := Subtype.ext h
  have h2 := S.psi_zV
  rw [h1, map_one] at h2
  exact allOnes_ne_one (congrArg Subtype.val h2).symm

theorem zV_sq : S.zV ^ 2 = 1 := by
  have h : (⟨S.zV, S.zV_mem_V⟩ : ↥V) ^ 2 = 1 := by
    apply S.frame.ψ.injective
    rw [map_pow, S.psi_zV, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact allOnes_mul_self
  exact congrArg Subtype.val h

theorem ZV_eq_zpowers :
    V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers S.zV := by
  apply le_antisymm
  · intro x hx
    rcases S.mem_ZV_iff.1 hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact S.mem_ZV_iff.2 (Or.inr rfl)

theorem card_ZV : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [S.ZV_eq_zpowers, Nat.card_zpowers]
  exact orderOf_eq_prime S.zV_sq S.zV_ne_one

end Setting134

end CFSG.Quasithin.H13.A6
