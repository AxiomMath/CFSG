module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecCB213
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {Γ : Type} [Group Γ]

theorem exists_mul_of_le_sup {K T X : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTX : T ≤ X) (hXKT : X ≤ K ⊔ T) {x : G} (hx : x ∈ X) :
    ∃ k ∈ X ⊓ K, ∃ t ∈ T, x = k * t := by
  obtain ⟨k, hk, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTK (hXKT hx)
  refine ⟨k, mem_inf.2 ⟨?_, hk⟩, t, ht, rfl⟩
  have e : k = k * t * t⁻¹ := by group
  rw [e]
  exact mul_mem hx (inv_mem (hTX ht))

structure ParData (K T U L1T : Subgroup G) (ρ : ↥(normalizer (U : Set G)) →* Γ)
    (Q P : Subgroup Γ) : Prop where
  KU : K ≤ normalizer (U : Set G)
  TK : T ≤ normalizer (K : Set G)
  L1T_le : L1T ≤ K ⊔ T
  T_le : T ≤ L1T
  ker : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ K → ρ g = 1 → (g : G) ∈ T
  img : ∀ γ ∈ Q, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ K ∧ ρ g = γ
  img_le : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ K → ρ g ∈ Q
  P_iff : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ K → (ρ g ∈ P ↔ (g : G) ∈ L1T)

namespace ParData

variable {K T U L1T : Subgroup G} {ρ : ↥(normalizer (U : Set G)) →* Γ} {Q P : Subgroup Γ}
  (D : ParData K T U L1T ρ Q P)
include D

@[expose] def img' (_ : ParData K T U L1T ρ Q P) (X : Subgroup G) : Subgroup Γ :=
  ((X ⊓ K).subgroupOf (normalizer (U : Set G))).map ρ

theorem mem_img' {X : Subgroup G} {g : ↥(normalizer (U : Set G))} (hg : (g : G) ∈ X ⊓ K) :
    ρ g ∈ D.img' X :=
  ⟨g, mem_subgroupOf.2 hg, rfl⟩

theorem img'_le (X : Subgroup G) : D.img' X ≤ Q := by
  rintro _ ⟨g, hg, rfl⟩
  exact D.img_le g (mem_inf.1 (mem_subgroupOf.1 hg)).2

theorem mem_of_img' {X : Subgroup G} (hTX : T ≤ X) {g : ↥(normalizer (U : Set G))}
    (hgK : (g : G) ∈ K) (hg : ρ g ∈ D.img' X) : (g : G) ∈ X := by
  obtain ⟨x, hx, hxg⟩ := hg
  obtain ⟨hxX, hxK⟩ := mem_inf.1 (mem_subgroupOf.1 hx)
  have h1 : ρ (x⁻¹ * g) = 1 := by rw [map_mul, map_inv, hxg, inv_mul_cancel]
  have h2 := D.ker (x⁻¹ * g) (mul_mem (inv_mem hxK) hgK) h1
  have e : (g : G) = x * (x⁻¹ * g : ↥(normalizer (U : Set G))) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact mul_mem hxX (hTX h2)

theorem P_le_img' (hPQ : P ≤ Q) {X : Subgroup G} (hX : L1T ≤ X) : P ≤ D.img' X := by
  intro γ hγ
  obtain ⟨g, hgK, rfl⟩ := D.img γ (hPQ hγ)
  exact D.mem_img' (mem_inf.2 ⟨hX ((D.P_iff g hgK).1 hγ), hgK⟩)

theorem le_of_img'_le {X : Subgroup G} (hTX : T ≤ X) (hXKT : X ≤ K ⊔ T)
    (h : D.img' X ≤ P) : X ≤ L1T := by
  intro x hx
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_le_sup D.TK hTX hXKT hx
  have hkU : k ∈ normalizer (U : Set G) := D.KU (mem_inf.1 hk).2
  have h1 := (D.P_iff ⟨k, hkU⟩ (mem_inf.1 hk).2).1 (h (D.mem_img' (g := ⟨k, hkU⟩) hk))
  exact mul_mem h1 (D.T_le ht)

theorem eq_or_eq_of_le_sup (hPQ : P ≤ Q)
    (hmax : ∀ Y : Subgroup Γ, P ≤ Y → Y ≤ Q → Y = P ∨ Y = Q) {X : Subgroup G}
    (hX : L1T ≤ X) (hXKT : X ≤ K ⊔ T) : X = L1T ∨ X = K ⊔ T := by
  have hTX : T ≤ X := D.T_le.trans hX
  rcases hmax _ (D.P_le_img' hPQ hX) (D.img'_le X) with h | h
  · exact Or.inl (le_antisymm (D.le_of_img'_le hTX hXKT h.le) hX)
  · right
    refine le_antisymm hXKT (sup_le (fun k hk => ?_) hTX)
    have hkU : k ∈ normalizer (U : Set G) := D.KU hk
    have h1 : ρ ⟨k, hkU⟩ ∈ D.img' X := by
      rw [h]
      exact D.img_le ⟨k, hkU⟩ hk
    exact D.mem_of_img' hTX (g := ⟨k, hkU⟩) hk h1

theorem existsUnique_isHStar [Finite G] {M : Subgroup G} (hL1TM : L1T ≤ M)
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hO2 : pCoreOf 2 (K ⊔ T) ≠ ⊥) {B P₂ : Subgroup Γ}
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hP₂Q : P₂ ≤ Q) (hP₂P : ¬ P₂ ≤ P)
    (hover : ∀ Y : Subgroup Γ, B ≤ Y → Y ≤ Q → ¬ Y ≤ P → P₂ ≤ Y)
    (hKM : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ K → (g : G) ∈ M → ρ g ∈ P) :
    ∃ H₂ : Subgroup G, IsHStar T M H₂ ∧ H₂ ≤ K ⊔ T ∧
      ∀ X : Subgroup G, IsHStar T M X → X ≤ K ⊔ T → X = H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₂ : Subgroup G := ((P₂.comap ρ).map (normalizer (U : Set G)).subtype ⊓ K) ⊔ T with hH₂
  have hTH₂ : T ≤ H₂ := le_sup_right
  have hH₂KT : H₂ ≤ K ⊔ T := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hBX : ∀ {X : Subgroup G}, T ≤ X → B ≤ D.img' X := fun {X} hTX β hβ => by
    obtain ⟨g, hg, rfl⟩ := hB β hβ
    exact D.mem_img' (mem_inf.2 ⟨hTX (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)
  have hH₂le : ∀ {X : Subgroup G}, T ≤ X → P₂ ≤ D.img' X → H₂ ≤ X := fun {X} hTX h => by
    refine sup_le (fun g hg => ?_) hTX
    obtain ⟨⟨⟨g', hg'U⟩, hg'P, rfl⟩, hgK⟩ := hg
    exact D.mem_of_img' hTX (g := ⟨g', hg'U⟩) hgK (h hg'P)
  have hP₂H₂ : P₂ ≤ D.img' H₂ := fun γ hγ => by
    obtain ⟨g, hgK, rfl⟩ := D.img γ (hP₂Q hγ)
    exact D.mem_img' (mem_inf.2 ⟨mem_sup_left (mem_inf.2 ⟨⟨g, hγ, rfl⟩, hgK⟩), hgK⟩)
  have hnotP : ∀ {X : Subgroup G}, T ≤ X → X ≤ K ⊔ T → ¬ X ≤ M → ¬ D.img' X ≤ P :=
    fun {X} hTX hXKT hXM h => hXM ((D.le_of_img'_le hTX hXKT h).trans hL1TM)
  have hInH : InH T H₂ := by
    refine ⟨hTH₂, fun h => hO2 (le_bot_iff.1 ?_)⟩
    rw [← h]
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl).trans hTH₂)
      (hH₂KT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hH₂M : ¬ H₂ ≤ M := by
    intro h
    apply hP₂P
    refine hP₂H₂.trans ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgH, hgK⟩ := mem_inf.1 (mem_subgroupOf.1 hg)
    exact hKM g hgK (h hgH)
  have hstar : IsHStar T M H₂ := by
    refine ⟨hInH, hH₂M, fun Y hY hYH hYM => le_antisymm hYH (hH₂le hY.1 ?_)⟩
    exact hover _ (hBX hY.1) (D.img'_le Y) (hnotP hY.1 (hYH.trans hH₂KT) hYM)
  refine ⟨H₂, hstar, hH₂KT, fun X hX hXKT => ?_⟩
  have hle : H₂ ≤ X :=
    hH₂le hX.1.1 (hover _ (hBX hX.1.1) (D.img'_le X) (hnotP hX.1.1 hXKT hX.2.1))
  exact (hX.2.2 H₂ hInH hle hH₂M).symm

end ParData

end CFSG.Quasithin.H13.NQS134
