module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

variable {G : Type} [Group G]

@[expose] noncomputable def O2 (Y : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥Y).map Y.subtype

theorem O2_isPGroup [Finite G] (Y : Subgroup G) : IsPGroup 2 ↥(O2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype

theorem O2_normal (Y : Subgroup G) : ∀ y ∈ Y, ∀ x ∈ O2 Y, y * x * y⁻¹ ∈ O2 Y := by
  rintro y hy _ ⟨x, hx, rfl⟩
  exact ⟨⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem x hx ⟨y, hy⟩, rfl⟩

theorem le_O2 {Y T : Subgroup G} (hTY : T ≤ Y) (hT2 : IsPGroup 2 ↥T)
    (hTn : ∀ y ∈ Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T) : T ≤ O2 Y := by
  intro t ht
  refine ⟨⟨t, hTY ht⟩, ?_, rfl⟩
  have hn : (T.subgroupOf Y).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hTn g g.2 x hx⟩
  have hp : IsPGroup 2 ↥(T.subgroupOf Y) := hT2.comap_subtype
  have hle : T.subgroupOf Y ≤ CFSG.pCore 2 ↥Y :=
    le_sSup (s := {K : Subgroup ↥Y | K.Normal ∧ IsPGroup 2 ↥K}) ⟨hn, hp⟩
  exact hle (Subgroup.mem_subgroupOf.2 ht)

theorem le_normalizer_O2 (Y : Subgroup G) : Y ≤ Subgroup.normalizer (O2 Y : Set G) := fun y hy => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => O2_normal Y y hy x hx, fun hx => by
    have := O2_normal Y y⁻¹ (Y.inv_mem hy) _ hx
    simpa [mul_assoc] using this⟩

variable [Finite G]

theorem exists_maximal_two_local {E N M B : Subgroup G}
    (hM2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ M = Subgroup.normalizer (S : Set G))
    (hMN : ¬ M ≤ N) (hBM : B ≤ M) (hBE : B ≤ E) (hBnc : ¬ IsCyclic ↥B) :
    ∃ R B₁ : Subgroup G, IsPGroup 2 ↥R ∧ R ≠ ⊥ ∧ ¬ Subgroup.normalizer (R : Set G) ≤ N ∧
      B₁ ≤ Subgroup.normalizer (R : Set G) ∧ B₁ ≤ E ∧ ¬ IsCyclic ↥B₁ ∧
      ∀ Y₁ : Subgroup G, ¬ Y₁ ≤ N → O2 Y₁ ≠ ⊥ → (∃ B₂ : Subgroup G, B₂ ≤ Y₁ ∧ B₂ ≤ E ∧
        ¬ IsCyclic ↥B₂) → Nat.card ↥(O2 Y₁) ≤ Nat.card ↥R := by
  classical
  obtain ⟨S, hS1, hS2, rfl⟩ := hM2
  let 𝒴 : Set (Subgroup G) := {Y₁ | ¬ Y₁ ≤ N ∧ O2 Y₁ ≠ ⊥ ∧
    ∃ B₂ : Subgroup G, B₂ ≤ Y₁ ∧ B₂ ≤ E ∧ ¬ IsCyclic ↥B₂}
  have hMmem : Subgroup.normalizer (S : Set G) ∈ 𝒴 := by
    refine ⟨hMN, ?_, B, hBM, hBE, hBnc⟩
    intro h
    have hSO : S ≤ O2 (Subgroup.normalizer (S : Set G)) :=
      le_O2 Subgroup.le_normalizer hS2 (fun y hy t ht => (Subgroup.mem_normalizer_iff.1 hy t).1 ht)
    rw [h] at hSO
    exact hS1 (le_bot_iff.1 hSO)
  obtain ⟨Y₁, ⟨hY₁N, hY₁O, B₂, hB₂Y, hB₂E, hB₂nc⟩, hmax⟩ :=
    Set.exists_max_image 𝒴 (fun Y => Nat.card ↥(O2 Y)) (Set.toFinite 𝒴) ⟨_, hMmem⟩
  have hY₁R : Y₁ ≤ Subgroup.normalizer (O2 Y₁ : Set G) := le_normalizer_O2 Y₁
  refine ⟨O2 Y₁, B₂, O2_isPGroup Y₁, hY₁O, fun h => hY₁N (hY₁R.trans h), hB₂Y.trans hY₁R, hB₂E,
    hB₂nc, fun Y₂ hY₂N hY₂O hB => hmax Y₂ ⟨hY₂N, hY₂O, hB⟩⟩

theorem hmax_of_family {E N R B' R' : Subgroup G}
    (hfam : ∀ Y₁ : Subgroup G, ¬ Y₁ ≤ N → O2 Y₁ ≠ ⊥ → (∃ B₂ : Subgroup G, B₂ ≤ Y₁ ∧ B₂ ≤ E ∧
      ¬ IsCyclic ↥B₂) → Nat.card ↥(O2 Y₁) ≤ Nat.card ↥R)
    (hB'E : B' ≤ E) (hB'nc : ¬ IsCyclic ↥B') (hRR' : Nat.card ↥R' = Nat.card ↥R) :
    ∀ T : Subgroup G, IsPGroup 2 ↥T → Nat.card ↥R' < Nat.card ↥T →
      B' ≤ Subgroup.normalizer (T : Set G) → Subgroup.normalizer (T : Set G) ≤ N := by
  intro T hT2 hlt hB'T
  by_contra hTN
  have hTO : T ≤ O2 (Subgroup.normalizer (T : Set G)) :=
    le_O2 Subgroup.le_normalizer hT2 (fun y hy t ht => (Subgroup.mem_normalizer_iff.1 hy t).1 ht)
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥T = 1 := by rw [h]; exact Subgroup.card_bot
    have h2 : 0 < Nat.card ↥R' := Nat.card_pos
    omega
  have hO : O2 (Subgroup.normalizer (T : Set G)) ≠ ⊥ := fun h => hT1 (le_bot_iff.1 (h ▸ hTO))
  have h1 := hfam _ hTN hO ⟨B', hB'T, hB'E, hB'nc⟩
  have h2 : Nat.card ↥T ≤ Nat.card ↥(O2 (Subgroup.normalizer (T : Set G))) :=
    Subgroup.card_le_of_le hTO
  omega

end Sec1511

end CFSG.RankThree.PartOne
