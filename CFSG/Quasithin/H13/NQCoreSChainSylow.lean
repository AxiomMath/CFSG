module

public import CFSG.Quasithin.H13.NQCoreSChainStmts

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sc_sylow_structure {T D X P : Subgroup G} {p : ℕ} (hS : SCSetup T D X p)
    (hP : IsSylowOf p P X) :
    pCoreOf 2 X ≤ T ∧ pCoreOf 2 X ⊔ P = X ∧ P ⊔ T = X ⊔ T ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) ∧
      T = pCoreOf 2 X ⊔ (T ⊓ normalizer (P : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hS.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := hS.canonical.isPGroup
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hTN : T ≤ normalizer (X : Set G) := hS.le_normalizer.trans hS.canonical.normalizer_eq.le
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, hS.sylow.1, hS.sylow.2⟩
  have hqX : pCoreOf 2 X = (CFSG.pCore 2 X).map X.subtype := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  obtain ⟨AX, hAXdef⟩ : ∃ AX : Subgroup G, AX = (CFSG.pCore 2 X).map X.subtype := ⟨_, rfl⟩
  have hAX2 : IsPGroup 2 AX := hAXdef ▸ CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x => by
    rw [hAXdef]
    exact mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) := by
    rw [hAXdef]
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (hS.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hAXX : AX ≤ X := by
    rw [hAXdef]
    exact map_subtype_le _
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h1, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hsup : AX ⊔ P = X := by
    refine le_antisymm (sup_le hAXX hPX) fun x hx => ?_
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx', sup_comm]
    exact mul_mem_sup hy hya
  have hPT : ∀ y ∈ P, ∀ q ∈ T, ∃ q' ∈ T, ∃ y' ∈ P, y * q = q' * y' := by
    intro y hy q hq
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hTN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hAXT (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  have hTP : ∀ q ∈ T, ∀ y ∈ P, ∃ y' ∈ P, ∃ q' ∈ T, q * y = y' * q' := by
    intro q hq y hy
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hAXT hya) hq, by group⟩
  have hset : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
    ext z
    constructor
    · rintro ⟨y, hy, q, hq, rfl⟩
      obtain ⟨q', hq', y', hy', he⟩ := hPT y hy q hq
      exact ⟨q', hq', y', hy', he.symm⟩
    · rintro ⟨q, hq, y, hy, rfl⟩
      obtain ⟨y', hy', q', hq', he⟩ := hTP q hq y hy
      exact ⟨y', hy', q', hq', he.symm⟩
  have hPTX : P ⊔ T = X ⊔ T := by
    refine le_antisymm (sup_le_sup_right hPX T) (sup_le ?_ le_sup_right)
    rw [← hsup]
    exact sup_le (hAXT.trans le_sup_right) le_sup_left
  have hfrat : T = AX ⊔ (T ⊓ normalizer (P : Set G)) := by
    refine le_antisymm (fun t ht => ?_) (sup_le hAXT inf_le_left)
    set P' := P.map (MulAut.conj t).toMonoidHom with hP'
    have hP'X : P' ≤ X := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp (hTN ht) y).mp (hPX hy)
    have hcard : Nat.card P' = Nat.card P :=
      card_map_of_injective (MulAut.conj t).injective
    have hP'S : IsSylowOf p P' X :=
      CFSG.ABGLocalTools.isSylowOf_of_card hP'X (hcard.trans hP.card_eq)
    obtain ⟨k, hkX, hk⟩ := hP'S.exists_mem_conj hP
    have hmemP' : ∀ x : G, x ∈ P' ↔ t⁻¹ * x * t ∈ P := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
      · intro hx
        exact ⟨t⁻¹ * x * t, hx, by simp [mul_assoc]⟩
    have hkt : (k * t)⁻¹ ∈ normalizer (P : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      rw [hk x, hmemP']
      constructor
      · intro h
        simpa [mul_assoc] using h
      · intro h
        simpa [mul_assoc] using h
    have hkt' : k * t ∈ normalizer (P : Set G) := by simpa using inv_mem hkt
    obtain ⟨y, hy, hya⟩ := hXPA k hkX
    have hn : (y⁻¹ * k) * t ∈ T := by
      have : y⁻¹ * k ∈ T := hAXT hya
      exact mul_mem this ht
    have hnN : (y⁻¹ * k) * t ∈ normalizer (P : Set G) := by
      have : y⁻¹ ∈ normalizer (P : Set G) := le_normalizer (inv_mem hy)
      simpa [mul_assoc] using mul_mem this hkt'
    have ht' : t = (y⁻¹ * k)⁻¹ * ((y⁻¹ * k) * t) := by group
    rw [ht']
    exact mul_mem_sup (inv_mem hya) ⟨hn, hnN⟩
  rw [hqX, ← hAXdef]
  exact ⟨hAXT, hsup, hPTX, hset, hfrat⟩

end CFSG.Quasithin.H13.NQCore
