module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Pl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def IsPlaneSub (T M H PQ R : Subgroup G) : Prop :=
  pCoreOf 2 H ≤ R ∧ R ≤ PQ ∧ (pCoreOf 2 H).relIndex R = 3 ∧
    mIdx (uHi T M H R) (quasithinOmegaOneCenter T) = 2

structure IsE9Dat (T M H PQ R₁ R₂ : Subgroup G) (s : G) : Prop where
  plane₁ : IsPlaneSub T M H PQ R₁
  plane₂ : IsPlaneSub T M H PQ R₂
  sup : R₁ ⊔ R₂ = PQ
  inf : R₁ ⊓ R₂ = pCoreOf 2 H
  s_mem : s ∈ T
  conj : conjSub s R₁ = R₂
  indexT : (T ⊓ Subgroup.normalizer (R₁ : Set G)).relIndex T = 2
  dir_inf : uHi T M H R₁ ⊓ uHi T M H R₂ = quasithinOmegaOneCenter T
  dir_sup : uHi T M H R₁ ⊔ uHi T M H R₂ = uK T M H ⊔ quasithinOmegaOneCenter T
  cent₁ : ⁅uHi T M H R₁, R₂⁆ ≤ quasithinOmegaOneCenter T
  cent₂ : ⁅uHi T M H R₂, R₁⁆ ≤ quasithinOmegaOneCenter T

end Defs

section Dat

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem card_tildeOf_eq_relIndex' {Z X : Subgroup G} (hZX : Z ≤ X)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card (tildeOf Z X) = Z.relIndex X := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := X)
    le_rfl hZX hXN
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  exact h1

theorem card_Wsub_uHi (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {R : Subgroup G} (hRH : R ≤ H) :
    Nat.card (Wsub h (uHi T M H R)) =
      2 ^ mIdx (uHi T M H R) (quasithinOmegaOneCenter T) := by
  have hi : uHi T M H R ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hRH
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  rw [card_Wsub h hi, card_tildeOf_eq_relIndex' (Z_le_uHi T M H R) (hi.trans hUZ),
    HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi)]

theorem ker_resBeta_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c) :
    (resBeta (rhoH h)).ker = (pCoreOf 2 H).subgroupOf H := by
  ext x
  rw [ker_resBeta _ hsplit, MonoidHom.mem_ker, rhoH_eq_one_iff, Subgroup.mem_subgroupOf]

theorem IsPlaneSub.exists_HLb (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h98.toHypF91, ∃ a ∈ kOf (rhoH h98.toHypF91),
      ∃ c ∈ fixV (rhoH h98.toHypF91).range, w = a * c)
    {R : Subgroup G} (hR : IsPlaneSub T M H PQ R) :
    ∃ Q : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91))),
      Q ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) ∧ Nat.card Q = 3 ∧
        rk (commV Q) = 2 ∧ R = HLb (resBeta (rhoH h98.toHypF91)) Q := by
  obtain ⟨hQH, hRPQ, hidx, hmI⟩ := hR
  have hH : IsHTM T M H := hred.isHTM
  have hRH : R ≤ H := hRPQ.trans hred.le
  have hker := ker_resBeta_eq h98.toHypF91 hsplit
  set β := resBeta (rhoH h98.toHypF91) with hβ
  set Q : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91))) := (R.subgroupOf H).map β with hQdef
  have hQP : Q ≤ (PQ.subgroupOf H).map β :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hRPQ (Subgroup.mem_subgroupOf.mp hx))
  have hQrange : Q ≤ β.range := Subgroup.map_le_range _ _
  have hRQ : R = HLb β Q := by
    ext x
    constructor
    · intro hx
      exact (mem_HLb_iff (hRH hx)).mpr ⟨⟨x, hRH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · intro hx
      have hxH : x ∈ H := HLb_le Q hx
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp ((mem_HLb_iff hxH).mp hx)
      have hmem : r⁻¹ * ⟨x, hxH⟩ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hrx, inv_mul_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at hmem
      have h1 : (r : G)⁻¹ * x ∈ R := hQH hmem
      have e : x = (r : G) * ((r : G)⁻¹ * x) := by group
      rw [e]
      exact R.mul_mem (Subgroup.mem_subgroupOf.mp hr) h1
  have hcard : Nat.card Q = 3 := by
    rw [hQdef, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hRH]
    exact hidx
  refine ⟨Q, hQP, hcard, ?_, hRQ⟩
  have hW := Wsub_uHi_HLb h98.toHypF91 hsplit hQrange
  rw [← hRQ] at hW
  have hc4 := card_Wsub_uHi S hH h98.toHypF91 hRH
  rw [hmI, hW, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hc4
  have hsq : ∀ v : ↥(kOf (rhoH h98.toHypF91)), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using IntMod.sq_eq_one (v : UMod h98.toHypF91))
  have hpow := card_eq_two_pow hsq (commV Q)
  rw [hpow] at hc4
  exact Nat.pow_right_injective (le_refl 2) hc4

end Dat

end CFSG.Quasithin
