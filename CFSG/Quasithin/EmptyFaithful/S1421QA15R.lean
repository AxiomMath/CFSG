module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs
public import CFSG.Quasithin.EmptyFaithful.S1421STC3Step

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

section General

variable {G : Type} [Group G]

theorem le_or_le_sup_of_relIndex_eq_three {Y O C : Subgroup G} (hOY : O ≤ Y) (hCY : C ≤ Y)
    (h3 : O.relIndex Y = 3) : C ≤ O ∨ Y ≤ C ⊔ O := by
  have hON : O ≤ C ⊔ O := le_sup_right
  have hNY : C ⊔ O ≤ Y := sup_le hCY hOY
  have hmul := Subgroup.relIndex_mul_relIndex O (C ⊔ O) Y hON hNY
  rw [h3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hmul) with h1 | h1
  · exact Or.inr (Subgroup.relIndex_eq_one.mp h1)
  · rw [h1] at hmul
    have h2 : O.relIndex (C ⊔ O) = 1 := by omega
    exact Or.inl (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h2))

theorem exists_two_pow_mem_of_mem_sup {Y S : Subgroup G} (hS : IsPGroup 2 S)
    (hN : S ≤ Subgroup.normalizer (Y : Set G)) {u : G} (hu : u ∈ Y ⊔ S) :
    ∃ m : ℕ, u ^ 2 ^ m ∈ Y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Y S hN, Set.mem_mul] at hu
  obtain ⟨y, hy, s, hs, rfl⟩ := hu
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  refine ⟨m, ?_⟩
  have hyN : y ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hy
  have hsN : s ∈ Subgroup.normalizer (Y : Set G) := hN hs
  have hy1 : QuotientGroup.mk' (Y.subgroupOf (Subgroup.normalizer (Y : Set G)))
      ⟨y, hyN⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
  have hsm : (⟨s, hsN⟩ : Subgroup.normalizer (Y : Set G)) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hmem : (⟨y * s, mul_mem hyN hsN⟩ : Subgroup.normalizer (Y : Set G)) ^ 2 ^ m ∈
      Y.subgroupOf (Subgroup.normalizer (Y : Set G)) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    have e1 : (⟨y * s, mul_mem hyN hsN⟩ : Subgroup.normalizer (Y : Set G)) =
        ⟨y, hyN⟩ * ⟨s, hsN⟩ := rfl
    rw [e1, map_mul, hy1, one_mul, ← map_pow, hsm, map_one]
  exact Subgroup.mem_subgroupOf.mp hmem

end General

section Def

variable {G : Type} [Group G]

@[expose] def rOf (T M K1 : Subgroup G) : Subgroup G := pCoreOf 2 (yOfL22 T M ⊔ sOf T K1)

end Def

section Basic

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem sOf_le_normalizer_yOfL22 (st : Setting1427 T M H K1) :
    sOf T K1 ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
  sOf_le_T.trans (T_le_normalizer_y st.hyp)

omit [Finite G] in
theorem yOfL22_le_g0Of (T M H K1 : Subgroup G) : yOfL22 T M ≤ g0Of T M H K1 :=
  (le_sup_left : yOfL22 T M ≤ l2Of T H (yOfL22 T M)).trans (le_sup_right.trans le_sup_left)

omit [Finite G] in
theorem yOfL22_sup_sOf_le_g0Of (T M H K1 : Subgroup G) :
    yOfL22 T M ⊔ sOf T K1 ≤ g0Of T M H K1 :=
  sup_le (yOfL22_le_g0Of T M H K1) le_sup_right

theorem Core3Ctx.le_g0Of (c : Core3Ctx T M H K1 L M₁) : L ≤ g0Of T M H K1 := by
  rw [c.eq]
  exact le_sup_left.trans le_sup_left

theorem Core3Ctx.g0Of_le_normalizer (c : Core3Ctx T M H K1 L M₁) :
    g0Of T M H K1 ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer c.le_g0Of).mp c.normal

theorem Core3Ctx.isSylowTwoOf_sOf_sup (c : Core3Ctx T M H K1 L M₁) :
    IsSylowTwoOf (sOf T K1) (yOfL22 T M ⊔ sOf T K1) :=
  A4.isSylowTwoOf_mono (isSylowTwoOf_g0 c.inM c.sylow) le_sup_right
    (yOfL22_sup_sOf_le_g0Of T M H K1)

theorem rOf_le_sOf (c : Core3Ctx T M H K1 L M₁) : rOf T M K1 ≤ sOf T K1 :=
  pCoreOf_two_le_of_isSylowTwoOf c.isSylowTwoOf_sOf_sup

theorem inf_yOfL22_le_pCoreOf_of_not_le (c : Core3Ctx T M H K1 L M₁) (hY : ¬ yOfL22 T M ≤ L) :
    yOfL22 T M ⊓ L ≤ pCoreOf 2 (yOfL22 T M) := by
  have hYN : yOfL22 T M ≤ Subgroup.normalizer (L : Set G) :=
    (yOfL22_le_g0Of T M H K1).trans c.g0Of_le_normalizer
  have hC : yOfL22 T M ≤ Subgroup.normalizer ((yOfL22 T M ⊓ L : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hYN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hO : yOfL22 T M ≤ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hCY : yOfL22 T M ⊓ L ≤ yOfL22 T M := inf_le_left
  have hOY : pCoreOf 2 (yOfL22 T M) ≤ yOfL22 T M := pCoreOf_le 2 _
  rcases le_or_le_sup_of_relIndex_eq_three hOY hCY (relIndex_pCoreOf_y c.st.hyp c.st.facts)
    with h | h
  · exact h
  · exfalso
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (yOfL22 T M ⊓ L)
      (pCoreOf 2 (yOfL22 T M)) (hCY.trans hO)
    have hrep : ∀ y ∈ yOfL22 T M, ∃ x ∈ yOfL22 T M ⊓ L, ∃ o ∈ yOfL22 T M,
        (∃ m : ℕ, o ^ 2 ^ m = 1) ∧ y = x * o := by
      intro y hy
      have hy' : y ∈ ((yOfL22 T M ⊓ L ⊔ pCoreOf 2 (yOfL22 T M) : Subgroup G) : Set G) := h hy
      rw [hmul, Set.mem_mul] at hy'
      obtain ⟨x, hx, o, ho, rfl⟩ := hy'
      obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (yOfL22 T M) ⟨o, ho⟩
      exact ⟨x, hx, o, hOY ho, ⟨m, by simpa using congrArg Subtype.val hm⟩, rfl⟩
    have hCeq := eq_of_forall_mul_two_element hCY hC (oTwoUpper_yOfL22 T M) hrep
    exact hY (hCeq.symm.le.trans inf_le_right)

theorem isPGroup_sup_inf_of_not_le (c : Core3Ctx T M H K1 L M₁) (hY : ¬ yOfL22 T M ≤ L) :
    IsPGroup 2 ↥((yOfL22 T M ⊔ sOf T K1) ⊓ L) := by
  rintro ⟨u, huX, huL⟩
  obtain ⟨m, hm⟩ :=
    exists_two_pow_mem_of_mem_sup (isPGroup_sOf c.st) (sOf_le_normalizer_yOfL22 c.st) huX
  have hmem : u ^ 2 ^ m ∈ pCoreOf 2 (yOfL22 T M) :=
    inf_yOfL22_le_pCoreOf_of_not_le c hY ⟨hm, L.pow_mem huL _⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (yOfL22 T M) ⟨u ^ 2 ^ m, hmem⟩
  refine ⟨m + k, Subtype.ext ?_⟩
  have hk' : (u ^ 2 ^ m) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  simpa [pow_add, pow_mul] using hk'

theorem inf_sOf_le_rOf_of_not_le (c : Core3Ctx T M H K1 L M₁) (hY : ¬ yOfL22 T M ≤ L) :
    sOf T K1 ⊓ L ≤ rOf T M K1 := by
  have hXL : yOfL22 T M ⊔ sOf T K1 ≤ Subgroup.normalizer (L : Set G) :=
    (yOfL22_sup_sOf_le_g0Of T M H K1).trans c.g0Of_le_normalizer
  have hDR : (yOfL22 T M ⊔ sOf T K1) ⊓ L ≤ rOf T M K1 :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer hXL).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (isPGroup_sup_inf_of_not_le c hY)
  exact (inf_le_inf_right L le_sup_right).trans hDR

theorem isSylowTwoOf_rOf_inf_of_not_le (c : Core3Ctx T M H K1 L M₁) (hY : ¬ yOfL22 T M ≤ L) :
    IsSylowTwoOf (rOf T M K1 ⊓ L) L := by
  have h := A4.isSylowTwoOf_inf_normal (isSylowTwoOf_g0 c.inM c.sylow) c.le_g0Of
    c.g0Of_le_normalizer
  have heq : rOf T M K1 ⊓ L = sOf T K1 ⊓ L :=
    le_antisymm (inf_le_inf_right L (rOf_le_sOf c))
      (le_inf (inf_sOf_le_rOf_of_not_le c hY) inf_le_right)
  rw [heq]
  exact h

end Basic

end S1421

end CFSG.Quasithin
