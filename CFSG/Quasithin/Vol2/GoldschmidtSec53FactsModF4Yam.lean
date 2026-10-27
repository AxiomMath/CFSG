module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Base
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.Quasithin.H13.Sec53F.BA
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (largeRee_named_covers nonabelian_zero
  nonabelian_one)

set_option linter.unusedSectionVars false


section Lattice

variable {C : Type*} [Group C] {B P₀ P₁ U : Subgroup C}

theorem isCoatom_of_covers (hUB : U ≤ B) (c0 : B ⋖ P₀) (c1 : B ⋖ P₁) (hn0 : P₀ ≠ ⊤)
    (hn1 : P₁ ≠ ⊤) (hcov : ∀ A : Subgroup C, U ≤ A → A ≠ ⊤ → A ≤ P₀ ∨ A ≤ P₁) :
    IsCoatom P₀ ∧ IsCoatom P₁ := by
  refine ⟨⟨hn0, fun b hb => ?_⟩, ⟨hn1, fun b hb => ?_⟩⟩
  · by_contra hbt
    rcases hcov b (hUB.trans (c0.le.trans hb.le)) hbt with h | h
    · exact lt_irrefl _ (hb.trans_le h)
    · exact c1.2 c0.lt (hb.trans_le h)
  · by_contra hbt
    rcases hcov b (hUB.trans (c1.le.trans hb.le)) hbt with h | h
    · exact c0.2 c1.lt (hb.trans_le h)
    · exact lt_irrefl _ (hb.trans_le h)

theorem inf_eq_of_covers (c0 : B ⋖ P₀) (c1 : B ⋖ P₁) (hne : P₀ ≠ P₁) : P₀ ⊓ P₁ = B := by
  have hB : B ≤ P₀ ⊓ P₁ := le_inf c0.le c1.le
  rcases c0.eq_or_eq hB inf_le_left with h | h
  · exact h
  · have hle : P₀ ≤ P₁ := h ▸ inf_le_right
    rcases c1.eq_or_eq c0.le hle with h' | h'
    · exact absurd h' c0.lt.ne'
    · exact absurd h' hne

theorem isTwoLocal_of_isCoatom {V : Subgroup C} (hP : IsCoatom P₀) (hV : V ≠ ⊥)
    (hVp : IsPGroup 2 ↥V) (hPN : P₀ ≤ Subgroup.normalizer (V : Set C))
    (hno : ∀ R : Subgroup C, R.Normal → IsPGroup 2 ↥R → R = ⊥) : IsTwoLocal P₀ :=
  ⟨V, hV, hVp, ((hP.le_iff.1 hPN).resolve_left fun h =>
    hV (hno V (Subgroup.normalizer_eq_top_iff.1 h) hVp)).symm⟩

end Lattice

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem eq_bot_of_normal_pGroup (hK : Nat.card K = 2 ^ (2 * a + 1))
    {R : Subgroup ↥(F4.reeGamma K a)} (hR : R.Normal) (hRp : IsPGroup 2 ↥R) : R = ⊥ := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hsyl := (largeRee_named_covers a K hK).1
  have hRc : R ≤ pCoreOf 2 (⊤ : Subgroup ↥(F4.reeGamma K a)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (Subgroup.normalizer_eq_top_iff.2 hR).ge hRp
  have hRU := hRc.trans (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl)
  have hRB : R ≤ ((F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a)).normalCore :=
    Subgroup.normal_le_normalCore.2 (hRU.trans (Subgroup.subgroupOf_mono (F4.reeGamma K a)
      reeFixedPosUnipotent_le_reeFixedBorel))
  have h1 := hRB.trans (normalCore_reeFixedBorel_le_center hK)
  rwa [large_Ree_fixed_group_center_trivial a K hK, ← eq_bot_iff] at h1

theorem radical_subgroupOf_ne_bot (j : Fin F4.fixedOrbitCount)
    (hnab : ∃ x ∈ F4.reeFixedOrbitComplementUnipotent K a j,
      ∃ y ∈ F4.reeFixedOrbitComplementUnipotent K a j, x * y ≠ y * x) :
    (F4.reeFixedOrbitComplementUnipotent K a j).subgroupOf (F4.reeGamma K a) ≠ ⊥ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  intro h
  apply hxy
  have hx' : (⟨x, reeFixedOrbitComplementUnipotent_le_reeGamma j hx⟩ : ↥(F4.reeGamma K a)) ∈
      (F4.reeFixedOrbitComplementUnipotent K a j).subgroupOf (F4.reeGamma K a) := hx
  rw [h, Subgroup.mem_bot] at hx'
  have : x = 1 := congrArg Subtype.val hx'
  rw [this, one_mul, mul_one]

theorem f4_yamStd (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Yam.YamStd ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hsyl, hcov, hn0, hn1, hgen, -, -⟩ := largeRee_named_covers a K hK
  have hD := CFSG.QuasithinUnique.B113Lie.LargeRee.parabolicData ha hK
  have c0 := (hcov _).2 (Or.inl rfl)
  have c1 := (hcov _).2 (Or.inr rfl)
  have hne : ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) ≠
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
    intro h
    rw [h, sup_idem] at hgen
    exact hn1 hgen
  have hUB := (Subgroup.le_normalizer
    (H := ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))))
  have hcov' : ∀ A : Subgroup ↥(F4.reeGamma K a),
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ≤ A → A ≠ ⊤ →
      A ≤ ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) ∨
        A ≤ ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
    intro A hUA hA
    obtain ⟨P, hP, hAP⟩ := hD.cover A hUA hA
    rcases hP with rfl | hP
    · exact Or.inl hAP
    · exact Or.inr (Set.mem_singleton_iff.1 hP ▸ hAP)
  obtain ⟨hco0, hco1⟩ := isCoatom_of_covers hUB c0 c1 hn0 hn1 hcov'
  have hno : ∀ R : Subgroup ↥(F4.reeGamma K a), R.Normal → IsPGroup 2 ↥R → R = ⊥ :=
    fun R hR hRp => eq_bot_of_normal_pGroup hK hR hRp
  exact ⟨hsyl, hno, hne, c0.le, c1.le, hco0, hco1,
    fun A hA hAt => hcov' A (hUB.trans hA) hAt,
    isTwoLocal_of_isCoatom hco0 (radical_subgroupOf_ne_bot _ (nonabelian_zero hK))
      (isPGroup_subgroupOf_rad ha hK _) (parabolic_subgroupOf_le_normalizer _) hno,
    isTwoLocal_of_isCoatom hco1 (radical_subgroupOf_ne_bot _ (nonabelian_one hK))
      (isPGroup_subgroupOf_rad ha hK _) (parabolic_subgroupOf_le_normalizer _) hno⟩

end CFSG.Quasithin.H13.Sec53F.ReeF4
