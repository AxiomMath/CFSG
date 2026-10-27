module

public import CFSG.Quasithin.Background.F9Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem normalizer_LT_le (h : HypF91 T V L V₁ Vp H) {x : G} (hxLT : x ∈ L ⊔ T)
    (hxN : x ∈ Subgroup.normalizer (V₁ : Set G)) : x ∈ L₁Of L V₁ ⊔ T := by
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T h.normalizes_L
  obtain ⟨l, hl, t, ht, rfl⟩ : x ∈ (L : Set G) * T := by rw [← hmul]; exact hxLT
  have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    have := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ (h.T_normalizes_V₁ ht))
    simpa using this
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    isSylowTwoOf_mono_right (isSylowTwoOf_inf_normal h.sylow (le_top : L ≤ ⊤) h.normalizes_L)
      (le_inf inf_le_right (inf_le_left.trans h.T_normalizes_V₁)) inf_le_left
  have hl' := le_oTwoRes_sup_of_isSylowTwoOf hsyl ⟨hl, hlN⟩
  have hle : oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G)) ⊔ (T ⊓ L) ≤ L₁Of L V₁ ⊔ T :=
    sup_le_sup le_rfl inf_le_left
  exact Subgroup.mul_mem _ (hle hl') (le_sup_right (a := L₁Of L V₁) ht)

theorem mem_H_of_conj_eq (h : HypF91 T V L V₁ Vp H) {g y : G} (hg : g ∈ L) (hy : y ∈ L ⊔ T)
    (hV : conjSub g⁻¹ V₁ = conjSub y⁻¹ V₁) : y * g⁻¹ ∈ H := by
  have hN : y * g⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    have := congrArg (conjSub y) hV
    rwa [← conjSub_mul, conjSub_inv_conjSub] at this
  have hLT : y * g⁻¹ ∈ L ⊔ T :=
    Subgroup.mul_mem _ hy (Subgroup.inv_mem _ (le_sup_left (a := L) (b := T) hg))
  exact h.L₁T_le_H (h.normalizer_LT_le hLT hN)

theorem F96_1 (h : HypF91 T V L V₁ Vp H) {g y : G} (hg : g ∈ L) (hy : y ∈ L ⊔ T)
    (hV : conjSub g⁻¹ V₁ = conjSub y⁻¹ V₁) :
    conjSub g⁻¹ H = conjSub y⁻¹ H ∧ conjSub g⁻¹ (pCoreOf 2 H) = conjSub y⁻¹ (pCoreOf 2 H) ∧
      conjSub g⁻¹ (conjClosure Vp H) = conjSub y⁻¹ (conjClosure Vp H) ∧
      conjSub g⁻¹ (conjClosure V H) = conjSub y⁻¹ (conjClosure V H) := by
  have hH := h.mem_H_of_conj_eq hg hy hV
  have key : ∀ X : Subgroup G, H ≤ Subgroup.normalizer (X : Set G) →
      conjSub g⁻¹ X = conjSub y⁻¹ X := fun X hX => by
    have e : g⁻¹ = y⁻¹ * (y * g⁻¹) := by group
    rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hX hH)]
  exact ⟨key H Subgroup.le_normalizer, key _ (le_normalizer_pCoreOf 2 H),
    key _ (le_normalizer_conjClosure Vp H), key _ (le_normalizer_conjClosure V H)⟩

theorem F96_2 (h : HypF91 T V L V₁ Vp H) {g g₀ : G} (hg : g ∈ L) (hg₀ : g₀ ∈ L)
    (hV : conjSub g⁻¹ V₁ = conjSub g₀⁻¹ V₁) (hsq : g₀ * g₀ ∈ L₁Of L V₁ ⊔ T) :
    conjSub g₀⁻¹ (conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H)) =
        conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H ∧
      conjSub g₀⁻¹ (conjClosure V H ⊓ conjSub g⁻¹ (pCoreOf 2 H)) =
        conjSub g⁻¹ (conjClosure V H) ⊓ pCoreOf 2 H := by
  obtain ⟨-, hQ, hU, hVH⟩ := h.F96_1 hg (le_sup_left (a := L) (b := T) hg₀) hV
  have hsqH : (g₀ * g₀)⁻¹ ∈ H := Subgroup.inv_mem _ (h.L₁T_le_H hsq)
  have hQ2 : conjSub g₀⁻¹ (conjSub g₀⁻¹ (pCoreOf 2 H)) = pCoreOf 2 H := by
    rw [← conjSub_mul, show g₀⁻¹ * g₀⁻¹ = (g₀ * g₀)⁻¹ by group,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hsqH)]
  constructor
  · rw [conjSub_inf, hQ, hQ2, hU]
  · rw [conjSub_inf, hQ, hQ2, hVH]

theorem F96_3 (h : HypF91 T V L V₁ Vp H) {g : G} (hne : conjSub g⁻¹ V₁ ≠ V₁) :
    ⁅conjClosure V H ⊓ conjSub g⁻¹ (pCoreOf 2 H), conjSub g⁻¹ (conjClosure Vp H)⁆ ≤
        conjSub g⁻¹ V₁ ∧
      ⁅conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H),
        conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H⁆ = ⊥ := by
  have hUV : conjClosure Vp H ≤ conjClosure V H :=
    conjClosure_mono h.Vp_le_V le_rfl
  have hQU : ⁅pCoreOf 2 H, conjClosure Vp H⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun q hq u hu => ?_
    have := V₁.inv_mem (h.commutator_conjClosure_le u hu q hq)
    have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this
  have hQUg : ⁅conjSub g⁻¹ (pCoreOf 2 H), conjSub g⁻¹ (conjClosure Vp H)⁆ ≤ conjSub g⁻¹ V₁ := by
    rw [conjSub_commutator]; exact conjSub_mono _ hQU
  have part1 : ⁅conjClosure V H ⊓ conjSub g⁻¹ (pCoreOf 2 H), conjSub g⁻¹ (conjClosure Vp H)⁆ ≤
      conjSub g⁻¹ V₁ :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans hQUg
  refine ⟨part1, ?_⟩
  have hA : ⁅conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H),
      conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H⁆ ≤ conjSub g⁻¹ V₁ :=
    (Subgroup.commutator_mono (inf_le_inf_right _ hUV)
      (inf_le_left)).trans part1
  have hB : ⁅conjClosure Vp H ⊓ conjSub g⁻¹ (pCoreOf 2 H),
      conjSub g⁻¹ (conjClosure Vp H) ⊓ pCoreOf 2 H⁆ ≤ V₁ := by
    refine (Subgroup.commutator_mono inf_le_left inf_le_right).trans ?_
    rw [Subgroup.commutator_comm]; exact hQU
  have hbot : V₁ ⊓ conjSub g⁻¹ V₁ = ⊥ := by
    by_contra hne'
    have hcard : Nat.card (conjSub g⁻¹ V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
    have h1 : V₁ ≤ conjSub g⁻¹ V₁ := le_of_card_eq_two_of_inf_ne_bot h.card_V₁ hne'
    have h2 : V₁ = conjSub g⁻¹ V₁ :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, h.card_V₁])
    exact hne h2.symm
  exact le_bot_iff.mp (le_trans (le_inf hB hA) hbot.le)

end HypF91

end Fin

end CFSG.Quasithin
