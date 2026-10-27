module

public import CFSG.Quasithin.Vol2.Ch11SecA12Iface
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecA11Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

structure StarHyp (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G) : Prop where
  hyp : Hyp11 G T L I 2
  v₁ : IsVi T L I 2 1 V₁
  v₂ : IsVi T L I 2 2 V₂
  cartan : IsCartanX T L X
  comp : quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G))
  normal : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G)
  lt : LOf L V₁ < K
  not_le : ¬ K ≤ Subgroup.normalizer (L : Set G)
  charTwo : QuasithinUnique.CharTwo K
  le_cent : K ≤ Subgroup.centralizer (V₁ : Set G)
  psl : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)
  pgl : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(K ⊔ SecA.xOne X (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(K ⊔ SecA.xOne X (LOf L V₁)) ≃*
      (Matrix.GeneralLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))

namespace StarHyp

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem sylow (h : StarHyp G T L I V₁ V₂ X K) : quasithinIsSylowTwo T := h.hyp.fsu.sylow

theorem T_le_normalizer_V₁ (h : StarHyp G T L I V₁ V₂ X K) :
    T ≤ Subgroup.normalizer (V₁ : Set G) := h.v₁.2

theorem T_le_normalizer_K (h : StarHyp G T L I V₁ V₂ X K) :
    T ≤ Subgroup.normalizer (K : Set G) := h.T_le_normalizer_V₁.trans h.normal

theorem K_le_normalizer_V₁ (h : StarHyp G T L I V₁ V₂ X K) :
    K ≤ Subgroup.normalizer (V₁ : Set G) :=
  h.le_cent.trans (Subgroup.centralizer_le_normalizer _)

theorem perfect (h : StarHyp G T L I V₁ V₂ X K) : ⁅K, K⁆ = K := h.comp.2.1

theorem K_ne_bot (h : StarHyp G T L I V₁ V₂ X K) : K ≠ ⊥ := h.comp.1

theorem L₁_le_K (h : StarHyp G T L I V₁ V₂ X K) : LOf L V₁ ≤ K := h.lt.le

theorem L₁_ne_K (h : StarHyp G T L I V₁ V₂ X K) : LOf L V₁ ≠ K := h.lt.ne

theorem T_le_normalizer_L₁ (h : StarHyp G T L I V₁ V₂ X K) :
    T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
  SecA.T_le_normalizer_lOf h.hyp.normal h.v₁.2

theorem T_le_normalizer_L₂ (h : StarHyp G T L I V₁ V₂ X K) :
    T ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
  SecA.T_le_normalizer_lOf h.hyp.normal h.v₂.2

theorem perfect_L₁ (_h : StarHyp G T L I V₁ V₂ X K) : ⁅LOf L V₁, LOf L V₁⁆ = LOf L V₁ :=
  perfectCore_perfect _

theorem isSylowTwoOf_inf (h : StarHyp G T L I V₁ V₂ X K) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer h.T_le_normalizer_K)

theorem pCoreOf_le_inf (h : StarHyp G T L I V₁ V₂ X K) : pCoreOf 2 K ≤ T ⊓ K :=
  pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf_inf

theorem pCoreOf_le_T (h : StarHyp G T L I V₁ V₂ X K) : pCoreOf 2 K ≤ T :=
  h.pCoreOf_le_inf.trans inf_le_left

theorem V₁_le_T (h : StarHyp G T L I V₁ V₂ X K) : V₁ ≤ T :=
  (SecA.IsVi.le_fsuV h.v₁).trans (SecA.fsuV_le_T h.hyp)

theorem V₁_ne_bot (h : StarHyp G T L I V₁ V₂ X K) : V₁ ≠ ⊥ :=
  SecA.IsVi.ne_bot h.hyp h.v₁ le_rfl

theorem isPGroup_V₁ (h : StarHyp G T L I V₁ V₂ X K) : IsPGroup 2 V₁ :=
  (SecA.isPGroup_fsuV h.hyp).to_le (SecA.IsVi.le_fsuV h.v₁)

end StarHyp

theorem starHyp_of {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X)
    (hK : quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G)))
    (hKn : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K) (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (hK2 : QuasithinUnique.CharTwo K) (hKC : K ≤ Subgroup.centralizer (V₁ : Set G))
    (hK3 : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKX : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(K ⊔ SecA.xOne X (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(K ⊔ SecA.xOne X (LOf L V₁)) ≃*
        (Matrix.GeneralLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))) :
    StarHyp G T L I V₁ V₂ X K :=
  ⟨h, hV₁, hV₂, hX, hK, hKn, hlt, hKM, hK2, hKC, hK3, hKX⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
