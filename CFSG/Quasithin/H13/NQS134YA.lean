module

public import CFSG.Quasithin.H13.NQS13410Asm2

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure KWData (S : A6.Setting134 G T L V) (K W : Subgroup G) [IsMulCommutative ↥W] : Prop where
  Kf : quasithinIsFaithfulLocal T K
  TK : T ≤ normalizer (K : Set G)
  KM : ¬ K ≤ normalizer (L : Set G)
  KZV : ¬ K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G)
  KJ : ⁅K, thompsonJ T⁆ = K
  Ktype : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
    LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K
  Wirr : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W
  TW : T ≤ normalizer (W : Set G)
  fsu : FSU G T K W
  Wcl : W = conjClosure (quasithinOmegaOneCenter T ⊓ W) K
  mod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
    (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
    (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
      FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) ∨
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
      BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∧ W ⊓ centralizer (K : Set G) = ⊥)
  o2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)

namespace KWData

variable {S : A6.Setting134 G T L V} {K W : Subgroup G} [IsMulCommutative ↥W]
  (D : KWData S K W)
include D

theorem isSylowTwoOf : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, D.Kf.1.1, D.Kf.1.2.2.1⟩

theorem charTwo : CharTwo (K ⊔ T) := U3.s134_charTwo_of_inH S ⟨le_sup_right, D.Kf.1.2.2.2⟩

theorem W_le_T : W ≤ T :=
  (D.Wirr.1.trans (R2_le_pCoreOf (K ⊔ T))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf D.isSylowTwoOf)

theorem isSylowTwoOf_inf : IsSylowTwoOf (T ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal D.isSylowTwoOf le_sup_left (sup_le le_normalizer D.TK)

theorem sq_eq_one {w : G} (hw : w ∈ W) : w ^ 2 = 1 :=
  (twoReduced_R2 (K ⊔ T)).2.2.1.2 w (D.Wirr.1 hw)

theorem normalizer_W_le (h1332 : Stmt13_3_2) :
    normalizer (W : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨-, ⟨-, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K D.Kf
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨W, D.Wirr.2.1, S.h13.sylow.1.to_le D.W_le_T, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
  have := huniqK M' hM' ((sup_le D.Wirr.2.2.1 D.TW).trans hle)
  exact this ▸ hle

theorem not_le_centralizer_R2 :
    ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) := by
  intro h
  apply D.KZV
  have hZV : V ⊓ centralizer (L : Set G) ≤ reducedAggregate (K ⊔ T) :=
    ((S.ZV_le_ZL.trans inf_le_left).trans (le_conjClosure _ K)).trans
      (vH_le_R2 D.isSylowTwoOf D.charTwo D.TK)
  exact h.trans (centralizer_le (SetLike.coe_subset_coe.mpr hZV))

theorem pCoreOf_le_R2 : pCoreOf 2 K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) :=
  (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le le_normalizer D.TK).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans (pCoreOf_le_centralizer_R2 (K ⊔ T))

theorem card_autOn_R2_le : Nat.card ↥(autOn K (reducedAggregate (K ⊔ T))) ≤ 1080 := by
  have hdvd := A6.card_autOn_dvd_quot (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1)
    D.pCoreOf_le_R2
  obtain ⟨c5, c3, c6, cH⟩ := card_quot_of_type K
  have hle : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≤ 1080 := by
    rcases D.Ktype with h | h | h | h
    · rw [c5 h]
      norm_num
    · rw [c3 h]
      norm_num
    · rw [c6 h]
      norm_num
    · rw [cH h]
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans hle

theorem vK_ne_bot : ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ≠ ⊥ := by
  intro h
  apply D.KZV
  have h1 : K ≤ centralizer (conjClosure (quasithinOmegaOneCenter T) K : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  exact h1.trans (centralizer_le (SetLike.coe_subset_coe.mpr
    ((S.ZV_le_ZL.trans inf_le_left).trans (le_conjClosure _ K))))

theorem Z_le_vK :
    quasithinOmegaOneCenter T ≤
      ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ⊔ U3.cZ T K := by
  rw [← vH_eq_sup D.isSylowTwoOf D.charTwo D.TK]
  exact le_conjClosure _ K

theorem split (h56 : AsB56) :
    ∃ _ : IsMulCommutative ↥(reducedAggregate (K ⊔ T)),
      commV (autOn K (reducedAggregate (K ⊔ T))) ∈
          IrrPlus (autOn K (reducedAggregate (K ⊔ T))) ⊤ ∨
        B51Case1ii (ffJ (autOn (K ⊔ T) (reducedAggregate (K ⊔ T))))
          (autOn K (reducedAggregate (K ⊔ T))) := by
  obtain ⟨hab, -, hcases⟩ := b51Part1_K h56 S D.Kf D.TK D.fsu.quasisimple
    D.not_le_centralizer_R2 D.KJ
  refine ⟨hab, ?_⟩
  have h6048 : Nat.card ↥(autOn K (reducedAggregate (K ⊔ T))) ≤ 6048 :=
    D.card_autOn_R2_le.trans (by norm_num)
  rcases hcases with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr h
  · exact absurd h (U3.not_case1iii_iv h6048).1
  · exact absurd h (U3.not_case1iii_iv h6048).2

theorem comm_eq_of_irr [IsMulCommutative ↥(reducedAggregate (K ⊔ T))]
    (hi : commV (autOn K (reducedAggregate (K ⊔ T))) ∈
      IrrPlus (autOn K (reducedAggregate (K ⊔ T))) ⊤) :
    ⁅reducedAggregate (K ⊔ T), K⁆ = W ∧
      ⁅reducedAggregate (K ⊔ T), K⁆ = ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ :=
  ⟨U3.eq_of_irrPlus (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1) hi D.Wirr.1 D.Wirr.2.2.1
      D.Wirr.2.2.2.1 D.Wirr.2.1,
    comm_R2_eq_vK D.isSylowTwoOf D.charTwo D.TK D.Kf.1.2.1.2.1 hi D.vK_ne_bot⟩

theorem W_le_comm : W ≤ ⁅reducedAggregate (K ⊔ T), K⁆ := by
  have h := commutator_mono D.Wirr.1 (le_refl K)
  rwa [D.Wirr.2.2.2.1] at h

theorem Z_le_comm :
    quasithinOmegaOneCenter T ≤ ⁅reducedAggregate (K ⊔ T), K⁆ ⊔ U3.cZ T K :=
  D.Z_le_vK.trans (sup_le_sup_right (vK_le_comm D.isSylowTwoOf D.charTwo D.TK) _)

end KWData

end CFSG.Quasithin.H13.NQS134
