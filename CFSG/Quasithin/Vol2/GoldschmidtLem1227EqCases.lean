module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqPar
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqL32
public import CFSG.Quasithin.Vol2.GoldschmidtOut1222
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Background.B69Num
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace Lem1227Eq

variable {G : Type} [Group G] [Finite G] {T K H M₀ : Subgroup G}

theorem nonempty_star_equiv (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K) {X : Type} [Group X]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) :
    Nonempty (↥(E2.star M₀ H K) ≃* X) := by
  obtain ⟨eS⟩ := nonempty_mulEquiv_star hKH hHK hmin hker
  exact ⟨eS.symm.trans e⟩

theorem nonempty_star_equiv_of_center (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K) {X : Type} [Group X]
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* X) (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    Nonempty (↥(E2.star M₀ H K) ≃* X) :=
  nonempty_star_equiv hKH hHK hmin hker
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e)

theorem not_isPGroup_two_of_three_dvd {X : Type*} [Group X] [Finite X] (h : 3 ∣ Nat.card X) :
    ¬ IsPGroup 2 X := by
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h
  have := (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem l32_not_D_A {V : Subgroup G} [IsMulCommutative ↥V]
    (hH : Hyp1223 G T K V) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcard : Nat.card V = 8 ∨ Nat.card V = 16) :
    ¬ E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)) ∧
      E2.autCard (E2.star M₀ H T) (E2.star M₀ H K) ≤ 8 := by
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hH.normalizes
  obtain ⟨hsq, hO⟩ := hyp_facts hH
  have d : SL32Data K V :=
    ⟨hH.irrPlus.2.2.1, hsq, hH.irrPlus.2.2.2.1, hH.irrPlus.2.2.2.2.2.1, hO, ⟨e⟩, hcard⟩
  have hin := d.exists_mul_mem_pCoreOf hTV hTK
  have hOker : pCoreOf 2 K ≤ kerIn M₀ H :=
    (pCoreOf_le_pCoreOf_of_normal hKH hHK).trans hmin.pCoreOf_le_kerIn
  have hinn := inner_star (M₀ := M₀) (T := T) hKH fun t ht => by
    obtain ⟨k, hk, h⟩ := hin t ht
    exact ⟨k, hk, fun x hx => hOker (h x hx)⟩
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    Lem8.center_eq_bot_of_mulEquiv e (Out1222.center_sl_zmod_two_eq_bot 3)
  obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    isSimpleGroup_sl_zmodTwo (n := 3) le_rfl
  have hsimple : IsSimpleGroup ↥(E2.star M₀ H K) := e2.isSimpleGroup
  have hcardK : Nat.card ↥(E2.star M₀ H K) = 168 := by
    rw [Nat.card_congr e2.toEquiv]
    exact card_sl_three_zmod_two
  have hZK : Subgroup.center ↥(E2.star M₀ H K) = ⊥ :=
    Lem8.center_eq_bot_of_mulEquiv e2 (Out1222.center_sl_zmod_two_eq_bot 3)
  obtain ⟨hT2, hSyl⟩ := isSylowTwoOf_star hKH hHK hmin
  have hnn : ¬ E2.star M₀ H K ≤ Subgroup.normalizer ((E2.star M₀ H (T ⊓ K) :
      Subgroup (E2.StarQuot M₀ H)) : Set (E2.StarQuot M₀ H)) :=
    not_le_normalizer_of_simple hSyl (by rw [hcardK]; norm_num)
      (not_isPGroup_two_of_three_dvd (by rw [hcardK]; norm_num))
  refine ⟨not_isDiagramNontrivial_of_inner hSyl hnn (star_le_normalizer hTK)
    (star_le_normalizer_star (le_normalizer_inf_self hTK)) hinn, ?_⟩
  exact autCard_le_eight_of_inner hT2 (star_le_normalizer hTK) hZK hcardK hinn

theorem false_of_lieModel_four {X : Type} [Group X]
    (hfam : B69.E22Fam X) (hL : LieModel X .PSL 4 2 1) (hcard : Nat.card X = 20160) : False := by
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
  obtain ⟨F, _, _, hF, ⟨e3⟩⟩ := hfam.exists_psl_three_four hcard
  exact B69.not_equiv_sl_four_psl_three (by rw [hK', pow_one]) hF e' e3

end Lem1227Eq

end CFSG.Quasithin.H13
