module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank

@[expose] def Lemma4310Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      Concl438 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ →
        ¬ IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K

variable {G : Type} [Group G] [Finite G]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem not_isC134Case4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hCS : T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    ¬ C134CorrLocal.IsC134Case4Corr (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K := by
  intro h
  obtain ⟨⟨m, F, _, _, -, hF, -, ⟨e⟩, -⟩, -⟩ := h
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    sk.base.pCoreOf_le_S.trans sk.S_le_normalizer
  have h1 : c134Q (K ⊔ pCoreOf 2 I) K ≤ pCoreOf 2 K :=
    (commutator_le_pCoreOf_of_le (perfect_of_mem_cComp sk.cComp) hRK le_rfl).1
  have h2 : c134CQ (K ⊔ pCoreOf 2 I) K ≤ T ⊓ H ⊓ Subgroup.centralizer (K : Set G) :=
    le_inf ((inf_le_left.trans h1).trans (sk.pCoreOf_K_le_S hR hC h37 h38 h39)) inf_le_right
  rw [hCS, le_bot_iff] at h2
  have hcard := Nat.card_congr e.toEquiv
  rw [h2, Subgroup.card_bot,
    show Nat.card (Multiplicative (Fin (2 * m) → ZMod 2)) = Nat.card (Fin (2 * m) → ZMod 2)
      from rfl, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hcard
  have hm : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have := Fintype.one_lt_card (α := F)
    rw [hF, hm0', pow_zero] at this
    exact lt_irrefl 1 this
  have : 2 ≤ 2 ^ (2 * m) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Setting432K

theorem lemma4310_of (h2 : Lemma4310Two) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Lemma4310 := by
  intro G _ _ T M L n I H K t sk hchar h41 h438 hCS
  rcases h438.2 with c2 | c3 | c4
  · exact absurd c2 (h2 G T M L n I H K t sk hchar h41 h438 hCS)
  · exact c3
  · exact absurd c4 (sk.not_isC134Case4 hR hC h37 h38 h39 hCS)

end CFSG.Quasithin.H13.Ch4
