module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeSetup
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeY
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeShape
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeEnd
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S22Fin3R (D : Data G) (Ch : Choice2011 G) : Prop :=
  S22_8 D Ch → S22_15 D Ch → S22_17 D Ch → H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig,
    ∀ (K : Subgroup G) (n : ℕ), K2213 D c p K n → ∀ t ∈ D.T, t ∉ normalizer (K : Set G) →
    mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M c.V)) →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M → ∀ H ∈ hSet D.T D.M,
    centralizer (D.Z : Set G) ≤ H → D.M ⊓ centralizer (c.V : Set G) ≤ H →
    p ∣ Nat.card ↥(H ⊓ D.M) → (∃ x ∈ D.M ⊓ centralizer (c.V : Set G), orderOf x = p) →
      ∃ m f : ℕ, 2 < m ∧ m ≤ 4 ∧ 2 < f ∧ ¬ 2 ^ f ≡ 1 [MOD p] ∧
        Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 (H ⊓ D.M)))) ≃*
          CFSG.Open.StatedSL (m - 1) (GaloisField 2 f)) ∧
        (m = 3 → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M →
          Opp p (H ⊓ D.M) ∈ calC (D.M ⊓ centralizer (c.V : Set G)) →
          Nonempty (Bar2 (Opp p (H ⊓ D.M)) ≃* CFSG.Open.StatedSL 2 (GaloisField 2 f)) →
            ∃ A : Subgroup G, c.B0 ≤ A ∧ IsMulCommutative A ∧
              A ⊓ Opp p (H ⊓ D.M) ⊓ c.B0 = ⊥ ∧ Nonempty (↥(A ⊓ Opp p (H ⊓ D.M)) ≃* ↥c.B0))

theorem s22_fin_of_s22Fin3R {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h82 : F08.R82 D) (h16 : S21_16 D Ch) (h17 : S21_17 D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hR : S22Fin3R D Ch) :
    S22_8 D Ch → S22_15 D Ch → S22_17 D Ch → S22_fin D Ch := by
  intro h8 h15 h2217 h1930 c p hp K n hK t htT htN hX
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨hsp, H, hH, hZH, hVH, hpH, x, hx, hxp⟩ :=
    P22fin3.setup D hSg h15 h1930 c hp hK htT htN hX
  obtain ⟨m, f, hm, hm4, hf, h1, ⟨e⟩, hRA⟩ :=
    hR h8 h15 h2217 h1930 c p hp K n hK t htT htN hX hsp H hH hZH hVH hpH ⟨x, hx, hxp⟩
  obtain ⟨hYV, hYC, hY, ⟨eY⟩⟩ := P22fin3.opp_mem_calC (X := H ⊓ D.M) c.hVM inf_le_right
    (le_inf hVH inf_le_left) hpP hp2 hx hxp hm (by omega) h1 e
  obtain rfl : m = 3 := P22fin3.eq_three_of_s21_16 hm hm4 hf eY (h16 h1930 c.toCtx21 _ hY)
  have hL2 := h15 h1930 c p hp K n hK
  have htM : t ∈ D.M := D.sylowM.le htT
  have hYV' : Opp p (H ⊓ D.M) ≤ centralizer (c.V : Set G) := hYV.trans inf_le_right
  have hk1 := P22fin3.isStronglyPEmbedded_three_of_sup D h82 h17 h1930 c hK.1 hL2 htM htN hY
    hYV' hf.le eY
  obtain ⟨A, hBA, hA, hAYB, ⟨eA⟩⟩ := hRA rfl hk1 hYC ⟨eY⟩
  exact P22fin3.false_of_endgame D hSg h76 h17 h1930 c hσ hk1 (by have := hn3 h1930 c; omega)
    hK.1 hL2 htM htN hY hYV' hf.le eY hBA hA hAYB eA

end CFSG.LocalAnalysis.UniquenessCase.UC22
