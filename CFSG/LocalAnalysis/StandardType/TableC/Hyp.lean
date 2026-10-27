module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.TableC.HypLeaves
public import CFSG.LocalAnalysis.StandardType.TableC.Extract
public import CFSG.LocalAnalysis.StandardType.TableC.HypJNorm

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem GGTCCtx.h0
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    ψ.range = ggG0 p B x L D J ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧
      StatedLieAdmissible t n 2 f ∧ 2 ≤ (ggU t n f).D.rank ∧
      commutator ↥(ggG0 p B x L D J) = ⊤ ∧
      LieModel (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) t n 2 f :=
  ⟨h.1.2.2.2.2.1.1, h.1.2.2.2.2.1.2, h.1.2.2.2.1.1, h.1.2.2.2.1.2, h.1.2.2.2.2.2.1.1,
    h.1.2.2.2.2.2.1.2⟩

theorem GGTCCtx.h12
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    p.Prime ∧ p ≠ 2 ∧ D ≤ B ∧ Nat.card D = p ^ 2 ∧ x ∈ D ∧ x ≠ 1 ∧
      IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) ∧
      B ≤ Subgroup.normalizer (J : Set G) ∧ B ⊓ Subgroup.centralizer (J : Set G) = D ∧
      L ≤ ggG0 p B x L D J ∧
      IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) ∧ J ≤ L ∧
      (∀ K : Subgroup G, IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) → K = J) ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) := by
  have hctx := h.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hctx.sstar.2.2.2.1
  have hLc : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL
      (le_inf le_sup_left hL.1) inf_le_right
  have hmkL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hctx.stdType.1
  have hHL := ggSixCtx_normalizer_and_innerDiag_on_L hctx
  have hJL : J ≤ L := hctx.j_le_inf.trans inf_le_left
  have hJH : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hctx.j_isComponentOf_inf
      (le_inf hJL (hctx.j_isComponentOf_inf.1.trans inf_le_right))
      (inf_le_inf_right _ le_sup_left)
  have hJonly : ∀ K : Subgroup G,
      IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) → K = J := fun K hK =>
    (CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hK.2.2 hJH hK
      ((le_largeEvenLayer hK).trans hctx.stdSub.1.2.2.2.2.1.symm.le) le_rfl).symm
  exact ⟨hctx.prime, hctx.ne_two, hctx.stdSub.1.1, hctx.card_d, hctx.x_mem_d, hctx.sstar.2.2.1,
    hctx.j_isComponentOf_inf, GGTCCtx.j_norm h,
    hctx.stdSub.1.2.2.2.2.2.2.symm, le_sup_left, hLc, hJL, hJonly, hHL.1, hmkL⟩

theorem GGTCCtx.h345
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    (∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S) ∧
      B ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
      (∀ b ∈ B, GGPsiInnerDiag (ggU t n f).D ψ b) ∧ IsElemAbelian p B ∧ p ^ 4 ≤ Nat.card B ∧
      B ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧
      (∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) ∧
      ∀ E T : Subgroup G, T ≠ ⊥ → IsPGroup 2 T → IsElemAbelian p E →
        E ≤ Subgroup.normalizer (T : Set G) → Nat.card E ≤ Nat.card B := by
  obtain ⟨hctx, -, -, -, -⟩ := h
  obtain ⟨-, -, -, -, -, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hBBs : B ≤ Bs := hctx.bstar.1
  exact ⟨hctx.sstar.2.2.2.2, hBBs.trans hBsN, fun b hb => hVI b (hBBs hb), hctx.sstar.1.1,
    hctx.pow_four_le_card_b,
    eq_bot_iff.mpr ((inf_le_inf_right _ hBBs).trans
      (bstar_inf_centralizer_ggG0_eq_bot hctx.config).le),
    hctx.sstar.1.2.2, ggTC_rank_le hctx.prime hctx.sstar.1⟩

theorem GGTCCtx.h7_odd
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    ∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G,
      IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) → J ≤ K →
        Odd (Nat.card (Subgroup.center ↥K)) := by
  intro d hd hd1 K hK hJK
  have hKeq : ggKd p B x L D J d = K := ggKd_eq_of_le_component hK h.1.j_comp.2.2 hJK
  have hz := h.2.2.2.2 d hd hd1
  rwa [hKeq] at hz

theorem GGTCCtx.hN
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    (t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1) → p ^ (n - 3) ≤ Nat.card B :=
  fun hc => (GGSixCtxV2.typeA_hN h.1 hc).2

theorem GGTCCtx.h8
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    (t = .E6 ∨ t = .twistedE6) → ∃ A : Subgroup G, B ≤ A ∧ IsElemAbelian p A ∧
      A ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
      (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) ∧
      A ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧
      (∀ y ∈ (A ⊔ ggG0 p B x L D J) ⊓ Subgroup.centralizer (A : Set G), orderOf y = p →
        y ∈ A) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ ggG0 p B x L D J) ≤ Nat.card A :=
  GGSixCtxV2.typeE_hE h.1

theorem ggTCHyp_of_ctx
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) :
    GGTCHyp t n f ψ p (ggG0 p B x L D J) B D J L x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.h0
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k15, k13, k14⟩ := h.h12
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := h.h345
  exact ⟨h1, h2, h3, h4, h5, h6, h.2.2.1, k1, k2, m2, m3, m4, m5, h.hN, m6, m7, m8, k3, k4, k5, k6,
    k7, k8, k9, k10, k11, k12, k15, k13, k14, m1, h.h7, h.h7_odd, h.h6, h.h8⟩

theorem ggSixFieldExtTableCAt_of_tcAt
    {t : StatedLieTag} (h : GGTCAt t) : GGSixFieldExtTableCAt t := by
  intro G _ _ p B Bs x L D J n f ψ hc hD hodd hcomp hz _ hE6 hF
  exact h G n f ψ p _ B D J L x (ggTCHyp_of_ctx ⟨hc, hD, hodd, hcomp, hz⟩) hF hE6

end CFSG.StandardType.TableCRes

end
