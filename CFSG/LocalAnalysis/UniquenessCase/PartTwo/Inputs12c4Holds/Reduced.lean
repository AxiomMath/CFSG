module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542FourModule
public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem isTwoReducedIn_of {M V : Subgroup G} (hV : InCalV M V)
    (hR : TwoReduced M V) : IsTwoReducedIn M V := by
  obtain ⟨-, hVM, hMN, hVel⟩ := hV
  refine ⟨hVM, hMN, hVel, ?_⟩
  intro D hDM hDN hD2
  set W : Subgroup G := Subgroup.centralizer (V : Set G)
  set C : Subgroup G := M ⊓ W
  set K : Subgroup G := D ⊔ C
  have hKM : K ≤ M := sup_le hDM inf_le_left
  have hMW : M ≤ Subgroup.normalizer (W : Set G) :=
    hMN.trans (B2F.normalizer_le_normalizer_centralizer V)
  have hMM : M ≤ Subgroup.normalizer (M : Set G) := fun x hx => Subgroup.le_normalizer hx
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := B2F.le_normalizer_inf hMM hMW
  have hDC : D ≤ Subgroup.normalizer (C : Set G) := hDM.trans hMC
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := B2F.le_normalizer_sup hDN hMC
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := hKM.trans hMC
  haveI : (C.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDC
  haveI : (C.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKC
  have hDquot : IsPGroup 2 (D ⧸ C.subgroupOf D) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hD2 d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      exact ⟨M.pow_mem (hDM d.2) (2 ^ k), hk⟩
  have hKquot : IsPGroup 2 (K ⧸ C.subgroupOf K) :=
    hDquot.of_equiv (QuotientGroup.quotientInfEquivProdNormalizerQuotient D C hDC)
  have hidx : ∃ n : ℕ, (W.subgroupOf K).index = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKquot
    have hCW : C.subgroupOf K = W.subgroupOf K := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hKM x.2, h⟩⟩
    refine ⟨n, ?_⟩
    rw [Subgroup.index_eq_card, ← hn, ← hCW]
  exact le_sup_left.trans (hR K hKM hMK le_sup_right hidx)

theorem pCoreOf_le_centralizer {M V : Subgroup G} (hV : InCalV M V) (hR : TwoReduced M V) :
    pCoreOf 2 M ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have h2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  refine (isTwoReducedIn_of hV hR).2.2.2 (pCoreOf 2 M) hD ?_ ?_
  · exact le_normalizer_pCoreOf 2 M
  · intro d hd
    obtain ⟨k, hk⟩ := h2 ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hk']
    exact Subgroup.one_mem _

theorem pCoreOf_autI_eq_bot {M V : Subgroup G} (hV : InCalV M V) (hR : TwoReduced M V)
    (hVe : IsElemAbelian 2 V) : pCoreOf 2 (autI hVe M) = ⊥ := by
  have hred : IsTwoReducedIn M V := isTwoReducedIn_of hV hR
  have h := CFSG.Quasithin.EmptyFaithfulMultiple.pCore_autOn_eq_bot hred
  have h' : CFSG.pCore 2 (autI hVe M) = ⊥ := h
  rw [pCoreOf, h', Subgroup.map_bot]

theorem isKGroup_autI {M V : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ normalizer (V : Set G)) (hK : CFSG.Open.IsKGroup ↥M) :
    CFSG.Open.IsKGroup ↥(autI hVe M) := by
  let φ : M →* MulAut (IntMod V hVe) := convHom hVe M hMN
  have hrange : φ.range = autI hVe M := range_convHom hVe M hMN
  refine hK.of_surjective (φ.codRestrict (autI hVe M) ?_) ?_
  · intro x
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  · intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact y.2)
    exact ⟨x, Subtype.ext hx⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg
