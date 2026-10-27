module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem IsChiefSeriesBetween.eq_zero_of_self {H U N : Subgroup G} {m : ℕ}
    (h : F112W.IsChiefSeriesBetween H U N N m) : m = 0 := by
  cases h with
  | refl => rfl
  | central hstep _ hs => exact absurd (hs.le.trans_lt hstep.2.2.1) (lt_irrefl _)
  | noncentral hstep _ hs => exact absurd (hs.le.trans_lt hstep.2.2.1) (lt_irrefl _)

theorem IsChiefSeriesBetween.le_one_of_irred {H U W N : Subgroup G} {m : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W N m)
    (hirr : ∀ K : Subgroup G, IsNormalIn H U K → W ≤ K → K ≤ N → K = W ∨ K = N) : m ≤ 1 := by
  cases h with
  | refl => exact Nat.zero_le _
  | @central N L' m hstep _ hs =>
    rcases hirr L' hstep.2.1 hs.le hstep.2.2.1.le with rfl | rfl
    · have := IsChiefSeriesBetween.eq_zero_of_self hs
      omega
    · exact absurd hstep.2.2.1 (lt_irrefl _)
  | @noncentral N L' m hstep _ hs =>
    rcases hirr L' hstep.2.1 hs.le hstep.2.2.1.le with rfl | rfl
    · rw [IsChiefSeriesBetween.eq_zero_of_self hs]
    · exact absurd hstep.2.2.1 (lt_irrefl _)

theorem le_one_of_isShort2 [Finite G] {L : Subgroup G} (hL : IsShort2 L) {n : ℕ}
    (hn : IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) n) : n ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hUQ : blockU L ≤ pCoreOf 2 L := F112W.commutator_le_self_of_le_normalizer hLQ
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZC : blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have hQn : IsNormalIn L (pCoreOf 2 L) (pCoreOf 2 L) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hLQ
  have hUn : IsNormalIn L (pCoreOf 2 L) (blockU L) :=
    F112W.isNormalIn_of_le_normalizer hUQ fun g hg =>
      A4.mem_normalizer_commutator (hLQ hg) (Subgroup.le_normalizer hg)
  have hZn : IsNormalIn L (pCoreOf 2 L) (blockZ L) := ⟨hZU.trans hUQ, fun g hg z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp (hZC hz) g hg), mul_inv_cancel_right]
    exact hz⟩
  have h1 : F112W.eta L (pCoreOf 2 L) (pCoreOf 2 L) = F112W.eta L (pCoreOf 2 L) (blockU L) :=
    F112W.eta_eq_of_commutator_le hQL le_rfl hUn hQn hUQ
      (Subgroup.commutator_mono le_rfl (oTwoUpper_le L))
  obtain ⟨m, hm⟩ := F112W.exists_isChiefSeriesBetween hZn (blockU L) hUn hZU
  have h2 := F112W.eta_eq_add hQL hZn hm
  have h3 : F112W.eta L (pCoreOf 2 L) (blockZ L) = 0 := by
    refine (F112W.eta_eq_zero_iff hQL le_rfl hZn).mpr ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hZC.trans (Subgroup.centralizer_le (oTwoUpper_le L))
  have h4 : m ≤ 1 := IsChiefSeriesBetween.le_one_of_irred hm fun K hK hZK hKU =>
    hL.2.2.2.2.2 K hZK hKU (D14.le_normalizer_of_isNormalIn hK)
  have h5 := (F112W.isChiefSeriesFrom_iff_eta hQL hQn).mp hn
  omega

end CFSG.Quasithin.H13
