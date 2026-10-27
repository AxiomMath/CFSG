module

public import CFSG.Quasithin.EmptyFaithful.S152ZFDefs
public import CFSG.Quasithin.EmptyFaithful.S152ZFTwist
public import CFSG.Quasithin.EmptyFaithful.S152He9R
public import CFSG.Quasithin.EmptyFaithful.S152XB
public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G]

theorem isQuasithinSub_mono {X Y : Subgroup G} (hXY : X ≤ Y) (hY : IsQuasithinSub Y) :
    IsQuasithinSub X := by
  intro p hp hp2 R hR hR1 hR2
  exact (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf_right _ hXY)).trans
    (hY p hp hp2 R (hR.trans hXY) hR1 hR2)

omit [Finite G] in
theorem card_of_small {L : Subgroup G}
    (hF : Nonempty (OTwoQuot L ≃* DihedralGroup 5) ∨
      Nonempty (OTwoQuot L ≃* ↥(CFSG.Open.Sz 0))) :
    Nat.card (OTwoQuot L) = 10 ∨ Nat.card (OTwoQuot L) = 20 := by
  rcases hF with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  · right
    rw [Nat.card_congr e.toEquiv]
    exact card_sz_zero_eq_twenty

@[expose] def twistFree (L2 S : Subgroup G) : Subgroup G :=
  (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ S)

variable {L1 L2 S : Subgroup G}

theorem pCoreOf_sup_le (hS2 : S ≤ Subgroup.normalizer (L2 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2) : pCoreOf 2 (L2 ⊔ S) ≤ S := by
  have hSS : IsSylowTwoOf S S := ⟨le_rfl, hS, by simp⟩
  have hodd : ¬ 2 ∣ (L2 ⊓ S).relIndex L2 := by
    rw [inf_comm]
    exact F7.isSylowTwoOf_odd_relIndex hsyl
  exact isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_sup hS2 hSS hodd)

theorem twistFree_le (hS2 : S ≤ Subgroup.normalizer (L2 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2) : twistFree L2 S ≤ S :=
  sup_le inf_le_left (pCoreOf_sup_le hS2 hS hsyl)

omit [Finite G] in
theorem inf_le_twistFree : S ⊓ L2 ≤ twistFree L2 S := le_sup_left

theorem twistFree_inf_L2 (hS2 : S ≤ Subgroup.normalizer (L2 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2) : twistFree L2 S ⊓ L2 = S ⊓ L2 :=
  le_antisymm (inf_le_inf_right L2 (twistFree_le hS2 hS hsyl))
    (le_inf inf_le_twistFree inf_le_right)

omit [Finite G] in
theorem le_normalizer_twistFree (hS2 : S ≤ Subgroup.normalizer (L2 : Set G)) :
    S ≤ Subgroup.normalizer ((twistFree L2 S : Subgroup G) : Set G) := by
  have h1 : S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    F1.le_normalizer_inf_of_le hS2
  have h2 : S ≤ Subgroup.normalizer ((pCoreOf 2 (L2 ⊔ S) : Subgroup G) : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 (L2 ⊔ S))
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1 hx, h2 hx⟩

theorem inf_L1_le_twistFree (hH : Hyp111 L1 L2 S)
    (hF1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (e : OTwoQuot L2 ≃* Alt5) : S ⊓ L1 ≤ twistFree L2 S :=
  inf_le_sup_pCore hH.h1.normalizes hH.h2.normalizes hH.h1.pgroup hH.h2.sylow hH.h1.borel_le e
    (not_three_dvd_card hF1)

theorem twistFree_inf_L1 (hH : Hyp111 L1 L2 S)
    (hF1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (e : OTwoQuot L2 ≃* Alt5) : twistFree L2 S ⊓ L1 = S ⊓ L1 :=
  le_antisymm (inf_le_inf_right L1 (twistFree_le hH.h2.normalizes hH.h1.pgroup hH.h2.sylow))
    (le_inf (inf_L1_le_twistFree hH hF1 e) inf_le_right)

theorem borelOf_twistFree_right (hH : Hyp111 L1 L2 S) :
    borelOf L2 (twistFree L2 S) = borelOf L2 S := by
  unfold borelOf
  rw [twistFree_inf_L2 hH.h2.normalizes hH.h1.pgroup hH.h2.sylow]

theorem borelOf_twistFree_left (hH : Hyp111 L1 L2 S)
    (hF1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (e : OTwoQuot L2 ≃* Alt5) : borelOf L1 (twistFree L2 S) = borelOf L1 S := by
  unfold borelOf
  rw [twistFree_inf_L1 hH hF1 e]

theorem hyp111_twistFree (hH : Hyp111 L1 L2 S)
    (hF1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (e : OTwoQuot L2 ≃* Alt5) : Hyp111 L1 L2 (twistFree L2 S) := by
  set S0 := twistFree L2 S with hS0
  have hS1 : S ≤ Subgroup.normalizer (L1 : Set G) := hH.h1.normalizes
  have hS2 : S ≤ Subgroup.normalizer (L2 : Set G) := hH.h2.normalizes
  have hle : S0 ≤ S := twistFree_le hS2 hH.h1.pgroup hH.h2.sylow
  have hinf1 : S0 ⊓ L1 = S ⊓ L1 := twistFree_inf_L1 hH hF1 e
  have hinf2 : S0 ⊓ L2 = S ⊓ L2 := twistFree_inf_L2 hS2 hH.h1.pgroup hH.h2.sylow
  have hB2 : borelOf L2 S0 = borelOf L2 S := borelOf_twistFree_right hH
  have hB1 : borelOf L1 S0 = borelOf L1 S := borelOf_twistFree_left hH hF1 e
  have hSN : S ≤ Subgroup.normalizer (S0 : Set G) := le_normalizer_twistFree hS2
  have hSB2 : S ≤ Subgroup.normalizer ((borelOf L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hS2
  have hSB1 : S ≤ Subgroup.normalizer ((borelOf L1 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf hS1
  refine ⟨⟨inferInstance, hH.h1.pgroup.to_le hle, hle.trans hS1, ?_, hH.h1.listed, ?_, ?_⟩,
    ⟨inferInstance, hH.h1.pgroup.to_le hle, hle.trans hS2, ?_, hH.h2.listed, ?_, ?_⟩, ?_⟩
  · rw [hinf1]; exact hH.h1.sylow
  · rw [hB2]; exact hH.h1.borel_le
  · rw [hB2]
    have hHK : L1 ⊔ S0 ⊔ borelOf L2 S ≤ L1 ⊔ S ⊔ borelOf L2 S :=
      sup_le_sup_right (sup_le_sup_left hle L1) _
    refine CharTwo.of_normal hH.h1.charTwo hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr ?_)
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
    · intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_sup (L1 ⊔ S0) (borelOf L2 S) ⟨?_, hSB2 hx⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup L1 S0 ⟨hS1 hx, hSN hx⟩
    · exact le_sup_right.trans Subgroup.le_normalizer
  · rw [hinf2]; exact hH.h2.sylow
  · rw [hB1]; exact hH.h2.borel_le
  · rw [hB1]
    have hHK : L2 ⊔ S0 ⊔ borelOf L1 S ≤ L2 ⊔ S ⊔ borelOf L1 S :=
      sup_le_sup_right (sup_le_sup_left hle L2) _
    refine CharTwo.of_normal hH.h2.charTwo hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr ?_)
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
    · intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_sup (L2 ⊔ S0) (borelOf L1 S) ⟨?_, hSB1 hx⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup L2 S0 ⟨hS2 hx, hSN hx⟩
    · exact le_sup_right.trans Subgroup.le_normalizer
  ·
    have hG0' : L1 ⊔ L2 ⊔ S0 ≤ L1 ⊔ L2 ⊔ S := sup_le_sup_left hle _
    have hnorm : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer ((L1 ⊔ L2 ⊔ S0 : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
      · exact (le_sup_right.trans le_sup_left).trans Subgroup.le_normalizer
      · intro x hx
        refine Subgroup.inf_normalizer_le_normalizer_sup (L1 ⊔ L2) S0 ⟨?_, hSN hx⟩
        exact Subgroup.inf_normalizer_le_normalizer_sup L1 L2 ⟨hS1 hx, hS2 hx⟩
    have hsub : pCoreOf 2 (L1 ⊔ L2 ⊔ S0) ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hG0')
        (hnorm.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    rw [hH.o2] at hsub
    exact le_bot_iff.mp hsub

theorem untw_twistFree (hH : Hyp111 L1 L2 S)
    (hF1 : Nat.card (OTwoQuot L1) = 10 ∨ Nat.card (OTwoQuot L1) = 20)
    (e : OTwoQuot L2 ≃* Alt5) :
    ∀ s ∈ twistFree L2 S, ∃ l ∈ L2, ∃ q ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 (twistFree L2 S)),
      s = l * q := by
  have hS1 : S ≤ Subgroup.normalizer (L1 : Set G) := hH.h1.normalizes
  have hS2 : S ≤ Subgroup.normalizer (L2 : Set G) := hH.h2.normalizes
  set S0 := twistFree L2 S with hS0
  set Q2 := pCoreOf 2 (L2 ⊔ S) with hQ2
  have hle : S0 ≤ S := twistFree_le hS2 hH.h1.pgroup hH.h2.sylow
  have hQS : Q2 ≤ S := pCoreOf_sup_le hS2 hH.h1.pgroup hH.h2.sylow
  have hQ0 : Q2 ≤ S0 := le_sup_right
  have hB1S : borelOf L1 S = S ⊓ L1 := by
    unfold borelOf
    exact S152X.inf_normalizer_eq_of_card hH.h1.sylow hF1
  have hB1 : borelOf L1 S0 = S ⊓ L1 := (borelOf_twistFree_left hH hF1 e).trans hB1S
  have hbig : bigB L1 L2 S0 ≤ L2 ⊔ S := by
    refine sup_le (sup_le ?_ ?_) (hle.trans le_sup_right)
    · rw [hB1]; exact inf_le_left.trans le_sup_right
    · exact (F1.borelOf_le L2 S0).trans le_sup_left
  have hQle : Q2 ≤ pCoreOf 2 (L2 ⊔ bigB L1 L2 S0) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (pCoreOf_isPGroup 2 _)
    · exact hQ0.trans (le_sup_right.trans le_sup_right)
    · exact (sup_le le_sup_left hbig).trans (le_normalizer_pCoreOf 2 (L2 ⊔ S))
  intro s hs
  have hQN : Q2 ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    hQS.trans (F1.le_normalizer_inf_of_le hS2)
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp hs
  exact ⟨a, ha.2, b, hQle hb, rfl⟩

end CFSG.Quasithin.F204

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F204

theorem input15204F112_of_untw (h : Input15204F112Untw) : Input15204F112 := by
  intro G _ _ L1 L2 S hH hqt _ hFD hA5
  obtain ⟨e⟩ := hA5
  have hF1 := card_of_small hFD
  have hB1S : borelOf L1 S = S ⊓ L1 := by
    unfold borelOf
    exact S152X.inf_normalizer_eq_of_card hH.h1.sylow hF1
  refine h G L1 L2 (twistFree L2 S) (hyp111_twistFree hH hF1 e) ?_ ?_ hFD ⟨e⟩
    (untw_twistFree hH hF1 e)
  · exact isQuasithinSub_mono (sup_le_sup_left
      (twistFree_le hH.h2.normalizes hH.h1.pgroup hH.h2.sylow) _) hqt
  · left
    rw [borelOf_twistFree_left hH hF1 e, hB1S,
      sup_eq_left.2 (inf_L1_le_twistFree hH hF1 e), Subgroup.subgroupOf_self]
    infer_instance

end CFSG.Quasithin.He9
