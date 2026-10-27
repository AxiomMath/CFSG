module

public import CFSG.Quasithin.Vol2.Asc94.TSCaseII
public import CFSG.Quasithin.Vol2.Asc94.TSModel12
public import CFSG.Quasithin.Vol2.Asc94.HeNB1
public import CFSG.Quasithin.Vol2.Asc94.HeNB6
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeldBridge
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step410
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.Quasithin.A94.HeK

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem card_T : Nat.card (tr e L52.Tm) = 1024 := by
  rw [card_tr, L52.card_Tm]; norm_num

theorem card_Q : Nat.card (tr e L52.Qh) = 2 ^ 7 := by
  rw [card_tr, L52.card_Qh]; norm_num

theorem Q_le_T : tr e L52.Qh ≤ tr e L52.Tm := tr_mono e L52.Qh_le_Tm

theorem lt_card_Q_T : Nat.card (tr e L52.Qh) < Nat.card (tr e L52.Tm) := by
  rw [card_Q, card_T]; norm_num

theorem centerIn_T (hz : orderOf z = 2) : centerIn (tr e L52.Tm) = zpowers z := by
  show centerIn (frame0 e hz).T = zpowers z
  apply le_antisymm
  · rintro x ⟨hxT, hxc⟩
    rcases (frame0 e hz).center_T x hxT (fun y hy => (mem_centralizer_iff.mp hxc y hy).symm) with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers z
  · rw [zpowers_le]
    refine ⟨(frame0 e hz).z_mem_T, mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (frame0 e hz).z_comm_T hy |>.symm

theorem isSylowOf_T_top (hz : orderOf z = 2) : IsSylowOf 2 (tr e L52.Tm) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := s39_2 (frame0 e hz)
  refine isSylowOf_of_card le_top ?_
  rw [card_top, ← P.card_eq_multiplicity]
  show Nat.card (tr e L52.Tm) = Nat.card P
  rw [show (tr e L52.Tm : Subgroup G) = (frame0 e hz).T from rfl, ← hP]

theorem T_le_normalizer_A1 (hz : orderOf z = 2) (hF6 : L52.F6Model) :
    tr e L52.Tm ≤ normalizer ((tr e L52.A1 : Subgroup G) : Set G) := by
  intro t ht
  show t ∈ normalizer (((frame2 e hz hF6).A : Subgroup G) : Set G)
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := (frame2 e hz hF6).A_normal t⁻¹ (inv_mem ht) a ha
    simpa using this
  · intro ha
    have := (frame2 e hz hF6).A_normal t ht _ ha
    simpa [mul_assoc] using this

theorem T_le_normalizer_A2 (hz : orderOf z = 2) (hF6 : L52.F6Model) :
    tr e L52.Tm ≤ normalizer ((tr e L52.A2 : Subgroup G) : Set G) := by
  intro t ht
  show t ∈ normalizer (((frame2 e hz hF6).A' : Subgroup G) : Set G)
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := (frame2 e hz hF6).A'_normal t⁻¹ (inv_mem ht) a ha
    simpa using this
  · intro ha
    have := (frame2 e hz hF6).A'_normal t ht _ ha
    simpa [mul_assoc] using this

theorem isSylowOf_T_normalizer_J (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) :
    IsSylowOf 2 (tr e L52.Tm)
      (normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz := S.ord
  obtain ⟨-, hN, -⟩ := caseII_facts hF6 S h1 h2
  refine isSylowOf_of_card ?_ ?_
  · have := (frame4 e hz hF6).T_le_normalizer_J
    exact this
  · have hN' : Nat.card ↥(normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) =
        9 * 1024 := hN
    rw [hN', card_T]
    have : (9 * 1024 : ℕ).factorization 2 = 10 := by
      rw [show (9 * 1024 : ℕ) = 9 * 2 ^ 10 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      simp
    rw [this]; norm_num

theorem pCoreOf_Cz : pCoreOf 2 (Cz z) = tr e L52.Qh := (tr_Qh_eq e).symm

theorem isExtraspecial_Q : CFSG.IsExtraspecialPGroup 2 ↥(tr e L52.Qh) :=
  CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
    (Subgroup.equivMapOfInjective L52.Qh (emb e) (emb_injective e))
    L52.isExtraspecialPGroup_Qh

theorem centerIn_Q (hz : orderOf z = 2) : centerIn (tr e L52.Qh) = zpowers z := by
  have h : tr e (L52.Qh ⊓ centralizer (L52.Qh : Set L52.Hc)) = centerIn (tr e L52.Qh) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyQ, hyc⟩, rfl⟩
      refine ⟨emb_mem_tr e hyQ, mem_centralizer_iff.mpr fun w hw => ?_⟩
      obtain ⟨w', hw', rfl⟩ := hw
      exact (emb_mul_comm e).2 (mem_centralizer_iff.mp hyc w' hw')
    · rintro ⟨⟨y, hyQ, rfl⟩, hc⟩
      refine ⟨y, ⟨hyQ, mem_centralizer_iff.mpr fun w hw => ?_⟩, rfl⟩
      have := mem_centralizer_iff.mp hc (emb e w) (emb_mem_tr e hw)
      exact (emb_mul_comm e).1 this
  rw [← h, L52.inf_centralizer_Qh, tr_zpowers_zt e hz]

theorem nonempty_iso_cornerTransvection {z' : G} (e' : ↥(Cz z') ≃* L52.Hc) :
    Nonempty (↥(Cz z') ≃*
      ↥(centralizer ({CFSG.LargeExtraspecial.DW.cornerTransvection (N := 5) (by norm_num)} :
        Set (SL(5, ZMod 2))))) :=
  ⟨e'⟩

end CFSG.Quasithin.A94.HeK
