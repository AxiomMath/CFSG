module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
import CFSG.CGT.PushingUpLit.C2L.TameBridge
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

private theorem not_three_dvd_delta_normalizer (h : Ctx A c L d) {T₀ : Subgroup G}
    (hT₀Q : T₀ ∈ scriptQ A (lB A))
    (h1 : Case148One A (lB A) (Subgroup.normalizer (T₀ : Set G))) :
    ¬ 3 ∣ Nat.card ↥(delta A (lB A) (Subgroup.normalizer (T₀ : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := Subgroup.normalizer (T₀ : Set G) with hY
  set O' : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  set OY : Subgroup G := pPrimeCoreOf 3 Y with hOY
  set Z : Subgroup G := (O' ⊓ Y) ⊔ OY with hZ
  have hS14 : Sec14Std G A c L := h.conf.sec15R.toSec14Std
  have hA : Late.IsE27 A := h.isE27
  have hAmax := hS14.maximal_isElemAbelian
  have hANT : A ≤ Subgroup.normalizer (T₀ : Set G) := (mem_scriptQ_iff.mp hT₀Q).2.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.normalizer (T₀ : Set G)).map (MulAut.conj a).toMonoidHom =
      Subgroup.normalizer (T₀ : Set G)
    rw [Subgroup.map_equiv_normalizer_eq T₀ (MulAut.conj a),
      Late.map_conj_eq_of_mem_normalizer (hANT ha)]
  have hAOY : A ≤ Subgroup.normalizer (OY : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hAO' : A ≤ Subgroup.normalizer (O' : Set G) := by
    have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
    exact hAC.trans ((Subgroup.le_normalizer (H := Subgroup.centralizer (A : Set G))).trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))))
  have hAO'Y : A ≤ Subgroup.normalizer ((O' ⊓ Y : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAO' hAY
  have hO'3 : ¬ 3 ∣ Nat.card O' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hOY3 : ¬ 3 ∣ Nat.card OY :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hO'Y_norm : O' ⊓ Y ≤ Subgroup.normalizer (OY : Set G) :=
    (inf_le_right.trans (Subgroup.le_normalizer (H := Y))).trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hO'Y3 : ¬ 3 ∣ Nat.card ↥(O' ⊓ Y) :=
    fun h => hO'3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hZ3 : ¬ 3 ∣ Nat.card Z := by
    rw [hZ]
    exact Sec6.not_dvd_card_sup Nat.prime_three hO'Y_norm hO'Y3 hOY3
  have hQZ : ∀ Q : Subgroup G, Q ∈ scriptQ A (lB A) → Q ≤ Y → Q ≤ Z := by
    intro Q hQ hQY
    obtain ⟨hQpi, hAQ, -⟩ := mem_scriptQ_iff.mp hQ
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQpi
    have hcommQ : ⁅Q, A⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Q, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Q
    have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
      3 Nat.prime_three A Q hA.isPGroup hQ3 hAQ
    have hcommQ0 : ⁅Q, A⁆ ∈ scriptQZero A (lB A) :=
      ⟨mem_scriptQ_of_le hQ hcommQ hAcomm, hidem.symm⟩
    have hcommO : ⁅Q, A⁆ ≤ OY :=
      (le_deltaZero hcommQ0 (hcommQ.trans hQY)).trans h1
    have hCA : Q ⊓ Subgroup.centralizer (A : Set G) ≤ O' :=
      inf_centralizer_le_xA hAmax hQ3
    have hCAY : Q ⊓ Subgroup.centralizer (A : Set G) ≤ O' ⊓ Y :=
      le_inf hCA (inf_le_left.trans hQY)
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A Q hA.isPGroup hQ3 hAQ, hZ]
    exact sup_le (hcommO.trans le_sup_right) (hCAY.trans le_sup_left)
  have hDZ : delta A (lB A) Y ≤ Z := by
    unfold delta
    exact sSup_le fun Q hQ => hQZ Q hQ.1 hQ.2
  exact fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le hDZ))

theorem mem_star_of_case1 (h146 : Item146 A (lB A)) (h : Ctx A c L d) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    {T T₀ : Subgroup G} (hT₀2 : IsPGroup 2 ↥T₀) (hT₀Q : T₀ ∈ scriptQ A (lB A))
    (hTT₀ : T ≤ T₀) (hgT₀ : g ∈ Subgroup.normalizer (T₀ : Set G))
    (hmax : ∀ T' : Subgroup G, IsPGroup 2 ↥T' → T' ∈ scriptQ A (lB A) → T ≤ T' →
      g ∈ Subgroup.normalizer (T' : Set G) → Nat.card T' ≤ Nat.card T₀)
    (h1 : Case148One A (lB A) (Subgroup.normalizer (T₀ : Set G))) :
    T₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := Subgroup.normalizer (T₀ : Set G) with hY
  have hT₀pi : T₀ ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hT₀Q, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two T₀).mpr hT₀2⟩
  refine ⟨hT₀pi, fun S hS hT₀S => ?_⟩
  by_contra hnot
  have hT₀Slt : T₀ < S := lt_of_le_of_ne hT₀S fun hEq => hnot (le_of_eq hEq.symm)
  have hS2 : IsPGroup 2 ↥S := isPGroup_of_mem_scriptQPi Nat.prime_two hS
  have hSQ : S ∈ scriptQ A (lB A) := hS.1.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hSQ).2.1
  have hANT : A ≤ Subgroup.normalizer (T₀ : Set G) := (mem_scriptQ_iff.mp hT₀Q).2.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.normalizer (T₀ : Set G)).map (MulAut.conj a).toMonoidHom =
      Subgroup.normalizer (T₀ : Set G)
    rw [Subgroup.map_equiv_normalizer_eq T₀ (MulAut.conj a),
      Late.map_conj_eq_of_mem_normalizer (hANT ha)]
  set T₁ : Subgroup G := S ⊓ Y with hT₁
  have hT₁lt : T₀ < T₁ := CFSG.CGT.PushingUpLit.C2L.Tame.lt_inf_normalizer_of_lt hS2 hT₀Slt
  have hT₁A : A ≤ Subgroup.normalizer (T₁ : Set G) := Late.le_normalizer_inf hAS hAY
  have hT₁Q : T₁ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hSQ inf_le_left hT₁A
  have hT₁2 : IsPGroup 2 ↥T₁ := hS2.to_le inf_le_left
  have hT₁D : T₁ ≤ delta A (lB A) Y := le_delta hT₁Q inf_le_right
  have hD3 : ¬ 3 ∣ Nat.card ↥(delta A (lB A) Y) := not_three_dvd_delta_normalizer h hT₀Q h1
  have hDQ : delta A (lB A) Y ∈ scriptQ A (lB A) :=
    Sec16.Proof165.delta_mem_scriptQ_of_three h.isE27 h146 Y hD3
  have hAD : A ≤ Subgroup.normalizer (delta A (lB A) Y : Set G) := le_normalizer_delta Y
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.normalizer (T₀ : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (T₀ : Set G)
    rw [Subgroup.map_equiv_normalizer_eq T₀ (MulAut.conj g),
      Late.map_conj_eq_of_mem_normalizer hgT₀]
  have hgD : g ∈ Subgroup.normalizer (delta A (lB A) Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (delta A (lB A) Y).map (MulAut.conj g).toMonoidHom = delta A (lB A) Y
    have hmap : Y.map (MulAut.conj g).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgY
    rw [Sec17.HeadProof.map_conj_delta hgA Y, hmap]
  set P : Subgroup G := A ⊔ Subgroup.zpowers g with hP
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hzg3 : IsPGroup 3 (Subgroup.zpowers g) := by
    obtain ⟨k, hk⟩ := hg3
    exact isPGroup_iff_card_dvd_pow.mpr ⟨k, by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk⟩
  have hP3 : IsPGroup 3 ↥P := by
    rw [hP]
    exact IsPGroup.to_sup_of_normal_left' hA3 hzg3 (Subgroup.zpowers_le.mpr hgA)
  have hAP : A ≤ P := by rw [hP]; exact le_sup_left
  have hgP : g ∈ P := by
    rw [hP]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hPD : P ≤ Subgroup.normalizer (delta A (lB A) Y : Set G) := by
    rw [hP]
    exact sup_le hAD (Subgroup.zpowers_le.mpr hgD)
  have hPT : P ≤ Subgroup.normalizer (T₀ : Set G) := by
    rw [hP]
    exact sup_le hANT (Subgroup.zpowers_le.mpr hgT₀)
  have hT₀D : T₀ ≤ delta A (lB A) Y := le_delta hT₀Q (Subgroup.le_normalizer (H := T₀))
  obtain ⟨Q₁, hT₀Q₁, hQ₁D, hQ₁2, hQ₁rel, hPQ₁⟩ :=
    HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.exists_invariant_sylow_containing_of_pGroup
      Nat.prime_three Nat.prime_two hP3 hPD hD3 hT₀D hT₀2 hPT
  have hQ₁Q : Q₁ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hDQ hQ₁D (hAP.trans hPQ₁)
  have hTQ₁ : T ≤ Q₁ := hTT₀.trans hT₀Q₁
  have hgQ₁ : g ∈ Subgroup.normalizer (Q₁ : Set G) := hPQ₁ hgP
  have hQ₁syl : CFSG.ABGLocalTools.IsSylowOf 2 Q₁ (delta A (lB A) Y) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQ₁D, hQ₁2, hQ₁rel⟩
  have hcardle : Nat.card T₁ ≤ Nat.card Q₁ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_card_le hQ₁syl hT₁2 hT₁D
  have hcard : Nat.card T₀ < Nat.card Q₁ :=
    lt_of_lt_of_le (Subgroup.card_lt_of_lt hT₁lt) hcardle
  exact (not_le_of_gt hcard) (hmax Q₁ hQ₁2 hQ₁Q hTQ₁ hgQ₁)

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
