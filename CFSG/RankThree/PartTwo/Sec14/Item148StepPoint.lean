module

public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] noncomputable def Item142AllS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A

@[expose] noncomputable def Item143NAllS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item143N A (lB A)

@[expose] def Step148PointOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, Subgroup.zpowers b ∈ omegaA A → ∀ Lb ∈ lA A b,
        Q ≤ Lb ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers b : Set G)) →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        ∃ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)),
          K = deltaZero A (lB A) K ∧ K ≤ Lb

@[expose] noncomputable def HJConfig143 {G : Type} [Group G] [Finite G] (A : Subgroup G) (b : G) :
    Prop :=
  ∃ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A ∧ Lb ∈ lA A b' ∧
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn Lb d ∧ b ∈ Subgroup.closure {b', d} ∧
    ∃ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X ∧
      Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) ∧
      ((X ∈ thetaComponentsAt 3 b ∧
          X = lB A (Subgroup.closure {b, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
          Subgroup.zpowers b ≠ Subgroup.zpowers d) ∨
        (Subgroup.zpowers b = Subgroup.zpowers d ∧
          (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
          (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              CFSG.Blueprint.NativeSporadic.ON ∨
            Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              (alternatingGroup (Fin 6)) ∨
            IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))))

@[expose] noncomputable def Step148PointHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        HJConfig143 A b →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_le148 {M C A : Subgroup G} (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hCM : C ≤ Subgroup.normalizer (M : Set G))
    (hCA : C ≤ Subgroup.centralizer (A : Set G)) : ⁅M ⊔ C, A⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro g hg a ha
  have hg' : g ∈ ((M : Set G) * (C : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M C hCM]
    exact hg
  obtain ⟨m, hm, k, hk, rfl⟩ := hg'
  have hka : k * a = a * k := (Subgroup.mem_centralizer_iff.mp (hCA hk) a ha).symm
  have key : ⁅m * k, a⁆ = m * (a * m⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc m * k * a * (m * k)⁻¹ * a⁻¹ = m * (k * a) * k⁻¹ * m⁻¹ * a⁻¹ := by group
      _ = m * (a * k) * k⁻¹ * m⁻¹ * a⁻¹ := by rw [hka]
      _ = m * (a * m⁻¹ * a⁻¹) := by group
  rw [key]
  exact M.mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hAM ha) _).mp (M.inv_mem hm))

omit [Finite G] in
theorem inf_le_pPrimeCoreOf148 {N X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hN : Nat.Coprime 3 (Nat.card N)) : N ⊓ X ≤ pPrimeCoreOf 3 X :=
  le_pPrimeCoreOf inf_le_right (fun _ hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hXN hx, Subgroup.le_normalizer hx⟩)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hN)

omit [Finite G] in
theorem centralizer_zpowers148 (b : G) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem three_dvd_card_of_types148 {L : Subgroup G}
    (hT : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    3 ∣ Nat.card L := by
  rcases hT with ⟨⟨φ⟩⟩ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  · have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
    exact (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi he hiso).trans h1
  · exact three_dvd_card_of_thetaQuot φ
      (by rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]; norm_num)
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeM12]; norm_num)

theorem exists_isPoint148_of (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (hΩ : Step148PointOmega) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h143 : Item143N A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B : Subgroup G}
    (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)))
    (hHJ : Subgroup.zpowers b ∉ omegaA A → HJConfig143 A b →
      ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le) :
    ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le := by
  have hD := h.toSec13Data
  have hAc : IsMulCommutative A := hD.isElemAbelian.1
  have hbA : b ∈ A := hB.1 hb
  have hQB : Q ≤ Subgroup.centralizer (B : Set G) := hQY.trans inf_le_right
  have hQb' : Q ≤ Subgroup.centralizer ({b} : Set G) :=
    hQB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hQA : Q = ⁅Q, A⁆ := hQ.2
  have hQinv : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) := hQ.1.1
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  have hcontra : ∀ N : Subgroup G, Nat.Coprime 3 (Nat.card N) →
      Y ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (N : Set G) → Q ≤ N → False := by
    intro N hN hYN hQN
    exact hQb ((le_inf hQN (hQY.trans (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hb))))).trans (inf_le_pPrimeCoreOf148 hYN hN))
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  ·
    obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
      hD.card_eq hbΩ
    have hLbA : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb
    have hS : Sec14Std G A b Lb := { h with zpowers_mem_omegaA := hbΩ, mem_lA := hLbA }
    set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHdef
    have hCH : Subgroup.centralizer ({b} : Set G) ≤ H := by
      rw [← centralizer_zpowers148]
      exact Subgroup.centralizer_le_normalizer _
    have hQH : Q ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hQb'.trans hCH, hQinv.2.1, hQinv.2.2⟩
    obtain ⟨Qs, hQs, hQQs⟩ := exists_le_mem_maxInvariantPiSubgroups hQH
    obtain ⟨hQsmem, halt⟩ := h142 G A b Lb hS Qs hQs
    have hAH : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (hAb.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    have hYH : Y ⊓ Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (inf_le_right.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    rcases halt with ⟨-, hQsK, hOK, hcard⟩ | ⟨hK, -⟩
    ·
      exfalso
      rw [← hHdef] at hOK hcard
      set K := k142 A (lB A) b with hKdef
      have hidx : ((pPrimeCoreOf 3 H).subgroupOf K).index = 2 := by
        have h1 := Subgroup.card_mul_index ((pPrimeCoreOf 3 H).subgroupOf K)
        have h2 : Nat.card ↥((pPrimeCoreOf 3 H).subgroupOf K) = Nat.card (pPrimeCoreOf 3 H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
        rw [h2, hcard] at h1
        have hpos : 0 < Nat.card (pPrimeCoreOf 3 H) := Nat.card_pos
        have h3 : Nat.card (pPrimeCoreOf 3 H) * ((pPrimeCoreOf 3 H).subgroupOf K).index =
            Nat.card (pPrimeCoreOf 3 H) * 2 := by rw [h1, mul_comm]
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q' hQ' =>
        hQ'.1.1.2.2
      have hQK : Q ≤ K := hQQs.trans (hQsK ▸ le_rfl)
      refine hcontra (pPrimeCoreOf 3 H) (coprime_card_pPrimeCoreOf 3 H) hYH ?_
      rw [hQA, Subgroup.commutator_le]
      intro x hx a ha
      have hxK : x ∈ K := hQK hx
      have hax : a * x⁻¹ * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAK ha) _).mp (K.inv_mem hxK)
      have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hxK⟩)
        (b := ⟨a * x⁻¹ * a⁻¹, hax⟩)).mpr ?_
      · rw [Subgroup.mem_subgroupOf] at hmem
        rw [commutatorElement_def]
        simpa [mul_assoc] using hmem
      · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        constructor
        · intro hx'
          exact (Subgroup.mem_normalizer_iff.mp (hAH ha) _).mp ((pPrimeCoreOf 3 H).inv_mem hx')
        · intro hax'
          have := (Subgroup.mem_normalizer_iff.mp (hAH (A.inv_mem ha)) _).mp hax'
          simpa [mul_assoc] using this
    ·
      have hQsK : Qs ≤ k142 A (lB A) b := le_delta hQsmem.1 (hQsmem.2.trans hCH)
      have hLbN : A ≤ Subgroup.normalizer (Lb : Set G) := hLbA.2.1
      have h3 : 3 ∣ Nat.card Lb := three_dvd_card_of_types148 (h.chosen136.2 b hbΩ Lb hLbA).1
      have hCLb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Lb : Set G) :=
        centralizer_le_normalizer_of_three_dvd hS h3
      have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
      have hLbH : Lb ≤ H := (le_centralizer_of_mem_thetaComponentsAt hLbA.1).trans hCH
      have hM : A ≤ Subgroup.normalizer
          ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) :=
        le_normalizer_sup (A := A) hLbN hAH
      have hCM : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer
          ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) := by
        have h1 : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
            Subgroup.centralizer ({b} : Set G) := (pPrimeCoreOf_le 3 _).trans hCA
        exact le_normalizer_sup (A := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
          (h1.trans hCLb) ((h1.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H))
      have hQLb : Q ≤ Lb ⊔ pPrimeCoreOf 3 H := by
        rw [hQA]
        refine (Subgroup.commutator_mono (hQQs.trans (hQsK.trans hK.le)) le_rfl).trans ?_
        exact commutator_sup_le148 hM hCM (pPrimeCoreOf_le 3 _)
      obtain ⟨K, hK', hKΔ, hKLb⟩ :=
        hΩ G A c L h Y hY hs hYB B hB Q hQ hQY b hb hbΩ Lb hLbA hQLb hQb
      exact ⟨b, K, Lb, hB, hQ, hQY, hb, hb1, hK', hKΔ, hKLb, hLbA.1, Or.inl ⟨hbΩ, hLbA⟩⟩
  ·
    obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
      (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3)
    obtain ⟨-, halt⟩ := h143 b hbA hb1 hbΩ Qs hQs
    rcases halt with h1 | h2
    ·
      exfalso
      have hQΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hQ.1 hQb'
      have hcomm := commutator_sup_le_pPrimeCoreOf hAc (Subgroup.zpowers_le.mpr hbA)
      rw [centralizer_zpowers148] at hcomm
      refine hcontra (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
        (coprime_card_pPrimeCoreOf 3 _)
        (inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 _)) ?_
      rw [hQA]
      exact (Subgroup.commutator_mono (hQΔ.trans h1.le) le_rfl).trans hcomm
    · exact hHJ hbΩ h2


theorem step148Point_of (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NAllS14) (hΩ : Step148PointOmega) (hHJ : Step148PointHJ) : Step148Point := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hQb
  exact exists_isPoint148_of h422 h45 h142 hΩ h (h143 G A c L h) hY hs hYB hB hQ hQY hb hb1 hQb
    fun hbΩ h2 => hHJ G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb h2

theorem exists_isPoint148_of_not_allPointsHJ (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (hΩ : Step148PointOmega) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hNHJ : ¬ AllPointsHJ A) (h143 : Item143N A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B : Subgroup G}
    (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le := by
  refine exists_isPoint148_of h422 h45 h142 hΩ h h143 hY hs hYB hB hQ hQY hb hb1 hQb
    fun _ h2 => ?_
  obtain ⟨b', d, Lb, hb', hLb, hJ, hdA, hd1, hdc, -⟩ := h2
  exact (hNHJ fun e he => exists_hj_of_hj_point h134 h48 h415 h hb' hLb hJ hdA hd1 hdc he).elim

end CFSG.RankThree.PartTwo.Sec14
