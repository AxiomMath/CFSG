module

public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159
public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.Sporadic.HeldB.Common
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate7233Base
import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof15Res3W

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ h : G, h ∈ Subgroup.normalizer (D : Set G) → ∀ y : G,
      y ∈ Subgroup.centralizer (D : Set G) → h * y * h⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    intro h hh y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro d hd
    have hd' : h⁻¹ * d * h⁻¹⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) d).mp hd
    have := hy _ hd'
    calc d * (h * y * h⁻¹) = h * ((h⁻¹ * d * h⁻¹⁻¹) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * d * h⁻¹⁻¹)) * h⁻¹ := by rw [this]
      _ = h * y * h⁻¹ * d := by group
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem centralizer_inf_le_of_ne {A D D' : Subgroup G} (hD : IsHyperplane A D)
    (hD' : IsHyperplane A D') (hne : D ≠ D') :
    Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (D' : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  have h3 : Nat.card A = 3 * Nat.card D := hD.2
  have h3' : Nat.card A = 3 * Nat.card D' := hD'.2
  have hDD : Nat.card D = Nat.card D' := by omega
  have hsup : D ⊔ D' = A := by
    have hle : D ⊔ D' ≤ A := sup_le hD.1 hD'.1
    have hlt : D < D ⊔ D' := by
      refine lt_of_le_of_ne le_sup_left fun h => hne ?_
      have hD'D : D' ≤ D := h ▸ le_sup_right
      exact (Subgroup.eq_of_le_of_card_ge hD'D hDD.le).symm
    have hdvd1 : Nat.card D ∣ Nat.card (D ⊔ D' : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
    have hdvd2 : Nat.card (D ⊔ D' : Subgroup G) ∣ Nat.card A := Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk⟩ := hdvd1
    have hpos : 0 < Nat.card D := Nat.card_pos
    have hk1 : 1 < k := by
      have := Subgroup.card_lt_of_lt hlt
      rw [hk] at this
      by_contra hk1
      push Not at hk1
      interval_cases k <;> simp_all
    have hkd : k ∣ 3 := by
      rw [hk, h3, mul_comm 3] at hdvd2
      exact (Nat.mul_dvd_mul_iff_left hpos).mp hdvd2
    have hk3 : k = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hkd with h | h
      · omega
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hk3, h3, mul_comm])
  rw [← hsup]
  exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp inf_le_left)
    (Subgroup.le_centralizer_iff.mp inf_le_right))

theorem sup_pPrimeCoreOf_mem_scriptQ {A D : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hAab : IsMulCommutative A) (hD : IsHyperplane A D) :
    pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) with hX
  set Y := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hY
  have hCAD : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hD.1
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  have hCX : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    hCAD.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hCY : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := (pPrimeCoreOf_le 3 _).trans hCX
  have hpi : ∀ Z : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 Z) := fun Z =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Z))
  have hJpi : IsPiSubgroup (piCompl 3) (X ⊔ Y) := by
    rw [sup_comm]
    exact isPiSubgroup_piCompl_sup (hpi _) (hpi _) hYX
  have hCJ : Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) :=
    le_normalizer_sup hCX hCY
  have hJD : X ⊔ Y ≤ Subgroup.centralizer (D : Set G) :=
    sup_le (pPrimeCoreOf_le 3 _) ((pPrimeCoreOf_le 3 _).trans hCAD)
  refine ⟨⟨le_top, hJpi, hAC.trans hCJ⟩, fun D' hD' => ?_⟩
  by_cases hDD : D' = D
  · subst hDD
    exact inf_le_left.trans (le_sup_left : X ⊔ Y ≤ qBound A LB D')
  ·
    have hle : (X ⊔ Y) ⊓ Subgroup.centralizer (D' : Set G) ≤
        (X ⊔ Y) ⊓ Subgroup.centralizer (A : Set G) := by
      refine le_inf inf_le_left ?_
      have := centralizer_inf_le_of_ne hD hD' (Ne.symm hDD)
      exact (le_inf (inf_le_left.trans hJD) inf_le_right).trans this
    have hcop :
        Nat.Coprime 3 (Nat.card ((X ⊔ Y) ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
      exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hJpi
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hY' : (X ⊔ Y) ⊓ Subgroup.centralizer (A : Set G) ≤ Y :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hCJ Subgroup.le_normalizer) hcop
    have hYq : Y ≤ qBound A LB D' := by
      unfold qBound
      exact le_sup_right.trans le_sup_left
    exact hle.trans (hY'.trans hYq)

omit [Finite G] in
theorem le_normalizer_map_conj {A X : Subgroup G} {g : G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)]
  conv_lhs => rw [← map_conj_eq_of_mem_normalizer hg]
  exact Subgroup.map_mono hAX

section Ctx

theorem eq_sup_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) :
    c ∉ A ⊓ L ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hcL : c ∉ L := ctx.hypS.2.2 c ctx.zpowers_mem_omegaA L ctx.mem_lA
  exact ⟨fun hc => hcL hc.2, eq_sup_of_card_nine ctx.toSec13Data ctx.card_inf fun hc => hcL hc.2⟩

theorem not_le_normalizer_zpowers_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro hle
  have h := ctx.ncard_omegaA
  rw [ctx.omegaA_eq, Proof1511.orbitIn_eq_singleton hle, Set.ncard_singleton] at h
  norm_num at h

theorem exists_transv_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) {b : G}
    (hb : b ∈ A ⊓ L) : ∃ (w : G) (hw : w ∈ Subgroup.normalizer (A : Set G)),
      A.normalizerMonoidHom ⟨w, hw⟩ ∈ transvAxis A (A ⊓ L) ∧ w * c * w⁻¹ = c * b := by
  have hD := ctx.toSec13Data
  obtain ⟨-, hAa⟩ := eq_sup_of_ctx159 ctx
  refine exists_transv_of_irreducible (K := L ⊓ Subgroup.normalizer (A : Set G))
    hD.isElemAbelian hD.mem_A hAa ctx.card_inf (fun k hk => ?_) ctx.irreducible inf_le_right
    (Late.le_normalizer_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer))
    ctx.normalizer_le_inf (not_le_normalizer_zpowers_of_ctx159 ctx) hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk.1)

theorem isEmpty_j2_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) {b : G}
    (hb : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun φ => ?_⟩
  rw [ctx.omegaA_eq] at hb
  obtain ⟨x, hx, hbx⟩ := hb
  rw [MonoidHom.map_zpowers] at hbx
  have hbx' : Subgroup.zpowers b = Subgroup.zpowers (x * c * x⁻¹) := hbx
  have hLb' : Lb ∈ lA A (x * c * x⁻¹) := by
    rw [← lA_eq_of_zpowers_eq hbx']
    exact hLb
  have hLc : Lb.map (MulAut.conj x⁻¹).toMonoidHom ∈ lA A c := by
    have := (map_conj_mem_lA_iff (inv_mem hx)).mpr hLb'
    rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at this
  have h3 : 3 ∣ Nat.card (Lb.map (MulAut.conj x⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Lb)
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
    exact (show 3 ∣ 604800 by norm_num).trans h1
  have heq : Lb.map (MulAut.conj x⁻¹).toMonoidHom = L :=
    (ctx.chosen136.2 c ctx.zpowers_mem_omegaA L ctx.mem_lA).2 _ hLc.1 h3
  have ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2 := by
    have e := thetaQuotEquiv (MulAut.conj x⁻¹) Lb
    rw [heq] at e
    exact e.symm.trans φ
  obtain ⟨hJL, hJA, hJM⟩ := KFacts.KS14.ks17J2NotList
  rcases ctx.types with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
  · exact hJL p e (Proof1511.isoLThreePi_of_mulEquiv ψ hL3)
  · exact hJA.false (ψ.symm.trans χ)
  · exact hJM.false (ψ.symm.trans χ)

theorem lB_eq_bot_of_ctx159
    {A L : Subgroup G} {c : G}
    (ctx : Ctx159 G A c L) (D : Subgroup G) : lB A D = ⊥ :=
  lB_eq_bot fun _ _ Lb hc => (isEmpty_j2_of_ctx159 ctx hc.2.1
    (hc.2.2.1 ▸ Set.mem_singleton Lb)).false (Item148HJ.j2_of_isLBConfig hc).some

theorem exists_faithful_two_group {A L : Subgroup G} {c : G} (h : Sec15R G A c L) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      ∀ b ∈ A, b ∈ Subgroup.centralizer (Q : Set G) → b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSD := h.toSec13Data
  obtain ⟨hAe, -, U, hU1, hU2, hAU⟩ := hSD.mem_partTwoE
  set M := Subgroup.normalizer (U : Set G) with hM
  set Q := (CFSG.pCore 2 ↥M).map M.subtype with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAU.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥M)))
  have hchar := h.toTheoremFourHyp.charTwoType M ⟨U, hU1, hU2, rfl⟩
  have hQeq : CFSG.Assembly.pCoreOf 2 M = Q := by
    unfold CFSG.Assembly.pCoreOf
    try with_reducible rfl
  rw [hQeq] at hchar
  refine ⟨Q, hQ2, hAQ, fun b hbA hbC => ?_⟩
  have hbQ : b ∈ Q := hchar ⟨hAU hbA, hbC⟩
  obtain ⟨k, hk⟩ := hQ2 ⟨b, hbQ⟩
  have hk' : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf b ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one (hAe.2 b hbA))
  have h2 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem exists_hyperplane_commutator_ne_bot {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    ∃ Q D : Subgroup G, IsPGroup 2 Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      IsHyperplane A D ∧ ⁅Q ⊓ Subgroup.centralizer (D : Set G), A ⊓ L⁆ ≠ ⊥ := by
  have hSD := h.toSec13Data
  obtain ⟨hAe, hA27, -⟩ := hSD.mem_partTwoE
  obtain ⟨Q, hQ2, hAQ, hfaith⟩ := exists_faithful_two_group h
  by_contra hno
  push Not at hno
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hQB : Q ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hAe
      (by rw [hA27]; norm_num) hAQ hcop fun H hHA hH9 => ?_
    have hHyp : IsHyperplane A H := ⟨hHA, by rw [hA27, hH9]; norm_num⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (hno Q H hQ2 hAQ hHyp)
  have hB1 : A ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    exact hfaith b hb.1 (Subgroup.le_centralizer_iff.mp hQB hb)
  rw [hB1, Subgroup.card_bot] at h9
  norm_num at h9

theorem exists_hyperplane_mem_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) :
    ∃ Q D : Subgroup G, IsPGroup 2 Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      IsHyperplane A D ∧ D ≠ A ⊓ L ∧ c ∈ D ∧
      ⁅Q ⊓ Subgroup.centralizer (D : Set G), A ⊓ L⁆ ≠ ⊥ := by
  have hSD := ctx.toSec13Data
  have hAe := hSD.isElemAbelian
  obtain ⟨-, hAa⟩ := eq_sup_of_ctx159 ctx
  obtain ⟨Q, D, hQ2, hAQ, hDh, hQD⟩ :=
    exists_hyperplane_commutator_ne_bot ctx.toSec15R ctx.card_inf
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hDB : D ≠ A ⊓ L := by
    rintro rfl
    exact hQD ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr inf_le_right)
  have hDB' : ¬ D ≤ A ⊓ L := fun hle => hDB (Subgroup.eq_of_le_of_card_ge hle (by
      have h1 := hDh.2
      rw [hSD.card_eq] at h1
      rw [ctx.card_inf]
      omega))
  obtain ⟨y, hyD, hyB⟩ := Set.not_subset.mp hDB'
  obtain ⟨i, hi, b, hb, hyb⟩ := exists_pow_mul_of_mem hAe hSD.mem_A hAa (hDh.1 hyD)
  have hc3 : c ^ 3 = 1 := hAe.2 c hSD.mem_A
  obtain ⟨b', hb', hcbD⟩ : ∃ b' ∈ A ⊓ L, c * b' ∈ D := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact absurd (by rw [hyb, pow_zero, one_mul]; exact hb) hyB
    · exact ⟨b, hb, by rw [hyb, pow_one] at hyD; exact hyD⟩
    · refine ⟨b ^ 2, Subgroup.pow_mem _ hb 2, ?_⟩
      have hy2 : y ^ 2 = c * b ^ 2 := by
        have hcb : Commute (c ^ 2) b :=
          Commute.pow_left (hcomm c hSD.mem_A b hb.1) 2
        rw [hyb, hcb.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul]
      rw [← hy2]
      exact Subgroup.pow_mem _ hyD 2
  obtain ⟨x, hx, -, hxc⟩ := exists_transv_of_ctx159 ctx hb'
  have hBx : (A ⊓ L).map (MulAut.conj x⁻¹).toMonoidHom = A ⊓ L :=
    map_conj_eq_of_mem_normalizer (ctx.normalizer_le_inf (inv_mem hx))
  refine ⟨Q.map (MulAut.conj x⁻¹).toMonoidHom, D.map (MulAut.conj x⁻¹).toMonoidHom,
    hQ2.map _, le_normalizer_map_conj hAQ (inv_mem hx), hDh.map_conj (inv_mem hx), ?_,
    ⟨c * b', hcbD, ?_⟩, ?_⟩
  · intro heq
    apply hDB
    have h1 : (D.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = D := by
      rw [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
    rw [heq, map_conj_eq_of_mem_normalizer (ctx.normalizer_le_inf hx)] at h1
    exact h1.symm
  · show x⁻¹ * (c * b') * x⁻¹⁻¹ = c
    rw [← hxc]
    group
  · rw [← map_conj_centralizer, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective, ← hBx,
      ← Subgroup.map_commutator]
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x⁻¹).injective]

theorem mem_scriptQ_of_le_centralizer (h142 : Item142R) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hPc : P ≤ Subgroup.centralizer ({c} : Set G)) : P ∈ scriptQ A (lB A) := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hPH : P ≤ H := hPc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have h3 : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hinv : P ∈ invariantPiSubgroups H A (piCompl 3) :=
    (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mpr ⟨hPH, h3, hAP⟩
  obtain ⟨Q, hPQ, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hinv
  let := ker142_normal (LB := lB A) h.isElemAbelian.1 h.mem_A
  obtain ⟨hQq, -⟩ := h142 G A c L h Q hQ
  exact mem_scriptQ_of_le hQq.1 hPQ hAP

theorem exists_isW159_mem_normalizer {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L)
    {D : Subgroup G} (hD : IsHyperplane A D) (hcD : c ∈ D) :
    ∃ w : G, IsW159 A L w ∧ w ∈ Subgroup.normalizer (D : Set G) := by
  have hSD := ctx.toSec13Data
  have hAe := hSD.isElemAbelian
  obtain ⟨-, hAa⟩ := eq_sup_of_ctx159 ctx
  have hD9 : Nat.card D = 9 := by
    have := hD.2
    rw [hSD.card_eq] at this
    omega
  have hmemD : ∀ d ∈ D, ∀ i : ℕ, ∀ b : G, d = c ^ i * b → b ∈ D := by
    intro d hdD i b hdb
    have : b = (c ^ i)⁻¹ * d := by rw [hdb]; group
    rw [this]
    exact D.mul_mem (D.inv_mem (D.pow_mem hcD i)) hdD
  obtain ⟨v, hvD, hvB, hv1⟩ : ∃ v ∈ D, v ∈ A ⊓ L ∧ v ≠ 1 := by
    have hDc : ¬ D ≤ Subgroup.zpowers c := fun hle => by
      have := Subgroup.card_le_of_le hle
      rw [hD9, hSD.card_zpowers] at this
      omega
    obtain ⟨d, hdD, hdc⟩ := Set.not_subset.mp hDc
    obtain ⟨i, -, b, hb, hdb⟩ := exists_pow_mul_of_mem hAe hSD.mem_A hAa (hD.1 hdD)
    refine ⟨b, hmemD d hdD i b hdb, hb, fun hb1 => hdc ?_⟩
    rw [hdb, hb1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
  obtain ⟨w₀, hw₀A, hT, hw₀c⟩ := exists_transv_of_ctx159 ctx hvB
  have hfix : ∀ b ∈ A ⊓ L, w₀ * b * w₀⁻¹ = b := fun b hb =>
    congrArg Subtype.val (hT.1 ⟨b, hb.1⟩ hb)
  have hw₀D : w₀ ∈ Subgroup.normalizer (D : Set G) := by
    have hle : D.map (MulAut.conj w₀).toMonoidHom ≤ D := by
      rintro _ ⟨d, hdD, rfl⟩
      obtain ⟨i, -, b, hb, hdb⟩ := exists_pow_mul_of_mem hAe hSD.mem_A hAa (hD.1 hdD)
      show w₀ * d * w₀⁻¹ ∈ D
      rw [hdb, show w₀ * (c ^ i * b) * w₀⁻¹ = (w₀ * c ^ i * w₀⁻¹) * (w₀ * b * w₀⁻¹) by group,
        ← conj_pow, hw₀c, hfix b hb]
      exact D.mul_mem (D.pow_mem (D.mul_mem hcD hvD) i) (hmemD d hdD i b hdb)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj w₀).injective]))
  obtain ⟨k, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w₀).ne' 3
    (by norm_num)
  have hconj : ∀ j : ℕ, w₀ ^ j * c * (w₀ ^ j)⁻¹ = c * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc w₀ ^ (j + 1) * c * (w₀ ^ (j + 1))⁻¹ = w₀ * (w₀ ^ j * c * (w₀ ^ j)⁻¹) * w₀⁻¹ := by
            group
        _ = (w₀ * c * w₀⁻¹) * (w₀ * v * w₀⁻¹) ^ j := by rw [ih, conj_pow]; group
        _ = c * v ^ (j + 1) := by rw [hw₀c, hfix v hvB, pow_succ']; group
  refine ⟨w₀ ^ m, ⟨Subgroup.pow_mem _ hw₀A m, ⟨k, ?_⟩, fun b hb => ?_, fun hC => ?_⟩,
    Subgroup.pow_mem _ hw₀D m⟩
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  · have hcb : Commute w₀ b := mul_inv_eq_iff_eq_mul.mp (hfix b hb)
    exact (hcb.pow_left m).eq
  ·
    have hc := (Subgroup.mem_centralizer_iff.mp hC) c hSD.mem_A
    have h1 : w₀ ^ m * c * (w₀ ^ m)⁻¹ = c := by rw [← hc, mul_inv_cancel_right]
    rw [hconj m, mul_eq_left] at h1
    have hv3 : orderOf v = 3 := orderOf_eq_prime (hAe.2 v hvB.1) hv1
    exact hm3 (hv3 ▸ orderOf_dvd_of_pow_eq_one h1)

end Ctx

end Proof15Res3W

open Proof15Res3W

theorem step159WT_of
    (h142 : Item142R) : Step159WT := by
  intro G _ _ A c L ctx
  have h := ctx.toSec15R
  have hSD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hSD.mem_partTwoE
  obtain ⟨Q, D, hQ2, hAQ, hD, -, hcD, hQD⟩ := exists_hyperplane_mem_of_ctx159 ctx
  set P := Q ⊓ Subgroup.centralizer (D : Set G) with hPdef
  have hcommA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hSD.isElemAbelian.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAD : A ≤ Subgroup.centralizer (D : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hcommA d (hD.1 hd) a ha
  have hP2 : IsPGroup 2 P := hQ2.to_le inf_le_left
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    Late.le_normalizer_inf hAQ (hAD.trans Subgroup.le_normalizer)
  have hP1 : P ≠ ⊥ := fun h0 => hQD (by rw [h0, Subgroup.commutator_bot_left])
  have hPD : P ≤ Subgroup.centralizer (D : Set G) := inf_le_right
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) :=
    hPD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcD))
  have hPQ := mem_scriptQ_of_le_centralizer h142 h hP2 hAP hPc
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) with hX
  set Y := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hY
  have hPJ : P ≤ X ⊔ Y := by
    have h1 := hPQ.2 D hD
    rw [inf_eq_left.mpr hPD] at h1
    have h2 : qBound A (lB A) D = X ⊔ Y := by
      rw [qBound, lB_eq_bot_of_ctx159 ctx D, sup_bot_eq]
    rwa [h2] at h1
  have hJQ : X ⊔ Y ∈ scriptQ A (lB A) := sup_pPrimeCoreOf_mem_scriptQ hSD.isElemAbelian.1 hD
  obtain ⟨w, hw, hwD⟩ := exists_isW159_mem_normalizer ctx hD hcD
  obtain ⟨k, hwk⟩ := hw.2.1
  have hwJ : w ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
    have hwX : w ∈ Subgroup.normalizer (X : Set G) :=
      normalizer_le_normalizer_pPrimeCoreOf 3 _ (normalizer_le_normalizer_centralizer D hwD)
    have hwY : w ∈ Subgroup.normalizer (Y : Set G) :=
      normalizer_le_normalizer_pPrimeCoreOf 3 _ (normalizer_le_normalizer_centralizer A hw.1)
    exact le_normalizer_sup (Subgroup.zpowers_le.mpr hwX) (Subgroup.zpowers_le.mpr hwY)
      (Subgroup.mem_zpowers w)
  have hR3 : IsPGroup 3 (A ⊔ Subgroup.zpowers w : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hA.isPGroup (Proof159Res2.isPGroup_zpowers hwk)
      (Subgroup.zpowers_le.mpr hw.1)
  have hRJ : A ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) :=
    sup_le hJQ.1.2.2 (Subgroup.zpowers_le.mpr hwJ)
  have hJ3 : ¬ 3 ∣ Nat.card (X ⊔ Y : Subgroup G) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hJQ.1.2.1
  obtain ⟨S, ⟨hSJ, hS2, hSmax⟩, -, hRS⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three Nat.prime_two hR3
      hJ3 hRJ bot_le IsPGroup.of_bot (fun r _ => Subgroup.mem_normalizer_iff.mpr fun g => by
        simp)
  have hS1 : S ≠ ⊥ := by
    intro hS0
    exact hP1 ((hSmax P hPJ hP2 (by rw [hS0]; exact bot_le)).trans hS0)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_sup_left.trans hRS
  refine ⟨w, hw, S, ⟨⟨mem_scriptQ_of_le hJQ hSJ hAS, le_top⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩, hS1, ?_⟩
  exact hRS (le_sup_right (a := A) (Subgroup.mem_zpowers w))

end CFSG.RankThree.PartTwo.Sec15
