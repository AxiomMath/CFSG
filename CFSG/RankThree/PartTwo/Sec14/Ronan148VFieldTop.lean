module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofFieldTop
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Ronan148VFieldTwist
import CFSG.RankThree.PartTwo.Sec14.Ronan148JTools
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Concl142Item
import CFSG.RankThree.PartTwo.Sec14.Ronan148JGen
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Sporadic.ON
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_sup_pPrimeCoreOf_le {A : Subgroup G} {a : G} (ha : a ∈ A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  set M := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hM
  set C := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hC
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx a ha)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hAa.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hCa : C ≤ Subgroup.centralizer ({a} : Set G) := by
    refine (pPrimeCoreOf_le 3 _).trans fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) a ha).symm
  have hCM : C ≤ Subgroup.normalizer (M : Set G) := hCa.trans (le_normalizer_pPrimeCoreOf 3 _)
  rw [Subgroup.commutator_le]
  intro x hx g hg
  have hx' : x ∈ (M : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M C hCM]
    exact hx
  obtain ⟨m, hm, c, hc, rfl⟩ := Set.mem_mul.mp hx'
  have hcg : c * g = g * c := ((Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hc)) g hg).symm
  have hgm : g * m⁻¹ * g⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (hAM hg) m⁻¹).mp (M.inv_mem hm)
  have e1 : ⁅m * c, g⁆ = m * (g * m⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    calc m * c * g * (m * c)⁻¹ * g⁻¹ = m * (c * g) * c⁻¹ * m⁻¹ * g⁻¹ := by group
      _ = m * (g * c) * c⁻¹ * m⁻¹ * g⁻¹ := by rw [hcg]
      _ = m * (g * m⁻¹ * g⁻¹) := by group
  rw [e1]
  exact M.mul_mem hm hgm

theorem card_eq_three_mul_of_isTripleCover {X T : Type} [Group X] [Group T]
    (h : Sec4.IsTripleCover X T) : Nat.card X = 3 * Nat.card T := by
  obtain ⟨hc, ⟨χ⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr χ.toEquiv, mul_comm]

section Certificates

theorem img148_pPrimeCoreOf_inf_eq_bot {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e j : G} (he : e ∈ A) (hjA : j ∈ A)
    {K J : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n)
    (hJpi : Sec4.IsoLThreePi ↥(img148 A Y J) 2 (3 * n))
    (hind : KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y e he) .field)
    (hJs : IsSimpleGroup ↥(img148 A Y J)) (hKs : IsSimpleGroup ↥(img148 A Y K)) (hKJ : K ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJY : J = Y)
    (hKe : img148 A Y K ≤
      Subgroup.centralizer ({alpha148 A Y e he} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hjJ : j ∈ J) :
    img148 A Y (pPrimeCoreOf 3 (Subgroup.centralizer ({e * j} : Set G)) ⊓ Y) = ⊥ := by
  set a := e * j with hadef
  have haA : a ∈ A := A.mul_mem he hjA
  set M := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ Y with hMdef
  set σ := alpha148 A Y e he with hσdef
  have hσ3 : σ ^ 3 = 1 := alpha148_pow_three hA3 he
  have hσN : σ ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ (alpha148_mem_img148 he)
  set z := alpha148 A Y j hjA with hzdef
  have hzJ : z ∈ img148 A Y J := mem_img148_iff.mpr ⟨j, Subgroup.mem_sup_right hjA, hjJ, rfl⟩
  have hz3 : z ^ 3 = 1 := alpha148_pow_three hA3 hjA
  have hzσ : z * σ = σ * z := by
    rw [hzdef, hσdef, ← alpha148_mul hjA he, ← alpha148_mul he hjA, alpha148_eq_mk',
      alpha148_eq_mk']
    congr 1
    exact Subtype.ext (hAab j hjA e he)
  have hσz : σ * z = alpha148 A Y a haA := (alpha148_mul he hjA).symm
  have hMY : M ≤ Y := inf_le_right
  have hMM : M ≤ Y ⊔ A := hMY.trans le_sup_left
  have hNX : img148 A Y M ≤ img148 A Y J := img148_mono (hMY.trans hJY.symm.le)
  have hN3 : ¬ 3 ∣ Nat.card (img148 A Y M) := by
    intro h3
    have h1 : 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :=
      (h3.trans (card_img148_dvd hMM)).trans (Subgroup.card_dvd_of_le inf_le_left)
    have := coprime_card_pPrimeCoreOf (G := G) 3 (Subgroup.centralizer ({a} : Set G))
    exact absurd (Nat.Coprime.eq_one_of_dvd this h1) (by norm_num)
  have hYa : Y ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) hg.2) x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg.1) x
    simp only [hMdef, Subgroup.mem_inf]
    exact and_congr h1 h2
  have hNn : img148 A Y J ⊓ Subgroup.centralizer ({σ * z} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
      Subgroup.normalizer (img148 A Y M : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine le_trans ?_ (img148_le_normalizer hYa)
    intro x hx
    obtain ⟨hxJ, hxc⟩ := Subgroup.mem_inf.mp hx
    rw [hσz] at hxc
    have hxY : x ∈ img148 A Y Y := hJY ▸ hxJ
    refine Item148Rank.mem_img148_centralizer_of_commute148 hAY haA (hA3 a haA) le_rfl hxY ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  exact eq_bot_of_field_twist hn hJpi hJs hind hσ3 hσN (img148_mono hKJ) hKe hKs hKpi hzJ hz3
    hzσ hNX hN3 hNn

theorem false_of_kType148_of_J2 {A Y : Subgroup G} [(ker148 A Y).Normal] {e : G}
    {K Le : Subgroup G} {n : ℕ} (hkt : KType148 A Y e K Le)
    (hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n)
    (ψ : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) : False := by
  rcases hkt.2 with ⟨-, -, h1 | ⟨-, h1⟩ | h1⟩ | ⟨hON, -⟩
  · obtain ⟨φ⟩ := h1
    exact Item148PtRes2.not_isoLThreePi_J2 2 n
      (Sec15.Proof1511.isoLThreePi_of_mulEquiv (φ.trans ψ) hKpi)
  · obtain ⟨φ⟩ := h1
    exact Sec15.Proof1511.not_isoLThreePi_of_A7 φ hKpi
  · obtain ⟨p, f, e', hp, -, -, hL3, -⟩ := h1
    apply Item148PtRes2.not_isoLThreePi_J2 p (f * e')
    rcases hL3 with ⟨hq, ⟨χ⟩⟩ | ⟨hq, ⟨χ⟩⟩
    · exact Or.inl ⟨hq, ⟨ψ.symm.trans χ⟩⟩
    · exact Or.inr ⟨hq, ⟨ψ.symm.trans χ⟩⟩
  · have h1 := card_eq_three_mul_of_isTripleCover hON
    rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2, CFSG.Sporadic.ON.card_ON] at h1
    omega

theorem false_of_lA_J2_of_kType148 {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {e b : G} {K Le Lb : Subgroup G} {n : ℕ}
    (hkt : KType148 A Y e K Le) (hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n)
    (hLe : Le ∈ thetaComponentsAt 3 e) (h3Le : 3 ∣ Nat.card Le)
    (hzb : Subgroup.zpowers b = Subgroup.zpowers e) (hbΩ : Subgroup.zpowers b ∈ omegaA A)
    (hLb : Lb ∈ lA A b)
    (hJ2 : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    False := by
  have hLbe : Lb ∈ lA A e := by
    rw [← lA_eq_of_zpowers_eq hzb]
    exact hLb
  have heΩ : Subgroup.zpowers e ∈ omegaA A := by
    rw [← hzb]
    exact hbΩ
  have hLeLb : Le = Lb := (hS.chosen136.2 e heΩ Lb hLbe).2 Le hLe h3Le
  subst hLeLb
  obtain ⟨ψ⟩ := hJ2
  exact false_of_kType148_of_J2 hkt hKpi ψ

theorem exists_mem_inf_not_mem_zpowers {A E J : Subgroup G} {e : G} (hA : Late.IsE27 A)
    (hE : IsHyperplane A E) (he : e ∈ A) (heE : e ∈ E) (he3 : orderOf e = 3)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAeq : A = Subgroup.zpowers e ⊔ (A ⊓ J)) :
    ∃ j ∈ A, j ∈ J ∧ j ∈ E ∧ j ∉ Subgroup.zpowers e := by
  have hEcard : Nat.card E = 9 := by
    have h1 := hE.2
    rw [hA.2] at h1
    omega
  obtain ⟨b, hbE, hbe⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers e := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers e from hcon)
    rw [hEcard, Nat.card_zpowers, he3] at h1
    omega
  have hbA : b ∈ A := hE.1 hbE
  have heN : Subgroup.zpowers e ≤ Subgroup.normalizer ((A ⊓ J : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem he hx.1) (A.inv_mem he), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hAJ he) x).mp hx.2
    · intro hx
      have hx1 : x = e⁻¹ * (e * x * e⁻¹) * e := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hx1]
        exact A.mul_mem (A.mul_mem (A.inv_mem he) hx.1) he
      · exact (Subgroup.mem_normalizer_iff.mp (hAJ he) x).mpr hx.2
  have hb' : b ∈ (Subgroup.zpowers e : Set G) * ((A ⊓ J : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ heN, ← hAeq]
    exact hbA
  obtain ⟨h, hh, j, hj, hbhj⟩ := Set.mem_mul.mp hb'
  have hhE : h ∈ E := (Subgroup.zpowers_le.mpr heE) hh
  refine ⟨j, hj.1, hj.2, ?_, ?_⟩
  · have : j = h⁻¹ * b := by rw [← hbhj]; group
    rw [this]
    exact E.mul_mem (E.inv_mem hhE) hbE
  · intro hje
    apply hbe
    rw [← hbhj]
    exact (Subgroup.zpowers e).mul_mem hh hje

theorem img148_le_bot_of_no_twisted_point (h143 : Ronan148Q.Item143QS14) {A L : Subgroup G}
    {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A) (he3 : orderOf e = 3)
    {K J : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G))
    (hKΔ : K = deltaZero A (lB A) K) (hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n)
    (hJpi : Sec4.IsoLThreePi ↥(img148 A Y J) 2 (3 * n))
    (hind : KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y e he) .field)
    (hJs : IsSimpleGroup ↥(img148 A Y J)) (hKs : IsSimpleGroup ↥(img148 A Y K)) (hKJ : K ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJY : J = Y)
    (hAeq : A = Subgroup.zpowers e ⊔ (A ⊓ J))
    (hHJ : ∀ (b d : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → False)
    (hno : ∀ j ∈ A, j ∈ J → j ∉ Subgroup.zpowers e → Subgroup.zpowers (e * j) ∈ omegaA A →
      ∀ R ∈ scriptQZero A (lB A), R ≤ K ⊓ Subgroup.centralizer ({j} : Set G) →
        img148 A Y R ≤ ⊥) :
    img148 A Y K ≤ ⊥ := by
  have hA : Late.IsE27 A := hS.isE27'
  have hAF : A ∈ partTwoF G := hS.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hKe : img148 A Y K ≤
      Subgroup.centralizer ({alpha148 A Y e he} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    obtain ⟨g, hgM, hgK, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hKY.trans inf_le_right) hgK)
  rw [hKΔ]
  refine Ronan148J.img148_deltaZero_le_of_hyperplanes_of_le hA (hKY.trans inf_le_left)
    fun E hE R hR hRE => ?_
  have hRK : R ≤ K := hRE.trans inf_le_left
  have hRE' : R ≤ Subgroup.centralizer (E : Set G) := hRE.trans inf_le_right
  have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := hRK.trans (hKY.trans inf_le_right)
  have hRY : R ≤ Y := hRK.trans (hKY.trans inf_le_left)
  by_cases heE : e ∈ E
  swap
  ·
    have hAE : E ⊔ Subgroup.zpowers e = A := Item148HJ.sup_zpowers_eq_of_isHyperplane hE he heE
    have hRA : R ≤ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← hAE]
      refine sup_le (Subgroup.le_centralizer_iff.mp hRE') ?_
      rw [Subgroup.zpowers_le]
      intro r hr
      exact Subgroup.mem_centralizer_singleton_iff.mp (hRe hr)
    have hR1 : R = ⊥ := by
      rw [hR.2]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRA
    rw [hR1]
    intro x hx
    obtain ⟨g, hgM, hg, rfl⟩ := mem_img148_iff.mp hx
    have hg1 : (⟨g, hgM⟩ : ↥(Y ⊔ A)) = 1 := Subtype.ext (Subgroup.mem_bot.mp hg)
    rw [hg1, map_one]
    exact Subgroup.one_mem _
  obtain ⟨j, hjA, hjJ, hjE, hje⟩ := exists_mem_inf_not_mem_zpowers hA hE he heE he3 hAJ hAeq
  have haA : e * j ∈ A := A.mul_mem he hjA
  have hae : e * j ∉ Subgroup.zpowers e := by
    intro hae
    apply hje
    have : j = e⁻¹ * (e * j) := by group
    rw [this]
    exact (Subgroup.zpowers e).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers e)) hae
  have ha1 : e * j ≠ 1 := fun h1 => hae (h1 ▸ Subgroup.one_mem _)
  have hRa : R ≤ Subgroup.centralizer ({e * j} : Set G) :=
    hRE'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (E.mul_mem heE hjE)))
  by_cases hejΩ : Subgroup.zpowers (e * j) ∈ omegaA A
  · exact hno j hjA hjJ hje hejΩ R hR
      (le_inf hRK (hRE'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hjE))))
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({e * j} : Set G))) A (piCompl 3)
  rcases ((h143 G A c L hS) (e * j) haA ha1 hejΩ Q₀ hQ₀).2 with hΔ | hcase
  swap
  · exfalso
    obtain ⟨b', d', Lb, hb'Ω, hLb, hJ2, hd'A, hd'1, hd'c, -⟩ := hcase
    exact hHJ b' d' Lb hb'Ω hLb hJ2 hd'A hd'1 hd'c
  have hRΔ : R ≤ delta A (lB A) (Subgroup.centralizer ({e * j} : Set G)) := le_delta hR.1 hRa
  rw [hΔ] at hRΔ
  have hRM : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({e * j} : Set G)) := by
    rw [hR.2]
    exact (Subgroup.commutator_mono hRΔ le_rfl).trans (commutator_sup_pPrimeCoreOf_le haA hAab)
  exact (img148_mono (le_inf hRM hRY)).trans (img148_pPrimeCoreOf_inf_eq_bot hAY hA3 hAab he
    hjA hn hKpi hJpi hind hJs hKs hKJ hAJ hJY hKe hjJ).le

theorem not_isoLThreePi_two_of_card_eq_1876896 {X : Type} [Group X]
    (hX : Nat.card X = 1876896) {n : ℕ} (hn : 1 ≤ n) : ¬ Sec4.IsoLThreePi X 2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2n 2
  have h8 : 8 ≤ (2 ^ n) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2n 3
  have hbound : ∀ M g : ℕ, 1 ≤ M → g ≤ 3 → 1876896 * g = (2 ^ n) ^ 3 * M → n ≤ 7 := by
    intro M g hM hg hc
    by_contra hn8
    have h256 : 256 ≤ 2 ^ n := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 256 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h256 3
    have h5 : (2 ^ n) ^ 3 ≤ (2 ^ n) ^ 3 * M := Nat.le_mul_of_pos_right _ hM
    omega
  rintro (⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩)
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [← Nat.card_congr φ.toEquiv, hX, GaloisField.card 2 n (by omega)] at hc
    have hn7 : n ≤ 7 := hbound _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (by omega))) (Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)) hc
    interval_cases n <;> revert hc hq <;> norm_num
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    rw [← Nat.card_congr φ.toEquiv, hX] at hc
    have hn7 : n ≤ 7 := hbound _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (by omega))) (Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)) hc
    interval_cases n <;> revert hc hq <;> norm_num

theorem zpowers_mem_omegaA_of_kType148 {A Y : Subgroup G} [(ker148 A Y).Normal] {e : G}
    {K Le : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (hkt : KType148 A Y e K Le)
    (hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n) :
    Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e := by
  rcases hkt.2 with ⟨heΩ, hLe, -⟩ | ⟨-, h1 | h1⟩
  · exact ⟨heΩ, hLe⟩
  · obtain ⟨φ⟩ := h1
    exact (Sec15.Proof1511.not_isoLThreePi_of_A7 φ hKpi).elim
  · obtain ⟨h7, ⟨φ⟩⟩ := h1
    refine (not_isoLThreePi_two_of_card_eq_1876896 ?_ hn hKpi).elim
    rw [Nat.card_congr φ.toEquiv]
    exact Sec15.card_projSL_three_seven

@[expose] def Step148FieldTopPointTw : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) → J = Y →
        letI := ker148_normal hY.2
        ∃ j ∈ A, j ∈ J ∧ j ∉ Subgroup.zpowers e ∧ Subgroup.zpowers (e * j) ∈ omegaA A ∧
          ∃ R ∈ scriptQZero A (lB A), R ≤ K ⊓ Subgroup.centralizer ({j} : Set G) ∧
            ¬ img148 A Y R ≤ ⊥

theorem step148FieldTopPointTw_holds (h143 : Ronan148Q.Item143QS14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) : Step148FieldTopPointTw := by
  intro G _ _ A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hField hAeq hJY
  letI := ker148_normal hY.2
  by_contra hno
  push Not at hno
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hS.mem_partTwoF.1.2
  obtain ⟨n, hn, hKpi, hJpi, hind⟩ := hField
  obtain ⟨-, -, -, -, he1, hKc, hKΔ, hKLe, hLe, -⟩ := hP
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hKc
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have hKM : K ≤ Y ⊔ A := (hKY.trans inf_le_left).trans le_sup_left
  have he3 : orderOf e = 3 := orderOf_eq_prime (hA3 e he) he1
  have hKs : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 hS hkt
  have hJp : Group.IsPerfect ↥(img148 A Y J) := by
    have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    exact isPerfect_img148 hJM
  have hJs : IsSimpleGroup ↥(img148 A Y J) :=
    (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega) hJpi).1
  have h3K : 3 ∣ Nat.card K :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hKpi).trans (card_img148_dvd hKM)
  obtain ⟨heΩ, -⟩ := zpowers_mem_omegaA_of_kType148 hn hkt hKpi
  have hK1 : img148 A Y K ≤ ⊥ := by
    refine img148_le_bot_of_no_twisted_point h143 hS hY.2 he he3 hn hKY hKΔ hKpi hJpi hind hJs
      hKs hKJ hAJ hJY hAeq (fun b' d' Lb hb'Ω hLb hJ2 hd'A hd'1 hd'c => ?_) hno
    obtain ⟨Le', hLe', hJ2'⟩ := exists_hj_of_hj_point h134 h48 h415 hS hb'Ω hLb hJ2 hd'A hd'1
      hd'c heΩ
    exact false_of_lA_J2_of_kType148 hS hkt hKpi hLe (h3K.trans (Subgroup.card_dvd_of_le hKLe))
      rfl heΩ hLe' hJ2'
  have hKbot : img148 A Y K = ⊥ := le_bot_iff.mp hK1
  have : Nontrivial ↥(img148 A Y K) := hKs.toNontrivial
  have h1 : Nat.card ↥(img148 A Y K) = 1 := by rw [hKbot, Subgroup.card_bot]
  have h2 := Finite.one_lt_card (α := ↥(img148 A Y K))
  omega

@[expose] def KF148FieldTopTwistR : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J K E : Subgroup X) (σ : X) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥J 2 (3 * n) → KFacts.InducesStdKind J σ .field → σ ^ 3 = 1 →
    K ≤ J → K ≤ Subgroup.centralizer ({σ} : Set X) → IsSimpleGroup ↥K →
    Sec4.IsoLThreePi ↥K 2 n → E ≤ J → E ≤ Subgroup.centralizer ({σ} : Set X) →
    IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    ∀ z ∈ E, z ≠ 1 → ∀ R : Subgroup X, R ≤ K ⊓ Subgroup.centralizer ({z} : Set X) →
      ¬ 3 ∣ Nat.card R → Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X) →
      R = ⁅R, Subgroup.zpowers σ ⊔ E⁆ → R ≠ ⊥ →
      ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
        Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
        ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K

theorem step148RankImgGeFieldTopNotK_of_twistR (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142AllS14) (hTw : Step148FieldTopPointTw) (hKF : KF148FieldTopTwistR) :
    Step148RankImgGeFieldTopNotK := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hField hAeq hJY
  letI := ker148_normal hY.2
  intro hXK
  obtain ⟨j, hjA, hjJ, hje, hejΩ, R, hR, hRKj, hRα⟩ :=
    hTw G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hField hAeq hJY
  obtain ⟨n, hn, hKpi, hJpi, hind⟩ := hField
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  obtain ⟨hAE, -⟩ := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hJY' : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hAeq' : img148 A Y A = Subgroup.zpowers (alpha148 A Y e he) ⊔ img148 A Y (A ⊓ J) := by
    refine le_antisymm ?_ (sup_le ((Subgroup.zpowers_le).mpr (alpha148_mem_img148 he))
      (img148_mono inf_le_left))
    have hle : img148 A Y A ≤
        img148 A Y (Subgroup.zpowers e) ⊔ img148 A Y (A ⊓ J) := by
      rw [← img148_sup ((Subgroup.zpowers_le.mpr he).trans le_sup_right)
        (inf_le_left.trans le_sup_right)]
      exact img148_mono hAeq.le
    exact hle.trans (sup_le_sup_right (img148_zpowers_le he) _)
  have hKs : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 h hkt
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have hKe : img148 A Y K ≤
      Subgroup.centralizer ({alpha148 A Y e he} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    obtain ⟨g, hgM, hgK, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hKYC.trans inf_le_right) hgK)
  have hEA : img148 A Y (A ⊓ J) ≤ img148 A Y A := img148_mono inf_le_left
  have hEe : img148 A Y (A ⊓ J) ≤
      Subgroup.centralizer ({alpha148 A Y e he} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x (hEA hx) _ (alpha148_mem_img148 he))
  have hEc : IsMulCommutative ↥(img148 A Y (A ⊓ J)) :=
    ⟨⟨fun x y => Subtype.ext (hAab x.1 (hEA x.2) y.1 (hEA y.2))⟩⟩
  have hE3 : ∀ x ∈ img148 A Y (A ⊓ J), x ^ 3 = 1 := fun x hx => hAE.2 x (hEA hx)
  have hzE : alpha148 A Y j hjA ∈ img148 A Y (A ⊓ J) :=
    mem_img148_iff.mpr ⟨j, Subgroup.mem_sup_right hjA, ⟨hjA, hjJ⟩, rfl⟩
  have hz1 : alpha148 A Y j hjA ≠ 1 := by
    intro h1
    apply hje
    have h2 : alpha148 A Y j hjA = alpha148 A Y 1 (Subgroup.one_mem A) := by
      rw [h1, alpha148_eq_mk']
      exact (map_one _).symm
    have : j = 1 := alpha148_injective hA3 hjA (Subgroup.one_mem A) h2
    rw [this]
    exact Subgroup.one_mem _
  have hRK : R ≤ K := hRKj.trans inf_le_left
  have hRM : R ≤ Y ⊔ A := (hRK.trans (hKYC.trans inf_le_left)).trans le_sup_left
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    have := hR.1.1.2.1 ⟨3, Nat.prime_three⟩ h3
    exact this rfl
  have hRαK : img148 A Y R ≤ img148 A Y K ⊓
      Subgroup.centralizer ({alpha148 A Y j hjA} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine le_inf (img148_mono hRK) ?_
    intro x hx
    obtain ⟨g, hgM, hgR, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hRKj.trans inf_le_right) hgR)
  have hRα3 : ¬ 3 ∣ Nat.card (img148 A Y R) := fun h3 => hR3 (h3.trans (card_img148_dvd hRM))
  have hRαN : img148 A Y A ≤ Subgroup.normalizer (img148 A Y R : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hR.1.1.2.2
  have hRαc : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
    rw [← HJRes2.img148_commutator_eq hRM le_sup_right, ← hR.2]
  rw [hAeq'] at hRαN hRαc
  obtain ⟨V, hVJ, hV3, hAV, hVK⟩ := hKF _ (img148 A Y J) (img148 A Y K) (img148 A Y (A ⊓ J))
    (alpha148 A Y e he) n hn hJpi hind he3 (img148_mono hKJ) hKe hKs hKpi
    (img148_mono inf_le_right) hEe hEc hE3 _ hzE hz1 (img148 A Y R) hRαK hRα3 hRαN hRαc
    (fun hb => hRα (le_of_eq hb))
  rw [← hAeq'] at hAV hVK
  have hσz : alpha148 A Y e he * alpha148 A Y j hjA = alpha148 A Y (e * j) (A.mul_mem he hjA) :=
    (alpha148_mul he hjA).symm
  rw [hσz] at hVJ
  have hVb : V ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({e * j} : Set G)) := by
    intro v hv
    refine Item148Rank.mem_img148_centralizer_of_commute148 hAY (A.mul_mem he hjA)
      (hA3 _ (A.mul_mem he hjA)) le_rfl (img148_mono hJY' (hVJ hv).1) ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hVJ hv).2).symm
  have h142c : Concl142S14 := concl142_forall_of_item142 h422 h45 h142
  exact hVK ((Ronan148J.commutator_le_img148_deltaZero_of_point h142c h hY hejΩ V hVb hV3
    hAV).trans hXK)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
