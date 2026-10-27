module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sk
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x

variable {G : Type} [Group G] [Finite G]

namespace P22so

theorem eq_bot_of_normal_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) {P : Subgroup X}
    (hP : P.Normal) (hP2 : IsPGroup 2 P) : P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := P22y.center_eq_bot_of_isL2Ev h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI := P22y.charP_two_of_card hF
  haveI : Finite X := Finite.of_equiv _ e.toEquiv.symm
  have hn := P22y.one_le_of_card hF
  have hcard : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
  by_cases h4 : 4 ≤ Nat.card F
  · haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := P22y.isSimpleGroup_sl2 h4
    haveI : IsSimpleGroup X :=
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).isSimpleGroup
    haveI := hP
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
    · exact hb
    · exfalso
      have hX2 : IsPGroup 2 X := (ht ▸ hP2).of_equiv Subgroup.topEquiv
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hX2
      have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := by
        rw [← hk, hcard]
        exact Dvd.intro_left _ rfl
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hq : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hqq : 4 ≤ (2 ^ n) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      obtain ⟨r, hr⟩ : ∃ r, (2 ^ n) ^ 2 = 2 * r := ⟨2 ^ (2 * n - 1), by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega⟩
      generalize (2 ^ n) ^ 2 = q at hj hr hqq
      rcases j with _ | j
      · rw [pow_zero] at hj
        omega
      · rw [pow_succ] at hj
        omega
  · have hn1 : n = 1 := by
      by_contra hne
      apply h4
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst hn1
    have hX6 : Nat.card X = 6 := by rw [hcard]; norm_num
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
    have hdvd : 2 ^ k ∣ 6 := hk ▸ hX6 ▸ Subgroup.card_subgroup_dvd_card P
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h4' : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have := Nat.dvd_trans h4' hdvd
      norm_num at this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
    · exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
    · have hc := CFSG.Semidihedral.Local.le_center_of_normal_card_two hP (by rw [hk, pow_one])
      rw [hZ] at hc
      exact le_bot_iff.1 hc

theorem pCoreOf_le_of_isSylowOf {P H : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P H) :
    pCoreOf 2 H ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPN : P ≤ normalizer (pCoreOf 2 H : Set G) :=
    hP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hsup : IsPGroup 2 (pCoreOf 2 H ⊔ P : Subgroup G) := hQp.to_sup_of_normal_left' hP.isPGroup hPN
  have heq := hP.eq_of_le le_sup_right (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hP.le) hsup
  exact le_sup_left.trans heq.le

theorem Z_le_jOf (D : Data G) : D.Z ≤ jOf D.T := by
  obtain ⟨A, hA⟩ := exists_mem_elemThompsonFamily ↥D.T
  have hmax := isMax_of_mem_family hA
  refine le_trans ?_ (le_jOf_of_isMax hmax)
  obtain ⟨hAT, hAel, hAmax⟩ := hmax
  have hZ : ∀ z ∈ D.Z, z ∈ D.T ∧ (∀ k ∈ D.T, k * z = z * k) ∧ z ^ 2 = 1 := fun z hz =>
    CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz
  have hZel : IsElemAbelian 2 D.Z := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => (hZ z hz).2.2⟩
    exact ((hZ b b.2).2.1 a (hZ a a.2).1)
  have hsup : IsElemAbelian 2 (A.map D.T.subtype ⊔ D.Z) :=
    hAel.sup_of_commute hZel fun a ha z hz => (hZ z hz).2.1 a (hAT ha)
  have hle : A.map D.T.subtype ⊔ D.Z ≤ D.T := sup_le hAT fun z hz => (hZ z hz).1
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : A.map D.T.subtype ≤ _) (hAmax _ hle hsup)
  exact le_sup_right.trans heq.symm.le

theorem U_le_proofN (D : Data G) : D.U ≤ proofN D := by
  have hZN : D.Z ≤ proofN D := (Z_le_jOf D).trans (uc22p22e_jOf_le D.sylowM)
  have hMN := uc22p22t_M_le_normalizer_jOf D
  change uCore D.M D.T ≤ proofN D
  unfold uCore
  refine iSup_le fun g => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_normalizer_iff.1 (hMN g.2) z).1 (hZN hz)

theorem exists_isMax_le (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) :
    ∃ B : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T B ∧ B ≤ proofN D ⊓ centralizer (D.U : Set G) := by
  obtain ⟨A, hA⟩ := exists_mem_elemThompsonFamily ↥D.T
  have hmax := isMax_of_mem_family hA
  have hno := uc22p22xf_noStrictOffender_of D Ch h2 h3 h51 hH c A hA
  set A' : Subgroup G := A.map D.T.subtype with hA'def
  have hA'N : A' ≤ proofN D := (le_jOf_of_isMax hmax).trans (uc22p22e_jOf_le D.sylowM)
  obtain ⟨hA'T, hA'el, hA'max⟩ := hmax
  have hU := uc22p22xf_hel D
  have hUT := uc22p22xf_UleT D
  have hUc : D.U ≤ centralizer (D.U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv => hU.comm hv hu
  have hext : ∀ X : Subgroup G, A' ≤ X → X ≤ D.T → IsElemAbelian 2 X → X = A' := fun X hAX hXT hXel =>
    (Subgroup.eq_of_le_of_card_ge hAX (hA'max X hXT hXel)).symm
  have hCUle : centralizer (A' : Set G) ⊓ D.U ≤ A' := by
    have hX := hext (A' ⊔ (centralizer (A' : Set G) ⊓ D.U)) le_sup_left
      (sup_le hA'T (inf_le_right.trans hUT))
      (hA'el.sup_of_commute (hU.mono inf_le_right) fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 hb.1 a ha)
    exact le_sup_right.trans hX.le
  have hA₁U : ∀ a ∈ centralizer (D.U : Set G) ⊓ A', ∀ u ∈ D.U, a * u = u * a := fun a ha u hu =>
    (Subgroup.mem_centralizer_iff.1 ha.1 u hu).symm
  set B : Subgroup G := centralizer (D.U : Set G) ⊓ A' ⊔ D.U with hBdef
  have hBel : IsElemAbelian 2 B := (hA'el.mono inf_le_right).sup_of_commute hU hA₁U
  have hBT : B ≤ D.T := sup_le (inf_le_right.trans hA'T) hUT
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (centralizer (D.U : Set G) ⊓ A') D.U hA₁U
  have hinf : (centralizer (D.U : Set G) ⊓ A') ⊓ D.U = centralizer (A' : Set G) ⊓ D.U := by
    ext x
    constructor
    · rintro ⟨⟨_, hxA⟩, hxU⟩
      exact ⟨Subgroup.mem_centralizer_iff.2 fun h hh => hA'el.comm hh hxA, hxU⟩
    · rintro ⟨hxc, hxU⟩
      exact ⟨⟨hUc hxU, hCUle ⟨hxc, hxU⟩⟩, hxU⟩
  rw [hinf] at hprod
  have e1 := Subgroup.relIndex_mul_card (H := centralizer (D.U : Set G)) (K := A')
  have e2 := Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := D.U)
  have hcpos : 0 < Nat.card ↥(centralizer (A' : Set G) ⊓ D.U) := Nat.card_pos
  have hcard : Nat.card A' ≤ Nat.card B := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(centralizer (A' : Set G) ⊓ D.U)) ?_ hcpos
    calc Nat.card A' * Nat.card ↥(centralizer (A' : Set G) ⊓ D.U)
        = (centralizer (D.U : Set G)).relIndex A' * Nat.card ↥(centralizer (D.U : Set G) ⊓ A') *
            Nat.card ↥(centralizer (A' : Set G) ⊓ D.U) := by rw [e1]
      _ ≤ (centralizer (A' : Set G)).relIndex D.U * Nat.card ↥(centralizer (D.U : Set G) ⊓ A') *
            Nat.card ↥(centralizer (A' : Set G) ⊓ D.U) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hno)
      _ = Nat.card ↥(centralizer (D.U : Set G) ⊓ A') * Nat.card D.U := by rw [← e2]; ring
      _ = Nat.card B * Nat.card ↥(centralizer (A' : Set G) ⊓ D.U) := hprod.symm
  refine ⟨B, ⟨hBT, hBel, fun X hXT hXel => (hA'max X hXT hXel).trans hcard⟩, ?_⟩
  refine sup_le (le_inf (inf_le_right.trans hA'N) inf_le_left) (le_inf (U_le_proofN D) hUc)

theorem isMax_of_isMax_of_le {T R B A : Subgroup G} (hB : CFSG.Quasithin.IsMaxElemAbelian T B) (hBR : B ≤ R)
    (hRT : R ≤ T) (hA : CFSG.Quasithin.IsMaxElemAbelian R A) : CFSG.Quasithin.IsMaxElemAbelian T A :=
  ⟨hA.1.trans hRT, hA.2.1, fun Y hYT hYel => (hB.2.2 Y hYT hYel).trans (hA.2.2 B hBR hB.2.1)⟩

theorem isMax_of_le {T R B : Subgroup G} (hB : CFSG.Quasithin.IsMaxElemAbelian T B) (hBR : B ≤ R)
    (hRT : R ≤ T) : CFSG.Quasithin.IsMaxElemAbelian R B :=
  ⟨hBR, hB.2.1, fun Y hYR hYel => hB.2.2 Y (hYR.trans hRT) hYel⟩

omit [Finite G] in
theorem mem_normalizer_centralizer_of {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) :
    g ∈ normalizer (centralizer (V : Set G) : Set G) := by
  have key : ∀ y ∈ normalizer (V : Set G), ∀ x ∈ centralizer (V : Set G), y * x * y⁻¹ ∈ centralizer (V : Set G) := by
    intro y hy x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hu' : y⁻¹ * u * y ∈ V := by
      have h := (mem_normalizer_iff.1 hy (y⁻¹ * u * y)).2
      apply h
      simpa [mul_assoc] using hu
    have hc := hx _ hu'
    calc u * (y * x * y⁻¹) = y * ((y⁻¹ * u * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * u * y)) * y⁻¹ := by rw [hc]
      _ = y * x * y⁻¹ * u := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end P22so

open P22so

end CFSG.LocalAnalysis.UniquenessCase.UC22
