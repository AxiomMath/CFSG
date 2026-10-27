module

public import CFSG.RankThree.PartTwo.Sec13.RonanItem137
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SQuot
import CFSG.RankThree.PartTwo.Sec13.Ronan138SNorm
import CFSG.RankThree.PartTwo.Sec13.Ronan138SCent
import CFSG.RankThree.PartTwo.Sec13.Ronan138SLStep
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Ronan138SInner
import CFSG.RankThree.PartTwo.Sec13.Ronan138SHeis
import CFSG.RankThree.PartTwo.Sec13.Ronan138SPGL
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item137ProofM12
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix (ProjGenLinGroup)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree Type123)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped commutatorElement

section Small

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_of_mem_zpowers_of_pow_three_pow {g d : G} (hd3 : d ^ 3 = 1)
    (hg : g * d * g⁻¹ ∈ Subgroup.zpowers d) {k : ℕ} (hgk : g ^ 3 ^ k = 1) :
    g * d * g⁻¹ = d := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hpow : ∀ n : ℕ, g ^ n * d * (g ^ n)⁻¹ = d ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc g ^ (n + 1) * d * (g ^ (n + 1))⁻¹ = g * (g ^ n * d * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * d ^ (m ^ n) * g⁻¹ := by rw [ih]
        _ = (g * d * g⁻¹) ^ (m ^ n) := by rw [conj_zpow]
        _ = d ^ (m ^ (n + 1)) := by rw [← hm, ← _root_.zpow_mul, pow_succ, mul_comm]
  have h1 := hpow (3 ^ k)
  rw [hgk, one_mul, inv_one, mul_one] at h1
  have key : ∀ n : ℕ, ((m : ZMod 3)) ^ 3 ^ n = (m : ZMod 3) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have hmod : (m ^ 3 ^ k) % 3 = m % 3 := by
    have : ((m ^ 3 ^ k : ℤ) : ZMod 3) = (m : ZMod 3) := by
      push_cast
      exact key k
    exact (ZMod.intCast_eq_intCast_iff' _ _ 3).mp this
  calc g * d * g⁻¹ = d ^ m := hm.symm
    _ = d ^ (m % 3) := zpow_eq_zpow_emod_of_pow_three hd3 m
    _ = d ^ ((m ^ 3 ^ k) % 3) := by rw [hmod]
    _ = d ^ (m ^ 3 ^ k) := (zpow_eq_zpow_emod_of_pow_three hd3 _).symm
    _ = d := h1.symm

theorem mem_thetaQuotCentralizer_of_commute {L : Subgroup G} {x : G}
    (hx : ∀ l ∈ L, x * l = l * x) : x ∈ Sec4.thetaQuotCentralizer L := by
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (hx l hl).symm)
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
  rw [hx l hl, mul_inv_cancel_right, inv_mul_cancel]
  exact one_mem _

end Small

section LSide

variable {G : Type} [Group G] [Finite G]

theorem card_le_nine_of_m12 (h414 : Sec4.Item4_14_local) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) (Y : Subgroup X) (hY : IsPGroup 3 Y)
    (hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : Nat.card Y ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨⟨hex, hQ27, -⟩, -⟩ := h414 X hX Q
  have hdvd : Nat.card Y ∣ 27 := hQ27 ▸ Subgroup.card_dvd_of_le hYQ
  obtain ⟨n, hn3, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card Y ∣ 3 ^ 3 by simpa using hdvd)
  interval_cases n
  · rw [hn]; norm_num
  · rw [hn]; norm_num
  · rw [hn]; norm_num
  · exfalso
    have hYQeq : Y = Q := Subgroup.eq_of_le_of_card_ge hYQ (by rw [hQ27, hn]; norm_num)
    obtain ⟨-, hcomm, -, hZ3⟩ := hex
    have hcen : Subgroup.center (Q : Subgroup X) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨q, hq⟩ -
      rw [Subgroup.mem_center_iff]
      rintro ⟨q', hq'⟩
      apply Subtype.ext
      rw [← hYQeq] at hq hq'
      exact (hYab q hq q' hq').symm
    rw [hcen, Subgroup.card_top, hQ27] at hZ3
    norm_num at hZ3

theorem le_zpowers_sup_of_m12 (h131 : Item131) (hspor : SporadicModels131)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    A ≤ Subgroup.zpowers c ⊔ L := by
  obtain ⟨hcL, h9, -⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine (S := A ⊓ L) hc3
      (fun hcB => hcL hcB.2) le_rfl h9 (fun b hb => h.isElemAbelian.2 b hb.1)
      (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  exact hAB ▸ sup_le_sup_left inf_le_right _

theorem normalizer_zpowers_le_normalizer_of_m12 (h131 : Item131) (hspor : SporadicModels131)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, h9, -⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hspor' := hspor
  obtain ⟨-, ⟨-, hM12z⟩, -⟩ := hspor'
  obtain ⟨φ⟩ := hM
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ hM12z
  have hAcL : A ≤ Subgroup.zpowers c ⊔ L := le_zpowers_sup_of_m12 h131 hspor h ⟨φ⟩
  have hmax : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → A ≤ F' →
      Nat.card F' ≤ Nat.card A := fun F' hF' hAF' =>
    (h.mem_partTwoF.2.1 F' hF' hAF') ▸ le_rfl
  have h3L := three_dvd_card_of_sec13Data h131 hspor h
  intro x hx
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c)
  have hL' := Sec11.map_conj_mem_thetaComponentsAt hc3 h.mem_thetaComponentsAt hxc
  have h3L' : 3 ∣ Nat.card (L.map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact h3L
  have heq := eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZ hAcL
    h.isElemAbelian hmax hL' h3L'
  exact map_conj_eq_iff_mem_normalizer.mp heq

end LSide

section Main


theorem item137PGLSylow_of_not_mem (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hK18 : KFacts.KS18M12) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e →
              e ∈ Subgroup.centralizer (P : Set G) → e ∉ Subgroup.zpowers c →
              Sec8.IsZ3PGLThreePi (lBarA e K E) → e ∉ L →
                P ≤ K ⊔ E ∧ (Nat.card ↥(K ⊔ E)).factorization 3 = 4 := by
  intro G _ _ A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec hPGL heL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hcfg' := hcfg
  obtain ⟨hPsyl, hAP, -, -, hΔ, -, -, hEA, -, -, -, -, -, -, -, hEdec, -⟩ := hcfg'
  obtain ⟨d, hdL, hd1, hd3, hPP, hZc, hdZ, hP81, hPexp⟩ :=
    exists_commutator_eq_zpowers_of_isSylowOf h131 hspor h414 h hM hPsyl hAP
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hP81]; norm_num)
  have hEΔ : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27} := by
    rw [hΔ]
    exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨hEP, hE3, hE27⟩ := hEΔ
  have hA3 := h.isElemAbelian
  have hA27 := h.card_eq
  have hc3 : c ^ 3 = 1 := hA3.2 c h.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e hD.mem_A
  have he1 : e ≠ 1 := hD.ne_one
  have heE : e ∈ E := hD.mem_A
  have heP : e ∈ P := hEP heE
  have hcP : c ∈ P := hAP h.mem_A
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hXF.2.1
  have hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
    h.mem_partTwoF.2.1
  have hPe : ∀ x ∈ P, x * e = e * x := fun x hx => Subgroup.mem_centralizer_iff.mp heZ x hx
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  have hspor' := hspor
  obtain ⟨-, ⟨-, hM12z⟩, -⟩ := hspor'
  obtain ⟨φM⟩ := hM
  have hZL : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φM hM12z
  obtain ⟨-, -, hinnL, -⟩ := hK18 (L ⧸ aschbacherSolvableCore 3 L) ⟨φM⟩
  have hinn : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∃ y : L ⧸ aschbacherSolvableCore 3 L, σ = MulAut.conj y := hinnL
  have hab9 := card_le_nine_of_m12 h414 (X := L ⧸ aschbacherSolvableCore 3 L) ⟨φM⟩
  have hLH := normalizer_zpowers_le_normalizer_of_m12 h131 hspor h ⟨φM⟩
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hθL3 := (Sec6.theta_solvable_and_not_dvd L).2
  have hθK3 := (Sec6.theta_solvable_and_not_dvd K).2
  have hcE : c ∈ E := hEdec ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hLc y hy.2).symm k).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hEdec, hE27, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot hc3 hcL).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one] at hcard
    omega
  have hB3 : IsPGroup 3 (E ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hEL9]; norm_num)
  have hBab : ∀ x ∈ E ⊓ L, ∀ y ∈ E ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute hx.1 hy.1
  obtain ⟨heK, ⟨φaut⟩, x₀, hx₀E, hx₀type⟩ := facts131_of_isZ3PGLThreePi h131 hspor hD hPGL
  obtain ⟨b, hbE, hbK, hb1⟩ : ∃ b ∈ E, b ∈ K ∧ b ≠ 1 := by
    set σ := φaut.symm (Multiplicative.ofAdd (1 : ZMod 3)) with hσ
    have hσ1 : (σ : MulAut E) ≠ 1 := by
      intro h1
      have h2 : σ = 1 := Subtype.ext h1
      have h3 : Multiplicative.ofAdd (1 : ZMod 3) = φaut 1 := by
        rw [← h2, hσ, MulEquiv.apply_symm_apply]
      rw [map_one φaut, ofAdd_eq_one] at h3
      exact absurd h3 one_ne_zero
    obtain ⟨k, hkN, hkK, hkσ⟩ := Sec4.mem_autIn_iff.mp σ.2
    obtain ⟨a, ha⟩ : ∃ a : E, (σ : MulAut E) a ≠ a := by
      by_contra hall
      push Not at hall
      exact hσ1 (MulEquiv.ext hall)
    rw [← hkσ] at ha
    have ha' : k * (a : G) * k⁻¹ ≠ a := fun h' => ha (Subtype.ext (by
      rw [Sec4.normalizerMonoidHom_apply_coe]; exact h'))
    refine ⟨k * a * k⁻¹ * (a : G)⁻¹, ?_, ?_, ?_⟩
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hkN a).mp a.2) (inv_mem a.2)
    · have haK : (a : G) * k⁻¹ * (a : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hK.2.1 a.2) _).mp (inv_mem hkK)
      have : k * a * k⁻¹ * (a : G)⁻¹ = k * ((a : G) * k⁻¹ * (a : G)⁻¹) := by group
      rw [this]
      exact mul_mem hkK haK
    · intro h1
      exact ha' (mul_inv_eq_one.mp h1)
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card hEP hE27 hP81
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    mem_normalizer_of_mem_lA hK he3 heK hbE hbK hb1 (hPNE hx) (hPe x hx)
  obtain ⟨i, j, hij⟩ := hZc e heP (fun x hx => (hPe x hx).symm)
  have hdj : d ^ j ∈ L := Subgroup.zpow_mem _ hdL j
  have hciL : c ^ i ∉ L := by
    intro hci
    apply heL
    rw [hij]
    exact mul_mem hci hdj
  have hci1 : c ^ i ≠ 1 := fun h1 => hciL (h1 ▸ one_mem _)
  have hczp : c ∈ Subgroup.zpowers (c ^ i) := by
    have hle : Subgroup.zpowers (c ^ i) ≤ Subgroup.zpowers c :=
      Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers c i)
    have hci3 : (c ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc3,
        one_zpow]
    have heq : Subgroup.zpowers (c ^ i) = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_zpowers_of_pow_three hci3 hci1, card_zpowers_of_pow_three hc3 h.ne_one])
    rw [heq]
    exact Subgroup.mem_zpowers c
  have hde : Subgroup.zpowers d ⊓ Subgroup.zpowers e = ⊥ := by
    rw [inf_comm, eq_bot_iff]
    intro x hx
    rw [← zpowers_inf_eq_bot he3 heL]
    exact ⟨hx.1, Subgroup.zpowers_le.mpr hdL hx.2⟩
  have hce : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxc, hxe⟩
    by_contra hx1
    apply hec
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
    have hx3 : (e ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, he3,
        one_zpow]
    have heq : Subgroup.zpowers (e ^ m) = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers e m))
        (by rw [card_zpowers_of_pow_three hx3 hx1, card_zpowers_of_pow_three he3 he1])
    have hle : Subgroup.zpowers (e ^ m) ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hxc
    rw [heq] at hle
    exact hle (Subgroup.mem_zpowers e)
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e :=
    fun a ha ha' => hCE ▸ Subgroup.mem_inf.mpr ⟨ha, ha'⟩
  have hCL : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a ha ha'
    have haL : a ∈ Subgroup.zpowers c ⊔ L := (hEdec ▸ sup_le_sup_left inf_le_right _ :
      E ≤ Subgroup.zpowers c ⊔ L) ha
    obtain ⟨m, l, hl, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup h.le_centralizer haL
    have hcm : c ^ m ∈ Sec4.thetaQuotCentralizer L :=
      mem_thetaQuotCentralizer_of_commute fun l' hl' =>
        (Commute.zpow_left (hLc l' hl').symm m).eq
    have hlT : l ∈ Sec4.thetaQuotCentralizer L := by
      have : l = (c ^ m)⁻¹ * (c ^ m * l) := by group
      rw [this]
      exact mul_mem (inv_mem hcm) ha'
    have hlθ := Sec17.inf_thetaQuotCentralizer_le hZL ⟨hl, hlT⟩
    have hl3 : l ^ 3 = 1 := by
      have hcl : Commute (c ^ m) l := (Commute.zpow_left (hLc l hl).symm m)
      have h1 : (c ^ m * l) ^ 3 = 1 := hE3.2 _ ha
      rw [hcl.mul_pow] at h1
      have h2 : (c ^ m) ^ 3 = 1 := by
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc3,
          one_zpow]
      rwa [h2, one_mul] at h1
    have hl1 : l = 1 := eq_one_of_mem_of_pow_three_pow' hθL3 hlθ (k := 1) (by simpa using hl3)
    rw [hl1, mul_one]
    exact Subgroup.zpow_mem_zpowers c m
  have hCP : ∀ x ∈ P, x ∈ Sec4.thetaQuotCentralizer K → x ∈ Subgroup.zpowers e := by
    intro x hx hxC
    by_cases hxE : x ∈ E
    · exact hCK x hxE hxC
    exfalso
    apply hxE
    have hxcomm : ∀ a ∈ E, a * x = x * a := by
      intro a ha
      have h1 : x * a * x⁻¹ * a⁻¹ ∈ ⁅P, P⁆ := by
        rw [← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator hx (hEP ha)
      have h2 : x * a * x⁻¹ * a⁻¹ ∈ E :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hPNE hx) a).mp ha) (inv_mem ha)
      have h3 : x * a * x⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
        have : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
        rw [this]
        exact mul_mem hxC (Sec6.conj_mem_thetaQuotCentralizer (inv_mem hxC) (hK.2.1 ha))
      have h4 : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers d ⊓ Subgroup.zpowers e :=
        ⟨hPP ▸ h1, hCK _ h2 h3⟩
      rw [hde, Subgroup.mem_bot] at h4
      have : x * a = a * x := by
        calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
          _ = a * x := by rw [h4, one_mul]
      exact this.symm
    have hsup := Sec15.isElemAbelian_sup_zpowers hE3 (hPexp x hx) hxcomm
    rw [← hEmax _ hsup le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have heA : e ∈ A := Sec15.mem_of_mem_partTwoF h.mem_partTwoF he3 (fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPe y (hAP hy)))
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAP.trans hPNK
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := hK.2.1
  have hCA : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e := by
    refine le_antisymm (fun x hx => hCP x (hAP hx.1) hx.2) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨heA, (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _).2⟩
  have hLstep : ∀ r : G, r ∈ Subgroup.normalizer (L : Set G) → (∀ a ∈ E, r * a = a * r) →
      (∃ k : ℕ, r ^ 3 ^ k = 1) → ∃ β ∈ E ⊓ L, β⁻¹ * r ∈ Sec4.thetaQuotCentralizer L :=
    fun r hrN hrE hr3 => exists_mem_inv_mul_mem_of_commute inf_le_right hB3 hEL9 hBab hZL hinn
      hab9 hrN (fun b hb => hrE b hb.1) hr3
  have hCT : ∀ T : Subgroup G, IsPGroup 3 T → E ≤ T → T ≤ Subgroup.normalizer (K : Set G) →
      ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e :=
    fun T hT hET hTK => mem_zpowers_of_mem_thetaQuotCentralizer hE3 hEmax hEdec hU hLH hc3 he3
      heL hce hCK hCL hLstep hT hET hTK
  obtain ⟨hx₀N, π, p, f, Fld, _, hPi, hq, ψ, y₀, hy₀, hy₀3, hx₀act⟩ := hx₀type
  have hx₀ψ : ActsPGL ψ x₀ y₀ := ⟨hx₀N, hy₀, hx₀act⟩
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    (facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hq2 : 2 < p ^ f := Item138Proof.two_lt_of_mulEquiv hKq hPi hq ψ
  haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Fld)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hKact : ∀ k ∈ K, ∃ s ∈ slPi π 3 (p ^ f) Fld, ActsPGL ψ k s := by
    intro k hk
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (ψ ((⟨k, hk⟩ : K) :
      K ⧸ aschbacherSolvableCore 3 K)).2
    exact ⟨s, hs, actsPGL_of_mem hπ hk hs hse.symm⟩
  have hAact := actsPGL_of_maximal hKq hA3 hAmax hA27 hAN heA he1 hCA hPi hq hq2 ψ
  have hEact := actsPGL_of_maximal hKq hE3 hEmax hE27 hEN heE he1 hCE hPi hq hq2 ψ
  have hAE : A ⊔ E = P := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAP hEP) ?_
    have hEsup : E < A ⊔ E := by
      refine lt_of_le_of_ne le_sup_right fun h' => hEA ?_
      have hAE' : A ≤ E := h' ▸ le_sup_left
      exact (Subgroup.eq_of_le_of_card_ge hAE' (by rw [hA27, hE27])).symm
    have hdvd : Nat.card (A ⊔ E : Subgroup G) ∣ 81 := hP81 ▸ Subgroup.card_dvd_of_le
      (sup_le hAP hEP)
    have hdvd2 : 27 ∣ Nat.card (A ⊔ E : Subgroup G) := hE27 ▸ Subgroup.card_dvd_of_le le_sup_right
    have hne : Nat.card (A ⊔ E : Subgroup G) ≠ 27 := fun h27 =>
      hEsup.ne (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h27, hE27]))
    obtain ⟨n, hn⟩ := hdvd2
    rw [hP81]
    have : n ∣ 3 := by
      rw [hn, show (81 : ℕ) = 27 * 3 by norm_num] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h1 | h1
    · exact absurd (by rw [hn, h1, mul_one]) hne
    · rw [hn, h1]
  have hPact : ∀ x ∈ P, ∃ y, ActsPGL ψ x y := by
    intro x hx
    have hx' : x ∈ ((A ⊔ E : Subgroup G) : Set G) := hAE ▸ hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A E (hAP.trans hPNE)] at hx'
    obtain ⟨a, ha, ε, hε, rfl⟩ := hx'
    obtain ⟨ya, hya⟩ := hAact a ha
    obtain ⟨yε, hyε⟩ := hEact ε hε
    exact ⟨ya * yε, hya.mul hyε⟩
  have hy₀n := mk_not_mem_projImage_slPi_of_type3 hPi hq hy₀ hy₀3
  have hPKE : P ≤ K ⊔ E := by
    intro x hx
    obtain ⟨y, hy⟩ := hPact x hx
    obtain ⟨jj, s, hs, hys⟩ := exists_zpow_mul_of_mem_glPi hPi hq hq2 hy₀ hy₀n hy.2.1
    obtain ⟨z, hz⟩ := ψ.surjective ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hkact : ActsPGL ψ k s := actsPGL_of_mem hπ hk hs (by rw [hz])
    have hx'act := (hx₀ψ.zpow hπ (-jj)).mul hy
    have hcls : ProjGenLinGroup.mk (y₀ ^ (-jj) * y) = ProjGenLinGroup.mk s := by
      rw [map_mul, map_zpow, hys, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    have hkx := hkact.inv_mul_mem_thetaQuotCentralizer hx'act hcls.symm
    have hx'P : x₀ ^ (-jj) * x ∈ P := mul_mem (P.zpow_mem (hEP hx₀E) _) hx
    have hmem := mem_sup_zpowers_of_inner (K := K) (P := P) (e := e) hZK hP3 hPNK
      (fun T hT hPT hTK => hCT T hT (hEP.trans hPT) hTK) hx'P hk hkx
    have hx0 : x = x₀ ^ jj * (x₀ ^ (-jj) * x) := by
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [hx0]
    refine mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hx₀E _)) ?_
    exact (sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right heE)) :
      K ⊔ Subgroup.zpowers e ≤ K ⊔ E) hmem
  refine ⟨hPKE, ?_⟩
  have hKEN : K ⊔ E ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hEN
  have hKEact : ∀ x ∈ K ⊔ E, ∃ y, ActsPGL ψ x y := by
    intro x hx
    have hx' : x ∈ ((E ⊔ K : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E K hEN] at hx'
    obtain ⟨ε, hε, k, hk, rfl⟩ := hx'
    obtain ⟨yε, hyε⟩ := hEact ε hε
    obtain ⟨s, -, hks⟩ := hKact k hk
    exact ⟨yε * s, hyε.mul hks⟩
  have hKEe : ∀ x ∈ K ⊔ E, x * e = e * x := by
    have hle : K ⊔ E ≤ Subgroup.centralizer ({e} : Set G) :=
      sup_le hD.le_centralizer (fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hy heE))
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := K ⊔ E)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup ↥(K ⊔ E)).map (K ⊔ E).subtype with hTdef
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T (K ⊔ E) := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun y hy =>
    ⟨⟨y, hPKE hy⟩, hQ (show (⟨y, _⟩ : ↥(K ⊔ E)) ∈ P.subgroupOf (K ⊔ E) from hy), rfl⟩
  have hT3 : IsPGroup 3 T := hTsyl.isPGroup
  have hTKE : T ≤ K ⊔ E := hTsyl.le
  have hPL : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    hPsyl.inf_of_le_normalizer le_sup_right (sup_le h.le_normalizer Subgroup.le_normalizer)
  have hAcL : A ≤ Subgroup.zpowers c ⊔ L := le_zpowers_sup_of_m12 h131 hspor h ⟨φM⟩
  have hPcL : P ≤ Subgroup.zpowers c ⊔ L := hPsyl.le.trans (sup_le hAcL le_sup_right)
  have hPdec : ∀ x ∈ P, ∃ m : ℤ, ∃ l ∈ P ⊓ L, x = c ^ m * l := by
    intro x hx
    obtain ⟨m, l, hl, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup h.le_centralizer (hPcL hx)
    refine ⟨m, l, ⟨?_, hl⟩, rfl⟩
    have := P.mul_mem (P.inv_mem (P.zpow_mem hcP m)) hx
    rwa [inv_mul_cancel_left] at this
  obtain ⟨sb, hsb, hbact⟩ := hKact b hbK
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hPi hq
  have hy₀cube : ProjGenLinGroup.mk y₀ ^ 3 = 1 := by
    rw [← map_pow, Sec4.mk_eq_one_iff_mem_statedScalars]
    exact Sec4.mem_statedScalars_of_mem_zPi hPi hq hτ hτ1 hy₀3.2.1
  have hb3 : ProjGenLinGroup.mk sb ^ 3 = 1 := by
    have h1 := hbact.pow hπ 3
    rw [hE3.2 b hbE] at h1
    have h2 := ActsPGL.mk_eq hPi hq h1 (actsPGL_one hπ)
    rwa [map_pow, map_one] at h2
  have hby : ProjGenLinGroup.mk sb * ProjGenLinGroup.mk y₀ =
      ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk sb :=
    hbact.commute hPi hq hx₀ψ (hD.commute hbE hx₀E)
  have hsbPSL : ProjGenLinGroup.mk sb ∈ projImage (slPi π 3 (p ^ f) Fld) :=
    Subgroup.mem_map_of_mem _ hsb
  have hbn : ProjGenLinGroup.mk sb ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₀) := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [zpow_eq_zpow_emod_of_pow_three hy₀cube] at hm
    have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm3 with h0 | h1 | h2
    · rw [h0, zpow_zero] at hm
      apply hb1
      have hbC := hbact.mem_thetaQuotCentralizer hm.symm
      have hbθ := Sec17.inf_thetaQuotCentralizer_le hZK ⟨hbK, hbC⟩
      exact eq_one_of_mem_of_pow_three_pow' hθK3 hbθ (k := 1) (by simpa using hE3.2 b hbE)
    · rw [h1, zpow_one] at hm
      exact hy₀n (hm ▸ hsbPSL)
    · rw [h2] at hm
      apply hy₀n
      have h4 : ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk y₀ ^ (2 : ℤ) = 1 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_succ', hy₀cube]
      rw [eq_inv_of_mul_eq_one_left h4, hm]
      exact inv_mem hsbPSL
  have hTP : T = P := by
    by_contra hne
    have hPT' : P.subgroupOf T < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      refine le_antisymm (fun y hy => ?_) hPT
      have : (⟨y, hy⟩ : T) ∈ P.subgroupOf T := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    haveI : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hT3
    have hlt := Group.normalizerCondition_of_isNilpotent (G := ↥T) (P.subgroupOf T) hPT'
    obtain ⟨g₀, hg₀N, hg₀P⟩ :
        ∃ g₀ ∈ Subgroup.normalizer ((P.subgroupOf T : Subgroup T) : Set T),
          g₀ ∉ P.subgroupOf T :=
      SetLike.not_le_iff_exists.mp (fun h => lt_irrefl _ (lt_of_lt_of_le hlt h))
    set g : G := (g₀ : G) with hgdef
    have hgT : g ∈ T := g₀.2
    have hgP : g ∉ P := fun h' => hg₀P (Subgroup.mem_subgroupOf.mpr h')
    have hgN : g ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨y, hPT hy⟩).mp
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hy
        have hyT : y ∈ T := by
          have h1 : g⁻¹ * (g * y * g⁻¹) * g ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem hgT) (hPT hy)) hgT
          have e' : g⁻¹ * (g * y * g⁻¹) * g = y := by group
          rwa [e'] at h1
        have h2 := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨y, hyT⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h2
    have hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hT3 ⟨g, hgT⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hge : g * e = e * g := hKEe g (hTKE hgT)
    have hgd : g * d * g⁻¹ = d := by
      have hgdP : g * d * g⁻¹ ∈ ⁅P, P⁆ := by
        rw [← map_commutator_eq_of_mem_normalizer hgN]
        exact ⟨d, hPP ▸ Subgroup.mem_zpowers d, rfl⟩
      rw [hPP] at hgdP
      obtain ⟨k, hk⟩ := hg3
      exact conj_eq_of_mem_zpowers_of_pow_three_pow hd3 hgdP hk
    have hgd' : Commute g d := by
      show g * d = d * g
      calc g * d = g * d * g⁻¹ * g := by group
        _ = d * g := by rw [hgd]
    have hgci : Commute g (c ^ i) := by
      have hci : c ^ i = e * (d ^ j)⁻¹ := by rw [hij]; group
      rw [hci]
      exact (show Commute g e from hge).mul_right (hgd'.zpow_right j).inv_right
    have hgc : Commute g c := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hczp
      rw [← hm]
      exact hgci.zpow_right m
    have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      centralizer_le_normalizer_zpowers c
        (Subgroup.mem_centralizer_singleton_iff.mpr hgc.eq)
    have hgL : g ∈ Subgroup.normalizer (L : Set G) := hLH hgH
    have hgPL : g ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyP, hyL⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgN y).mp hyP,
          (Subgroup.mem_normalizer_iff.mp hgL y).mp hyL⟩
      · rintro ⟨hyP, hyL⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgN y).mpr hyP,
          (Subgroup.mem_normalizer_iff.mp hgL y).mpr hyL⟩
    obtain ⟨y, hyPL, hyg⟩ := exists_mem_inv_mul_mem_of_normalizes inf_le_right hPL.isPGroup
      hPL.card_eq hZL hinn hgL hgPL hg3
    set g' := y⁻¹ * g with hg'def
    have hg'T : g' ∈ T := mul_mem (inv_mem (hPT hyPL.1)) hgT
    have hg'P : g' ∉ P := fun h' => hgP (by
      have := P.mul_mem hyPL.1 h'
      rwa [hg'def, mul_inv_cancel_left] at this)
    have hg'N : g' ∈ Subgroup.normalizer (P : Set G) :=
      mul_mem (inv_mem (Subgroup.le_normalizer hyPL.1)) hgN
    have hg'PL : ∀ w ∈ P ⊓ L, g' * w = w * g' := by
      intro w hw
      have h1 : w⁻¹ * (g' * w * g'⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
        (Sec6.mem_thetaQuotCentralizer_iff.mp hyg).2 w hw.2
      have h2 : w⁻¹ * (g' * w * g'⁻¹) ∈ P :=
        mul_mem (inv_mem hw.1) ((Subgroup.mem_normalizer_iff.mp hg'N w).mp hw.1)
      have h3 : w⁻¹ * (g' * w * g'⁻¹) = 1 :=
        eq_one_of_mem_of_pow_three_pow' hθL3 h1 (k := 1) (by simpa using hPexp _ h2)
      have h4 : g' * w * g'⁻¹ = w := by
        calc g' * w * g'⁻¹ = w * (w⁻¹ * (g' * w * g'⁻¹)) := by group
          _ = w := by rw [h3, mul_one]
      calc g' * w = g' * w * g'⁻¹ * g' := by group
        _ = w * g' := by rw [h4]
    have hg'c : Commute g' c := by
      have hyc : Commute y⁻¹ c := (show Commute y c from hLc y hyPL.2).inv_left
      exact hyc.mul_left hgc
    have hg'P' : ∀ x ∈ P, Commute g' x := by
      intro x hx
      obtain ⟨m, l, hl, rfl⟩ := hPdec x hx
      exact (hg'c.zpow_right m).mul_right (hg'PL l hl)
    obtain ⟨y', hy'⟩ := hKEact g' (hTKE hg'T)
    have hc0 := hy'.commute hPi hq hx₀ψ (hg'P' x₀ (hEP hx₀E))
    have hcb := hy'.commute hPi hq hbact (hg'P' b (hEP hbE))
    have hmem := mem_sup_of_commute_type3 hPi hq hy₀3 hb3 hby hbn hc0 hcb
    have hyN : Subgroup.zpowers (ProjGenLinGroup.mk y₀) ≤
        Subgroup.normalizer ((Subgroup.zpowers (ProjGenLinGroup.mk sb) :
          Subgroup (ProjGenLinGroup (Fin 3) Fld)) : Set (ProjGenLinGroup (Fin 3) Fld)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro z hz
      obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((Commute.zpow_left hby v)).eq
    have hmem' : ProjGenLinGroup.mk y' ∈ ((Subgroup.zpowers (ProjGenLinGroup.mk y₀) ⊔
        Subgroup.zpowers (ProjGenLinGroup.mk sb) : Subgroup _) :
          Set (ProjGenLinGroup (Fin 3) Fld)) := hmem
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyN] at hmem'
    obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := hmem'
    obtain ⟨u, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
    obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
    have hact2 := (hx₀ψ.zpow hπ u).mul (hbact.zpow hπ v)
    have hcls : ProjGenLinGroup.mk (y₀ ^ u * sb ^ v) = ProjGenLinGroup.mk y' := by
      rw [map_mul, map_zpow, map_zpow]
      exact ha
    have hmemC := hact2.inv_mul_mem_thetaQuotCentralizer hy' hcls
    have haE : x₀ ^ u * b ^ v ∈ E := mul_mem (Subgroup.zpow_mem _ hx₀E u)
      (Subgroup.zpow_mem _ hbE v)
    have haT : (x₀ ^ u * b ^ v)⁻¹ * g' ∈ T := mul_mem (inv_mem (hPT (hEP haE))) hg'T
    have he' := hCT T hT3 (hEP.trans hPT) (hTKE.trans hKEN) _ haT hmemC
    have hg'E : g' ∈ E := by
      have := E.mul_mem haE (Subgroup.zpowers_le.mpr heE he')
      rwa [mul_inv_cancel_left] at this
    exact hg'P (hEP hg'E)
  have hcardT := hTsyl.card_eq
  rw [hTP, hP81, show (81 : ℕ) = 3 ^ 4 by norm_num] at hcardT
  exact (Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3)) hcardT).symm

end Main

section InL

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem apply_eq_of_mem_zpowers_of_pow_three {E : Type*} [Group E] (σ : MulAut E)
    (hσ : σ ^ 3 = 1) {c : E} (hc3 : c ^ 3 = 1) (hσc : σ c ∈ Subgroup.zpowers c) : σ c = c := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hσc
  have hpow : ∀ n : ℕ, (σ ^ n) c = c ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_zpow, ← hm, ← _root_.zpow_mul, pow_succ']
  have h2 := hpow 3
  rw [hσ, MulAut.one_apply] at h2
  have hmod : (m ^ 3) % 3 = m % 3 := by
    have : ((m ^ 3 : ℤ) : ZMod 3) = (m : ZMod 3) := by
      push_cast
      exact ZMod.pow_card _
    exact (ZMod.intCast_eq_intCast_iff' _ _ 3).mp this
  calc σ c = c ^ m := hm.symm
    _ = c ^ (m % 3) := zpow_eq_zpow_emod_of_pow_three hc3 m
    _ = c ^ ((m ^ 3) % 3) := by rw [hmod]
    _ = c ^ (m ^ 3) := (zpow_eq_zpow_emod_of_pow_three hc3 _).symm
    _ = c := h2.symm

theorem false_of_mem (h131 : Item131) (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {P E F : Subgroup G} {t : G} (hcfg : Config137 A c L P E F t) (hST : HypS E ∨ HypT E)
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {e : G} {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heZ : e ∈ Subgroup.centralizer (P : Set G)) (hec : e ∉ Subgroup.zpowers c)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA e K E)) (heL : e ∈ L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hcfg' := hcfg
  obtain ⟨hPsyl, hAP, -, -, hΔ, -, -, -, -, -, -, -, -, -, -, hEdec, -⟩ := hcfg'
  obtain ⟨d, hdL, -, hd3, -, hZc, -, hP81, hPexp⟩ :=
    exists_commutator_eq_zpowers_of_isSylowOf h131 hspor h414 h hM hPsyl hAP
  have hEΔ : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27} := by
    rw [hΔ]
    exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨hEP, hE3, hE27⟩ := hEΔ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e hD.mem_A
  have he1 : e ≠ 1 := hD.ne_one
  have heE : e ∈ E := hD.mem_A
  have hPe : ∀ x ∈ P, x * e = e * x := fun x hx => Subgroup.mem_centralizer_iff.mp heZ x hx
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  have hLH := normalizer_zpowers_le_normalizer_of_m12 h131 hspor h hM
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hZL : ∀ z ∈ P, (∀ x ∈ P, z * x = x * z) → z ∈ L → z ∈ Subgroup.zpowers d := by
    intro z hz hzc hzL
    obtain ⟨α, β, rfl⟩ := hZc z hz hzc
    have hcα : c ^ α ∈ L := by
      have e1 : c ^ α = c ^ α * d ^ β * (d ^ β)⁻¹ := by group
      rw [e1]
      exact L.mul_mem hzL (L.inv_mem (L.zpow_mem hdL β))
    have hcα1 : c ^ α = 1 := by
      have := Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem_zpowers c α, hcα⟩
      rwa [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at this
    rw [hcα1, one_mul]
    exact Subgroup.zpow_mem_zpowers d β
  have hed : e ∈ Subgroup.zpowers d := hZL e (hEP heE) (fun x hx => (hPe x hx).symm) heL
  have hde : Subgroup.zpowers d ≤ Subgroup.zpowers e := by
    have hle : Subgroup.zpowers e ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hed
    have hd1 : d ≠ 1 := fun h1 => he1 (by rw [h1, Subgroup.zpowers_one_eq_bot] at hed; exact hed)
    rw [Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_zpowers_of_pow_three hd3 hd1, card_zpowers_of_pow_three he3 he1])]
  obtain ⟨heK, ⟨φaut⟩, -⟩ := facts131_of_isZ3PGLThreePi h131 hspor hD hPGL
  set σ := φaut.symm (Multiplicative.ofAdd (1 : ZMod 3)) with hσ
  have hσ1 : (σ : MulAut E) ≠ 1 := by
    intro h1
    have h2 : σ = 1 := Subtype.ext h1
    have h3 : Multiplicative.ofAdd (1 : ZMod 3) = φaut 1 := by
      rw [← h2, hσ, MulEquiv.apply_symm_apply]
    rw [map_one φaut, ofAdd_eq_one] at h3
    exact absurd h3 one_ne_zero
  have hσ3 : (σ : MulAut E) ^ 3 = 1 := by
    have h1 : σ ^ 3 = 1 := by
      apply φaut.injective
      rw [map_pow, map_one, hσ, MulEquiv.apply_symm_apply, ← ofAdd_nsmul, ofAdd_eq_one,
        nsmul_eq_mul, mul_one]
      exact ZMod.natCast_self 3
    exact congrArg Subtype.val h1
  obtain ⟨k, hkN, hkK, hkσ⟩ := Sec4.mem_autIn_iff.mp σ.2
  have hkL : k ∈ Subgroup.normalizer (L : Set G) := hLH (hU hkN)
  have hcE : c ∈ E := hEdec ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hσc : (σ : MulAut E) ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
    refine apply_eq_of_mem_zpowers_of_pow_three _ hσ3 (Subtype.ext (by simpa using hc3)) ?_
    rw [← hkσ]
    have h1 : k * c * k⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hU hkN) c).mp (Subgroup.mem_zpowers c)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, Sec4.normalizerMonoidHom_apply_coe]
    exact hm
  have hkc : k * c * k⁻¹ = c := by
    have := congrArg Subtype.val hσc
    rwa [← hkσ, Sec4.normalizerMonoidHom_apply_coe] at this
  obtain ⟨a, ha⟩ : ∃ a : E, (σ : MulAut E) a ≠ a := by
    by_contra hall
    push Not at hall
    exact hσ1 (MulEquiv.ext hall)
  have haL : (a : G) ∈ Subgroup.zpowers c ⊔ L :=
    (hEdec ▸ sup_le_sup_left inf_le_right _ : E ≤ Subgroup.zpowers c ⊔ L) a.2
  obtain ⟨m, l, hl, hal⟩ := exists_zpow_mul_of_mem_zpowers_sup h.le_centralizer haL
  have hlE : l ∈ E := by
    have e1 : l = (c ^ m)⁻¹ * (a : G) := by rw [hal]; group
    rw [e1]
    exact E.mul_mem (E.inv_mem (E.zpow_mem hcE m)) a.2
  have hkl : k * l * k⁻¹ ≠ l := by
    intro hkl
    apply ha
    apply Subtype.ext
    rw [← hkσ, Sec4.normalizerMonoidHom_apply_coe, hal]
    calc k * (c ^ m * l) * k⁻¹ = (k * c * k⁻¹) ^ m * (k * l * k⁻¹) := by rw [conj_zpow]; group
      _ = c ^ m * l := by rw [hkc, hkl]
  set v := k * l * k⁻¹ * l⁻¹ with hvdef
  have hvE : v ∈ E := mul_mem ((Subgroup.mem_normalizer_iff.mp hkN l).mp hlE) (inv_mem hlE)
  have hvL : v ∈ L := mul_mem ((Subgroup.mem_normalizer_iff.mp hkL l).mp hl) (inv_mem hl)
  have hvK : v ∈ K := by
    have hlK : l * k⁻¹ * l⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hK.2.1 hlE) _).mp (inv_mem hkK)
    have : v = k * (l * k⁻¹ * l⁻¹) := by rw [hvdef]; group
    rw [this]
    exact mul_mem hkK hlK
  have hv1 : v ≠ 1 := fun h1 => hkl (mul_inv_eq_one.mp h1)
  have hEK3 : Nat.card (E ⊓ K : Subgroup G) ≤ 3 := by
    by_contra hgt
    push Not at hgt
    apply not_le_zpowers_sup_of_isZ3PGLThreePi hD hPGL
    have hcomm : ∀ x ∈ Subgroup.zpowers e, ∀ y ∈ E ⊓ K, x * y = y * x := by
      intro x hx y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hD.commute hD.mem_A hy.1) n).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot he3 heK).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three he3 he1] at hcard
    have hle : Subgroup.zpowers e ⊔ (E ⊓ K) ≤ E := sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left
    have hdvd : Nat.card (E ⊓ K : Subgroup G) ∣ 27 := hE27 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h9 : 9 ≤ Nat.card (E ⊓ K : Subgroup G) := by
      obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card (E ⊓ K : Subgroup G) ∣ 3 ^ 3 by simpa using hdvd)
      rw [hn] at hgt ⊢
      have h2 : 2 ≤ n := by
        by_contra h'
        push Not at h'
        interval_cases n <;> norm_num at hgt
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have heq : Subgroup.zpowers e ⊔ (E ⊓ K) = E := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hE27]; omega)
    rw [← heq]
    exact sup_le_sup_left inf_le_right _
  have hEKv : ∀ x ∈ E ⊓ K, x ∈ Subgroup.zpowers v := by
    intro x hx
    have hle : Subgroup.zpowers v ≤ E ⊓ K := Subgroup.zpowers_le.mpr ⟨hvE, hvK⟩
    have hv3 : v ^ 3 = 1 := hE3.2 v hvE
    have heq : Subgroup.zpowers v = E ⊓ K := Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_zpowers_of_pow_three hv3 hv1]; exact hEK3)
    exact heq ▸ hx
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card hEP hE27 hP81
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    mem_normalizer_of_mem_lA hK he3 heK hvE hvK hv1 (hPNE hx) (hPe x hx)
  have hvZ : ∀ x ∈ P, v * x = x * v := by
    intro x hx
    have h1 : x * v * x⁻¹ ∈ Subgroup.zpowers v :=
      hEKv _ ⟨(Subgroup.mem_normalizer_iff.mp (hPNE hx) v).mp hvE,
        (Subgroup.mem_normalizer_iff.mp (hPNK hx) v).mp hvK⟩
    have h2 := conj_eq_of_mem_zpowers_of_pow_three_pow (hE3.2 v hvE) h1 (k := 1)
      (by simpa using hPexp x hx)
    calc v * x = (x * v * x⁻¹) * x := by rw [h2]
      _ = x * v := by group
  have hvd := hZL v (hEP hvE) hvZ hvL
  have : v ∈ Subgroup.zpowers e ⊓ K := ⟨hde hvd, hvK⟩
  rw [zpowers_inf_eq_bot he3 heK, Subgroup.mem_bot] at this
  exact hv1 this

end InL

section Assembly


theorem item137PGLSylow_of (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hK18 : KFacts.KS18M12) :
    RonanItem137.Item137PGLSylow := by
  intro G _ _ A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec hPGL
  by_cases heL : e ∈ L
  · exact (false_of_mem h131 hspor h414 h hM hcfg hST hU heΩ hK heZ hec hPGL heL).elim
  · exact item137PGLSylow_of_not_mem h131 hspor h414 hK18 G A c L h hM P E F t hcfg hST hU e K
      heΩ hK heZ hec hPGL heL

theorem item137InvertPGL_of (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hK18 : KFacts.KS18M12) : Item137InvertPGL :=
  RonanItem137.item137InvertPGL_of_sylow (item137PGLSylow_of h131 hspor h414 hK18)

end Assembly

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
