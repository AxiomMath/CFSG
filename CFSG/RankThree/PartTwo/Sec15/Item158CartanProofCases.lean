module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofPair
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofFuse
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProof
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148StepRank
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)

@[expose] noncomputable def Step158CartanNineR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∃ E F : Subgroup G, E ≤ P ∧ F ≤ P ∧
        CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L ∧
        CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ F ≤ Subgroup.zpowers c ⊔ L ∧
        Nat.card (F ⊓ L : Subgroup G) = 9 ∧
        (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
        F ≤ Subgroup.normalizer (E : Set G)

namespace Proof158Cartan

variable {G : Type} [Group G] [Finite G]

theorem exists_model {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), Sec4.PiField π p e K ∧ Sec4.ModThree π (p ^ e) ∧
      2 < p ^ e ∧ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        projImage (Sec4.slPi π 3 (p ^ e) K)) := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model he hL3
  refine ⟨π, K, inferInstance, hK, hq, ?_, ⟨φ⟩⟩
  have hp : p.Prime := Fact.out
  have h2 : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  by_contra hle
  have h2' : p ^ e = 2 := by omega
  cases π
  · have hπ : (false : Bool) = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
      fun _ => hK.unitary
    have hsol : Group.IsSolvable (projImage (Sec4.glPi false 3 (p ^ e) K)) :=
      isSolvable_projImage_glPi_two hK h2'
    have hle : projImage (Sec4.slPi false 3 (p ^ e) K) ≤ projImage (Sec4.glPi false 3 (p ^ e) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    have hsol' : Group.IsSolvable (projImage (Sec4.slPi false 3 (p ^ e) K)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hsolL : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hsolL
  · change p ^ e % 3 = 1 at hq
    omega

theorem facts_of_sylow {A L Y P : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (h3L : 3 ∣ Nat.card L)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G))) :
    IsPGroup 3 P ∧ P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      P ≤ Subgroup.normalizer (L : Set G) ∧
      P ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, rfl⟩ := hP
  have hPK : (Q : Subgroup _).map (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G)).subtype ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G) :=
    Subgroup.map_subtype_le _
  refine ⟨Q.isPGroup'.map _, hPK.trans inf_le_left,
    (hPK.trans inf_le_left).trans (Sec16.normalizer_zpowers_le_normalizer_L hR h3L),
    (hPK.trans inf_le_right).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)⟩

theorem actBar_zpow_eq_one {L : Subgroup G} {c : G} (hLc : ∀ l ∈ L, l * c = c * l) (k : ℤ)
    (hk : c ^ k ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1 :=
  actBar_eq_one_of_commute hk fun l hl => (Commute.zpow_right (hLc l hl) k).eq

theorem cartanP_inner
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    {P : Subgroup G} (hAP : A ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (hΩ : A ≠ omegaOneThree P) (hcL : c ∉ L) (h9AL : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ E F : Subgroup G, E ≤ P ∧ F ≤ P ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn E L ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ F ≤ Subgroup.zpowers c ⊔ L ∧
      Nat.card (F ⊓ L : Subgroup G) = 9 ∧
      (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
      F ≤ Subgroup.normalizer (E : Set G) := by
  have hD := hR.toSec13Data
  have hA := hD.isElemAbelian
  have hA27 := hD.card_eq
  have hcA := hD.mem_A
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9AL ▸ Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨hP3, hPH, hPL, hPU⟩ := facts_of_sylow hR h3L hP
  have hFE : partTwoF G = partTwoE G :=
    (hR.toTheoremFourHyp.partTwoF_eq_partTwoE hR.partTwoS_eq).1
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Sec19.Step1914TriProof.eq_zpowers_sup_of_nine_le ⟨hA, hA27⟩ hcA hcL (by rw [h9AL])
  have hsecA : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a haA haC
    have h1 := hD.mem_lA.2.2.1
    rw [sectionCentralizer_eq_inf hD.le_normalizer] at h1
    have h2 : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := ⟨haA, haC⟩
    rw [h1] at h2
    exact h2
  obtain ⟨π, K, _, hK, hq, hq2, ⟨φ⟩⟩ := exists_model hD.mem_thetaComponentsAt he hL3
  obtain ⟨E, hEP, -, hE, hE27, hsec, hTC, hAE⟩ :=
    exists_cartan_of_pair hFE hcL hc3 hLc hY.2.2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hPU hPH hPL hP3 hAP hA hA27 hAeq
      hsecA hΩ hK hq hq2 h9 φ
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hA.2 x hx.1⟩
    have h3 : (x : G) * y = y * x :=
      congrArg Subtype.val (hA.1.is_comm.comm (⟨x, x.2.1⟩ : ↥A) ⟨y, y.2.1⟩)
    exact Subtype.ext h3
  refine ⟨E, A, hEP, hAP, hE, hE27, hsec, hTC, hA, hA27, ?_, h9AL, fun y hy hy1 z hz hz1 => ?_,
    hAE⟩
  · rw [hAeq]
    exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  · obtain ⟨w, hwL, -, hw⟩ := exists_conj_eq_of_autIn hc3 hcL hLc hAeq hB h9AL hQ hy hz hy1 hz1
    exact ⟨w, hwL, hw⟩

theorem cartanP_pgl
    (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    (hmeet : MeetsY4 A (lB A) L Y) {P : Subgroup G} (hAP : A ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (hcL : c ∉ L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    ∃ E F : Subgroup G, E ≤ P ∧ F ≤ P ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn E L ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ F ≤ Subgroup.zpowers c ⊔ L ∧
      Nat.card (F ⊓ L : Subgroup G) = 9 ∧
      (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
      F ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := hR.toSec13Data
  have hA := hD.isElemAbelian
  have hcA := hD.mem_A
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hFE : partTwoF G = partTwoE G :=
    (hR.toTheoremFourHyp.partTwoF_eq_partTwoE hR.partTwoS_eq).1
  obtain ⟨X, hX4, hXLY⟩ := hmeet
  obtain ⟨B, hBX, hB, hB9⟩ := step158InnerRank_of_route h134 h48 h148 G A c L hR p e he hL3 hPGL
    hx X hX4 (hXLY.trans inf_le_left)
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (hB9 ▸ Subgroup.card_dvd_of_le (hBX.trans
      (hXLY.trans inf_le_left)))
  obtain ⟨hP3, hPH, hPL, hPU⟩ := facts_of_sylow hR h3L hP
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hBK : B ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) := by
    intro b hb
    have hbL : b ∈ L := hXLY (hBX hb) |>.1
    have hbY : b ∈ Y := hXLY (hBX hb) |>.2
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.le_normalizer hbY⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hbc : b * c = c * b := hLc b hbL
    constructor
    · intro hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have : b * c ^ k * b⁻¹ = c ^ k := by
        rw [(Commute.zpow_right hbc k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have h1 : b * c ^ k * b⁻¹ = c ^ k := by
        rw [(Commute.zpow_right hbc k).eq, mul_inv_cancel_right]
      have h2 : b * z * b⁻¹ = b * c ^ k * b⁻¹ := by rw [h1, hk]
      have : z = c ^ k := by
        calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
          _ = b⁻¹ * (b * c ^ k * b⁻¹) * b := by rw [h2]
          _ = c ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  obtain ⟨k, hkK, hBk⟩ := Proof158Inner.exists_conj_le_of_isSylowOf hP hB3 hBK
  set D := B.map (MulAut.conj k).toMonoidHom with hDdef
  have hDL : D ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
      Sec16.normalizer_zpowers_le_normalizer_L hR h3L hkK.1
    exact (Subgroup.mem_normalizer_iff.mp hkN b).mp (hXLY (hBX hb)).1
  have hDe : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_map hB _
  have hD9 : Nat.card D = 9 := by
    rw [hDdef, Subgroup.card_map_of_injective (MulAut.conj k).injective, hB9]
  have hDP : D ≤ P := hBk
  have hDc : ∀ d ∈ D, d * c = c * d := fun d hd => hLc d (hDL hd)
  set F := D ⊔ Subgroup.zpowers c with hFdef
  have hF : CFSG.Assembly.IsElemAbelian 3 F := isElemAbelian_sup_zpowers hDe hc3 hDc
  have hcF : c ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hFP : F ≤ P := sup_le hDP (Subgroup.zpowers_le.mpr (hAP hcA))
  have hF27 : Nat.card F = 27 := by
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        rw [← hDc d hd, mul_inv_cancel_right]
        exact hd
      · intro hd
        have h1 : c⁻¹ * (c * d * c⁻¹) * c = d := by group
        rw [← h1]
        have h2 := hDc _ hd
        have h3 : c⁻¹ * (c * d * c⁻¹) * c = c * d * c⁻¹ := by
          calc c⁻¹ * (c * d * c⁻¹) * c = c⁻¹ * ((c * d * c⁻¹) * c) := by group
            _ = c⁻¹ * (c * (c * d * c⁻¹)) := by rw [h2]
            _ = c * d * c⁻¹ := by group
        rw [h3]
        exact hd
    have h1 := Sec6.card_sup_mul_card_inf hcN
    have hinf : Subgroup.zpowers c ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have h2 : g ∈ Subgroup.zpowers c ⊓ L := ⟨hg.1, hDL hg.2⟩
      rw [zpowers_inf_eq_bot hc3 hcL] at h2
      exact h2
    rw [hinf, Subgroup.card_bot, mul_one, card_zpowers_of_pow_three hc3 hc1, hD9] at h1
    rw [hFdef, sup_comm]
    omega
  have hFL : F ⊓ L = D := by
    refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left hDL)
    have hcD : ∀ t ∈ D, c * t * c⁻¹ ∈ D := fun t ht => by
      rw [← hDc t ht, mul_inv_cancel_right]
      exact ht
    obtain ⟨t, htD, m, -, hgt⟩ := exists_mul_pow_of_mem_sup hc3 hcD hg.1
    have hcm : c ^ m ∈ L := by
      have h1 : c ^ m = t⁻¹ * g := by rw [hgt]; group
      rw [h1]
      exact L.mul_mem (L.inv_mem (hDL htD)) hg.2
    have hcm1 : c ^ m = 1 := by
      have h2 : c ^ m ∈ Subgroup.zpowers c ⊓ L := ⟨Subgroup.npow_mem_zpowers c m, hcm⟩
      rw [zpowers_inf_eq_bot hc3 hcL] at h2
      exact h2
    rw [hgt, hcm1, mul_one]
    exact htD
  have hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L) := by
    rw [hFL, hFdef, sup_comm]
  have hZ := (facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hsecF : ∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a haF haC
    have hcD : ∀ t ∈ D, c * t * c⁻¹ ∈ D := fun t ht => by
      rw [← hDc t ht, mul_inv_cancel_right]
      exact ht
    obtain ⟨t, htD, m, -, rfl⟩ := exists_mul_pow_of_mem_sup hc3 hcD haF
    have htL : t ∈ L := hDL htD
    have hcmT : c ^ m ∈ Sec4.thetaQuotCentralizer L := by
      have hcN : c ^ m ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.pow_mem _ (hD.le_normalizer hcA) m
      have h1 := actBar_eq_one_of_commute hcN fun l hl => (Commute.pow_right (hLc l hl) m).eq
      exact (actBar_eq_one_iff ⟨c ^ m, hcN⟩).mp h1
    have htT : t ∈ Sec4.thetaQuotCentralizer L := by
      have h1 : t = (t * c ^ m) * (c ^ m)⁻¹ := by group
      rw [h1]
      exact Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hcmT)
    obtain ⟨-, htθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp htT
    have hcen : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨t, htL⟩) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H l =>
        have h1 := htθ l l.2
        obtain ⟨u, hu, hul⟩ := h1
        rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          QuotientGroup.eq]
        have hu' : (l : G)⁻¹ * (t * l * t⁻¹) = (u : G) := hul.symm
        have h2 : (⟨l, l.2⟩ * ⟨t, htL⟩ : ↥L)⁻¹ * (⟨t, htL⟩ * ⟨l, l.2⟩) =
            ⟨t, htL⟩⁻¹ * u * ⟨t, htL⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hu']
          group
        rw [h2]
        have h3 := (aschbacherSolvableCore_normal 3 ↥L).conj_mem _ hu (⟨t, htL⟩⁻¹)
        rwa [inv_inv] at h3
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    have ht1 : t = 1 := eq_one_of_mem_theta_of_isPGroup (hP3.to_le hDP) htD
      ⟨⟨t, htL⟩, hcen, rfl⟩
    rw [ht1, one_mul]
    exact Subgroup.npow_mem_zpowers c m
  obtain ⟨x, hxA, hx3⟩ := hx
  have hΩF : F ≠ omegaOneThree P := by
    intro hFΩ
    have hxΩ : x ∈ omegaOneThree P := Subgroup.subset_closure ⟨hAP hxA, hA.2 x hxA⟩
    rw [← hFΩ] at hxΩ
    have hcD : ∀ t ∈ D, c * t * c⁻¹ ∈ D := fun t ht => by
      rw [← hDc t ht, mul_inv_cancel_right]
      exact ht
    obtain ⟨t, htD, m, -, hxt⟩ := exists_mul_pow_of_mem_sup hc3 hcD hxΩ
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer hcA
    have hx' := Proof142Res.inducesTypeOn_mul_of_eq_one hx3
      (Subgroup.zpow_mem _ hcN (-(m : ℤ)))
      (actBar_zpow_eq_one hLc (-(m : ℤ)) (Subgroup.zpow_mem _ hcN (-(m : ℤ))))
    apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hD.mem_thetaComponentsAt hx'
    have h1 : x * c ^ (-(m : ℤ)) = t := by
      rw [hxt, zpow_neg, zpow_natCast]
      group
    rw [h1]
    exact hDL htD
  obtain ⟨π, K, _, hK, hq, hq2, ⟨φ⟩⟩ := exists_model hD.mem_thetaComponentsAt he hL3
  obtain ⟨E, hEP, -, hE, hE27, hsec, hTC, hFN⟩ :=
    exists_cartan_of_pair hFE hcL hc3 hLc hY.2.2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hPU hPH hPL hP3 hFP hF hF27 hFeq
      hsecF hΩF hK hq hq2 h9 φ
  refine ⟨E, F, hEP, hFP, hE, hE27, hsec, hTC, hF, hF27, ?_, by rw [hFL, hD9], ?_, hFN⟩
  · exact sup_le (hDL.trans le_sup_right) le_sup_left
  · intro y hy hy1 z hz hz1
    rw [hFL] at hy hz
    exact exists_conj_of_elemAbelian_nine he hL3 h9 hDL hDe hD9 hy hy1 hz hz1

end Proof158Cartan

open Proof158Cartan

theorem step158CartanP_of
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) (hNine : Step158CartanNineR) : Step158CartanP := by
  intro G _ _ A c L hR p e _ he hL3 Y hY hmeet P hAP hP hΩ
  by_cases h9 : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8
  · exact hNine G A c L hR p e he hL3 h9 Y hY hmeet P hAP hP hΩ
  have hD := hR.toSec13Data
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
      ⟨hcL, h9AL, -, hcase⟩ | ⟨-, -, hspor, -⟩ | ⟨hcL, hPGL, -, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ⟩ | ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
    · exact cartanP_inner hR he hL3 h9 hY hAP hP hΩ hcL h9AL hQ
    · exact (Proof1511.not_isoLThreePi_of_A7 ψ hL3).elim
    · exact (KFacts.KS14.not_isoLThreePi_M22 p e (isoLThreePi_of_mulEquiv148 ψ.symm hL3)).elim
  · rcases hspor with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact (Proof1511.not_isoLThreePi_of_prod_M12 hD φ hL3).elim
    · exact (Proof1511.not_isoLThreePi_of_prod_J2 hD φ hL3).elim
  · exact cartanP_pgl h134 h48 h148 hR he hL3 h9 hY hmeet hAP hP hcL hPGL hx
  · exact (hR.hypS.2.2 c hR.zpowers_mem_omegaA L hR.mem_lA hcL).elim

end CFSG.RankThree.PartTwo.Sec15
