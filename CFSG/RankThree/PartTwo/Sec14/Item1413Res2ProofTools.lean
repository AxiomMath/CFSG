module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofCase3
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartOne.KE8F.HyperGen
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.J2
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res2

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_zpowers_of_conj_mem {g x : G} (h : g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hle : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr h
  exact mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm.le)

theorem not_le_normalizer_zpowers_of_irreducible {A B K : Subgroup G} {a f : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) (hAa : A = Subgroup.zpowers a ⊔ B)
    (haB : Subgroup.zpowers a ⊓ B = ⊥) (hB9 : Nat.card B = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hfA : f ∈ A) (hf1 : f ≠ 1)
    (hfa : Subgroup.zpowers f ≠ Subgroup.zpowers a) :
    ¬ K ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := by
  intro hKf
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨i, hi, b, hb, rfl⟩ := exists_pow_mul_of_mem hA haA hAa hfA
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at hf1 hfa
    apply hfa
    have ha3 : a ^ 3 = 1 := hA.2 a haA
    interval_cases i
    · exact absurd (pow_zero a) hf1
    · rw [pow_one]
    · refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2))
        (Subgroup.zpowers_le.mpr ?_)
      have h2 : (a ^ 2) ^ 2 ∈ Subgroup.zpowers (a ^ 2) :=
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one] at h2
  have hbA : b ∈ A := hBA hb
  have hbo : orderOf b = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA.2 b hbA) hb1
  have hKb : K ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    intro l hl
    apply mem_normalizer_zpowers_of_conj_mem
    have hla : l * a * l⁻¹ = a := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hKa hl), mul_inv_cancel_right]
    have hlai : l * a ^ i * l⁻¹ = a ^ i := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hla]
    have hy : l * b * l⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKB hl) b).mp hb
    have hf : l * (a ^ i * b) * l⁻¹ ∈ Subgroup.zpowers (a ^ i * b) :=
      (Subgroup.mem_normalizer_iff.mp (hKf hl) _).mp (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hf
    have hab : Commute (a ^ i) b := hcomm _ (Subgroup.pow_mem _ haA i) _ hbA
    rw [hab.mul_zpow] at hk
    have hsplit : l * (a ^ i * b) * l⁻¹ = a ^ i * (l * b * l⁻¹) := by
      rw [show l * (a ^ i * b) * l⁻¹ = (l * a ^ i * l⁻¹) * (l * b * l⁻¹) by group, hlai]
    rw [hsplit] at hk
    have hmem : (a ^ i)⁻¹ * (a ^ i) ^ k ∈ Subgroup.zpowers a ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i))
        (zpow_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i) k), ?_⟩
      have heq : (a ^ i)⁻¹ * (a ^ i) ^ k = (l * b * l⁻¹) * (b ^ k)⁻¹ := by
        calc (a ^ i)⁻¹ * (a ^ i) ^ k = (a ^ i)⁻¹ * ((a ^ i) ^ k * b ^ k) * (b ^ k)⁻¹ := by
              group
          _ = (a ^ i)⁻¹ * (a ^ i * (l * b * l⁻¹)) * (b ^ k)⁻¹ := by rw [hk]
          _ = (l * b * l⁻¹) * (b ^ k)⁻¹ := by group
      rw [heq]
      exact mul_mem hy (inv_mem (zpow_mem hb k))
    rw [haB, Subgroup.mem_bot] at hmem
    rw [← inv_mul_eq_one.mp hmem] at hk
    rw [← mul_left_cancel hk]
    exact zpow_mem (Subgroup.mem_zpowers b) k
  rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hb) hKb with h | h
  · exact hb1 (Subgroup.zpowers_eq_bot.mp h)
  · have h3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
    rw [h, hB9] at h3
    norm_num at h3

theorem m22_point
    (h131 : Item131) {A La : Subgroup G} {a : G}
    (hD : Sec13Data G A a La)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22) :
    a ∉ La ∧ Nat.card (A ⊓ La : Subgroup G) = 9 ∧ A = Subgroup.zpowers a ⊔ (A ⊓ La) ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (La ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ La)) := by
  have hM22s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hM22p : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M22).Prime := by
    rw [KFacts.KS14.card_nativeM22]
    norm_num
  have haL : a ∉ La := Proof1413.not_mem_of_mulEquiv_simple hD hM22p φ
  have hM12 : Nat.card CFSG.Blueprint.NativeSporadic.M22 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeM12]
    norm_num
  have hJ2 : Nat.card CFSG.Blueprint.NativeSporadic.M22 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeJ2]
    norm_num
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -, hcase⟩ |
      ⟨-, -, hMJ, -⟩ | ⟨-, hPGL, -⟩ | ⟨haL', -⟩
  · have hAe := hD.isElemAbelian
    have hcB : a ∉ A ⊓ La := fun h => haL h.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ La) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
    exact ⟨haL, h9, hAa, isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2⟩
  · exfalso
    rcases hMJ with hM | hM
    · obtain ⟨ψ⟩ := hM
      obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne hM12).false (φ.symm.trans χ)
    · obtain ⟨ψ⟩ := hM
      obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne hJ2).false (φ.symm.trans χ)
  · exact absurd (Sec13.facts_of_isZ3PGLThreePi hD hPGL).1
      (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  · exact absurd haL' haL

theorem not_le_normalizer_of_point {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    {f : G} (hfA : f ∈ A) (hf1 : f ≠ 1) (hfc : Subgroup.zpowers f ≠ Subgroup.zpowers c) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := by
  have hcB : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [inf_comm]
    exact Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq
      (fun h => hcL h.2)
  intro hW
  exact not_le_normalizer_zpowers_of_irreducible hD.isElemAbelian hD.mem_A hAa hcB h9 hirr
    (inf_le_left.trans hD.le_centralizer) (inf_normalizer_le_normalizer_inf A L) hfA hf1 hfc
    (inf_le_right.trans hW)

theorem not_le_normalizer_of_m22
    (h131 : Item131) {A La : Subgroup G} {a : G}
    (hD : Sec13Data G A a La)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22) {f : G}
    (hfA : f ∈ A) (hf1 : f ≠ 1) (hfa : Subgroup.zpowers f ≠ Subgroup.zpowers a) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := by
  obtain ⟨haL, h9, hAa, hirr⟩ := m22_point h131 hD φ
  exact not_le_normalizer_of_point hD haL h9 hAa hirr hfA hf1 hfa

omit [Finite G] in
theorem eq_of_eq_map_conj_of_le_normalizer {A F F₀ : Subgroup G} {w : G}
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (F₀ : Set G))
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (h : F₀ = F.map (MulAut.conj w).toMonoidHom) :
    F = F₀ := by
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (F₀ : Set G) := hW (inv_mem hw)
  rw [← Late.map_conj_eq_of_mem_normalizer hwinv, h, map_conj_map_conj, inv_mul_cancel,
    map_conj_one]

theorem false_of_two_m22
    (h131 : Item131) (h133 : Item133) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G}
    (hLa : La ∈ lA A a)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) (hba : Subgroup.zpowers b ≠ Subgroup.zpowers a)
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b)
    (ψ : ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M22) : False := by
  have hSa := Proof1413.sec14Std_at hS ha hLa
  have hSb := Proof1413.sec14Std_at hS hb hLb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  have hWb := not_le_normalizer_of_m22 h131 hSa.toSec13Data φ hbA hSb.toSec13Data.ne_one hba
  have h3 := Proof1413.case3_of_m22 h133 hSb.toSec13Data hSb.hypS_or_hypT ψ hWb
  have haΩ : Subgroup.zpowers a ∈ orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers b) :=
    by rw [← h3.2.2.2.2.2.1]; exact ha
  obtain ⟨w, hw, haw⟩ := haΩ
  exact hba (eq_of_eq_map_conj_of_le_normalizer hW hw haw)

omit [Finite G] in
theorem isElementaryAbelian_of_isElemAbelian {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) : CFSG.IsElementaryAbelian 3 ↥A :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA

theorem exists_hyperplane_inf_centralizer_ne_bot {A V : Subgroup G} (hA : IsE27 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V) (hV : V ≠ ⊥) :
    ∃ B, IsHyperplane A B ∧ V ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 ↥A := isElementaryAbelian_of_isElemAbelian hA.1
  have : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hA.2]
    norm_num
  have hgen := PartOne.KE8F.le_iSup_hyperplane_centralizers hAV hV3
  by_contra hall
  push Not at hall
  apply hV
  rw [eq_bot_iff]
  refine hgen.trans (iSup₂_le fun B hB =>
    (hall (B.map A.subtype) ⟨Subgroup.map_subtype_le B, ?_⟩).le)
  rw [Subgroup.card_map_of_injective A.subtype_injective, ← hB, Subgroup.index_mul_card]

theorem le_of_forall_centralizer {A B T U : Subgroup G} (hA : IsE27 A) (hB : IsHyperplane A B)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hT3 : ¬ 3 ∣ Nat.card T)
    (hU : ∀ b ∈ B, b ≠ 1 → T ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ →
      T ⊓ Subgroup.centralizer ({b} : Set G) ≤ U) : T ≤ U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [hA.2] at h
    omega
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from
      congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hB.1 x.2⟩ ⟨y, hB.1 y.2⟩))⟩⟩,
      fun x hx => hA.1.2 x (hB.1 hx)⟩
  have : CFSG.IsElementaryAbelian 3 ↥B := isElementaryAbelian_of_isElemAbelian hBe
  have : Nontrivial ↥B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hB9]
    norm_num
  have hgen := PartOne.KE8F.le_iSup_hyperplane_centralizers (hB.1.trans hAT) hT3
  refine hgen.trans (iSup₂_le fun D hD => ?_)
  have hD3 : Nat.card D = 3 := by
    have h := Subgroup.index_mul_card D
    rw [hD, hB9] at h
    omega
  rcases D.bot_or_exists_ne_one with hD0 | ⟨x, hxD, hx1⟩
  · rw [hD0, Subgroup.card_bot] at hD3
    norm_num at hD3
  have hle : T ⊓ Subgroup.centralizer ((D.map B.subtype : Subgroup G) : Set G) ≤
      T ⊓ Subgroup.centralizer ({(x : G)} : Set G) :=
    inf_le_inf_left T (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ⟨x, hxD, rfl⟩))
  by_cases h0 : T ⊓ Subgroup.centralizer ({(x : G)} : Set G) = ⊥
  · rw [h0] at hle
    exact hle.trans bot_le
  · exact hle.trans (hU x x.2 (fun h => hx1 (Subtype.ext h)) h0)

theorem exists_mem_hyperplane_inf_centralizer_ne_bot {A B T : Subgroup G} (hA : IsE27 A)
    (hB : IsHyperplane A B) (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hT3 : ¬ 3 ∣ Nat.card T)
    (hT : T ≠ ⊥) : ∃ b ∈ B, b ≠ 1 ∧ T ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
  by_contra hall
  push Not at hall
  exact hT (le_bot_iff.mp (le_of_forall_centralizer hA hB hAT hT3
    fun b hb hb1 hne => absurd (hall b hb hb1) hne))

omit [Finite G] in
theorem exists_ne_bot_of_not_transOn {A Y V : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : ¬ TransOn A LB V Y) : ∃ S ∈ scriptQPiStar A LB Y (piOf 2), S ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply h
  intro S hS T hT
  rw [hall S hS, hall T hT]
  exact isConjIn_refl _ _

omit [Finite G] in
theorem exists_not_isConjIn {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hX : ¬ TransOn A LB (xA A) ⊤) (S : Subgroup G) :
    ∃ T ∈ scriptQPiStar A LB ⊤ (piOf 2), ¬ IsConjIn (xA A) S T := by
  by_contra hall
  push Not at hall
  apply hX
  intro T₁ hT₁ T₂ hT₂
  rw [inf_top_eq]
  exact (hall T₁ hT₁).symm.trans (hall T₂ hT₂)

omit [Finite G] in
theorem ne_bot_of_not_isConjIn {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T) : T ≠ ⊥ := by
  intro hT0
  apply hST
  have hle : S ≤ T := hT.2 hS.prop (by rw [hT0]; exact bot_le)
  rw [hT0, le_bot_iff] at hle
  rw [hle, hT0]
  exact isConjIn_refl _ _

theorem irreducible_of_cases131
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hM12 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hJ2 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -, hcase⟩ |
      ⟨-, -, hMJ, -⟩ | ⟨-, hP, -⟩ | ⟨hcL', -⟩
  · have hAe := hD.isElemAbelian
    have hcB : c ∉ A ⊓ L := fun h => hcL h.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
    exact ⟨h9, hAa, isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2⟩
  · exfalso
    rcases hMJ with hM | hM
    · obtain ⟨ψ⟩ := hM
      obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
      exact hM12.false χ
    · obtain ⟨ψ⟩ := hM
      obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
      exact hJ2.false χ
  · exact absurd hP hPGL
  · exact absurd hcL' hcL

omit [Finite G] in
theorem mem_normalizer_xA {A : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    w ∈ Subgroup.normalizer (xA A : Set G) := by
  refine normalizer_le_normalizer_pPrimeCoreOf 3 _ (mem_normalizer_of_map_conj_eq ?_)
  rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hw]

theorem map_conj_mem_scriptQPi_map {A Y Q : Subgroup G} {π : Set Nat.Primes} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hQ : Q ∈ scriptQPi A (lB A) Y π) :
    Q.map (MulAut.conj w).toMonoidHom ∈
      scriptQPi A (lB A) (Y.map (MulAut.conj w).toMonoidHom) π := by
  have h := map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hw (Q := Q) (π := π)
    ⟨⟨hQ.1.1, le_top⟩, hQ.2⟩
  exact ⟨⟨h.1.1, Subgroup.map_mono hQ.1.2⟩, h.2⟩

theorem map_conj_mem_scriptQPiStar_map {A Y Q : Subgroup G} {π : Set Nat.Primes} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hQ : Q ∈ scriptQPiStar A (lB A) Y π) :
    Q.map (MulAut.conj w).toMonoidHom ∈
      scriptQPiStar A (lB A) (Y.map (MulAut.conj w).toMonoidHom) π := by
  refine ⟨map_conj_mem_scriptQPi_map hw hQ.prop, fun V hV hle => ?_⟩
  have hV' := map_conj_mem_scriptQPi_map (inv_mem hw) hV
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one] at hV'
  have hle' : Q ≤ V.map (MulAut.conj w⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hle
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  have h := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) (hQ.2 hV' hle')
  rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h

theorem map_conj_mem_gammaA {A F : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hF : F ∈ gammaA A (lB A)) :
    F.map (MulAut.conj w).toMonoidHom ∈ gammaA A (lB A) := by
  refine ⟨(map_conj_mem_omegaA_iff hw).mpr hF.1, fun hT => hF.2 fun S hS T hT' => ?_⟩
  have hN : (Subgroup.normalizer (F : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.normalizer ((F.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq F (MulAut.conj w)
  have hS' := map_conj_mem_scriptQPiStar_map hw hS
  have hT'' := map_conj_mem_scriptQPiStar_map hw hT'
  rw [hN] at hS' hT''
  obtain ⟨y, hy, hyT⟩ := hT _ hS' _ hT''
  obtain ⟨hyX, hyN⟩ := Subgroup.mem_inf.mp hy
  refine ⟨w⁻¹ * y * w, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (mem_normalizer_xA hw)) y).mp hyX
    simpa using h1
  · refine mem_normalizer_of_map_conj_eq ?_
    have h2 : F.map (MulAut.conj (w⁻¹ * y * w)).toMonoidHom =
        ((F.map (MulAut.conj w).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
          (MulAut.conj w⁻¹).toMonoidHom := by
      rw [map_conj_map_conj, map_conj_map_conj]
    rw [h2, Late.map_conj_eq_of_mem_normalizer hyN, map_conj_map_conj, inv_mul_cancel,
      map_conj_one]
  · have h3 := congrArg (Subgroup.map (MulAut.conj w⁻¹).toMonoidHom) hyT
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h3
    rw [h3, mul_assoc]

theorem exists_mem_scriptQPiStar (A Y : Subgroup G) (LB : Subgroup G → Subgroup G)
    (π : Set Nat.Primes) : ∃ R, R ∈ scriptQPiStar A LB Y π := by
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A LB Y π := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A π).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨R, -, hR⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A LB Y π)) hbot
  exact ⟨R, hR⟩

end Proof1413Res2

end CFSG.RankThree.PartTwo.Sec14
