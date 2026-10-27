module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate10019
import Certificates.Certificate10019Base

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515A7Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))

@[expose] noncomputable def Step1515A7Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    omegaA A = {Subgroup.zpowers c} →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L

@[expose] noncomputable def Step1515M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    omegaA A = {Subgroup.zpowers c} →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Step1515LA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    omegaA A = {Subgroup.zpowers c} →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
        (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
          CFSG.Assembly.RankThreeEven.projSU 3 5 1)) ∧
        (∀ Y₀ ∈ scriptY0Star A (lB A), ¬ L ≤ Y₀) ∧ IsSimpleGroup ↥L ∧
        Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
          Subgroup.centralizer (L : Set G)))

@[expose] noncomputable def Step1515HJList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON ∨
      (Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L)

@[expose] noncomputable def Step1515HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
        omegaA A = {Subgroup.zpowers c}

@[expose] def Claim1515M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
    ∀ X ∈ scriptY4 A (lB A), X ≤ L → L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem isIrreducibleOn_of_cases131 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hcL : c ∉ L) (h9 : Nat.card ↥(A ⊓ L) = 9) {P Q R : Prop}
    (hcase : (P ∧ (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
      (Q ∧ Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
      (R ∧ Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2))) :
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
  have hAe := hD.isElemAbelian
  have hcB : c ∉ A ⊓ L := fun h => hcL h.2
  have hAa := eq_sup_of_card_nine hD h9 hcB
  obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
  obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
  have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
  exact isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2

theorem false_of_prod_of_isZ3PGLThreePi {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hcL : c ∉ L)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) : False := by
  obtain ⟨φ⟩ := hprod
  have h9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ
  have hcB : c ∉ A ⊓ L := fun h => hcL h.2
  have hAa := eq_sup_of_card_nine hD h9 hcB
  have hEH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hEc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hcl : ∀ (k : ℤ), ∀ y ∈ L, c ^ k * y = y * c ^ k := fun k y hy =>
    (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hy)).symm
      k)
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      have hcy : c * y = y * c := hD.commute hD.mem_A hy.1
      rw [hcy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hy' : c * y * c⁻¹ ∈ A := hy.1
      have hcy : c * y * c⁻¹ * c = c * (c * y * c⁻¹) := hD.commute hy' hD.mem_A
      have hyy : y = c * y * c⁻¹ := by
        have := congrArg (fun t => c⁻¹ * t) hcy
        simpa [mul_assoc] using this
      rw [hyy]
      exact hy
  have hinn : ∀ e ∈ A, ∀ hN : e ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hN⟩) z = w * z * w⁻¹ := by
    intro e he hN
    have he' : e ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
      rw [← hAa]
      exact he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at he'
    obtain ⟨z, hz, a, ha, rfl⟩ := Set.mem_mul.mp he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨((⟨a, ha.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), fun w => ?_⟩
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hax : a * (x : G) * a⁻¹ ∈ L :=
        mul_mem (mul_mem ha.2 x.2) (inv_mem ha.2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      calc c ^ k * a * (x : G) * (a⁻¹ * (c ^ k)⁻¹)
          = c ^ k * (a * (x : G) * a⁻¹) * (c ^ k)⁻¹ := by group
        _ = a * (x : G) * a⁻¹ := by rw [hcl k _ hax, mul_inv_cancel_right]
  exact false_of_inner_of_isZ3PGLThreePi hD hD.le_normalizer hEH hEc
    (fun x hx => exists_lBar_conj_eq_of_inner hD.mem_thetaComponentsAt hD.le_normalizer hEH hinn
      hx) hPGL

theorem not_dvd_relIndex_of_eq_sup_theta {X L : Subgroup G} (hXL : X ≤ L)
    (h : L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype) : ¬ 3 ∣ X.relIndex L := by
  have hN : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥L).map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  have hLN : L ≤ Subgroup.normalizer
      (((aschbacherSolvableCore 3 ↥L).map L.subtype : Subgroup G) : Set G) := by
    have h1 := Subgroup.le_normalizer_map (H := aschbacherSolvableCore 3 ↥L) L.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have := not_dvd_relIndex_sup_of_le_normalizer hN (hXL.trans hLN)
  rwa [← h] at this

theorem false_of_m12_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h137 : Item137)
    (hM12 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {Y X : Subgroup G} (hY : Y ∈ scriptY2 A) (hXY : X ≤ Y) (hXL : X ≤ L)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hidx : ¬ 3 ∣ X.relIndex L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  obtain ⟨E, hEle, hEab, hE27, -, -, hnT⟩ := h137 G A c L hD hM12
  have hidx' : ¬ 3 ∣ (A ⊔ X).relIndex (A ⊔ L) := fun h3 =>
    hidx (h3.trans (relIndex_sup_dvd_of_le_normalizer hXL hAX hD.le_normalizer))
  have hMU : A ⊔ X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    sup_le (hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
  have hEE : E ∈ partTwoE G :=
    mem_partTwoE_of_not_dvd_relIndex (sup_le_sup_left hXL A) hidx' hY.2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hMU (hEle.trans inf_le_left) hEab hE27
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hc3 : c ^ 3 = 1 := by
    rw [← hD.orderOf_eq]
    exact pow_orderOf_eq_one c
  have hEC : E ≤ Subgroup.centralizer ({c} : Set G) :=
    hEle.trans (inf_le_left.trans (sup_le hD.A_le_centralizer hD.le_centralizer))
  have hcE : c ∈ E := mem_of_mem_partTwoF (hFE ▸ hEE) hc3 hEC
  have hER : E ∈ reachE A :=
    ⟨hEE, Relation.ReflTransGen.single ⟨hD.mem_partTwoE, hEE, ⟨Subgroup.zpowers c,
      h.zpowers_mem_omegaA, Subgroup.zpowers_le.mpr hcE⟩⟩⟩
  exact hnT (hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR hER)

theorem false_of_m12 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h137 : Item137) (hcl : Claim1515M12)
    (hM12 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y) : False := by
  obtain ⟨X, hX4, hXLY⟩ := hm
  have hXL : X ≤ L := hXLY.trans inf_le_left
  exact false_of_m12_of_le h h137 hM12 hY.prop.2 (hXLY.trans inf_le_right) hXL hX4.1.2
    (not_dvd_relIndex_of_eq_sup_theta hXL (hcl G A c L h hM12 X hX4 hXL))

theorem isEmpty_mulEquiv_M12_of_M22 {X : Type} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.M22) :
    IsEmpty (X ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  refine ⟨fun ψ => ?_⟩
  have h := Nat.card_congr (φ.symm.trans ψ).toEquiv
  rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeM12] at h
  omega

theorem isEmpty_mulEquiv_M12_of_J2 {X : Type} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) :
    IsEmpty (X ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  refine ⟨fun ψ => ?_⟩
  have h := Nat.card_congr (φ.symm.trans ψ).toEquiv
  rw [KFacts.KS14.card_nativeJ2, KFacts.KS14.card_nativeM12] at h
  omega

theorem isEmpty_mulEquiv_M12_of_A7 {X : Type} [Group X]
    (φ : X ≃* alternatingGroup (Fin 7)) :
    IsEmpty (X ≃* CFSG.Blueprint.NativeSporadic.M12) :=
  ⟨fun ψ => KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1.false (ψ.symm.trans φ)⟩

end Proof1514

open Proof1514

theorem rank3II_15_15_of
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511 A (lB A) c L) (h1512 : Item1512 A (lB A) L)
    (h1513 : Item1513 A (lB A) c L) (h156 : Item156 A (lB A))
    (hA7T : Step1515A7Trans) (hA7O : Step1515A7Omega) (hM22 : Step1515M22)
    (hLA7 : Step1515LA7) (hHJL : Step1515HJList) (hHJ : Step1515HJ) :
    Step1515 A (lB A) c L := by
  intro Y hY hm hce
  have hD := h.toSec13Data
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
      hY.prop.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
    ⟨hcL, h9, hprod, hcase⟩ | ⟨-, -, hMJ, -⟩ | ⟨hcL, hPGL, -, -⟩ | ⟨hcL, -⟩
  ·
    have hirr := isIrreducibleOn_of_cases131 hD hcL h9 hcase
    rcases h1513 ⟨Y, hY.prop⟩ hirr h9 with ⟨hL7, hWS, -, hT⟩ | hΩ
    · exact (hce (Or.inr (Or.inl ⟨hL7, hWS, hT, hA7T G A c L h hL7 hWS hT Y hY hm⟩))).elim
    · rcases hcase with ⟨⟨p, e, hp, he, hiso⟩, -⟩ | ⟨hL7, -⟩ | ⟨hL22, -⟩
      ·
        obtain ⟨hprod', -, hYL, hcases, -⟩ := h1511 p e he hiso Y hY.prop hm P hAP hP
        rcases hcases with hε | hY7
        · exact ⟨p, e, hp, he, hiso, hprod', hYL, hε, hΩ⟩
        · obtain ⟨hU, hno, hsimp, hodd⟩ := hLA7 G A c L h p e he hiso hΩ Y hY hm hYL hY7
          exact (hce (Or.inr (Or.inr ⟨hU, hY7, by rwa [inf_comm], hΩ, hno, hsimp, hodd⟩))).elim
      ·
        obtain ⟨hYL, hLY⟩ := hA7O G A c L h hL7 hΩ Y hY hm
        exact (hce (Or.inl ⟨hYL, hLY, hΩ, hprod, isEmpty_mulEquiv_M12_of_A7 hL7.some⟩)).elim
      ·
        have hYL' := h1512 hL22 Y hY (hM22 G A c L h hL22 hΩ Y hY hm)
        have hLY : L ≤ Y := by
          rw [hYL']
          exact le_sup_left
        refine (hce (Or.inl ⟨?_, ?_, hΩ, hprod, isEmpty_mulEquiv_M12_of_M22 hL22.some⟩)).elim
        · rw [inf_eq_right.mpr hLY]
          exact hYL'
        · rw [inf_eq_left.mpr hLY]
          exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  ·
    rcases hMJ with hψ | hψ
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, -, hM12⟩ := facts_of_prod hD hM12p hM12z ψ
      exact (false_of_m12 h h137 hcl hM12 hY hm).elim
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, hprod, hJ⟩ := facts_of_prod hD hJ2p hJ2z ψ
      rcases hHJL G A c L h hJ Y hY hm with h5 | h6 | hON | ⟨hYL, hLY⟩
      · exact ((h156 Y hY).1.false h5.some).elim
      · exact ((h156 Y hY).2.1 h6).elim
      · exact ((h156 Y hY).2.2 hON).elim
      · exact (hce (Or.inl ⟨hYL, hLY, hHJ G A c L h hJ Y hY hm hYL hLY, hprod,
          isEmpty_mulEquiv_M12_of_J2 hJ.some⟩)).elim
  ·
    obtain ⟨⟨p, e, hp, he, hiso⟩, -, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    obtain ⟨hprod', -⟩ := h1511 p e he hiso Y hY.prop hm P hAP hP
    exact (false_of_prod_of_isZ3PGLThreePi hD hcL hprod' hPGL).elim
  ·
    exact (h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA hcL).elim

end CFSG.RankThree.PartTwo.Sec15
