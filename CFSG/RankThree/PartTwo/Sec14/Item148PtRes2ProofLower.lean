module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step142LowerGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

@[expose] def Step142L34Index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
    Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) : Subgroup G) =
      2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))

namespace Item148PtRes2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_conj_mem' {Γ : Type*} [Group Γ] {H M : Subgroup Γ}
    (h : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M) : H ≤ Subgroup.normalizer (M : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨h g hg m, fun hm => ?_⟩
  have h1 := h g⁻¹ (inv_mem hg) _ hm
  have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
  rwa [e] at h1

theorem eq_bot_of_l34 {X : Type*} [Group X] (ψ : X ≃* projSL 3 (GaloisField 2 2))
    {E Y : Subgroup X} (hE : Nat.card E = 9) (hY : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set X)) : Y = ⊥ := by
  set ψ' := ψ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ'
  have hE' : Nat.card (E.map ψ'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ'.injective, hE]
  have hY' : ¬ 3 ∣ Nat.card (Y.map ψ'.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ'.injective]
    exact hY
  have hEY' : E.map ψ'.toMonoidHom ≤
      Subgroup.normalizer ((Y.map ψ'.toMonoidHom : Subgroup _) : Set _) :=
    (Subgroup.map_mono hEY).trans (Subgroup.le_normalizer_map _)
  have h1 := KFacts.L34.eq_bot_of_le_normalizer KFacts.L34.card_galoisField_two_two hE' hY' hEY'
  rw [eq_bot_iff]
  intro y hy
  have h2 : ψ'.toMonoidHom y ∈ Y.map ψ'.toMonoidHom := ⟨y, hy, rfl⟩
  rw [h1, Subgroup.mem_bot] at h2
  rw [Subgroup.mem_bot]
  exact ψ'.injective (h2.trans (map_one ψ').symm)

theorem theta_le_pPrimeCoreOf_centralizer {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    inSubgroup (aschbacherSolvableCore 3) L ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) := by
  have hD := h.toSec13Data
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCcN := centralizer_le_normalizer_of_three_dvd h h3L
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans hD.le_centralizer)
    (hCcN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3

theorem le_sSup_of_gen {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hgen : sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤) :
    L ≤ sSup (invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) := by
  have hD := h.toSec13Data
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set F := {X : Subgroup (↥L ⧸ θ) | ¬ 3 ∣ Nat.card X ∧
    ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} with hF
  set N := sSup (invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
    (piCompl 3)) with hN
  have hpre : ∀ X ∈ F, (X.comap (QuotientGroup.mk' θ)).map L.subtype ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) := by
    rintro X ⟨hX3, hXinv⟩
    refine ⟨(Subgroup.map_subtype_le _).trans
      (hLc.trans (centralizer_singleton_le_normalizer_zpowers c)), ?_, ?_⟩
    · rw [isPiSubgroup_piCompl_iff Nat.prime_three,
        Subgroup.card_map_of_injective L.subtype_injective]
      exact not_three_dvd_card_comap _ hX3 (by rw [QuotientGroup.ker_mk']; exact hθ3)
    · refine le_normalizer_of_conj_mem' fun a ha m hm => ?_
      obtain ⟨l, hl, rfl⟩ := hm
      have haN := hAN ha
      have hl' : a * (l : G) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN l).mp l.2
      refine ⟨⟨_, hl'⟩, ?_, rfl⟩
      have hσ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, haN⟩) ∈
          Sec4.autThetaQuot A L :=
        Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩
      exact hXinv _ hσ ⟨QuotientGroup.mk' θ l, hl, rfl⟩
  have hbot : (⊥ : Subgroup (↥L ⧸ θ)) ∈ F :=
    ⟨by rw [Subgroup.card_bot]; norm_num, fun σ _ => by rw [Subgroup.map_bot]⟩
  set T : Subgroup ↥L := N.subgroupOf L with hT
  have hθT : θ ≤ T := by
    intro l hl
    refine Subgroup.mem_subgroupOf.mpr (le_sSup (hpre ⊥ hbot) ⟨l, ?_, rfl⟩)
    change QuotientGroup.mk' θ l ∈ (⊥ : Subgroup (↥L ⧸ θ))
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hl
  have hFT : ∀ X ∈ F, X ≤ T.map (QuotientGroup.mk' θ) := by
    intro X hX x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ x
    exact ⟨l, Subgroup.mem_subgroupOf.mpr (le_sSup (hpre X hX) ⟨l, hx, rfl⟩), rfl⟩
  have htop : T.map (QuotientGroup.mk' θ) = ⊤ := top_unique (hgen ▸ sSup_le hFT)
  intro g hg
  have hgT : (⟨g, hg⟩ : ↥L) ∈ T := by
    obtain ⟨t, ht, hteq⟩ : QuotientGroup.mk' θ ⟨g, hg⟩ ∈ T.map (QuotientGroup.mk' θ) :=
      htop ▸ Subgroup.mem_top _
    have h1 : t⁻¹ * ⟨g, hg⟩ ∈ θ := by
      rw [← QuotientGroup.ker_mk' θ, MonoidHom.mem_ker, map_mul, map_inv, hteq, inv_mul_cancel]
    have h2 := mul_mem ht (hθT h1)
    rwa [mul_inv_cancel_left] at h2
  exact Subgroup.mem_subgroupOf.mp hgT

theorem le_sup_of_l34 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) {V : Subgroup G}
    (hV : V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    V ≤ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  obtain ⟨hS, hZS⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
  obtain ⟨hcL, h9, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hZS φ
  have hAc := eq_zpowers_sup_of_card hD hcL h9
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCL := centralizer_le_normalizer_of_three_dvd h h3L
  have hVc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hV
  have hV3 : ¬ 3 ∣ Nat.card V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 a a.2)⟩
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A V hA3 hV3 hV.2.2]
  refine sup_le ?_ ((inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian h) hV3).trans
    le_sup_right)
  set Z := ⁅V, A⁆ with hZ
  have hZL : Z ≤ L := commutator_le_of_eq_zpowers_sup hAc hcA hAab hLc hVc (hVc.trans hCL)
  have hZV : Z ≤ V := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing V A hV.2.2
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hV3 (h3.trans (Subgroup.card_dvd_of_le hZV))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A V hV.2.2
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Zb := (Z.subgroupOf L).map (QuotientGroup.mk' θ) with hZb
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2).1))⟩
  have hEb9 : Nat.card Eb = 9 := by
    rw [hEb, Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hZb3 : ¬ 3 ∣ Nat.card Zb := by
    intro h3
    apply hZ3
    have h1 := h3.trans (Subgroup.card_map_dvd (Z.subgroupOf L) (QuotientGroup.mk' θ))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv] at h1
  have hEZ : (A ⊓ L).subgroupOf L ≤ Subgroup.normalizer ((Z.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    le_normalizer_of_conj_mem' fun e he z hz => by
      rw [Subgroup.mem_subgroupOf] at he hz ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hAZ (Subgroup.mem_inf.mp he).1) z).mp hz
  have hEbZb : Eb ≤ Subgroup.normalizer (Zb : Set (↥L ⧸ θ)) :=
    (Subgroup.map_mono hEZ).trans (Subgroup.le_normalizer_map _)
  have hZb1 : Zb = ⊥ := eq_bot_of_l34 ψ hEb9 hZb3 hEbZb
  have hZθ : Z ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    intro z hz
    have h1 : QuotientGroup.mk' θ ⟨z, hZL hz⟩ ∈ Zb :=
      ⟨⟨z, hZL hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    rw [hZb1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨z, hZL hz⟩, h1, rfl⟩
  exact hZθ.trans ((theta_le_pPrimeCoreOf_centralizer h).trans
    ((pPrimeCoreOf_centralizer_le c).trans le_sup_left))

theorem sup_mem_invariantPiSubgroups {A : Subgroup G} {c : G} (hcA : c ∈ A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers c
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y hy x hx
  have hCAH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)).trans hCH
  have hAH : A ≤ H := hAC.trans hCAH
  have hOO : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAH).trans (le_normalizer_pPrimeCoreOf 3 H)
  refine ⟨sup_le (pPrimeCoreOf_le 3 H) ((pPrimeCoreOf_le 3 _).trans hCAH), ?_, ?_⟩
  · rw [isPiSubgroup_piCompl_iff Nat.prime_three, sup_comm]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans (card_sup_dvd_card_mul hOO)) with
      h4 | h4
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 _) h4
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 _) h4
  · exact Proof142Res.le_normalizer_sup_of (hAH.trans (le_normalizer_pPrimeCoreOf 3 H))
      (hAC.trans (le_normalizer_pPrimeCoreOf 3 _))

end Item148PtRes2

open Item148PtRes2 in
theorem step142LowerS14_of (hGen : Step142LowerGen) (hIdx : Step142L34Index) :
    Step142LowerS14 := by
  intro G _ _ A c L h Q hQ
  by_cases hL34 : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))
  · left
    obtain ⟨φ⟩ := hL34
    have hD := h.toSec13Data
    have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
    have hR := sup_mem_invariantPiSubgroups hD.mem_A hAab
    have hQR := le_sup_of_l34 h φ hQ.1
    have hQeq := le_antisymm hQR (hQ.2 hR hQR)
    refine ⟨⟨φ⟩, fun V hV => hQeq ▸ le_sup_of_l34 h φ hV, ?_⟩
    rw [hQeq]
    exact hIdx G A c L h ⟨φ⟩
  · exact Or.inr (le_sSup_of_gen h (hGen G A c L h hL34))

end CFSG.RankThree.PartTwo.Sec14
