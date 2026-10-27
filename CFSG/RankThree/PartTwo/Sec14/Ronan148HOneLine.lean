module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HPointK
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HOneLineTools
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HYdMain
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.LocalRank.ThetaPlaneExactQuotients
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (coreSup
  TwoLines)
open scoped Pointwise commutatorElement

@[expose] def KF148OneLineComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON → KList46 X →
    ∀ (P L Q : Subgroup X), Late.IsE27 P → P ≤ Subgroup.normalizer (L : Set X) →
      Group.IsPerfect L → IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      aschbacherSolvableCore 3 ↥L = ⊥ →
      (∀ x ∈ P, (∀ l ∈ L, x * l = l * x) → x ∈ Subgroup.center X) →
      IsKleinFour Q → P ≤ Subgroup.normalizer (Q : Set X) →
      (∃ p ∈ P, p ∉ Subgroup.center X ∧ Q ≤ Subgroup.centralizer ({p} : Set X)) →
      Q ≤ Subgroup.normalizer (L : Set X) → ¬ Q ≤ Subgroup.centralizer (L : Set X) →
      ¬ ∀ R : Subgroup X, R ≤ L ⊔ Q → R ∈ invariantPiSubgroups ⊤ P (piCompl 3) → R ≤ Q

section General

variable {X : Type} [Group X] [Finite X]

theorem normal_of_le_center {Z : Subgroup X} (hZ : Z ≤ Subgroup.center X) : Z.Normal :=
  ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (hZ hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩

theorem centralizer_zpowers_sup_center (b : X) :
    Subgroup.centralizer ((Subgroup.zpowers b ⊔ Subgroup.center X : Subgroup X) : Set X) =
      Subgroup.centralizer ({b} : Set X) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)))
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : Subgroup.zpowers b ⊔ Subgroup.center X ≤ Subgroup.centralizer ({g} : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
      · intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp hz) g).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem isHyperplane_zpowers_sup_center {P : Subgroup X} (hP : Late.IsE27 P)
    (hZP : Subgroup.center X ≤ P) (hZ3 : Nat.card (Subgroup.center X) = 3) {b : X} (hbP : b ∈ P)
    (hbz : b ∉ Subgroup.center X) :
    IsHyperplane P (Subgroup.zpowers b ⊔ Subgroup.center X) := by
  have hb3 : b ^ 3 = 1 := hP.1.2 b hbP
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
  have hcb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hdisj : Disjoint (Subgroup.zpowers b) (Subgroup.center X) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxb, hxZ⟩
    by_contra hx
    have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hxb
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hcx : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hcb])
    apply hbz
    have hbx : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
    exact Subgroup.zpowers_le.mpr hxZ hbx
  refine ⟨sup_le (Subgroup.zpowers_le.mpr hbP) hZP, ?_⟩
  rw [CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint _ _
    ((Subgroup.center_le_centralizer _).trans (Subgroup.centralizer_le_normalizer _)) hdisj,
    hcb, hZ3, hP.2]

theorem inf_eq_bot_of_not_dvd {V W : Subgroup X} (hW : IsPGroup 3 W) (hV : ¬ 3 ∣ Nat.card V) :
    V ⊓ W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (V ⊓ W : Subgroup X) := hW.to_le inf_le_right
  rcases hp.card_eq_or_dvd with h1 | hdvd
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left)) hV

theorem isPiSubgroup_of_not_dvd {V : Subgroup X} (hV : ¬ 3 ∣ Nat.card V) :
    CFSG.IsPiSubgroup (piCompl 3) V := fun q hq h3 => hV (h3 ▸ hq)

theorem not_dvd_of_isPiSubgroup {V : Subgroup X} (hV : CFSG.IsPiSubgroup (piCompl 3) V) :
    ¬ 3 ∣ Nat.card V := fun h3 => (hV ⟨3, Nat.prime_three⟩ h3) rfl

theorem eq_bot_or_eq_of_le_kleinFour {P c O : Subgroup X} (hc : IsKleinFour c) (hOc : O ≤ c)
    (hPO : P ≤ Subgroup.normalizer (O : Set X))
    (hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X))) : O = ⊥ ∨ O = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hO : O = ⊥
  · exact Or.inl hO
  right
  have h4 : Nat.card c = 4 := hc.card_four
  have hdvd : Nat.card O ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hOc
  have hne1 : Nat.card O ≠ 1 := fun h => hO (Subgroup.card_eq_one.mp h)
  have hne2 : Nat.card O ≠ 2 := by
    intro h2
    obtain ⟨⟨t, htO⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO
    have huniq := (Nat.card_eq_two_iff' (1 : O)).mp h2
    have htP : t ∈ Subgroup.centralizer (P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hat : a * t * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hPO ha) t).mp htO
      have hne : (⟨a * t * a⁻¹, hat⟩ : O) ≠ 1 := by
        intro h
        apply ht1
        apply Subtype.ext
        have h' : a * t * a⁻¹ = 1 := congrArg Subtype.val h
        show t = 1
        calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
          _ = 1 := by rw [h']; group
      have heq : (⟨a * t * a⁻¹, hat⟩ : O) = ⟨t, htO⟩ := huniq.unique hne ht1
      have h' : a * t * a⁻¹ = t := congrArg Subtype.val heq
      calc a * t = a * t * a⁻¹ * a := by group
        _ = t * a := by rw [h']
    have ht2 : t ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨t, hOc htO⟩ : c)
      rw [hc.exponent_two] at this
      exact congrArg Subtype.val this
    obtain ⟨n, hn⟩ := hCP ⟨t, htP⟩
    have hn' : t ^ 3 ^ n = 1 := congrArg Subtype.val hn
    have h1 : orderOf t ∣ Nat.gcd 2 (3 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht2) (orderOf_dvd_of_pow_eq_one hn')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num))] at h1
    exact ht1 (Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)))
  have hle : Nat.card O ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card O := Nat.card_pos
  have h4' : Nat.card O = 4 := by
    interval_cases h : Nat.card O <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hOc (by rw [h4, h4'])

theorem map_subtype_le_normalizer {G : Subgroup X} {R S : Subgroup G}
    (h : S ≤ Subgroup.normalizer (R : Set G)) :
    S.map G.subtype ≤ Subgroup.normalizer ((R.map G.subtype : Subgroup X) : Set X) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map _)

theorem mem_normalizer_commutator {A B : Subgroup X} {n : X}
    (hA : n ∈ Subgroup.normalizer (A : Set X)) (hB : n ∈ Subgroup.normalizer (B : Set X)) :
    n ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem thetaAlpha_le_of_invariant {P B c : Subgroup X} (hBP : B ≤ P)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hBcard : Nat.card B = 3 ^ 2)
    (hinv : ∀ R : Subgroup X, R ∈ invariantPiSubgroups ⊤ P (piCompl 3) → R ≤ c) :
    thetaAlpha 3 B ≤ c := by
  obtain ⟨-, hT3, hTle, hTn, -, -, -, heq, -⟩ :=
    theta_plane_alpha_product_equivariance Nat.prime_three B hBcard
  have hPC : P ≤ Subgroup.centralizer (B : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hPab y (hBP hy) x hx
  have hPB : P ≤ Subgroup.normalizer (B : Set X) :=
    hPC.trans (Subgroup.centralizer_le_normalizer _)
  rw [heq]
  refine sup_le ?_ ?_
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun _ => hinv _ ⟨le_top, ?_, ?_⟩
    · set C := Subgroup.centralizer ({b} : Set X) with hC
      have hBC : B ≤ C := fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (hPab y (hBP hy) b (hBP hb))
      have hle : ⁅inSubgroup (aschbacherSolvableCore 3) C, B⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) C :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp
          (hBC.trans (le_normalizer_inSubgroup_theta b))
      have h3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) C) := by
        rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
        exact (solvable_prime_complement_core_characterization (H := C) Nat.prime_three).2.2.1
      exact isPiSubgroup_of_not_dvd fun h => h3 (h.trans (Subgroup.card_dvd_of_le hle))
    · intro n hn
      have hnC : n ∈ Subgroup.centralizer ({b} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (hPab n hn b (hBP hb))
      exact mem_normalizer_commutator (le_normalizer_inSubgroup_theta b hnC) (hPB hn)
  · refine hinv _ ⟨le_top, isPiSubgroup_of_not_dvd hT3, ?_⟩
    exact hPC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hTle).mp hTn)

theorem subgroupOf_map_subtype_of_le {H G : Subgroup X} (h : H ≤ G) :
    (H.subgroupOf G).map G.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h]

theorem isE27_subgroupOf {P G : Subgroup X} (hP : Late.IsE27 P) (hPG : P ≤ G) :
    Late.IsE27 (P.subgroupOf G) := by
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · show ((x : G) : X) * ((y : G) : X) = ((y : G) : X) * ((x : G) : X)
    exact congrArg Subtype.val (hP.1.1.is_comm.comm ⟨((x : G) : X), x.2⟩ ⟨((y : G) : X), y.2⟩)
  · simpa using hP.1.2 (x : X) hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hP.2]

theorem isElemAbelian_map_subtype {p : ℕ} {G : Subgroup X} {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.map G.subtype) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : X) * y = y * x
    rw [← hux, ← hvy, ← map_mul, ← map_mul]
    exact congrArg G.subtype (congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩))
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 u hu, map_one]

end General

theorem exists_faithful_component {H : Type} [Group H] [Finite H] {P Z B : Subgroup H}
    (hP : Late.IsE27 P) (hZP : Z ≤ P) (hZc : Z ≤ Subgroup.center H) (hZ3 : Nat.card Z = 3)
    (hBP : B ≤ P) (hBZ : B ⊓ Z = ⊥) (hBZP : B ⊔ Z = P)
    (hθ : aschbacherSolvableCore 3 H = ⊥)
    (hnorm : ∀ L ∈ thetaComponents 3 H, P ≤ Subgroup.normalizer (L : Set H))
    (hα : thetaAlpha 3 B ≠ ⊥) :
    ∃ L ∈ thetaComponents 3 H, (∀ x ∈ P, (∀ l ∈ L, x * l = l * x) → x ∈ Z) ∧
      ¬ thetaAlpha 3 B ≤ Subgroup.centralizer (L : Set H) := by
  haveI : Z.Normal := normal_of_le_center hZc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsElementaryAbelian 3 P :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 P).mpr hP.1
  have hBel : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : H) * y = y * x from congrArg (Subtype.val : P → H)
      (hP.1.1.is_comm.comm (⟨x, hBP x.2⟩ : P) ⟨y, hBP y.2⟩))⟩⟩, fun x hx => hP.1.2 x (hBP hx)⟩
  have hBcard : Nat.card B = 3 ^ 2 := by
    have h := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
      B Z (hZc.trans ((Subgroup.center_le_centralizer _).trans
        (Subgroup.centralizer_le_normalizer _))) (disjoint_iff.mpr hBZ)
    rw [hBZP, hP.2, hZ3] at h
    omega
  have hZpg : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZB : Z ⊓ B = ⊥ := by rw [inf_comm]; exact hBZ
  have hα' : ¬ thetaAlpha 3 (P.map (QuotientGroup.mk' Z)) ≤ aschbacherSolvableCore 3 (H ⧸ Z) := by
    obtain ⟨-, -, -, -, hc⟩ := theta_plane_alpha_exact_prime_kernel_quotients Nat.prime_three B
      hBel hBcard Z (Or.inr ⟨hZc, hZpg, hZB⟩)
    have hBmap : B.map (QuotientGroup.mk' Z) = P.map (QuotientGroup.mk' Z) := by
      rw [← hBZP, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    intro h
    apply hα
    have h' := (hc hZc hZpg hZB).mpr (hBmap ▸ h)
    rw [hθ] at h'
    exact le_bot_iff.mp h'
  obtain ⟨L, hL, a, ha, hker, -, -, hcent⟩ := central_line_faithful_component_detection
    Nat.prime_three hA (by rw [hP.2]; norm_num) Z hZP hZc hZ3 hnorm hα' B hBP
    (disjoint_iff.mpr hBZ) hBZP
  refine ⟨L, hL, fun x hxP hxL => ?_, fun hle => hcent ?_⟩
  · apply (hker ⟨x, hxP⟩).mp
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 := ha ⟨x, hxP⟩ l l (by
        show (l : H) = x * l * x⁻¹
        rw [hxL l l.2, mul_inv_cancel_right])
      rw [h1]
      rfl
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hle hy)) l hl]

section Model

set_option linter.unusedSectionVars false


open CFSG.RankThree.Native.ONTriple in
theorem exists_model_AG {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) :
    ∃ (φ : X ≃* GM) (j : ℕ), j < 2 ∧ P.map φ.toMonoidHom = AG j ∧
      ∀ x, x ∈ Subgroup.center X ↔ φ x ∈ Subgroup.zpowers zG := by
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  have hP' := Sec13.ON134.isE27_map hP ψ.toMonoidHom ψ.injective
  obtain ⟨h, j, hj, hPj⟩ := exists_conj_AG hP'
  let φ : X ≃* GM := ψ.trans (MulAut.conj h)
  refine ⟨φ, j, hj, ?_, fun x => ?_⟩
  · rw [← hPj, Subgroup.map_map]
    rfl
  · rw [← center_GM]
    exact (MulEquivClass.apply_mem_center_iff φ).symm

open CFSG.RankThree.Native.ONTriple in
theorem center_le_of_isE27 {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) : Subgroup.center X ≤ P := by
  obtain ⟨φ, j, -, hPφ, hc⟩ := exists_model_AG hperf hT hP
  intro z hz
  have h1 : φ z ∈ AG j := Subgroup.zpowers_le.mpr (zG_mem_AG j) ((hc z).mp hz)
  rw [← hPφ] at h1
  obtain ⟨p, hp, hpz⟩ := h1
  have : p = z := φ.injective hpz
  rw [← this]
  exact hp

open CFSG.RankThree.Native.ONTriple
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
theorem isKleinFour_core {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P Y : Subgroup X}
    (hP : Late.IsE27 P) (hPY : P ≤ Subgroup.normalizer (Y : Set X)) {p : X} (hp : p ∈ P)
    (hpz : p ∉ Subgroup.center X)
    (hc : pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X)) ≠ ⊥) :
    IsKleinFour (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X))) := by
  obtain ⟨φ, j, hj, hPφ, hcφ⟩ := exists_model_AG hperf hT hP
  have hYnorm : AG j ≤ Subgroup.normalizer ((Y.map φ.toMonoidHom : Subgroup GM) : Set GM) := by
    intro a ha
    rw [← hPφ] at ha
    obtain ⟨p0, hp0, rfl⟩ := ha
    change φ p0 ∈ Subgroup.normalizer ((Y.map φ.toMonoidHom : Subgroup GM) : Set GM)
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := φ.surjective y'
    have h1 : φ y ∈ Y.map φ.toMonoidHom ↔ y ∈ Y := by
      rw [Subgroup.mem_map_equiv]; simp
    have h2 : φ p0 * φ y * (φ p0)⁻¹ ∈ Y.map φ.toMonoidHom ↔ p0 * y * p0⁻¹ ∈ Y := by
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_equiv]; simp
    rw [h1, h2]
    exact Subgroup.mem_normalizer_iff.1 (hPY hp0) y
  obtain ⟨l, hl, he, -⟩ := PointSig.core_map_eq (Y := Y) hj hPφ hcφ hp hpz
  set c := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X)) with hcdef
  have e : ↥c ≃* ↥(c.map φ.toMonoidHom) :=
    c.equivMapOfInjective φ.toMonoidHom φ.injective
  rcases core_cases hj hl hYnorm with h0 | ⟨m, hm, hXG⟩
  · exfalso
    apply hc
    rw [← he] at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h0
  · have hK : IsKleinFour (XG j l m hj hm) := isKleinFour_XG hj hm
    rw [← hXG, ← he] at hK
    exact ⟨by rw [Nat.card_congr e.toEquiv]; exact hK.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hK.exponent_two⟩

theorem le_core_of_invariant {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P Y : Subgroup X}
    (hP : Late.IsE27 P)
    (hsig : ∀ H : Subgroup X, IsHyperplane P H → ∀ V : Subgroup X,
      V ≤ Y ⊓ Subgroup.centralizer (H : Set X) → V ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
      V = ⁅V, P⁆ → V ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H : Set X)))
    {p₀ : X}
    (hother : ∀ q ∈ P, q ∉ Subgroup.center X →
      Subgroup.centralizer ({q} : Set X) ≠ Subgroup.centralizer ({p₀} : Set X) →
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({q} : Set X)) = ⊥)
    {R : Subgroup X} (hRY : R ≤ Y) (hR : R ∈ invariantPiSubgroups ⊤ P (piCompl 3)) :
    R ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p₀} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hT.1
  have hZP : Subgroup.center X ≤ P := center_le_of_isE27 hperf hT hP
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hperf hT hP
  have hPpg : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hP.1.2 x x.2)⟩
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hP.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨B, hBP, hBZ, hBZP⟩ := exists_complement_of_isE27 hP hZP
  have hBcard : Nat.card B = 9 := by
    have h := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
      B (Subgroup.center X) ((Subgroup.center_le_centralizer _).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hBZ)
    rw [hBZP, hP.2, hZ3] at h
    omega
  have hBel : IsElementaryAbelian 3 B :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mpr
      ⟨⟨⟨fun x y => Subtype.ext (hPab x (hBP x.2) y (hBP y.2))⟩⟩, fun x hx => hP.1.2 x (hBP hx)⟩
  have hR3 : ¬ 3 ∣ Nat.card R := not_dvd_of_isPiSubgroup hR.2.1
  refine CFSG.RankThree.GroupTheory.SteinbergBM.le_of_forall_inf_centralizer_le hBel
    (by rw [hBcard]; norm_num) hR3 (hBP.trans hR.2.2) ?_
  intro b hb hb1
  have hbP : b ∈ P := hBP hb
  have hbz : b ∉ Subgroup.center X := fun h => hb1 (by
    have hmem : b ∈ B ⊓ Subgroup.center X := ⟨hb, h⟩
    rw [hBZ] at hmem
    exact (Subgroup.mem_bot).mp hmem)
  set V := R ⊓ Subgroup.centralizer ({b} : Set X) with hV
  have hV3 : ¬ 3 ∣ Nat.card V := fun h => hR3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hPV : P ≤ Subgroup.normalizer (V : Set X) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hR.2.2 ha, Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hPab a ha b hbP))⟩
  have hVcomm : V = ⁅V, P⁆ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three P V hPpg hV3 hPV
    rw [inf_eq_bot_of_not_dvd hCP hV3, sup_bot_eq] at h
    exact h
  have hHb := isHyperplane_zpowers_sup_center hP hZP hZ3 hbP hbz
  have hCb := centralizer_zpowers_sup_center b
  have hVle : V ≤ Y ⊓ Subgroup.centralizer
      ((Subgroup.zpowers b ⊔ Subgroup.center X : Subgroup X) : Set X) := by
    rw [hCb]
    exact inf_le_inf_right _ hRY
  have h1 := hsig _ hHb V hVle ⟨le_top, isPiSubgroup_of_not_dvd hV3, hPV⟩ hVcomm
  rw [hCb] at h1
  by_cases hC : Subgroup.centralizer ({b} : Set X) = Subgroup.centralizer ({p₀} : Set X)
  · rw [hC] at h1
    exact h1
  · rw [hother b hbP hbz hC] at h1
    exact h1.trans bot_le


theorem kf148OneLineK_of_comp (hcomp : KF148OneLineComp) : KF148OneLineK := by
  intro X _ _ hperf hT hKX P Y hP hPY hsig htwo
  by_contra hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hT.1
  have hZP : Subgroup.center X ≤ P := center_le_of_isE27 hperf hT hP
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hperf hT hP
  have hPpg : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hP.1.2 x x.2)⟩
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hP.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨p₀, hp₀, hp₀z, hc₀⟩ : ∃ p ∈ P, p ∉ Subgroup.center X ∧
      ¬ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X)) ≤ pPrimeCoreOf 3 Y := by
    by_contra h
    push Not at h
    exact hnot (iSup_le fun p => iSup_le fun hp => iSup_le fun hpz => h p hp hpz)
  set c₀ := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p₀} : Set X)) with hc₀def
  have hc₀ne : c₀ ≠ ⊥ := fun h => hc₀ (h ▸ bot_le)
  have hother : ∀ q ∈ P, q ∉ Subgroup.center X →
      Subgroup.centralizer ({q} : Set X) ≠ Subgroup.centralizer ({p₀} : Set X) →
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({q} : Set X)) = ⊥ := by
    intro q hq hqz hne
    by_contra h
    exact htwo ⟨p₀, hp₀, q, hq, hp₀z, hqz, Ne.symm hne, hc₀ne, h⟩
  have hK4 : IsKleinFour c₀ := isKleinFour_core hperf hT hP hPY hp₀ hp₀z hc₀ne
  have hstar : ∀ R : Subgroup X, R ≤ Y → R ∈ invariantPiSubgroups ⊤ P (piCompl 3) → R ≤ c₀ :=
    fun R hRY hR => le_core_of_invariant hperf hT hP hsig hother hRY hR
  have hc₀Y : c₀ ≤ Y := (pPrimeCoreOf_le 3 _).trans inf_le_left
  have hc₀C : c₀ ≤ Subgroup.centralizer ({p₀} : Set X) := (pPrimeCoreOf_le 3 _).trans inf_le_right
  have hPc₀ : P ≤ Subgroup.normalizer (c₀ : Set X) := fun a ha =>
    normalizer_le_normalizer_pPrimeCoreOf 3 _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hPY ha, Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.mpr (hPab a ha p₀ hp₀))⟩)
  have hc₀3 : ¬ 3 ∣ Nat.card c₀ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hO : pPrimeCoreOf 3 Y = ⊥ := by
    have hOinv : pPrimeCoreOf 3 Y ∈ invariantPiSubgroups ⊤ P (piCompl 3) :=
      ⟨le_top, isPiSubgroup_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 Y)), hPY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)⟩
    rcases eq_bot_or_eq_of_le_kleinFour hK4 (hstar _ (pPrimeCoreOf_le 3 Y) hOinv) hOinv.2.2 hCP
      with h | h
    · exact h
    · exact absurd (le_of_eq h.symm) hc₀
  set G := Y ⊔ P with hGdef
  have hYG : Y ≤ G := le_sup_left
  have hPG : P ≤ G := le_sup_right
  have hZG : Subgroup.center X ≤ G := hZP.trans hPG
  obtain ⟨B, hBP, hBZ, hBZP⟩ := exists_complement_of_isE27 hP hZP
  have hBcard : Nat.card B = 9 := by
    have h := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
      B (Subgroup.center X) ((Subgroup.center_le_centralizer _).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hBZ)
    rw [hBZP, hP.2, hZ3] at h
    omega
  set P' := P.subgroupOf G with hP'def
  set Z' := (Subgroup.center X).subgroupOf G with hZ'def
  set B' := B.subgroupOf G with hB'def
  set c' := c₀.subgroupOf G with hc'def
  have hP' : Late.IsE27 P' := isE27_subgroupOf hP hPG
  have hZ'P' : Z' ≤ P' := fun x hx => hZP hx
  have hZ'c : Z' ≤ Subgroup.center G := fun x hx =>
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext ((Subgroup.mem_center_iff.mp hx) g)
  have hZ'3 : Nat.card Z' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZG).toEquiv, hZ3]
  have hB'P' : B' ≤ P' := fun x hx => hBP hx
  have hB'Z' : B' ⊓ Z' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxZ⟩
    have hmem : (x : X) ∈ B ⊓ Subgroup.center X := ⟨hxB, hxZ⟩
    rw [hBZ, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  have hB'Z'P' : B' ⊔ Z' = P' := by
    rw [← Subgroup.subgroupOf_sup (hBP.trans hPG) hZG, hBZP]
  have hB'card : Nat.card B' = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBP.trans hPG)).toEquiv, hBcard]
    norm_num
  have hP'ab : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := fun x hx y hy =>
    Subtype.ext (hPab x hx y hy)
  have hθG : aschbacherSolvableCore 3 ↥G = ⊥ := by
    obtain ⟨-, hθc, hθ3, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥G) Nat.prime_three
    haveI : (aschbacherSolvableCore 3 ↥G).Normal := by haveI := hθc; infer_instance
    set T := aschbacherSolvableCore 3 ↥G with hTdef
    have hTX3 : ¬ 3 ∣ Nat.card (T.map G.subtype) := by
      rw [Subgroup.card_map_of_injective G.subtype_injective]
      exact hθ3
    have hTXY : T.map G.subtype ≤ Y :=
      le_of_le_sup_of_not_dvd hPY hPpg (Subgroup.map_subtype_le T) hTX3
    have hGT : G ≤ Subgroup.normalizer ((T.map G.subtype : Subgroup X) : Set X) := by
      have h := map_subtype_le_normalizer (R := T) (S := ⊤) (le_of_eq (Subgroup.normalizer_eq_top (H := T)).symm)
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    have hle : T.map G.subtype ≤ pPrimeCoreOf 3 Y :=
      le_pPrimeCoreOf hTXY (hYG.trans hGT)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hTX3)
    rw [hO, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp hle
  have h8 : ∀ E : Subgroup ↥G, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8 := by
    intro E hE
    rw [← Subgroup.card_map_of_injective G.subtype_injective]
    exact card_le_eight_of_isTripleCover hT _ (isElemAbelian_map_subtype hE)
  have hnormG : ∀ L ∈ thetaComponents 3 ↥G, ∀ g : ↥G, g ∈ Subgroup.normalizer (L : Set ↥G) := by
    intro L hL g
    have hker : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective
    have hLg : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponents 3 ↥G :=
      CFSG.RankThree.PartOne.EmbeddingTransport.map_mem_thetaComponents_of_surjective
        Nat.prime_three (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
        (by rw [hker]; infer_instance) (by rw [hker, Subgroup.card_bot]; norm_num) hL
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact eq_of_mem_thetaComponents hθG h8 hLg hL
  have hinv' : ∀ R : Subgroup ↥G, R ∈ invariantPiSubgroups ⊤ P' (piCompl 3) → R ≤ c' := by
    intro R hR
    have hR3 : ¬ 3 ∣ Nat.card (R.map G.subtype) := by
      rw [Subgroup.card_map_of_injective G.subtype_injective]
      exact not_dvd_of_isPiSubgroup hR.2.1
    have hPR : P ≤ Subgroup.normalizer ((R.map G.subtype : Subgroup X) : Set X) := by
      have h := map_subtype_le_normalizer hR.2.2
      rwa [subgroupOf_map_subtype_of_le hPG] at h
    have hRY : R.map G.subtype ≤ Y :=
      le_of_le_sup_of_not_dvd hPY hPpg (Subgroup.map_subtype_le R) hR3
    have h := hstar _ hRY ⟨le_top, isPiSubgroup_of_not_dvd hR3, hPR⟩
    intro r hr
    exact h ⟨r, hr, rfl⟩
  have hcα : c' ≤ thetaAlpha 3 B' := by
    set H₀ := Subgroup.zpowers p₀ ⊔ Subgroup.center X with hH₀
    have hH₀P : H₀ ≤ P := sup_le (Subgroup.zpowers_le.mpr hp₀) hZP
    have hH₀9 : Nat.card H₀ = 9 := by
      have h27 := (isHyperplane_zpowers_sup_center hP hZP hZ3 hp₀ hp₀z).2
      rw [hP.2] at h27
      show Nat.card ↥(Subgroup.zpowers p₀ ⊔ Subgroup.center X) = 9
      omega
    have hBH : B ⊓ H₀ ≠ ⊥ := by
      intro h
      have hc := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
        B H₀ (fun x hx => Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun y hy => hPab y (hBP hy) x (hH₀P hx)))
        (disjoint_iff.mpr h)
      have hle := Subgroup.card_le_of_le (sup_le hBP hH₀P)
      rw [hc, hBcard, hH₀9, hP.2] at hle
      omega
    obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBH
    have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
    have hb₀P : b₀ ∈ P := hBP hb₀.1
    have hb₀z : b₀ ∉ Subgroup.center X := fun h => hb₀1' (by
      have hmem : b₀ ∈ B ⊓ Subgroup.center X := ⟨hb₀.1, h⟩
      rw [hBZ] at hmem
      exact (Subgroup.mem_bot).mp hmem)
    have hCb₀ : Subgroup.centralizer ({b₀} : Set X) = Subgroup.centralizer ({p₀} : Set X) := by
      have hle : Subgroup.zpowers b₀ ⊔ Subgroup.center X ≤ H₀ :=
        sup_le (Subgroup.zpowers_le.mpr hb₀.2) le_sup_right
      have h9 : Nat.card (Subgroup.zpowers b₀ ⊔ Subgroup.center X : Subgroup X) = 9 := by
        have h27 := (isHyperplane_zpowers_sup_center hP hZP hZ3 hb₀P hb₀z).2
        rw [hP.2] at h27
        omega
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hH₀9, h9])
      rw [← centralizer_zpowers_sup_center b₀, heq, hH₀, centralizer_zpowers_sup_center p₀]
    set b₀' : ↥G := ⟨b₀, hPG hb₀P⟩ with hb₀'def
    have hb₀'B : b₀' ∈ B' := hb₀.1
    have hb₀'1 : b₀' ≠ 1 := fun h => hb₀1' (congrArg Subtype.val h)
    set C' := Subgroup.centralizer ({b₀'} : Set ↥G) with hC'
    have hc'C' : c' ≤ C' := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 : (x : X) ∈ Subgroup.centralizer ({b₀} : Set X) := hCb₀ ▸ hc₀C hx
      exact Subgroup.mem_centralizer_singleton_iff.mp h1
    have hC'N : C' ≤ Subgroup.normalizer (c' : Set ↥G) := by
      intro g hg
      have hgX : (g : X) ∈ Subgroup.normalizer (c₀ : Set X) := by
        obtain ⟨y, hy, q, hq, hyq⟩ := exists_mul_of_mem_sup hPY g.2
        have hgb : (g : X) * b₀ = b₀ * g := by
          have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
          exact this
        have hqb : q * b₀ = b₀ * q := hPab q hq b₀ hb₀P
        have hyC : y ∈ Subgroup.centralizer ({p₀} : Set X) := by
          rw [← hCb₀, Subgroup.mem_centralizer_singleton_iff]
          have hy' : y = (g : X) * q⁻¹ := by rw [← hyq]; group
          rw [hy']
          calc (g : X) * q⁻¹ * b₀ = (g : X) * (q⁻¹ * b₀) := by group
            _ = (g : X) * (b₀ * q⁻¹) := by
              congr 1
              calc q⁻¹ * b₀ = q⁻¹ * (b₀ * q) * q⁻¹ := by group
                _ = q⁻¹ * (q * b₀) * q⁻¹ := by rw [hqb]
                _ = b₀ * q⁻¹ := by group
            _ = (g : X) * b₀ * q⁻¹ := by group
            _ = b₀ * g * q⁻¹ := by rw [hgb]
            _ = b₀ * (g * q⁻¹) := by group
        have hyN : y ∈ Subgroup.normalizer (c₀ : Set X) :=
          le_normalizer_pPrimeCoreOf 3 _ ⟨hy, hyC⟩
        rw [← hyq]
        exact Subgroup.mul_mem _ hyN (hPc₀ hq)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      show (h : X) ∈ c₀ ↔ ((g * h * g⁻¹ : ↥G) : X) ∈ c₀
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hgX h
    have hc'θ : c' ≤ inSubgroup (aschbacherSolvableCore 3) C' := by
      set N := c'.subgroupOf C' with hN
      have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hc'C').mpr hC'N
      have hNsol : Group.IsSolvable N := by
        refine Group.isSolvable_of_comm fun x y => Subtype.ext (Subtype.ext (Subtype.ext ?_))
        have := hK4.isMulCommutative
        show (((x : C') : ↥G) : X) * (((y : C') : ↥G) : X) =
          (((y : C') : ↥G) : X) * (((x : C') : ↥G) : X)
        exact congrArg Subtype.val (this.is_comm.comm (⟨(((x : C') : ↥G) : X), x.2⟩ : c₀)
          ⟨(((y : C') : ↥G) : X), y.2⟩)
      have hN3 : ¬ 3 ∣ Nat.card N := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc'C').toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hc₀Y.trans hYG)).toEquiv]
        exact hc₀3
      have hNθ := (solvable_prime_complement_core_characterization (H := ↥C')
        Nat.prime_three).2.2.2.1 N hNn hNsol hN3
      intro x hx
      exact ⟨⟨x, hc'C' hx⟩, hNθ hx, rfl⟩
    have hP'c' : P' ≤ Subgroup.normalizer (c' : Set ↥G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      show (h : X) ∈ c₀ ↔ ((g * h * g⁻¹ : ↥G) : X) ∈ c₀
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hPc₀ hg) h
    have hc'B' : c' = ⁅c', B'⁆ := by
      have hB'pg : IsPGroup 3 B' := fun x => ⟨1, Subtype.ext (Subtype.ext (by
        have := hP.1.2 ((x : ↥G) : X) (hBP x.2)
        simpa using this))⟩
      have hc'3 : ¬ 3 ∣ Nat.card c' := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hc₀Y.trans hYG)).toEquiv]
        exact hc₀3
      have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
        3 Nat.prime_three B' c' hB'pg hc'3 (hB'P'.trans hP'c')
      have hbot : c' ⊓ Subgroup.centralizer (B' : Set ↥G) = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxc, hxB⟩
        have hxP : (x : X) ∈ Subgroup.centralizer (P : Set X) := by
          rw [← hBZP]
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hle : B ⊔ Subgroup.center X ≤ Subgroup.centralizer ({(x : X)} : Set X) := by
            refine sup_le (fun b hb => ?_) (fun z hz => ?_)
            · rw [Subgroup.mem_centralizer_singleton_iff]
              have := (Subgroup.mem_centralizer_iff.mp hxB) ⟨b, hPG (hBP hb)⟩ hb
              exact congrArg Subtype.val this
            · rw [Subgroup.mem_centralizer_singleton_iff]
              exact ((Subgroup.mem_center_iff.mp hz) x).symm
          exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
        have h1 : (x : X) ∈ c₀ ⊓ Subgroup.centralizer (P : Set X) := ⟨hxc, hxP⟩
        rw [inf_eq_bot_of_not_dvd hCP hc₀3, Subgroup.mem_bot] at h1
        exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
      rw [hbot, sup_bot_eq] at h
      exact h
    calc c' = ⁅c', B'⁆ := hc'B'
      _ ≤ ⁅inSubgroup (aschbacherSolvableCore 3) C', B'⁆ := Subgroup.commutator_mono hc'θ le_rfl
      _ ≤ thetaJ 3 B' := le_iSup_of_le b₀' (le_iSup_of_le hb₀'B (le_iSup_of_le hb₀'1 le_rfl))
      _ ≤ thetaAlpha 3 B' := le_sup_left
  have hc'ne : c' ≠ ⊥ := by
    intro h
    apply hc₀ne
    rw [← subgroupOf_map_subtype_of_le (hc₀Y.trans hYG), ← hc'def, h, Subgroup.map_bot]
  have hα : thetaAlpha 3 B' ≠ ⊥ := fun h => hc'ne (le_bot_iff.mp (h ▸ hcα))
  have hαc : thetaAlpha 3 B' ≤ c' := thetaAlpha_le_of_invariant hB'P' hP'ab hB'card hinv'
  obtain ⟨L, hL, hLker, hLcent⟩ := exists_faithful_component hP' hZ'P' hZ'c hZ'3 hB'P' hB'Z'
    hB'Z'P' hθG (fun L hL x _ => hnormG L hL x) hα
  set LX := L.map G.subtype with hLXdef
  have eL : ↥L ≃* ↥LX := L.equivMapOfInjective G.subtype G.subtype_injective
  have hLp : Group.IsPerfect L := hL.1
  have hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hL.2.2
  have hθL : aschbacherSolvableCore 3 ↥L = ⊥ := by
    obtain ⟨h1, -⟩ := theta_component_quotient_structure Nat.prime_three hL
    rw [hθG, inf_bot_eq] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have hθLX : aschbacherSolvableCore 3 ↥LX = ⊥ := by
    rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL, hθL,
      Subgroup.map_bot]
  have hLXp : Group.IsPerfect LX := isPerfect_of_mulEquiv eL hLp
  have hLXq : IsQuasisimple (↥LX ⧸ aschbacherSolvableCore 3 ↥LX) :=
    isQuasisimple_theta_of_mulEquiv eL hLq
  have hLXY : LX ≤ Y := le_of_le_sup_of_isPerfect hPY hPpg (Subgroup.map_subtype_le L) hLXp
  have hPLX : P ≤ Subgroup.normalizer (LX : Set X) := by
    have h := map_subtype_le_normalizer (R := L) (S := P') (fun x _ => hnormG L hL x)
    rwa [subgroupOf_map_subtype_of_le hPG] at h
  have hc₀LX : c₀ ≤ Subgroup.normalizer (LX : Set X) := by
    have h := map_subtype_le_normalizer (R := L) (S := c') (fun x _ => hnormG L hL x)
    rwa [subgroupOf_map_subtype_of_le (hc₀Y.trans hYG)] at h
  have hCPLX : ∀ x ∈ P, (∀ l ∈ LX, x * l = l * x) → x ∈ Subgroup.center X := by
    intro x hx hxl
    exact hLker ⟨x, hPG hx⟩ hx (fun l hl => Subtype.ext (hxl l ⟨l, hl, rfl⟩))
  have hnc : ¬ c₀ ≤ Subgroup.centralizer (LX : Set X) := by
    intro hle
    apply hLcent
    refine hαc.trans fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle hx)) l ⟨l, hl, rfl⟩)
  have hall : ∀ R : Subgroup X, R ≤ LX ⊔ c₀ → R ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
      R ≤ c₀ :=
    fun R hR hRinv => hstar R (hR.trans (sup_le hLXY hc₀Y)) hRinv
  exact hcomp X hperf hT hKX P LX c₀ hP hPLX hLXp hLXq hθLX hCPLX hK4 hPc₀ ⟨p₀, hp₀, hp₀z, hc₀C⟩
    hc₀LX hnc hall

end Model

section Consumer

set_option linter.unusedSectionVars false


theorem step148PointHJdONGenD_of_comp (h143 : Concl143S14) (h46 : Sec4.Item4_6)
    (hcomp : KF148OneLineComp) : Step148PointHJdONGenD :=
  step148PointHJdONGenD_of_oneLineK h143 h46 (kf148OneLineK_of_comp hcomp)

end Consumer

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
