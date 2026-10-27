module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25F
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofExcl
import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.StronglyEmbedded.Catalog

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan152SL25

open Proof152ConfA Proof152Gen Proof152F Proof152WE Proof15Res6

theorem exists_mem_inf_not_mem_thetaJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M X : Subgroup G}
    (hctx : Ctx152J A LB M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    ∃ x ∈ A, x ∈ X ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ x ∉ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  set φ : ↥A →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hctx.norm_x)
    with hφ
  have hS : IsPGroup 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hA.isPGroup.of_equiv Subgroup.topEquiv.symm).map φ
  obtain ⟨R, hR⟩ := exists_sylow_three_fixed hS
  have hRcard : Nat.card (R : Subgroup ↥X) = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have hX : Nat.card ↥X = 60 * Nat.card θ := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
      rwa [hX60] at this
    have h60 : Nat.factorization 60 3 = 1 := by
      rw [show (60 : ℕ) = 3 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hX, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h60,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero, pow_one]
  have hRnt : Nontrivial (R : Subgroup ↥X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hRcard]
    norm_num
  obtain ⟨⟨r, hrR⟩, hr1⟩ := exists_ne (1 : (R : Subgroup ↥X))
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrord : orderOf r = 3 := by
    have h := orderOf_dvd_natCard (⟨r, hrR⟩ : (R : Subgroup ↥X))
    rw [hRcard, Subgroup.orderOf_mk] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
    · exact h1
  have hRz : (R : Subgroup ↥X) = Subgroup.zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrR) ?_).symm
    rw [Nat.card_zpowers, hrord, hRcard]
  have hrA : ∀ a ∈ A, a * (r : G) * a⁻¹ = r := by
    intro a ha
    have hσ : (φ ⟨a, ha⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := Subtype.ext (hA.1.2 a ha)
      rw [this, map_one]
    have hmem : φ ⟨a, ha⟩ r ∈ Subgroup.zpowers r := by
      rw [← hRz, ← hR (φ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩]
      exact ⟨r, hrR, rfl⟩
    have h := eq_of_pow_three_eq_one hσ hrord hmem
    have h' := congrArg Subtype.val h
    rwa [hφ, MonoidHom.comp_apply, Sec4.normalizerMonoidHom_apply_coe] at h'
  have hr3 : (r : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hrord, pow_orderOf_eq_one, Subgroup.coe_one]
  have hrAm : (r : G) ∈ A := by
    refine mem_of_mem_partTwoF hAF hr3 fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (r : G) = a * r * a⁻¹ * a := by group
      _ = r * a := by rw [hrA a ha]
  refine ⟨r, hrAm, r.2, hr3, fun h => hr1' (Subtype.ext h), ?_⟩
  rintro ⟨t, ht, htr⟩
  have htr' : t = r := Subtype.ext htr
  rw [htr'] at ht
  have h := orderOf_dvd_natCard (⟨r, ht⟩ : θ)
  rw [Subgroup.orderOf_mk, hrord] at h
  exact hθ3 h

theorem exists_not_mem_thetaQuotCentralizerJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M X : Subgroup G}
    (hctx : Ctx152J A LB M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    ∃ a ∈ A, a ∉ Sec4.thetaQuotCentralizer X := by
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  obtain ⟨x, hxA, hxX, -, -, hxθ⟩ := exists_mem_inf_not_mem_thetaJ hctx hAF hA
  refine ⟨x, hxA, fun hxC => hxθ ?_⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hZ := center_theta_quot_eq_bot hXs hX60
  have hcen : (QuotientGroup.mk' θ ⟨x, hxX⟩ : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hxC
    obtain ⟨t, ht, hte⟩ := hl l l.2
    have hte' : (t : G) = (l : G)⁻¹ * (x * l * x⁻¹) := hte
    have h1 : (QuotientGroup.mk' θ l : ↥X ⧸ θ) =
        QuotientGroup.mk' θ (⟨x, hxX⟩ * l * (⟨x, hxX⟩ : ↥X)⁻¹) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : l⁻¹ * (⟨x, hxX⟩ * l * (⟨x, hxX⟩ : ↥X)⁻¹) = t :=
        Subtype.ext (by rw [hte']; simp)
      rw [this]
      exact ht
    rw [map_mul, map_mul, map_inv] at h1
    calc QuotientGroup.mk' θ l * QuotientGroup.mk' θ ⟨x, hxX⟩ =
        QuotientGroup.mk' θ ⟨x, hxX⟩ * QuotientGroup.mk' θ l *
          (QuotientGroup.mk' θ ⟨x, hxX⟩)⁻¹ * QuotientGroup.mk' θ ⟨x, hxX⟩ := by
          rw [← h1]
      _ = QuotientGroup.mk' θ ⟨x, hxX⟩ * QuotientGroup.mk' θ l := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact ⟨_, hcen, rfl⟩

theorem card_inf_thetaQuotCentralizerJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M X : Subgroup G}
    (hctx : Ctx152J A LB M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  have hmul := Sec13.card_inf_mul_card_autThetaQuot hctx.norm_x
  rw [hA.2] at hmul
  have hH27 : Nat.card (Sec4.autThetaQuot A X) ∣ 3 ^ 3 :=
    Dvd.intro_left _ (hmul.trans (by norm_num))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hH27
  have hH3 : Nat.card (Sec4.autThetaQuot A X) ∣ 3 :=
    card_dvd_three_of_mulEquiv e (IsPGroup.of_card hk)
  obtain ⟨a, haA, haC⟩ := exists_not_mem_thetaQuotCentralizerJ hctx hAF hA
  have hne : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≠ 27 := by
    intro h27
    have hle : A ≤ A ⊓ Sec4.thetaQuotCentralizer X :=
      (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA.2])).symm.le
    exact haC (hle haA).2
  rcases (Nat.dvd_prime Nat.prime_three).mp hH3 with h1 | h1
  · rw [h1, mul_one] at hmul
    exact absurd hmul hne
  · rw [h1] at hmul
    omega

theorem theta_eq_pCore_two_of_j2 {I : Type} [Group I] [Finite I]
    (e : I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2) :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 I with hO
  set θ := aschbacherSolvableCore 3 I with hθ
  have hOθ : O ≤ θ := Proof152F.pCore_two_le_theta I
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := I) Nat.prime_three).2.2.1
  have hθn : θ.Normal := aschbacherSolvableCore_normal 3 I
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have : IsSimpleGroup (I ⧸ O) := e.isSimpleGroup
  have hcard : Nat.card (I ⧸ O) = 604800 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J2.card_J2]
  have hn : (θ.map (QuotientGroup.mk' O)).Normal :=
    hθn.map _ (QuotientGroup.mk'_surjective O)
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · refine le_antisymm ?_ hOθ
    intro x hx
    have h1 : QuotientGroup.mk' O x ∈ θ.map (QuotientGroup.mk' O) := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have h1 : Nat.card (I ⧸ O) ∣ Nat.card θ := by
      rw [← Subgroup.card_top (G := I ⧸ O), ← htop]
      exact Subgroup.card_map_dvd _ _
    rw [hcard] at h1
    exact hθ3 ((show (3 : ℕ) ∣ 604800 by norm_num).trans h1)

theorem exists_lbConfig
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {M X : Subgroup G}
    (hctx : Ctx152J A (lB A) M X) :
    ∃ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B ∧
      (∀ x ∈ X, ∀ y ∈ B, ⁅x, y⁆ ∈ (aschbacherSolvableCore 3 ↥X).map X.subtype) ∧
      IsLBConfig A B b d Lb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  have hchar := (solvable_prime_complement_core_characterization (H := ↥X)
    Nat.prime_three).2.1
  have : (aschbacherSolvableCore 3 ↥X).Characteristic := hchar
  have hbound : ∀ E : Subgroup (MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X)),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 3 := by
    intro E hE
    have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    exact Nat.le_of_dvd (by norm_num) (card_dvd_three_of_mulEquiv e hE3)
  obtain ⟨B, hB, hB3, hBX⟩ := exists_hyperplane_of_autBound hbound h.isElemAbelian h.card_eq
    hctx.norm_x (aschbacherSolvableCore 3 ↥X) (MulEquiv.refl _)
  by_contra hno
  have hno' : ∀ b d Lb, ¬ IsLBConfig A B b d Lb := fun b d Lb hc =>
    hno ⟨B, b, d, Lb, hB, hBX, hc⟩
  have hLB : lB A B = ⊥ := lB_eq_bot hno'
  have hle := le_qBound_sup_of_eq_delta hctx.delta_x hB hB3 hBX
  have hndvd : ∀ K : Subgroup G, ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 K) := fun K =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hq3 : ¬ 3 ∣ Nat.card (qBound A (lB A) B) := by
    rw [qBound, hLB, sup_bot_eq]
    exact not_three_dvd_card_sup
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1)) (hndvd _)
      (hndvd _)
  have hQ3 : ¬ 3 ∣ Nat.card (X ⊓ qBound A (lB A) B : Subgroup G) := fun h3 =>
    hq3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hX3 := not_three_dvd_card_quot_of_le_sup (aschbacherSolvableCore 3 ↥X) inf_le_left hQ3 hle
  apply hX3
  rw [hX60]
  norm_num

theorem sectionCentralizer_eq_of_hyperplane
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {M X : Subgroup G} (hctx : Ctx152J A LB M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A)
    {B : Subgroup G} (hB : IsHyperplane A B)
    (hBX : ∀ x ∈ X, ∀ y ∈ B, ⁅x, y⁆ ∈ (aschbacherSolvableCore 3 ↥X).map X.subtype) :
    Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) := by
  rw [sectionCentralizer_eq_inf hctx.norm_x]
  congr 1
  have h9 := card_inf_thetaQuotCentralizerJ hctx hAF hA
  have hB9 : Nat.card B = 9 := by
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  have hle : B ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
    intro y hy
    refine ⟨hB.1 hy, Proof152F.mem_thetaQuotCentralizer_of_mem hctx.norm_x ⟨hB.1 hy, ?_⟩⟩
    intro x hx
    have h2 := inv_mem (hBX x hx y hy)
    rw [commutatorElement_inv, commutatorElement_def] at h2
    exact h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hB9])).symm

theorem lbConfig_facts {A B : Subgroup G} {b d : G}
    {Lb : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      IsPGroup 2 (aschbacherSolvableCore 3 ↥Lb) ∧ b ∈ A ∧ b ≠ 1 ∧ d ∈ A ∧ d ≠ 1 ∧
      IsThreeCentralIn Lb d ∧ d ∉ Subgroup.zpowers b := by
  obtain ⟨hBcl, hbΩ, hlA, ⟨eJ⟩, hdc⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := theta_eq_pCore_two_of_j2 eJ
  have hLb : Lb ∈ lA A b := hlA ▸ Set.mem_singleton Lb
  obtain ⟨hbA, hb3, -⟩ := zpowers_mem_omegaA_iff.mp hbΩ
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb3
    exact absurd hb3 (by norm_num)
  have hdB : d ∈ B := hBcl ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdA : d ∈ A := hB.1 hdB
  have hB9 : Nat.card B = 9 := by
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  have hdb : d ∉ Subgroup.zpowers b := by
    intro hdb
    have hle : B ≤ Subgroup.zpowers b := by
      rw [hBcl, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_zpowers x
      · exact hdb
    have := Subgroup.card_le_of_le hle
    rw [hB9, hb3] at this
    omega
  have hd1 : d ≠ 1 := fun h1 => hdb (h1 ▸ Subgroup.one_mem _)
  refine ⟨hbΩ, hLb, ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans eJ⟩, ?_, hbA, hb1, hdA, hd1,
    hdc, hdb⟩
  rw [hθ]
  exact CFSG.pCore_isPGroup

theorem inf_centralizer_le_frattini_of_lbConfig
    (h142 : Item142AllS14)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {M X : Subgroup G}
    (hctx : Ctx152J A (lB A) M X) {B : Subgroup G} {b d : G} {Lb : Subgroup G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (B : Set G))
    {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype := by
  have hA := h.isE27
  obtain ⟨hbΩ, hLb, hJ, hθL, hbA, -, hdA, -, -, -⟩ := lbConfig_facts hA hB hc
  have hcent' : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {b, d} : Set G) := by rw [hcent, hc.1]
  have hbC : b ∈ Sec4.thetaQuotCentralizer X := by
    refine Proof152F.mem_thetaQuotCentralizer_of_mem hctx.norm_x ?_
    rw [hcent']
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  rcases inf_centralizer_le_frattini_or_le_ofJ hctx hbA (hA.1.2 b hbA) hbC hP hp3 with hle | hle
  · exact hle
  · exact absurd hle (not_le_centralizer_ofJ h142 h hctx hbΩ hLb hJ hθL hdA hcent' hP hp3)

theorem exists_le_centralizerJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A) {M X : Subgroup G}
    (hctx : Ctx152J A LB M X) {b d : G} (hbA : b ∈ A) (hdA : d ∈ A) (hb1 : b ≠ 1)
    (hdb : d ∉ Subgroup.zpowers b)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {b, d} : Set G))
    {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P) (hp3 : p ≠ 3)
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype) :
    ∃ e ∈ Subgroup.closure ({b, d} : Set G), e ∉ Subgroup.zpowers b ∧
      P ≤ Subgroup.centralizer ({e} : Set G) := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := card_zpowers_eq_three hA hbA hb1
  have hd1 : d ≠ 1 := fun h1 => hdb (h1 ▸ Subgroup.one_mem _)
  set E := Subgroup.closure ({b, d} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hbA
    · exact hdA
  have hE9 : 3 ^ (1 + 1) ≤ Nat.card E := by
    have h1 := card_closure_pair hA hbA hdA
    rw [zpowers_inf_eq_bot (card_zpowers_eq_three hA hdA hd1) hdb,
      Subgroup.card_bot, mul_one, hb3, card_zpowers_eq_three hA hdA hd1] at h1
    rw [← hE] at h1
    omega
  have hEcomm : ∀ x y : ↥E, x * y = y * x := fun x y => Subtype.ext (by
    have h1 := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩)
    simpa using h1)
  have hEab : CFSG.Open.IsElemAbelian 3 E := ⟨⟨⟨hEcomm⟩⟩, fun x hx => hA.1.2 x (hEA hx)⟩
  have hPcop : Nat.Coprime 3 (Nat.card P) := by
    have hPp : IsPGroup p P := by
      rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
      · exact IsPGroup.of_card h
      · exact IsPGroup.of_card h
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hP.prime).mpr
      (Ne.symm hp3))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E P hEab hE9 (hEA.trans hP.norm_p) hPcop
  obtain ⟨F, ⟨hFE, hF3⟩, hFΦ⟩ : ∃ F ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      ¬ P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype := by
    by_contra hno
    have hno' : ∀ F ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
        P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype :=
      fun F hF => by
        by_contra hc
        exact hno ⟨F, hF, hc⟩
    refine false_of_le_frattini hP ?_
    have hle := iSup₂_le hno'
    rw [hgen] at hle
    exact hle
  obtain ⟨e, heF, he1⟩ : ∃ e ∈ F, e ≠ 1 := by
    by_contra hno
    have hno' : ∀ e ∈ F, e = 1 := fun e he => by
      by_contra hc
      exact hno ⟨e, he, hc⟩
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hno'
    rw [hbot, Subgroup.card_bot, pow_one] at hF3
    exact absurd hF3 (by norm_num)
  have heE : e ∈ E := hFE heF
  have heA : e ∈ A := hEA heE
  have heC : e ∈ Sec4.thetaQuotCentralizer X := by
    refine Proof152F.mem_thetaQuotCentralizer_of_mem hctx.norm_x ?_
    have he' : e ∈ (Subgroup.closure {b, d} : Set G) := heE
    rw [← hcent] at he'
    exact he'
  have hPe : P ≤ Subgroup.centralizer ({e} : Set G) := by
    rcases inf_centralizer_le_frattini_or_le_ofJ hctx heA (hA.1.2 e heA) heC hP hp3
      with hle | hle
    · exfalso
      refine hFΦ ((inf_le_inf_left _ ?_).trans hle)
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heF)
    · exact hle
  refine ⟨e, heE, fun heb => ?_, hPe⟩
  have hzeq : Subgroup.zpowers e = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heb)
      (by rw [hb3, card_zpowers_eq_three hA heA he1])
  rw [centralizer_singleton_eq_of_zpowers_eq hzeq] at hPe
  exact false_of_le_frattini hP ((le_inf le_rfl hPe).trans hfr)

end Ronan152SL25

open Ronan152SL25

@[expose] noncomputable def Step152SL25ER : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∉ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) → False

@[expose] noncomputable def Step152SL25EOmegaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∈ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) → False

theorem y4CoreExclSL25HJR_of_residual
    (h142 : Item142AllS14)
    (hE : Step152SL25ER) (hΩ : Step152SL25EOmegaR) : Y4CoreExclSL25HJR := by
  intro G _ _ A c L h hHJ M hM hF J _ hAJ hJM hΔ hcase
  exfalso
  have hctx : Ctx152J A (lB A) M J := ⟨hM, hF, hJM, hAJ, hΔ, hcase⟩
  have hA := h.isE27
  obtain ⟨B, b, d, Lb, hB, hBX, hc⟩ := exists_lbConfig h hctx
  have hcent := sectionCentralizer_eq_of_hyperplane hctx h.mem_partTwoF hA hB hBX
  obtain ⟨p, P, hP, hp3⟩ := exists_pData152J h.toTheoremFourHyp hctx hA.isPGroup
  have hp3' : p ≠ 3 := by omega
  have hfr := inf_centralizer_le_frattini_of_lbConfig h142 h.toSec14Std hctx hB hc hcent hP hp3'
  obtain ⟨-, -, -, -, hbA, hb1, hdA, -, -, hdb⟩ := lbConfig_facts hA hB hc
  have hcent' : Late.sectionCentralizer A J ((aschbacherSolvableCore 3 ↥J).map J.subtype) =
      (Subgroup.closure {b, d} : Set G) := by rw [hcent, hc.1]
  obtain ⟨e, heB, heb, hPe⟩ := exists_le_centralizerJ hA hctx hbA hdA hb1 hdb hcent' hP hp3' hfr
  have heB' : e ∈ B := hc.1 ▸ heB
  by_cases heΩ : Subgroup.zpowers e ∈ omegaA A
  · exact hΩ G A c L h hHJ M J hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB' heb heΩ hPe
  · exact hE G A c L h hHJ M J hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB' heb heΩ hPe

end CFSG.RankThree.PartTwo.Sec15
