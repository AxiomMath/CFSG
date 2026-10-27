module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagSecondComponent
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagExclude
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagNormalizeLift
public import CFSG.RankThree.PartTwo.Sec4.T444.Step452Residual
public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.Steps444
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagRankI22

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


@[expose] def CenterThreePrimeTwoAt (T : Type) [Group T] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    Nonempty (X ⧸ Subgroup.center X ≃* T) →
    ∀ Z : Subgroup X, Z ≤ Subgroup.center X → ¬ 3 ∣ Nat.card Z → IsPGroup 2 Z

@[expose] def ResidualAt (T : Type) [Group T] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → Group.IsPerfect X →
    CFSG.pCore 2 X = ⊥ → ∀ (K : Subgroup X) [K.Normal], Group.IsSolvable K →
      ¬ 9 ∣ Nat.card K → Nonempty (X ⧸ K ≃* T) → IsQuasisimple X

theorem residualAt_L34_of (h : Item4_52Residual) : ResidualAt (projSL 3 (GaloisField 2 2)) := h

theorem centerThreePrimeTwoAt_L34_of (h : KFacts.L34CenterThreePrimeTwo) :
    CenterThreePrimeTwoAt (projSL 3 (GaloisField 2 2)) := h

@[expose] def L34SectionPSL3Odd : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    ¬ HasSection (projSL 3 (GaloisField p e)) (projSL 3 (GaloisField 2 2))

@[expose] def L34SectionPSU3Odd : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    ¬ HasSection (projSU 3 p e) (projSL 3 (GaloisField 2 2))

@[expose] def L34SectionPSU3Even : Prop :=
  ∀ e : ℕ, Odd e → ¬ HasSection (projSU 3 2 e) (projSL 3 (GaloisField 2 2))

@[expose] def CoverU43CenterElem : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) →
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.center X) ∧ Nat.card (Subgroup.center X) ≤ 9

@[expose] def E81U43 : Prop :=
  ∃ V : Subgroup (projSU 4 3 1), CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V

@[expose] def E81McL : Prop :=
  ∃ V : Subgroup Blueprint.NativeSporadic.McL, CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V

@[expose] def E81ON : Prop :=
  ∃ V : Subgroup Blueprint.NativeSporadic.ON, CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V

section Certs


structure DiagInputs : Prop where
  kpSz : KFacts.KPSz
  schreier : SchreierFor CFSG.Assembly.InCatalog
  item45 : Item4_5
  item434Sec : Item4_34Sec
  item41LargePrime : Item4_1LargePrime
  item43 : Item4_3
  coverCenterThree : Census.CoverCenterThree
  coverU43Elem : CoverU43CenterElem
  e81U43 : E81U43
  e81McL : E81McL
  e81ON : E81ON
  l34PSL3Odd : L34SectionPSL3Odd
  l34PSU3Odd : L34SectionPSU3Odd
  l34PSU3Even : L34SectionPSU3Even
  residualL34 : ResidualAt (projSL 3 (GaloisField 2 2))
  centerL34 : CenterThreePrimeTwoAt (projSL 3 (GaloisField 2 2))
  residualSL3 : ∀ m : ℕ, 2 ≤ m → ResidualAt (projSL 3 (GaloisField 2 (2 * m)))
  centerSL3 : ∀ m : ℕ, 2 ≤ m → CenterThreePrimeTwoAt (projSL 3 (GaloisField 2 (2 * m)))
  residualM22 : ResidualAt Blueprint.NativeSporadic.M22
  centerM22 : CenterThreePrimeTwoAt Blueprint.NativeSporadic.M22

theorem ys03_N12_card_map_starQuot {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsPGroup 3 A) : Nat.card (A.map (starQuot G)) = Nat.card A := by
  have hinf := inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hA
    (not_three_dvd_card_pPrimeCore (G := G))
  have hinj : Function.Injective ((starQuot G).domRestrict A) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply] at hx
    have hxP : (x : G) ∈ CFSG.pPrimeCore 3 G := by
      rwa [starQuot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hx' : (x : G) ∈ A ⊓ CFSG.pPrimeCore 3 G := ⟨x.2, hxP⟩
    rw [hinf, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : ((starQuot G).domRestrict A).range = A.map (starQuot G) :=
    MonoidHom.domRestrict_range _ _
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem ys03_N13_map_ne_one {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : IsPGroup 3 A)
    {z : G} (hz : z ∈ A) (hz1 : z ≠ 1) : starQuot G z ≠ 1 := by
  intro h1
  have hzP : z ∈ CFSG.pPrimeCore 3 G := by
    rwa [starQuot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hinf := inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hA
    (not_three_dvd_card_pPrimeCore (G := G))
  have hz' : z ∈ A ⊓ CFSG.pPrimeCore 3 G := ⟨hz, hzP⟩
  rw [hinf, Subgroup.mem_bot] at hz'
  exact hz1 hz'

theorem ys03_I04a2_T_le_centralizer {G : Type} [Group G] [Finite G] {A L J T : Subgroup G} {z : G}
    (hL : L ∈ thetaComponents 3 G) (h3L : 3 ∣ Nat.card L) (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hA3 : IsPGroup 3 A) (hT3 : IsPGroup 3 T) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hTJ : T ≤ J)
    (hzA : z ∈ A) (hz1 : z ≠ 1) (hzJ : z ∈ J) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hC : Nat.card (A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) ≤ 3)
    (hdec : ∀ a ∈ A.map (starQuot G), ∃ c ∈ A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)), ∃ b ∈ L.map (starQuot G), a = c * b) :
    T ≤ Subgroup.centralizer (A : Set G) := by
  have hLc : IsComponent (L.map (starQuot G)) := isComponent_map_starQuot hL h3L
  have hJc : IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hLJ : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G), Commute x y := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hJc with hEq | hc
    · exact absurd (le_of_eq hEq.symm) hJL
    · exact ys03_I22_commute_of_bot hc
  have hz' : starQuot G z ≠ 1 := ys03_N13_map_ne_one hA3 hzA hz1
  have hzC : starQuot G z ∈ A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    ⟨⟨z, hzA, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (hLJ l hl (starQuot G z) ⟨z, hzJ, rfl⟩).eq⟩
  have hzle : Subgroup.zpowers (starQuot G z) ≤ A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (Subgroup.zpowers_le).mpr hzC
  have hord : 2 ≤ Nat.card (Subgroup.zpowers (starQuot G z)) := by
    rw [Nat.card_zpowers]
    have hpos : 0 < orderOf (starQuot G z) := orderOf_pos _
    have hne : orderOf (starQuot G z) ≠ 1 := fun h1 => hz' (orderOf_eq_one_iff.mp h1)
    omega
  have hdvd := Subgroup.card_dvd_of_le hzle
  have hCzp : Subgroup.zpowers (starQuot G z) = A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    refine Subgroup.eq_of_le_of_card_ge hzle ?_
    have key : ∀ a c : ℕ, a ∣ c → 2 ≤ a → c ≤ 3 → 0 < c → c ≤ a := by
      intro a c h1 h2 h3 h4
      obtain ⟨m, rfl⟩ := h1
      rcases m with _ | _ | m
      · omega
      · omega
      · nlinarith
    exact key _ _ hdvd hord hC Nat.card_pos
  have hinf := inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hT3
    (not_three_dvd_card_pPrimeCore (G := G))
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨c, hc, b, hb, hab⟩ := hdec (starQuot G a) ⟨a, ha, rfl⟩
  have hcz : c ∈ Subgroup.zpowers (starQuot G z) := hCzp ▸ hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  have hyz : Commute (starQuot G y) (starQuot G z) := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hTz hy) z (Set.mem_singleton z)
    exact (congrArg (starQuot G) h1).symm
  have hyc : Commute (starQuot G y) c := by
    rw [← hk]
    exact hyz.zpow_right k
  have hyb : Commute (starQuot G y) b :=
    (hLJ b hb (starQuot G y) ⟨y, hTJ hy, rfl⟩).symm
  have hya : Commute (starQuot G y) (starQuot G a) := by
    rw [hab]
    exact hyc.mul_right hyb
  have hcommT : y * a * y⁻¹ * a⁻¹ ∈ T := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hAT ha) y⁻¹).mp (T.inv_mem hy)
    have e : y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
    rw [e]
    exact T.mul_mem hy h1
  have hcommP : y * a * y⁻¹ * a⁻¹ ∈ CFSG.pPrimeCore 3 G := by
    have h1 : starQuot G (y * a * y⁻¹ * a⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hya.eq]
      group
    rwa [starQuot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : y * a * y⁻¹ * a⁻¹ ∈ T ⊓ CFSG.pPrimeCore 3 G := ⟨hcommT, hcommP⟩
  rw [hinf, Subgroup.mem_bot] at h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem ys03_I04a3_card_inf_le {G : Type} [Group G] [Finite G] {A L J : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (h3L : 3 ∣ Nat.card L) (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hA3 : IsPGroup 3 A)
    (hC : Nat.card (A.map (starQuot G) ⊓ Subgroup.centralizer
      (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) ≤ 3) :
    Nat.card (A ⊓ J : Subgroup G) ≤ 3 := by
  have hLc : IsComponent (L.map (starQuot G)) := isComponent_map_starQuot hL h3L
  have hJc : IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hLJ : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G), Commute x y := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hJc with hEq | hc
    · exact absurd (le_of_eq hEq.symm) hJL
    · exact ys03_I22_commute_of_bot hc
  have hle : (A ⊓ J).map (starQuot G) ≤ A.map (starQuot G) ⊓
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    rintro _ ⟨a, ⟨haA, haJ⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact (hLJ l hl (starQuot G a) ⟨a, haJ, rfl⟩).eq
  calc Nat.card (A ⊓ J : Subgroup G) = Nat.card ((A ⊓ J).map (starQuot G)) :=
        (ys03_N12_card_map_starQuot hA3.to_inf_left).symm
    _ ≤ _ := Subgroup.card_le_of_le hle
    _ ≤ 3 := hC

theorem ys03_I04a4_rank {G : Type} [Group G] [Finite G] {A E M : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hEA : E ≤ Subgroup.centralizer (A : Set G)) (hcap : Nat.card (A ⊓ E : Subgroup G) ≤ 3)
    (hM : A ⊔ E ≤ M) (hrk : CFSG.Open.pRank 3 M = 3) : False := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ E, Commute x y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hEA hy) x hx
  have hAE := ys03_I18_isElemAbelian_sup hA hE hcomm
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian_three hAE
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A E
    (fun x hx y hy => (hcomm x hx y hy).eq)).1
  rw [hk, hA27] at hcard
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have h3k : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 3 ^ k * Nat.card (A ⊓ E : Subgroup G) ≤ 3 ^ 3 * 3 := Nat.mul_le_mul h3k hcap
    omega
  have hle : k ≤ CFSG.Open.pRank 3 M :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three M)
      ⟨A ⊔ E, hM, hAE, hk⟩
  omega

theorem ys03_I04b_V_eq {Y : Type} [Group Y] {A' L' S : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) (hLp : Group.IsPerfect L')
    (hAab : IsMulCommutative A') (hA'S : A' ≤ S) (hL'S : L' ≤ S) (hS : S ≤ A' ⊔ L')
    {U V : Subgroup ↥S} (hUV : U ⊔ V = ⊤) (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : IsHeisThree U)
    (hVe : Nonempty (↥V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup ↥S) = 3) : V.map S.subtype = L' := by
  have hcom : commutator ↥S = V := KFacts.KS18.commutator_eq_of_isHeisSL hUV hcomm hU hVe h3
  have hSN : S ≤ Subgroup.normalizer (L' : Set Y) :=
    hS.trans (sup_le hAL Subgroup.le_normalizer)
  have hLn : (L'.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL'S).mpr hSN
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (L'.subgroupOf S)).comp (A'.subgroupOf S).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx : (x : Y) ∈ ((A' ⊔ L' : Subgroup Y) : Set Y) := hS x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A' L' hAL] at hx
    obtain ⟨a, ha, l, hl, hxal⟩ := hx
    refine ⟨⟨⟨a, hA'S ha⟩, ha⟩, ?_⟩
    change QuotientGroup.mk' (L'.subgroupOf S) ⟨a, hA'S ha⟩ = QuotientGroup.mk' (L'.subgroupOf S) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have : ((⟨a, hA'S ha⟩ : S)⁻¹ * x : S) = ⟨l, hL'S hl⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxal]
      group
    rw [this]
    exact hl
  have hcommA : ∀ a₁ a₂ : ↥(A'.subgroupOf S), a₁ * a₂ = a₂ * a₁ := by
    intro a₁ a₂
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val (hAab.is_comm.comm ⟨a₁.1.1, a₁.2⟩ ⟨a₂.1.1, a₂.2⟩)
    simpa using this
  have hab : ∀ p q : ↥S ⧸ L'.subgroupOf S, p * q = q * p := by
    intro p q
    obtain ⟨a₁, rfl⟩ := hsurj p
    obtain ⟨a₂, rfl⟩ := hsurj q
    rw [← map_mul, ← map_mul, hcommA a₁ a₂]
  have h1 : commutator ↥S ≤ L'.subgroupOf S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    have hx := map_commutatorElement (QuotientGroup.mk' (L'.subgroupOf S)) x y
    simp only [QuotientGroup.mk'_apply] at hx
    rw [hx]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hab _ _)
  have hL''perf : Group.IsPerfect ↥(L'.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hL'S).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have h2 : L'.subgroupOf S ≤ commutator ↥S := by
    calc L'.subgroupOf S = ⁅L'.subgroupOf S, L'.subgroupOf S⁆ :=
          (Subgroup.isPerfect_iff.mp hL''perf).symm
      _ ≤ ⁅(⊤ : Subgroup ↥S), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator ↥S := (commutator_def _).symm
  have hVeq : V = L'.subgroupOf S := le_antisymm (hcom ▸ h1) (hcom ▸ h2)
  rw [hVeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL'S]

theorem ys03_N15_equiv_of_map_eq {Y : Type} [Group Y] {S L' : Subgroup Y} {V : Subgroup ↥S}
    {T : Type} [Group T] (hVL : V.map S.subtype = L') (hVe : Nonempty (↥V ≃* T)) :
    Nonempty (↥L' ≃* T) :=
  ⟨((MulEquiv.subgroupCongr hVL.symm).trans
    (V.equivMapOfInjective S.subtype S.subtype_injective).symm).trans hVe.some⟩

theorem ys03_I08a_sectionFourHyp_map {G : Type} [Group G] [Finite G] (h1 : Item4_1LargePrime)
    (hG : SectionFourHyp G) {J : Subgroup G} (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) : SectionFourHyp ↥(J.map (starQuot G)) := by
  obtain ⟨η, -⟩ := exists_thetaQuot_equiv_map_starQuot hJ h3J
  exact Census.sectionFourHyp_of_mulEquiv η (Item41Narrow.sectionFourHyp_thetaQuotient h1 hG hJ)

theorem ys03_two_pow_mod_three (e : ℕ) :
    (Even e ∧ 2 ^ e % 3 = 1) ∨ (Odd e ∧ 2 ^ e % 3 = 2) := by
  induction e with
  | zero => left; exact ⟨⟨0, rfl⟩, by norm_num⟩
  | succ n ih =>
    rw [pow_succ]
    rcases ih with ⟨hn, h⟩ | ⟨hn, h⟩
    · right
      exact ⟨hn.add_one, by omega⟩
    · left
      exact ⟨hn.add_one, by omega⟩

theorem ys03_I09_branch {Y : Type} [Group Y] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hY : IsoLThreePi Y p e) (hsec : HasSection Y (projSL 3 (GaloisField 2 2)))
    (hSL : L34SectionPSL3Odd) (hSU : L34SectionPSU3Odd) (hSUe : L34SectionPSU3Even) :
    p = 2 ∧ Even e ∧ Nonempty (Y ≃* projSL 3 (GaloisField 2 e)) := by
  rcases hY with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · by_cases hp2 : p = 2
    · subst hp2
      have hev : Even e := by
        rcases ys03_two_pow_mod_three e with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · omega
      exact ⟨rfl, hev, ⟨f⟩⟩
    · exact absurd (KFacts.L34.hasSection_of_injective hsec f.toMonoidHom f.injective)
        (hSL p e hp2 he)
  · by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd e := by
        rcases ys03_two_pow_mod_three e with ⟨_, h⟩ | ⟨h, _⟩
        · omega
        · exact h
      exact absurd (KFacts.L34.hasSection_of_injective hsec f.toMonoidHom f.injective)
        (hSUe e hodd)
    · exact absurd (KFacts.L34.hasSection_of_injective hsec f.toMonoidHom f.injective)
        (hSU p e hp2 he)

open CFSG.Assembly.LowTwoRank in
theorem ys03_I09_cover {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) (hZ : Subgroup.center X ≠ ⊥) {e : ℕ} (he : 1 ≤ e)
    (h1 : 2 ^ e % 3 = 1) (f : X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 2 e)) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 e)) := by
  have : Group.IsPerfect X := hq.1
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hK : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  have e' : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL 3 (GaloisField 2 e)) :=
    f.trans ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL 3 _))).symm
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 3 (GaloisField 2 e)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSL 3 (GaloisField 2 e) →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hC hoddπ
    obtain ⟨s, hs, -⟩ :=
      SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := 3)
        (by norm_num) hπ hC hoddπ
    exact ⟨s, hs⟩
  obtain ⟨φ⟩ := Census.nonempty_mulEquiv_of_odd_splitting hodd hZ e'
    (Census.card_scalars_dvd_three (Or.inl ⟨hK, rfl⟩)) hsplit
  exact ⟨φ.trans (specialLinearGroupEquivStatedSL 3 _).symm⟩

theorem ys03_N08_isElemAbelian_of_card_three {X : Type} [Group X] {Z : Subgroup X}
    (h : Nat.card Z = 3) : CFSG.Assembly.IsElemAbelian 3 Z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic Z := isCyclic_of_prime_card h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
  · exact (IsCyclic.commGroup (α := Z)).mul_comm a b
  · have := pow_card_eq_one' (x := (⟨g, hg⟩ : Z))
    rw [h] at this
    exact congrArg Subtype.val this

theorem ys03_isExtOf_of_center_card_three {X A : Type} [Group X] [Finite X] [Group A]
    (hZ : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* A) :
    IsExtOf X A (Multiplicative (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic (Subgroup.center X) := isCyclic_of_prime_card hZ
  have e3 : Multiplicative (ZMod (Nat.card (Subgroup.center X))) ≃* Subgroup.center X :=
    zmodCyclicMulEquiv hcyc
  rw [hZ] at e3
  exact ⟨Subgroup.center X, inferInstance, ⟨e3.symm⟩, ⟨e⟩⟩

theorem ys03_N07_center_isPGroup {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : J ∈ thetaComponents 3 G) (h3J : 3 ∣ Nat.card J) :
    IsPGroup 3 (Subgroup.center ↥(J.map (starQuot G))) := by
  have hP := DiagSetting.center_isPGroup_three (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) 3)
    (isComponent_map_starQuot hJ h3J)
  exact IsPGroup.of_injective hP
    (Subgroup.equivMapOfInjective (Subgroup.center ↥(J.map (starQuot G)))
      (J.map (starQuot G)).subtype (J.map (starQuot G)).subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective _ _ _).injective

theorem ys03_exclude_of_E81 {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L) (hJ : J ∈ thetaComponents 3 G)
    (hL : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hZ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.center ↥(J.map (starQuot G))) ∧
      Subgroup.center ↥(J.map (starQuot G)) ≠ ⊥ ∧
      Nat.card (Subgroup.center ↥(J.map (starQuot G))) ≤ 9)
    {Q : Type} [Group Q] (hU : ∃ V : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V) :
    ¬ Nonempty (↥(J.map (starQuot G)) ⧸ Subgroup.center ↥(J.map (starQuot G)) ≃* Q) := by
  intro hne
  obtain ⟨e⟩ := hne
  obtain ⟨V, hVab, hV81⟩ := hU
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ys03_I22_rank_contradiction h hL hJ hJL hZ
    ⟨V.map e.symm.toMonoidHom, CFSG.Open.IsElemAbelian.map hVab _, ?_⟩
  rw [Subgroup.card_map_of_injective hinj]
  exact hV81

theorem ys03_N09_coverCenterThree_M22 (hC : Census.CoverCenterThree) {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (h : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.M22)) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  hC X hq hZ3 (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem ys03_N09_coverCenterThree_McL (hC : Census.CoverCenterThree) {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (h : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL)) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  hC X hq hZ3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem ys03_N09_coverCenterThree_ON (hC : Census.CoverCenterThree) {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (h : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  hC X hq hZ3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem ys03_C_not_alternating {Y : Type} [Group Y] {m : ℕ} (hm : m = 6 ∨ m = 7)
    (he : Nonempty (Y ≃* alternatingGroup (Fin m)))
    (hsec : HasSection Y (projSL 3 (GaloisField 2 2))) : False := by
  obtain ⟨e⟩ := he
  haveI : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hd := KFacts.L34.hasSection_card_dvd hsec
  rcases hm with rfl | rfl
  · rw [KFacts.L34.card_projSL, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin] at hd
    exact absurd hd (by decide)
  · rw [KFacts.L34.card_projSL, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin] at hd
    exact absurd hd (by decide)

theorem ys03_C_core (hI : DiagInputs) {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hSFH : SectionFourHyp X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (h3Z : 3 ∣ Nat.card (Subgroup.center X))
    (hsec : HasSection (X ⧸ Subgroup.center X) (projSL 3 (GaloisField 2 2)))
    (hexG2J3 : ¬ (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3)))
    (hexE81 : ∀ {Q : Type} [Group Q],
      (∃ V : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V) →
      (CFSG.Assembly.IsElemAbelian 3 (Subgroup.center X) ∧ Subgroup.center X ≠ ⊥ ∧
        Nat.card (Subgroup.center X) ≤ 9) → ¬ Nonempty (X ⧸ Subgroup.center X ≃* Q)) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 2 (2 * m))) ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * m)))) ∨
      (Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.M22) ∧
        Nat.card (Subgroup.center X) = 3) := by
  have hZne : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3Z
    omega
  have hcard3 : Nat.card (Subgroup.center X) ∣ 3 → Nat.card (Subgroup.center X) = 3 := fun hd => by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · rw [h1] at h3Z
      omega
    · exact h1
  have hZab : Nat.card (Subgroup.center X) = 3 →
      CFSG.Assembly.IsElemAbelian 3 (Subgroup.center X) ∧ Subgroup.center X ≠ ⊥ ∧
        Nat.card (Subgroup.center X) ≤ 9 := fun hc =>
    ⟨ys03_N08_isElemAbelian_of_card_three hc, hZne, by omega⟩
  rcases hI.item43 X hSFH hq h3Z with ⟨p, e, hp, he, hY⟩ | hA6 | hA7 | hG2 | hU43 | hM22 | hJ3 |
      hMcL | hON
  · haveI := hp
    obtain ⟨hp2, hev, ⟨f⟩⟩ :=
      ys03_I09_branch he hY hsec hI.l34PSL3Odd hI.l34PSU3Odd hI.l34PSU3Even
    subst hp2
    have h1 : 2 ^ e % 3 = 1 := by
      rcases ys03_two_pow_mod_three e with ⟨_, h⟩ | ⟨hodd, _⟩
      · exact h
      · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)
    obtain ⟨m, hm⟩ := hev
    obtain rfl : e = 2 * m := by omega
    exact Or.inl ⟨m, by omega, ⟨f⟩, ys03_I09_cover hq hZ3 hZne he h1 f⟩
  · exact (ys03_C_not_alternating (Or.inl rfl) hA6 hsec).elim
  · exact (ys03_C_not_alternating (Or.inr rfl) hA7 hsec).elim
  · exact (hexG2J3 (Or.inl hG2)).elim
  · obtain ⟨hz1, hz2⟩ := hI.coverU43Elem X hq hZ3 hU43
    exact (hexE81 hI.e81U43 ⟨hz1, hZne, hz2⟩ hU43).elim
  · exact Or.inr ⟨hM22, hcard3 (ys03_N09_coverCenterThree_M22 hI.coverCenterThree hq hZ3 hM22)⟩
  · exact (hexG2J3 (Or.inr hJ3)).elim
  · have hc := hcard3 (ys03_N09_coverCenterThree_McL hI.coverCenterThree hq hZ3 hMcL)
    exact (hexE81 hI.e81McL (hZab hc) hMcL).elim
  · have hc := hcard3 (ys03_N09_coverCenterThree_ON hI.coverCenterThree hq hZ3 hON)
    exact (hexE81 hI.e81ON (hZab hc) hON).elim

theorem ys03_I08_classify (hI : DiagInputs)
    {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G} {L J : Subgroup G}
    (h : DiagSetting G A M H s L) (hJ : J ∈ thetaComponents 3 G) (h3J : 3 ∣ Nat.card J)
    (hL4 : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (h3Z : 3 ∣ Nat.card (Subgroup.center ↥(J.map (starQuot G))))
    (hsec : HasSection (↥(J.map (starQuot G)) ⧸ Subgroup.center ↥(J.map (starQuot G)))
      (projSL 3 (GaloisField 2 2))) :
    (∃ m : ℕ, 1 ≤ m ∧
        Nonempty (↥(J.map (starQuot G)) ⧸ Subgroup.center ↥(J.map (starQuot G)) ≃*
          projSL 3 (GaloisField 2 (2 * m))) ∧
        Nonempty (↥(J.map (starQuot G)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * m)))) ∨
      (Nonempty (↥(J.map (starQuot G)) ⧸ Subgroup.center ↥(J.map (starQuot G)) ≃*
          Blueprint.NativeSporadic.M22) ∧
        Nat.card (Subgroup.center ↥(J.map (starQuot G))) = 3) :=
  ys03_C_core hI (isComponent_map_starQuot hJ h3J).1
    (ys03_I08a_sectionFourHyp_map hI.item41LargePrime h.ctx.ctx444.sectionFourHyp hJ h3J)
    (ys03_N07_center_isPGroup hJ h3J) h3Z hsec
    (ys03_I06_not_G2_J3 h hJ hsec)
    (fun hU hZ => ys03_exclude_of_E81 h hJ hL4 hJL hZ hU)

theorem ys03_N10_quotient_center_projSL {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :
    Nonempty (X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 2 2)) :=
  ⟨(QuotientGroup.congr (Subgroup.center X)
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) e
    (Subgroup.map_center_eq e)).trans specialLinearQuotientCenterEquiv⟩

theorem ys03_N11_isExtOf_of_mulEquiv {X Y A B : Type} [Group X] [Group Y] [Group A] [Group B]
    (e : X ≃* Y) (h : IsExtOf Y A B) : IsExtOf X A B := by
  obtain ⟨K, hK, ⟨eB⟩, ⟨eA⟩⟩ := h
  refine ⟨K.comap e.toMonoidHom, Subgroup.Normal.comap hK _, ⟨?_⟩, ⟨?_⟩⟩
  · exact (((K.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective K))).trans eB
  · exact (QuotientGroup.congr (K.comap e.toMonoidHom) K e
      (Subgroup.map_comap_eq_self_of_surjective e.surjective K)).trans eA

theorem ys03_D0a_solvable_quotient {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : X ∈ thetaComponents 3 G) (h3X : 3 ∣ Nat.card X) {T : Type} [Group T]
    (hZ3 : Nat.card (Subgroup.center ↥(X.map (starQuot G))) = 3)
    (e : ↥(X.map (starQuot G)) ⧸ Subgroup.center ↥(X.map (starQuot G)) ≃* T) :
    ∃ (K : Subgroup X) (_ : K.Normal), Group.IsSolvable K ∧ ¬ 9 ∣ Nat.card K ∧
      Nonempty (↥X ⧸ K ≃* T) := by
  obtain ⟨η, hη⟩ := exists_thetaQuot_equiv_map_starQuot hX h3X
  haveI : Group.IsSolvable (aschbacherSolvableCore 3 ↥X) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  let φ : ↥X →* ↥(X.map (starQuot G)) :=
    η.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
  have hφs : Function.Surjective φ := η.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : ∀ x : ↥X, φ x = 1 ↔ x ∈ aschbacherSolvableCore 3 ↥X := by
    intro x
    change η (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let K : Subgroup ↥X := (Subgroup.center ↥(X.map (starQuot G))).comap φ
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance φ
  have hθK : aschbacherSolvableCore 3 ↥X ≤ K := fun x hx =>
    Subgroup.mem_comap.mpr (by rw [(hφker x).mpr hx]; exact Subgroup.one_mem _)
  let g : K →* Subgroup.center ↥(X.map (starQuot G)) :=
    (φ.comp K.subtype).codRestrict _ (fun k => k.2)
  have hgs : Function.Surjective g := by
    intro z
    obtain ⟨x, hx⟩ := hφs z.1
    exact ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact z.2)⟩, Subtype.ext hx⟩
  have hgker : ∀ k : K, g k = 1 → (k : ↥X) ∈ aschbacherSolvableCore 3 ↥X := fun k hk =>
    (hφker k).mp (congrArg Subtype.val hk)
  refine ⟨K, hKn, ?_, ?_, ?_⟩
  · refine solvable_of_ker_le_range (Subgroup.inclusion hθK) g ?_
    intro k hk
    exact ⟨⟨k, hgker k hk⟩, Subtype.ext rfl⟩
  · have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv] at hcard
    have hZ3' : Nat.card (Subgroup.center ↥(X.map (starQuot G))) = 3 := hZ3
    rw [hZ3'] at hcard
    have hker3 : ¬ 3 ∣ Nat.card g.ker := by
      intro h3
      let ι : ↥g.ker →* ↥(aschbacherSolvableCore 3 ↥X) :=
        { toFun := fun k => ⟨((k : K) : ↥X), hgker k k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hι : Function.Injective ι := fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun z : ↥(aschbacherSolvableCore 3 ↥X) => (z : ↥X)) hab))
      exact three_not_dvd_card_aschbacherSolvableCore (G := ↥X)
        (h3.trans (Subgroup.card_dvd_of_injective ι hι))
    intro h9
    rw [hcard] at h9
    exact hker3 (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (by simpa using h9))
  · let ρ : ↥X →* ↥(X.map (starQuot G)) ⧸ Subgroup.center ↥(X.map (starQuot G)) :=
      (QuotientGroup.mk' _).comp φ
    have hρs : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hφs
    have hρker : ρ.ker = K := by
      ext x
      simp [ρ, K, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)).trans e⟩

theorem ys03_D0b_quasisimple_of_residualAt {X : Type} [Group X] [Finite X] {T : Type} [Group T]
    [IsSimpleGroup T] (hres : ResidualAt T) (hX : SectionFourHyp X) [Group.IsPerfect X]
    {K : Subgroup X} [K.Normal] (hK : Group.IsSolvable K) (h9 : ¬ 9 ∣ Nat.card K)
    (ψ : X ⧸ K ≃* T) : IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (X ⧸ K) := ψ.isSimpleGroup
  have hNn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hNK : CFSG.pCore 2 X ≤ K := Census.le_of_isSolvable_of_normal hNn
    (isSolvable_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := X)))
  have hKbn : (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKbs : Group.IsSolvable (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap_surjective K)
  have hKb9 : ¬ 9 ∣ Nat.card (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) := fun h =>
    h9 (h.trans (Subgroup.card_map_dvd _ _))
  exact hres _ (sectionFourHyp_quotient_pCore_two hX) inferInstance
    (Sec18.pCore_quotient_pCore_eq_bot 2) (K.map (QuotientGroup.mk' (CFSG.pCore 2 X))) hKbs hKb9
    ⟨(QuotientGroup.quotientQuotientEquivQuotient _ K hNK).trans ψ⟩

open CFSG.LocalCores in
theorem ys03_D0c_isPGroup_two {L : Type} [Group L] [Finite L] {T : Type} [Group T] [IsSimpleGroup T]
    (hmult : CenterThreePrimeTwoAt T) (hTc : Subgroup.center T = ⊥) [Group.IsPerfect L]
    (hq : IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {K : Subgroup L} [K.Normal] (ψ : L ⧸ K ≃* T) :
    IsPGroup 2 (aschbacherSolvableCore 3 L) := by
  set O := CFSG.pCore 2 L with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have : IsSimpleGroup (L ⧸ K) := ψ.isSimpleGroup
  have hOK : O ≤ K := Census.pCore_le 2
  set χ : L ⧸ O →* T := ψ.toMonoidHom.comp (QuotientGroup.map O K (MonoidHom.id L) hOK) with hχ
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨q, rfl⟩ := ψ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact ⟨(x : L ⧸ O), rfl⟩
  have hker : χ.ker = Subgroup.center (L ⧸ O) := by
    apply le_antisymm
    · rcases quasisimple_normal_subgroups hq (N := χ.ker) inferInstance with h | h
      · exfalso
        have : Nontrivial T := IsSimpleGroup.toNontrivial
        obtain ⟨y, hy⟩ := exists_ne (1 : T)
        obtain ⟨x, rfl⟩ := hχs y
        exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
      · exact h
    · intro z hz
      have h1 : χ z ∈ Subgroup.center T := Subgroup.map_center_le_center hχs ⟨z, hz, rfl⟩
      rw [hTc] at h1
      exact h1
  set eX : (L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχs) with heX
  obtain ⟨hθs, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set Z := (aschbacherSolvableCore 3 L).map (QuotientGroup.mk' O) with hZ
  have hZn : Z.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hZc : Z ≤ Subgroup.center (L ⧸ O) := by
    rcases quasisimple_normal_subgroups hq (N := Z) hZn with h | h
    · exfalso
      have hs : Group.IsSolvable (L ⧸ O) := by
        refine Group.isSolvable_of_surjective
          (f := (QuotientGroup.mk' O).comp (aschbacherSolvableCore 3 L).subtype) ?_
        intro y
        have hy : y ∈ Z := h ▸ Subgroup.mem_top y
        obtain ⟨t, ht, rfl⟩ := hy
        exact ⟨⟨t, ht⟩, rfl⟩
      have : Nontrivial (L ⧸ O) := isQuasisimple_nontrivial hq
      have : Group.IsPerfect (L ⧸ O) := inferInstance
      exact Group.IsPerfect.not_isSolvable (L ⧸ O) hs
    · exact h
  have h3Z : ¬ 3 ∣ Nat.card Z := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hZ2 := hmult (L ⧸ O) hq ⟨eX⟩ Z hZc h3Z
  intro t
  obtain ⟨k, hk⟩ := hZ2 ⟨QuotientGroup.mk' O t, t, t.2, rfl⟩
  have h1 : ((t : L) ^ 2 ^ k) ∈ O := by
    have h2 : (QuotientGroup.mk' O (t : L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 O) ⟨_, h1⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h3 : ((t : L) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
  exact h3

theorem ys03_D0d_iso {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : X ∈ thetaComponents 3 G)
    (h3X : 3 ∣ Nat.card X) (hθ : IsPGroup 2 (aschbacherSolvableCore 3 X)) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(X.map (starQuot G))) := by
  obtain ⟨η, -⟩ := exists_thetaQuot_equiv_map_starQuot hX h3X
  have hθO : aschbacherSolvableCore 3 ↥X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨inferInstance, hθ⟩
  have hOθ : CFSG.pCore 2 ↥X ≤ aschbacherSolvableCore 3 ↥X :=
    le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) CFSG.pCore_normal
      CFSG.pCore_isPGroup
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hOθ hθO)).trans η⟩

theorem ys03_D0e_center_bot {Q : Type} [Group Q] (hq : IsQuasisimple Q) {T : Type} [Group T]
    (e : Q ⧸ Subgroup.center Q ≃* T) : IsSimpleGroup T ∧ Subgroup.center T = ⊥ := by
  have : Group.IsPerfect Q := hq.1
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2.1
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  have h := Group.IsPerfect.center_quotient_center_eq_bot Q
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

theorem ys03_D0_generic {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G) {X : Subgroup G}
    (hX : X ∈ thetaComponents 3 G) (h3X : 3 ∣ Nat.card X) {T : Type} [Group T]
    (hZ3 : Nat.card (Subgroup.center ↥(X.map (starQuot G))) = 3)
    (e : ↥(X.map (starQuot G)) ⧸ Subgroup.center ↥(X.map (starQuot G)) ≃* T)
    (hres : ResidualAt T) (hmult : CenterThreePrimeTwoAt T) :
    X ∈ oTwoComponents G ∧ Nonempty (X ⧸ CFSG.pCore 2 X ≃* ↥(X.map (starQuot G))) := by
  obtain ⟨K, hKn, hKs, h9, ⟨ψ⟩⟩ := ys03_D0a_solvable_quotient hX h3X hZ3 e
  haveI := hKn
  haveI : Group.IsPerfect ↥X := hX.1
  obtain ⟨hTs, hTc⟩ := ys03_D0e_center_bot (isComponent_map_starQuot hX h3X).1 e
  haveI := hTs
  have hq := ys03_D0b_quasisimple_of_residualAt hres (sectionFourHyp_subgroup hG X) hKs h9 ψ
  exact ⟨⟨hX.1, hX.2.1, hq⟩, ys03_D0d_iso hX h3X (ys03_D0c_isPGroup_two hmult hTc hq ψ)⟩

theorem ys03_I14a1_L_witness {Y : Type} [Group Y] [Finite Y] {Lq : Subgroup Y}
    (e : Nonempty (↥Lq ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) :
    ∃ R : Subgroup Y, R ≤ Lq ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ ∃ E : Subgroup Y,
      E ≤ Lq ⊓ Subgroup.normalizer (R : Set Y) ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 := by
  obtain ⟨e⟩ := e
  have hψi : Function.Injective (Lq.subtype.comp e.symm.toMonoidHom) :=
    Lq.subtype_injective.comp e.symm.injective
  have hψX : ∀ k, (Lq.subtype.comp e.symm.toMonoidHom) k ∈ Lq := fun k => (e.symm k).2
  have hk2 : 2 ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    (KFacts.L34.localRank_three_specialLinearGroup KFacts.L34.card_galoisField_two_two).ge
  exact ys03_I22_witness_map _ hψi hψX hk2

theorem ys03_N14_two_le_pRank_of_SL34 {Y : Type} [Group Y] [Finite Y] {Lq : Subgroup Y}
    (e : Nonempty (↥Lq ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) :
    1 < CFSG.Open.pRank 3 Lq := by
  obtain ⟨R, -, -, -, E, hE, hEab, hEc⟩ := ys03_I14a1_L_witness e
  exact lt_of_lt_of_le (by norm_num : 1 < 2)
    (le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three Lq)
      ⟨E, fun x hx => (hE hx).1, hEab, hEc⟩)

theorem ys03_I14a_rank_two_components {G : Type} [Group G] [Finite G] {A M H : Subgroup G}
    {s : G} {L J : Subgroup G} (h : DiagSetting G A M H s L)
    (hL4 : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJc : IsComponent (J.map (starQuot G))) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hZJ : Nat.card (Subgroup.center ↥(J.map (starQuot G))) = 3)
    (hJrk : 1 < CFSG.Open.pRank 3 (J.map (starQuot G)))
    {K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hK : IsComponent K)
    (hKrk : 1 < CFSG.Open.pRank 3 K) :
    K = L.map (starQuot G) ∨ K = J.map (starQuot G) := by
  by_contra hne
  push Not at hne
  obtain ⟨hKL, hKJ⟩ := hne
  have hLc : IsComponent (L.map (starQuot G)) := isComponent_map_starQuot h.mem h.three_dvd
  have hcomm : ∀ {P Q : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)}, IsComponent P → IsComponent Q →
      P ≠ Q → ∀ x ∈ P, ∀ y ∈ Q, Commute x y := by
    intro P Q hP hQ hPQ
    rcases CFSG.LocalCores.distinct_components_commute hP hQ with hEq | hc
    · exact absurd hEq hPQ
    · exact ys03_I22_commute_of_bot hc
  have hLJ : L.map (starQuot G) ≠ J.map (starQuot G) := fun heq => hJL (le_of_eq heq.symm)
  have h12 := hcomm hLc hJc hLJ
  have h13 := hcomm hLc hK (Ne.symm hKL)
  have h23 := hcomm hJc hK (Ne.symm hKJ)
  have hH := DiagSetting.localRank_three_quotient_le h.ctx.ctx444.sectionFourHyp
  have hZL : Nat.card (Subgroup.center ↥(L.map (starQuot G))) = 3 :=
    KFacts.L34.card_center_of_mulEquiv hL4.some
  have hXY : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G) ⊔ K, Commute x y := by
    intro x hx y hy
    have hle : J.map (starQuot G) ⊔ K ≤ Subgroup.centralizer ({x} : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
      sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr (fun g hg => by
          rw [Set.mem_singleton_iff] at hg; subst hg; exact (h12 g hx z hz).eq))
        (fun z hz => Subgroup.mem_centralizer_iff.mpr (fun g hg => by
          rw [Set.mem_singleton_iff] at hg; subst hg; exact (h13 g hx z hz).eq))
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x (Set.mem_singleton x)
  have hcap1 : Nat.card (L.map (starQuot G) ⊓ (J.map (starQuot G) ⊔ K) :
      Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) ≤ 3 := (ys03_I22_cap_le hXY).trans hZL.le
  have hcap2 : Nat.card (J.map (starQuot G) ⊓ K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) ≤ 3 :=
    (ys03_I22_cap_le h23).trans hZJ.le
  obtain ⟨R, hRX, hR2, hR1, E₁, hE₁, hE₁ab, hE₁card⟩ := ys03_I14a1_L_witness hL4
  obtain ⟨E₂, hE₂, hE₂ab, hE₂card⟩ := Sec5.exists_elemAbelian_le_of_le_pRank Nat.prime_three
    (show 2 ≤ CFSG.Open.pRank 3 (J.map (starQuot G)) from hJrk)
  obtain ⟨E₃, hE₃, hE₃ab, hE₃card⟩ := Sec5.exists_elemAbelian_le_of_le_pRank Nat.prime_three
    (show 2 ≤ CFSG.Open.pRank 3 K from hKrk)
  have := ys03_I18_three_factors hH h12 h13 h23 hcap1 hcap2 hRX hR2 hR1
    ⟨E₁, hE₁, hE₁ab, hE₁card⟩ ⟨E₂, hE₂, hE₂ab, hE₂card⟩ ⟨E₃, hE₃, hE₃ab, hE₃card⟩
  omega

theorem ys03_I14b_map_I_le {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L) (hSz : KFacts.KPSz)
    (hS : SchreierFor CFSG.Assembly.InCatalog) (h45 : Item4_5)
    (hL4 : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJc : IsComponent (J.map (starQuot G))) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hZJ : Nat.card (Subgroup.center ↥(J.map (starQuot G))) = 3)
    (hJrk : 1 < CFSG.Open.pRank 3 (J.map (starQuot G)))
    (hmv : ∀ K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), IsComponent K →
      ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
        Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G)) → 1 < CFSG.Open.pRank 3 K) :
    (inSubgroup perfectResidual H).map (starQuot G) ≤
      L.map (starQuot G) ⊔ J.map (starQuot G) := by
  have hLc : IsComponent (L.map (starQuot G)) := isComponent_map_starQuot h.mem h.three_dvd
  have hIL := DiagSetting.I_le_layer hSz hS h45 h
  have hcompT : ∀ T : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), IsComponent T →
      T ≠ L.map (starQuot G) → T ≠ J.map (starQuot G) →
      (inSubgroup perfectResidual H).map (starQuot G) ≤
        Subgroup.centralizer (T : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    intro T hT hTL hTJ
    by_contra hmov
    rcases ys03_I14a_rank_two_components h hL4 hJc hJL hZJ hJrk hT (hmv T hT hmov) with h1 | h1
    · exact hTL h1
    · exact hTJ h1
  obtain ⟨hEC, hlayer⟩ := CFSG.WholeGroup.layer_eq_sup_others hLc
  set E₀ := sSup {T : Subgroup (G ⧸ CFSG.pPrimeCore 3 G) | IsComponent T ∧
    T ≠ L.map (starQuot G) ∧ T ≠ J.map (starQuot G)} with hE₀
  have hE₀le : E₀ ≤ sSup {T : Subgroup (G ⧸ CFSG.pPrimeCore 3 G) | IsComponent T ∧
      T ≠ L.map (starQuot G)} := sSup_le_sSup fun T hT => ⟨hT.1, hT.2.1⟩
  have hlayer' : CFSG.layer (G ⧸ CFSG.pPrimeCore 3 G) ≤
      (L.map (starQuot G) ⊔ J.map (starQuot G)) ⊔ E₀ := by
    rw [hlayer]
    refine sup_le (le_sup_of_le_left le_sup_left) (sSup_le fun T hT => ?_)
    by_cases hTJ : T = J.map (starQuot G)
    · rw [hTJ]
      exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right (le_sSup ⟨hT.1, hT.2, hTJ⟩)
  have hE₀J : E₀ ≤ Subgroup.centralizer ((J.map (starQuot G) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) :
      Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    refine sSup_le fun T hT => ?_
    rcases CFSG.LocalCores.distinct_components_commute hJc hT.1 with hEq | hc
    · exact absurd hEq.symm hT.2.2
    · exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have hES : E₀ ≤ Subgroup.centralizer ((L.map (starQuot G) ⊔ J.map (starQuot G) :
      Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    rw [← Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mp (hE₀le.trans hEC)
    · exact Subgroup.le_centralizer_iff.mp hE₀J
  have hEI : E₀ ≤ Subgroup.centralizer (((inSubgroup perfectResidual H).map (starQuot G) :
      Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    sSup_le fun T hT => Subgroup.le_centralizer_iff.mp (hcompT T hT.1 hT.2.1 hT.2.2)
  have hperf : ⁅(inSubgroup perfectResidual H).map (starQuot G),
      (inSubgroup perfectResidual H).map (starQuot G)⁆ =
        (inSubgroup perfectResidual H).map (starQuot G) := by
    rw [← Subgroup.map_commutator, DiagSetting.commutator_I_eq H]
  exact ys03_I02_le_of_le_sup_commute
    (S := L.map (starQuot G) ⊔ J.map (starQuot G)) (E := E₀)
    (I := (inSubgroup perfectResidual H).map (starQuot G))
    (fun x hx e he => (Subgroup.mem_centralizer_iff.mp (hES he)) x hx)
    (fun i hi e he => (Subgroup.mem_centralizer_iff.mp (hEI he)) i hi)
    (hIL.trans hlayer') hperf

theorem ys03_I14c_I_le {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L)
    (hIJ : inSubgroup perfectResidual H ≤ Subgroup.normalizer (J : Set G))
    (hmap : (inSubgroup perfectResidual H).map (starQuot G) ≤
      L.map (starQuot G) ⊔ J.map (starQuot G)) :
    inSubgroup perfectResidual H ≤ L ⊔ J := by
  have hIp : Group.IsPerfect ↥(inSubgroup perfectResidual H) :=
    Subgroup.isPerfect_iff.mpr (DiagSetting.commutator_I_eq H)
  obtain ⟨eI⟩ := h.I_iso
  exact Res4443.le_of_map_starQuot_le_L34 hIp eI
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_sup L J ⟨h.I_norm hx, hIJ hx⟩)
    (by rw [Subgroup.map_sup]; exact hmap)

theorem ys03_I15_LJ_normal {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L)
    (hL4 : Nonempty (↥(L.map (starQuot G)) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJ : J ∈ thetaComponents 3 G) (h3J : 3 ∣ Nat.card J)
    (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hZJ : Nat.card (Subgroup.center ↥(J.map (starQuot G))) = 3)
    (hLrk : 1 < CFSG.Open.pRank 3 (L.map (starQuot G)))
    (hJrk : 1 < CFSG.Open.pRank 3 (J.map (starQuot G))) : (L ⊔ J).Normal := by
  have hJc : IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have key : ∀ X : Subgroup G, X ∈ thetaComponents 3 G → 3 ∣ Nat.card X →
      1 < CFSG.Open.pRank 3 (X.map (starQuot G)) → ∀ g : G,
        X.map (MulAut.conj g).toMonoidHom = L ∨ X.map (MulAut.conj g).toMonoidHom = J := by
    intro X hX h3X hXrk g
    have hYmem : X.map (MulAut.conj g).toMonoidHom ∈ thetaComponents 3 G :=
      map_conj_mem_thetaComponents hX g
    have h3Y : 3 ∣ Nat.card (X.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact h3X
    have hYc : IsComponent ((X.map (MulAut.conj g).toMonoidHom).map (starQuot G)) :=
      isComponent_map_starQuot hYmem h3Y
    have hcomp : (starQuot G).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (starQuot G g)).toMonoidHom.comp (starQuot G) := by
      ext x
      simp [MulAut.conj_apply, map_mul, map_inv]
    have hYimg : (X.map (MulAut.conj g).toMonoidHom).map (starQuot G) =
        (X.map (starQuot G)).map (MulAut.conj (starQuot G g)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hYrk : 1 < CFSG.Open.pRank 3 ((X.map (MulAut.conj g).toMonoidHom).map (starQuot G)) := by
      rw [hYimg]
      exact lt_of_lt_of_le hXrk (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective
        3 Nat.prime_three _ (MulAut.conj (starQuot G g)).injective _)
    rcases ys03_I14a_rank_two_components h hL4 hJc hJL hZJ hJrk hYc hYrk with h1 | h1
    · exact Or.inl (eq_of_map_starQuot_eq_of_mem_thetaComponents hYmem h.mem h3Y h.three_dvd h1)
    · exact Or.inr (eq_of_map_starQuot_eq_of_mem_thetaComponents hYmem hJ h3Y h3J h1)
  refine ⟨fun n hn g => ?_⟩
  have hL' := key L h.mem h.three_dvd hLrk g
  have hJ' := key J hJ h3J hJrk g
  have hle : (L ⊔ J).map (MulAut.conj g).toMonoidHom ≤ L ⊔ J := by
    rw [Subgroup.map_sup]
    rcases hL' with h1 | h1 <;> rcases hJ' with h2 | h2 <;> rw [h1, h2]
    · exact sup_le le_sup_left le_sup_left
    · exact sup_le le_sup_right le_sup_left
    · exact sup_le le_sup_right le_sup_right
  simpa using hle (Subgroup.mem_map_of_mem _ hn)

theorem ys03_I16_commutator_eq {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L) (hN : (L ⊔ J).Normal)
    (hIle : inSubgroup perfectResidual H ≤ L ⊔ J)
    (hJc : ⁅J, inSubgroup perfectResidual H⁆ = J) :
    ⁅inSubgroup perfectResidual H, ⊤⁆ = L ⊔ J := by
  have hLc : ⁅L, inSubgroup perfectResidual H⁆ = L :=
    commutator_eq_self_of_not_le_centralizer h.mem h.three_dvd h.I_norm h.I_nc
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro i hi g _
    rw [commutatorElement_def]
    have e : i * g * i⁻¹ * g⁻¹ = i * (g * i⁻¹ * g⁻¹) := by group
    rw [e]
    exact (L ⊔ J).mul_mem (hIle hi) (hN.conj_mem _ ((L ⊔ J).inv_mem (hIle hi)) g)
  · refine sup_le ?_ ?_
    · calc L = ⁅L, inSubgroup perfectResidual H⁆ := hLc.symm
        _ ≤ ⁅inSubgroup perfectResidual H, ⊤⁆ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mono le_rfl le_top
    · calc J = ⁅J, inSubgroup perfectResidual H⁆ := hJc.symm
        _ ≤ ⁅inSubgroup perfectResidual H, ⊤⁆ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mono le_rfl le_top

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
