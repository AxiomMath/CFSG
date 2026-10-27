module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Bender.CoreCentralizesCenter
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Mat
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.Goldschmidt.Setup
public import CFSG.Goldschmidt.OddCore
public import CFSG.Quasithin.Recognition.Stroth.SubconstNatural
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryTransport
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.H13.NQCoreP134Inputs
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3
  CFSG.GH74.Uniqueness.Bender CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Quasithin.H13.NQCore MulAction CFSG.LocalAnalysis.ComponentInitial
  CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
  CFSG.ProperTwoGeneratedCore.RootCenter

private theorem eq_bot_of_fixedPoints_eq_top {G : Type*} [Group G]
    {Ω : Type*} [MulAction G Ω] [FaithfulSMul G Ω] {N : Subgroup G}
    (h : MulAction.fixedPoints N Ω = ⊤) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
  intro x
  have hx : x ∈ MulAction.fixedPoints N Ω := by rw [h]; exact Set.mem_univ x
  have := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
  simpa using this

private theorem natCard_le_degree_of_commutes_with_transitive {Y : Type*} [Group Y]
    {Ω : Type*} [Fintype Ω] [MulAction Y Ω] [FaithfulSMul Y Ω]
    {P C : Subgroup Y} (hCtrans : MulAction.IsPretransitive C Ω)
    (hcomm : ∀ p ∈ P, ∀ c ∈ C, (p : Y) * (c : Y) = (c : Y) * (p : Y))
    (ω : Ω) : Nat.card P ≤ Fintype.card Ω := by
  classical
  let f : P → Ω := fun p => (p : Y) • ω
  have hf : Function.Injective f := by
    intro p q hpq
    have hpq' : (p : Y) • ω = (q : Y) • ω := hpq
    have hfix : ((q⁻¹ * p : P) : Y) • ω = ω := by
      change ((q : Y)⁻¹ * (p : Y)) • ω = ω
      rw [mul_smul, hpq']
      simp
    have hbase : ((q⁻¹ * p : P) : Y) = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
      intro x
      obtain ⟨c, hc, rfl⟩ := hCtrans.exists_smul_eq ω x
      have hcomm' : ((q⁻¹ * p : P) : Y) * (c : Y) = (c : Y) * ((q⁻¹ * p : P) : Y) :=
        hcomm _ (q⁻¹ * p).2 c c.2
      have hcalc : ((q⁻¹ * p : P) : Y) • ((c : Y) • ω) = (c : Y) • ω := by
        calc ((q⁻¹ * p : P) : Y) • ((c : Y) • ω)
            = (((q⁻¹ * p : P) : Y) * (c : Y)) • ω := (mul_smul _ _ _).symm
          _ = ((c : Y) * ((q⁻¹ * p : P) : Y)) • ω := by rw [hcomm']
          _ = (c : Y) • (((q⁻¹ * p : P) : Y) • ω) := mul_smul _ _ _
          _ = (c : Y) • ω := by rw [hfix]
      have hcalc' : ((q⁻¹ * p : P) : Y) • (c • ω) = (c • ω) := by
        simpa [subgroup_smul_def] using hcalc
      rw [hcalc']
      simp
    have hqp : q⁻¹ * p = 1 := Subtype.ext hbase
    calc p = q * (q⁻¹ * p) := by group
      _ = q * 1 := by rw [hqp]
      _ = q := mul_one q
  calc Nat.card P ≤ Nat.card Ω := Nat.card_le_card_of_injective f hf
    _ = Fintype.card Ω := Nat.card_eq_fintype_card

private theorem centralizer_eq_bot_of_two_transitive {Y : Type*} [Group Y] [Finite Y]
    {Ω : Type*} [Fintype Ω] [MulAction Y Ω] [FaithfulSMul Y Ω]
    {P : Subgroup Y} [P.Normal] (hPne : P ≠ ⊥)
    (h2 : MulAction.IsMultiplyPretransitive Y Ω 2)
    (hPcard : Fintype.card Ω < Nat.card P) (ω : Ω) :
    Subgroup.centralizer (P : Set Y) = ⊥ := by
  classical
  haveI : MulAction.IsPreprimitive Y Ω := MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive Y Ω := MulAction.IsPreprimitive.isQuasiPreprimitive
  have hPfix : MulAction.fixedPoints P Ω ≠ ⊤ := fun h =>
    hPne (eq_bot_of_fixedPoints_eq_top h)
  have hCtrans : ∀ {C : Subgroup Y}, C.Normal → C ≠ ⊥ → MulAction.IsPretransitive C Ω := by
    intro C _ hCne
    exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (fun h =>
      hCne (eq_bot_of_fixedPoints_eq_top h))
  let C : Subgroup Y := Subgroup.centralizer (P : Set Y)
  change C = ⊥
  by_cases hCbot : C = ⊥
  · exact hCbot
  · have hCne : C ≠ ⊥ := hCbot
    have hCtrans : MulAction.IsPretransitive C Ω := hCtrans (inferInstance : C.Normal) hCne
    have hcomm : ∀ p ∈ P, ∀ c ∈ C, (p : Y) * (c : Y) = (c : Y) * (p : Y) := by
      intro p hp c hc
      exact Subgroup.mem_centralizer_iff.mp hc p hp
    have hle := natCard_le_degree_of_commutes_with_transitive hCtrans hcomm ω
    omega

private theorem card_of_regular_on_compl {Y : Type*} [Group Y] {Ω : Type*} [MulAction Y Ω]
    [Fintype Ω] (R : Subgroup Y) (ω : Ω) (hRle : R ≤ MulAction.stabilizer Y ω)
    (hreg : ∀ a b : Ω, a ≠ ω → b ≠ ω → ∃! r : R, (r : Y) • a = b)
    (ω₁ : Ω) (hω₁ : ω₁ ≠ ω) : Nat.card R = Fintype.card Ω - 1 := by
  classical
  let f : R → {x : Ω // x ≠ ω} := fun r => ⟨(r : Y) • ω₁, by
    intro h
    have hrω : (r : Y) • ω = ω := MulAction.mem_stabilizer_iff.mp (hRle r.2)
    have h1 : ω₁ = (r : Y)⁻¹ • ω := by rw [← h, inv_smul_smul]
    have h2 : (r : Y)⁻¹ • ω = ω := by
      have := congrArg (fun x => (r : Y)⁻¹ • x) hrω
      simpa [mul_smul] using this.symm
    exact hω₁ (h1.trans h2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro r s hrs
      have hrs' : (r : Y) • ω₁ = (s : Y) • ω₁ := congrArg Subtype.val hrs
      have ht : ((s⁻¹ * r : R) : Y) • ω₁ = ω₁ := by
        change ((s : Y)⁻¹ * (r : Y)) • ω₁ = ω₁
        rw [mul_smul, hrs']
        simp
      have h1 : ((1 : R) : Y) • ω₁ = ω₁ := by simp
      have hts : s⁻¹ * r = 1 := (hreg ω₁ ω₁ hω₁ hω₁).unique ht h1
      calc r = s * (s⁻¹ * r) := by group
        _ = s * 1 := by rw [hts]
        _ = s := mul_one s
    · rintro ⟨x, hx⟩
      obtain ⟨r, hr, -⟩ := hreg ω₁ x hω₁ hx
      exact ⟨r, Subtype.ext hr⟩
  have hcard : Nat.card R = Nat.card {x : Ω // x ≠ ω} := Nat.card_congr (Equiv.ofBijective f hf)
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

private theorem card_abelian_two_le_psu3 {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ k) ^ 2) {P : Type} [Group P] [Finite P]
    (eP : P ≃* StatedProj (StatedSU 3 (2 ^ k) F)) {A : Subgroup P}
    (hA : IsMulCommutative A) (hA2 : IsPGroup 2 A) : Nat.card A ≤ (2 ^ k) ^ 2 := by
  let h : UnitaryFieldData 2 k F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨Rmat, hRmat⟩ := exists_isHypTransport h
  let e : hypPSU h 1 1 ≃* StatedProj (StatedSU 3 (2 ^ k) F) :=
    hypPSUEquivStatedProj h hRmat (by norm_num)
  let e' : P ≃* hypPSU h 1 1 := eP.trans e.symm
  let A' : Subgroup (hypPSU h 1 1) := A.map e'.toMonoidHom
  have hA'card : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective e'.injective
  have hA'comm : IsMulCommutative A' := CFSG.Goldschmidt.isMulCommutative_map hA e'.toMonoidHom
  have hA'2 : IsPGroup 2 A' := hA2.map e'.toMonoidHom
  obtain ⟨S, hS⟩ := exists_sylow_hypProjUnitriangular (h := h)
  obtain ⟨T, hA'T⟩ := hA'2.exists_le_sylow
  haveI : Finite (Sylow 2 (hypPSU h 1 1)) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypPSU h 1 1) T S
  have hcoe : ((g • T : Sylow 2 (hypPSU h 1 1)) : Subgroup (hypPSU h 1 1)) =
      (T : Subgroup (hypPSU h 1 1)).map (MulAut.conj g).toMonoidHom := by
    apply Subgroup.ext
    intro x
    change x ∈ ((g • T : Sylow 2 (hypPSU h 1 1)) : Set (hypPSU h 1 1)) ↔
      x ∈ ((T : Subgroup (hypPSU h 1 1)).map (MulAut.conj g).toMonoidHom : Set (hypPSU h 1 1))
    rw [Sylow.coe_smul]
    simp [Set.mem_smul_set, Subgroup.mem_map, MulAut.conj_apply]
  let A'' : Subgroup (hypPSU h 1 1) := A'.map (MulAut.conj g).toMonoidHom
  have hA''le : A'' ≤ (S : Subgroup (hypPSU h 1 1)) := by
    rw [← hg, hcoe]
    exact Subgroup.map_mono hA'T
  have hA''comm : IsMulCommutative A'' :=
    CFSG.Goldschmidt.isMulCommutative_map hA'comm (MulAut.conj g).toMonoidHom
  have hA''subComm : IsMulCommutative (A''.subgroupOf (S : Subgroup (hypPSU h 1 1))) :=
    CFSG.Goldschmidt.isMulCommutative_subgroupOf hA''comm _
  let E : Subgroup (hypProjUnitriangular h 1 1) :=
    (A''.subgroupOf (S : Subgroup (hypPSU h 1 1))).map
      (MulEquiv.subgroupCongr hS).toMonoidHom
  have hEcomm : IsMulCommutative E :=
    CFSG.Goldschmidt.isMulCommutative_map hA''subComm (MulEquiv.subgroupCongr hS).toMonoidHom
  have hEcard : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective (MulEquiv.subgroupCongr hS).injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA''le).toEquiv,
      show Nat.card A'' = Nat.card A' from
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hA'card
  let f : UHeis h ≃* ↥(hypProjUnitriangular h 1 1) := uBarEquiv
  let E' : Subgroup (UHeis h) := E.map f.symm.toMonoidHom
  have hE'card : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective f.symm.injective
  have hE'comm : IsMulCommutative E' :=
    CFSG.Goldschmidt.isMulCommutative_map hEcomm f.symm.toMonoidHom
  have hE'comm' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE'comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbound := UHeis.card_le_sq E' hE'comm'
  rw [hE'card, hEcard] at hbound
  exact hbound

private theorem card_psu3_gt_degree {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ k) ^ 2) :
    (2 ^ k) ^ 3 + 1 < Nat.card (StatedProj (StatedSU 3 (2 ^ k) F)) := by
  set q := 2 ^ k with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqpos : 0 < q := by omega
  have hcard0 := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd
    (K := F) (p := 2) (f := k) Nat.prime_two (by omega) hF
  have hcard : Nat.card (StatedProj (StatedSU 3 q F)) * Nat.gcd 3 (q + 1) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    simpa [hq] using hcard0
  have hdvd : Nat.gcd 3 (q + 1) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q + 1))
  have hkey : Nat.card (StatedProj (StatedSU 3 q F)) * 3 ≥
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    calc Nat.card (StatedProj (StatedSU 3 q F)) * 3
        ≥ Nat.card (StatedProj (StatedSU 3 q F)) * Nat.gcd 3 (q + 1) :=
          Nat.mul_le_mul_left _ hdvd
      _ = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := hcard
  have hprod : 6 * (q ^ 3 + 1) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    have hq2m1 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by nlinarith
      omega
    have hq3ge : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    have h6 : 6 ≤ q ^ 3 * (q ^ 2 - 1) := by nlinarith
    calc 6 * (q ^ 3 + 1) = 6 * (q ^ 3 + 1) := rfl
      _ ≤ (q ^ 3 * (q ^ 2 - 1)) * (q ^ 3 + 1) := Nat.mul_le_mul_right _ h6
      _ = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by ring
  omega

private theorem relIndex_inf_dvd_card_outer {Y : Type*} [Group Y] [Finite Y]
    {P R : Subgroup Y} [P.Normal]
    (hC : Subgroup.centralizer (P : Set Y) = ⊥) :
    (R ⊓ P).relIndex R ∣ Nat.card (Outer ↥P) := by
  classical
  let φ : R →* Outer ↥P := toOuter P R
  have hker : φ.ker = (R ⊓ P).subgroupOf R := by
    ext x
    constructor
    · intro hx
      have hx1 : (QuotientGroup.mk' (inner ↥P)) (MulAut.conjNormal (H := P) (x : Y)) = 1 := hx
      have hxin : MulAut.conjNormal (H := P) (x : Y) ∈ inner ↥P :=
        (QuotientGroup.eq_one_iff _).mp hx1
      have hxP : (x : Y) ∈ P := by
        have := mem_sup_centralizer_of_conjNormal_inner (L := P) hxin
        simpa [hC] using this
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxP⟩
    · intro hx
      have hxP : (x : Y) ∈ P := (Subgroup.mem_subgroupOf.mp hx).2
      show φ x = 1
      dsimp [φ, toOuter]
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨⟨(x : Y), hxP⟩, ?_⟩
      exact (MulAut.conjNormal_val (H := P) (h := ⟨(x : Y), hxP⟩)).symm
  have hdvd := Subgroup.card_dvd_of_injective (QuotientGroup.kerLift φ)
    (QuotientGroup.kerLift_injective φ)
  rw [hker] at hdvd
  simpa [Subgroup.relIndex, Subgroup.index_eq_card] using hdvd

private theorem card_outer_of_bender_unitary {P : Type*} [Group P] [Finite P] {k e : ℕ}
    (hB : BenderType P k 3 e) :
    Nat.card (Outer P) = 2 * k * Nat.gcd 3 (2 ^ k + 1) := by
  obtain ⟨Dd, hDd, -, hDdcard, -, hquotcard⟩ := hB.outer_unitary
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  rw [hquotcard, hDdcard] at h
  rw [h]

private theorem sylow_center_le_inf {P : Type} [Group P] [Finite P]
    (A' U : Subgroup P) (Q : Sylow 2 P)
    (hA'ab : IsMulCommutative A') (hA'2 : IsPGroup 2 A')
    (hA'card : Nat.card A' = 16) (hA'Q : A' ≤ (Q : Subgroup P))
    (hUcenter : ∀ x, x ∈ U ↔ x ∈ (Q : Subgroup P) ∧
      ∀ y ∈ (Q : Subgroup P), x * y = y * x)
    {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = (2 ^ 2) ^ 2)
    (eP : P ≃* StatedProj (StatedSU 3 (2 ^ 2) F)) : U ≤ A' := by
  have hUab : IsMulCommutative U := by
    refine ⟨⟨fun u v => ?_⟩⟩
    apply Subtype.ext
    have hvQ : (v : P) ∈ (Q : Subgroup P) := ((hUcenter (v : P)).mp v.2).1
    exact ((hUcenter (u : P)).mp u.2).2 (v : P) hvQ
  have hUleQ : U ≤ (Q : Subgroup P) := fun u hu => ((hUcenter (u : P)).mp hu).1
  have hU2 : IsPGroup 2 U :=
    Q.isPGroup'.of_injective (Subgroup.inclusion hUleQ) (Subgroup.inclusion_injective _)
  have hcommAU : ∀ a ∈ A', ∀ u ∈ U, a * u = u * a := by
    intro a ha u hu
    have haQ : a ∈ (Q : Subgroup P) := hA'Q ha
    exact (((hUcenter (u : P)).mp hu).2 a haQ).symm
  have hSUab : IsMulCommutative (A' ⊔ U : Subgroup P) := by
    have hAA : A' ≤ Subgroup.centralizer (A' : Set P) := Subgroup.le_centralizer (H := A')
    have hUU : U ≤ Subgroup.centralizer (U : Set P) := Subgroup.le_centralizer (H := U)
    have hAU : A' ≤ Subgroup.centralizer (U : Set P) := by
      rw [Subgroup.le_centralizer_iff]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcommAU a ha u hu
    have hUA : U ≤ Subgroup.centralizer (A' : Set P) := by
      rw [Subgroup.le_centralizer_iff]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hcommAU a ha u hu).symm
    have hAle : A' ≤ Subgroup.centralizer ((A' ⊔ U : Subgroup P) : Set P) := by
      rw [Subgroup.le_centralizer_iff]
      exact sup_le hAA hUA
    have hUle : U ≤ Subgroup.centralizer ((A' ⊔ U : Subgroup P) : Set P) := by
      rw [Subgroup.le_centralizer_iff]
      exact sup_le hAU hUU
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le hAle hUle)
  have hcommUA : U ≤ Subgroup.centralizer (A' : Set P) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommAU a ha u hu
  have hnormUA : U ≤ Subgroup.normalizer (A' : Set P) :=
    hcommUA.trans (Subgroup.centralizer_le_normalizer _)
  have hSU2 : IsPGroup 2 (A' ⊔ U : Subgroup P) :=
    hA'2.to_sup_of_normal_left' hU2 hnormUA
  have hSUcard : Nat.card (A' ⊔ U : Subgroup P) ≤ 16 := by
    simpa using card_abelian_two_le_psu3 (k := 2) (by norm_num) hF4
      (P := P) eP hSUab hSU2
  have hge : 16 ≤ Nat.card (A' ⊔ U : Subgroup P) := by
    have hle : Nat.card A' ≤ Nat.card (A' ⊔ U : Subgroup P) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion le_sup_left)
        (Subgroup.inclusion_injective _)
    rw [hA'card] at hle
    exact hle
  have hsup_eq : A' = A' ⊔ U :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  rw [hsup_eq]
  exact le_sup_right

private theorem two_pow_gt_two_mul {k : ℕ} (hk : 3 ≤ k) : 2 * k < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      nlinarith

private theorem card_degree_and_card_regular {Y Ω F : Type} [Group Y] [Finite Y] [Fintype Ω]
    [MulAction Y Ω] [FaithfulSMul Y Ω] [Field F] [Finite F]
    (hF16 : Nat.card F = 16) (h2 : MulAction.IsMultiplyPretransitive Y Ω 2)
    (hdeg : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e)
    (hcopy : HasNormalCopy Y (StatedProj (StatedSU 3 4 F)))
    (ω : Ω) (R : Subgroup Y) (hRle : R ≤ MulAction.stabilizer Y ω)
    (hreg : ∀ a b : Ω, a ≠ ω → b ≠ ω → ∃! r : ↥R, (r : Y) • a = b) :
    Fintype.card Ω = 65 ∧ Nat.card R = 64 := by
  have hS : SubconstNatural := subconstNatural
  have hΩ65 : Fintype.card Ω = 65 := by
    have h := hS.2.2 Y Ω 2 F (by norm_num) hF16 h2 hdeg hcopy
    norm_num at h
    exact h
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁ : Ω, ω₁ ≠ ω := by
    by_contra h
    have hall : ∀ x : Ω, x = ω := fun x => by
      simpa using (not_exists.mp h x)
    have hsub : (Finset.univ : Finset Ω) ⊆ {ω} := by
      intro x _
      simp [hall x]
    have h1 := Finset.card_le_card hsub
    simp at h1
    omega
  exact ⟨hΩ65, by rw [card_of_regular_on_compl R ω hRle hreg ω₁ hω₁, hΩ65]⟩

private theorem card_inf_eq_sixteen {Y Ω F : Type} [Group Y] [Finite Y] [Fintype Ω]
    [MulAction Y Ω] [FaithfulSMul Y Ω] [Field F] [Finite F]
    (hF4 : Nat.card F = (2 ^ 2) ^ 2) (h2 : MulAction.IsMultiplyPretransitive Y Ω 2)
    (P : Subgroup Y) [P.Normal] (eP4 : P ≃* StatedProj (StatedSU 3 (2 ^ 2) F))
    (hPcard : Fintype.card Ω < Nat.card P) (ω : Ω) (R : Subgroup Y)
    (hRcomm : IsMulCommutative R) (hcardR : Nat.card R = 64) :
    Nat.card (R ⊓ P : Subgroup Y) = 16 ∧ (R ⊓ P : Subgroup Y).relIndex R = 4 := by
  let A : Subgroup Y := R ⊓ P
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 6) (by norm_num [hcardR])
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    show (x : Y) * (y : Y) = (y : Y) * (x : Y)
    have h := hRcomm.is_comm.comm (⟨x.1, x.2.1⟩ : R) (⟨y.1, y.2.1⟩ : R)
    exact congrArg Subtype.val h
  have hA2 : IsPGroup 2 A :=
    hR2.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hAleP : A ≤ P := inf_le_right
  let A' : Subgroup P := A.subgroupOf P
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleP).toEquiv
  have hA'ab : IsMulCommutative A' :=
    CFSG.Goldschmidt.isMulCommutative_subgroupOf hAab P
  have hA'2 : IsPGroup 2 A' :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAleP).symm
  have hAle : Nat.card A ≤ 16 := by
    have h := card_abelian_two_le_psu3 (k := 2) (by norm_num) (F := F) hF4
      (P := P) eP4 hA'ab hA'2
    simpa [hA'card] using h
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨ω⟩
    omega
  have hC : Subgroup.centralizer (P : Set Y) = ⊥ :=
    centralizer_eq_bot_of_two_transitive hPne h2 hPcard ω
  have hOutdvd : A.relIndex R ∣ Nat.card (Outer ↥P) := by
    change (R ⊓ P).relIndex R ∣ Nat.card (Outer ↥P)
    exact relIndex_inf_dvd_card_outer hC
  have hOutcard : Nat.card (Outer ↥P) = 4 := by
    obtain ⟨e, hB⟩ := benderType_statedProj (F := F) (n := 2) (by norm_num) hF4
    have h := card_outer_of_bender_unitary (hB.of_mulEquiv eP4.symm)
    norm_num [Nat.gcd_eq_right] at h
    exact h
  have hcardmul : Nat.card A * A.relIndex R = Nat.card R := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := R)
    rw [show A ⊓ R = A from inf_eq_left.mpr inf_le_left, hcardR] at h
    rw [hcardR]
    rwa [mul_comm] at h
  have hA16 : Nat.card A = 16 := by
    have hrel_le : A.relIndex R ≤ 4 := by
      rw [← hOutcard]
      exact Nat.le_of_dvd (by positivity) hOutdvd
    have hrel_dvd : A.relIndex R ∣ 64 := by
      refine ⟨Nat.card A, ?_⟩
      rw [mul_comm, hcardmul, hcardR]
    have hrel_pos : 0 < A.relIndex R := Nat.pos_of_dvd_of_pos hrel_dvd (by norm_num)
    have hrel_cases : A.relIndex R = 1 ∨ A.relIndex R = 2 ∨ A.relIndex R = 4 := by
      interval_cases A.relIndex R <;> simp_all
    rcases hrel_cases with h1 | h2 | h4
    · rw [h1, mul_one, hcardR] at hcardmul
      omega
    · rw [h2, mul_comm, hcardR] at hcardmul
      omega
    · rw [h4, mul_comm, hcardR] at hcardmul
      omega
  have hArel : A.relIndex R = 4 := by
    have h := hcardmul
    rw [hA16, hcardR] at h
    omega
  exact ⟨hA16, hArel⟩

private theorem rootCenterAut_index_contradiction {G : Type} [Group G] [Finite G]
    (Q : Sylow 2 G) (U : Subgroup G) (C D M Aauto : Subgroup (MulAut G))
    (hDinf : C ⊓ D = ⊥) (hDsup : C ⊔ D = rootCenterAut (Q : Subgroup G) U)
    (hDnormal : (C.subgroupOf (rootCenterAut (Q : Subgroup G) U)).Normal)
    (hDcard : Nat.card D = 10)
    (hMle : M ≤ rootCenterAut (Q : Subgroup G) U) (hMcard : Nat.card M = 64)
    (hCM : C ⊓ M = Aauto) (hAauto_card : Nat.card Aauto = 16) : False := by
  have hCroot : C ≤ rootCenterAut (Q : Subgroup G) U := by
    rw [← hDsup]
    exact le_sup_left
  let Croot : Subgroup (rootCenterAut (Q : Subgroup G) U) :=
    C.subgroupOf (rootCenterAut (Q : Subgroup G) U)
  let Mroot : Subgroup (rootCenterAut (Q : Subgroup G) U) :=
    M.subgroupOf (rootCenterAut (Q : Subgroup G) U)
  let Droot : Subgroup (rootCenterAut (Q : Subgroup G) U) :=
    D.subgroupOf (rootCenterAut (Q : Subgroup G) U)
  have hDroot_le : D ≤ rootCenterAut (Q : Subgroup G) U := by
    rw [← hDsup]
    exact le_sup_right
  have hCroot_normal : Croot.Normal := hDnormal
  haveI : Croot.Normal := hCroot_normal
  have htop : Croot ⊔ Droot = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := C) (A' := D)
      (B := rootCenterAut (Q : Subgroup G) U) hCroot hDroot_le
    rw [hDsup] at h
    simpa [Croot, Droot] using h.symm
  have hbot : Croot ⊓ Droot = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      have hx' := Subgroup.mem_inf.mp hx
      have hx1 : (x : MulAut G) ∈ C ⊓ D := Subgroup.mem_inf.mpr ⟨hx'.1, hx'.2⟩
      rw [hDinf] at hx1
      exact Subgroup.mem_bot.mp hx1
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact Subgroup.mem_inf.mpr ⟨Croot.one_mem, Droot.one_mem⟩
  have hDroot_card : Nat.card Droot = 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDroot_le).toEquiv, hDcard]
  have hCrelD : Croot.relIndex Droot = 10 := by
    have h := Subgroup.relIndex_mul_card Croot Droot
    rw [hbot, Subgroup.card_bot, mul_one, hDroot_card] at h
    exact h
  have hCindex : Croot.index = 10 := by
    have htower := Subgroup.relIndex_mul_relIndex (H := Croot) (K := Droot ⊔ Croot)
      (L := ⊤) le_sup_right le_top
    rw [Subgroup.relIndex_sup_right Droot Croot, hCrelD] at htower
    have htop' : Droot ⊔ Croot = ⊤ := by rw [sup_comm, htop]
    rw [htop', Subgroup.relIndex_self, Subgroup.relIndex_top_right] at htower
    simpa using htower.symm
  have hCrelMroot : Croot.relIndex Mroot = 4 := by
    have h := Subgroup.relIndex_subgroupOf (H := C) (K := M)
      (L := rootCenterAut (Q : Subgroup G) U) hMle
    rw [h]
    have hCMrel := Subgroup.relIndex_mul_card C M
    rw [hCM, hAauto_card, hMcard] at hCMrel
    omega
  have hCrelMsup : Croot.relIndex (Mroot ⊔ Croot) = 4 := by
    rw [Subgroup.relIndex_sup_right Mroot Croot, hCrelMroot]
  have htower2 := Subgroup.relIndex_mul_relIndex (H := Croot) (K := Mroot ⊔ Croot)
    (L := ⊤) le_sup_right le_top
  rw [hCrelMsup] at htower2
  simp only [Subgroup.relIndex_top_right, hCindex] at htower2
  omega

private theorem conjNormal_image_le_rootCenterAut {Y : Type} [Group Y] [Finite Y]
    (P : Subgroup Y) [P.Normal] {R A : Subgroup Y} (hAdef : A = R ⊓ P)
    (hRcomm : IsMulCommutative R) (Q : Sylow 2 ↥P) (U : Subgroup ↥P)
    {t : ↥P} (hcQ : BenderCore (2 ^ 2) 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1))
      (Q : Subgroup ↥P) t)
    (hUcenter : ∀ x, x ∈ U ↔ x ∈ (Q : Subgroup ↥P) ∧
      ∀ y ∈ (Q : Subgroup ↥P), x * y = y * x)
    (hUleA' : U ≤ A.subgroupOf P) (hA'Q : A.subgroupOf P ≤ (Q : Subgroup ↥P))
    (hC : Subgroup.centralizer (P : Set Y) = ⊥) (hcardR : Nat.card R = 64)
    (hA16 : Nat.card A = 16) :
    ∃ M Aauto : Subgroup (MulAut ↥P),
      M ≤ rootCenterAut (Q : Subgroup ↥P) U ∧ Nat.card M = 64 ∧
        Nat.card Aauto = 16 ∧ ((Q : Subgroup ↥P).map MulAut.conj) ⊓ M = Aauto := by
  have hAleR : A ≤ R := by rw [hAdef]; exact inf_le_left
  have hAleP : A ≤ P := by rw [hAdef]; exact inf_le_right
  let φ : Y →* MulAut ↥P := MulAut.conjNormal
  let M : Subgroup (MulAut ↥P) := R.map φ
  have hMle : M ≤ rootCenterAut (Q : Subgroup ↥P) U := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hm
    rw [mem_rootCenterAut]
    constructor
    · have hnorm : ∀ s ∈ (Q : Subgroup ↥P),
          (MulAut.conjNormal r) s ∈ (Q : Subgroup ↥P) := by
        apply hcQ.mem_of_centralizes_rootCenter (MulAut.conjNormal r)
        intro z hz
        have hz' := Subgroup.mem_inf.mp hz
        have hzU : z ∈ U := (hUcenter z).mpr ⟨hz'.1, fun y hy =>
          (Subgroup.mem_centralizer_iff.mp hz'.2 y hy).symm⟩
        have hzA' : z ∈ A.subgroupOf P := hUleA' hzU
        have hzA : (z : Y) ∈ A := (Subgroup.mem_subgroupOf.mp hzA')
        have hcomm : (r : Y) * (z : Y) = (z : Y) * (r : Y) :=
          congrArg Subtype.val
            (hRcomm.is_comm.comm (⟨r, hr⟩ : R)
              (⟨(z : Y), hAleR hzA⟩ : R))
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        simp [hcomm]
      have hmap_le : (Q : Subgroup ↥P).map (MulAut.conjNormal r).toMonoidHom ≤ Q := by
        intro s hs
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hs
        exact hnorm q hq
      have hcard : Nat.card ((Q : Subgroup ↥P).map
          (MulAut.conjNormal r).toMonoidHom) = Nat.card (Q : Subgroup ↥P) :=
        Subgroup.card_map_of_injective (MulAut.conjNormal r).injective
      exact Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
    · intro u hu
      have huA' : u ∈ A.subgroupOf P := hUleA' hu
      have huA : (u : Y) ∈ A := (Subgroup.mem_subgroupOf.mp huA')
      have hcomm : (r : Y) * (u : Y) = (u : Y) * (r : Y) :=
        congrArg Subtype.val
          (hRcomm.is_comm.comm (⟨r, hr⟩ : R)
            (⟨(u : Y), hAleR huA⟩ : R))
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      simp [hcomm]
  have hφinjY : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hcen : a * b⁻¹ ∈ Subgroup.centralizer (P : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h2 := congrArg (fun f : MulAut ↥P => f ⟨p, hp⟩) h1
      simp only [OneMemClass.coe_one, MulAut.one_apply, MulAut.conjNormal_apply] at h2
      have h3 : (a * b⁻¹ : Y) * p * (a * b⁻¹ : Y)⁻¹ = p := congrArg Subtype.val h2
      calc p * (a * b⁻¹) = ((a * b⁻¹) * p * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by rw [h3]
        _ = (a * b⁻¹) * p := by group
    rw [hC, Subgroup.mem_bot] at hcen
    calc a = (a * b⁻¹) * b := by group
      _ = b := by rw [hcen, one_mul]
  have hMcard : Nat.card M = 64 := by
    rw [Subgroup.card_map_of_injective hφinjY, hcardR]
  let Aauto : Subgroup (MulAut ↥P) := A.map φ
  have hAauto_card : Nat.card Aauto = 16 := by
    rw [Subgroup.card_map_of_injective hφinjY, hA16]
  have hCM : ((Q : Subgroup ↥P).map MulAut.conj) ⊓ M = Aauto := by
    apply le_antisymm
    · intro γ hγ
      obtain ⟨hγC, hγM⟩ := Subgroup.mem_inf.mp hγ
      obtain ⟨q, hq, hγq⟩ := Subgroup.mem_map.mp hγC
      obtain ⟨r, hr, hγr⟩ := Subgroup.mem_map.mp hγM
      have hφq : φ (q : ↥P) = MulAut.conj (q : ↥P) := by
        simp [φ, MulAut.conjNormal_val]
      have hrq : (r : Y) = (q : Y) := by
        apply hφinjY
        calc φ r = γ := hγr
          _ = MulAut.conj q := hγq.symm
          _ = φ (q : ↥P) := hφq.symm
      have hrA : (r : Y) ∈ A := by
        rw [hAdef]
        refine ⟨hr, ?_⟩
        rw [hrq]
        exact (q : ↥P).2
      exact ⟨r, hrA, hγr⟩
    · intro γ hγ
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hγ
      constructor
      · have haP : (a : Y) ∈ P := hAleP ha
        have hφa : φ (a : Y) = MulAut.conj ⟨(a : Y), haP⟩ := by
          change MulAut.conjNormal (H := P) (a : Y) = MulAut.conj ⟨(a : Y), haP⟩
          rw [← MulAut.conjNormal_val (H := P) (h := ⟨(a : Y), haP⟩)]
        refine ⟨⟨(a : Y), haP⟩, hA'Q ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr ha
        · exact hφa.symm
      · exact ⟨a, hAleR ha, rfl⟩
  exact ⟨M, Aauto, hMle, hMcard, hAauto_card, hCM⟩

theorem subconstUnitaryFourBound :
    ∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (F : Type) [Field F] [Finite F], Nat.card F = 16 →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y (StatedProj (StatedSU 3 4 F)) →
      ∀ (ω : Ω) (R : Subgroup Y), R ≤ MulAction.stabilizer Y ω →
        (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω → ω₂ ≠ ω → ∃! r : ↥R, (r : Y) • ω₁ = ω₂) →
        IsMulCommutative R → False := by
  intro Y _ _ Ω _ _ _ F _ _ hF16 h2 hdeg hcopy ω R hRle hreg hRcomm
  obtain ⟨hΩ65, hcardR⟩ := card_degree_and_card_regular hF16 h2 hdeg hcopy ω R hRle hreg
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 6) (by norm_num [hcardR])
  obtain ⟨P, hPnormal, ⟨eP⟩⟩ := hcopy
  haveI : P.Normal := hPnormal
  have hF4 : Nat.card F = (2 ^ 2) ^ 2 := by rw [hF16]; norm_num
  let eP4 : P ≃* StatedProj (StatedSU 3 (2 ^ 2) F) := by simpa using eP
  have hPcard : Fintype.card Ω < Nat.card P := by
    rw [hΩ65, Nat.card_congr eP4.toEquiv]
    exact card_psu3_gt_degree (k := 2) (by norm_num) hF4
  let A : Subgroup Y := R ⊓ P
  obtain ⟨hA16, hArel⟩ := card_inf_eq_sixteen hF4 h2 P eP4 hPcard ω R hRcomm hcardR
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨ω⟩
    omega
  have hC : Subgroup.centralizer (P : Set Y) = ⊥ :=
    centralizer_eq_bot_of_two_transitive hPne h2 hPcard ω
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    show (x : Y) * (y : Y) = (y : Y) * (x : Y)
    have h := hRcomm.is_comm.comm (⟨x.1, x.2.1⟩ : R) (⟨y.1, y.2.1⟩ : R)
    exact congrArg Subtype.val h
  have hA2 : IsPGroup 2 A :=
    hR2.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hAleP : A ≤ P := inf_le_right
  let A' : Subgroup P := A.subgroupOf P
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleP).toEquiv
  have hA'ab : IsMulCommutative A' :=
    CFSG.Goldschmidt.isMulCommutative_subgroupOf hAab P
  have hA'2 : IsPGroup 2 A' :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAleP).symm
  obtain ⟨Q, hA'Q⟩ := hA'2.exists_le_sylow
  obtain ⟨J, hJ, -, hfixed⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := F) 2 2 hF4
  obtain ⟨ePsu⟩ := CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J 4
    (by rw [hF16]; norm_num) hfixed
  let e : ↥P ≃* ProjectiveSpecialUnitaryMatrixGroup J := eP.trans ePsu.symm
  let U : Subgroup P :=
    (CFSG.omega₁ (G := (Q : Subgroup P)) (p := 2)).map (Q : Subgroup P).subtype
  obtain ⟨-, hUcenter, -, ⟨D, hDinf, hDsup, hDnormal, hDcard, hDdihedral⟩, -, -, -, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J 2 (by norm_num) hF4 hfixed hJ e Q U rfl
  have hUleA' : U ≤ A' :=
    sylow_center_le_inf A' U Q hA'ab hA'2 (by rw [hA'card, hA16]) hA'Q hUcenter hF4 eP4
  obtain ⟨S, w, hcS⟩ :=
    exists_benderCore_psu3_concrete J 2 (by norm_num) hF4 hfixed hJ
  let eQ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have heQ : (eQ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (Q : Subgroup ↥P).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective Q
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S eQ
  have hSmap : (eQ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    apply Subgroup.ext
    intro x
    change x ∈ ((g • S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        (MulAut.conj g).toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    rw [Sylow.coe_smul]
    simp [Set.mem_smul_set, Subgroup.mem_map, MulAut.conj_apply]
  have hcQm : BenderCore (2 ^ 2) 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1))
      (eQ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (MulAut.conj g w) := by
    rw [hSmap]
    exact hcS.map (MulAut.conj g)
  have hcQ : BenderCore (2 ^ 2) 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1))
      (Q : Subgroup ↥P) (e.symm (MulAut.conj g w)) := by
    have hmap := hcQm.map e.symm
    have heQmap : (eQ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        e.symm.toMonoidHom = (Q : Subgroup ↥P) := by
      rw [heQ]
      simp [Subgroup.map_map]
    rwa [heQmap] at hmap
  let C : Subgroup (MulAut ↥P) := (Q : Subgroup ↥P).map MulAut.conj
  obtain ⟨M, Aauto, hMle, hMcard, hAauto_card, hCM⟩ :=
    conjNormal_image_le_rootCenterAut P (rfl : A = R ⊓ P) hRcomm Q U hcQ hUcenter hUleA' hA'Q hC
      hcardR hA16
  exact rootCenterAut_index_contradiction Q U C D M Aauto hDinf hDsup hDnormal
    (by norm_num [hDcard]) hMle hMcard hCM hAauto_card

theorem subconstUnitaryNonabelian_of_subconstNatural (hS : SubconstNatural)
    : SubconstUnitaryNonabelian := by
  have h4 := subconstUnitaryFourBound
  intro Y _ _ Ω _ _ _ k F _ _ hk hF h2 hdeg hcopy ω R hRle hreg
  by_contra hnoncomm
  have hRcomm : IsMulCommutative R := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    by_contra h
    exact hnoncomm ⟨a, a.2, b, b.2, h⟩
  have hcopy0 := hcopy
  obtain ⟨P, hPnormal, ⟨eP⟩⟩ := hcopy
  haveI : P.Normal := hPnormal
  have hΩcard : Fintype.card Ω = 2 ^ (3 * k) + 1 :=
    hS.2.2 Y Ω k F hk hF h2 hdeg ⟨P, hPnormal, ⟨eP⟩⟩
  have hq : (2 ^ k) ^ 3 = 2 ^ (3 * k) := by rw [← pow_mul, mul_comm]
  have hΩpos : 0 < Fintype.card Ω := by rw [hΩcard]; positivity
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁ : Ω, ω₁ ≠ ω := by
    by_contra h
    have hall : ∀ x : Ω, x = ω := fun x => by
      simpa using (not_exists.mp h x)
    have hsub : (Finset.univ : Finset Ω) ⊆ {ω} := by
      intro x _
      simp [hall x]
    have h1 := Finset.card_le_card hsub
    simp at h1
    rw [hΩcard] at h1
    have : 8 ≤ 2 ^ (3 * k) := by
      have : 1 ≤ 3 * k := by omega
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 3 * k)
    omega
  have hcardR : Nat.card R = (2 ^ k) ^ 3 := by
    rw [card_of_regular_on_compl R ω hRle hreg ω₁ hω₁, hΩcard]
    rw [← hq]
    have : 1 ≤ (2 ^ k) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 3 * k) (by rw [hcardR, hq])
  have hPcard : Fintype.card Ω < Nat.card P := by
    rw [hΩcard, ← hq]
    simpa only [Nat.card_congr eP.toEquiv] using card_psu3_gt_degree hk hF
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨ω⟩
    omega
  have hC : Subgroup.centralizer (P : Set Y) = ⊥ :=
    centralizer_eq_bot_of_two_transitive hPne h2 hPcard ω
  let A : Subgroup Y := R ⊓ P
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    show (x : Y) * (y : Y) = (y : Y) * (x : Y)
    have h := hRcomm.is_comm.comm (⟨x.1, x.2.1⟩ : R) (⟨y.1, y.2.1⟩ : R)
    exact congrArg Subtype.val h
  have hA2 : IsPGroup 2 A :=
    hR2.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hAle : Nat.card A ≤ (2 ^ k) ^ 2 := by
    have hAleP : A ≤ P := inf_le_right
    have hA'card : Nat.card (A.subgroupOf P) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleP).toEquiv
    have hA'ab : IsMulCommutative (A.subgroupOf P) :=
      CFSG.Goldschmidt.isMulCommutative_subgroupOf hAab P
    have hA'2 : IsPGroup 2 (A.subgroupOf P) :=
      hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAleP).symm
    have := card_abelian_two_le_psu3 hk hF eP hA'ab hA'2
    rwa [hA'card] at this
  have hOutdvd : A.relIndex R ∣ Nat.card (Outer ↥P) := by
    change (R ⊓ P).relIndex R ∣ Nat.card (Outer ↥P)
    exact relIndex_inf_dvd_card_outer hC
  have hOutcard : Nat.card (Outer ↥P) = 2 * k * Nat.gcd 3 (2 ^ k + 1) := by
    obtain ⟨e, hB⟩ := benderType_statedProj (F := F) hk hF
    exact card_outer_of_bender_unitary (hB.of_mulEquiv eP.symm)
  have hrel_dvd : A.relIndex R ∣ Nat.card R := Subgroup.relIndex_dvd_card A R
  have hrel_pow : ∃ a, A.relIndex R = 2 ^ a := by
    have hdvd' : A.relIndex R ∣ 2 ^ (3 * k) := by
      rwa [hcardR, hq] at hrel_dvd
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (p := 2) (m := 3 * k)
      (i := A.relIndex R) Nat.prime_two).mp hdvd'
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hrel_pow
  have hdvdOut : 2 ^ a ∣ 2 * k * Nat.gcd 3 (2 ^ k + 1) := by
    rw [← hOutcard, ← ha]
    exact hOutdvd
  have hdodd : Odd (Nat.gcd 3 (2 ^ k + 1)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  have hcop : Nat.Coprime (2 ^ a) (Nat.gcd 3 (2 ^ k + 1)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hdodd)
  have hdvd2k : 2 ^ a ∣ 2 * k := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvdOut
  have hrel_le : A.relIndex R ≤ 2 * k := by
    rw [ha]
    exact Nat.le_of_dvd (by positivity) hdvd2k
  have hcard_mul : A.relIndex R * Nat.card A = Nat.card R := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := R)
    rwa [inf_eq_left.mpr inf_le_left] at h
  have hq_le_rel : 2 ^ k ≤ A.relIndex R := by
    have hq3 : (2 ^ k) ^ 3 = Nat.card R := hcardR.symm
    have hprod : (2 ^ k) ^ 2 * (2 ^ k) ≤ (2 ^ k) ^ 2 * A.relIndex R := by
      calc (2 ^ k) ^ 2 * (2 ^ k) = (2 ^ k) ^ 3 := by ring
        _ = Nat.card R := hq3
        _ = A.relIndex R * Nat.card A := hcard_mul.symm
        _ ≤ A.relIndex R * (2 ^ k) ^ 2 := Nat.mul_le_mul_left _ hAle
        _ = (2 ^ k) ^ 2 * A.relIndex R := by ring
    exact Nat.le_of_mul_le_mul_left hprod (by positivity)
  have hq_le_2k : 2 ^ k ≤ 2 * k := le_trans hq_le_rel hrel_le
  by_cases hk2 : k = 2
  · have hF16 : Nat.card F = 16 := by
      rw [hk2] at hF
      norm_num at hF
      exact hF
    have hcopy4 : HasNormalCopy Y (StatedProj (StatedSU 3 4 F)) := by
      rw [hk2] at hcopy0
      norm_num at hcopy0
      exact hcopy0
    exact h4 Y Ω F hF16 h2 hdeg hcopy4 ω R hRle hreg hRcomm
  · have hk3 : 3 ≤ k := by omega
    have hgt := two_pow_gt_two_mul hk3
    omega

theorem subconstUnitaryNonabelian : SubconstUnitaryNonabelian :=
  subconstUnitaryNonabelian_of_subconstNatural subconstNatural

end CFSG.Quasithin.Stroth
