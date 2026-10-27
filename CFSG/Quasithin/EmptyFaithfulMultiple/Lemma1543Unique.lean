module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543Closed
public import CFSG.Quasithin.Background.A4Local
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543Linear
import CFSG.Quasithin.Background.A4Reduced
import CFSG.Quasithin.Background.A1a
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.Quasithin.EmptyFaithful.QTKELocal
import CFSG.Quasithin.Background.OrderingMax
import CFSG.GroupTheory.ThompsonAxB
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Foundations
public import CFSG.Quasithin.Background.D1Statement
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

section General

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_fitting_of_pow {Q : Type*} [Group Q] [Finite Q]
    (hO2 : CFSG.Open.pCore 2 Q = ⊥) {z : Q} (hz : z ∈ CFSG.fittingSubgroup Q) {m : ℕ}
    (hm : z ^ 2 ^ m = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.fittingSubgroup Q
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨z, hz⟩ : F)) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_zpow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have h1 := Sylow.map_le_pCore (inferInstance : F.Normal) CFSG.fittingSubgroup_nilpotent 2 S
  rw [hO2] at h1
  exact Subgroup.mem_bot.mp (h1 ⟨⟨z, hz⟩, hS (Subgroup.mem_zpowers _), rfl⟩)

theorem mem_pCoreOf_of_mem_O2FOf {M : Subgroup G} {g : G} (hg : g ∈ O2FOf M) {m : ℕ}
    (hm : g ^ 2 ^ m = 1) : g ∈ pCoreOf 2 M := by
  obtain ⟨g', hg', rfl⟩ := hg
  have hm' : g' ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
  have h := eq_one_of_mem_fitting_of_pow B6.pCore_quotient_pCore (Subgroup.mem_comap.mp hg')
    (m := m) (by rw [← map_pow, hm', map_one])
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact ⟨g', h, rfl⟩

omit [Finite G] in
theorem pCoreOf_le_O2FOf (M : Subgroup G) : pCoreOf 2 M ≤ O2FOf M := by
  refine Subgroup.map_mono fun g hg => ?_
  show QuotientGroup.mk' (CFSG.Open.pCore 2 M) g ∈ CFSG.fittingSubgroup _
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).mpr hg]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem O2FOf_le (M : Subgroup G) : O2FOf M ≤ M := Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_O2FOf (M : Subgroup G) :
    M ≤ Subgroup.normalizer (O2FOf M : Set G) := by
  have hN : (O2F M).Normal := by
    unfold O2F
    infer_instance
  have h1 := Subgroup.le_normalizer_map (H := O2F M) M.subtype
  rwa [Subgroup.normalizer_eq_top_iff.mpr hN, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1

omit [Finite G] in
theorem oTwoUpper_sup_eq_of_le_normalizer {X R : Subgroup G} (hX : X = oTwoUpper X)
    (hR : IsPGroup 2 R) (hRX : R ≤ Subgroup.normalizer (X : Set G)) : oTwoUpper (X ⊔ R) = X := by
  refine le_antisymm (oTwoUpper_le_of_pow_mem fun g hg => ?_)
    (hX.le.trans (oTwoUpper_mono le_sup_left))
  have hg' : g ∈ (↑(X ⊔ R) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X R hRX] at hg'
  obtain ⟨x, hx, r, hr, rfl⟩ := hg'
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', he⟩ := A4.exists_pow_mul_eq hx (hRX hr) (2 ^ k)
  exact ⟨k, by rw [he, hk', mul_one]; exact hx'⟩

theorem mem_normalizer_of_conj_mem_sup {X R : Subgroup G} (hX : X = oTwoUpper X)
    (hR : IsPGroup 2 R) (hRX : R ≤ Subgroup.normalizer (X : Set G)) {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X ⊔ R) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  have hgXR : g ∈ Subgroup.normalizer ((X ⊔ R : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ X ⊔ R := hn
    have key : X ⊔ R ≤ (X ⊔ R).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => hg x hx) fun r hr => ?_
      exact le_sup_right (a := X) ((Subgroup.mem_normalizer_iff.mp hgR r).mp hr)
    exact key hn'
  have h := normalizer_le_normalizer_oTwoUpper (X ⊔ R) hgXR
  rwa [oTwoUpper_sup_eq_of_le_normalizer hX hR hRX] at h

theorem isSubnormal_of_le_O2FOf {M H : Subgroup G} (hRH : pCoreOf 2 M ≤ H)
    (hHK : H ≤ O2FOf M) : IsSubnormal H M := by
  have hHM : H ≤ M := hHK.trans (O2FOf_le M)
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 M)
  set F := CFSG.fittingSubgroup (M ⧸ CFSG.Open.pCore 2 M)
  set Y := (H.subgroupOf M).map π
  have hYF : Y ≤ F := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', he⟩ := hHK (Subgroup.mem_subgroupOf.mp hg)
    obtain rfl : g' = g := Subtype.ext he
    exact hg'
  have h1 : IsSubnormal Y F :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hYF).mp
      ((CFSG.Adapters.isSubnormal_top_iff _).mpr
        (CFSG.GorensteinWalter.isSubnormal_of_nilpotent CFSG.fittingSubgroup_nilpotent Y hYF))
  have h2 : IsSubnormal F ⊤ :=
    A4.subnormal_of_normal le_top (Subgroup.Normal.subgroupOf inferInstance ⊤)
  have h3 := A4.subnormal_comap π (A4.subnormal_trans h1 h2)
  have hker : π.ker ≤ H.subgroupOf M := by
    intro g hg
    rw [QuotientGroup.ker_mk'] at hg
    exact Subgroup.mem_subgroupOf.mpr (hRH ⟨g, hg, rfl⟩)
  rw [Subgroup.comap_top, Subgroup.comap_map_eq, sup_eq_left.mpr hker] at h3
  exact (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hHM).mp h3

theorem eq_one_of_centralizes {Q : Type*} [Group Q] [Finite Q] (hsolv : Group.IsSolvable Q)
    (hO2 : CFSG.Open.pCore 2 Q = ⊥) {Y : Subgroup Q}
    (hY : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ y ∈ CFSG.Open.pCore r Q,
      (∀ b ∈ CFSG.Open.pCore r Q ⊓ Y, b * y = y * b) → y ∈ Y)
    {s : Q} {m : ℕ} (hs : s ^ 2 ^ m = 1) (hsY : ∀ y ∈ Y, y * s = s * y) : s = 1 := by
  classical
  have hzY : ∀ a ∈ Subgroup.zpowers s, ∀ b ∈ Y, a * b = b * a := by
    rintro _ ⟨n, rfl⟩ b hb
    exact (Commute.zpow_left (hsY b hb).symm n).eq
  have hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      s ∈ Subgroup.centralizer (CFSG.Open.pCore r Q : Set Q) := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    set P := CFSG.Open.pCore r Q with hP
    have : P.Normal := CFSG.LieType.BorelTits.pCore_normal r
    set A := Subgroup.zpowers s
    set B := P ⊓ Y
    let α : A →* MulAut P := (MulAut.conjNormal (H := P)).comp A.subtype
    let β : B →* MulAut P := (MulAut.conjNormal (H := P)).comp B.subtype
    have hA : ¬ r ∣ Nat.card A := by
      intro h
      rw [Nat.card_zpowers] at h
      have h2 : r ∣ 2 ^ m := h.trans (orderOf_dvd_of_pow_eq_one hs)
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
    have hB : IsPGroup r B := (CFSG.LieType.BorelTits.pCore_isPGroup r (G := Q)).to_le inf_le_left
    have hcomm : ∀ a b, α a * β b = β b * α a := by
      intro a b
      ext y
      simp only [α, β, MulAut.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        MulAut.conjNormal_apply, Subgroup.coe_subtype]
      have hab : (a : Q) * b = b * a := hzY a a.2 b b.2.2
      calc (a : Q) * (b * y * (b : Q)⁻¹) * (a : Q)⁻¹ = (a * b) * y * ((a : Q) * b)⁻¹ := by group
        _ = (b * a) * y * ((b : Q) * a)⁻¹ := by rw [hab]
        _ = b * (a * y * (a : Q)⁻¹) * (b : Q)⁻¹ := by group
    have hfix : ∀ a y, (∀ b, β b y = y) → α a y = y := by
      intro a y hy
      have hyY : (y : Q) ∈ Y := by
        refine hY r hr hr2 y y.2 fun b hb => ?_
        have h1 := congrArg Subtype.val (hy ⟨b, hb⟩)
        simp only [β, MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply,
          Subgroup.coe_subtype] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1
      apply Subtype.ext
      simp only [α, MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply,
        Subgroup.coe_subtype]
      rw [mul_inv_eq_iff_eq_mul, hzY a a.2 y hyY]
    have h := CFSG.GroupTheory.thompson_A_times_B
      (CFSG.LieType.BorelTits.pCore_isPGroup r (G := Q)) hA hB α β hcomm hfix
      ⟨s, Subgroup.mem_zpowers s⟩
    intro y hy
    have h1 := congrArg (fun φ : MulAut P => ((φ ⟨y, hy⟩ : P) : Q)) h
    simp only [α, MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply,
      Subgroup.coe_subtype, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hF : s ∈ Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) := by
    refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
      (P := Subgroup.zpowers s) (fun q => ?_) (Subgroup.mem_zpowers s)
    rw [Subgroup.zpowers_le]
    by_cases hq2 : ((q : ℕ) : ℕ) = 2
    · rw [hq2, hO2]
      intro h hh
      rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
    · exact hr _ (Nat.prime_of_mem_primeFactors q.1.2) hq2
  exact eq_one_of_mem_fitting_of_pow hO2
    (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hF) hs

omit [Finite G] in
private theorem mk_mem_map_subgroupOf {M X : Subgroup G} {g : M} (hg : (g : G) ∈ X) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 M) g ∈
      (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.Open.pCore 2 M)) :=
  ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem isSylowTwoOf_centralizerSection {M X : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hsolv : Group.IsSolvable M) (hXo : X = oTwoUpper X) (hXp : X ≤ O2pOf M p)
    (hRX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G)) :
    IsSylowTwoOf (pCoreOf 2 M)
      (centralizerSection M (O2FOf M ⊓ Subgroup.normalizer (X : Set G)) (pCoreOf 2 M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 M with hR
  set H := O2FOf M ⊓ Subgroup.normalizer (X : Set G) with hH
  have hXK : X ≤ O2FOf M := hXp.trans (O2pOf_le_O2FOf M p)
  have hRH : R ≤ H := le_inf (pCoreOf_le_O2FOf M) hRX
  have hHM : H ≤ M := inf_le_left.trans (O2FOf_le M)
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨(le_centralizerSection_iff hRH).mpr ⟨pCoreOf_le 2 M,
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hHM.trans (le_normalizer_pCoreOf 2 M))⟩, hR2, fun P hPC hP2 hRP => ?_⟩
  intro s hsP
  have hsC := hPC hsP
  rw [mem_centralizerSection_iff_of_le hRH] at hsC
  obtain ⟨hsM, hsH⟩ := hsC
  obtain ⟨m, hm⟩ := hP2 ⟨s, hsP⟩
  have hm' : (⟨s, hsM⟩ : M) ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 M) with hπ
  set Y := (H.subgroupOf M).map π with hY
  have hsolvQ : Group.IsSolvable (M ⧸ CFSG.Open.pCore 2 M) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have hXbar : ∀ x ∈ X, ∀ hx : x ∈ M, π ⟨x, hx⟩ ∈ CFSG.Open.pCore p (M ⧸ CFSG.Open.pCore 2 M) := by
    intro x hx hxM
    obtain ⟨x', hx', he⟩ := hXp hx
    obtain rfl : x' = ⟨x, hxM⟩ := Subtype.ext he
    exact hx'
  have hXY : ∀ x ∈ X, ∀ hx : x ∈ M, π ⟨x, hx⟩ ∈ Y := fun x hx hxM =>
    mk_mem_map_subgroupOf (M := M) (g := ⟨x, hxM⟩) ⟨hXK hx, Subgroup.le_normalizer hx⟩
  have hYc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ y ∈ CFSG.Open.pCore r (M ⧸ CFSG.Open.pCore 2 M),
      (∀ b ∈ CFSG.Open.pCore r (M ⧸ CFSG.Open.pCore 2 M) ⊓ Y, b * y = y * b) → y ∈ Y := by
    intro r hr hr2 y hy hyc
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 M) y
    have hcX : ∀ x ∈ X, ∀ hx : x ∈ M, π ⟨x, hx⟩ * π g = π g * π ⟨x, hx⟩ := by
      intro x hx hxM
      by_cases hrp : r = p
      · subst hrp
        exact hyc _ ⟨hXbar x hx hxM, hXY x hx hxM⟩
      · have hdis : Disjoint (CFSG.Open.pCore r (M ⧸ CFSG.Open.pCore 2 M))
            (CFSG.Open.pCore p (M ⧸ CFSG.Open.pCore 2 M)) :=
          IsPGroup.disjoint_of_ne r p hrp _ _ (CFSG.LieType.BorelTits.pCore_isPGroup r)
            (CFSG.LieType.BorelTits.pCore_isPGroup p)
        exact (Subgroup.commute_of_normal_of_disjoint _ _ (CFSG.LieType.BorelTits.pCore_normal r)
          (CFSG.LieType.BorelTits.pCore_normal p) hdis _ _ hy (hXbar x hx hxM)).symm.eq
    have hgX : (g : G) ∈ Subgroup.normalizer (X : Set G) := by
      refine mem_normalizer_of_conj_mem_sup hXo hR2 hRX
        (le_normalizer_pCoreOf 2 M g.2) fun x hx => ?_
      have hxM : x ∈ M := hXK.trans (O2FOf_le M) hx
      have h1 := hcX x hx hxM
      have h2 : π (g * ⟨x, hxM⟩ * g⁻¹ * (⟨x, hxM⟩ : M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 : (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ R := ⟨_, h2, rfl⟩
      have e : (g : G) * x * (g : G)⁻¹ = ((g : G) * x * (g : G)⁻¹ * x⁻¹) * x := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem _ (le_sup_left (a := R) h3) (le_sup_right (b := X) hx)
    have hgK : (g : G) ∈ O2FOf M := by
      have h := CFSG.pCore_le_fitting (M ⧸ CFSG.Open.pCore 2 M) r
      exact ⟨g, h hy, rfl⟩
    exact mk_mem_map_subgroupOf (M := M) (g := g) ⟨hgK, hgX⟩
  have hs1 : π ⟨s, hsM⟩ = 1 := by
    refine eq_one_of_centralizes hsolvQ B6.pCore_quotient_pCore hYc (m := m)
      (by rw [← map_pow, hm', map_one]) ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hze⟩ := hsH y (Subgroup.mem_subgroupOf.mp hy)
    have hz' : z = y * ⟨s, hsM⟩ * y⁻¹ * (⟨s, hsM⟩ : M)⁻¹ := Subtype.ext (by simpa using hze)
    have h2 : π (y * ⟨s, hsM⟩ * y⁻¹ * (⟨s, hsM⟩ : M)⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hz']
      exact hz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π y * π ⟨s, hsM⟩ =
        (π y * π ⟨s, hsM⟩ * (π y)⁻¹ * (π ⟨s, hsM⟩)⁻¹) * (π ⟨s, hsM⟩ * π y) := by group
      _ = π ⟨s, hsM⟩ * π y := by rw [h2, one_mul]
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hs1
  exact ⟨_, hs1, rfl⟩

theorem le_pCoreOf_of_O2FOf_le_normalizer {MX R : Subgroup G} (hsolv : Group.IsSolvable MX)
    (hRMX : R ≤ MX) (hR2 : IsPGroup 2 R) (hN : O2FOf MX ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ pCoreOf 2 MX := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 MX) with hπ
  have hO2 : CFSG.Open.pCore 2 (MX ⧸ CFSG.Open.pCore 2 MX) = ⊥ := B6.pCore_quotient_pCore
  have hsolvQ : Group.IsSolvable (MX ⧸ CFSG.Open.pCore 2 MX) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have hFn : (O2F MX).Normal := by
    unfold O2F
    infer_instance
  intro r hr
  set r' : MX := ⟨r, hRMX hr⟩
  have hc : π r' ∈ Subgroup.centralizer
      (CFSG.fittingSubgroup (MX ⧸ CFSG.Open.pCore 2 MX) : Set (MX ⧸ CFSG.Open.pCore 2 MX)) := by
    intro z hz
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 MX) z
    have hf : f ∈ O2F MX := hz
    set c := r' * f * r'⁻¹ * f⁻¹ with hc
    have hcR : (c : G) ∈ R := by
      have h1 : (f : G) * r⁻¹ * (f : G)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hN ⟨f, hf, rfl⟩) r⁻¹).mp (R.inv_mem hr)
      have e : (c : G) = r * ((f : G) * r⁻¹ * (f : G)⁻¹) := by
        simp only [hc, r', Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact R.mul_mem hr h1
    have hcF : c ∈ O2F MX := by
      have h1 : r' * f * r'⁻¹ ∈ O2F MX := hFn.conj_mem f hf r'
      exact (O2F MX).mul_mem h1 ((O2F MX).inv_mem hf)
    obtain ⟨k, hk⟩ := hR2 ⟨c, hcR⟩
    have hk' : c ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : π c = 1 := eq_one_of_mem_fitting_of_pow hO2 hcF (m := k)
      (by rw [← map_pow, hk', map_one])
    have h2 : π r' * π f * (π r')⁻¹ * (π f)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    calc π f * π r' = (π r' * π f * (π r')⁻¹ * (π f)⁻¹)⁻¹ * (π r' * π f) := by group
      _ = π r' * π f := by rw [h2, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hk' : r' ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 : π r' = 1 := eq_one_of_mem_fitting_of_pow hO2
    (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvQ hc) (m := k)
    (by rw [← map_pow, hk', map_one])
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨r', h1, rfl⟩

theorem commutator_mem_pCoreOf_of_altBlock (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    {MX L : Subgroup G}
    (hMX : IsTwoLocal MX) (hL : IsBlock2 MX L) (hL3 : IsAltType L 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {y : G} (hyMX : y ∈ MX) {k : ℕ} (hy : y ^ p ^ k = 1) {l : G} (hl : l ∈ L) :
    l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 MX := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLMX : L ≤ MX := hL.2.1
  have hsnM : (L.subgroupOf MX).IsSubnormal := hL.2.2
  have hsn : IsSubnormal L MX :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hLMX).mp
      ((CFSG.Adapters.isSubnormal_top_iff _).mpr hsnM)
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 MX := A4.pCoreOf_le_of_subnormal 2 hsn
  have hcube : ∀ l ∈ L, l ^ 3 ∈ pCoreOf 2 MX := by
    intro l hl
    obtain ⟨α, -, hαker, -⟩ := hL3
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
    have h1 : (⟨l, hl⟩ : L) ^ 3 ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have h := pow_card_eq_one' (x := α ⟨l, hl⟩)
      rwa [hcard] at h
    rw [hαker] at h1
    exact hO2L ⟨_, h1, rfl⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 MX) with hπ
  set Lbar := (L.subgroupOf MX).map π with hLbar
  have hLbar3 : IsPGroup 3 Lbar := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨w, hw, he⟩ := hcube l (Subgroup.mem_subgroupOf.mp hl)
    have hw' : w = l ^ 3 := Subtype.ext (by simpa using he)
    have h1 : π (l ^ 3) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hw']
      exact hw
    simpa [pow_one, map_pow] using h1
  have hLbarsn : IsSubnormal Lbar ⊤ :=
    (CFSG.Adapters.isSubnormal_top_iff _).mpr (hsnM.map (QuotientGroup.mk'_surjective _))
  have hLbarP : Lbar ≤ CFSG.Open.pCore 3 (MX ⧸ CFSG.Open.pCore 2 MX) := by
    have h1 := le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer hLbar3
    have h2 := A4.pCoreOf_le_of_subnormal 3 hLbarsn
    rw [pCoreOf_top] at h2
    exact h1.trans h2
  set P := CFSG.Open.pCore 3 (MX ⧸ CFSG.Open.pCore 2 MX) with hP
  have : P.Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hα : (MulAut.conjNormal (H := P) (π ⟨y, hyMX⟩)) ^ p ^ k = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨y, hyMX⟩ : MX) ^ p ^ k = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one, map_one]
  have h1 := eq_one_of_pow_eq_one_of_lt (q := 3) (by norm_num)
    (CFSG.LieType.BorelTits.pCore_isPGroup 3) (pRank_pCore_quotient_le_two hK hMX
      Nat.prime_three (by norm_num)) hp (by omega) (by omega) hα
  have hlM : l ∈ MX := hLMX hl
  have hlP : π ⟨l, hlM⟩ ∈ P := hLbarP ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have h2 := congrArg (fun α : MulAut P => ((α ⟨_, hlP⟩ : P) : MX ⧸ CFSG.Open.pCore 2 MX)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  have h3 : π (⟨l, hlM⟩ * ⟨y, hyMX⟩ * (⟨l, hlM⟩ : MX)⁻¹ * (⟨y, hyMX⟩ : MX)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π ⟨l, hlM⟩ * π ⟨y, hyMX⟩ * (π ⟨l, hlM⟩)⁻¹ * (π ⟨y, hyMX⟩)⁻¹ =
        π ⟨l, hlM⟩ * (π ⟨y, hyMX⟩ * (π ⟨l, hlM⟩)⁻¹ * (π ⟨y, hyMX⟩)⁻¹) := by group
      _ = 1 := by
        rw [show π ⟨y, hyMX⟩ * (π ⟨l, hlM⟩)⁻¹ * (π ⟨y, hyMX⟩)⁻¹ =
            (π ⟨y, hyMX⟩ * π ⟨l, hlM⟩ * (π ⟨y, hyMX⟩)⁻¹)⁻¹ by group, h2, mul_inv_cancel]
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact ⟨_, h3, by simp⟩

end General

section Unique

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

omit [Finite G] in
private theorem mem_of_pow_mem_of_coprime {Q : Subgroup G} {x : G} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m ∈ Q) (hn : x ^ n ∈ Q) : x ∈ Q := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  have h1 : x ^ ((m : ℤ) * a + (n : ℤ) * b) = (x ^ m) ^ a * (x ^ n) ^ b := by
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have h2 : (m : ℤ) * a + (n : ℤ) * b = 1 := by linarith
  rw [h2, zpow_one] at h1
  rw [h1]
  exact Q.mul_mem (Q.zpow_mem hm a) (Q.zpow_mem hn b)

theorem eq_oTwoUpper_sup_of_le_O2FOf {M Y : Subgroup G} (hRY : pCoreOf 2 M ≤ Y)
    (hYK : Y ≤ O2FOf M) : Y = oTwoUpper Y ⊔ pCoreOf 2 M := by
  refine le_antisymm (fun y hy => ?_) (sup_le (oTwoUpper_le Y) hRY)
  set n := orderOf y
  set a := n.factorization 2
  have hn0 : n ≠ 0 := (orderOf_pos y).ne'
  have hdvd : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
  have hodd : Odd (orderOf (y ^ 2 ^ a)) := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn0))
  have h1 : y ^ 2 ^ a ∈ oTwoUpper Y ⊔ pCoreOf 2 M :=
    le_sup_left (a := oTwoUpper Y) (mem_oTwoUpper_of_odd (Y.pow_mem hy _) hodd)
  have h2 : y ^ (n / 2 ^ a) ∈ oTwoUpper Y ⊔ pCoreOf 2 M := by
    refine le_sup_right (b := pCoreOf 2 M) (mem_pCoreOf_of_mem_O2FOf (hYK (Y.pow_mem hy _))
      (m := a) ?_)
    rw [← pow_mul, Nat.div_mul_cancel hdvd, pow_orderOf_eq_one]
  refine mem_of_pow_mem_of_coprime ?_ h1 h2
  exact Nat.Coprime.pow_left a (Nat.Coprime.symm (Nat.coprime_two_right.mpr
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn0)))))

theorem exists_normal_pElements {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M)
    (hMc : CharTwo M) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hne : CFSG.Open.pCore p (M ⧸ CFSG.Open.pCore 2 M) ≠ ⊥) :
    ∃ Y₀ : Subgroup G, Y₀ ≤ M ∧ Y₀ = oTwoUpper Y₀ ∧ M ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Subgroup.normalizer (Y₀ : Set G) ≤ M ∧
      (∀ y ∈ Y₀, Odd (orderOf y) → ∃ k : ℕ, y ^ p ^ k = 1) ∧
      ∀ X : Subgroup G, X = oTwoUpper X → X ≤ O2pOf M p →
        pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G) → Y₀ ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 M with hR
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 M) with hπ
  set P := CFSG.Open.pCore p (M ⧸ CFSG.Open.pCore 2 M) with hP
  have : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hPp : IsPGroup p P := CFSG.LieType.BorelTits.pCore_isPGroup p
  set Zc := P ⊓ Subgroup.centralizer (P : Set (M ⧸ CFSG.Open.pCore 2 M)) with hZc
  have hZcn : Zc.Normal := Subgroup.normal_inf_normal _ _
  set YZ := (Zc.comap π).map M.subtype with hYZ
  set Y₀ := oTwoUpper YZ with hY₀
  have hYZM : YZ ≤ M := Subgroup.map_subtype_le _
  have hMYZ : M ≤ Subgroup.normalizer (YZ : Set G) := by
    have hN : (Zc.comap π).Normal := hZcn.comap π
    have h1 := Subgroup.le_normalizer_map (H := Zc.comap π) M.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hN, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
  have hMY₀ : M ≤ Subgroup.normalizer (Y₀ : Set G) :=
    hMYZ.trans (normalizer_le_normalizer_oTwoUpper YZ)
  have hY₀M : Y₀ ≤ M := (oTwoUpper_le YZ).trans hYZM
  have hYZmem : ∀ g ∈ YZ, ∃ g' : M, (g' : G) = g ∧ π g' ∈ Zc := by
    rintro _ ⟨g', hg', rfl⟩
    exact ⟨g', rfl, hg'⟩
  have hY₀R : ¬ Y₀ ≤ R := by
    intro hle
    have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
    have : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center P)
    set z' : M ⧸ CFSG.Open.pCore 2 M := ((z : P) : M ⧸ CFSG.Open.pCore 2 M) with hz'
    have hzZ : z' ∈ Zc := by
      refine ⟨(z : P).2, fun w hw => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩)
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 M) z'
    have hgYZ : (g : G) ∈ YZ := ⟨g, show π g ∈ Zc by rw [hπ, hg]; exact hzZ, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper YZ hgYZ
    obtain ⟨w, hw, hwe⟩ := hle hk
    have hw' : w = g ^ 2 ^ k := Subtype.ext (by simpa using hwe)
    have h1 : π (g ^ 2 ^ k) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hw']
      exact hw
    rw [map_pow, hπ, hg] at h1
    obtain ⟨n, hn⟩ := hPp (z : P)
    have hn' : z' ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hz'1 : z' = 1 := eq_one_of_pow_prime_pow hp.out Nat.prime_two hp2 hn' h1
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact hz'1
  refine ⟨Y₀, hY₀M, (A4.oTwoUpper_oTwoUpper YZ).symm, hMY₀, ?_, ?_, ?_⟩
  ·
    have hO : pCoreOf 2 Y₀ ≠ ⊥ := by
      intro hbot
      apply hY₀R
      intro y hy
      refine hMc ⟨hY₀M hy, fun r hr => ?_⟩
      have hc1 : y * r * y⁻¹ * r⁻¹ ∈ R :=
        R.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M (hY₀M hy))
          r).mp hr) (R.inv_mem hr)
      have hc2 : y * r * y⁻¹ * r⁻¹ ∈ Y₀ := by
        have h1 : r * y⁻¹ * r⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.mp
          (hMY₀ (pCoreOf_le 2 M hr)) y⁻¹).mp (Y₀.inv_mem hy)
        have e : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
        rw [e]
        exact Y₀.mul_mem hy h1
      have hc3 : y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 Y₀ := by
        refine le_pCoreOf_of_le_normalizer 2 (inf_le_left (b := R))
          (fun g hg => A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
            (le_normalizer_pCoreOf 2 M (hY₀M hg))) (hR2.to_le inf_le_right) ⟨hc2, hc1⟩
      rw [hbot, Subgroup.mem_bot] at hc3
      have e : r * y = y * r := by
        have := mul_eq_one_iff_eq_inv.mp hc3
        rw [inv_inv] at this
        calc r * y = (y * r * y⁻¹) * y := by rw [this]
          _ = y * r := by group
      exact e
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y₀ : Set G)) :=
      ⟨pCoreOf 2 Y₀, hO, pCoreOf_isPGroup 2 Y₀, rfl⟩
    have heq := hM.2 _ hloc (hMY₀.trans (normalizer_le_normalizer_pCoreOf 2 Y₀))
    rw [← heq]
    exact normalizer_le_normalizer_pCoreOf 2 Y₀
  ·
    intro y hy hodd
    obtain ⟨y', rfl, hy'⟩ := hYZmem y (oTwoUpper_le YZ hy)
    obtain ⟨a, ha⟩ := hPp ⟨_, hy'.1⟩
    have ha' : π (y' ^ p ^ a) = 1 := by rw [map_pow]; simpa using congrArg Subtype.val ha
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha'
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := M) ⟨_, ha'⟩
    have hb' : ((y' : G) ^ p ^ a) ^ 2 ^ b = 1 := by
      have := congrArg (fun z : CFSG.Open.pCore 2 M => ((z : M) : G)) hb
      simpa using this
    have hodd' : Odd (orderOf ((y' : G) ^ p ^ a)) := hodd.of_dvd_nat (orderOf_pow_dvd _)
    exact ⟨a, orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (hodd'.coprime_two_right.pow_right b) (orderOf_dvd_of_pow_eq_one hb'))⟩
  ·
    intro X hXo hXp hRX
    refine (oTwoUpper_le YZ).trans fun g hg => ?_
    obtain ⟨g', rfl, hg'⟩ := hYZmem g hg
    refine mem_normalizer_of_conj_mem_sup hXo hR2 hRX (le_normalizer_pCoreOf 2 M g'.2)
      fun x hx => ?_
    obtain ⟨x', hx', hxe⟩ := hXp hx
    have hc : π x' * π g' = π g' * π x' := hg'.2 _ hx'
    have h2 : π (g' * x' * g'⁻¹ * x'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : (g' : G) * x * (g' : G)⁻¹ * x⁻¹ ∈ R := ⟨_, h2, by simp [← hxe]⟩
    have e : (g' : G) * x * (g' : G)⁻¹ =
        ((g' : G) * x * (g' : G)⁻¹ * x⁻¹) * x := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem _ (le_sup_left (a := R) h3) (le_sup_right (b := X) hx)

theorem pCoreOf_ne_bot_of_isSmallXi (hyp : MultipleCentralizerHypothesis G T) {X : Subgroup G}
    (hX : IsSmallXi T X) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  set T' : Sylow 2 G := hyp.sylow.1.toSylow hyp.sylow.2 with hT'
  have hT'c : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hC : CharTwo (X ⊔ T) :=
    charTwo_of_inH hyp.qtke.2.1 T' (by rw [hT'c]; exact hX.2.2.1)
  set Q := pCoreOf 2 (X ⊔ T)
  have hXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hXQ : X ≤ Q := by
    intro x hx
    refine hC ⟨le_sup_left (b := T) hx, fun q hq => ?_⟩
    have hqXT : q ∈ X ⊔ T := pCoreOf_le 2 _ hq
    have hc1 : x * q * x⁻¹ * q⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _
        (le_sup_left (b := T) hx)) q).mp hq) (Q.inv_mem hq)
    have hc2 : x * q * x⁻¹ * q⁻¹ ∈ X := by
      have h1 : q * x⁻¹ * q⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hXN hqXT) x⁻¹).mp (X.inv_mem hx)
      have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
      rw [e]
      exact X.mul_mem hx h1
    have hc3 : x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 X := by
      refine le_pCoreOf_of_le_normalizer 2 (inf_le_left (b := Q))
        (fun g hg => A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
          (le_normalizer_pCoreOf 2 _ (le_sup_left (b := T) hg)))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨hc2, hc1⟩
    rw [hbot, Subgroup.mem_bot] at hc3
    have := mul_eq_one_iff_eq_inv.mp hc3
    rw [inv_inv] at this
    calc q * x = (x * q * x⁻¹) * x := by rw [this]
      _ = x * q := by group
  have hX2 : X ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
      ((pCoreOf_isPGroup 2 _).to_le hXQ)
  obtain ⟨p, hp, -, hidx⟩ := hX.2.2.2
  rw [Subgroup.relIndex_eq_one.mpr hX2] at hidx
  exact hp.one_lt.ne hidx

theorem exists_isUniqueM_of_isSmallXi (hC226 : InputC226) (hyp : MultipleCentralizerHypothesis G T)
    (h2 : Stmt1542Two G T) (h3 : Stmt1542Three G T) {X : Subgroup G} {p : ℕ}
    (hX : IsSmallXi T X) (hXp : (pCoreOf 2 X).relIndex X = p)
    (hmax : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ p) (hp3 : 3 < p) :
    ∃ M : Subgroup G, IsUniqueM (X ⊔ T) M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p', hp', hp'2, hidx⟩ := hX.2.2.2
  obtain rfl : p' = p := hidx.symm.trans hXp
  have : Fact p'.Prime := ⟨hp'⟩
  have hp5 : 5 ≤ p' := by
    rcases (by omega : p' = 4 ∨ 5 ≤ p') with h | h
    · subst h
      exact absurd hp' (by norm_num)
    · exact h
  set T' : Sylow 2 G := hyp.sylow.1.toSylow hyp.sylow.2 with hT'
  have hT'c : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hEven := hyp.qtke.2.1
  have hXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hO2X := pCoreOf_ne_bot_of_isSmallXi hyp hX
  obtain ⟨MX, hMX, hNMX⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 X, hO2X, pCoreOf_isPGroup 2 X, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)))
  have hNX : Subgroup.normalizer (X : Set G) ≤ MX :=
    (normalizer_le_normalizer_pCoreOf 2 X).trans hNMX
  have hXTMX : X ⊔ T ≤ MX := hXN.trans hNX
  refine ⟨MX, ⟨hMX, hXTMX⟩, fun M hM => ?_⟩
  have hMT : InM T M := ⟨hM.1, le_sup_right.trans hM.2⟩
  have hMXT : InM T MX := ⟨hMX, le_sup_right.trans hXTMX⟩
  have hTM : (T' : Subgroup G) ≤ M := hT'c ▸ hMT.2
  have hTMX : (T' : Subgroup G) ≤ MX := hT'c ▸ hMXT.2
  have hMc : CharTwo M := hEven M hM.1.1 ⟨T', hTM⟩
  have hMXc : CharTwo MX := hEven MX hMX.1 ⟨T', hTMX⟩
  have hXp2 : X ≤ O2pOf M p' := le_O2pOf_of_isSmallXi hyp h2 h3 hX hXp hmax hp3 hM
  have hRT : pCoreOf 2 M ≤ T := hT'c ▸ pCoreOf_two_le_sylow M T' hTM
  have hRX : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G) := hRT.trans hX.2.1
  have hRMX : pCoreOf 2 M ≤ MX := hRT.trans (le_sup_right.trans hXTMX)
  have hR2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  set Ya := O2FOf M ⊓ Subgroup.normalizer (X : Set G) with hYa
  have hRYa : pCoreOf 2 M ≤ Ya := le_inf (pCoreOf_le_O2FOf M) hRX
  have hYaI : Ya ≤ M ⊓ MX := le_inf (inf_le_left.trans (O2FOf_le M)) (inf_le_right.trans hNX)
  have hRI : pCoreOf 2 (M ⊓ MX) = pCoreOf 2 M :=
    a4_4_1_of_faithful hRYa hYaI (eq_oTwoUpper_sup_of_le_O2FOf hRYa inf_le_left)
      (isSubnormal_of_le_O2FOf hRYa inf_le_left)
      (isSylowTwoOf_centralizerSection hp'2 (h2 M hMT) hX.1 hXp2 hRX)
  have hCI : cgsIn MX (pCoreOf 2 M) ≤ M ⊓ MX := by
    have := a4_4_2_of_pCoreOf_eq hM.1 hRI
    rwa [hRI] at this
  have hIR : M ⊓ MX ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreOf 2 M)
  have hO2MX : pCoreOf 2 MX ≤ pCoreOf 2 M := by
    rw [← hRI]
    refine le_pCoreOf_of_le_normalizer 2 (le_inf ?_ (pCoreOf_le 2 MX))
      (inf_le_right.trans (le_normalizer_pCoreOf 2 MX)) (pCoreOf_isPGroup 2 MX)
    exact (hT'c ▸ pCoreOf_two_le_sylow MX T' hTMX).trans hMT.2
  by_cases hle : O2FOf MX ≤ M ⊓ MX
  ·
    have h1 : pCoreOf 2 M ≤ pCoreOf 2 MX :=
      le_pCoreOf_of_O2FOf_le_normalizer (h2 MX hMXT) hRMX hR2 (hle.trans hIR)
    exact a4_4_3_of_pCoreOf_eq hM.1 hMX (le_antisymm hO2MX h1)
  ·
    exfalso
    have hRne : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
    have hNR : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
      hM.1.2 _ ⟨pCoreOf 2 M, hRne, hR2, rfl⟩ (le_normalizer_pCoreOf 2 M)
    have hrad : IsTwoRadicalIn MX (pCoreOf 2 M) :=
      ⟨hRMX, hRne, by rw [hNR, inf_comm, hRI]⟩
    have hconj : conjClosure (pCoreOf 2 M) (M ⊓ MX) = pCoreOf 2 M :=
      le_antisymm (conjClosure_le fun h hh z hz =>
        (Subgroup.mem_normalizer_iff.mp (hIR hh) z).mp hz) (le_conjClosure _ _)
    have hsyl : IsSylowTwoOf (pCoreOf 2 M) (conjClosure (pCoreOf 2 M) (M ⊓ MX)) := by
      rw [hconj]
      refine ⟨le_rfl, hR2, ?_⟩
      rw [Subgroup.subgroupOf_self, Subgroup.index_top]
      norm_num
    have hMXO2 : pCoreOf 2 MX ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hMX.1
    obtain ⟨r, L, hL, hdec⟩ := hC226 G MX (pCoreOf 2 M) (M ⊓ MX)
      (isSQTKCat_of_hyp hyp hMXO2) hrad inf_le_right hCI
      hsyl (A4.charTwo_of_normal (O2FOf_le MX) (le_normalizer_O2FOf MX) hMXc) hle
    obtain ⟨i⟩ : Nonempty (Fin r) := by
      by_contra hr
      rw [not_nonempty_iff] at hr
      apply hle
      rw [hdec, iSup_of_empty, sup_bot_eq]
      exact inf_le_left
    obtain ⟨hLb, hL3, hLI⟩ := hL i
    have hPne : CFSG.Open.pCore p' (M ⧸ CFSG.Open.pCore 2 M) ≠ ⊥ := by
      intro hbot
      have hXR : X ≤ pCoreOf 2 M := by
        intro x hx
        obtain ⟨x', hx', rfl⟩ := hXp2 hx
        have hx'' : QuotientGroup.mk' (CFSG.Open.pCore 2 M) x' ∈
            CFSG.Open.pCore p' (M ⧸ CFSG.Open.pCore 2 M) := hx'
        rw [hbot] at hx''
        have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 M) x' = 1 := Subgroup.mem_bot.mp hx''
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact ⟨x', h1, rfl⟩
      have hX2 : X ≤ pCoreOf 2 X :=
        le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (hR2.to_le hXR)
      rw [Subgroup.relIndex_eq_one.mpr hX2] at hXp
      exact hp'.one_lt.ne hXp
    obtain ⟨Y₀, -, hY₀o, hMY₀, hNY₀, hY₀p, hY₀X⟩ := exists_normal_pElements hM.1 hMc hp'2 hPne
    have hY₀MX : Y₀ ≤ MX := (hY₀X X hX.1 hXp2 hRX).trans hNX
    apply hLI
    refine le_inf (fun l hl => hNY₀ ?_) hLb.2.1
    refine mem_normalizer_of_conj_mem_sup hY₀o (pCoreOf_isPGroup 2 MX)
      ((hO2MX.trans (pCoreOf_le 2 M)).trans hMY₀) (le_normalizer_pCoreOf 2 MX (hLb.2.1 hl))
      fun y hy => ?_
    rw [hY₀o] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyY, hodd⟩ := hy
      obtain ⟨k, hk⟩ := hY₀p y hyY hodd
      have hc := commutator_mem_pCoreOf_of_altBlock hyp.qtke hMX.1 hLb hL3 hp' hp5
        (hY₀MX hyY) hk hl
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem _ (le_sup_left (a := pCoreOf 2 MX) hc) (le_sup_right (b := Y₀) hyY)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha

end Unique

end CFSG.Quasithin.EmptyFaithfulMultiple
