module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Centralizer

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (projectivePointAction)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (ActionProperties)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  (matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar
    matrixProjectiveConjugationHom_derivedInclusion)

@[expose] def HighWittSubfieldSemilinearPointwiseCentralizer : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (d : ℕ) (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) (hext : IsExtension k Q₀ Q),
    (polarBilin Q₀).Nondegenerate →
    (∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) →
    ∀ g : similarityPairs Q,
      (∀ t ∈ subfieldDerivedImage k hext, matrixProjectiveConjugationHom Q g t = t) ↔
        ((∀ c ∈ k, g.val.right c = c) ∧ ∃ b : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) b)

structure SubfieldSetup {K : Type} [Field K] (k : Subfield K) {d : ℕ}
    (Q₀ : QuadraticForm k (Fin d → k)) (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (p : ℕ) : Prop where
  hext : IsExtension k Q₀ Q
  hσk : ∀ x, x ∈ k ↔ σ x = x
  hp : p.Prime
  hp2 : p ≠ 2
  hσ : orderOf σ = p
  hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)
  hnd₀ : (polarBilin Q₀).Nondegenerate
  hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0
  hnd : (polarBilin Q).Nondegenerate
  hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0
  hAP : ActionProperties Q (projectivePointAction Q)

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem fixingSubgroup_J (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p)
    (hE : ∀ β : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, β t = t) → β ∈ matrixProjectiveImage Q) :
    fixingSubgroup (MulAut (matrixProjectiveDerived Q))
        (subfieldDerivedImage k S.hext : Set (matrixProjectiveDerived Q)) =
      Subgroup.zpowers (fieldAutT Q σ S.hQσ) := by
  ext β
  constructor
  · intro hβ
    have hβJ : ∀ t ∈ subfieldDerivedImage k S.hext, β t = t := fun t ht => by
      simpa using (mem_fixingSubgroup_iff _).mp hβ t ht
    obtain ⟨g, hg⟩ := hE β hβJ
    obtain ⟨hgk, b, hb⟩ := (hBY K k d Q₀ Q S.hext S.hnd₀ S.hT₀ g).mp (fun t ht => by
      rw [show matrixProjectiveConjugationHom Q g = β from hg]
      exact hβJ t ht)
    have hmem : g.val.right ∈ Subgroup.zpowers σ :=
      CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed fun x hx =>
        hgk x ((S.hσk x).mpr hx)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : matrixProjectiveConjugationHom Q g =
        matrixProjectiveConjugationHom Q ((fieldPair Q σ S.hQσ) ^ m) := by
      refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q b ?_ ?_
      · rw [hb, fieldPair_zpow_val, SemidirectProduct.left_inr, one_mul]
      · rw [fieldPair_zpow_val, SemidirectProduct.right_inr, hm]
    rw [← hg]
    change matrixProjectiveConjugationHom Q g ∈ _
    rw [h1, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro hβ
    refine (Subgroup.zpowers_le (H := fixingSubgroup (MulAut (matrixProjectiveDerived Q))
      (subfieldDerivedImage k S.hext : Set (matrixProjectiveDerived Q)))).mpr ?_ hβ
    rw [mem_fixingSubgroup_iff]
    intro t ht
    simpa using fieldAutT_fixes_J k Q σ S.hQσ S.hext S.hσk ht


theorem centralizer_J_trivial (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p) {t : matrixProjectiveDerived Q}
    (ht : ∀ j ∈ subfieldDerivedImage k S.hext, t * j = j * t) : t = 1 := by
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q t
  have hκ := matrixProjectiveConjugationHom_derivedInclusion Q y
  have hfix : ∀ j ∈ subfieldDerivedImage k S.hext,
      matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q y) j = j := fun j hj => by
    rw [hκ, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact ht j hj
  obtain ⟨-, b, hb⟩ := (hBY K k d Q₀ Q S.hext S.hnd₀ S.hT₀ _).mp hfix
  have hb' : y.val = GeneralLinearGroup.scalar (Fin d) b := by
    rw [matrixDerivedInclusion_val, SemidirectProduct.left_inl] at hb
    exact hb
  rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_matrixDerivedScalars_iff Q y).mpr ⟨b, hb'.symm⟩

theorem solvable_normal_trivial (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p) {R : Subgroup (matrixProjectiveDerived Q)}
    (hRN : R ≤ subfieldFixedGroup k Q₀ Q)
    (hR : (R.subgroupOf (subfieldFixedGroup k Q₀ Q)).Normal) (hsolv : Group.IsSolvable R) :
    R = ⊥ := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hJsimple : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := by
    have := hsimp
    exact (inclEquiv k S.hext hd).symm.isSimpleGroup
  have hJnonab : ¬ ∀ a b : ↥(subfieldDerivedImage k S.hext), a * b = b * a := by
    intro h
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply (inclEquiv k S.hext hd).injective
    rw [map_mul, map_mul]
    exact h _ _
  have hJN := subfieldDerivedImage_le k S.hext
  have hJnorm := subfieldDerivedImage_normal k S.hext
  have hRJ : R ⊓ subfieldDerivedImage k S.hext = ⊥ := by
    have hR' : ((R ⊓ subfieldDerivedImage k S.hext).subgroupOf
        (subfieldDerivedImage k S.hext)).Normal := by
      refine ⟨fun x hx j => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨?_, (j * x * j⁻¹).2⟩
      have := hR.conj_mem ⟨x.1, hJN x.2⟩ (Subgroup.mem_subgroupOf.mpr hx.1) ⟨j.1, hJN j.2⟩
      exact Subgroup.mem_subgroupOf.mp this
    rcases hJsimple.eq_bot_or_eq_top_of_normal ((R ⊓ subfieldDerivedImage k S.hext).subgroupOf
      (subfieldDerivedImage k S.hext)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_assoc, inf_idem] at h
      exact h
    · exfalso
      have hJR : subfieldDerivedImage k S.hext ≤ R := fun t ht => by
        have : (⟨t, ht⟩ : ↥(subfieldDerivedImage k S.hext)) ∈
            (R ⊓ subfieldDerivedImage k S.hext).subgroupOf (subfieldDerivedImage k S.hext) := by
          rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      have hsolvJ : Group.IsSolvable ↥(subfieldDerivedImage k S.hext) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJR)
          (Subgroup.inclusion_injective hJR)
      exact hJnonab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolvJ)
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  refine centralizer_J_trivial hBY S fun j hj => ?_
  have hrN : r ∈ subfieldFixedGroup k Q₀ Q := hRN hr
  have hjN : j ∈ subfieldFixedGroup k Q₀ Q := hJN hj
  have h1 : r * j * r⁻¹ ∈ subfieldDerivedImage k S.hext := by
    have := hJnorm.conj_mem ⟨j, hjN⟩ (Subgroup.mem_subgroupOf.mpr hj) ⟨r, hrN⟩
    exact Subgroup.mem_subgroupOf.mp this
  have h2 : j * r⁻¹ * j⁻¹ ∈ R := by
    have := hR.conj_mem ⟨r⁻¹, inv_mem hrN⟩ (Subgroup.mem_subgroupOf.mpr (inv_mem hr))
      ⟨j, hjN⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hc : r * j * r⁻¹ * j⁻¹ ∈ R ⊓ subfieldDerivedImage k S.hext := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem h1 (inv_mem hj)⟩
    have : r * (j * r⁻¹ * j⁻¹) ∈ R := mul_mem hr h2
    simpa [mul_assoc] using this
  rw [hRJ, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
  exact hc


omit [Finite K] in
theorem SubfieldSetup.odd (S : SubfieldSetup k Q₀ Q σ p) : Odd p := S.hp.odd_of_ne_two S.hp2

omit [Finite K] in
theorem SubfieldSetup.σ_pow (S : SubfieldSetup k Q₀ Q σ p) : σ ^ p = 1 :=
  S.hσ ▸ pow_orderOf_eq_one σ

omit [Finite K] in
theorem fieldAutT_apply_iff (S : SubfieldSetup k Q₀ Q σ p) (t : matrixProjectiveDerived Q) :
    fieldAutT Q σ S.hQσ t = t ↔ t ∈ subfieldFixedGroup k Q₀ Q := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  exact fieldAutT_eq_self_iff k Q σ S.hQσ S.hext S.hσk S.odd S.σ_pow
    (exists_ne_zero_of_nondeg hd S.hnd) t

theorem fixingSubgroup_N (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p)
    (hE : ∀ β : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, β t = t) → β ∈ matrixProjectiveImage Q) :
    fixingSubgroup (MulAut (matrixProjectiveDerived Q))
        (subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) =
      Subgroup.zpowers (fieldAutT Q σ S.hQσ) := by
  apply le_antisymm
  · rw [← fixingSubgroup_J hBY S hE]
    exact fixingSubgroup_antitone _ _ (subfieldDerivedImage_le k S.hext)
  · refine (Subgroup.zpowers_le (H := fixingSubgroup (MulAut (matrixProjectiveDerived Q))
      (subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)))).mpr ?_
    rw [mem_fixingSubgroup_iff]
    intro t ht
    simpa using (fieldAutT_apply_iff S t).mpr ht


open CFSG.RankThree.PartOne.KCOrthogonalD4 (mulAut_conj_conj conj_injective_of_trivial_center)
open CFSG.RankThree.LocalRank
  (aschbacherSolvableCore solvable_prime_complement_core_characterization)
open CFSG.ComponentClassification (OuterAutomorphisms.inner)

theorem core_trivial (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p)
    (hE : ∀ β : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, β t = t) → β ∈ matrixProjectiveImage Q)
    {B : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hB : OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ B) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer
        ({fieldAutT Q σ S.hQσ} : Set (MulAut (matrixProjectiveDerived Q)))) = ⊥ := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  have hcenter := center_matrix_eq_bot hd S.hnd S.hT
  have hinj := conj_injective_of_trivial_center hcenter
  set a := fieldAutT Q σ S.hQσ with ha
  set N := subfieldFixedGroup k Q₀ Q with hN
  set C := B ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))) with hC
  obtain ⟨hsolv, hchar, hcop, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization S.hp (H := ↥C)
  have hnorm : (aschbacherSolvableCore p ↥C).Normal := inferInstance
  set core := aschbacherSolvableCore p ↥C with hcore
  have hS'norm : ∀ c' ∈ C, ∀ s ∈ core.map C.subtype, c' * s * c'⁻¹ ∈ core.map C.subtype := by
    rintro c' hc' _ ⟨s₁, hs₁, rfl⟩
    exact ⟨⟨c', hc'⟩ * s₁ * ⟨c', hc'⟩⁻¹, hnorm.conj_mem s₁ hs₁ ⟨c', hc'⟩, rfl⟩
  have hconjC : ∀ n ∈ N, (MulAut.conj n : MulAut (matrixProjectiveDerived Q)) ∈ C := by
    intro n hn
    refine Subgroup.mem_inf.mpr ⟨hB ⟨n, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * MulAut.conj n * a⁻¹ = MulAut.conj (a n) := mulAut_conj_conj a n
    rw [(fieldAutT_apply_iff S n).mpr hn] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  let R : Subgroup (matrixProjectiveDerived Q) :=
    N ⊓ (core.map C.subtype).comap (MulAut.conj : matrixProjectiveDerived Q →* _)
  have hRN : R ≤ N := inf_le_left
  have hRnormal : (R.subgroupOf N).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine Subgroup.mem_inf.mpr ⟨(m * x * m⁻¹).2, ?_⟩
    have h1 := hS'norm _ (hconjC m.1 m.2) _ (Subgroup.mem_inf.mp hx).2
    simpa using h1
  have hRsolv : Group.IsSolvable R := by
    have hS'solv : Group.IsSolvable ↥(core.map C.subtype) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective core C.subtype C.subtype_injective).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective core C.subtype C.subtype_injective).symm.injective
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((MulAut.conj : matrixProjectiveDerived Q →* _).comp R.subtype).codRestrict
        (core.map C.subtype) (fun x => (Subgroup.mem_inf.mp x.2).2)) ?_
    intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hxy
  have hRbot : R = ⊥ := solvable_normal_trivial hBY S hRN hRnormal hRsolv
  rw [eq_bot_iff]
  rintro s ⟨c, hc, rfl⟩
  have hfixc : ∀ n ∈ N, (c : MulAut (matrixProjectiveDerived Q)) n = n := by
    intro n hn
    have hcn : (c : MulAut (matrixProjectiveDerived Q)) n ∈ N := by
      rw [← fieldAutT_apply_iff S]
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
      have : (a * (c : MulAut (matrixProjectiveDerived Q))) n =
          ((c : MulAut (matrixProjectiveDerived Q)) * a) n := by rw [hcomm]
      rw [MulAut.mul_apply, MulAut.mul_apply, (fieldAutT_apply_iff S n).mpr hn] at this
      exact this
    have hmem : (c : MulAut (matrixProjectiveDerived Q)) n * n⁻¹ ∈ R := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem hcn (inv_mem hn), ?_⟩
      have hcS' : (c : MulAut (matrixProjectiveDerived Q)) ∈ core.map C.subtype := ⟨c, hc, rfl⟩
      have h2 := hS'norm _ (hconjC n hn) _ (inv_mem hcS')
      have h3 := mul_mem hcS' h2
      have h4 : (MulAut.conj ((c : MulAut (matrixProjectiveDerived Q)) n * n⁻¹) :
          MulAut (matrixProjectiveDerived Q)) = (c : MulAut (matrixProjectiveDerived Q)) *
          (MulAut.conj n * (c : MulAut (matrixProjectiveDerived Q))⁻¹ * (MulAut.conj n)⁻¹) := by
        rw [map_mul, map_inv, ← mulAut_conj_conj]
        group
      rw [Subgroup.mem_comap, h4]
      exact h3
    rw [hRbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hmemfix : (c : MulAut (matrixProjectiveDerived Q)) ∈
      fixingSubgroup (MulAut (matrixProjectiveDerived Q))
        (N : Set (matrixProjectiveDerived Q)) := by
    rw [mem_fixingSubgroup_iff]
    intro n hn
    simpa using hfixc n hn
  rw [fixingSubgroup_N hBY S hE] at hmemfix
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemfix
  have hap : a ^ p = 1 :=
    (fieldAutT_pow_eq_one_iff Q σ S.hQσ S.hnd S.hT S.hAP p).mpr S.σ_pow
  have hcp : (c : MulAut (matrixProjectiveDerived Q)) ^ p = 1 := by
    rw [← hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hap,
      _root_.one_zpow]
  have hord1 : orderOf (c : MulAut (matrixProjectiveDerived Q)) ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have hord2 : orderOf (c : MulAut (matrixProjectiveDerived Q)) ∣ Nat.card core := by
    rw [Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard core hc
  have hcopr : Nat.Coprime p (Nat.card core) := (S.hp.coprime_iff_not_dvd).mpr hcop
  have hone : orderOf (c : MulAut (matrixProjectiveDerived Q)) = 1 :=
    Nat.dvd_one.mp (hcopr.gcd_eq_one ▸ Nat.dvd_gcd hord1 hord2)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

end Centralizer

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
