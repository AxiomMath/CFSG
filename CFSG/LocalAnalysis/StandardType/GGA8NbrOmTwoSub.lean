module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrameCore
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

open Polynomial Module Multiplicative CFSG.Assembly CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm CoordOm CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit CFSG.LieType.Universal
open CFSG.RankThree.Classical2 (orthDerived)

namespace A8Coord

private theorem om9_singular_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) {u : V}
    {ν : K} (hTu : T u = ν • u) (hν : ν ^ 2 ≠ 1) : Q u = 0 := by
  have h := hT u
  rw [hTu, QuadraticMap.map_smul, smul_eq_mul, ← sq] at h
  have : (ν ^ 2 - 1) * Q u = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν)

private theorem om9_polar_isometry {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (x y : V) :
    QuadraticMap.polar Q (T x) (T y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hT]

private theorem om9_polar_eq_zero_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) {x y : V}
    {l n : K} (hx : T x = l • x) (hy : T y = n • y) (hln : l * n ≠ 1) :
    QuadraticMap.polar Q x y = 0 := by
  have h := om9_polar_isometry hT x y
  rw [hx, hy, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
    smul_eq_mul, ← mul_assoc] at h
  have : (l * n - 1) * QuadraticMap.polar Q x y = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hln)

private theorem om9_eigen_of_mem_primaryComponent {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] {x : V ≃ₗ[K] V} {l : K} {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap (X - C l)) : x v = l • v := by
  rw [mem_primaryComponent] at hv
  simpa [sub_eq_zero] using hv

private theorem om9_pow_apply_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {T : V ≃ₗ[K] V} {u : V} {ν : K} (h : T u = ν • u) (n : ℕ) :
    (T ^ n) u = ν ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

section Eigen


private theorem om9_exists_eigen {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module
    K V] [FiniteDimensional K V] (hK : Nat.card K = 8) {g : V ≃ₗ[K] V} (hg : g ^ 7 = 1)
    {Y : Submodule K V} (hY : Y ≠ ⊥) (hYg : ∀ y ∈ Y, g y ∈ Y) :
    ∃ y ∈ Y, y ≠ 0 ∧ ∃ c : K, g y = c • y := by
  classical
  set f : Module.End K Y := g.toLinearMap.restrict hYg with hf
  have hpow : ∀ n : ℕ, ∀ y : Y, ((f ^ n) y : V) = (g ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hf8 : aeval f (X ^ 8 - X : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X]
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearMap.sub_apply, Submodule.coe_sub, hpow 8, LinearMap.zero_apply,
      Submodule.coe_zero, pow_succ, hg, one_mul]
    exact sub_self _
  have hspl : (X ^ 8 - X : K[X]).Splits := by
    have := Polynomial.splits_X_pow_nat_card_sub_X (K := K)
    rwa [hK] at this
  have hne : (X ^ 8 - X : K[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.natDegree) h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
    simp at this
  have hdvd : minpoly K f ∣ X ^ 8 - X := minpoly.dvd K f hf8
  have hms : (minpoly K f).Splits := hspl.of_dvd hne hdvd
  have : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.mpr hY
  have hdeg : (minpoly K f).degree ≠ 0 := by
    have := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) f)
    intro h
    rw [Polynomial.natDegree_eq_of_degree_eq_some h] at this
    exact lt_irrefl 0 this
  obtain ⟨c, hc⟩ := hms.exists_eval_eq_zero hdeg
  have hev : f.HasEigenvalue c := Module.End.hasEigenvalue_of_isRoot hc
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  refine ⟨y, y.2, fun h0 => hy.2 (Subtype.ext h0), c, ?_⟩
  have := congrArg Subtype.val hy.apply_eq_smul
  simpa [hf] using this

private theorem om9_exists_common_eigen {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hK : Nat.card K = 8) (S : Finset (V ≃ₗ[K] V)) :
    (∀ g ∈ S, g ^ 7 = 1) → (∀ g ∈ S, ∀ g' ∈ S, g * g' = g' * g) →
    ∀ {Y : Submodule K V}, Y ≠ ⊥ → (∀ g ∈ S, ∀ y ∈ Y, g y ∈ Y) →
      ∃ y ∈ Y, y ≠ 0 ∧ ∀ g ∈ S, ∃ c : K, g y = c • y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ Y hY _
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    exact ⟨y, hy, hy0, fun g hg => absurd hg (Finset.notMem_empty g)⟩
  | insert g S hgS ih =>
    intro h7 hc Y hY hinv
    obtain ⟨y0, hy0, hy00, c, hgc⟩ :=
      om9_exists_eigen hK (h7 g (Finset.mem_insert_self g S)) hY
        (hinv g (Finset.mem_insert_self g S))
    set Y' : Submodule K V := Y ⊓ Module.End.eigenspace g.toLinearMap c with hY'
    have hmem : ∀ y, y ∈ Y' ↔ y ∈ Y ∧ g y = c • y := fun y => by
      rw [hY', Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      rfl
    have hY'0 : Y' ≠ ⊥ := fun h => hy00 (by
      have : y0 ∈ Y' := (hmem y0).mpr ⟨hy0, hgc⟩
      rw [h] at this
      exact (Submodule.mem_bot K).mp this)
    have hinv' : ∀ g' ∈ S, ∀ y ∈ Y', g' y ∈ Y' := by
      intro g' hg' y hy
      obtain ⟨hyY, hyg⟩ := (hmem y).mp hy
      refine (hmem _).mpr ⟨hinv g' (Finset.mem_insert_of_mem hg') y hyY, ?_⟩
      have hcomm := hc g (Finset.mem_insert_self g S) g' (Finset.mem_insert_of_mem hg')
      rw [← LinearEquiv.mul_apply, hcomm, LinearEquiv.mul_apply, hyg, map_smul]
    obtain ⟨y, hy, hy0', hyS⟩ := ih (fun g' hg' => h7 g' (Finset.mem_insert_of_mem hg'))
      (fun g' hg' g'' hg'' => hc g' (Finset.mem_insert_of_mem hg') g''
        (Finset.mem_insert_of_mem hg'')) hY'0 hinv'
    refine ⟨y, ((hmem y).mp hy).1, hy0', fun g' hg' => ?_⟩
    rcases Finset.mem_insert.mp hg' with rfl | hg'
    · exact ⟨c, ((hmem y).mp hy).2⟩
    · exact hyS g' hg'

end Eigen

section Root

open CFSG.ClassicalGroups.Orthogonal


private theorem om9_isPGroup_rootGroup {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (e : V) : IsPGroup 2 (rootGroup Q e) := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  have hww : w + w = 0 := by rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  rw [pow_one, Subgroup.coe_pow, sq, eichler_mul hw hw, hww, eichler_zero_right]
  rfl

private theorem om9_exists_twoSubgroup_of_eichler {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {A J : Subgroup (V ≃ₗ[K] V)} {e w : V}
    (hJA : ∀ g ∈ A, ∀ x ∈ J, g * x * g⁻¹ ∈ J)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (heA : ∀ g ∈ A, ∃ c : K, g e = c • e)
    (hw : QuadraticMap.polar Q e w = 0) (hEJ : eichler Q e w ∈ J) (hE1 : eichler Q e w ≠ 1) :
    ∃ T : Subgroup (V ≃ₗ[K] V), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[K] V)) := by
  refine ⟨J ⊓ rootGroup Q e, ?_, (om9_isPGroup_rootGroup e).to_le inf_le_right, inf_le_left, ?_⟩
  · intro hbot
    have : eichler Q e w ∈ J ⊓ rootGroup Q e := ⟨hEJ, eichler_mem_rootGroup hw⟩
    rw [hbot] at this
    exact hE1 ((Subgroup.mem_bot).mp this)
  · have hfw : ∀ g ∈ A, ∀ x ∈ J ⊓ rootGroup Q e, g * x * g⁻¹ ∈ J ⊓ rootGroup Q e := by
      intro g hg x hx
      obtain ⟨c, hc⟩ := heA g hg
      exact ⟨hJA g hg x hx.1, conj_mem_rootGroup_of_apply_eq_smul (hAO hg) hc hx.2⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfw g hg x, fun hx => ?_⟩
    have := hfw g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

end Root

section Linear

open CFSG.ClassicalGroups.Orthogonal


private theorem om9_exists_mem_ne_zero_polar_eq_zero {K : Type} [Field K] {V : Type} [AddCommGroup
    V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {Y : Submodule K V} (hY : 2 ≤
    finrank K Y) (x : V) :
    ∃ y ∈ Y, y ≠ 0 ∧ QuadraticMap.polar Q x y = 0 := by
  by_contra H
  push Not at H
  let f : Y →ₗ[K] K := (QuadraticMap.polarBilin Q x).domRestrict Y
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    exact H y y.2 (fun h => hy0 (Subtype.ext h)) hy
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at this
  omega

private theorem om9_exists_mem_ne_zero_polar_eq_zero₂ {K : Type} [Field K] {V : Type} [AddCommGroup
    V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {Y : Submodule K V} (hY : 3 ≤
    finrank K Y) (x x' : V) :
    ∃ y ∈ Y, y ≠ 0 ∧ QuadraticMap.polar Q x y = 0 ∧ QuadraticMap.polar Q x' y = 0 := by
  by_contra H
  push Not at H
  let f : Y →ₗ[K] K × K := LinearMap.prod ((QuadraticMap.polarBilin Q x).domRestrict Y)
    ((QuadraticMap.polarBilin Q x').domRestrict Y)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    exact H y y.2 (fun h => hy0 (Subtype.ext h)) (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

private theorem om9_finrank_le_of_perp {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {P R : Submodule K V}
    (hperf : ∀ u ∈ P, (∀ v ∈ R, QuadraticMap.polar Q u v = 0) → u = 0) :
    finrank K P ≤ finrank K R := by
  let Φ : P →ₗ[K] Module.Dual K R :=
    (QuadraticMap.polarBilin Q).compl₁₂ P.subtype R.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hperf u u.2 fun v hv => ?_)
    have := LinearMap.congr_fun hu ⟨v, hv⟩
    exact this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

private theorem om9_eichler_ne_one {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q
    : QuadraticForm K V} {e w y : V} (he : Q e = 0) (hw : QuadraticMap.polar Q e w = 0)
    (hy : QuadraticMap.polar Q y e ≠ 0) (hind : ∀ t : K, w ≠ t • e) : eichler Q e w ≠ 1 := by
  intro h1
  have key : eichler Q e w y = y := by rw [h1]; rfl
  rw [eichler_apply he hw] at key
  have h2 : QuadraticMap.polar Q y e • w =
      (QuadraticMap.polar Q y w + Q w * QuadraticMap.polar Q y e) • e := by
    refine sub_eq_zero.mp ?_
    rw [← add_sub_cancel_left y (_ - _), ← add_sub_assoc, key, sub_self]
  apply hind ((QuadraticMap.polar Q y e)⁻¹ *
    (QuadraticMap.polar Q y w + Q w * QuadraticMap.polar Q y e))
  rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hy, one_smul]

end Linear

section Class



private theorem om9_exists_zeta {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) : ∃ ζ : Kˣ,
    orderOf ζ = 7 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := Fintype.ofFinite K
  have hc : Nat.card Kˣ = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  exact exists_prime_orderOf_dvd_card' 7 (by rw [hc])

private theorem om9_mem_pc_iff {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {a : V
    ≃ₗ[K] V} {l : K} {v : V} :
    v ∈ primaryComponent a.toLinearMap (X - C l) ↔ a v = l • v := by
  rw [mem_primaryComponent]
  simp [sub_eq_zero]

private theorem om9_mem_pc_of_comm {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {a
    : V ≃ₗ[K] V} {g : V ≃ₗ[K] V} (hg : g * a = a * g) {l : K} {v : V}
    (hv : v ∈ primaryComponent a.toLinearMap (X - C l)) :
    g v ∈ primaryComponent a.toLinearMap (X - C l) := by
  rw [om9_mem_pc_iff] at hv ⊢
  rw [← LinearEquiv.mul_apply, ← hg, LinearEquiv.mul_apply, hv, map_smul]

private theorem om9_class_eichler {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 7 a) (hK : Nat.card K = 8)
    {A : Subgroup (V ≃ₗ[K] V)} (hA7 : ∀ g ∈ A, g ^ 7 = 1)
    (hAc : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g) (haA : ∀ g ∈ A, g * a = a * g)
    {h : K[X]} (hh : h ∈ primaryFactors a.toLinearMap) (hX : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity a.toLinearMap h) :
    ∃ e w : V, (∀ g ∈ A, ∃ c : K, g e = c • e) ∧ QuadraticMap.polar Q e w = 0 ∧
      eichler Q e w ∈ specialBlock Q a h ∧ eichler Q e w ≠ 1 := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  obtain ⟨ζ, hζ⟩ := om9_exists_zeta hK
  have hh' := hh
  obtain ⟨k, -, rfl⟩ := omf_exists_eq_X_sub_C hx (by norm_num) hζ hh
  set μ := (ζ : K) ^ k with hμ
  have hμ0 : μ ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hμ1 : μ ≠ 1 := fun h1 => hX (by rw [h1, C_1])
  have hμ7 : μ ^ 7 = 1 := by
    rw [hμ, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one,
      Units.val_one, one_pow]
  have hμ2 : μ ^ 2 ≠ 1 := fun h2 => hμ1 (by
    have : μ ^ Nat.gcd 2 7 = 1 := pow_gcd_eq_one.mpr ⟨h2, hμ7⟩
    simpa using this)
  have hμi2 : μ⁻¹ ^ 2 ≠ 1 := fun h2 => hμ2 (by rw [inv_pow, inv_eq_one] at h2; exact h2)
  have hT : ∀ v, Q (a v) = Q v := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp hx.mem
  set S := (Set.toFinite (A : Set (V ≃ₗ[K] V))).toFinset with hS
  have hSm : ∀ g, g ∈ S ↔ g ∈ A := fun g => Set.Finite.mem_toFinset _
  obtain ⟨e, heY, he0, heA⟩ := om9_exists_common_eigen hK S
    (fun g hg => hA7 g ((hSm g).mp hg))
    (fun g hg g' hg' => hAc g ((hSm g).mp hg) g' ((hSm g').mp hg'))
    (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    (fun g hg y hy => om9_mem_pc_of_comm (haA g ((hSm g).mp hg)) hy)
  have he : a e = μ • e := om9_mem_pc_iff.mp heY
  have hQe : Q e = 0 := om9_singular_of_eigen hT he hμ2
  have hrec := hx.reciprocalPolynomial_mem hh
  rw [omf_reciprocalPolynomial_X_sub_C hμ0] at hrec
  haveI : Fact (Irreducible (X - C μ)) := ⟨irreducible_X_sub_C μ⟩
  have hdimh : 2 ≤ finrank K (primaryComponent a.toLinearMap (X - C μ)) := by
    rw [finrank_primaryComponent, natDegree_X_sub_C, one_mul]
    exact hm
  have hdim : 2 ≤ finrank K (primaryComponent a.toLinearMap (X - C μ⁻¹)) := by
    refine hdimh.trans (om9_finrank_le_of_perp (Q := Q) fun u hu hperp => ?_)
    refine hx.eq_zero_of_polar_primaryComponent fun l hl v hv => ?_
    by_cases hlr : l = X - C μ⁻¹
    · subst hlr
      exact hperp v hv
    · refine hx.polar_primaryComponent_eq_zero hh hl ?_ hu hv
      rwa [omf_reciprocalPolynomial_X_sub_C hμ0]
  obtain ⟨w, hwY, hw0, hew⟩ := om9_exists_mem_ne_zero_polar_eq_zero (Q := Q) hdim e
  have hw : a w = μ⁻¹ • w := om9_mem_pc_iff.mp hwY
  have hQw : Q w = 0 := om9_singular_of_eigen hT hw hμi2
  refine ⟨e, w, fun g hg => heA g ((hSm g).mpr hg), hew, ?_, ?_⟩
  ·
    set E := eichler Q e w with hE
    have hiso : ∀ v, Q (E v) = Q v :=
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp (eichler_mem_orthogonalGroup Q e w)
    have hconj : a * E * a⁻¹ = E := by
      rw [hE, eichler_conj hx.mem, he, hw, eichler_smul_left, smul_smul, mul_inv_cancel₀ hμ0,
        one_smul]
    have hcomm : ∀ v, E (a v) = a (E v) := fun v => by
      have : a * E = E * a := calc
        a * E = (a * E * a⁻¹) * a := by group
        _ = E * a := by rw [hconj]
      rw [← LinearEquiv.mul_apply, ← this, LinearEquiv.mul_apply]
    have hS' : E ∈ supportedBlock Q a (X - C μ) := by
      refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨hiso, hcomm⟩, ?_⟩
      rw [fixes_othersSpace_iff]
      intro l hl hlh hlh' v hv
      obtain ⟨m, -, rfl⟩ := omf_exists_eq_X_sub_C hx (by norm_num) hζ hl
      have hv' := om9_eigen_of_mem_primaryComponent hv
      rw [omf_reciprocalPolynomial_X_sub_C hμ0] at hlh'
      have hl1 : (ζ : K) ^ m ≠ μ := fun h => hlh (by rw [h])
      have hl2 : (ζ : K) ^ m ≠ μ⁻¹ := fun h => hlh' (by rw [h])
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · exact om9_polar_eq_zero_of_eigen hT hv' he fun h => hl2 (eq_inv_of_mul_eq_one_left h)
      · exact om9_polar_eq_zero_of_eigen hT hv' hw fun h =>
          hl1 (by rw [← mul_inv_eq_one₀ hμ0]; exact h)
    refine mem_specialBlock.mpr ⟨hS', ?_⟩
    set d := blockDet Q a (X - C μ) ⟨E, hS'⟩ with hd
    have hdd : d * d = 1 := by
      rw [hd, ← map_mul]
      have hww : w + w = 0 := by rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
      have : (⟨E, hS'⟩ * ⟨E, hS'⟩ : ↥(supportedBlock Q a (X - C μ))) = 1 :=
        Subtype.ext (by
          change E * E = 1
          rw [hE, eichler_mul hew hew, hww, eichler_zero_right])
      rw [this, map_one]
    have h2 : (2 : AdjoinRoot (X - C μ)) = 0 := by
      have : (2 : AdjoinRoot (X - C μ)) = algebraMap K _ 2 := (map_ofNat _ 2).symm
      rw [this, CharTwo.two_eq_zero, map_zero]
    have hsq : (d - 1) ^ 2 = 0 := by linear_combination hdd + (1 - d) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  ·
    obtain ⟨y, hy⟩ : ∃ y, QuadraticMap.polar Q y e ≠ 0 := by
      by_contra H
      push Not at H
      exact he0 (hx.regular e fun v => by rw [QuadraticMap.polar_comm]; exact H v)
    refine om9_eichler_ne_one hQe hew hy fun t ht => hw0 ?_
    have h1 : a w = μ • w := by rw [ht, map_smul, he, smul_comm]
    rw [hw] at h1
    have : (μ⁻¹ - μ) • w = 0 := by rw [sub_smul, h1, sub_self]
    refine (smul_eq_zero.mp this).resolve_left fun h0 => hμ2 ?_
    have : μ⁻¹ = μ := sub_eq_zero.mp h0
    rw [sq]
    nth_rewrite 1 [← this]
    exact inv_mul_cancel₀ hμ0

end Class

section Split



private theorem om9_jordan_eq_zero {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {a
    : V ≃ₗ[K] V} (ha7 : a ^ 7 = 1) (h7 : (7 : K) ≠ 0) {l : K}
    (hl7 : l ^ 7 = 1) {m n : V} (hn : a n = l • n) (hm : a m = l • m + n) : n = 0 := by
  have key : ∀ j : ℕ, (a ^ (j + 1)) m = l ^ (j + 1) • m + (((j : K) + 1) * l ^ j) • n := by
    intro j
    induction j with
    | zero => simp [hm]
    | succ j ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_smul, map_smul, hm, hn]
      push_cast
      module
  have h := key 6
  rw [ha7] at h
  change m = _ at h
  rw [show (6 + 1 : ℕ) = 7 from rfl, hl7, one_smul] at h
  have h' : ((((6 : ℕ) : K) + 1) * l ^ 6) • n = 0 := add_eq_left.mp h.symm
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl7
  refine (smul_eq_zero.mp h').resolve_left (mul_ne_zero ?_ (pow_ne_zero _ hl0))
  norm_num
  exact h7

private theorem om9_exists_second_eigen {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hK : Nat.card K = 8) {a : V ≃ₗ[K] V} (ha7 : a ^ 7 = 1)
    (h7 : (7 : K) ≠ 0) {M : Submodule K V} (hM : 2 ≤ finrank K M) (hMa : ∀ v ∈ M, a v ∈ M)
    {x : V} {l : K} (hx : a x = l • x) (hl7 : l ^ 7 = 1) :
    ∃ y ∈ M, (∀ t : K, y ≠ t • x) ∧ ∃ c : K, a y = c • y := by
  classical
  set f : V →ₗ[K] V := a.toLinearMap - l • LinearMap.id with hf
  have hfa : ∀ v, f v = a v - l • v := fun v => rfl
  set M₂ := M.map f with hM₂
  by_cases h2 : M₂ = ⊥
  · have hall : ∀ v ∈ M, a v = l • v := fun v hv => by
      have : f v ∈ M₂ := Submodule.mem_map_of_mem hv
      rw [h2, Submodule.mem_bot, hfa, sub_eq_zero] at this
      exact this
    have hnle : ¬ M ≤ K ∙ x := fun hle => by
      have := Submodule.finrank_mono hle
      have h1 : finrank K (K ∙ x) ≤ 1 := by
        simpa using finrank_span_le_card (R := K) ({x} : Set V)
      omega
    obtain ⟨y, hyM, hyx⟩ := Set.not_subset.mp hnle
    refine ⟨y, hyM, fun t ht => hyx ?_, l, hall y hyM⟩
    rw [ht]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self x)
  · have hM₂a : ∀ v ∈ M₂, a v ∈ M₂ := by
      rintro _ ⟨m, hm, rfl⟩
      refine ⟨a m, hMa m hm, ?_⟩
      simp only [hfa, map_sub, map_smul]
    obtain ⟨y, hyM₂, hy0, c, hyc⟩ := om9_exists_eigen hK ha7 h2 hM₂a
    obtain ⟨m, hm, rfl⟩ := hyM₂
    refine ⟨f m, by rw [hfa]; exact M.sub_mem (hMa m hm) (M.smul_mem l hm), fun t ht => ?_,
      c, hyc⟩
    have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hy0 ht
    have hx0 : x = 0 := by
      refine om9_jordan_eq_zero ha7 h7 hl7 hx (m := t⁻¹ • m) ?_
      have : a m = l • m + t • x := eq_add_of_sub_eq' ht
      rw [map_smul, this, smul_add, smul_smul t⁻¹ t, inv_mul_cancel₀ ht0, one_smul, smul_comm]
    exact hy0 (by rw [ht, hx0, smul_zero])

end Split

section NotSplit



private theorem om9_seven_eq_one {K : Type} [Field K] [CharP K 2] : (7 : K) = 1 := by
  have := CharTwo.two_eq_zero (R := K)
  linear_combination 3 * this

private theorem om9_eq_zero_of_mem_fixed_perp {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V} (hx :
    OddOrderIsometry Q 7 a) {v : V} (hv : v ∈ fixedSpace a)
    (hperp : ∀ w ∈ fixedSpace a, QuadraticMap.polar Q v w = 0) : v = 0 := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have h1 : (⟨v, hv⟩ : fixedSpace a) = 0 := hWnd.1 ⟨v, hv⟩ fun w' => hperp w'.1 w'.2
  exact congrArg Subtype.val h1

private theorem om9_eigen_pow_seven {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 7 a) {z
    : V} {c : K} (hz : a z = c • z)
    (hz0 : z ≠ 0) : c ^ 7 = 1 := by
  have h : (a ^ 7) z = c ^ 7 • z := om9_pow_apply_of_eigen hz 7
  rw [hx.pow_eq_one] at h
  change z = _ at h
  have : (c ^ 7 - 1) • z = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)

private theorem om9_singular_of_eigen_ne_one {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V} (hx :
    OddOrderIsometry Q 7 a) {z : V} {c : K}
    (hz : a z = c • z) (hz0 : z ≠ 0) (hc1 : c ≠ 1) : Q z = 0 := by
  have hT : ∀ v, Q (a v) = Q v := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp hx.mem
  have hc7 := om9_eigen_pow_seven hx hz hz0
  have hc2 : c ^ 2 ≠ 1 := fun h2 => hc1 (by
    have : c ^ Nat.gcd 2 7 = 1 := pow_gcd_eq_one.mpr ⟨h2, hc7⟩
    simpa using this)
  exact om9_singular_of_eigen hT hz hc2

private theorem om9_not_splitFour {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 7 a) (hK : Nat.card K = 8)
    (hV : finrank K V = 8) (hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ¬ SplitFour (Q.comp (fixedSpace a).subtype) := by
  classical
  intro hsp
  set W := fixedSpace a with hW
  obtain ⟨h4, S, hS2, hS0⟩ := hsp
  have h7 : (7 : K) ≠ 0 := by rw [om9_seven_eq_one]; exact one_ne_zero
  have ha7 := hx.pow_eq_one
  set Y : Submodule K V := S.map W.subtype with hY
  have hY2 : finrank K Y = 2 := by rw [hY, Submodule.finrank_map_subtype_eq, hS2]
  have hY0 : ∀ u ∈ Y, Q u = 0 := by
    rintro _ ⟨s, hs, rfl⟩
    exact hS0 s hs
  have hYW : ∀ u ∈ Y, u ∈ W := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  set Φ : V →ₗ[K] W →ₗ[K] K := (QuadraticMap.polarBilin Q).compl₂ W.subtype with hΦ
  set N := LinearMap.ker Φ with hN
  have hmemN : ∀ v, v ∈ N ↔ ∀ w ∈ W, QuadraticMap.polar Q v w = 0 := by
    intro v
    rw [hN, LinearMap.mem_ker]
    constructor
    · intro h w hw
      exact LinearMap.congr_fun h ⟨w, hw⟩
    · intro h
      ext w
      exact h w.1 w.2
  have hN4 : 4 ≤ finrank K N := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [← hN] at h1
    have h2 : finrank K (LinearMap.range Φ) ≤ 4 := by
      refine (Submodule.finrank_le _).trans ?_
      rw [Module.finrank_linearMap, Module.finrank_self, h4]
    omega
  have hNa : ∀ v ∈ N, a v ∈ N := by
    intro v hv
    refine (hmemN _).mpr fun w hw => ?_
    have hw' : a.symm w = w := by
      rw [LinearEquiv.symm_apply_eq]
      exact (mem_fixedSpace.mp hw).symm
    rw [hx.polar_apply, hw']
    exact (hmemN v).mp hv w hw
  have hWN : ∀ v, v ∈ W → v ∈ N → v = 0 := fun v hvW hvN =>
    om9_eq_zero_of_mem_fixed_perp hx hvW ((hmemN v).mp hvN)
  have hNne : N ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hN4
    omega
  obtain ⟨x, hxN, hx0, l, hxl⟩ := om9_exists_eigen hK ha7 hNne hNa
  have hl1 : l ≠ 1 := by
    rintro rfl
    exact hx0 (hWN x (mem_fixedSpace.mpr (by rw [hxl, one_smul])) hxN)
  have hl7 := om9_eigen_pow_seven hx hxl hx0
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl7
  have hQx := om9_singular_of_eigen_ne_one hx hxl hx0 hl1
  set Ψ : V →ₗ[K] (W →ₗ[K] K) × K := Φ.prod (QuadraticMap.polarBilin Q x) with hΨ
  set M := LinearMap.ker Ψ with hM
  have hmemM : ∀ v, v ∈ M ↔ v ∈ N ∧ QuadraticMap.polar Q x v = 0 := by
    intro v
    rw [hM, LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero, hN, LinearMap.mem_ker]
    rfl
  have hM3 : 3 ≤ finrank K M := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [← hM] at h1
    have h2 : finrank K (LinearMap.range Ψ) ≤ 5 := by
      refine (Submodule.finrank_le _).trans ?_
      rw [Module.finrank_prod, Module.finrank_linearMap, Module.finrank_self, h4]
    omega
  have hxs : a.symm x = l⁻¹ • x := by
    rw [LinearEquiv.symm_apply_eq, map_smul, hxl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hMa : ∀ v ∈ M, a v ∈ M := by
    intro v hv
    obtain ⟨hvN, hxv⟩ := (hmemM v).mp hv
    refine (hmemM _).mpr ⟨hNa v hvN, ?_⟩
    rw [QuadraticMap.polar_comm, hx.polar_apply, hxs, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_comm, hxv, smul_zero]
  obtain ⟨y, hyM, hyx, c, hyc⟩ := om9_exists_second_eigen hK ha7 h7 (by omega) hMa hxl hl7
  have hy0 : y ≠ 0 := fun h => hyx 0 (by rw [h, zero_smul])
  obtain ⟨hyN, hxy⟩ := (hmemM y).mp hyM
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hy0 (hWN y (mem_fixedSpace.mpr (by rw [hyc, one_smul])) hyN)
  have hQy := om9_singular_of_eigen_ne_one hx hyc hy0 hc1
  set Z : Submodule K V := (K ∙ x) ⊔ (K ∙ y) with hZ
  have hZN : Z ≤ N := sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hxN)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hyN)
  have hxy0 : (K ∙ x) ⊓ (K ∙ y) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvx, hvy⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hvx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvy
    by_cases ht0 : t = 0
    · rw [ht0, zero_smul] at ht
      exact ht.symm
    · exfalso
      apply hyx (t⁻¹ * s)
      rw [mul_smul, ← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hZ2 : finrank K Z = 2 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ x) (K ∙ y)
    rw [hxy0, finrank_bot, finrank_span_singleton hx0, finrank_span_singleton hy0] at h1
    omega
  have hQZ : ∀ z ∈ Z, Q z = 0 := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [QuadraticMap.map_add Q (s • x) (t • y), QuadraticMap.map_smul, QuadraticMap.map_smul, hQx,
      hQy, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hxy]
    simp
  have hYZ : Y ⊓ Z = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvY, hvZ⟩
    exact hWN v (hYW v hvY) (hZN hvZ)
  have hU4 : finrank K ↥(Y ⊔ Z) = 4 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y Z
    rw [hYZ, finrank_bot, hY2, hZ2] at h1
    omega
  refine hplus ⟨Y ⊔ Z, by omega, fun v hv => ?_⟩
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [QuadraticMap.map_add Q u z, hY0 u hu, hQZ z hz, QuadraticMap.polar_comm,
    (hmemN z).mp (hZN hz) u (hYW u hu)]
  simp

end NotSplit


section Fixed



private theorem om9_exists_singular_common_eigen {K : Type} [Field K] [Finite K] [CharP K 2] {V :
    Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K]
    V} (hx : OddOrderIsometry Q 7 a) (hK : Nat.card K = 8)
    {A : Subgroup (V ≃ₗ[K] V)} (hA7 : ∀ g ∈ A, g ^ 7 = 1)
    (hAc : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {W : Submodule K V}
    (hW3 : 3 ≤ finrank K W) (hWA : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W) :
    ∃ e ∈ W, e ≠ 0 ∧ Q e = 0 ∧ ∀ g ∈ A, ∃ c : K, g e = c • e := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  by_cases htriv : ∀ g ∈ A, ∀ w ∈ W, g w = w
  · obtain ⟨e, heW, he0, hQe⟩ :=
      CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_any (Q := Q) hW3
    exact ⟨e, heW, he0, hQe, fun g hg => ⟨1, by rw [one_smul]; exact htriv g hg e heW⟩⟩
  push Not at htriv
  obtain ⟨g, hg, w, hw, hgw⟩ := htriv
  set f : V →ₗ[K] V := g.toLinearMap - LinearMap.id with hf
  have hfa : ∀ v, f v = g v - v := fun v => rfl
  set M₂ := W.map f with hM₂
  have hM₂0 : M₂ ≠ ⊥ := fun h => by
    have : f w ∈ M₂ := Submodule.mem_map_of_mem hw
    rw [h, Submodule.mem_bot, hfa, sub_eq_zero] at this
    exact hgw this
  set S := (Set.toFinite (A : Set (V ≃ₗ[K] V))).toFinset with hS
  have hSm : ∀ g, g ∈ S ↔ g ∈ A := fun g => Set.Finite.mem_toFinset _
  obtain ⟨e, heM, he0, heA⟩ := om9_exists_common_eigen hK S
    (fun g hg => hA7 g ((hSm g).mp hg))
    (fun g hg g' hg' => hAc g ((hSm g).mp hg) g' ((hSm g').mp hg')) hM₂0
    (by
      rintro g' hg' _ ⟨m, hm, rfl⟩
      refine ⟨g' m, hWA g' ((hSm g').mp hg') m hm, ?_⟩
      have hc := hAc g hg g' ((hSm g').mp hg')
      rw [hfa, hfa, map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hc])
  obtain ⟨m, hmW, rfl⟩ := heM
  have heW : f m ∈ W := by rw [hfa]; exact W.sub_mem (hWA g hg m hmW) hmW
  obtain ⟨c, hc⟩ := heA g ((hSm g).mpr hg)
  have hgx : OddOrderIsometry Q 7 g := ⟨hAO hg, hA7 g hg, hx.cast_ne_zero, hx.regular⟩
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply he0
    refine om9_jordan_eq_zero (hA7 g hg) (by rw [om9_seven_eq_one]; exact one_ne_zero) (one_pow 7)
      hc (m := m) ?_
    rw [one_smul, hfa]
    abel
  exact ⟨f m, heW, he0, om9_singular_of_eigen_ne_one hgx hc he0 hc1,
    fun g' hg' => heA g' ((hSm g').mpr hg')⟩

private theorem om9_fixed_eichler {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 7 a) (hK : Nat.card K = 8)
    (hV : finrank K V = 8) (hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {A : Subgroup (V ≃ₗ[K] V)} (hA7 : ∀ g ∈ A, g ^ 7 = 1)
    (hAc : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g) (haA : ∀ g ∈ A, g * a = a * g)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a (X - 1)) :
    ∃ e w : V, (∀ g ∈ A, ∃ c : K, g e = c • e) ∧ QuadraticMap.polar Q e w = 0 ∧
      eichler Q e w ∈ L ∧ eichler Q e w ≠ 1 := by
  classical
  set F := supportedBlock Q a (X - 1) with hF
  set W := fixedSpace a with hW
  set R := Q.comp W.subtype with hR
  set OW := TauCeti.QuadraticMap.orthogonalGroup R with hOW
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set T := (L.subgroupOf F).map ρ with hT
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hLF).symm.trans
        ((L.subgroupOf F).equivMapOfInjective ρ hρinj)) hLq
  have hTs : CFSG.Assembly.IsSubnormal T OW := by
    have h1 : CFSG.Assembly.IsSubnormal L F :=
      ggSubnormal_mono hL.2.1 hLF (supportedBlock_le_isometryCentralizer _)
    have h2 := ggSubnormal_comap F.subtype h1
    rw [show F.comap F.subtype = ⊤ from Subgroup.subgroupOf_self F] at h2
    have h3 := ggSubnormal_map ρ h2
    rwa [← MonoidHom.range_eq_map, hρ, range_fixRho] at h3
  have hmemT : ∀ u (hu : u ∈ F), ρ ⟨u, hu⟩ ∈ T → u ∈ L := by
    intro u hu h
    obtain ⟨y, hy, hyu⟩ := h
    have := hρinj hyu
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  obtain ⟨h4, ⟨-, hTc⟩ | ⟨hsp, -⟩⟩ := structure_of_isSubnormal hRnd hTq hTs
  swap
  · exact absurd hsp (om9_not_splitFour hx hK hV hplus)
  have hWA : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W := fun g hg w hw => by
    rw [hW, mem_fixedSpace] at hw ⊢
    rw [← LinearEquiv.mul_apply, ← haA g hg, LinearEquiv.mul_apply, hw]
  have hW4 : 4 ≤ finrank K W := h4
  obtain ⟨e, heW, he0, hQe, heA⟩ :=
    om9_exists_singular_common_eigen hx hK hA7 hAc hAO (by omega : 3 ≤ finrank K W) hWA
  obtain ⟨y, hyW, hy⟩ : ∃ y ∈ W, QuadraticMap.polar Q e y ≠ 0 := by
    by_contra H
    push Not at H
    exact he0 (om9_eq_zero_of_mem_fixed_perp hx heW H)
  obtain ⟨y', hy'W, hey'⟩ : ∃ y' ∈ W, QuadraticMap.polar Q e y' = 1 :=
    ⟨_, W.smul_mem (QuadraticMap.polar Q e y)⁻¹ hyW, by
      rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  obtain ⟨f, hfW, hQf, hef⟩ : ∃ f ∈ W, Q f = 0 ∧ QuadraticMap.polar Q e f = 1 := by
    refine ⟨y' + Q y' • e, W.add_mem hy'W (W.smul_mem _ heW), ?_, ?_⟩
    · rw [QuadraticMap.map_add Q y' (Q y' • e), QuadraticMap.map_smul, hQe,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hey']
      simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
      exact CharTwo.add_self_eq_zero _
    · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQe, smul_zero, add_zero, hey']
  obtain ⟨w, hwW, hw0, hew, hfw⟩ :=
    om9_exists_mem_ne_zero_polar_eq_zero₂ (Q := Q) (Y := W) (by omega) e f
  have hT : ∀ v, Q (a v) = Q v := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp hx.mem
  obtain ⟨ζ, hζ⟩ := om9_exists_zeta hK
  have hζ1 : (ζ : K) ≠ 1 := fun h => by
    have := hζ
    rw [show ζ = 1 from Units.ext h, orderOf_one] at this
    norm_num at this
  refine ⟨e, w, heA, hew, ?_, ?_⟩
  · set E := eichler Q e w with hE
    have hae : a e = e := mem_fixedSpace.mp heW
    have haw : a w = w := mem_fixedSpace.mp hwW
    have hiso : ∀ v, Q (E v) = Q v :=
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp (eichler_mem_orthogonalGroup Q e w)
    have hconj : a * E * a⁻¹ = E := by rw [hE, eichler_conj hx.mem, hae, haw]
    have hcomm : ∀ v, E (a v) = a (E v) := fun v => by
      have : a * E = E * a := calc
        a * E = (a * E * a⁻¹) * a := by group
        _ = E * a := by rw [hconj]
      rw [← LinearEquiv.mul_apply, ← this, LinearEquiv.mul_apply]
    have hEF : E ∈ F := by
      refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨hiso, hcomm⟩, ?_⟩
      rw [fixes_othersSpace_iff]
      intro l hl hlh _ v hv
      obtain ⟨m, -, rfl⟩ := omf_exists_eq_X_sub_C hx (by norm_num) hζ hl
      have hv' := om9_eigen_of_mem_primaryComponent hv
      have hl1 : (ζ : K) ^ m ≠ 1 := fun h => hlh (by rw [h, C_1])
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · exact om9_polar_eq_zero_of_eigen hT hv' (show a e = (1 : K) • e by rw [one_smul, hae])
          (by rw [mul_one]; exact hl1)
      · exact om9_polar_eq_zero_of_eigen hT hv' (show a w = (1 : K) • w by rw [one_smul, haw])
          (by rw [mul_one]; exact hl1)
    have hρE : ρ ⟨E, hEF⟩ = eichler R ⟨e, heW⟩ ⟨w, hwW⟩ := by
      have hRe : R ⟨e, heW⟩ = 0 := hQe
      have hRew : QuadraticMap.polar R ⟨e, heW⟩ ⟨w, hwW⟩ = 0 := hew
      refine LinearEquiv.ext fun z => Subtype.ext ?_
      rw [coe_fixRho, eichler_apply hRe hRew]
      change eichler Q e w (z : V) = _
      rw [eichler_apply hQe hew]
      rfl
    refine hmemT E hEF ?_
    rw [hρE, hTc]
    let P : HypPair R := ⟨⟨e, heW⟩, ⟨f, hfW⟩, hQe, hQf, hef⟩
    exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup ζ.ne_zero hζ1 P
      (HypPair.mem_perp.mpr ⟨hew, hfw⟩)
  · refine om9_eichler_ne_one hQe hew (y := f)
      (by rw [QuadraticMap.polar_comm, hef]; exact one_ne_zero)
      fun t ht => hw0 ?_
    have h1 : QuadraticMap.polar Q f w = t := by
      rw [ht, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hef, smul_eq_mul, mul_one]
    rw [hfw] at h1
    rw [ht, ← h1, zero_smul]

end Fixed

section Main

open CFSG.ClassicalGroups.Orthogonal


private theorem om9_twoSubgroup_frame {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V
    ≃ₗ[K] V)} {r : ℕ} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q 7 A r) (hK : Nat.card K = 8)
    (hV : finrank K V = 8) (hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {β : Fin r → ZMod 7} {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {F.ι (ofAdd β)})) :
    ∃ T : Subgroup (V ≃ₗ[K] V), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[K] V)) := by
  classical
  have hp7 : Nat.Prime 7 := by norm_num
  set a := F.ι (ofAdd β) with ha
  have hx : OddOrderIsometry Q 7 a := F.oddOrderIsometry hQ (by norm_num) hp7 hAΩ _
  have hAι : ∀ g ∈ A, ∃ s, F.ι s = g := fun g hg => by
    have : g ∈ F.ι.range := by rw [F.range]; exact hg
    exact this
  have hA7 : ∀ g ∈ A, g ^ 7 = 1 := fun g hg => by
    obtain ⟨s, rfl⟩ := hAι g hg
    exact F.pow_p s
  have hAc : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g := fun g hg g' hg' => by
    obtain ⟨s, rfl⟩ := hAι g hg
    obtain ⟨t, rfl⟩ := hAι g' hg'
    rw [← map_mul, ← map_mul, mul_comm]
  have haA : ∀ g ∈ A, g * a = a * g := fun g hg => hAc g hg a (F.mem _)
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    orthDerived_le_orthogonalGroup (hAΩ hg)
  have hAC : ∀ g ∈ A, g ∈ isometryCentralizer Q a := fun g hg =>
    Subgroup.mem_inf.mpr ⟨hAO hg, Subgroup.mem_centralizer_singleton_iff.mpr (haA g hg)⟩
  have hL := isComponentOf_isometryCentralizer hJ
  obtain ⟨-, -, hn, -⟩ := exists_block_of_isComponentOf hx hp7 (by norm_num) hJ
  have hJA : ∀ g ∈ A, ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun g hg x hx' =>
    hn g (hAC g hg) (hA7 g hg) x hx'
  obtain ⟨h, hh, hLF⟩ := exists_le_supportedBlock hx hL
  by_cases hX : h = X - 1
  · subst hX
    obtain ⟨e, w, heA, hew, hEJ, hE1⟩ :=
      om9_fixed_eichler hx hK hV hplus hA7 hAc haA hAO hL hLF
    exact om9_exists_twoSubgroup_of_eichler hJA hAO heA hew hEJ hE1
  · have hJeq := free_case hx hp7 (by norm_num) hh hX hL hLF
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hLq : CFSG.IsQuasisimple J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hL.2.2
    have hm : 2 ≤ primaryMultiplicity a.toLinearMap h := by
      by_contra hm
      have hpos : 1 ≤ primaryMultiplicity a.toLinearMap h := by
        have hne : primaryComponent a.toLinearMap h ≠ ⊥ :=
          primaryComponent_ne_bot hx.squarefree_minpoly hh
        have : Nontrivial (primaryComponent a.toLinearMap h) :=
          Submodule.nontrivial_iff_ne_bot.mpr hne
        exact Module.finrank_pos
      have h1 := hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega)
      rw [← hJeq] at h1
      obtain ⟨u, u', huu⟩ := exists_mul_ne_of_isQuasisimple hLq
      have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 ▸ u.2))
      have hu' : u' = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 ▸ u'.2))
      exact huu (by rw [hu, hu'])
    obtain ⟨e, w, heA, hew, hEJ, hE1⟩ := om9_class_eichler hx hK hA7 hAc haA hh hX hm
    rw [← hJeq] at hEJ
    exact om9_exists_twoSubgroup_of_eichler hJA hAO heA hew hEJ hE1

end Main


theorem omComp_twoSubgroup {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hAΩ : A ≤ omΩ)
    (F : SevOm.Frame omQ 7 A 3) {β : Fin 3 → ZMod 7} (hβ0 : β ≠ 0)
    {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (hJ : IsComponentOf J (omΩ ⊓ Subgroup.centralizer {F.ι (ofAdd β)})) :
    ∃ T : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      A ≤ Subgroup.normalizer (T : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) := by
  have hQ : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2 (by norm_num)
      (minusCoeffs_irr 2 3)).1
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  have hV : finrank (GaloisField 2 3) OmV = 8 := by
    simp only [OmV, Module.finrank_fin_fun]
  have hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType omQ := fun h =>
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (by norm_num)
      (minusCoeffs_irr 2 3)
      (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry 4
          (GaloisField 2 3) (by norm_num) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2).symm h)
  exact om9_twoSubgroup_frame hQ hAΩ F hK hV hplus hJ

end A8Coord

end CFSG.StandardType

end
