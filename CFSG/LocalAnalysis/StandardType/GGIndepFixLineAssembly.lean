module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineFamilyDefs
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineSl
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineMon
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineExc
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6ka_permMap_monomial {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n)) :
    ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ (ZS.permMap p f σ) (f i) = c • f j :=
  fun i => ⟨σ i, 1, one_ne_zero, by simp [ZS.permMap]⟩

private lemma l6ka_diagMap_apply {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ)
    (i : Fin n) : (ZS.diagMap p f d) (f i) = (d i : ZMod p) • f i := by
  apply f.equivFun.injective
  simp only [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_smul]
  ext j
  simp only [LinearEquiv.piCongrRight_apply]
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self]
  by_cases hji : j = i
  · subst hji; simp [LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul]
  · simp [Finsupp.single_eq_of_ne hji]

private lemma l6ka_diagMap_monomial {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) :
    ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ (ZS.diagMap p f d) (f i) = c • f j :=
  fun i => ⟨i, (d i : ZMod p), Units.ne_zero (d i), by rw [l6ka_diagMap_apply]⟩

private lemma l6ka_monomial_mul {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (a b : U ≃ₗ[ZMod p] U)
    (ha : ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j)
    (hb : ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ b (f i) = c • f j) :
    ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ (a * b) (f i) = c • f j := by
  intro i
  obtain ⟨j, c, hc, hbc⟩ := hb i
  obtain ⟨k, c', hc', hac⟩ := ha j
  refine ⟨k, c * c', mul_ne_zero hc hc', ?_⟩
  rw [LinearEquiv.mul_apply, hbc, map_smul, hac, smul_smul]

private lemma l6ka_monomial_symm {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (a : U ≃ₗ[ZMod p] U)
    (ha : ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j) :
    ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a.symm (f i) = c • f j := by
  classical
  let J : Fin n → Fin n := fun i => (ha i).choose
  have hJspec : ∀ i, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f (J i) := fun i => (ha i).choose_spec
  let C : Fin n → ZMod p := fun i => (hJspec i).choose
  have hC : ∀ i, C i ≠ 0 := fun i => (hJspec i).choose_spec.1
  have hJ : ∀ i, a (f i) = C i • f (J i) := fun i => (hJspec i).choose_spec.2
  have hJinj : Function.Injective J := by
    intro i i' hij
    by_contra hne
    have hsym : ∀ k, a.symm (f (J k)) = (C k)⁻¹ • f k := by
      intro k
      have hf : f (J k) = (C k)⁻¹ • a (f k) := by
        rw [hJ k, smul_smul, inv_mul_cancel₀ (hC k), one_smul]
      rw [hf, map_smul, LinearEquiv.symm_apply_apply]
    have heq : (C i)⁻¹ • f i = (C i')⁻¹ • f i' := by
      rw [← hsym i, ← hsym i', hij]
    have hcoord := congrArg (fun v => f.repr v i) heq
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at hcoord
    rw [Finsupp.single_eq_of_ne hne, mul_zero] at hcoord
    exact inv_ne_zero (hC i) hcoord
  have hJsurj : Function.Surjective J := Finite.injective_iff_surjective.mp hJinj
  intro i
  obtain ⟨k, hk⟩ := hJsurj i
  refine ⟨k, (C k)⁻¹, inv_ne_zero (hC k), ?_⟩
  have hf : f i = (C k)⁻¹ • a (f k) := by
    rw [hJ k, hk, smul_smul, inv_mul_cancel₀ (hC k), one_smul]
  rw [hf, map_smul, LinearEquiv.symm_apply_apply]

private lemma l6ka_monomial_closure {p n : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin n) (ZMod p) U) (S : Set (U ≃ₗ[ZMod p] U))
    (hgen : ∀ a ∈ S, ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j) :
    ∀ a ∈ Subgroup.closure S, ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j := by
  let M : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {a | ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j}
      one_mem' := fun i => ⟨i, 1, one_ne_zero, by simp⟩
      mul_mem' := fun ha hb => l6ka_monomial_mul f _ _ ha hb
      inv_mem' := fun ha => l6ka_monomial_symm f _ ha }
  intro a ha
  exact (Subgroup.closure_le M).mpr (fun x hx => hgen x hx) ha

private lemma l6ka_isom_closure {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (Q0 : QuadraticForm (ZMod p) U) (c : ZMod p) :
    ∀ g ∈ Subgroup.closure (ZS.ClassRefl p Q0 c), ZS.IsIsom p Q0 g := by
  let I : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ZS.IsIsom p Q0 g}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        rw [LinearEquiv.mul_apply, ha (b v), hb v]
      inv_mem' := by
        intro a ha
        show ZS.IsIsom p Q0 a.symm
        intro v
        have h := ha (a.symm v)
        rw [LinearEquiv.apply_symm_apply] at h
        exact h.symm }
  intro g hg
  exact (Subgroup.closure_le I).mpr (fun t ht => ht.2.1) hg

theorem ggIndepFixLineLin_of_families (hZS : ZS.UseInput) (hW : GGFixLineNotWeyl) :
    GGIndepFixLineLin := by
  intro p N _ hp2 hN5 hpN V _ _ hV h α r hind hpair hr ι _ s hs hconn x hx0 hfixH hxnot hnt
  let S : GGFixLineHyp p N h α r s x :=
    { odd := hp2, five_le := hN5, dvd := hpN, dim_le := hV, finite_family := inferInstance,
      indep := hind, pair := hpair, r_form := hr, s_refl := hs, conn := hconn,
      x_ne := hx0, fix_H := hfixH, x_not_fix := hxnot, no_transvection := hnt }
  have : Module.Finite (ZMod p) V := ggFixLine_finite s hs hfixH
  obtain ⟨hb1, hb2⟩ := ggFixLine_fix_bounds hp2 hN5 hpN (V := V) hV hind hpair hr
  by_contra hne
  have hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2 := by omega
  have : Module.Finite (ZMod p) ↥(ggFixLineT r s) :=
    FiniteDimensional.finiteDimensional_submodule (ggFixLineT r s)
  have hTprops := ggFixLine_T_props S
  have h3 : 3 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    have h := hTprops.2.2.1
    omega
  have hfam : ZS.Family p (ggFixLineQ S) :=
    hZS p ↥(ggFixLineT r s) (ggFixLineQ S) hp2 h3 (ggFixLine_Q_reflGen S) (ggFixLine_Q_absIrred S)
  rcases hfam with hlw | hslpm | ⟨Q0, hnd, hQeq⟩ | ⟨Q0, c, hnd, _hc, hcl⟩
    | ⟨f, i₀, i₁, ζ, _m, _hi, _hm, _hζ, hQeq⟩ | ⟨f, i₀, i₁, ζ, _m, _hi, _hm, _hζ, hQeq⟩
    | ⟨k, hadm, hdim, hcard, hcen, _hdmax, _honeclass, _hmodel⟩
    | ⟨hp5, hdim4, _hcard, _hneg, _hdmax, _honeclass⟩
  · exact (hW p N V ι h α r s x S hF2) hlw
  · exact ggFixLine_not_slpm S hslpm
  · exact ggFixLine_not_orth S hF2 Q0 hnd (fun g hg => (hQeq g).mp hg)
  · exact ggFixLine_not_orth S hF2 Q0 hnd (fun g hg =>
      l6ka_isom_closure Q0 c g (by rwa [hcl] at hg))
  · have hmon : ∀ a ∈ ggFixLineQ S, ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j := by
      have hgen : ∀ a ∈ (Set.range (ZS.permMap p f) ∪ {ZS.diagMap p f (ZS.pairUnit p i₀ i₁ ζ)}),
          ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j := by
        intro a ha
        rcases ha with ⟨σ, rfl⟩ | ha
        · exact l6ka_permMap_monomial f σ
        · rw [Set.mem_singleton_iff] at ha
          subst ha
          exact l6ka_diagMap_monomial f (ZS.pairUnit p i₀ i₁ ζ)
      rw [hQeq]
      change ∀ a ∈ Subgroup.closure (Set.range (ZS.permMap p f) ∪
        {ZS.diagMap p f (ZS.pairUnit p i₀ i₁ ζ)}), ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j
      exact l6ka_monomial_closure f _ hgen
    exact ggFixLine_not_monomial S hF2 f hmon
  · have hmon : ∀ a ∈ ggFixLineQ S, ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j := by
      have hgen : ∀ a ∈ (Set.range (ZS.permMap p f) ∪
          {ZS.diagMap p f (fun i => if i = i₀ then -1 else 1),
            ZS.diagMap p f (ZS.pairUnit p i₀ i₁ ζ)}),
          ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j := by
        intro a ha
        rcases ha with ⟨σ, rfl⟩ | ha
        · exact l6ka_permMap_monomial f σ
        · rw [Set.mem_insert_iff] at ha
          rcases ha with ha | ha
          · subst ha; exact l6ka_diagMap_monomial f _
          · rw [Set.mem_singleton_iff] at ha
            subst ha
            exact l6ka_diagMap_monomial f (ZS.pairUnit p i₀ i₁ ζ)
      rw [hQeq]
      change ∀ a ∈ Subgroup.closure (Set.range (ZS.permMap p f) ∪
        {ZS.diagMap p f (fun i => if i = i₀ then -1 else 1),
         ZS.diagMap p f (ZS.pairUnit p i₀ i₁ ζ)}),
        ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j
      exact l6ka_monomial_closure f _ hgen
    exact ggFixLine_not_monomial S hF2 f hmon
  · exact ggFixLine_not_exc S hF2 k hadm hdim hcard hcen
  ·
    have hN : N = 5 := by
      have := hTprops.2.2.1
      have := hTprops.2.2.2
      omega
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp (hN ▸ hpN))

end CFSG.StandardType

end
