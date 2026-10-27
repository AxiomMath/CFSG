module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel

public section

namespace CFSG.RankThree.PartOne.KCUnitaryMixing

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary

section Poly

variable {K : Type*} [Field K]

theorem exists_pow_dvd_comp {p : ℕ} (hp : p.Prime) {f g : K[X]} (hfm : f.Monic)
    (hf : Irreducible f) (hfd : f ∣ X ^ p - 1) (hf1 : f ≠ X - C 1) (hgm : g.Monic)
    (hg : Irreducible g) (hgd : g ∣ X ^ p - 1) (hg1 : g ≠ X - C 1) :
    ∃ j : ℕ, 0 < j ∧ j < p ∧ g ∣ f.comp (X ^ j) := by
  classical
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set ω : AdjoinRoot g := AdjoinRoot.root g with hωdef
  have hωp : ω ^ p = 1 := by
    have h1 : AdjoinRoot.mk g (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hgd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact h1
  have hω1 : ω ≠ 1 := by
    intro h1
    have h2 : AdjoinRoot.mk g (X - C 1) = 0 := by
      rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, map_one,
        ← hωdef, h1, sub_self]
    exact hg1 (eq_of_monic_of_associated hgm (monic_X_sub_C 1)
      (hg.associated_of_dvd (irreducible_X_sub_C 1) (AdjoinRoot.mk_eq_zero.mp h2)))
  have hprim : IsPrimitiveRoot ω p := by
    have hord : orderOf ω = p := orderOf_eq_prime hωp hω1
    rw [← hord]
    exact IsPrimitiveRoot.orderOf ω
  set φ := algebraMap K (AdjoinRoot g) with hφ
  have hprod := Polynomial.X_pow_sub_one_eq_prod hp.pos hprim
  have hfmap : f.map φ ∣ ∏ ζ ∈ nthRootsFinset p (1 : AdjoinRoot g), (X - C ζ) := by
    rw [← hprod]
    have := Polynomial.map_dvd φ hfd
    simpa using this
  have hq1 : ¬ IsUnit (f.map φ) := by
    intro hu
    have h1 : f.map φ = 1 := (hfm.map φ).isUnit_iff.mp hu
    have h2 : f = 1 := Polynomial.map_injective φ φ.injective (by rw [h1, Polynomial.map_one])
    exact hf.not_isUnit (h2 ▸ isUnit_one)
  obtain ⟨i, hi, hidvd⟩ := WfDvdMonoid.exists_irreducible_factor hq1
    (Polynomial.map_monic_ne_zero hfm)
  obtain ⟨ζ, hζmem, hζ⟩ := (hi.prime.dvd_finsetProd_iff _).mp (hidvd.trans hfmap)
  have hroot : (f.map φ).IsRoot ζ := by
    refine dvd_iff_isRoot.mp ?_
    exact ((hi.associated_of_dvd (irreducible_X_sub_C ζ) hζ).symm.dvd).trans hidvd
  have hζp : ζ ^ p = 1 := (mem_nthRootsFinset hp.pos (1 : AdjoinRoot g)).mp hζmem
  obtain ⟨j, hjp, hj⟩ := hprim.eq_pow_of_pow_eq_one hζp
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hj
      rw [← hj] at hroot
      have h1 : f.IsRoot 1 := by
        rw [Polynomial.IsRoot.def] at hroot ⊢
        rw [Polynomial.eval_map] at hroot
        have h2 : Polynomial.eval₂ φ (φ 1) f = φ (Polynomial.eval 1 f) :=
          Polynomial.eval₂_at_apply φ 1
        rw [map_one, hroot] at h2
        exact φ.injective (by rw [← h2, map_zero])
      exact hf1 (eq_of_monic_of_associated hfm (monic_X_sub_C 1)
        ((irreducible_X_sub_C 1).associated_of_dvd hf (dvd_iff_isRoot.mpr h1)).symm)
    · exact h0
  refine ⟨j, hj0, hjp, AdjoinRoot.mk_eq_zero.mp ?_⟩
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_comp, aeval_X_pow, hj, Polynomial.aeval_def,
    ← Polynomial.eval_map]
  exact hroot

end Poly

section Linear

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem pow_apply_mem {T : Module.End K V} {S : Submodule K V} (hS : ∀ s ∈ S, T s ∈ S) (n : ℕ)
    {s : V} (hs : s ∈ S) : (T ^ n) s ∈ S := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hS _ ih

omit [FiniteDimensional K V] in
theorem aeval_apply_mem {T : Module.End K V} {S : Submodule K V} (hS : ∀ s ∈ S, T s ∈ S)
    (q : K[X]) {s : V} (hs : s ∈ S) : aeval T q s ∈ S := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial]
    change (algebraMap K (Module.End K V) c) ((T ^ n) s) ∈ S
    rw [Module.algebraMap_end_apply]
    exact S.smul_mem c (pow_apply_mem hS n hs)

omit [FiniteDimensional K V] in
theorem aeval_apply_eq_of_agree {T₁ T₂ : Module.End K V} {S : Submodule K V}
    (h₂ : ∀ s ∈ S, T₂ s ∈ S) (hag : ∀ s ∈ S, T₁ s = T₂ s)
    (q : K[X]) {s : V} (hs : s ∈ S) : aeval T₁ q s = aeval T₂ q s := by
  have hpow : ∀ n : ℕ, ∀ s ∈ S, (T₁ ^ n) s = (T₂ ^ n) s := by
    intro n
    induction n with
    | zero => intro s _; rfl
    | succ n ih =>
      intro s hs
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih s hs,
        hag _ (pow_apply_mem h₂ n hs)]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial]
    change (algebraMap K (Module.End K V) c) ((T₁ ^ n) s) =
      (algebraMap K (Module.End K V) c) ((T₂ ^ n) s)
    rw [hpow n s hs]

theorem exists_primaryFactor_mem {T : Module.End K V} (hsq : Squarefree (minpoly K T))
    {S : Submodule K V} (hS : ∀ s ∈ S, T s ∈ S) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ a ∈ primaryFactors T, ∃ w ∈ S, w ∈ primaryComponent T a ∧ w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsum := LinearMap.congr_fun (sum_primaryProjection hsq) v
  rw [LinearMap.sum_apply] at hsum
  have hz : ∀ a ∈ primaryFactors T, primaryProjection T a v = 0 := by
    intro a ha
    by_contra hne
    exact hne (hcon a ha (primaryProjection T a v) (aeval_apply_mem hS _ hv)
      (primaryProjection_mem hsq ha v))
  rw [Finset.sum_eq_zero hz] at hsum
  exact hv0 (by simpa using hsum.symm)

theorem mem_primaryFactors_of_apply_eq_zero {T : Module.End K V} {a : K[X]} (ha : Irreducible a)
    (ham : a.Monic) {v : V} (hv : aeval T a v = 0) (hv0 : v ≠ 0) : a ∈ primaryFactors T := by
  refine mem_primaryFactors.mpr ⟨ha, ham, ?_⟩
  by_contra hnd
  obtain ⟨u, r, hur⟩ := ha.coprime_iff_not_dvd.mpr hnd
  have h1 : aeval T (u * a + r * minpoly K T) v = v := by
    rw [hur, map_one]
    rfl
  rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, add_zero, Module.End.mul_apply, hv,
    map_zero] at h1
  exact hv0 h1.symm

omit [FiniteDimensional K V] in
theorem linearIndependent_pair_of_disjoint {T : Module.End K V} {a : K[X]} [Fact (Irreducible a)]
    {S₁ S₂ : Submodule K V} (hS₁ : ∀ s ∈ S₁, T s ∈ S₁) (hS₂ : ∀ s ∈ S₂, T s ∈ S₂)
    (hdisj : Disjoint S₁ S₂) {v w : V} (hv : v ∈ S₁) (hw : w ∈ S₂)
    (hva : v ∈ primaryComponent T a) (hwa : w ∈ primaryComponent T a) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) :
    LinearIndependent (AdjoinRoot a) ![(⟨v, hva⟩ : primaryComponent T a), ⟨w, hwa⟩] := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ hc
  obtain ⟨r₁, rfl⟩ := AdjoinRoot.mk_surjective c₁
  obtain ⟨r₂, rfl⟩ := AdjoinRoot.mk_surjective c₂
  have hc' := congrArg Subtype.val hc
  simp only [coe_mk_smul_primaryComponent, Submodule.coe_add, Submodule.coe_zero] at hc'
  have hm₁ : aeval T r₁ v ∈ S₁ := aeval_apply_mem hS₁ r₁ hv
  have hm₂ : aeval T r₂ w ∈ S₂ := aeval_apply_mem hS₂ r₂ hw
  have hneg : aeval T r₁ v = -(aeval T r₂ w) := eq_neg_of_add_eq_zero_left hc'
  have h0 : aeval T r₁ v = 0 := by
    have hmem : aeval T r₁ v ∈ S₁ ⊓ S₂ := ⟨hm₁, by rw [hneg]; exact S₂.neg_mem hm₂⟩
    rw [hdisj.eq_bot] at hmem
    exact (Submodule.mem_bot K).mp hmem
  have h0' : aeval T r₂ w = 0 := by
    rw [h0, zero_add] at hc'
    exact hc'
  refine ⟨?_, ?_⟩
  · have : (AdjoinRoot.mk a r₁ • (⟨v, hva⟩ : primaryComponent T a)) = 0 :=
      Subtype.ext (by simpa using h0)
    exact (smul_eq_zero.mp this).resolve_right (fun h => hv0 (congrArg Subtype.val h))
  · have : (AdjoinRoot.mk a r₂ • (⟨w, hwa⟩ : primaryComponent T a)) = 0 :=
      Subtype.ext (by simpa using h0')
    exact (smul_eq_zero.mp this).resolve_right (fun h => hw0 (congrArg Subtype.val h))

theorem two_le_primaryMultiplicity {T : Module.End K V} {a : K[X]} [Fact (Irreducible a)]
    {S₁ S₂ : Submodule K V} (hS₁ : ∀ s ∈ S₁, T s ∈ S₁) (hS₂ : ∀ s ∈ S₂, T s ∈ S₂)
    (hdisj : Disjoint S₁ S₂) {v w : V} (hv : v ∈ S₁) (hw : w ∈ S₂)
    (hva : v ∈ primaryComponent T a) (hwa : w ∈ primaryComponent T a) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    2 ≤ primaryMultiplicity T a := by
  have hind := linearIndependent_pair_of_disjoint (a := a) hS₁ hS₂ hdisj hv hw hva hwa hv0 hw0
  have := hind.fintype_card_le_finrank
  simpa using this

end Linear

section SelfDual

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem natDegree_ne_one_of_selfDual {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ ℓ ^ f + 1)
    {a : K[X]} (ham : a.Monic) (hd : a ∣ X ^ p - 1) (ha1 : a ≠ X - C 1)
    (hself : KCUnitary.dualPoly h.bar a = a) : a.natDegree ≠ 1 := by
  intro hdeg
  have hc1 : a.coeff 1 = 1 := by
    have := ham.coeff_natDegree
    rwa [hdeg] at this
  have haeq : a = X - C (-a.coeff 0) := by
    have := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
    rw [hc1] at this
    rw [map_neg, sub_neg_eq_add]
    simpa using this
  set μ : K := -a.coeff 0 with hμ
  have hroot : (X ^ p - 1 : K[X]).IsRoot μ := dvd_iff_isRoot.mp (by rw [← haeq]; exact hd)
  have hμp : μ ^ p = 1 := by
    simpa [Polynomial.IsRoot.def, sub_eq_zero] using hroot
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply ha1
    rw [haeq, h1]
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hμp
    exact zero_ne_one hμp
  have hbar0 : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
  rw [haeq, KCUnitaryBlock.dualPoly_X_sub_C hbar0] at hself
  have hinv : (h.bar μ)⁻¹ = μ := by
    have := congrArg (fun q : K[X] => q.coeff 0) hself
    simpa using this
  have hnorm : μ * h.bar μ = 1 := by
    calc μ * h.bar μ = (h.bar μ)⁻¹ * h.bar μ := by rw [hinv]
      _ = 1 := inv_mul_cancel₀ hbar0
  have hpow : μ ^ (ℓ ^ f + 1) = 1 := by
    rw [← h.norm_eq_pow]
    exact hnorm
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf μ = p := orderOf_eq_prime hμp hμ1
  exact hpq (hord ▸ orderOf_dvd_of_pow_eq_one hpow)

end SelfDual

section Plane

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KCUnitaryScalar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem act_planeRep_eq_xlin (t : ↥Ahat) : act (planeRep h n Ahat) t = xlin h n t.1 := rfl

theorem lineSpace_stable (S : PlaneSetup h n p Ahat) (y : ↥Ahat) {L : Subgroup ↥Ahat}
    {s : Fin n → K} (hs : s ∈ lineSpace (planeRep h n Ahat) (idForm h n) L) :
    act (planeRep h n Ahat) y s ∈ lineSpace (planeRep h n Ahat) (idForm h n) L := by
  set ρ := planeRep h n Ahat with hρ
  have hcomm : ∀ z : ↥Ahat, z * y = y * z := fun z => Subtype.ext (S.commute z.2 y.2)
  refine ⟨fun z hz => ?_, fun u hu => ?_⟩
  · have h1 : act ρ z s = s := hs.1 z hz
    rw [← Module.End.mul_apply, ← act_mul, hcomm z, act_mul, Module.End.mul_apply, h1]
  · have hu' : act ρ y⁻¹ u = u := hu y⁻¹ (Subgroup.mem_top _)
    have h1 : idForm h n (act ρ y (act ρ y⁻¹ u)) (act ρ y s) = idForm h n (act ρ y⁻¹ u) s :=
      planeRep_mem Ahat y _ _
    rw [act_inv_apply, hu'] at h1
    rw [h1]
    exact hs.2 u hu

theorem disjoint_lineSpace (hdec : PlaneKernelDecomposition h n p Ahat) {L M : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hM : Nat.card M = p) (hLM : L ≠ M) :
    Disjoint (lineSpace (planeRep h n Ahat) (idForm h n) L)
      (lineSpace (planeRep h n Ahat) (idForm h n) M) := by
  rw [Submodule.disjoint_def]
  intro x hxL hxM
  have := hdec.nondegenerate_line L hL ⟨x, hxL⟩ (fun y => by
    rw [LinearMap.domRestrict₁₂_apply]
    exact hdec.orthogonal_line_line M L hM hL hLM.symm x hxM y y.2)
  exact congrArg Subtype.val this

theorem sup_eq_top_of_lines (S : PlaneSetup h n p Ahat) {L M : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hM : Nat.card M = p) (hLM : L ≠ M) : L ⊔ M = ⊤ := by
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  have hP := isPlane_of_elementaryAbelian S.prime S.elem S.card
  have hinf := hP.inf_eq_bot hL hM hLM
  have hd1 : p ∣ Nat.card ↥(L ⊔ M) := hL ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(L ⊔ M) ∣ p ^ 2 := S.card ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow S.prime).mp hd2
  have hp2 := S.prime.two_le
  interval_cases k
  · rw [pow_zero] at hkc
    rw [hkc] at hd1
    exact absurd (Nat.le_of_dvd one_pos hd1) (by omega)
  · rw [pow_one] at hkc
    exfalso
    have heq : L = L ⊔ M :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hkc, hL])
    have hML : M ≤ L := heq ▸ le_sup_right
    have : M ≤ ⊥ := hinf ▸ le_inf hML le_rfl
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hM
    omega
  · exact (Subgroup.card_eq_iff_eq_top (L ⊔ M)).mp (by rw [hkc, S.card])

theorem eq_zero_of_fixed_lineSpace (S : PlaneSetup h n p Ahat)
    (hdec : PlaneKernelDecomposition h n p Ahat) {L M : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hM : Nat.card M = p) (hLM : L ≠ M) {t : ↥Ahat} (htM : t ∈ M) (ht1 : t ≠ 1)
    {v : Fin n → K} (hv : v ∈ lineSpace (planeRep h n Ahat) (idForm h n) L)
    (htv : act (planeRep h n Ahat) t v = v) : v = 0 := by
  set ρ := planeRep h n Ahat with hρ
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  have hP := isPlane_of_elementaryAbelian S.prime S.elem S.card
  let Stab : Subgroup ↥Ahat :=
    { carrier := {y | act ρ y v = v}
      mul_mem' := fun {a b} (ha : act ρ a v = v) (hb : act ρ b v = v) => by
        show act ρ (a * b) v = v
        rw [act_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show act ρ 1 v = v
        rw [act_one]
        rfl
      inv_mem' := fun {a} (ha : act ρ a v = v) => by
        show act ρ a⁻¹ v = v
        calc act ρ a⁻¹ v = act ρ a⁻¹ (act ρ a v) := by rw [ha]
          _ = v := by rw [← Module.End.mul_apply, ← act_mul, inv_mul_cancel, act_one]; rfl }
  have hLle : L ≤ Stab := fun y hy => hv.1 y hy
  have hMle : M ≤ Stab := by
    rw [← hP.zpowers_eq hM htM ht1, Subgroup.zpowers_le]
    exact htv
  have htop : ⊤ ≤ Stab := (sup_eq_top_of_lines S hL hM hLM) ▸ sup_le hLle hMle
  have hv0 : v ∈ fixedSpace ρ ⊤ := fun y _ => htop (Subgroup.mem_top y)
  have := hdec.nondegenerate_fixed ⟨v, hv0⟩ (fun y => by
    have h1 := (idForm_isSymm h n).eq y v
    rw [hv.2 y y.2, map_zero] at h1
    rw [LinearMap.domRestrict₁₂_apply]
    exact h1.symm)
  exact congrArg Subtype.val this

theorem primaryFactor_dvd_pow_sub_one (S : PlaneSetup h n p Ahat) (t : ↥Ahat) {g : K[X]}
    (hg : g ∈ primaryFactors (act (planeRep h n Ahat) t)) : g ∣ X ^ p - 1 := by
  have hpow : act (planeRep h n Ahat) t ^ p = 1 := by
    rw [← act_pow, show t ^ p = 1 from Subtype.ext (S.pow_eq_one t.2), act_one]
  refine (mem_primaryFactors.mp hg).2.2.trans (minpoly.dvd K _ ?_)
  simp [hpow]

theorem exists_factor_of_line (S : PlaneSetup h n p Ahat)
    (hdec : PlaneKernelDecomposition h n p Ahat) {L M : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hM : Nat.card M = p) (hLM : L ≠ M) {t : ↥Ahat} (htM : t ∈ M) (ht1 : t ≠ 1)
    (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥) :
    ∃ g ∈ primaryFactors (act (planeRep h n Ahat) t), g ≠ X - C 1 ∧
      ∃ v ∈ lineSpace (planeRep h n Ahat) (idForm h n) L,
        v ∈ primaryComponent (act (planeRep h n Ahat) t) g ∧ v ≠ 0 := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVL
  have hsq : Squarefree (minpoly K (act (planeRep h n Ahat) t)) :=
    (S.planeData t.2).squarefree_minpoly
  obtain ⟨g, hg, v, hvL, hvg, hv0⟩ := exists_primaryFactor_mem hsq
    (fun s hs => lineSpace_stable S t hs) hv₀ hv₀0
  refine ⟨g, hg, ?_, v, hvL, hvg, hv0⟩
  rintro rfl
  have hfix : act (planeRep h n Ahat) t v = v := by
    have := mem_primaryComponent.mp hvg
    simpa [sub_eq_zero] using this
  exact hv0 (eq_zero_of_fixed_lineSpace S hdec hL hM hLM htM ht1 hvL hfix)

theorem exists_mixing_factor (S : PlaneSetup h n p Ahat)
    (hdec : PlaneKernelDecomposition h n p Ahat) (hpq : ¬ p ∣ ℓ ^ f + 1) {L M : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hM : Nat.card M = p) (hLM : L ≠ M)
    (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    (hVM : lineSpace (planeRep h n Ahat) (idForm h n) M ≠ ⊥) :
    ∃ x : gramSU h (idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧ ∃ a : GoodBlockIdx h x,
      (a.1 : K[X]) ≠ X - C 1 ∧
      (∃ v ∈ lineSpace (planeRep h n Ahat) (idForm h n) L,
        v ∈ primaryComponent (xlin h n x) (a.1 : K[X]) ∧ v ≠ 0) ∧
      (∃ w ∈ lineSpace (planeRep h n Ahat) (idForm h n) M,
        w ∈ primaryComponent (xlin h n x) (a.1 : K[X]) ∧ w ≠ 0) := by
  classical
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  set ρ := planeRep h n Ahat with hρ
  have hP := isPlane_of_elementaryAbelian S.prime S.elem S.card
  have hinf := hP.inf_eq_bot hL hM hLM
  have hex : ∀ N : Subgroup ↥Ahat, Nat.card N = p → ∃ t : ↥Ahat, t ∈ N ∧ t ≠ 1 := by
    intro N hN
    have h1 : Nontrivial ↥N :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; exact S.prime.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥N)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  obtain ⟨tL, htL, htL1⟩ := hex L hL
  obtain ⟨tM, htM, htM1⟩ := hex M hM
  obtain ⟨fL, hfL, hfL1, v, hvL, hvf, hv0⟩ :=
    exists_factor_of_line S hdec hL hM hLM htM htM1 hVL
  obtain ⟨gM, hgM, hgM1, w, hwM, hwg, hw0⟩ :=
    exists_factor_of_line S hdec hM hL hLM.symm htL htL1 hVM
  have hfd := primaryFactor_dvd_pow_sub_one S tM hfL
  have hgd := primaryFactor_dvd_pow_sub_one S tL hgM
  have hfmon := monic_of_mem_primaryFactors hfL
  have hfirr := irreducible_of_mem_primaryFactors hfL
  obtain ⟨j, hj0, hjp, hdvd⟩ := exists_pow_dvd_comp S.prime hfmon hfirr hfd hfL1
    (monic_of_mem_primaryFactors hgM) (irreducible_of_mem_primaryFactors hgM) hgd hgM1
  set a : ↥Ahat := tL ^ j * tM with ha
  set T : Module.End K (Fin n → K) := act ρ a with hT
  have hTL : ∀ s ∈ lineSpace ρ (idForm h n) L, T s = act ρ tM s := by
    intro s hs
    have hs' := lineSpace_stable S tM hs
    rw [hT, ha, act_mul, Module.End.mul_apply]
    exact hs'.1 (tL ^ j) (pow_mem htL j)
  have hTM : ∀ s ∈ lineSpace ρ (idForm h n) M, T s = (act ρ tL ^ j) s := by
    intro s hs
    rw [hT, ha, act_mul, Module.End.mul_apply, hs.1 tM htM, act_pow]
  have hUstab : ∀ s ∈ lineSpace ρ (idForm h n) M,
      (act ρ tL ^ j) s ∈ lineSpace ρ (idForm h n) M := by
    intro s hs
    rw [← act_pow]
    exact lineSpace_stable S (tL ^ j) hs
  have hfv : aeval T fL v = 0 := by
    rw [aeval_apply_eq_of_agree (fun s hs => lineSpace_stable S tM hs) hTL fL hvL]
    exact mem_primaryComponent.mp hvf
  have hfw : aeval T fL w = 0 := by
    rw [aeval_apply_eq_of_agree hUstab hTM fL hwM]
    have hcomp : aeval (act ρ tL) (fL.comp (X ^ j)) = aeval (act ρ tL ^ j) fL := by
      rw [Polynomial.aeval_comp, aeval_X_pow]
    obtain ⟨q, hq⟩ := hdvd
    rw [← hcomp, hq, mul_comm, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hwg,
      map_zero]
  have hmem : fL ∈ primaryFactors T := mem_primaryFactors_of_apply_eq_zero hfirr hfmon hfv hv0
  have : Fact (Irreducible fL) := ⟨hfirr⟩
  have hgood : IsGoodBlock h (toLinU h n (liftUnitary a.1)) ⟨fL, hmem⟩ := by
    refine ⟨two_le_primaryMultiplicity (T := T) (a := fL) (S₁ := lineSpace ρ (idForm h n) L)
      (S₂ := lineSpace ρ (idForm h n) M) (fun s hs => lineSpace_stable S a hs)
      (fun s hs => lineSpace_stable S a hs) (disjoint_lineSpace hdec hL hM hLM) hvL hwM
      (mem_primaryComponent.mpr hfv) (mem_primaryComponent.mpr hfw) hv0 hw0, ?_⟩
    intro hself
    have hdeg := natDegree_ne_one_of_selfDual (h := h) S.prime hpq hfmon hfd hfL1 hself
    have hpos : 0 < fL.natDegree := hfirr.natDegree_pos
    have hd2 : 2 ≤ fL.natDegree := by omega
    have hq2 := two_le_pow_of h
    have hQ : 4 ≤ ℓ ^ (f * fL.natDegree) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (ℓ ^ f) ^ 2 := Nat.pow_le_pow_left hq2 2
        _ ≤ (ℓ ^ f) ^ fL.natDegree := Nat.pow_le_pow_right (by omega) hd2
        _ = ℓ ^ (f * fL.natDegree) := by rw [← pow_mul]
    change (primaryMultiplicity T fL, ℓ ^ (f * fL.natDegree)) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    omega
  have ha1 : a ≠ 1 := by
    intro h1
    apply htM1
    have h2 : tM = (tL ^ j)⁻¹ := by
      rw [ha] at h1
      exact eq_inv_of_mul_eq_one_right h1
    have h3 : tM ∈ L ⊓ M := ⟨h2 ▸ L.inv_mem (L.pow_mem htL j), htM⟩
    rw [hinf] at h3
    exact (Subgroup.mem_bot).mp h3
  exact ⟨a.1, a.2, fun h1 => ha1 (Subtype.ext h1), ⟨⟨fL, hmem⟩, hgood⟩, hfL1,
    ⟨v, hvL, mem_primaryComponent.mpr hfv, hv0⟩, ⟨w, hwM, mem_primaryComponent.mpr hfw, hw0⟩⟩

end Plane

end CFSG.RankThree.PartOne.KCUnitaryMixing
