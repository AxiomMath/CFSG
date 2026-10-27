module

public import CFSG.RankThree.PartOne.S15K.U5Lift
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.S15K.AutLayer

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Setup

abbrev idSU : Subgroup (GL (Fin 5) K) := gramSU h (idGram K 5)

abbrev idU : Subgroup (GL (Fin 5) K) := primeFormUnitary h (idGram K 5)

theorem idSU_le_idU : idSU h ≤ idU h := fun _ hg => ((mem_gramSU_iff_unitary h).mp hg).1

@[expose] noncomputable def idPhi : ↥(idSU h) →* LinearMap.GeneralLinearGroup K (Fin 5 → K) :=
  (toLinU h 5).comp (Subgroup.inclusion (idSU_le_idU h))

theorem idPhi_injective : Function.Injective (idPhi h) := fun _ _ e =>
  Subgroup.inclusion_injective _ (toLinU_injective e)

@[expose] noncomputable def idPi : ↥(idSU h) →* primeFormP h (idGram K 5) :=
  QuotientGroup.mk' (normOneScalars h (idSU h) 5)

@[expose] noncomputable def idConj (g : ↥(idU h)) : MulAut ↥(idSU h) :=
  primeFormConjSU h (idGram K 5) g

theorem idConj_coe (g : ↥(idU h)) (w : ↥(idSU h)) :
    ((idConj h g w : ↥(idSU h)) : GL (Fin 5) K) = (g : GL (Fin 5) K) * w * (g : GL (Fin 5) K)⁻¹ :=
  rfl

theorem idPi_idConj (g : ↥(idU h)) (w : ↥(idSU h)) :
    idPi h (idConj h g w) = primeFormConjHom h (idGram K 5) g (idPi h w) :=
  (primeFormConjHom_mk h (idGram K 5) g w).symm

theorem ker_idPi_le_center : (idPi h).ker ≤ Subgroup.center ↥(idSU h) := by
  rw [idPi, QuotientGroup.ker_mk']
  exact normOneScalars_le_center h _ 5

theorem idPi_surjective : Function.Surjective (idPi h) := QuotientGroup.mk'_surjective _

theorem idConj_fix_ker (g : ↥(idU h)) : ∀ k ∈ (idPi h).ker, idConj h g k = k := by
  intro k hk
  rw [idPi, QuotientGroup.ker_mk'] at hk
  obtain ⟨c, -, -, hc⟩ := hk
  apply Subtype.ext
  rw [idConj_coe, hc]
  exact (commute_scalar c (g : GL (Fin 5) K)).mul_inv_cancel

theorem commute_toLinU_iff (a b : ↥(idU h)) :
    Commute ((toLinU h 5 a : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))
      ((toLinU h 5 b : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) ↔
      a * b = b * a := by
  constructor
  · intro hc
    apply toLinU_injective (h := h)
    rw [map_mul, map_mul]
    exact Units.ext hc.eq
  · intro hab
    have := congrArg (fun z : ↥(idU h) =>
      ((toLinU h 5 z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))) hab
    have h2 : ((toLinU h 5 a : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) * ((toLinU h 5 b : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) = ((toLinU h 5 b : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) * ((toLinU h 5 a : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) := by
      simpa only [map_mul, Units.val_mul] using this
    exact h2

theorem idConj_eq_self_iff (g : ↥(idU h)) (w : ↥(idSU h)) :
    idConj h g w = w ↔
      Subgroup.inclusion (idSU_le_idU h) w * g = g * Subgroup.inclusion (idSU_le_idU h) w := by
  rw [Subtype.ext_iff, idConj_coe, mul_inv_eq_iff_eq_mul, Subtype.ext_iff]
  constructor <;> intro hh <;> exact hh.symm

theorem idPhi_mem_unitaryCentralizer_iff (g : ↥(idU h)) (w : ↥(idSU h)) :
    idPhi h w ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) ↔ idConj h g w = w := by
  rw [mem_unitaryCentralizer, idConj_eq_self_iff]
  have hU : idPhi h w ∈ sesqUnitaryGroup (idForm h 5) :=
    toLinU_mem (Subgroup.inclusion (idSU_le_idU h) w)
  constructor
  · rintro ⟨-, hc⟩
    exact (commute_toLinU_iff h _ g).mp hc
  · intro he
    exact ⟨hU, (commute_toLinU_iff h _ g).mpr he⟩

end Setup

section Family

variable {h}

abbrev BlockIdx (x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Type :=
  {a : primaryFactors (x : Module.End K (Fin 5 → K)) //
    2 ≤ primaryMultiplicity (x : Module.End K (Fin 5 → K)) (a : K[X])}

variable (h) in
@[expose] noncomputable def blockSU (g : ↥(idU h)) (a : BlockIdx (toLinU h 5 g)) :
    Subgroup ↥(idSU h) :=
  (specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X])).comap (idPhi h)

variable {g : ↥(idU h)} (HU : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g))
  (hq : 4 ≤ 2 ^ f)

include HU hq in
theorem specialBlock_le_range (a : primaryFactors ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
    (Fin 5 → K)) : Module.End K (Fin 5 → K))) :
    specialBlock (idForm h 5) (toLinU h 5 g) (a : K[X]) ≤ (idPhi h).range := by
  intro y hy
  have hu := specialBlock_le_unitaryCentralizer hy
  have hdet : LinearMap.det ((y : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) = 1 := (specialBlockFacts HU hq a).detK y hy
  have hmem : Matrix.GeneralLinearGroup.toLin.symm y ∈ gramSU h (idGram K 5) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K 5), MulEquiv.apply_symm_apply,
      mem_sesqSpecialUnitaryGroup]
    exact ⟨hu.1, hdet⟩
  exact ⟨⟨_, hmem⟩, MulEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin : GL (Fin 5) K ≃*
    LinearMap.GeneralLinearGroup K (Fin 5 → K)) y⟩

include HU hq in
theorem map_blockSU (a : BlockIdx (toLinU h 5 g)) :
    (blockSU h g a).map (idPhi h) = specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) :=
  Subgroup.map_comap_eq_self (specialBlock_le_range HU hq a.1)

omit HU hq in
theorem blockSU_le_fixed (a : BlockIdx (toLinU h 5 g)) : blockSU h g a ≤ fixedSub (idConj h g) := by
  intro w hw
  exact (idPhi_mem_unitaryCentralizer_iff h g w).mp
    (specialBlock_le_unitaryCentralizer
      (show idPhi h w ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) from hw))

include HU hq in
theorem isQuasisimple_blockSU (a : BlockIdx (toLinU h 5 g)) : IsQuasisimple ↥(blockSU h g a) := by
  have e : ↥(blockSU h g a) ≃*
      ↥(specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (blockSU h g a) (idPhi h) (idPhi_injective h)).trans
      (MulEquiv.subgroupCongr (map_blockSU HU hq a))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm ((specialBlockFacts HU hq a.1).quasisimple a.2)

omit HU hq in
theorem conj_mem_blockSU (a : BlockIdx (toLinU h 5 g)) {w : ↥(idSU h)}
    (hw : w ∈ fixedSub (idConj h g)) {u : ↥(idSU h)} (hu : u ∈ blockSU h g a) :
    w * u * w⁻¹ ∈ blockSU h g a := by
  have hwc : idPhi h w ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) :=
    (idPhi_mem_unitaryCentralizer_iff h g w).mpr hw
  have := conj_mem_specialBlock hwc
    (show idPhi h u ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) from hu)
  change idPhi h (w * u * w⁻¹) ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X])
  rw [map_mul, map_mul, map_inv]
  exact this

include HU hq in
theorem derived_fixed_le_iSup : ⁅fixedSub (idConj h g), fixedSub (idConj h g)⁆ ≤ ⨆ a, blockSU h g a := by
  set M := unitaryCentralizer (idForm h 5) (toLinU h 5 g) with hM
  have h1 : (fixedSub (idConj h g)).map (idPhi h) ≤ M := by
    rintro _ ⟨w, hw, rfl⟩
    exact (idPhi_mem_unitaryCentralizer_iff h g w).mpr hw
  have h2 : (⁅fixedSub (idConj h g), fixedSub (idConj h g)⁆).map (idPhi h) ≤
      ⨆ a : BlockIdx (toLinU h 5 g), specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono h1 h1).trans
      (commutator_unitaryCentralizer_eq_iSup_specialBlock HU hq).le
  have h3 : (⨆ a : BlockIdx (toLinU h 5 g), blockSU h g a).map (idPhi h) =
      ⨆ a : BlockIdx (toLinU h 5 g), specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun a => map_blockSU HU hq a
  intro w hw
  have h4 : idPhi h w ∈ (⨆ a : BlockIdx (toLinU h 5 g), blockSU h g a).map (idPhi h) := by
    rw [h3]
    exact h2 (Subgroup.mem_map_of_mem _ hw)
  obtain ⟨w', hw', hww'⟩ := h4
  rwa [← idPhi_injective h hww']

end Family

section Centre

variable {h}

theorem fix_of_mem_orbitFactor {x : LinearMap.GeneralLinearGroup K (Fin 5 → K)}
    (HU' : UnitaryPrimaryData h.bar (idForm h 5) x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K (Fin 5 → K))) (hself : dualPoly h.bar a = a)
    {y : LinearMap.GeneralLinearGroup K (Fin 5 → K)} (hy : y ∈ orbitFactor (idForm h 5) x a)
    {v : Fin 5 → K} (hv : primaryProjection (x : Module.End K (Fin 5 → K)) a v = 0) :
    (y : Module.End K (Fin 5 → K)) v = v := by
  classical
  have hsq := HU'.squarefree
  have hsum : v = ∑ b ∈ primaryFactors (x : Module.End K (Fin 5 → K)),
      primaryProjection (x : Module.End K (Fin 5 → K)) b v := by
    have := LinearMap.congr_fun (sum_primaryProjection hsq) v
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  conv_lhs => rw [hsum]
  rw [map_sum]
  conv_rhs => rw [hsum]
  refine Finset.sum_congr rfl fun b hb => ?_
  by_cases hba : b = a
  · subst hba
    rw [hv, map_zero]
  · refine hy.2 b hb ?_ _ (primaryProjection_mem hsq hb v)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hself, not_or]
    exact ⟨hba, hba⟩


open CFSG.RankThree.PartOne.KCUnitaryBlock in
theorem exists_not_mem_primaryComponent {g : ↥(idU h)} {μ : K} (hμ : h.bar μ * μ = 1)
    (hg1 : ¬ ∃ d : Kˣ, d ^ (2 ^ f + 1) = 1 ∧
      (g : GL (Fin 5) K) = GeneralLinearGroup.scalar (Fin 5) d) :
    ∃ v : Fin 5 → K, v ∉ primaryComponent ((toLinU h 5 g : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ) := by
  by_contra hall
  push Not at hall
  apply hg1
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hμ
    exact zero_ne_one hμ
  refine ⟨Units.mk0 μ hμ0, ?_, ?_⟩
  · rw [pow_succ_eq_one_iff_norm h]
    show h.norm μ = 1
    rw [UnitaryFieldData.norm, mul_comm]
    exact hμ
  · apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have h1 := mem_primaryComponent_X_sub_C.mp (hall v)
    rw [toLinU_apply_eq] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h1]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Centre

section CentreBlock

variable {h} {g : ↥(idU h)} (HU : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g))
  (hq : 4 ≤ 2 ^ f) (a : BlockIdx (toLinU h 5 g)) {μ : K} (hax : (a.1 : K[X]) = X - C μ)
  (hμ : h.bar μ * μ = 1)

include hax in
theorem mem_primaryFactors_of_blockIdx :
    (X - C μ : K[X]) ∈ primaryFactors ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) := by
  have := a.1.2
  rwa [hax] at this

include HU hax hμ in
theorem eq_one_of_mem_blockSU_of_mem_ker
    (hnotTop : ∃ v : Fin 5 → K, v ∉ primaryComponent ((toLinU h 5 g :
      LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ))
    {z : ↥(idSU h)} (hz : z ∈ blockSU h g a) (hzk : z ∈ (idPi h).ker) : z = 1 := by
  have ha' := mem_primaryFactors_of_blockIdx a hax
  have hself := dualPoly_X_sub_C_eq h hμ
  have hsq := HU.squarefree
  obtain ⟨c, -, -, hc⟩ : z ∈ normOneScalars h (idSU h) 5 := by
    rwa [idPi, QuotientGroup.ker_mk'] at hzk
  have hz' : idPhi h z ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := hz
  rw [hax] at hz'
  obtain ⟨v, hv⟩ := hnotTop
  set π := primaryProjection ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
    Module.End K (Fin 5 → K)) (X - C μ) with hπ
  have hππ : ∀ v, π (π v) = π v := fun v => by
    have := congrArg (fun T : Module.End K (Fin 5 → K) => T v) (primaryProjection_mul_self hsq ha')
    exact this
  have hv'0 : π (v - π v) = 0 := by rw [map_sub, hππ, sub_self]
  have hv'ne : v - π v ≠ 0 := by
    intro h0
    apply hv
    have : v = π v := sub_eq_zero.mp h0
    rw [this]
    exact primaryProjection_mem hsq ha' v
  have hfix := fix_of_mem_orbitFactor HU ha' hself (specialBlock_le_orbitFactor hz') hv'0
  have hact := toLinU_scalar' h (z := Subgroup.inclusion (idSU_le_idU h) z) (c := c) hc
  have hphi : ((idPhi h z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) =
      (c : K) • (1 : Module.End K (Fin 5 → K)) := hact
  rw [hphi] at hfix
  have h1 : ((c : K) - 1) • (v - π v) = 0 := by
    rw [sub_smul, one_smul]
    simpa using sub_eq_zero.mpr hfix
  have h2 := (smul_eq_zero.mp h1).resolve_right hv'ne
  have hc1 : c = 1 := Units.ext (sub_eq_zero.mp h2)
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl


include HU hq hax hμ in
theorem eq_one_of_central_blockSU {p : ℕ} (hp : p.Prime)
    (hmlt : Module.finrank K (primaryComponent ((toLinU h 5 g :
      LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ)) < p)
    {w : ↥(idSU h)} (hw : w ∈ blockSU h g a) (hcomm : ∀ w' ∈ blockSU h g a, w * w' = w' * w)
    (hwp : w ^ p = 1) : w = 1 := by
  classical
  have ha' := mem_primaryFactors_of_blockIdx a hax
  have hself := dualPoly_X_sub_C_eq h hμ
  have hsq := HU.squarefree
  set x : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) with hx
  have hw' : idPhi h w ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := hw
  have hwM : idPhi h w ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) :=
    specialBlock_le_unitaryCentralizer hw'
  have hmk : ∀ r : K[X], AdjoinRoot.mk (a.1 : K[X]) r =
      algebraMap K (AdjoinRoot (a.1 : K[X])) (r.eval μ) := by
    intro r
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk, hax]
    exact X_sub_C_dvd_sub_C_eval
  obtain ⟨c', hc'⟩ := (specialBlockFacts HU hq a.1).scalar (idPhi h w) hwM (fun _ y hy => by
    obtain ⟨w', hw'y⟩ : y ∈ (idPhi h).range := specialBlock_le_range HU hq a.1 hy
    subst hw'y
    have hw'' : w' ∈ blockSU h g a := hy
    show idPhi h w * idPhi h w' = idPhi h w' * idPhi h w
    rw [← map_mul, ← map_mul, hcomm w' hw''])
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective c'
  rw [hmk] at hc'
  set κ : K := r.eval μ with hκ
  have hact : ∀ v ∈ primaryComponent x (X - C μ),
      ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) v =
        κ • v := by
    intro v hv
    rw [← hax] at hv
    have := hc' ⟨v, hv⟩
    rw [coe_algebraMap_smul_primaryComponent] at this
    exact this
  have hVa := primaryComponent_ne_bot hsq ha'
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVa
  have hworb : idPhi h w ∈ orbitFactor (idForm h 5) (toLinU h 5 g) (X - C μ) := by
    have := specialBlock_le_orbitFactor hw'
    rwa [hax] at this
  have hid : ∀ b ∈ primaryFactors x, b ≠ X - C μ → ∀ v ∈ primaryComponent x b,
      ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) v = v := by
    intro b hb hba v hv
    refine hworb.2 b hb ?_ v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hself, not_or]
    exact ⟨hba, hba⟩
  have hcommx : Commute ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) x := (mem_unitaryCentralizer.mp hwM).2
  have hdet : κ ^ Module.finrank K (primaryComponent x (X - C μ)) = 1 := by
    have h1 := (specialBlockFacts HU hq a.1).detK _ hw'
    rw [det_eq_det_restrict_of_trivial_off hsq ha' hcommx hid] at h1
    have hres : ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)).restrict
        (fun _ hv => apply_mem_primaryComponent (a := X - C μ) hcommx hv) =
        κ • (LinearMap.id : Module.End K (primaryComponent x (X - C μ))) := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact hact v v.2
    rw [hres, LinearMap.det_smul, LinearMap.det_id, mul_one] at h1
    exact h1
  have hpow : ∀ n : ℕ, (((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) ^ n) v₀ = κ ^ n • v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hact v₀ hv₀, map_smul, ih, smul_smul, pow_succ']
  have hκp : κ ^ p = 1 := by
    have h1 := hpow p
    have hwp' : ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hwp, map_one]
      rfl
    rw [hwp'] at h1
    have h2 : (κ ^ p - 1) • v₀ = 0 := by
      rw [sub_smul, one_smul, ← h1]
      simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv₀ne)
  have hmpos : 0 < Module.finrank K (primaryComponent x (X - C μ)) := by
    have : Nontrivial (primaryComponent x (X - C μ)) := Submodule.nontrivial_iff_ne_bot.mpr hVa
    exact Module.finrank_pos
  have hcop : Nat.Coprime p (Module.finrank K (primaryComponent x (X - C μ))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      have := Nat.le_of_dvd hmpos hd
      omega
  have hκ1 : κ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hκp, hdet⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have hone : ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) = 1 := by
    refine LinearMap.ext fun v => ?_
    set π := primaryProjection x (X - C μ) with hπ
    have hππ : π (π v) = π v := by
      have := congrArg (fun T : Module.End K (Fin 5 → K) => T v)
        (primaryProjection_mul_self hsq ha')
      exact this
    have h1 : ((idPhi h w : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))
        (π v) = π v := by
      rw [hact _ (primaryProjection_mem hsq ha' v), hκ1, one_smul]
    have h2 := fix_of_mem_orbitFactor HU ha' hself hworb (v := v - π v) (by rw [map_sub, hππ, sub_self])
    have h3 : v = π v + (v - π v) := by abel
    conv_lhs => rw [h3]
    rw [map_add, h1, h2]
    simp
  have : idPhi h w = 1 := Units.ext hone
  exact idPhi_injective h (this.trans (map_one _).symm)


theorem coe_restrict_pow {V : Type*} [AddCommGroup V] [Module K V] (A : Module.End K V)
    {W : Submodule K V} (hA : ∀ v ∈ W, A v ∈ W) (n : ℕ) (v : W) :
    ((((A.restrict hA) ^ n) v : W) : V) = (A ^ n) (v : V) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
    rfl

include HU hq hax hμ in
theorem exists_inner_blockSU {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    (A : ↥(idU h))
    (hnotTop : ∃ v : Fin 5 → K, v ∉ primaryComponent ((toLinU h 5 g :
      LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) (X - C μ))
    (hAx : Commute ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K))) {c₀ : Kˣ} (hc₀ : c₀ ^ (2 ^ f + 1) = 1)
    (hAp : (A : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c₀) :
    ∃ w₀ ∈ blockSU h g a, ∀ w' ∈ blockSU h g a, idConj h A w' = w₀ * w' * w₀⁻¹ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have ha' := mem_primaryFactors_of_blockIdx a hax
  have hsq := HU.squarefree
  set x : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) with hx
  set A' : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))
    with hA'
  have hAV : ∀ v ∈ primaryComponent x (X - C μ), A' v ∈ primaryComponent x (X - C μ) :=
    fun v hv => apply_mem_primaryComponent hAx hv
  have hA'p : A' ^ p = (c₀ : K) • (1 : Module.End K (Fin 5 → K)) := by
    have h1 := toLinU_scalar' h (z := A ^ p) (c := c₀) (by rw [Subgroup.coe_pow]; exact hAp)
    rw [map_pow, Units.val_pow_eq_pow_val] at h1
    exact h1
  set m := Module.finrank K (primaryComponent x (X - C μ)) with hm
  have hVa := primaryComponent_ne_bot hsq ha'
  have hmpos : 0 < m := by
    have : Nontrivial (primaryComponent x (X - C μ)) := Submodule.nontrivial_iff_ne_bot.mpr hVa
    exact Module.finrank_pos
  have hmlt : m < p := by
    obtain ⟨v, hv⟩ := hnotTop
    have h1 := Submodule.finrank_lt (s := primaryComponent x (X - C μ))
      (fun h' => hv (by rw [h']; trivial))
    have h2 : Module.finrank K (Fin 5 → K) = 5 := by simp
    omega
  have hcop : Nat.Coprime p m :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      have := Nat.le_of_dvd hmpos hd
      omega
  set d : K := LinearMap.det (A'.restrict hAV) with hd
  have hdp : d ^ p = (c₀ : K) ^ m := by
    have h1 : (A'.restrict hAV) ^ p =
        (c₀ : K) • (LinearMap.id : Module.End K (primaryComponent x (X - C μ))) := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [coe_restrict_pow, hA'p]
      simp
    have := congrArg LinearMap.det h1
    rw [map_pow, LinearMap.det_smul, LinearMap.det_id, mul_one] at this
    exact this
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hdp
    exact pow_ne_zero m c₀.ne_zero hdp.symm
  have hc₀n : h.bar (c₀ : K) * c₀ = 1 := by
    have := (pow_succ_eq_one_iff_norm h c₀).mp hc₀
    rw [UnitaryFieldData.norm] at this
    rw [mul_comm]
    exact this
  have hdn : h.bar d * d = 1 :=
    bar_mul_eq_one_of_pow_eq h hp hp2 hpq hdp (by rw [map_pow, ← mul_pow, hc₀n, one_pow])
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (p : ℤ) * u + (m : ℤ) * v = 1 := by
    obtain ⟨a₁, b₁, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨a₁, b₁, by linarith⟩
  set cc : K := (c₀ : K) ^ u * d ^ v with hcc
  have hcc0 : cc ≠ 0 := mul_ne_zero (zpow_ne_zero _ c₀.ne_zero) (zpow_ne_zero _ hd0)
  have hccn : h.bar cc * cc = 1 := by
    rw [hcc, map_mul, map_zpow₀, map_zpow₀]
    calc h.bar (c₀ : K) ^ u * h.bar d ^ v * ((c₀ : K) ^ u * d ^ v)
        = (h.bar (c₀ : K) * c₀) ^ u * (h.bar d * d) ^ v := by
          rw [_root_.mul_zpow, _root_.mul_zpow]; ring
      _ = 1 := by rw [hc₀n, hdn, _root_.one_zpow, _root_.one_zpow, mul_one]
  have hccm : cc ^ m = d := by
    have e1 : (d : K) ^ ((p : ℤ) * u) = (c₀ : K) ^ ((m : ℤ) * u) := by
      rw [_root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hdp]
    have e2 : cc ^ m = (c₀ : K) ^ ((m : ℤ) * u) * d ^ ((m : ℤ) * v) := by
      rw [hcc, mul_pow, ← zpow_natCast ((c₀ : K) ^ u) m, ← zpow_natCast (d ^ v) m,
        ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm u, mul_comm v]
    rw [e2, ← e1, ← zpow_add₀ hd0]
    have : (p : ℤ) * u + (m : ℤ) * v = 1 := huv
    rw [this, zpow_one]
  obtain ⟨s, hsSB, hsA⟩ := exists_specialBlock_mul_scalar h HU hμ ha' (toLinU h 5 A) (toLinU_mem A)
    hAx hcc0 hccn (by rw [hccm])
  have hsSB' : s ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := by
    rw [hax]; exact hsSB
  obtain ⟨w₀, hw₀⟩ : s ∈ (idPhi h).range := specialBlock_le_range HU hq a.1 hsSB'
  have hw₀B : w₀ ∈ blockSU h g a := by
    show idPhi h w₀ ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X])
    rw [hw₀]; exact hsSB'
  refine ⟨w₀, hw₀B, fun w' hw' => ?_⟩
  set Y : LinearMap.GeneralLinearGroup K (Fin 5 → K) := s⁻¹ * toLinU h 5 A with hY
  have hsY : toLinU h 5 A = s * Y := by rw [hY]; group
  have hsM : s ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) :=
    specialBlock_le_unitaryCentralizer hsSB'
  have hAM : toLinU h 5 A ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) :=
    mem_unitaryCentralizer.mpr ⟨toLinU_mem A, hAx⟩
  have hYM : Y ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 g) :=
    mul_mem (inv_mem hsM) hAM
  have hYact : ∀ v ∈ primaryComponent x (X - C μ), (Y : Module.End K (Fin 5 → K)) v = cc • v := by
    intro v hv
    have h1 := hsA v hv
    change A' v = _ at h1
    rw [hY, Units.val_mul, Module.End.mul_apply]
    change ((s⁻¹ : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) (A' v) = _
    rw [h1, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have hscal : ∃ c'' : AdjoinRoot (a.1 : K[X]), ∀ v : primaryComponent x (a.1 : K[X]),
      (Y : Module.End K (Fin 5 → K)) (v : Fin 5 → K) = ((c'' • v : primaryComponent x (a.1 : K[X])) :
        Fin 5 → K) := by
    refine ⟨algebraMap K (AdjoinRoot (a.1 : K[X])) cc, fun v => ?_⟩
    rw [coe_algebraMap_smul_primaryComponent]
    have hv' : (v : Fin 5 → K) ∈ primaryComponent x (X - C μ) := by rw [← hax]; exact v.2
    exact hYact _ hv'
  have hcommY : Commute Y (idPhi h w') :=
    commute_orbitFactor_of_scalar HU a.1 hYM hscal (specialBlock_le_orbitFactor (show idPhi h w' ∈
      specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) from hw'))
  apply idPhi_injective h
  have e1 : idPhi h (idConj h A w') = toLinU h 5 A * idPhi h w' * (toLinU h 5 A)⁻¹ := by
    change toLinU h 5 (Subgroup.inclusion (idSU_le_idU h) (idConj h A w')) = _
    have : Subgroup.inclusion (idSU_le_idU h) (idConj h A w') =
        A * Subgroup.inclusion (idSU_le_idU h) w' * A⁻¹ := Subtype.ext (idConj_coe h A w')
    rw [this, map_mul, map_mul, map_inv]
    rfl
  rw [e1, map_mul, map_mul, map_inv, hw₀, hsY]
  calc s * Y * idPhi h w' * (s * Y)⁻¹ = s * (Y * idPhi h w' * Y⁻¹) * s⁻¹ := by group
    _ = s * idPhi h w' * s⁻¹ := by rw [hcommY.mul_inv_cancel]

end CentreBlock


end CFSG.RankThree.PartOne.S15K
