module

public import CFSG.RankThree.PartOne.FOC.PSUSetup
public import CFSG.RankThree.PartOne.FOC.RankBlock
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.FOC.CentralQuot
public import CFSG.RankThree.PartOne.FOC.UnitarySplit

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary Polynomial

section Main

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem two_le_pow_of_unitaryFieldData (h : UnitaryFieldData ℓ f K) : 2 ≤ ℓ ^ f :=
  h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) ℓ)

@[expose] def DetTrivial (h : UnitaryFieldData ℓ f K) (x : ↥(gramSU h (idGram K n))) (p : ℕ) : Prop :=
  ∀ a : primaryFactors ((phiS h x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)),
    IsGoodBlock h (phiS h x) a →
    p ∣ primaryMultiplicity ((phiS h x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) →
    ∀ (g : LinearMap.GeneralLinearGroup K (Fin n → K))
      (hg : g ∈ orbitFactor (idForm h n) (phiS h x) (a : K[X])), g ^ p = 1 →
      blockDetHom (phiS h x) (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ = 1

theorem mem_sup_centralizer_psu_aux {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hZ : ¬ p ∣ Nat.card (normOneScalars h (gramSU h (idGram K n)) n))
    {x Y : ↥(gramSU h (idGram K n))} (hxp : x ^ p = 1) (hYp : Y ^ p = 1) (hdet : DetTrivial h x p)
    (hxY : x * Y = Y * x)
    {E : Subgroup (primeFormP h (idGram K n))}
    (hE : IsComponentOf (Subgroup.centralizer ({(x : primeFormP h (idGram K n))} :
      Set (primeFormP h (idGram K n)))) E) :
    (Y : primeFormP h (idGram K n)) ∈ E ⊔ Subgroup.centralizer (E : Set (primeFormP h (idGram K n))) := by
  classical
  have : Finite K := h.finite
  have hZc : normOneScalars h (gramSU h (idGram K n)) n ≤
      Subgroup.center ↥(gramSU h (idGram K n)) := normOneScalars_le_center h _ n
  have hp3 : 3 < p := by omega
  have hq := two_le_pow_of_unitaryFieldData h
  set xl : LinearMap.GeneralLinearGroup K (Fin n → K) := phiS h x with hxl
  have HU : UnitaryPrimaryData h.bar (idForm h n) xl := primaryData_phiS hpℓ hp hxp
  have hsplit : GoodSplit h (idForm h n) xl p := goodSplit_of_det HU hp hdet
  have hYM : phiS h Y ∈ unitaryCentralizer (idForm h n) xl := by
    refine Subgroup.mem_inf.mpr ⟨phiS_mem_unitary Y, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hxl, ← map_mul, ← map_mul, hxY]
  have hYpl : (phiS h Y) ^ p = 1 := by rw [← map_pow, hYp, map_one]
  obtain ⟨z, hzM, hzc, k, hk, hYzk⟩ := exists_central_factor HU hq hp hp3 hsplit hYM hYpl
  let ι := {a : primaryFactors (xl : Module.End K (Fin n → K)) // IsGoodBlock h xl a}
  have hSBle : ∀ a : ι, specialBlock (idForm h n) xl (a.1 : K[X]) ≤ (phiS h (n := n)).range :=
    fun a g hg => mem_range_phiS
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good HU hq a.1 a.2 hg)
  let F : ι → Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) xl (a.1 : K[X])).comap (phiS h)
  have hFmap : ∀ a : ι, (F a).map (phiS h) = specialBlock (idForm h n) xl (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  have hFq : ∀ a : ι, CFSG.IsQuasisimple ↥(F a) := by
    intro a
    have e : ↥(F a) ≃* ↥(specialBlock (idForm h n) xl (a.1 : K[X])) :=
      (Subgroup.equivMapOfInjective (F a) (phiS h) phiS_injective).trans
        (MulEquiv.subgroupCongr (hFmap a))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((specialBlockFacts_of_good HU hq a.1 a.2).quasisimple a.2.1)
  have hSM : ∀ g : ↥(gramSU h (idGram K n)), g ∈ Subgroup.centralizer ({x} : Set _) →
      phiS h g ∈ unitaryCentralizer (idForm h n) xl := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨phiS_mem_unitary g, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hxl, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  have hFC : ∀ a : ι, F a ≤ Subgroup.centralizer ({x} : Set ↥(gramSU h (idGram K n))) := by
    intro a g hg
    have hu : phiS h g ∈ unitaryCentralizer (idForm h n) xl :=
      specialBlock_le_unitaryCentralizer (show phiS h g ∈ specialBlock (idForm h n) xl (a.1 : K[X])
        from hg)
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2
    refine Subgroup.mem_centralizer_singleton_iff.mpr (phiS_injective ?_)
    rw [map_mul, map_mul]
    exact this
  have hFn : ∀ a : ι, ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(gramSU h (idGram K n))),
      ∀ f' ∈ F a, g * f' * g⁻¹ ∈ F a := by
    intro a g hg f' hf'
    have hconj := conj_mem_specialBlock (hSM g hg)
      (show phiS h f' ∈ specialBlock (idForm h n) xl (a.1 : K[X]) from hf')
    change phiS h (g * f' * g⁻¹) ∈ specialBlock (idForm h n) xl (a.1 : K[X])
    rw [map_mul, map_mul, map_inv]
    exact hconj
  have hkle : k ∈ (phiS h (n := n)).range :=
    (iSup_le fun a : ι => hSBle a) hk
  have hzle : z ∈ (phiS h (n := n)).range := by
    have : z = phiS h Y * k⁻¹ := by rw [hYzk]; simp
    rw [this]
    exact mul_mem ⟨Y, rfl⟩ (inv_mem hkle)
  obtain ⟨zS, hzS⟩ := hzle
  obtain ⟨kS, hkS⟩ := hkle
  have hYeq : Y = zS * kS := phiS_injective (by rw [map_mul, hzS, hkS, hYzk])
  have hzc' : ∀ G ∈ Subgroup.centralizer ({x} : Set ↥(gramSU h (idGram K n))), zS * G = G * zS := by
    intro G hG
    apply phiS_injective
    rw [map_mul, map_mul, hzS]
    exact (hzc _ (hSM G hG)).eq
  have hk' : kS ∈ ⨆ a : ι, F a := by
    have hmapsup : (⨆ a : ι, F a).map (phiS h) =
        ⨆ a : ι, specialBlock (idForm h n) xl (a.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hFmap
    have hk2 : phiS h kS ∈ (⨆ a : ι, F a).map (phiS h) := by
      rw [hmapsup, hkS]
      exact hk
    obtain ⟨s, hs, hs'⟩ := hk2
    have : s = kS := phiS_injective hs'
    rw [← this]
    exact hs
  rw [hYeq]
  exact mem_sup_centralizer_of_central_factorization _ hp hZ hZc hxp F hFq hFC hFn rfl hzc' hk' hE

@[expose] noncomputable def psiBack {B' : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K))}
    (hle : B' ≤ (phiS h (n := n)).range) : ↥B' →* ↥(gramSU h (idGram K n)) :=
  (MonoidHom.ofInjective (phiS_injective (h := h) (n := n))).symm.toMonoidHom.comp
    (Subgroup.inclusion hle)

theorem phiS_psiBack {B' : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K))}
    (hle : B' ≤ (phiS h (n := n)).range) (g : ↥B') :
    phiS h (psiBack hle g) = (g : LinearMap.GeneralLinearGroup K (Fin n → K)) := by
  have := (MonoidHom.ofInjective (phiS_injective (h := h) (n := n))).apply_symm_apply
    (Subgroup.inclusion hle g)
  exact congrArg Subtype.val this

theorem psiBack_injective {B' : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K))}
    (hle : B' ≤ (phiS h (n := n)).range) : Function.Injective (psiBack hle) := by
  intro g g' e
  apply Subtype.ext
  rw [← phiS_psiBack hle g, ← phiS_psiBack hle g', e]

open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo) in
theorem detTrivial_of_localRank {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hZ : ¬ p ∣ Nat.card (normOneScalars h (gramSU h (idGram K n)) n))
    {x : ↥(gramSU h (idGram K n))} (hxp : x ^ p = 1)
    (hrank : LocalRankLeTwo p (primeFormP h (idGram K n))) : DetTrivial h x p := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hq := two_le_pow_of_unitaryFieldData h
  set xl : LinearMap.GeneralLinearGroup K (Fin n → K) := phiS h x with hxl
  have HU : UnitaryPrimaryData h.bar (idForm h n) xl := primaryData_phiS hpℓ hp hxp
  intro a ha hpm g hg hgp
  by_contra hδ
  set δ : (AdjoinRoot (a : K[X]))ˣ :=
    blockDetHom xl (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ with hδdef
  have hm5 : 5 ≤ primaryMultiplicity (xl : Module.End K (Fin n → K)) (a : K[X]) :=
    hp5.trans (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num) ha.1) hpm)
  have hδp : δ ^ p = 1 := by
    rw [hδdef, ← map_pow]
    have : (⟨g, orbitFactor_le_gl_centralizer hg⟩ : gl_centralizer xl) ^ p = 1 :=
      Subtype.ext (by simpa using hgp)
    rw [this, map_one]
  have hδord : orderOf δ = p := orderOf_eq_prime hδp hδ
  set M : Subgroup (AdjoinRoot (a : K[X]))ˣ := Subgroup.zpowers δ with hM
  have hMcard : Nat.card ↥M = p := by rw [hM, Nat.card_zpowers, hδord]
  have hMp : ∀ y : ↥M, y ^ p = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    change (y : (AdjoinRoot (a : K[X]))ˣ) ^ p = 1
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hδp,
      _root_.one_zpow]
  have key : ∃ (R : ↥M × ↥M × ↥M →* LinearMap.GeneralLinearGroup K (Fin n → K))
      (u : LinearMap.GeneralLinearGroup K (Fin n → K)),
      (∀ r, R r ∈ specialBlock (idForm h n) xl (a : K[X])) ∧
      u ∈ specialBlock (idForm h n) xl (a : K[X]) ∧ Function.Injective R ∧ u ^ 2 = 1 ∧
      (∀ r, u * R r = R r * u) ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]),
        ∀ v : primaryComponent (xl : Module.End K (Fin n → K)) (a : K[X]),
          ((u : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
            (v : Fin n → K) = ((c • v : primaryComponent (xl : Module.End K (Fin n → K))
              (a : K[X])) : Fin n → K) := by
    by_cases hself : dualPoly h.bar (a : K[X]) = a
    · refine exists_torus_selfDual hself (selfDualPrimaryBlock HU a hself) hm5 M ?_
      intro y hy
      have hδQ : ((δ : (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) ^
          ((ℓ ^ f) ^ (a : K[X]).natDegree + 1) = 1 :=
        selfDual_det_pow hself (selfDualPrimaryBlock HU a hself) hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hk, Units.val_zpow_eq_zpow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, zpow_natCast, hδQ, _root_.one_zpow]
    · exact exists_torus_paired (pairedPrimaryBlock HU a (Ne.symm hself)) hm5 M
  obtain ⟨R, u, hR, hu, hRinj, hu2, hcomm, hns⟩ := key
  have hle : specialBlock (idForm h n) xl (a : K[X]) ≤ (phiS h (n := n)).range :=
    fun g' hg' => mem_range_phiS
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good HU hq a ha hg')
  let ψ := psiBack (h := h) hle
  let ρ : ↥(specialBlock (idForm h n) xl (a : K[X])) →* primeFormP h (idGram K n) :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).comp ψ
  let R' : ↥M × ↥M × ↥M →* ↥(specialBlock (idForm h n) xl (a : K[X])) :=
    R.codRestrict _ hR
  have hψR : ∀ r, ψ (R' r) = 1 → R' r = 1 := fun r hr =>
    psiBack_injective hle (by rw [hr, map_one])
  have hinj : Function.Injective (ρ.comp R') := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hmem : ψ (R' r) ∈ normOneScalars h (gramSU h (idGram K n)) n := by
      rw [← QuotientGroup.eq_one_iff]
      exact hr
    have hpow : (ψ (R' r)) ^ p = 1 := by
      rw [← map_pow, ← map_pow]
      have : r ^ p = 1 := Prod.ext (hMp r.1) (Prod.ext (hMp r.2.1) (hMp r.2.2))
      rw [this, map_one, map_one]
    have h1 : ψ (R' r) = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd_card _ hp hZ hmem hpow
    have h2 : R' r = 1 := hψR r h1
    have h3 : R r = 1 := congrArg Subtype.val h2
    exact hRinj (h3.trans (map_one R).symm)
  let u' : ↥(specialBlock (idForm h n) xl (a : K[X])) := ⟨u, hu⟩
  have hu1 : ρ u' ≠ 1 := by
    intro h1
    have hmem : ψ u' ∈ normOneScalars h (gramSU h (idGram K n)) n := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    obtain ⟨c, hc⟩ := phiS_apply_of_mem_normOneScalars hmem
    apply hns
    refine ⟨algebraMap K (AdjoinRoot (a : K[X])) c, fun v => ?_⟩
    have h2 : ((u : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        (v : Fin n → K) = c • (v : Fin n → K) := by
      have := hc (v : Fin n → K)
      rwa [phiS_psiBack hle u'] at this
    rw [h2, coe_algebraMap_smul_primaryComponent]
  have hu2' : u' ^ 2 = 1 := Subtype.ext hu2
  have hcomm' : ∀ r, u' * R' r = R' r * u' := fun r => Subtype.ext (hcomm r)
  exact not_localRankLeTwo_of_torus_involution hMcard hMp ρ R' hinj u' hu2'
    hu1 hcomm' hrank

theorem innerComp_psu {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hn : 1 ≤ n)
    (hZ : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    [Finite (primeFormP h (idGram K n))] :
    InnerComp p (primeFormP h (idGram K n)) := by
  intro hrank b y hbp hyp hby E hE
  have : Finite K := h.finite
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h (gramSU h (idGram K n)) n) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h hn]
    exact hZ
  have hZc : normOneScalars h (gramSU h (idGram K n)) n ≤
      Subgroup.center ↥(gramSU h (idGram K n)) := normOneScalars_le_center h _ n
  obtain ⟨x, rfl, hxp⟩ := exists_mk_lift_pow_eq_one _ hp hZ' hbp
  obtain ⟨Y, rfl, hYp⟩ := exists_mk_lift_pow_eq_one _ hp hZ' hyp
  have hxY : x * Y = Y * x := commute_of_mk_commute _ hp hZ' hZc hxp hby
  exact mem_sup_centralizer_psu_aux hp hp5 hpℓ hZ' hxp hYp
    (detTrivial_of_localRank hp hp5 hpℓ hZ' hxp hrank) hxY hE

end Main

end CFSG.RankThree.PartOne.FOC
