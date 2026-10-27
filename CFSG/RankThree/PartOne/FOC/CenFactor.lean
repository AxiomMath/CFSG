module

public import CFSG.RankThree.PartOne.FOC.PSUSetup
public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.FOC.UnitaryFactorAll

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary Polynomial

section Abstract

@[expose] def QuasiFactored {G : Type} [Group G] (C : Subgroup G) : Prop :=
  ∃ (ι : Type) (F : ι → Subgroup G), (∀ i, CFSG.IsQuasisimple ↥(F i)) ∧ (∀ i, F i ≤ C) ∧
    (∀ i, ∀ g ∈ C, ∀ f ∈ F i, g * f * g⁻¹ ∈ F i) ∧
    ∀ g ∈ C, ∃ z k : G, g = z * k ∧ (∀ c ∈ C, z * c = c * z) ∧ k ∈ ⨆ i, F i

theorem isComponentOf_of_normalized {G : Type} [Group G] {C F : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥F) (hFC : F ≤ C) (hFn : ∀ g ∈ C, ∀ f ∈ F, g * f * g⁻¹ ∈ F) :
    IsComponentOf C F := by
  refine ⟨hFC, hq, ?_⟩
  have hN : (F.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hFn (g : G) g.2 (n : G) hn
    simpa using this⟩
  exact hN.isSubnormal

theorem QuasiFactored.mem_sup_centralizer {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hC : QuasiFactored C) {E : Subgroup G} (hE : IsComponentOf C E) {g : G} (hg : g ∈ C) :
    g ∈ E ⊔ Subgroup.centralizer (E : Set G) := by
  obtain ⟨ι, F, hFq, hFC, hFn, hfac⟩ := hC
  obtain ⟨z, k, hgzk, hzc, hk⟩ := hfac g hg
  exact mem_sup_centralizer_of_factorization F
    (fun i => Or.inr (isComponentOf_of_normalized (hFq i) (hFC i) (hFn i))) hgzk hzc hk hE

end Abstract

section Cen

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (n)

@[expose] def cenSU (P : GL (Fin n) K) : Subgroup ↥(gramSU h (idGram K n)) :=
  (Subgroup.centralizer ({P} : Set (GL (Fin n) K))).comap (gramSU h (idGram K n)).subtype

variable {h n}

theorem mem_cenSU {P : GL (Fin n) K} {g : ↥(gramSU h (idGram K n))} :
    g ∈ cenSU h n P ↔ (g : GL (Fin n) K) * P = P * (g : GL (Fin n) K) := by
  unfold cenSU
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  rfl

theorem primaryData_toLin {P : GL (Fin n) K} (hP : P ∈ primeFormUnitary h (idGram K n)) {c : Kˣ}
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hap : P ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P) := by
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar hpK hap
  have hX : ((Matrix.GeneralLinearGroup.toLin P : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  refine ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n,
    (toLin_mem_sesqUnitaryGroup_iff P).mpr hP, ?_⟩
  rw [hX]
  exact hsq

theorem cenSU_factor [Finite K] {P : GL (Fin n) K}
    (HU : UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P))
    (hq : 2 ≤ ℓ ^ f)
    (hexc : ∀ a : primaryFactors ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      2 ≤ primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]) →
      IsGoodBlock h (Matrix.GeneralLinearGroup.toLin P) a)
    (hsplit : GoodSplitAll h (idForm h n) (Matrix.GeneralLinearGroup.toLin P)) :
    ∃ F : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) //
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin P) a} → Subgroup ↥(gramSU h (idGram K n)),
      (∀ a, CFSG.IsQuasisimple ↥(F a)) ∧ (∀ a, F a ≤ cenSU h n P) ∧
      (∀ a, ∀ g ∈ cenSU h n P, ∀ f ∈ F a, g * f * g⁻¹ ∈ F a) ∧
      ∀ g ∈ cenSU h n P, ∃ z k : ↥(gramSU h (idGram K n)), g = z * k ∧
        (∀ c ∈ cenSU h n P, z * c = c * z) ∧ k ∈ ⨆ a, F a := by
  classical
  set xl : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin P with hxl
  have hSBle : ∀ a : {a : primaryFactors (xl : Module.End K (Fin n → K)) // IsGoodBlock h xl a},
      specialBlock (idForm h n) xl (a.1 : K[X]) ≤ (phiS h (n := n)).range :=
    fun a g hg => mem_range_phiS
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good HU hq a.1 a.2 hg)
  let F : {a : primaryFactors (xl : Module.End K (Fin n → K)) // IsGoodBlock h xl a} →
      Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) xl (a.1 : K[X])).comap (phiS h)
  have hFmap : ∀ a : {a : primaryFactors (xl : Module.End K (Fin n → K)) // IsGoodBlock h xl a},
      (F a).map (phiS h) = specialBlock (idForm h n) xl (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  have hSM : ∀ g : ↥(gramSU h (idGram K n)), g ∈ cenSU h n P →
      phiS h g ∈ unitaryCentralizer (idForm h n) xl := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨phiS_mem_unitary g, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := mem_cenSU.mp hg
    show Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) * Matrix.GeneralLinearGroup.toLin P =
      Matrix.GeneralLinearGroup.toLin P * Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K)
    rw [← map_mul, ← map_mul, this]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro a
    have e : ↥(F a) ≃* ↥(specialBlock (idForm h n) xl (a.1 : K[X])) :=
      (Subgroup.equivMapOfInjective (F a) (phiS h) phiS_injective).trans
        (MulEquiv.subgroupCongr (hFmap a))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((specialBlockFacts_of_good HU hq a.1 a.2).quasisimple a.2.1)
  · intro a g hg
    have hu : phiS h g ∈ unitaryCentralizer (idForm h n) xl :=
      specialBlock_le_unitaryCentralizer (show phiS h g ∈ specialBlock (idForm h n) xl (a.1 : K[X])
        from hg)
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2
    refine mem_cenSU.mpr ?_
    have h1 : Matrix.GeneralLinearGroup.toLin ((g : GL (Fin n) K) * P) =
        Matrix.GeneralLinearGroup.toLin (P * (g : GL (Fin n) K)) := by
      rw [map_mul, map_mul]
      exact this
    exact Matrix.GeneralLinearGroup.toLin.injective h1
  · intro a g hg f' hf'
    have hconj := conj_mem_specialBlock (hSM g hg)
      (show phiS h f' ∈ specialBlock (idForm h n) xl (a.1 : K[X]) from hf')
    change phiS h (g * f' * g⁻¹) ∈ specialBlock (idForm h n) xl (a.1 : K[X])
    rw [map_mul, map_mul, map_inv]
    exact hconj
  · intro g hg
    obtain ⟨z, hzM, hzc, k, hk, hYzk⟩ := exists_central_factor_all HU hq hexc hsplit (hSM g hg)
    have hkle : k ∈ (phiS h (n := n)).range :=
      (iSup_le fun a : {a : primaryFactors (xl : Module.End K (Fin n → K)) //
        IsGoodBlock h xl a} => hSBle a) hk
    have hzle : z ∈ (phiS h (n := n)).range := by
      have : z = phiS h g * k⁻¹ := by rw [hYzk]; simp
      rw [this]
      exact mul_mem ⟨g, rfl⟩ (inv_mem hkle)
    obtain ⟨zS, hzS⟩ := hzle
    obtain ⟨kS, hkS⟩ := hkle
    have hYeq : g = zS * kS := phiS_injective (by rw [map_mul, hzS, hkS, hYzk])
    refine ⟨zS, kS, hYeq, fun G hG => ?_, ?_⟩
    · apply phiS_injective
      rw [map_mul, map_mul, hzS]
      exact (hzc _ (hSM G hG)).eq
    · have hmapsup : (⨆ a : {a : primaryFactors (xl : Module.End K (Fin n → K)) //
          IsGoodBlock h xl a}, F a).map (phiS h) =
          ⨆ a : {a : primaryFactors (xl : Module.End K (Fin n → K)) // IsGoodBlock h xl a},
            specialBlock (idForm h n) xl (a.1 : K[X]) := by
        rw [Subgroup.map_iSup]
        exact iSup_congr hFmap
      have hk2 : phiS h kS ∈ (⨆ a : {a : primaryFactors (xl : Module.End K (Fin n → K)) //
          IsGoodBlock h xl a}, F a).map (phiS h) := by
        rw [hmapsup, hkS]
        exact hk
      obtain ⟨s, hs, hs'⟩ := hk2
      have : s = kS := phiS_injective hs'
      rw [← this]
      exact hs

theorem cenSU_quasiFactored [Finite K] {P : GL (Fin n) K}
    (HU : UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P))
    (hq : 2 ≤ ℓ ^ f)
    (hexc : ∀ a : primaryFactors ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      2 ≤ primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]) →
      IsGoodBlock h (Matrix.GeneralLinearGroup.toLin P) a)
    (hsplit : GoodSplitAll h (idForm h n) (Matrix.GeneralLinearGroup.toLin P)) :
    QuasiFactored (cenSU h n P) := by
  obtain ⟨F, hFq, hFC, hFn, hfac⟩ := cenSU_factor HU hq hexc hsplit
  exact ⟨_, F, hFq, hFC, hFn, hfac⟩

theorem cenSU_comm_of_mult_le_one [Finite K] {P : GL (Fin n) K}
    (HU : UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P))
    (hq : 2 ≤ ℓ ^ f)
    (hm : ∀ a : primaryFactors ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin P :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]) ≤ 1) :
    ∀ a b : ↥(gramSU h (idGram K n)), a ∈ cenSU h n P → b ∈ cenSU h n P → a * b = b * a := by
  have hnot : ∀ a : primaryFactors ((Matrix.GeneralLinearGroup.toLin P :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      ¬ IsGoodBlock h (Matrix.GeneralLinearGroup.toLin P) a := fun a ha => by
    have := ha.1
    have := hm a
    omega
  obtain ⟨F, -, -, -, hfac⟩ := cenSU_factor HU hq (fun a h2 => absurd h2 (by have := hm a; omega))
    (fun a ha => absurd ha (hnot a))
  intro a b ha hb
  obtain ⟨z, k, hgzk, hzc, hk⟩ := hfac a ha
  have hk1 : k = 1 := by
    have : (⨆ i, F i : Subgroup ↥(gramSU h (idGram K n))) = ⊥ := by
      refine iSup_eq_bot.mpr fun i => absurd i.2 (hnot i.1)
    rw [this, Subgroup.mem_bot] at hk
    exact hk
  rw [hk1, mul_one] at hgzk
  rw [hgzk]
  exact hzc b hb

end Cen

end CFSG.RankThree.PartOne.FOC
