module

public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.LieType.Steinberg.Adjoint.BaseChange

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.ClassicalInvolution.Upgrade CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg

private theorem irgTS_entrywiseCongr_D {τ : Tag}
    (F : RootOperatorFamily τ)
    {K L : Type} [Field K] [Field L] (φ : K →+* L) (α : Root τ) (k : ℕ) :
    entrywiseCongr φ (F.D K α k) = F.D L α k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single]
  exact BaseChange.D F α k b

private theorem irgTS_entrywiseCongr_zero {τ : Tag}
    {K L : Type} [Field K] [Field L] (φ : K →+* L) :
    entrywiseCongr φ (0 : Module.End K (RootModule τ K)) = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rw [entrywiseCongr_single]
  simp

private theorem irgTS_entrywiseCongr_add {τ : Tag}
    {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (A B : Module.End K (RootModule τ K)) :
    entrywiseCongr φ (A + B) = entrywiseCongr φ A + entrywiseCongr φ B := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply]
  rw [entrywiseCongr_single, entrywiseCongr_single, entrywiseCongr_single]
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add φ)]

private theorem irgTS_entrywiseCongr_smul {τ : Tag}
    {K L : Type} [Field K] [Field L] (φ : K →+* L) (r : K)
    (A : Module.End K (RootModule τ K)) :
    entrywiseCongr φ (r • A) = φ r • entrywiseCongr φ A := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply]
  rw [entrywiseCongr_single, entrywiseCongr_single]
  rw [LinearMap.smul_apply, mapRange_smul_semi]

private theorem irgTS_entrywiseCongr_elt {τ : Tag}
    (F : RootOperatorFamily τ)
    {K L : Type} [Field K] [Field L] (φ : K →+* L) (α : Root τ) (c : K) :
    entrywiseCongr φ (F.elt K α c) = F.elt L α (φ c) := by
  let g : Module.End K (RootModule τ K) →+ Module.End L (RootModule τ L) :=
    { toFun := entrywiseCongr φ
      map_zero' := irgTS_entrywiseCongr_zero φ
      map_add' := irgTS_entrywiseCongr_add φ }
  rw [RootOperatorFamily.elt, RootOperatorFamily.elt]
  change g (∑ k ∈ Finset.range 4, c ^ k • F.D K α k) =
    ∑ k ∈ Finset.range 4, (φ c) ^ k • F.D L α k
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show entrywiseCongr φ (c ^ k • F.D K α k) = (φ c) ^ k • F.D L α k
  rw [irgTS_entrywiseCongr_smul, irgTS_entrywiseCongr_D, map_pow]

private noncomputable def irgTS_adjCongr {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    adjointGroup d4 K ≃* adjointGroup d4 L :=
  (Subgroup.equivMapOfInjective (adjointGroup d4 K) (modGLCongr d4 e).toMonoidHom
      (modGLCongr d4 e).injective).trans
    (MulEquiv.subgroupCongr (map_adjointGroup d4 e))

private theorem irgTS_adjCongr_apply {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (x : adjointGroup d4 K) :
    ((irgTS_adjCongr e x : adjointGroup d4 L) : ModGL d4 L) =
      modGLCongr d4 e (x : ModGL d4 K) := rfl

private theorem irgTS_adjCongr_eltElement {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (α : Root d4) (c : K) :
    irgTS_adjCongr e ((rootOperatorFamily d4).eltElement α c) =
      (rootOperatorFamily d4).eltElement α (e c) := by
  apply Subtype.ext
  apply Units.ext
  rw [irgTS_adjCongr_apply, coe_modGLCongr]
  change entrywiseCongr e.toRingHom ((rootOperatorFamily d4).elt K α c) =
    (rootOperatorFamily d4).elt L α (e c)
  exact irgTS_entrywiseCongr_elt (rootOperatorFamily d4) e.toRingHom α c

private theorem irgTS_adjCongr_xPar {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (γ : Fin d4.rank → ℤ) (c : K) :
    irgTS_adjCongr e (xPar (rootOperatorFamily d4) γ c) =
      xPar (rootOperatorFamily d4) γ (e c) := by
  by_cases hγ : IsRoot d4 γ
  · rw [xPar_of_isRoot hγ, xPar_of_isRoot hγ]
    exact irgTS_adjCongr_eltElement e ⟨γ, hγ⟩ c
  · rw [xPar_of_not_isRoot hγ, xPar_of_not_isRoot hγ, map_one]

private theorem irgTS_adjCongr_twistC {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {σK : K →+* K} {σL : L →+* L} (hσ : ∀ c, e (σK c) = σL (e c)) (g : adjointGroup d4 K) :
    irgTS_adjCongr e (twistC .D4 K σK g) = twistC .D4 L σL (irgTS_adjCongr e g) := by
  apply Subtype.ext
  rw [irgTS_adjCongr_apply, coe_twistC, coe_twistC, irgTS_adjCongr_apply]
  exact modGLCongr_twistHom .D4 e σK σL hσ (g : ModGL d4 K)

private theorem irgTS_map_rootGroup_adjCongr {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    (rootGroup (rootOperatorFamily d4) K γ).map (irgTS_adjCongr e).toMonoidHom =
      rootGroup (rootOperatorFamily d4) L γ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ x).1 hx
    exact (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ _).2
      ⟨e c, (irgTS_adjCongr_xPar e γ c).symm⟩
  · intro y hy
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ y).1 hy
    refine ⟨xPar (rootOperatorFamily d4) γ (e.symm d), xPar_mem hγ _, ?_⟩
    show irgTS_adjCongr e (xPar (rootOperatorFamily d4) γ (e.symm d)) =
      xPar (rootOperatorFamily d4) γ d
    rw [irgTS_adjCongr_xPar, RingEquiv.apply_symm_apply]

private theorem irgTS_map_twistedRootSubgroup {ι κ G G' : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Group G] [Group G']
    {Φ : Set (ι → ℤ)} {o : ι → κ} {X : (ι → ℤ) → Subgroup G}
    {X' : (ι → ℤ) → Subgroup G'} (T : G ≃* G')
    (hX : ∀ α ∈ Φ, (X α).map T.toMonoidHom = X' α)
    {σ : G →* G} {σ' : G' →* G'} (hσ : ∀ g, T (σ g) = σ' (T g)) (β : κ → ℤ) :
    (twistedRootSubgroup Φ o X σ β).map T.toMonoidHom =
      twistedRootSubgroup Φ o X' σ' β := by
  unfold twistedRootSubgroup
  rw [Subgroup.map_inf _ _ _ T.injective]
  congr 1
  · rw [Subgroup.map_iSup T.toMonoidHom]
    refine iSup_congr fun α => ?_
    rw [Subgroup.map_iSup T.toMonoidHom]
    refine iSup_congr fun hα => ?_
    rw [Subgroup.map_iSup T.toMonoidHom]
    exact iSup_congr fun _ => hX α hα
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show σ' (T x) = T x
      rw [← hσ, hx]
      rfl
    · intro hy
      refine ⟨T.symm y, ?_, by simp⟩
      show σ (T.symm y) = T.symm y
      apply T.injective
      rw [hσ, T.apply_symm_apply, hy]
      rfl

private theorem irgTS_map_twistedRootSubgroupD4 {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {σK : K →+* K} {σL : L →+* L}
    (hσ : ∀ c, e (σK c) = σL (e c)) (β : Fin (Tag.rank .G2) → ℤ) :
    (twistedRootSubgroupD4 σK β).map (irgTS_adjCongr e).toMonoidHom =
      twistedRootSubgroupD4 σL β := by
  unfold twistedRootSubgroupD4
  exact irgTS_map_twistedRootSubgroup (T := irgTS_adjCongr e) (Φ := {α | IsRoot d4 α})
    (o := orbitMap) (X := rootGroup (rootOperatorFamily d4) K)
    (X' := rootGroup (rootOperatorFamily d4) L)
    (σ := twistC .D4 K σK) (σ' := twistC .D4 L σL)
    (fun α hα => irgTS_map_rootGroup_adjCongr e (γ := α) hα)
    (fun g => irgTS_adjCongr_twistC e hσ g) β

private theorem irgTS_map_twistedGroup {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {σK : K →+* K} {σL : L →+* L}
    (hσ : ∀ c, e (σK c) = σL (e c)) :
    (twistedGroup σK).map (irgTS_adjCongr e).toMonoidHom = twistedGroup σL := by
  unfold twistedGroup
  rw [Subgroup.map_iSup (irgTS_adjCongr e).toMonoidHom]
  refine iSup_congr fun β => ?_
  rw [Subgroup.map_iSup (irgTS_adjCongr e).toMonoidHom]
  exact iSup_congr fun _ => irgTS_map_twistedRootSubgroupD4 e hσ β

noncomputable def irgTS_twistedCongr {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {σK : K →+* K} {σL : L →+* L}
    (hσ : ∀ c, e (σK c) = σL (e c)) : twistedGroup σK ≃* twistedGroup σL :=
  (Subgroup.equivMapOfInjective (twistedGroup σK) (irgTS_adjCongr e).toMonoidHom
      (irgTS_adjCongr e).injective).trans
    (MulEquiv.subgroupCongr (irgTS_map_twistedGroup e hσ))

theorem irgTS_exists_rootCompat_equiv {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {σK : K →+* K} {σL : L →+* L}
    (hσ : ∀ c, e (σK c) = σL (e c)) :
    ∀ β, IsRoot .G2 β →
      (twistedRootGroup σK β).map (irgTS_twistedCongr e hσ).toMonoidHom =
        twistedRootGroup σL β := by
  intro β hβ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (x : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σK β at hx
    change ((irgTS_twistedCongr e hσ) x : adjointGroup d4 L) ∈
      twistedRootSubgroupD4 σL β
    have hcoe : (((irgTS_twistedCongr e hσ) x : twistedGroup σL) : adjointGroup d4 L) =
        irgTS_adjCongr e (x : adjointGroup d4 K) := rfl
    rw [hcoe, ← irgTS_map_twistedRootSubgroupD4 e hσ β]
    exact Subgroup.mem_map_of_mem (irgTS_adjCongr e).toMonoidHom hx
  · intro y hy
    change (y : adjointGroup d4 L) ∈ twistedRootSubgroupD4 σL β at hy
    rw [← irgTS_map_twistedRootSubgroupD4 e hσ β] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨(irgTS_twistedCongr e hσ).symm y, ?_, by simp⟩
    change (((irgTS_twistedCongr e hσ).symm y : twistedGroup σK) :
        adjointGroup d4 K) ∈ twistedRootSubgroupD4 σK β
    have hcoe : ((((irgTS_twistedCongr e hσ).symm y : twistedGroup σK) :
        adjointGroup d4 K)) = (irgTS_adjCongr e).symm (y : adjointGroup d4 L) := by
      apply (irgTS_adjCongr e).injective
      rw [MulEquiv.apply_symm_apply,
        ← show (((irgTS_twistedCongr e hσ) ((irgTS_twistedCongr e hσ).symm y) :
            twistedGroup σL) : adjointGroup d4 L) =
          irgTS_adjCongr e (((irgTS_twistedCongr e hσ).symm y : twistedGroup σK) :
            adjointGroup d4 K) from rfl]
      rw [MulEquiv.apply_symm_apply]
    rw [hcoe, ← hzy]
    exact (MulEquiv.symm_apply_apply (irgTS_adjCongr e) z).symm ▸ hz

end CFSG.StandardType.RCKRP
