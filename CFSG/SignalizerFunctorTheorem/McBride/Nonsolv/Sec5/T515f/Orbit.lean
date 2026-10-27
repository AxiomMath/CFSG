module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem kOf_le_normalizer_orbitClosure {B G J : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    kOf G ≤ Subgroup.normalizer (orbitClosure J B : Set Γ) := by
  rw [← (isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ).sup_eq]
  exact sup_le Subgroup.le_normalizer
    ((outsideOrbit_le_centralizer hBG hsol hJ).trans (Subgroup.centralizer_le_normalizer _))

theorem smear_le_kOf_inf_centralizer {B G J : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    smear J B ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ) :=
  le_inf ((smear_le_orbitClosure J B).trans (orbitClosure_le_kOf hBG hsol hJ))
    (smear_le_centralizer J B)

omit [Finite Γ] in
theorem kOf_inf_centralizer_le {B : Subgroup Γ} (G : Subgroup Γ) :
    kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤ G ⊓ Subgroup.centralizer (B : Set Γ) :=
  inf_le_inf_right _ (kOf_le G)

theorem normal_smear_subgroupOf {B G J : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    ((smear J B).subgroupOf (kOf G ⊓ Subgroup.centralizer (B : Set Γ))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (smear_le_kOf_inf_centralizer hBG hsol hJ)]
  intro t u ht hu
  obtain ⟨huK, huC⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨htL, htC⟩ := Subgroup.mem_inf.mp ht
  exact Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (kOf_le_normalizer_orbitClosure hBG hsol hJ huK) t).mp htL,
      mul_mem (mul_mem huC htC) (inv_mem huC)⟩

theorem normal_kOf_inf_centralizer_subgroupOf (G B : Subgroup Γ) :
    ((kOf G ⊓ Subgroup.centralizer (B : Set Γ)).subgroupOf
      (G ⊓ Subgroup.centralizer (B : Set Γ))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (kOf_inf_centralizer_le G)]
  intro u v hu hv
  obtain ⟨huK, huC⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hvG, hvC⟩ := Subgroup.mem_inf.mp hv
  exact Subgroup.mem_inf.mpr
    ⟨conj_mem_kOf (Subgroup.le_normalizer hvG) huK, mul_mem (mul_mem hvC huC) (inv_mem hvC)⟩

theorem pairProj_mem_smear {B G J : Subgroup Γ} (hBG : B ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) {u : Γ}
    (hu : u ∈ kOf G ⊓ Subgroup.centralizer (B : Set Γ)) :
    ((pairProj (isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ)
      ⟨u, (Subgroup.mem_inf.mp hu).1⟩ : orbitClosure J B) : Γ) ∈ smear J B := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ
  obtain ⟨m, hm, hum⟩ := pairProj_spec hdp ⟨u, (Subgroup.mem_inf.mp hu).1⟩
  set l : orbitClosure J B := pairProj hdp ⟨u, (Subgroup.mem_inf.mp hu).1⟩ with hl
  have hum' : (l : Γ) * m = u := hum
  refine Subgroup.mem_inf.mpr ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hbl : b * (l : Γ) * b⁻¹ ∈ orbitClosure J B :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_orbitClosure hb) l).mp l.2
  have hbm : b * m * b⁻¹ ∈ outsideOrbit G B J :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_outsideOrbit hBG hb) m).mp hm
  have hub : b * u = u * b := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 b hb
  have heq : (b * (l : Γ) * b⁻¹) * (b * m * b⁻¹) = (l : Γ) * m := by
    calc (b * (l : Γ) * b⁻¹) * (b * m * b⁻¹) = b * ((l : Γ) * m) * b⁻¹ := by group
      _ = b * u * b⁻¹ := by rw [hum']
      _ = (l : Γ) * m := by rw [hub, mul_inv_cancel_right, hum']
  have := (eq_of_mul_eq_of_isDirectPair hdp hbl l.2 hbm hm heq).1
  calc b * (l : Γ) = b * (l : Γ) * b⁻¹ * b := by group
    _ = (l : Γ) * b := by rw [this]

theorem le_outsideOrbit_of_le_centralizer_smear {B G J F : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hFU : F ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ)) (hFs : IsSimpleGroup F)
    (hFnc : ¬ IsMulCommutative F) (hFc : F ≤ Subgroup.centralizer (smear J B : Set Γ)) :
    F ≤ outsideOrbit G B J := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ
  have hFK : F ≤ kOf G := hFU.trans inf_le_left
  have hπ : ∀ f : F, ((pairProj hdp ⟨f, hFK f.2⟩ : orbitClosure J B) : Γ) ∈ smear J B :=
    fun f => pairProj_mem_smear hBG hsol hJ (hFU f.2)
  let φ : ↥F →* ↥(orbitClosure J B) := (pairProj hdp).comp (Subgroup.inclusion hFK)
  have hφ : ∀ x y : F, φ x * φ y = φ y * φ x := by
    intro x y
    have hy : ((φ y : orbitClosure J B) : Γ) ∈ kOf G := hdp.sup_eq ▸
      Subgroup.mem_sup_left (φ y).2
    have hc : ((φ y : orbitClosure J B) : Γ) * (x : Γ) = (x : Γ) * (φ y : Γ) :=
      Subgroup.mem_centralizer_iff.mp (hFc x.2) _ (hπ y)
    have hc' : (⟨(φ y : Γ), hy⟩ : kOf G) * ⟨x, hFK x.2⟩ = ⟨x, hFK x.2⟩ * ⟨(φ y : Γ), hy⟩ :=
      Subtype.ext hc
    have h1 := congrArg (pairProj hdp) hc'
    rw [map_mul, map_mul] at h1
    have h2 : pairProj hdp ⟨(φ y : Γ), hy⟩ = φ y :=
      Subtype.ext (pairProj_of_mem_left hdp (φ y).2 hy)
    rw [h2] at h1
    exact h1.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  · exfalso
    refine hFnc (isMulCommutative_iff.mpr fun x y => ?_)
    refine (MonoidHom.ker_eq_bot_iff φ).mp hker ?_
    rw [map_mul, map_mul]
    exact hφ x y
  · intro f hf
    have h1 : φ ⟨f, hf⟩ = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)
    obtain ⟨m, hm, hfm⟩ := pairProj_spec hdp ⟨f, hFK hf⟩
    have h2 : pairProj hdp ⟨f, hFK hf⟩ = 1 := h1
    rw [h2, Subgroup.coe_one, one_mul] at hfm
    have hfm' : f = m := hfm.symm
    rw [hfm']
    exact hm

theorem eq_bot_of_forall_le_outsideOrbit {B G F : Subgroup Γ} (hsol : sol G = ⊥)
    (hFK : F ≤ kOf G) (h : ∀ J ∈ lcal G, F ≤ outsideOrbit G B J) : F = ⊥ := by
  have hK := isDirectProduct_lcal_kOf hsol
  refine eq_bot_iff.mpr fun f hf => ?_
  have h1 : (⟨f, hFK hf⟩ : kOf G) = 1 := by
    refine hK.ext_coord fun J hJ => ?_
    rw [map_one, hK.coord_eq_one_iff hJ]
    exact sSup_le_sSup
      (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr (self_mem_conjOrbit B J)))
      (h J hJ hf)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

theorem inf_orbitClosure_eq_bot_of_not_mem_conjOrbit {B G J J' : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hJ' : J' ∈ lcal G) (h : J' ∉ conjOrbit B J) :
    orbitClosure J B ⊓ orbitClosure J' B = ⊥ := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ
  have hle : orbitClosure J' B ≤ outsideOrbit G B J := by
    rw [orbitClosure_eq_sSup]
    refine sSup_le_sSup fun K hK => ⟨conjOrbit_subset_lcal hBG hJ' hK, fun hKJ => h ?_⟩
    obtain ⟨b, hb, rfl⟩ := hK
    have := map_conj_mem_conjOrbit hKJ (inv_mem hb)
    rwa [map_conj_map_conj_inv] at this
  exact eq_bot_iff.mpr ((inf_le_inf_left _ hle).trans hdp.inf_eq_bot.le)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f
