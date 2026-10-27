module

public import CFSG.LocalAnalysis.WeakClosure81.W183Ker182A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem kerMV_isSolvable_182 (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i) :
    Group.IsSolvable ↥(kerMV V H) := by
  obtain ⟨hOK, -⟩ := c.exists_component182_ker_AS h172 h5_4 h5_11 h5_13 h2
  rw [← hOK, OInf]
  exact @CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv _ _
    _ _ (Subgroup.equivMapOfInjective (CFSG.solvableRadical ↥H) H.subtype H.subtype_injective)
    (CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical)

private theorem w183_perfSocleMod_map {Y Y' : Type*} [Group Y] [Group Y']
    {Kk F : Subgroup Y} (h : PerfSocleMod Kk F) (π : Y →* Y')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Kk) :
    PerfSocleMod (Kk.map π) (F.map π) := by
  have hmem : ∀ x : Y, π x ∈ Kk.map π ↔ x ∈ Kk := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      have hmem' : k⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      have h2 := Kk.mul_mem hk (hker hmem')
      simpa using h2
    · intro hx
      exact Subgroup.mem_map_of_mem π hx
  refine
    { normal_left := h.normal_left.map π hπ
      normal_right := h.normal_right.map π hπ
      le := Subgroup.map_mono h.le
      perfect := ?_
      not_le := ?_
      centralizer_le := ?_ }
  · calc F.map π ≤ (⁅F, F⁆ ⊔ Kk).map π := Subgroup.map_mono h.perfect
      _ = ⁅F, F⁆.map π ⊔ Kk.map π := Subgroup.map_sup _ _ _
      _ = ⁅F.map π, F.map π⁆ ⊔ Kk.map π := by rw [Subgroup.map_commutator]
  · intro hFK
    exact h.not_le fun f hf => (hmem f).1 (hFK (Subgroup.mem_map_of_mem π hf))
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hπ y'
    refine (hmem y).2 (h.centralizer_le y fun f hf => (hmem _).1 ?_)
    rw [map_commutatorElement]
    exact hy' (π f) (Subgroup.mem_map_of_mem π hf)

private theorem w183_generalizedFitting_eq_layer {Q : Type*} [Group Q] [Finite Q]
    (h : CFSG.solvableRadical Q = ⊥) : CFSG.generalizedFitting Q = CFSG.layer Q := by
  have hfit : CFSG.fittingSubgroup Q = ⊥ := by
    rw [eq_bot_iff, ← h]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (CFSG.LocalCores.fitting_nilpotent (G := Q)).2.1 inferInstance
  rw [CFSG.generalizedFitting.eq_sup, hfit, bot_sup_eq]

private theorem w183_perfSocleMod_of_component182 (hOK : OInf H = kerMV V H)
    {L : Subgroup G} (hL : IsComponentModN (kerMV V H) H L) :
    ∃ Kk F : Subgroup ↥H, PerfSocleMod Kk F ∧
      Kk = (kerMV V H).subgroupOf H ∧
      ∀ j : ↥H, j ∈ Kk ↔ (j : G) ∈ kerMV V H := by
  let K₀ : Subgroup ↥H := (kerMV V H).subgroupOf H
  have hK₀eq : K₀ = CFSG.solvableRadical ↥H := by
    show ((kerMV V H).subgroupOf H) = CFSG.solvableRadical ↥H
    rw [← hOK, OInf]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  haveI hK₀n : K₀.Normal := by
    rw [hK₀eq]
    infer_instance
  let Q := ↥H ⧸ K₀
  let μ : ↥H →* Q := QuotientGroup.mk' K₀
  haveI hK₀solv : Group.IsSolvable K₀ := by
    rw [hK₀eq]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  haveI hRsolv : Group.IsSolvable (CFSG.solvableRadical Q) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hsol : CFSG.solvableRadical Q = ⊥ := by
    have hcomap : Group.IsSolvable ((CFSG.solvableRadical Q).comap μ) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_comap_mk' (R := K₀)
        (N := CFSG.solvableRadical Q)
    have hleS : (CFSG.solvableRadical Q).comap μ ≤ CFSG.solvableRadical ↥H :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
        (Subgroup.Normal.comap inferInstance μ) hcomap
    have hle : (CFSG.solvableRadical Q).comap μ ≤ K₀ :=
      hleS.trans (le_of_eq hK₀eq.symm)
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K₀ q
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr (hle hq)
  have hlayerbot : CFSG.layer Q ≠ ⊥ := by
    intro hlayer
    have hgen := w183_generalizedFitting_eq_layer hsol
    have hcent : (⊤ : Subgroup Q) ≤ ⊥ := by
      have hgenbot : CFSG.generalizedFitting Q = ⊥ := by rw [hgen, hlayer]
      have hcentbot : Subgroup.centralizer (↑(⊥ : Subgroup Q) : Set Q) = ⊤ := by
        rw [Subgroup.centralizer_eq_top_iff_subset]
        simp
      calc (⊤ : Subgroup Q) = Subgroup.centralizer (↑(⊥ : Subgroup Q) : Set Q) :=
            hcentbot.symm
        _ = Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q) := by rw [hgenbot]
        _ ≤ CFSG.generalizedFitting Q := CFSG.centralizer_generalizedFitting_le Q
        _ = ⊥ := hgenbot
    haveI : Subsingleton Q := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup Q) := hcent (Subgroup.mem_top a)
      have hb : b ∈ (⊥ : Subgroup Q) := hcent (Subgroup.mem_top b)
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hKtop : K₀ = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton K₀ inferInstance
    obtain ⟨X, instX, φ, hφs, hφk, hX⟩ := hL.2.2.2.2
    haveI : Finite X := Finite.of_surjective φ hφs
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hX
    have hsub : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨l, rfl⟩ := hφs a
      obtain ⟨l', rfl⟩ := hφs b
      have hl : (⟨(l : G), hL.2.2.1 l.2⟩ : ↥H) ∈ K₀ := by
        rw [hKtop]
        exact Subgroup.mem_top _
      have hl' : (⟨(l' : G), hL.2.2.1 l'.2⟩ : ↥H) ∈ K₀ := by
        rw [hKtop]
        exact Subgroup.mem_top _
      have h1 : (l : G) ∈ kerMV V H := Subgroup.mem_subgroupOf.mp hl
      have h2 : (l' : G) ∈ kerMV V H := Subgroup.mem_subgroupOf.mp hl'
      rw [(hφk l).mpr h1, (hφk l').mpr h2]
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
  let F₀ : Subgroup ↥H := (CFSG.layer Q).comap μ
  have hμF : F₀.map μ = CFSG.layer Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K₀) _
  have hμK : K₀.map μ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, show μ.ker = K₀ from QuotientGroup.ker_mk' K₀]
  refine ⟨K₀, F₀, ?_, rfl, fun j => Subgroup.mem_subgroupOf⟩
  haveI hchar : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  refine
    { normal_left := hK₀n
      normal_right := Subgroup.Normal.comap inferInstance μ
      le := ?_
      perfect := ?_
      not_le := ?_
      centralizer_le := ?_ }
  · intro x hx
    rw [Subgroup.mem_comap, show μ x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  · have hmap : F₀.map μ ≤ ⁅F₀, F₀⁆.map μ := by
      rw [hμF, Subgroup.map_commutator, hμF, CFSG.LocalCores.layer_perfect]
    have hmap' := (Subgroup.map_le_map_iff (f := μ)).mp hmap
    rwa [show μ.ker = K₀ from QuotientGroup.ker_mk' K₀] at hmap' 
  · intro hFK
    apply hlayerbot
    have hle : CFSG.layer Q ≤ (⊥ : Subgroup Q) := by
      rw [← hμF, ← hμK]
      exact Subgroup.map_mono hFK
    rwa [le_bot_iff] at hle
  · intro y hy
    have hcent : μ y ∈ Subgroup.centralizer (CFSG.layer Q : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp (hμF ▸ hq)
      have h2 : μ ⁅y, f⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hy f hf)
      rw [map_commutatorElement] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
    have hz : μ y = 1 := by
      rw [← Subgroup.mem_bot, ← CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot
        hsol]
      exact hcent
    exact (QuotientGroup.eq_one_iff y).mp hz

theorem exists_perfSocleMod_182 (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i)
    (M : ModDataE H (eOmegaZ H D.T)) :
    ∃ Kk F : Subgroup ↥(M.img H), PerfSocleMod Kk F ∧
      ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
        (r ∈ Kk ↔ (j : G) ∈ kerMV V H) := by
  obtain ⟨hOK, L, hL, -, -⟩ := c.exists_component182_ker_AS h172 h5_4 h5_11 h5_13 h2
  obtain ⟨K₀, F₀, hsoc, -, hK₀mem⟩ := w183_perfSocleMod_of_component182 hOK hL
  obtain ⟨π, hπs, hπval, hπk⟩ := M.exists_surjective_img
  have hker' : π.ker ≤ K₀ := by
    intro j hj
    rw [MonoidHom.mem_ker, hπk] at hj
    exact (hK₀mem j).2 (c.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨j.2, hj⟩)
  refine ⟨K₀.map π, F₀.map π, w183_perfSocleMod_map hsoc π hπs hker', ?_⟩
  intro j r hr
  have hrj : r = π j := Subtype.ext (hr.trans (hπval j).symm)
  rw [hrj]
  constructor
  · intro hmem
    obtain ⟨j', hj'K, hj'⟩ := Subgroup.mem_map.mp hmem
    have hjj : j'⁻¹ * j ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hj', inv_mul_cancel]
    have h1 : j'⁻¹ * j ∈ K₀ := hker' hjj
    have h2 : j ∈ K₀ := by
      have := K₀.mul_mem hj'K h1
      simpa using this
    exact (hK₀mem j).1 h2
  · intro hjK
    exact Subgroup.mem_map_of_mem π ((hK₀mem j).2 hjK)

theorem kernSetting_of_minCex_182 {j : ℕ} (hB : ListBNonabelian) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {Kk F : Subgroup ↥(M.img H)} (hsoc : PerfSocleMod Kk F)
    (hK : Group.IsSolvable ↥(kerMV V H))
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H)) :
    KernSetting Kk F (opResidual 2 (⊤ : Subgroup ↥(M.img H))) where
  socle := hsoc
  solvable := isSolvable_kk M (kerMV_le_self V H) hKk hK
  o2_eq_bot := eq_bot_of_pCoreOf_eq_bot (x.pCoreOf_img_eq_bot M)
  normal := opResidual_top_props.1
  two_quotient := opResidual_top_props.2.1
  le_of_not_le := fun _ hN hNK =>
    opResidual_top_props.2.2 _ (c.two_quotient_img_zero hB h2 M hKk hN hNK)

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
