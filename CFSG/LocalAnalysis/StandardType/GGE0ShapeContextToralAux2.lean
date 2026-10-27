module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToralAux
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeRealConj
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeToralityA5
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeToralPlane
public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.HardMathSupport.Timmesfeld.Torality.ToralPairOne
public import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem mem_contextImage_aux {G : Type} [Group G] {G0 H : Subgroup G}
    {φ : MulAut G0} :
    φ ∈ contextImage G0 H ↔
      ∃ n : Subgroup.normalizer (G0 : Set G), (n : G) ∈ H ∧
        Subgroup.normalizerMonoidHom G0 n = φ := by
  rw [contextImage, Subgroup.mem_map]
  simp only [Subgroup.mem_comap]
  exact Iff.rfl

private theorem contextImage_eq_map_conj_aux {G : Type} [Group G] {G0 H : Subgroup G}
    (hH : H ≤ G0) :
    contextImage G0 H =
      (H.subgroupOf G0).map (MulAut.conj : ↥G0 →* MulAut ↥G0) := by
  ext φ
  simp only [contextImage, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨n, hnH, hφ⟩
    refine ⟨⟨(n : G), hH hnH⟩, Subgroup.mem_subgroupOf.mpr hnH, ?_⟩
    rw [← hφ]
    ext x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe G0 n x
  · rintro ⟨a, ha, hφ⟩
    have haH : (a : G) ∈ H := Subgroup.mem_subgroupOf.mp ha
    refine ⟨⟨(a : G), Subgroup.le_normalizer (hH haH)⟩, haH, ?_⟩
    rw [← hφ]
    ext x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    rfl

private theorem realizedSubgroup_map_conj_aux {G : Type} [Group G] {G0 H : Subgroup G}
    {L : Type} [Field L] [IsAlgClosed L]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I L) :
    realizedSubgroup R ((H.subgroupOf G0).map (MulAut.conj : ↥G0 →* MulAut ↥G0)) =
      (H.subgroupOf G0).map (R.setup.Γ.subtype.comp R.groupEquiv.toMonoidHom) := by
  ext x
  simp only [realizedSubgroup, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨h, hh, hhφ⟩ := hφ
    refine ⟨h, hh, ?_⟩
    have hφeq : φ = ⟨MulAut.conj h, R.inner_le ⟨h, rfl⟩⟩ := Subtype.ext hhφ.symm
    rw [hφeq, R.inner_compatible h]
    rfl
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨MulAut.conj h, R.inner_le ⟨h, rfl⟩⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hh), R.inner_compatible h⟩

private theorem realizedSubgroup_contextImage_aux {G : Type} [Group G] {G0 H : Subgroup G}
    {L : Type} [Field L] [IsAlgClosed L]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I L) (hH : H ≤ G0) :
    realizedSubgroup R (contextImage G0 H) =
      (H.subgroupOf G0).map (R.setup.Γ.subtype.comp R.groupEquiv.toMonoidHom) := by
  rw [contextImage_eq_map_conj_aux hH, realizedSubgroup_map_conj_aux]

private theorem map_subgroupOf_centralizer_eq_aux {G : Type} [Group G] {G0 D : Subgroup G}
    {L : Type} [Field L] [IsAlgClosed L]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I L)
    (hDI : contextImage G0 D ≤ I) (hDN : D ≤ Subgroup.normalizer (G0 : Set G)) :
    ((G0 ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G0).map
        (R.setup.Γ.subtype.comp R.groupEquiv.toMonoidHom) =
      R.setup.Γ ⊓ Subgroup.centralizer
        (realizedSubgroup R (contextImage G0 D) : Set (ModGL .E6 L)) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨(R.groupEquiv x).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz
    simp only [realizedSubgroup, SetLike.mem_coe, Subgroup.mem_map] at hz
    obtain ⟨φ, hφ, rfl⟩ := hz
    have hφD : φ.1 ∈ contextImage G0 D := Subgroup.mem_comap.mp hφ
    rw [mem_contextImage_aux] at hφD
    obtain ⟨n, hnD, hnφ⟩ := hφD
    have hxD : (x : G) ∈ Subgroup.centralizer (D : Set G) := (Subgroup.mem_subgroupOf.mp hx).2
    have hcomm : (n : G) * (x : G) = (x : G) * (n : G) :=
      (Subgroup.mem_centralizer_iff.mp hxD) (n : G) hnD
    have hfix : φ.1 x = x := by
      rw [← hnφ]
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcomm]
      group
    have hconj : R.action φ * (R.groupEquiv x : ModGL .E6 L) * (R.action φ)⁻¹ =
        (R.groupEquiv x : ModGL .E6 L) := by
      rw [← R.compatible φ x, hfix]
    change R.action φ * (R.groupEquiv x : ModGL .E6 L) =
      (R.groupEquiv x : ModGL .E6 L) * R.action φ
    calc R.action φ * (R.groupEquiv x : ModGL .E6 L)
        = R.action φ * (R.groupEquiv x : ModGL .E6 L) * (R.action φ)⁻¹ * R.action φ := by
          group
      _ = (R.groupEquiv x : ModGL .E6 L) * R.action φ := by rw [hconj]
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyΓ, hyC⟩ := hy
    let x : G0 := R.groupEquiv.symm ⟨y, hyΓ⟩
    have hfx : (R.setup.Γ.subtype.comp R.groupEquiv.toMonoidHom) x = y := by
      change R.setup.Γ.subtype (R.groupEquiv x) = y
      rw [show R.groupEquiv x = ⟨y, hyΓ⟩ from MulEquiv.apply_symm_apply R.groupEquiv ⟨y, hyΓ⟩]
      rfl
    refine ⟨x, ?_, hfx⟩
    change (x : G) ∈ G0 ⊓ Subgroup.centralizer (D : Set G)
    refine ⟨x.2, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro d hd
    have hφdD : Subgroup.normalizerMonoidHom G0 ⟨d, hDN hd⟩ ∈ contextImage G0 D := by
      rw [mem_contextImage_aux]
      exact ⟨⟨d, hDN hd⟩, hd, rfl⟩
    let φd : I := ⟨Subgroup.normalizerMonoidHom G0 ⟨d, hDN hd⟩, hDI hφdD⟩
    have hactd : R.action φd ∈ realizedSubgroup R (contextImage G0 D) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mpr hφdD)
    have hcommd : R.action φd * y = y * R.action φd :=
      (Subgroup.mem_centralizer_iff.mp hyC) (R.action φd) hactd
    have hfixd : φd.1 x = x := by
      apply R.groupEquiv.injective
      apply Subtype.ext
      rw [R.compatible φd x]
      have hxeq : (R.groupEquiv x : ModGL .E6 L) = y := hfx
      rw [hxeq]
      calc R.action φd * y * (R.action φd)⁻¹ = y * R.action φd * (R.action φd)⁻¹ := by
            rw [hcommd]
        _ = y := by group
    have hdcomm : (d : G) * (x : G) = (x : G) * (d : G) := by
      have h := congrArg (fun w : G0 => (w : G)) hfixd
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      have h2 : (d : G) * (x : G) * d⁻¹ = (x : G) := h
      calc (d : G) * (x : G) = ((d : G) * (x : G) * d⁻¹) * d := by
            simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = (x : G) * d := by rw [h2]
    exact hdcomm

private theorem contextImage_mono_aux {G : Type} [Group G] {G0 H1 H2 : Subgroup G}
    (h : H1 ≤ H2) : contextImage G0 H1 ≤ contextImage G0 H2 := by
  rw [contextImage, contextImage]
  exact Subgroup.map_mono (Subgroup.comap_mono h)

private theorem realizedSubgroup_mono_aux {C : Type} [Group C] {I : Subgroup (MulAut C)}
    {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) {E1 E2 : Subgroup (MulAut C)} (h : E1 ≤ E2) :
    realizedSubgroup R E1 ≤ realizedSubgroup R E2 := by
  intro x hx
  rw [realizedSubgroup, Subgroup.mem_map] at hx ⊢
  simp only [Subgroup.mem_comap] at hx ⊢
  obtain ⟨φ, hφ, rfl⟩ := hx
  exact ⟨φ, h hφ, rfl⟩

private theorem isComponentOf_subgroupOf_aux {Γ : Type*} [Group Γ] {A K H : Subgroup Γ}
    (h : IsComponentOf A K) (hAH : A ≤ H) :
    IsComponentOf (A.subgroupOf H) (K.subgroupOf H) := by
  refine ⟨Subgroup.subgroupOf_mono H h.1, ?_, ?_⟩
  · simpa only [Subgroup.subgroupOf] using h.2.1.comap H.subtype
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAH) h.2.2

private theorem isComponentOf_map_aux {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ)
    (hf : Function.Injective f) {A K : Subgroup Γ} (h : IsComponentOf A K) :
    IsComponentOf (A.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map f,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (A.equivMapOfInjective f hf).symm h.2.2⟩

theorem component_dictionary
    {G : Type} [Group G] {G0 D J : Subgroup G}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I Ω)
    (hDI : contextImage G0 D ≤ I)
    (hDN : D ≤ Subgroup.normalizer (G0 : Set G))
    (hcomp : IsComponentOf J (G0 ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf (realizedSubgroup R (contextImage G0 J))
      (R.setup.Γ ⊓
        Subgroup.centralizer (realizedSubgroup R (contextImage G0 D) : Set _)) := by
  have hJG0 : J ≤ G0 := hcomp.1.trans inf_le_left
  have hcomp' : IsComponentOf (J.subgroupOf G0)
      ((G0 ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G0) :=
    isComponentOf_subgroupOf_aux hcomp hJG0
  have hf : Function.Injective
      (R.setup.Γ.subtype.comp R.groupEquiv.toMonoidHom) :=
    (Subgroup.subtype_injective R.setup.Γ).comp R.groupEquiv.injective
  have hmap := isComponentOf_map_aux _ hf hcomp'
  rw [← realizedSubgroup_contextImage_aux R hJG0,
    map_subgroupOf_centralizer_eq_aux R hDI hDN] at hmap
  exact hmap

theorem centralizer_dictionary
    {G : Type} [Group G] {G0 B D J : Subgroup G}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I Ω)
    (hJI : contextImage G0 J ≤ I)
    (hJG0 : J ≤ G0)
    (hDj : D = B ⊓ Subgroup.centralizer (J : Set G)) :
    realizedSubgroup R (contextImage G0 B) ⊓
        Subgroup.centralizer (realizedSubgroup R (contextImage G0 J) : Set _) =
      realizedSubgroup R (contextImage G0 D) := by
  have hDB : D ≤ B := hDj.le.trans inf_le_left
  have hDC : D ≤ Subgroup.centralizer (J : Set G) := hDj.le.trans inf_le_right
  have hDleB : contextImage G0 D ≤ contextImage G0 B := contextImage_mono_aux hDB
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxB, hxC⟩
    simp only [realizedSubgroup, SetLike.mem_coe, Subgroup.mem_map] at hxB
    obtain ⟨φ, hφ, rfl⟩ := hxB
    have hφB : φ.1 ∈ contextImage G0 B := Subgroup.mem_comap.mp hφ
    rw [mem_contextImage_aux] at hφB
    obtain ⟨n, hnB, hnφ⟩ := hφB
    have hnC : (n : G) ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hconjj : MulAut.conj (⟨j, hJG0 hj⟩ : ↥G0) ∈ contextImage G0 J := by
        rw [mem_contextImage_aux]
        refine ⟨⟨j, Subgroup.le_normalizer (hJG0 hj)⟩, hj, ?_⟩
        ext y
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
        rfl
      let φj : I := ⟨MulAut.conj (⟨j, hJG0 hj⟩ : ↥G0), hJI hconjj⟩
      have hactj : R.action φj ∈ realizedSubgroup R (contextImage G0 J) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mpr hconjj)
      have hcommj : R.action φj * R.action φ = R.action φ * R.action φj :=
        (Subgroup.mem_centralizer_iff.mp hxC) (R.action φj) hactj
      have hφjeq : R.action φj =
          (R.groupEquiv (⟨j, hJG0 hj⟩ : ↥G0) : ModGL .E6 Ω) := by
        have : φj = ⟨MulAut.conj (⟨j, hJG0 hj⟩ : ↥G0),
            R.inner_le ⟨⟨j, hJG0 hj⟩, rfl⟩⟩ := Subtype.ext rfl
        rw [this, R.inner_compatible]
      have hfixj : φ.1 (⟨j, hJG0 hj⟩ : ↥G0) = ⟨j, hJG0 hj⟩ := by
        apply R.groupEquiv.injective
        apply Subtype.ext
        rw [R.compatible φ (⟨j, hJG0 hj⟩ : ↥G0)]
        rw [hφjeq] at hcommj
        rw [← hcommj]
        group
      have hnj : (n : G) * j = j * (n : G) := by
        have h := congrArg (fun w : G0 => (w : G)) hfixj
        rw [← hnφ] at h
        change ((Subgroup.normalizerMonoidHom G0 n) (⟨j, hJG0 hj⟩ : ↥G0) : G) = j at h
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        calc (n : G) * j = ((n : G) * j * (n : G)⁻¹) * (n : G) := by group
          _ = j * (n : G) := by rw [h]
      exact hnj.symm
    have hnD : (n : G) ∈ D := by
      rw [hDj]
      exact ⟨hnB, hnC⟩
    have hφD : φ.1 ∈ contextImage G0 D := by
      rw [mem_contextImage_aux]
      exact ⟨n, hnD, hnφ⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mpr hφD)
  · intro x hx
    rw [Subgroup.mem_inf]
    constructor
    · exact realizedSubgroup_mono_aux R hDleB hx
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [realizedSubgroup, SetLike.mem_coe, Subgroup.mem_map] at hx hz
      obtain ⟨φ, hφ, rfl⟩ := hx
      obtain ⟨ψ, hψ, rfl⟩ := hz
      have hφD : φ.1 ∈ contextImage G0 D := Subgroup.mem_comap.mp hφ
      have hψJ : ψ.1 ∈ contextImage G0 J := Subgroup.mem_comap.mp hψ
      rw [mem_contextImage_aux] at hφD hψJ
      obtain ⟨n, hnD, hnφ⟩ := hφD
      obtain ⟨m, hmJ, hmψ⟩ := hψJ
      have hψeq : R.action ψ =
          (R.groupEquiv (⟨(m : G), hJG0 hmJ⟩ : ↥G0) : ModGL .E6 Ω) := by
        have hmconj : ψ.1 = MulAut.conj (⟨(m : G), hJG0 hmJ⟩ : ↥G0) := by
          rw [← hmψ]
          ext y
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
          rfl
        have : ψ = ⟨MulAut.conj (⟨(m : G), hJG0 hmJ⟩ : ↥G0),
            R.inner_le ⟨⟨(m : G), hJG0 hmJ⟩, rfl⟩⟩ := Subtype.ext hmconj
        rw [this, R.inner_compatible]
      have hnm : (m : G) * (n : G) = (n : G) * (m : G) :=
        (Subgroup.mem_centralizer_iff.mp (hDC hnD)) (m : G) hmJ
      have hfix : φ.1 (⟨(m : G), hJG0 hmJ⟩ : ↥G0) = ⟨(m : G), hJG0 hmJ⟩ := by
        rw [← hnφ]
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rw [← hnm]
        group
      rw [hψeq]
      have hconj := R.compatible φ (⟨(m : G), hJG0 hmJ⟩ : ↥G0)
      rw [hfix] at hconj
      calc (R.groupEquiv (⟨(m : G), hJG0 hmJ⟩ : ↥G0) : ModGL .E6 Ω) * R.action φ
          = (R.action φ * (R.groupEquiv (⟨(m : G), hJG0 hmJ⟩ : ↥G0) : ModGL .E6 Ω) *
              (R.action φ)⁻¹) * R.action φ := by conv_lhs => rw [hconj]
        _ = R.action φ * (R.groupEquiv (⟨(m : G), hJG0 hmJ⟩ : ↥G0) : ModGL .E6 Ω) := by
              group

theorem exists_inner_model_action
    {C M : Type} [Group C] [Group M] (hZ : Subgroup.center C = ⊥)
    (ψ : C →* M) (hψ : Function.Injective ψ)
    {A : Subgroup (MulAut C)}
    (hA : A ≤ (MulAut.conj : C →* MulAut C).range) :
    ∃ ρ : A →* M, Function.Injective ρ ∧ ρ.range ≤ ψ.range ∧
      (∀ (a : A) (c : C), ψ (a.1 c) = ρ a * ψ c * (ρ a)⁻¹) ∧
      (∀ (x : C) (hx : MulAut.conj x ∈ A), ρ ⟨MulAut.conj x, hx⟩ = ψ x) := by
  classical
  have hc : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  let e : C ≃* (MulAut.conj : C →* MulAut C).range := MonoidHom.ofInjective hc
  let η : A →* C := e.symm.toMonoidHom.comp (Subgroup.inclusion hA)
  have hη : ∀ a : A, MulAut.conj (η a) = a.1 := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hA a))
    exact h
  let ρ : A →* M := ψ.comp η
  refine ⟨ρ, hψ.comp (e.symm.injective.comp (Subgroup.inclusion_injective hA)), ?_, ?_, ?_⟩
  · rintro y ⟨a, rfl⟩
    exact ⟨η a, rfl⟩
  · intro a c
    rw [← hη a, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl
  · intro x hx
    change ψ (η ⟨MulAut.conj x, hx⟩) = ψ x
    exact congrArg ψ (hc (hη ⟨MulAut.conj x, hx⟩))


theorem exists_shape_model_action
    {C : Type} [Group C] {I_C : Subgroup (MulAut C)}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup Tag.E6 Ω 5) (e : C ≃* S.Γ)
    (hΓle : S.Γ ≤ S.D.model)
    (hInn : (MulAut.conj : C →* MulAut C).range ≤ I_C)
    (hreal : ∀ φ : I_C, ∃ d ∈ S.D.model, ∀ x : C, e (φ.1 x) = d * e x * d⁻¹)
    (hfaith : ∀ d ∈ S.D.model, (∀ x : S.Γ, d * x * d⁻¹ = x) → d = 1) :
    ∃ act : I_C →* ModGL Tag.E6 Ω,
      (∀ c : C, act ⟨MulAut.conj c, hInn ⟨c, rfl⟩⟩ = (e c : ModGL Tag.E6 Ω)) ∧
      (∀ φ : I_C, act φ ∈ S.D.model) ∧
      (∀ (φ : I_C) (x : C), e (φ.1 x) = act φ * e x * (act φ)⁻¹) := by
  classical
  let d : I_C → ModGL Tag.E6 Ω := fun φ => (hreal φ).choose
  have hd_mem : ∀ φ : I_C, d φ ∈ S.D.model := fun φ => (hreal φ).choose_spec.1
  have hd_rel : ∀ (φ : I_C) (x : C), e (φ.1 x) = d φ * e x * (d φ)⁻¹ :=
    fun φ => (hreal φ).choose_spec.2
  have hd_unique : ∀ (φ : I_C) (d' : ModGL Tag.E6 Ω), d' ∈ S.D.model →
      (∀ x : C, e (φ.1 x) = d' * e x * d'⁻¹) → d' = d φ := by
    intro φ d' hd'm hd'rel
    have hmem : (d φ)⁻¹ * d' ∈ S.D.model :=
      S.D.model.mul_mem (S.D.model.inv_mem (hd_mem φ)) hd'm
    have hcent : ∀ x : S.Γ, ((d φ)⁻¹ * d') * x * ((d φ)⁻¹ * d')⁻¹ = x := by
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      have h : d φ * e y * (d φ)⁻¹ = d' * e y * d'⁻¹ := by
        rw [← hd_rel φ y, hd'rel y]
      calc ((d φ)⁻¹ * d') * e y * ((d φ)⁻¹ * d')⁻¹
          = (d φ)⁻¹ * (d' * e y * d'⁻¹) * d φ := by group
        _ = (d φ)⁻¹ * (d φ * e y * (d φ)⁻¹) * d φ := by rw [h]
        _ = e y := by group
    have h1 : (d φ)⁻¹ * d' = 1 := hfaith _ hmem hcent
    calc d' = d φ * ((d φ)⁻¹ * d') := by group
      _ = d φ * 1 := by rw [h1]
      _ = d φ := by rw [mul_one]
  refine ⟨{ toFun := d, map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · exact (hd_unique 1 1 S.D.model.one_mem (by intro x; simp)).symm
  · intro φ ψ
    exact (hd_unique (φ * ψ) (d φ * d ψ)
      (S.D.model.mul_mem (hd_mem φ) (hd_mem ψ)) (by
        intro x
        show e (φ.1 (ψ.1 x)) = (d φ * d ψ) * e x * (d φ * d ψ)⁻¹
        rw [hd_rel φ (ψ.1 x), hd_rel ψ x]
        group)).symm
  · intro c
    refine (hd_unique ⟨MulAut.conj c, hInn ⟨c, rfl⟩⟩ (e c) ?_ ?_).symm
    · show (e c : ModGL Tag.E6 Ω) ∈ S.D.model
      exact hΓle (e c).2
    · intro x
      show e ((MulAut.conj c) x) =
        (e c : ModGL Tag.E6 Ω) * e x * (e c : ModGL Tag.E6 Ω)⁻¹
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · intro φ
    exact hd_mem φ
  · intro φ x
    exact hd_rel φ x

theorem contextImage_mono {G : Type} [Group G] {G0 H1 H2 : Subgroup G} (h : H1 ≤ H2) :
    contextImage G0 H1 ≤ contextImage G0 H2 := by
  intro φ hφ
  rw [contextImage, Subgroup.mem_map] at hφ ⊢
  simp only [Subgroup.mem_comap] at hφ ⊢
  obtain ⟨n, hn, rfl⟩ := hφ
  exact ⟨n, h hn, rfl⟩

theorem realizedSubgroup_mono {C : Type} [Group C] {I : Subgroup (MulAut C)}
    {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) {E1 E2 : Subgroup (MulAut C)} (h : E1 ≤ E2) :
    realizedSubgroup R E1 ≤ realizedSubgroup R E2 := by
  intro x hx
  rw [realizedSubgroup, Subgroup.mem_map] at hx ⊢
  simp only [Subgroup.mem_comap] at hx ⊢
  obtain ⟨φ, hφ, rfl⟩ := hx
  exact ⟨φ, h hφ, rfl⟩

theorem exists_plane_of_realization
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut (ggG0 3 B x L D J))}
    (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
    (hDI : contextImage (ggG0 3 B x L D J) D ≤ I)
    (hBT : realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤ torusGroup .E6 Ω) :
    ∃ a : Fin 2 → Fin Tag.E6.rank → Ωˣ,
      planeGroup a = realizedSubgroup R (contextImage (ggG0 3 B x L D J) D) ∧
      (∀ i j, a i j ^ 3 = 1) :=
  plane_of_realization R s1.1
    ((hctx.stdSub.1.1.trans hctx.bstar.1).trans hctx.bstar_le_normalizer) hDI
    ((realizedSubgroup_mono R
      (contextImage_mono (hctx.stdSub.1.1.trans hctx.bstar.1))).trans hBT)
    (by rw [hctx.card_d]; norm_num)
    (fun d hd => hctx.bstar.2.1.2 d (hctx.bstar.1 (hctx.stdSub.1.1 hd)))

theorem isComponentOf_realized
    {G : Type} [Group G] {G0 D J : Subgroup G}
    {L : Type} [Field L] [IsAlgClosed L]
    (I : Subgroup (MulAut G0)) (R : ShapeRealization G0 I L)
    (hD : contextImage G0 D ≤ I)
    (hDN : D ≤ Subgroup.normalizer (G0 : Set G))
    (hcomp : IsComponentOf J (G0 ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf (realizedSubgroup R (contextImage G0 J))
      (R.setup.Γ ⊓
        Subgroup.centralizer (realizedSubgroup R (contextImage G0 D) : Set _)) :=
  component_dictionary R hD hDN hcomp

theorem inf_centralizer_realized
    {G : Type} [Group G] {G0 B D J : Subgroup G}
    {L : Type} [Field L] [IsAlgClosed L]
    (I : Subgroup (MulAut G0)) (R : ShapeRealization G0 I L)
    (hJI : contextImage G0 J ≤ I)
    (hJG0 : J ≤ G0)
    (hD : D = B ⊓ Subgroup.centralizer (J : Set G)) :
    realizedSubgroup R (contextImage G0 B) ⊓
        Subgroup.centralizer (realizedSubgroup R (contextImage G0 J) : Set _) =
      realizedSubgroup R (contextImage G0 D) :=
  centralizer_dictionary R hJI hJG0 hD

end CFSG.StandardType
