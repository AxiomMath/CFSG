module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeTransvections
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AmbientBridge
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open CFSG.ComponentClassification.OutcomeLocal
open Module
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem exists_dual_ker_eq
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V) :
    ∃ (v : V) (φ : Dual (ZMod 2) V), v ∉ W ∧ (∀ w ∈ W, φ w = 0) ∧ φ v = 1 ∧
      (∀ x, φ x = 0 → x ∈ W) := by
  classical
  obtain ⟨v, -, hv⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_mem_notMem_of_finrank_lt
    (U := (⊤ : Submodule (ZMod 2) V)) (S := W) (by rw [finrank_top]; omega)
  obtain ⟨φ, hφW, hφv⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_dual_eq_one_of_notMem hv
  have htop : ∀ x ∉ W, W ⊔ Submodule.span (ZMod 2) {x} = ⊤ := fun x hx =>
    Submodule.eq_top_of_finrank_eq (K := ZMod 2)
      (by rw [Submodule.finrank_sup_span_singleton hx]; omega)
  refine ⟨v, φ, hv, hφW, hφv, ?_⟩
  intro x hx
  by_contra hxW
  have hφ0 : φ = 0 := by
    ext y
    obtain ⟨u, hu, z, hz, hy⟩ := Submodule.mem_sup.mp
      (show y ∈ W ⊔ Submodule.span (ZMod 2) {x} from by rw [htop x hxW]; trivial)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [← hy, map_add, hφW u hu, LinearMap.map_smul, hx, smul_zero, add_zero]
    rfl
  have h0 : φ v = 0 := congrArg (fun ψ : Dual (ZMod 2) V => ψ v) hφ0
  rw [hφv] at h0
  exact one_ne_zero h0

theorem eq_tv_of_fixes_hyperplane
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V)
    {φ : Dual (ZMod 2) V} (hφW : ∀ w ∈ W, φ w = 0)
    {v : V} (hv : v ∉ W) (hφv : φ v = 1)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hfix : ∀ w ∈ W, (t : V →ₗ[ZMod 2] V) w = w) :
    ∃ (a : V) (ha : a ∈ W), t = tv φ a (hφW a ha) := by
  classical
  have htop : ∀ x ∉ W, W ⊔ Submodule.span (ZMod 2) {x} = ⊤ := fun x hx =>
    Submodule.eq_top_of_finrank_eq (K := ZMod 2)
      (by rw [Submodule.finrank_sup_span_singleton hx]; omega)
  have htvW : (t : V →ₗ[ZMod 2] V) v ∉ W := by
    intro h
    have h1 : (t : V →ₗ[ZMod 2] V) ((t : V →ₗ[ZMod 2] V) v) = (t : V →ₗ[ZMod 2] V) v :=
      hfix ((t : V →ₗ[ZMod 2] V) v) h
    have h2 : (t : V →ₗ[ZMod 2] V) ((t : V →ₗ[ZMod 2] V) v) = v := by
      simpa using congrArg
        (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V => (g : V →ₗ[ZMod 2] V) v) ht2
    exact hv (h2 ▸ (h1.symm ▸ h))
  obtain ⟨u, hu, z, hz, htz⟩ := Submodule.mem_sup.mp
    (show ((t : V →ₗ[ZMod 2] V) v) ∈ W ⊔ Submodule.span (ZMod 2) {v} from by
      rw [htop v hv]; trivial)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c = 1 := by
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one c with h0 | h1
    · exfalso
      rw [h0, zero_smul, add_zero] at htz
      exact htvW (by rw [← htz]; exact hu)
    · exact h1
  rw [hc, one_smul] at htz
  refine ⟨u, hu, ?_⟩
  refine tv_ext fun x => congrArg (fun f : V →ₗ[ZMod 2] V => f x) ?_
  refine LinearMap.ext_on (s := (W : Set V) ∪ {v}) ?_ ?_
  · rw [Submodule.span_union, Submodule.span_eq W, htop v hv]
  · rintro y (hy | hy)
    · rw [hfix y hy, tv_apply, hφW y hy]
      simp
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, tv_apply, hφv, one_smul, add_comm v u, htz]

theorem isF2Transvection_conj
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (ht : IsF2Transvection t)
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    IsF2Transvection (g * t * g⁻¹) := by
  have hinv : ∀ (x : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V),
      (x : V →ₗ[ZMod 2] V) (((x⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v) = v :=
    fun x v =>
      CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection.gl_apply_inv_apply x v
  have hinv' : ∀ (x : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V),
      ((x⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
        ((x : V →ₗ[ZMod 2] V) v) = v := by
    intro x v
    simpa using hinv x⁻¹ v
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) a) = 0 := by
    rw [LinearMap.comp_apply, hinv' g a, h]
  rw [conj_tv g φ a h h']
  refine (isF2Transvection_iff _).mpr ⟨_, _, h', ?_, ?_, rfl⟩
  · intro h0
    apply hφ
    ext x
    have h1 : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
        (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x) = 0 := by
      simpa using LinearMap.congr_fun h0
        (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x)
    rw [LinearMap.comp_apply, hinv' g x] at h1
    simpa using h1
  · intro h0
    apply ha
    have h1 : ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
        (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) a) = 0 := by
      rw [h0, map_zero]
    rwa [hinv'] at h1

theorem imgGL_mono {N : Subgroup G} (hN : IsElemAbelian 2 N) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ≤ Subgroup.normalizer (N : Set G)) (h₂ : L₂ ≤ Subgroup.normalizer (N : Set G))
    (h : L₁ ≤ L₂) : imgGL hN L₁ h₁ ≤ imgGL hN L₂ h₂ := by
  rintro _ ⟨y, rfl⟩
  exact mem_imgGL.mpr ⟨⟨y, h y.2⟩, rfl⟩

theorem imgGL_eq_map_subgroupOf {N A Y : Subgroup G} (hN : IsElemAbelian 2 N)
    (hA : A ≤ Y) (hAY : A ≤ Subgroup.normalizer (N : Set G))
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) :
    imgGL hN A hAY = (A.subgroupOf Y).map (actGL hN Y hY) := by
  ext g
  rw [mem_imgGL, Subgroup.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, hA a.2⟩, a.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

noncomputable def unitsEquiv (V : Type) [AddCommGroup V] [Module (ZMod 2) V] :
    CFSG.Quasithin.G11.GLV V ≃* LinearMap.GeneralLinearGroup (ZMod 2) V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm

private theorem unitsEquiv_coe (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    (φ : CFSG.Quasithin.G11.GLV V) :
    ((unitsEquiv V φ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) =
      (φ : V →ₗ[ZMod 2] V) := rfl

theorem isIrreducibleOn_imgGL {N : Subgroup G} (hN : IsElemAbelian 2 N) {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (N : Set G)) (hirr : IrrOn L N) :
    ∀ W : Submodule (ZMod 2) (Additive (VN hN)),
      CFSG.Quasithin.G11.Invariant (imgGL hN L hL) W → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  exact eq_bot_or_top_of_sub hN W
    (hirr _ (subgroupOfSub_le hN W) (normalizer_subgroupOfSub hN hL W hW))

theorem isGInvariant_map_units {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (G : Subgroup (CFSG.Quasithin.G11.GLV V)) (W : Submodule (ZMod 2) V) :
    CFSG.ComponentClassification.OutcomeLocal.IsGInvariant
        (G.map (unitsEquiv V).toMonoidHom) W ↔ CFSG.Quasithin.G11.Invariant G W := by
  constructor
  · intro h g hg w hw
    simpa [unitsEquiv_coe] using h (unitsEquiv V g) (Subgroup.mem_map_of_mem _ hg) w hw
  · intro h k hk w hw
    obtain ⟨g, hg, rfl⟩ := hk
    simpa [unitsEquiv_coe] using h g hg w hw

theorem isIrreducibleOn_units {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (G : Subgroup (CFSG.Quasithin.G11.GLV V))
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.Quasithin.G11.Invariant G W → W = ⊥ ∨ W = ⊤) :
    CFSG.ComponentClassification.OutcomeLocal.IsIrreducibleOn
      (G.map (unitsEquiv V).toMonoidHom) := by
  intro W hW
  exact hirr W ((isGInvariant_map_units G W).mp hW)

theorem imgGL_eq_of_frattini (c : Ctx23L D Ch) (hU : IsElemAbelian 2 D.U)
    (hM : D.M ≤ Subgroup.normalizer (D.U : Set G))
    (hY : D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ≤
      Subgroup.normalizer (D.U : Set G)) :
    imgGL hU D.M hM =
      imgGL hU (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) hY := by
  refine le_antisymm ?_ (imgGL_mono hU _ _ inf_le_left)
  rintro _ ⟨m, rfl⟩
  obtain ⟨k, hk, n, hn, hkn⟩ := frattini_decomp c m.2
  refine mem_imgGL.mpr ⟨⟨n, hn⟩, ?_⟩
  have hkm : actHom D.U D.M hM ⟨k, hk.1⟩ = 1 :=
    (actHom_eq_one_iff D.U D.M hM ⟨k, hk.1⟩).mpr hk.2
  have hsub : (⟨m, m.2⟩ : ↥D.M) = ⟨k, hk.1⟩ * ⟨n, hn.1⟩ := Subtype.ext hkn
  have hact : actHom D.U _ hY ⟨n, hn⟩ = actHom D.U D.M hM ⟨m, m.2⟩ := by
    rw [hsub, map_mul, hkm, one_mul]
    rfl
  exact congrArg toGL hact

theorem card_imgGL_of_injective {N A : Subgroup G} (hN : IsElemAbelian 2 N)
    (hA : A ≤ Subgroup.normalizer (N : Set G))
    (hfaith : ∀ a : ↥A, actGL hN A hA a = 1 → a = 1) :
    Nat.card (imgGL hN A hA) = Nat.card A := by
  have hinj : Function.Injective (fun a : ↥A => actGL hN A hA a) := by
    intro a b hab
    have h1 : actGL hN A hA a * (actGL hN A hA b)⁻¹ = 1 := by
      simpa [hab]
    have h2 : a * b⁻¹ = 1 := hfaith (a * b⁻¹) (by rw [map_mul, map_inv]; exact h1)
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [h2, one_mul]
  exact Nat.card_range_of_injective hinj

private theorem actGL_involution (hU : IsElemAbelian 2 D.U) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (D.U : Set G))
    (hinvol : ∀ e ∈ E, e * e = 1) (e : ↥E) :
    actGL hU E hE e * actGL hU E hE e = 1 := by
  rw [← map_mul, show e * e = 1 from Subtype.ext (hinvol (e : G) e.2), map_one]

private theorem actGL_fixes_axis (hU : IsElemAbelian 2 D.U) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (D.U : Set G)) {W : Subgroup G} {W' : Subgroup (VN hU)}
    (hW' : ∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ W)
    (hfix : ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ = w) (e : ↥E)
    {w : Additive (VN hU)} (hw : w ∈ toSubmodule W') :
    actGL hU E hE e w = w := by
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective w
  have huW : ((VN.toN u : ↥D.U) : G) ∈ W := hW' u (by simpa [mem_toSubmodule] using hw)
  apply Additive.toMul.injective
  apply Subtype.ext
  show (e : G) * ((VN.toN u : ↥D.U) : G) * (e : G)⁻¹ = ((VN.toN u : ↥D.U) : G)
  exact hfix (e : G) e.2 ((VN.toN u : ↥D.U) : G) huW

private theorem actGL_faithful (hU : IsElemAbelian 2 D.U) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (D.U : Set G))
    (hfaith : ∀ e ∈ E, (∀ u ∈ D.U, e * u * e⁻¹ = u) → e = 1) (e : ↥E)
    (he : actGL hU E hE e = 1) : e = 1 := by
  refine Subtype.ext (hfaith (e : G) e.2 ?_)
  intro u hu
  have h1 : actGL hU E hE e (Additive.ofMul (VN.ofN hU ⟨u, hu⟩)) =
      Additive.ofMul (VN.ofN hU ⟨u, hu⟩) := by rw [he]; rfl
  have h2 := congrArg (fun x : Additive (VN hU) => VN.toN (Additive.toMul x)) h1
  have h3 : actHom D.U E hE e ⟨u, hu⟩ = ⟨u, hu⟩ := h2
  have h4 := congrArg (fun x : ↥D.U => (x : G)) h3
  simpa [actHom_apply_coe] using h4

private def vnMulEquiv (hU : IsElemAbelian 2 D.U) : VN hU ≃* ↥D.U where
  toFun := VN.toN
  invFun := VN.ofN hU
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem exists_axis_functional (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G)) (h3 : 3 ≤ rk ↥D.U)
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g) :
    ∃ (W' : Subgroup (VN hU)) (v : Additive (VN hU)) (φ : Dual (ZMod 2) (Additive (VN hU))),
      Nat.card W' = 2 ^ (rk (VN hU) - 1) ∧ (∀ w, φ w = 0 ↔ w ∈ toSubmodule W') ∧
        v ∉ toSubmodule W' ∧ φ v = 1 ∧
        (finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU))) ∧
        (∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ D.U ⊓ conjSubgroup D.M g) := by
  classical
  let W : Subgroup G := D.U ⊓ conjSubgroup D.M g
  let W' : Subgroup (VN hU) :=
    { carrier := (W.subgroupOf D.U).carrier
      mul_mem' := fun hx hy => (W.subgroupOf D.U).mul_mem hx hy
      one_mem' := (W.subgroupOf D.U).one_mem
      inv_mem' := fun hx => (W.subgroupOf D.U).inv_mem hx }
  obtain ⟨-, hWcard, -, -, -, -⟩ := full_transvections hU hUM hMU hTI hO hC
  have hW'card : Nat.card W' = 2 ^ (rk (VN hU) - 1) := by
    have h1 : Nat.card W' = Nat.card (W.subgroupOf D.U) := rfl
    have h2 : Nat.card (W.subgroupOf D.U) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h3' : Nat.card W = 2 ^ (rk (VN hU) - 1) := by
      rw [show rk (VN hU) = rk ↥D.U from rfl]
      exact hWcard
    rw [h1, h2, h3']
  have hVcard : Nat.card (Additive (VN hU)) = 2 ^ rk (VN hU) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card,
      ← rk_eq_finrank_additive]
  have hdim : finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU)) := by
    have h1 : Nat.card (toSubmodule W') = 2 ^ (rk (VN hU) - 1) := by
      rw [show Nat.card (toSubmodule W') = Nat.card W' from rfl, hW'card]
    have h2 : 2 ^ finrank (ZMod 2) (toSubmodule W') = Nat.card (toSubmodule W') := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
    have h3' : 2 ^ finrank (ZMod 2) (Additive (VN hU)) = Nat.card (Additive (VN hU)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
    have h4 : finrank (ZMod 2) (toSubmodule W') = rk (VN hU) - 1 :=
      Nat.pow_right_injective (le_refl 2) (h2.trans h1)
    have h5 : finrank (ZMod 2) (Additive (VN hU)) = rk (VN hU) :=
      Nat.pow_right_injective (le_refl 2) (h3'.trans hVcard)
    have h6 : 1 ≤ rk (VN hU) := by
      have h7 : rk (VN hU) = rk ↥D.U := rfl
      omega
    omega
  have hW'le : ∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ D.U ⊓ conjSubgroup D.M g := by
    intro u hu
    have h1 : VN.toN u ∈ W.subgroupOf D.U := hu
    simpa only [Subgroup.mem_subgroupOf] using h1
  obtain ⟨v, φ, hv, hφW, hφv, hker⟩ := exists_dual_ker_eq hdim
  exact ⟨W', v, φ, hW'card, fun w => ⟨hker w, hφW w⟩, hv, hφv, hdim, hW'le⟩

private theorem imgGL_axis_subset (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g)
    {W' : Subgroup (VN hU)} {v : Additive (VN hU)} {φ : Dual (ZMod 2) (Additive (VN hU))}
    (hdim : finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU)))
    (hW'le : ∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ D.U ⊓ conjSubgroup D.M g)
    (hphi : ∀ w ∈ toSubmodule W', φ w = 0) (hvW : v ∉ toSubmodule W') (hv : φ v = 1) :
    ∀ t ∈ (imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
        (unitsEquiv (Additive (VN hU))).toMonoidHom,
      ∃ a : ↥(toSubmodule W'), t = tv φ a.1 (hphi a.1 a.2) := by
  classical
  let E : Subgroup G := conjSubgroup D.U g ⊓ D.M
  have hE : E ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  obtain ⟨-, -, hEinvol, hEfix, hEfaith, -⟩ := full_transvections hU hUM hMU hTI hO hC
  rintro _ ⟨t, ⟨e, rfl⟩, rfl⟩
  by_cases he : e = 1
  · refine ⟨⟨0, (toSubmodule W').zero_mem⟩, ?_⟩
    subst he
    rw [map_one, map_one, tv_zero_right]
  · have h2 : unitsEquiv (Additive (VN hU)) (actGL hU E hE e) *
        unitsEquiv (Additive (VN hU)) (actGL hU E hE e) = 1 := by
      rw [← map_mul, actGL_involution hU hE hEinvol e, map_one]
    have h1 : unitsEquiv (Additive (VN hU)) (actGL hU E hE e) ≠ 1 := by
      intro h
      apply he
      apply actGL_faithful hU hE hEfaith e
      exact (unitsEquiv (Additive (VN hU))).injective (by simpa using h)
    obtain ⟨a, ha, hta⟩ := eq_tv_of_fixes_hyperplane hdim hphi hvW hv h2 h1
      (fun w hw => actGL_fixes_axis hU hE (W := D.U ⊓ conjSubgroup D.M g) hW'le hEfix e hw)
    exact ⟨⟨a, ha⟩, hta⟩

private theorem card_axis_imgGL (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g) :
    Nat.card ↥((imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
      (unitsEquiv (Additive (VN hU))).toMonoidHom) = 2 ^ (rk (VN hU) - 1) := by
  classical
  let E : Subgroup G := conjSubgroup D.U g ⊓ D.M
  have hE : E ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  obtain ⟨hEcard, -, -, -, hEfaith, -⟩ := full_transvections hU hUM hMU hTI hO hC
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (imgGL hU E hE)
    (unitsEquiv (Additive (VN hU))).toMonoidHom (unitsEquiv _).injective).toEquiv]
  rw [card_imgGL_of_injective hU hE (fun a ha => actGL_faithful hU hE hEfaith a ha)]
  have hE2 : Nat.card ↥E = 2 ^ (rk (VN hU) - 1) := by
    change Nat.card ↥(conjSubgroup D.U g ⊓ D.M) = 2 ^ (rk (VN hU) - 1)
    rw [show rk (VN hU) = rk ↥D.U from rfl]
    exact hEcard
  exact hE2

private theorem set_eq_range_of_card_eq {α β : Type} [Finite α] [Finite β]
    {s : Set β} {f : α → β} (hsub : s ⊆ Set.range f) (hinj : Function.Injective f)
    (hcard : Nat.card s = Nat.card α) : s = Set.range f := by
  haveI : Fintype s := Fintype.ofFinite _
  haveI : Fintype (Set.range f) := Fintype.ofFinite _
  refine Set.eq_of_subset_of_card_le hsub ?_
  rw [show Fintype.card ↥(Set.range f) = Nat.card ↥(Set.range f) from
        (Nat.card_eq_fintype_card).symm,
    show Fintype.card ↥s = Nat.card ↥s from (Nat.card_eq_fintype_card).symm,
    Nat.card_range_of_injective hinj, ← hcard]

private theorem axis_transvections_set (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g)
    {W' : Subgroup (VN hU)} {v : Additive (VN hU)} {φ : Dual (ZMod 2) (Additive (VN hU))}
    (hdim : finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU)))
    (hW'le : ∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ D.U ⊓ conjSubgroup D.M g)
    (hphi : ∀ w ∈ toSubmodule W', φ w = 0) (hvW : v ∉ toSubmodule W') (hv : φ v = 1)
    (hW'card : Nat.card W' = 2 ^ (rk (VN hU) - 1)) :
    ((imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
        (unitsEquiv (Additive (VN hU))).toMonoidHom : Set _) =
      Set.range (fun a : ↥(toSubmodule W') => tv φ a.1 (hphi a.1 a.2)) := by
  classical
  let E : Subgroup G := conjSubgroup D.U g ⊓ D.M
  have hE : E ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  let f : ↥(toSubmodule W') → LinearMap.GeneralLinearGroup (ZMod 2) (Additive (VN hU)) :=
    fun a => tv φ a.1 (hphi a.1 a.2)
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun t : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (VN hU)) =>
      (t : Additive (VN hU) →ₗ[ZMod 2] Additive (VN hU)) v) hab
    simp only [f, tv_apply, hv, one_smul] at h
    exact Subtype.ext (add_left_cancel h)
  have hsub : ((imgGL hU E hE).map (unitsEquiv (Additive (VN hU))).toMonoidHom : Set _) ⊆
      Set.range f := by
    intro t ht
    obtain ⟨a, rfl⟩ :=
      (imgGL_axis_subset hU hUM hMU hTI hO hC hdim hW'le hphi hvW hv) t ht
    exact ⟨a, rfl⟩
  have hEcard' := card_axis_imgGL hU hUM hMU hTI hO hC
  have hcardα : Nat.card ↥(toSubmodule W') = 2 ^ (rk (VN hU) - 1) := by
    rw [show Nat.card ↥(toSubmodule W') = Nat.card W' from rfl, hW'card]
  have hcards : Nat.card ((imgGL hU E hE).map
      (unitsEquiv (Additive (VN hU))).toMonoidHom : Subgroup _).carrier =
      Nat.card ↥(toSubmodule W') := by
    rw [show Nat.card ((imgGL hU E hE).map
        (unitsEquiv (Additive (VN hU))).toMonoidHom : Subgroup _).carrier =
        Nat.card ↥((imgGL hU E hE).map
          (unitsEquiv (Additive (VN hU))).toMonoidHom : Subgroup _) from rfl, hEcard', hcardα]
  exact set_eq_range_of_card_eq hsub hinj hcards

private theorem imgGL_axis_eq (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g)
    {W' : Subgroup (VN hU)} {v : Additive (VN hU)} {φ : Dual (ZMod 2) (Additive (VN hU))}
    (hdim : finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU)))
    (hW'le : ∀ u ∈ W', ((VN.toN u : ↥D.U) : G) ∈ D.U ⊓ conjSubgroup D.M g)
    (hphi : ∀ w ∈ toSubmodule W', φ w = 0) (hvW : v ∉ toSubmodule W') (hv : φ v = 1)
    (hW'card : Nat.card W' = 2 ^ (rk (VN hU) - 1)) :
    ∀ t, t ∈ (imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
        (unitsEquiv (Additive (VN hU))).toMonoidHom ↔
      ∃ a : ↥(toSubmodule W'), t = tv φ a.1 (hphi a.1 a.2) := by
  have hset := axis_transvections_set hU hUM hMU hTI hO hC hdim hW'le hphi hvW hv hW'card
  intro t
  have htiff : (t ∈ ((imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
      (unitsEquiv (Additive (VN hU))).toMonoidHom : Subgroup _) : Prop) ↔
      t ∈ Set.range (fun a : ↥(toSubmodule W') => tv φ a.1 (hphi a.1 a.2)) := by
    change t ∈ (((imgGL hU (conjSubgroup D.U g ⊓ D.M) (inf_le_right.trans hMU)).map
      (unitsEquiv (Additive (VN hU))).toMonoidHom : Subgroup _) : Set _) ↔
      t ∈ Set.range (fun a : ↥(toSubmodule W') => tv φ a.1 (hphi a.1 a.2))
    rw [hset]
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := Set.mem_range.mp (htiff.mp ht)
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact htiff.mpr (Set.mem_range.mpr ⟨a, rfl⟩)

private theorem exists_second_axis
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : CFSG.ComponentClassification.OutcomeLocal.IsIrreducibleOn Mbar)
    {W : Submodule (ZMod 2) V}
    (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤) :
    ∃ m ∈ Mbar, Submodule.map (m : V →ₗ[ZMod 2] V) W ≠ W := by
  by_contra h
  push Not at h
  have hinv : IsGInvariant Mbar W := by
    intro m hm w hw
    rw [← h m hm]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  rcases hirr W hinv with hbot | htop
  · exact hWbot hbot
  · exact hWtop htop

private theorem second_axis_data
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hker : ∀ v, φ v = 0 ↔ v ∈ W)
    {m : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hmW : Submodule.map (m : V →ₗ[ZMod 2] V) W ≠ W)
    (hWtop : W ≠ ⊤) (hfin : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V) :
    ∃ (W₂ : Submodule (ZMod 2) V) (ψ : Dual (ZMod 2) V),
      W₂ = Submodule.map (m : V →ₗ[ZMod 2] V) W ∧
        ψ = φ ∘ₗ ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) ∧
        (∀ v, ψ v = 0 ↔ v ∈ W₂) ∧ W₂ ≠ ⊤ ∧ ∃ b, b ∈ W₂ ∧ b ∉ W := by
  classical
  let W₂ : Submodule (ZMod 2) V := Submodule.map (m : V →ₗ[ZMod 2] V) W
  let ψ : Dual (ZMod 2) V :=
    φ ∘ₗ ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
  have hmul_inv : ∀ w, (m : V →ₗ[ZMod 2] V)
      (((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) = w := by
    intro w
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) w) (mul_inv_cancel m)
    rwa [show ((m * m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w =
        (m : V →ₗ[ZMod 2] V) (((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) w) from rfl,
      show ((1 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w from rfl] at h
  have hinv_mul : ∀ w, ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((m : V →ₗ[ZMod 2] V) w) = w := by
    intro w
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) w) (inv_mul_cancel m)
    rwa [show ((m⁻¹ * m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w =
        ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((m : V →ₗ[ZMod 2] V) w) from rfl,
      show ((1 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w from rfl] at h
  have hker₂ : ∀ x, ψ x = 0 ↔ x ∈ W₂ := by
    intro x
    constructor
    · intro hx
      have hx' : ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x ∈ W :=
        (hker _).mp hx
      exact Submodule.mem_map.mpr ⟨_, hx', hmul_inv x⟩
    · rintro ⟨w, hw, rfl⟩
      have h1 : ψ (((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) = φ w := by
        change φ (((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          (((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w)) = φ w
        rw [hinv_mul w]
      rw [h1]
      exact (hker w).mpr hw
  have hW₂top : W₂ ≠ ⊤ := by
    intro h
    have hfin2 : finrank (ZMod 2) W₂ = finrank (ZMod 2) W := by
      rw [show finrank (ZMod 2) W₂ = finrank (ZMod 2) (Submodule.map
        (m : V →ₗ[ZMod 2] V) W) from rfl]
      exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod 2) V m : V ≃ₗ[ZMod 2] V) W
    have hV : finrank (ZMod 2) W₂ = finrank (ZMod 2) V := by rw [h, finrank_top]
    omega
  have hsep : ∃ b, b ∈ W₂ ∧ b ∉ W := by
    by_contra h
    push Not at h
    have hle : W₂ ≤ W := fun x hx => h x hx
    have hfin2 : finrank (ZMod 2) W₂ = finrank (ZMod 2) W := by
      rw [show finrank (ZMod 2) W₂ = finrank (ZMod 2) (Submodule.map
        (m : V →ₗ[ZMod 2] V) W) from rfl]
      exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod 2) V m : V ≃ₗ[ZMod 2] V) W
    exact hmW (Submodule.eq_of_le_of_finrank_eq hle hfin2)
  exact ⟨W₂, ψ, rfl, rfl, hker₂, hW₂top, hsep⟩

private theorem transvection_closure_normal
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hY : Y = Subgroup.closure {t | t ∈ Mbar ∧ IsF2Transvection t}) :
    Mbar ≤ Subgroup.normalizer (Y : Set _) := by
  subst hY
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hS : ∀ m ∈ Mbar, ∀ t ∈ {t : LinearMap.GeneralLinearGroup (ZMod 2) V |
      t ∈ Mbar ∧ IsF2Transvection t}, m * t * m⁻¹ ∈
      {t : LinearMap.GeneralLinearGroup (ZMod 2) V | t ∈ Mbar ∧ IsF2Transvection t} := by
    intro m hm t ⟨htM, httv⟩
    exact ⟨Mbar.mul_mem (Mbar.mul_mem hm htM) (Mbar.inv_mem hm), isF2Transvection_conj httv m⟩
  rw [MonoidHom.map_closure]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le (k := (MulAut.conj m) '' {t : LinearMap.GeneralLinearGroup
        (ZMod 2) V | t ∈ Mbar ∧ IsF2Transvection t}) (K := Subgroup.closure
        {t : LinearMap.GeneralLinearGroup (ZMod 2) V | t ∈ Mbar ∧ IsF2Transvection t})).mpr ?_
    rintro x ⟨t, ht, rfl⟩
    exact Subgroup.subset_closure (hS m hm t ht)
  · refine (Subgroup.closure_le (k := {t : LinearMap.GeneralLinearGroup (ZMod 2) V |
        t ∈ Mbar ∧ IsF2Transvection t}) (K := Subgroup.closure
        ((MulAut.conj m) '' {t : LinearMap.GeneralLinearGroup (ZMod 2) V |
          t ∈ Mbar ∧ IsF2Transvection t}))).mpr fun x hx => ?_
    have hx' := hS m⁻¹ (Mbar.inv_mem hm) x hx
    refine Subgroup.subset_closure ⟨m⁻¹ * x * (m⁻¹)⁻¹, hx', ?_⟩
    simp only [MulAut.conj_apply]
    group

private theorem transvection_full_closure
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hY : Y = Subgroup.closure {t | t ∈ Mbar ∧ IsF2Transvection t})
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hφ : φ ≠ 0) (hfull : ∀ a ∈ W, InG Mbar φ a) :
    ∀ a ∈ W, InG Y φ a := by
  intro a ha
  by_cases ha0 : a = 0
  · subst ha0
    exact inG_zero_right φ
  · obtain ⟨h0, htv⟩ := hfull a ha
    refine ⟨h0, ?_⟩
    rw [hY]
    exact Subgroup.subset_closure ⟨htv, (isF2Transvection_iff _).mpr
      ⟨φ, a, h0, hφ, ha0, rfl⟩⟩

private theorem transvection_conj_full
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hnormal : Mbar ≤ Subgroup.normalizer (Y : Set _))
    {m : LinearMap.GeneralLinearGroup (ZMod 2) V} (hmM : m ∈ Mbar)
    {W W₂ : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hW₂ : W₂ = Submodule.map (m : V →ₗ[ZMod 2] V) W)
    (hker₂ : ∀ v, (φ ∘ₗ ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) v = 0 ↔ v ∈ W₂)
    (hfull : ∀ a ∈ W, InG Y φ a) :
    ∀ b ∈ W₂, InG Y (φ ∘ₗ ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) b := by
  intro b hb
  rw [hW₂] at hb
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hb
  have hmem : ((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) a ∈ W₂ := by
    rw [hW₂]
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  have hmem' : (φ ∘ₗ ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) (((m : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) a) = 0 := (hker₂ _).mpr hmem
  refine ⟨hmem', ?_⟩
  obtain ⟨h0, hmY⟩ := hfull a ha
  have hmY' : m * tv φ a h0 * m⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hnormal hmM) _).mp hmY
  have hconj := conj_tv m φ a h0 hmem'
  rw [← hconj]
  exact hmY'

private theorem transvection_closure_eq_top
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (h3 : 3 ≤ finrank (ZMod 2) V)
    (Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : CFSG.ComponentClassification.OutcomeLocal.IsIrreducibleOn Mbar)
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hker : ∀ v, φ v = 0 ↔ v ∈ W) (hφ : φ ≠ 0)
    (hfin : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V)
    (hfull : ∀ a ∈ W, InG Mbar φ a) :
    Mbar = ⊤ := by
  classical
  let S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    {t | t ∈ Mbar ∧ IsF2Transvection t}
  let Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := Subgroup.closure S
  have hgen : GenByTransvections Y := ⟨S, fun t ht => ht.2, rfl⟩
  have hYle : Y ≤ Mbar :=
    (Subgroup.closure_le (k := S) (K := Mbar)).mpr fun t ht => ht.1
  have hnormal : Mbar ≤ Subgroup.normalizer (Y : Set _) := transvection_closure_normal Mbar Y rfl
  have hfullY : ∀ a ∈ W, InG Y φ a := transvection_full_closure rfl hφ hfull
  have hirrY : CFSG.ComponentClassification.OutcomeLocal.IsIrreducibleOn Y :=
    irreducible_transvection_subgroup hnormal hirr hWtop hker hφ hfullY
  obtain ⟨m, hmM, hmW⟩ := exists_second_axis Mbar hirr hWbot hWtop
  obtain ⟨W₂, ψ, hW₂, hψ, hker₂, hW₂top, hsep⟩ := second_axis_data hker hmW hWtop hfin
  subst ψ
  have hfull₂ := transvection_conj_full hnormal hmM hW₂ hker₂ hfullY
  have htopY : Y = ⊤ :=
    image_eq_top h3 Y hgen hirrY hker hker₂ hWtop hW₂top hsep hfullY hfull₂
  rw [eq_top_iff]
  rw [← htopY]
  exact hYle

private theorem axis_proper_nontrivial (hU : IsElemAbelian 2 D.U) (h3 : 3 ≤ rk ↥D.U)
    {W' : Subgroup (VN hU)}
    (hdim : finrank (ZMod 2) (toSubmodule W') + 1 = finrank (ZMod 2) (Additive (VN hU))) :
    (3 ≤ finrank (ZMod 2) (Additive (VN hU))) ∧ toSubmodule W' ≠ ⊥ ∧ toSubmodule W' ≠ ⊤ := by
  have h3' : 3 ≤ finrank (ZMod 2) (Additive (VN hU)) := by
    have h1 : finrank (ZMod 2) (Additive (VN hU)) = rk (VN hU) := by
      rw [← rk_eq_finrank_additive]
    have h2 : rk (VN hU) = rk ↥D.U := rfl
    omega
  refine ⟨h3', ?_, ?_⟩
  · intro h
    have h0 : finrank (ZMod 2) (toSubmodule W') = 0 := by rw [h, finrank_bot]
    omega
  · intro h
    have hfin : finrank (ZMod 2) (toSubmodule W') = finrank (ZMod 2) (Additive (VN hU)) := by
      rw [h, finrank_top]
    omega

private theorem imgGL_eq_top_of_obstruction (c : Ctx23L D Ch)
    (hU : IsElemAbelian 2 D.U) (hUM : D.U ≤ D.M)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G)) (h3 : 3 ≤ rk ↥D.U)
    {g : G} (hTI : D.U ⊓ conjSubgroup D.U g = ⊥) (hO : InCalO 1 D.M ⊥ D.U g)
    (hC : ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g)
    (hirr : IrrOn (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) D.U) :
    imgGL hU (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))
      (inf_le_left.trans hMU) = ⊤ := by
  classical
  let V := Additive (VN hU)
  let Y : Subgroup G := D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)
  have hY : Y ≤ Subgroup.normalizer (D.U : Set G) := inf_le_left.trans hMU
  let e := unitsEquiv V
  let Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    (imgGL hU Y hY).map e.toMonoidHom
  let E : Subgroup G := conjSubgroup D.U g ⊓ D.M
  have hE : E ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  obtain ⟨W', v, φ, hW'card, hker, hvW, hv, hdim, hW'le⟩ :=
    exists_axis_functional hU hUM hMU h3 hTI hO hC
  have hφ : φ ≠ 0 := by
    intro h0
    rw [h0] at hv
    exact zero_ne_one hv
  have hphi : ∀ w ∈ toSubmodule W', φ w = 0 := fun w hw => (hker w).mpr hw
  obtain ⟨h3', hWbot, hWtop⟩ := axis_proper_nontrivial hU h3 hdim
  have hEbar_le : (imgGL hU E hE).map e.toMonoidHom ≤ Mbar := by
    have h1 : imgGL hU E hE ≤ imgGL hU D.M hMU := imgGL_mono hU hE hMU inf_le_right
    have h2 : imgGL hU Y hY = imgGL hU D.M hMU :=
      (imgGL_eq_of_frattini c hU hMU hY).symm
    show (imgGL hU E hE).map e.toMonoidHom ≤ (imgGL hU Y hY).map e.toMonoidHom
    rw [h2]
    exact Subgroup.map_mono h1
  have hfull : ∀ a ∈ toSubmodule W', InG Mbar φ a := by
    intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      exact ⟨hphi 0 ha, by rw [tv_zero_right]; exact Mbar.one_mem⟩
    · refine ⟨hphi a ha, hEbar_le ?_⟩
      exact (imgGL_axis_eq hU hUM hMU hTI hO hC hdim hW'le hphi hvW hv hW'card
        (tv φ a (hphi a ha))).mpr ⟨⟨a, ha⟩, rfl⟩
  have hMbar_top : Mbar = ⊤ :=
    transvection_closure_eq_top h3' Mbar
      (isIrreducibleOn_units (imgGL hU Y hY) (isIrreducibleOn_imgGL hU hY hirr))
      hWbot hWtop hker hφ hdim hfull
  have hmap : (imgGL hU Y hY).map e.toMonoidHom = ⊤ := hMbar_top
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top (e x))
  rwa [e.injective hyx] at hy

private theorem obstruction_TI (c : Ctx23L D Ch) (hUM : D.U ≤ D.M) {g : G}
    (hO : InCalO2 1 D.M ⊥ D.U g) : D.U ⊓ conjSubgroup D.U g = ⊥ := by
  have h := c.hTI g⁻¹
  simp only [CFSG.CGT.Timmesfeld75.conjSubgroup, CFSG.Quasithin.conjSubgroup] at h
  rcases h with hbot | heq
  · exact hbot
  · exfalso
    apply hO.1.2.1
    exact (inf_eq_left.mp heq).trans (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUM)

private theorem obstruction_centralizer (c : Ctx23L D Ch) (hUM : D.U ≤ D.M) {g : G}
    (hO : InCalO2 1 D.M ⊥ D.U g) :
    ∀ e ∈ conjSubgroup D.U g ⊓ D.M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup D.M g := by
  intro e he he1
  have hgeU : g * e * g⁻¹ ∈ D.U := (CFSG.Quasithin.mem_conjSubgroup_iff).mp he.1
  have hge1 : g * e * g⁻¹ ≠ 1 := by
    intro h
    apply he1
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  have hC := Ctx23.centralizer_le_M c.toCtx23 hgeU hge1
  intro x hx
  rw [CFSG.Quasithin.mem_conjSubgroup_iff]
  apply hC
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * e * g⁻¹) = g * (x * e) * g⁻¹ := by group
    _ = g * (e * x) * g⁻¹ := by rw [hx]
    _ = g * e * g⁻¹ * (g * x * g⁻¹) := by group

private theorem obstruction_K_subnormal (c : Ctx23L D Ch) (hU : IsElemAbelian 2 D.U)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    (hMtop : imgGL hU (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))
      (inf_le_left.trans hMU) = ⊤)
    {L₁ : Subgroup G}
    (hL₁ : L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))) :
    CFSG.Open.IsSubnormal (imgGL hU (L₁ ⊓ D.M) (inf_le_right.trans hMU)) ⊤ := by
  let H : Subgroup G := Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)
  let Y : Subgroup G := D.M ⊓ H
  let A : Subgroup G := L₁ ⊓ D.M
  have hY : Y ≤ Subgroup.normalizer (D.U : Set G) := inf_le_left.trans hMU
  have hA : A ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  have hAY : A ≤ Y := le_inf inf_le_right (inf_le_left.trans hL₁.2.le)
  have hsub : CFSG.Open.IsSubnormal A Y := by
    have h1 := CFSG.Open.IsSubnormal.inf hL₁.2 Y
    have h1' : L₁ ⊓ Y = A := by
      show L₁ ⊓ (D.M ⊓ H) = L₁ ⊓ D.M
      calc L₁ ⊓ (D.M ⊓ H) = (L₁ ⊓ D.M) ⊓ H := (inf_assoc L₁ D.M H).symm
        _ = L₁ ⊓ D.M := inf_eq_left.mpr (inf_le_left.trans hL₁.2.le)
    rwa [h1', inf_eq_right.mpr inf_le_right] at h1
  let f : ↥Y →* ↥(imgGL hU Y hY) :=
    { toFun := fun y => ⟨actGL hU Y hY y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp x.2
    exact ⟨y, Subtype.ext hy⟩
  have hmapM : ((A.subgroupOf Y).map f).IsSubnormal :=
    Subgroup.IsSubnormal.map hf (CFSG.Open.IsSubnormal.subgroupOf hsub)
  have hEq : (A.subgroupOf Y).map f = (imgGL hU A hA).subgroupOf (imgGL hU Y hY) := by
    ext x
    constructor
    · rintro ⟨y, hy, hfy⟩
      refine ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
      exact congrArg (fun z : ↥(imgGL hU Y hY) =>
        (z : CFSG.Quasithin.G11.GLV (Additive (VN hU)))) hfy
    · intro hx
      rw [Subgroup.mem_subgroupOf, mem_imgGL] at hx
      obtain ⟨a, ha⟩ := hx
      refine ⟨⟨a.1, hAY a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, ?_⟩
      exact Subtype.ext ha
  have hsubImg : CFSG.Open.IsSubnormal (imgGL hU A hA) (imgGL hU Y hY) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf (imgGL_mono hU hA hY hAY)).mpr (hEq ▸ hmapM)
  rwa [hMtop] at hsubImg

private theorem U0_le_U (c : Ctx23L D Ch) : c.U0 ≤ D.U :=
  uc22p22v_conjClosure_le (inf_le_right.trans (le_normalizer_uCore D.M D.T)) (Data.Z_le_U D)

private theorem obstruction_centralizes_of_bot (hU : IsElemAbelian 2 D.U)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G)) {L₁ : Subgroup G}
    (hK : imgGL hU (L₁ ⊓ D.M) (inf_le_right.trans hMU) = ⊥) :
    L₁ ⊓ D.M ≤ Subgroup.centralizer (D.U : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hA : L₁ ⊓ D.M ≤ Subgroup.normalizer (D.U : Set G) := inf_le_right.trans hMU
  have h1 : actGL hU (L₁ ⊓ D.M) hA ⟨x, hx⟩ = 1 := by
    have h2 : actGL hU (L₁ ⊓ D.M) hA ⟨x, hx⟩ ∈ imgGL hU (L₁ ⊓ D.M) hA :=
      MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    rw [hK] at h2
    exact Subgroup.mem_bot.mp h2
  have hx' := (actGL_eq_one_iff hU (L₁ ⊓ D.M) hA ⟨x, hx⟩).mp h1
  exact (Subgroup.mem_centralizer_iff.mp hx') u hu

private theorem exists_order_two_subgroup (c : Ctx23L D Ch) {k : ℕ}
    (hcard : Nat.card c.U0 = 2 ^ k) (hk2 : 2 ≤ k) :
    ∃ P : Subgroup G, P ≤ c.U0 ∧ P ≠ ⊥ ∧ P ≠ c.U0 := by
  have h2k : 2 ∣ Nat.card c.U0 := by
    have h1 : 2 ^ 1 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    simpa [hcard] using h1
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2k
  let P : Subgroup G := Subgroup.zpowers (x : G)
  have hPle : P ≤ c.U0 := Subgroup.zpowers_le.mpr x.2
  have hPcard : Nat.card P = 2 := by
    change Nat.card (Subgroup.zpowers (x : G)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hx2
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h] at hPcard
    exact absurd hPcard (by norm_num)
  have hPlt : P ≠ c.U0 := by
    intro h
    have h2eq : 2 ^ k = 2 := by rw [← hcard, ← h, hPcard]
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    omega
  exact ⟨P, hPle, hPne, hPlt⟩

private theorem obstruction_K_ne_bot (c : Ctx23L D Ch) (hU : IsElemAbelian 2 D.U)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0) {k : ℕ} (hcard : Nat.card c.U0 = 2 ^ k) (hk2 : 2 ≤ k)
    {L₁ : Subgroup G} (hL0L₁ : c.L0 ≤ L₁) :
    imgGL hU (L₁ ⊓ D.M) (inf_le_right.trans hMU) ≠ ⊥ := by
  intro hK
  have hcent := obstruction_centralizes_of_bot hU hMU hK
  have hL0M : c.L0 ⊓ D.M ≤ L₁ ⊓ D.M := le_inf (inf_le_left.trans hL0L₁) inf_le_right
  obtain ⟨P, hPle, hPne, hPlt⟩ := exists_order_two_subgroup c hcard hk2
  have hPinv : c.L0 ⊓ D.M ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    refine (Subgroup.mem_normalizer_iff).mpr (fun p => ?_)
    constructor
    · intro hp
      have hpU : p ∈ D.U := U0_le_U c (hPle hp)
      have hyC : y ∈ Subgroup.centralizer (D.U : Set G) := hcent (hL0M hy)
      have hcomm : y * p = p * y := (Subgroup.mem_centralizer_iff.mp hyC p hpU).symm
      rw [show y * p * y⁻¹ = p from by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]]
      exact hp
    · intro hp
      have hy' : y⁻¹ ∈ c.L0 ⊓ D.M := (c.L0 ⊓ D.M).inv_mem hy
      have hy'C : y⁻¹ ∈ Subgroup.centralizer (D.U : Set G) := hcent (hL0M hy')
      have hpU : y * p * y⁻¹ ∈ D.U := U0_le_U c (hPle hp)
      have hcomm : y⁻¹ * (y * p * y⁻¹) = (y * p * y⁻¹) * y⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp hy'C _ hpU).symm
      rw [show p = y⁻¹ * (y * p * y⁻¹) * y from by group,
        show y⁻¹ * (y * p * y⁻¹) * y = y * p * y⁻¹ from by rw [hcomm]; group]
      exact hp
  rcases hirr P hPle hPinv with h | h
  · exact hPne h
  · exact hPlt h

private theorem obstruction_K_normalizes (hU : IsElemAbelian 2 D.U)
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G))
    {c : Ctx23L D Ch} {L₁ : Subgroup G}
    (hU0inv : L₁ ⊓ D.M ≤ Subgroup.normalizer (c.U0 : Set G))
    {U₀ : Subgroup (VN hU)}
    (hU₀ : ∀ u : VN hU, u ∈ U₀ ↔ (VN.toN u : G) ∈ c.U0) :
    ∀ k ∈ imgGL hU (L₁ ⊓ D.M) (inf_le_right.trans hMU), ∀ u ∈ U₀,
      Additive.toMul ((k : Additive (VN hU) →ₗ[ZMod 2] Additive (VN hU))
        (Additive.ofMul u)) ∈ U₀ := by
  rintro k ⟨a, rfl⟩ u hu
  have hu0 : ((VN.toN u : ↥D.U) : G) ∈ c.U0 := (hU₀ u).mp hu
  have ha : (a : G) ∈ L₁ ⊓ D.M := a.2
  have hconj : (a : G) * ((VN.toN u : ↥D.U) : G) * (a : G)⁻¹ ∈ c.U0 :=
    (Subgroup.mem_normalizer_iff.mp (hU0inv ha) ((VN.toN u : ↥D.U) : G)).mp hu0
  rw [hU₀]
  exact hconj

private theorem U0_data (c : Ctx23L D Ch) (hU : IsElemAbelian 2 D.U) {k : ℕ} (hk2 : 2 ≤ k)
    (hcard : Nat.card c.U0 = 2 ^ k) (hlt : c.U0 < D.U) :
    ∃ U₀ : Subgroup (VN hU), U₀ ≠ ⊥ ∧ U₀ ≠ ⊤ ∧
      (∀ u : VN hU, u ∈ U₀ ↔ (VN.toN u : G) ∈ c.U0) := by
  let U₀ : Subgroup (VN hU) :=
    { carrier := (c.U0.subgroupOf D.U).carrier
      mul_mem' := fun hx hy => (c.U0.subgroupOf D.U).mul_mem hx hy
      one_mem' := (c.U0.subgroupOf D.U).one_mem
      inv_mem' := fun hx => (c.U0.subgroupOf D.U).inv_mem hx }
  have hU₀ : ∀ u : VN hU, u ∈ U₀ ↔ (VN.toN u : G) ∈ c.U0 := by
    intro u
    rw [show u ∈ U₀ ↔ u ∈ c.U0.subgroupOf D.U from Iff.rfl]
    exact Subgroup.mem_subgroupOf
  have hcardU0 : Nat.card U₀ = Nat.card c.U0 := by
    change Nat.card ↥(c.U0.subgroupOf D.U) = Nat.card ↥c.U0
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U0_le_U c)).toEquiv
  have hU₀ne : U₀ ≠ ⊥ := by
    intro h
    have h1 : Nat.card U₀ = 1 := by rw [h]; simp
    have h4 : 4 ≤ Nat.card c.U0 := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    omega
  have hU₀lt : U₀ ≠ ⊤ := by
    intro h
    have hcardU : Nat.card D.U = Nat.card c.U0 := by
      calc Nat.card D.U = Nat.card (⊤ : Subgroup (VN hU)) := by
            rw [Subgroup.card_top]
            rfl
        _ = Nat.card U₀ := by rw [h]
        _ = Nat.card c.U0 := hcardU0
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge (U0_le_U c) (le_of_eq hcardU))
  exact ⟨U₀, hU₀ne, hU₀lt, hU₀⟩

namespace Ctx23L

theorem not_exists_inCalO2_one (c : Ctx23L D Ch) (k : ℕ) (hk2 : 2 ≤ k)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hcard : Nat.card c.U0 = 2 ^ k) (hlt : c.U0 < D.U) (h3 : 3 ≤ rk ↥D.U)
    (L₁ : Subgroup G)
    (hL₁ : L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)))
    (hL0L₁ : c.L0 ≤ L₁) (hU0inv : L₁ ⊓ D.M ≤ Subgroup.normalizer (c.U0 : Set G)) :
    ¬ ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  rintro ⟨g, hO⟩
  have hU : IsElemAbelian 2 D.U :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2
  have hUM : D.U ≤ D.M :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).1.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M))
  have hMU : D.M ≤ Subgroup.normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  have hTI : D.U ⊓ conjSubgroup D.U g = ⊥ := obstruction_TI c hUM hO
  have hC := obstruction_centralizer c hUM hO
  have hirrY : IrrOn (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) D.U :=
    irrOn_normalizer_wClos c hU0 hirr
  have hMtop := imgGL_eq_top_of_obstruction c hU hUM hMU h3 hTI hO.1 hC hirrY
  have hKsub := obstruction_K_subnormal c hU hMU hMtop hL₁
  have hKne := obstruction_K_ne_bot c hU hMU hirr hcard hk2 hL0L₁
  obtain ⟨U₀, hU₀ne, hU₀lt, hU₀⟩ := U0_data c hU hk2 hcard hlt
  exact false_of_obstruction (U := VN hU) h3 hMtop (hMtop.symm ▸ hKsub) hKne hU₀ne hU₀lt
    (obstruction_K_normalizes hU hMU hU0inv hU₀)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
