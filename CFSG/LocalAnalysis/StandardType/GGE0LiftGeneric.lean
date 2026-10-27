module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType.ClassicalPosition

theorem largeEvenMarking_of_isComponentOf_pi
    {r : ℕ} {H : Fin r → Type} [∀ k, Group (H k)] [∀ k, Finite (H k)]
    (hH : ∀ k, ∀ C : Subgroup (H k), IsComponentOf C ⊤ →
      LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True))
    {C : Subgroup (∀ k, H k)} (hC : IsComponentOf C ⊤) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  classical
  obtain ⟨i, hi⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.exists_factor_of_isComponentOf_top (CFSG.Assembly.isComponentOf_iff_open.1 hC)
  let F := CFSG.LieType.SemisimpleCentralizers.Held.factorSub (H := H) i
  let e : ↥F ≃* ↥(⊤ : Subgroup (H i)) :=
    { toFun := fun w => ⟨w.1 i, trivial⟩
      invFun := fun a => ⟨Pi.mulSingle i a.1,
        CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mpr
          (fun j hj => Pi.mulSingle_eq_of_ne hj a.1)⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext j
        by_cases hj : j = i
        · subst j
          simp
        · simp [hj, CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mp w.2 j hj]
      right_inv := fun a => by apply Subtype.ext; simp
      map_mul' := fun a b => rfl }
  exact largeEvenMarking_of_isComponentOf_mulEquiv e (hH i)
    (hC.of_le_of_le hi le_top)

private theorem ggE0Concl_factorSub {r : ℕ} {H : Fin r → Type} [∀ k, Group (H k)]
    (hH : ∀ k, ∀ C : Subgroup (H k), IsComponentOf C ⊤ → GGE0Concl (⊤ : Subgroup (H k)) C)
    (i : Fin r) {C : Subgroup (∀ k, H k)}
    (hC : IsComponentOf C (CFSG.LieType.SemisimpleCentralizers.Held.factorSub (H := H) i)) :
    GGE0Concl (CFSG.LieType.SemisimpleCentralizers.Held.factorSub (H := H) i) C := by
  let e : H i →* ∀ k, H k := MonoidHom.mulSingle H i
  have he : Function.Injective e := by
    intro a b hab
    simpa [e, MonoidHom.mulSingle_apply] using congrFun hab i
  have hfac : (⊤ : Subgroup (H i)).map e =
      CFSG.LieType.SemisimpleCentralizers.Held.factorSub (H := H) i := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨a, -, rfl⟩
      exact CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mpr
        (fun j hj => Pi.mulSingle_eq_of_ne hj a)
    · intro w hw
      have hw' : ∀ j, j ≠ i → w j = 1 :=
        CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mp hw
      refine ⟨w i, trivial, ?_⟩
      funext j
      by_cases hj : j = i
      · subst j
        simp [e]
      · simp [e, hj, hw' j hj]
  have hrange : e.range =
      CFSG.LieType.SemisimpleCentralizers.Held.factorSub (H := H) i := by
    rw [MonoidHom.range_eq_map, hfac]
  have hmapC : (C.comap e).map e = C :=
    Subgroup.map_comap_eq_self (f := e) (H := C) (by rw [hrange]; exact hC.1)
  have hcomp : IsComponentOf (C.comap e) ⊤ :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff he).1 (by
      rw [hmapC, hfac]
      exact hC)
  have h := (ggE0Concl_map_iff e he ⊤ (C.comap e)).mpr (hH i (C.comap e) hcomp)
  rwa [hfac, hmapC] at h

theorem ggE0Concl_pi {r : ℕ} {H : Fin r → Type} [∀ k, Group (H k)] [∀ k, Finite (H k)]
    (hH : ∀ k, ∀ C : Subgroup (H k), IsComponentOf C ⊤ → GGE0Concl (⊤ : Subgroup (H k)) C)
    {C : Subgroup (∀ k, H k)} (hC : IsComponentOf C ⊤) :
    GGE0Concl (⊤ : Subgroup (∀ k, H k)) C := by
  classical
  let F : Fin r → Subgroup (∀ k, H k) :=
    CFSG.LieType.SemisimpleCentralizers.Held.factorSub
  have htop : (⨆ i, F i) = ⊤ := by
    refine eq_top_iff.mpr fun w _ =>
      Subgroup.pi_mem_of_mulSingle_mem w fun i => Subgroup.mem_iSup_of_mem i ?_
    exact CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mpr
      (fun j hj => Pi.mulSingle_eq_of_ne hj _)
  have hcomm : ∀ i ∈ (Finset.univ : Finset (Fin r)), ∀ j ∈ Finset.univ, i ≠ j →
      ∀ x ∈ F i, ∀ y ∈ F j, Commute x y := by
    intro i _ j _ hij x hx y hy
    have hx' : ∀ k, k ≠ i → x k = 1 :=
      CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mp hx
    have hy' : ∀ k, k ≠ j → y k = 1 :=
      CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mp hy
    ext k
    by_cases hk : k = i
    · subst k
      simp [hy' i hij]
    · simp [hx' k hk]
  have hblock : ∀ i ∈ (Finset.univ : Finset (Fin r)), ∀ C : Subgroup (∀ k, H k),
      IsComponentOf C (F i) → GGE0Concl (F i) C :=
    fun i _ C hC => ggE0Concl_factorSub hH i hC
  have htop' : (⨆ i ∈ (Finset.univ : Finset (Fin r)), F i) = ⊤ := by
    simpa using htop
  rw [← htop'] at hC ⊢
  exact ggE0Concl_biSup Finset.univ F hcomm hblock hC

private theorem largeEvenMarking_of_centerQuotEquiv {X Y : Type} [Group X] [Group Y]
    (hX : commutator X = ⊤)
    (e : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y)
    {P : LargeEvenMarkProp X} {P' : LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ → P lab R I F (e.trans θ))
    (h : LargeEvenMarking Y P') : LargeEvenMarking X P := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.trans θ, hPP' lab R I F θ hθ⟩

private theorem exists_centerQuotEquiv_of_isGLLift {U H G : Type} [Group U] [Group H] [Group G]
    (j : U →* H) (hj : Function.Injective j) (ψ : U →* G)
    (hψ : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U}
    (hJ' : CFSG.Assembly.IsQuasisimple ↥J') :
    ∃ e : ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) ≃*
        ↥(J'.map j) ⧸ Subgroup.center ↥(J'.map j),
      ∀ u : ↥J', e (QuotientGroup.mk (ψ.subgroupMap J' u)) =
        QuotientGroup.mk (Subgroup.equivMapOfInjective J' j hj u) := by
  let πψ : ↥J' →* ↥(J'.map ψ) := ψ.subgroupMap J'
  have hsurj : Function.Surjective πψ := MonoidHom.subgroupMap_surjective ψ J'
  have hker : πψ.ker ≤ Subgroup.center ↥J' := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    have h1 : ψ (u : U) = 1 := by
      exact congrArg (fun x : ↥(J'.map ψ) => (x : G)) (MonoidHom.mem_ker.mp hu)
    exact Subgroup.mem_center_iff.mp (hψ (MonoidHom.mem_ker.mpr h1)) (p : U)
  have hc : Subgroup.center ↥J' =
      ((QuotientGroup.mk' (Subgroup.center ↥(J'.map ψ))).comp πψ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect ⟨hJ'.1⟩ πψ hsurj hker]
  let eψ : ↥J' ⧸ Subgroup.center ↥J' ≃* ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hsurj))
  have hEψ : ∀ u : ↥J', eψ (QuotientGroup.mk u) = QuotientGroup.mk (πψ u) := by
    intro u
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk
      ((QuotientGroup.mk' (Subgroup.center ↥(J'.map ψ))).comp πψ) u
  refine ⟨eψ.symm.trans (centerQuotCongr (Subgroup.equivMapOfInjective J' j hj)), fun u => ?_⟩
  rw [MulEquiv.trans_apply, eψ.symm_apply_eq.mpr (hEψ u).symm, centerQuotCongr_mk]

private theorem le_normalizer_of_isGLLift_action {U H G : Type} [Group U] [Group H] [Group G]
    (j : U →* H) (hj : Function.Injective j) (ψ : U →* G) {A : Subgroup H}
    {J' : Subgroup U} (hAn : A ≤ Subgroup.normalizer (J'.map j : Set H)) {E₀ : Subgroup G}
    (hact : ∀ ε ∈ E₀, ∃ a ∈ A, ∀ u : U, ∃ u' : U,
      j u' = a⁻¹ * j u * a ∧ ε⁻¹ * ψ u * ε = ψ u') :
    E₀ ≤ Subgroup.normalizer (J'.map ψ : Set G) := by
  have hstep : ∀ δ ∈ E₀, ∀ x ∈ J'.map ψ, δ⁻¹ * x * δ ∈ J'.map ψ := by
    intro δ hδ x hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨a, ha, hactδ⟩ := hact δ hδ
    obtain ⟨u', hu'j, hu'ψ⟩ := hactδ u
    have hmem : a⁻¹ * j u * a ∈ J'.map j :=
      (Subgroup.mem_set_normalizer_iff''.mp (hAn ha) (j u)).mp (Subgroup.mem_map_of_mem j hu)
    have hu' : u' ∈ J' := (Subgroup.mem_map_iff_mem hj).mp (hu'j ▸ hmem)
    rw [hu'ψ]
    exact Subgroup.mem_map_of_mem ψ hu'
  intro ε hε
  rw [Subgroup.mem_set_normalizer_iff'']
  intro h
  refine ⟨fun hh => hstep ε hε h hh, fun hh => ?_⟩
  have h' := hstep ε⁻¹ (E₀.inv_mem hε) (ε⁻¹ * h * ε) hh
  rwa [show ε⁻¹⁻¹ * (ε⁻¹ * h * ε) * ε⁻¹ = h from by group] at h'

private theorem largeEvenMarking_of_isGLLift_action {U H G : Type} [Group U] [Group H] [Group G]
    (j : U →* H) (hj : Function.Injective j) (ψ : U →* G) (hψ : ψ.ker ≤ Subgroup.center U)
    {A : Subgroup H} {J' : Subgroup U} (hJ' : CFSG.Assembly.IsQuasisimple ↥J')
    (hA : GGE0Concl A (J'.map j)) {E₀ : Subgroup G}
    (hact : ∀ ε ∈ E₀, ∃ a ∈ A, ∀ u : U, ∃ u' : U,
      j u' = a⁻¹ * j u * a ∧ ε⁻¹ * ψ u * ε = ψ u')
    (hm : LargeEvenMarking ↥(J'.map ψ) (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking ↥(J'.map ψ)
      (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ E₀, ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' => (l' : G) = ε⁻¹ * l * ε) φ) := by
  let πψ : ↥J' →* ↥(J'.map ψ) := ψ.subgroupMap J'
  let πj : ↥J' ≃* ↥(J'.map j) := Subgroup.equivMapOfInjective J' j hj
  obtain ⟨ec, hEc⟩ := exists_centerQuotEquiv_of_isGLLift j hj ψ hψ hJ'
  have hJc : ⁅(⊤ : Subgroup ↥J'), ⊤⁆ = ⊤ := hJ'.1
  have hCj : commutator ↥(J'.map j) = ⊤ := by
    have h := Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) πj.toMonoidHom
    rw [hJc, Subgroup.map_top_of_surjective _ πj.surjective] at h
    exact h.symm
  have hCψ : commutator ↥(J'.map ψ) = ⊤ := by
    have h := Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) πψ
    rw [hJc, Subgroup.map_top_of_surjective _
      (MonoidHom.subgroupMap_surjective ψ J')] at h
    exact h.symm
  have hmarkCj : LargeEvenMarking ↥(J'.map j) (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_of_centerQuotEquiv hCj ec.symm
      (fun _ _ _ _ _ _ _ => trivial) hm
  refine largeEvenMarking_of_centerQuotEquiv hCψ ec ?_ (hA.2 hmarkCj)
  intro lab R _ I F θ hθ
  obtain ⟨htag, hAind⟩ := hθ
  refine ⟨htag, fun ε hε => ?_⟩
  obtain ⟨a, ha, hactε⟩ := hact ε hε
  obtain ⟨φ, hφI, hφ⟩ := hAind a ha
  refine ⟨φ, hφI, fun l l' hrel => ?_⟩
  obtain ⟨u, hu⟩ := MonoidHom.subgroupMap_surjective ψ J' l
  obtain ⟨v, hvj, hvψ⟩ := hactε u
  have hmem : a⁻¹ * j u * a ∈ J'.map j :=
    (Subgroup.mem_set_normalizer_iff''.mp (hA.1 ha) (j u)).mp (Subgroup.mem_map_of_mem j u.2)
  have hv : v ∈ J' := (Subgroup.mem_map_iff_mem hj).mp (hvj ▸ hmem)
  have hul : ψ u = (l : G) := congrArg Subtype.val hu
  have hvl : πψ ⟨v, hv⟩ = l' := by
    apply Subtype.ext
    rw [show ((πψ ⟨v, hv⟩ : ↥(J'.map ψ)) : G) = ψ v from rfl, ← hvψ, hul]
    exact hrel.symm
  have h1 : (ec.trans θ) (QuotientGroup.mk l) = θ (QuotientGroup.mk (πj u)) := by
    rw [MulEquiv.trans_apply, ← hu, hEc u]
  have h2 : (ec.trans θ) (QuotientGroup.mk l') = θ (QuotientGroup.mk (πj ⟨v, hv⟩)) := by
    rw [MulEquiv.trans_apply, ← hvl, hEc ⟨v, hv⟩]
  calc φ ((ec.trans θ) (QuotientGroup.mk l))
      = φ (θ (QuotientGroup.mk (πj u))) := by rw [h1]
    _ = θ (QuotientGroup.mk (πj ⟨v, hv⟩)) := hφ _ _ (by simpa [πj] using hvj)
    _ = (ec.trans θ) (QuotientGroup.mk l') := h2.symm

theorem ggE0Concl_of_isGLLift_action {U H G : Type} [Group U] [Group H] [Group G]
    (j : U →* H) (hj : Function.Injective j) (ψ : U →* G) (hψ : ψ.ker ≤ Subgroup.center U)
    {A : Subgroup H} {J' : Subgroup U} (hJ' : CFSG.Assembly.IsQuasisimple ↥J')
    (hA : GGE0Concl A (J'.map j)) {E₀ : Subgroup G}
    (hact : ∀ ε ∈ E₀, ∃ a ∈ A, ∀ u : U, ∃ u' : U,
      j u' = a⁻¹ * j u * a ∧ ε⁻¹ * ψ u * ε = ψ u') :
    GGE0Concl E₀ (J'.map ψ) := by
  refine ⟨le_normalizer_of_isGLLift_action j hj ψ hA.1 hact, fun hm => ?_⟩
  exact largeEvenMarking_of_isGLLift_action j hj ψ hψ hJ' hA hact hm

theorem commute_of_val_eq_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {u : GL ι F} (hu : ∃ a : F, (u : Matrix ι ι F) = Matrix.scalar ι a) (t : GL ι F) :
    Commute u t := by
  obtain ⟨a, ha⟩ := hu
  show u * t = t * u
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ha]
  exact Matrix.scalar_commute a (fun _ => Commute.all _ _) _

theorem commute_of_inv_mul_eq_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {s₀ s t : GL ι F} (h₀ : Commute s₀ t)
    (hs : ∃ a : F, ((s₀⁻¹ * s : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a) :
    Commute s t := by
  have h := h₀.mul_left (commute_of_val_eq_scalar hs t)
  rwa [mul_inv_cancel_left] at h

theorem pow_eq_one_of_commutator_eq_scalar {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Nonempty ι] {s t : GL ι F} {a : F} {p : ℕ}
    (ha : (((t * s)⁻¹ * (s * t) : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a)
    (htp : ∃ μ : F, ((t ^ p : GL ι F) : Matrix ι ι F) = Matrix.scalar ι μ) :
    a ^ p = 1 := by
  set ζ : GL ι F := (t * s)⁻¹ * (s * t) with hζdef
  have hζt : Commute ζ t := commute_of_val_eq_scalar ⟨a, ha⟩ t
  have hζs : Commute ζ s := commute_of_val_eq_scalar ⟨a, ha⟩ s
  have hmul : s * t = t * s * ζ := by
    rw [hζdef]
    exact (mul_inv_cancel_left (t * s) (s * t)).symm
  have hconj : s * t * s⁻¹ = t * ζ := by
    calc s * t * s⁻¹ = (t * s * ζ) * s⁻¹ := by rw [hmul]
      _ = t * (s * ζ * s⁻¹) := by simp only [mul_assoc]
      _ = t * ζ := by rw [← hζs.eq]; group
  obtain ⟨μ, hμ⟩ := htp
  have hcomm : Commute (t ^ p) s := commute_of_val_eq_scalar ⟨μ, hμ⟩ s
  have h1 : s * t ^ p * s⁻¹ = (t * ζ) ^ p := by
    rw [← hconj, conj_pow]
  have h2 : s * t ^ p * s⁻¹ = t ^ p := by
    rw [← hcomm.eq]
    group
  have h3 : (t * ζ) ^ p = t ^ p * ζ ^ p := hζt.symm.mul_pow p
  have h4 : ζ ^ p = 1 := by
    rw [h1, h3] at h2
    exact mul_left_cancel (by rw [h2, mul_one])
  have h5 : ((ζ : Matrix ι ι F)) ^ p = (1 : Matrix ι ι F) := by
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
  rw [show (ζ : Matrix ι ι F) = Matrix.scalar ι a from ha, ← map_pow] at h5
  have h6 : Matrix.scalar ι (a ^ p) = Matrix.scalar ι 1 := by
    rw [h5, map_one]
  exact Matrix.scalar_inj.mp h6

theorem isGLLift_commute_of_mem_closure {U X ι F : Type} [Group U] [Group X] [Finite X]
    [Fintype ι] [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X}
    (huniq : ∀ {s s' : GL ι F} {c : X}, IsGLLift j ψ s c → IsGLLift j ψ s' c →
      ∃ a : F, ((s'⁻¹ * s : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a)
    {S : Set X} (hlift : ∀ c ∈ Subgroup.closure S, ∃ s, IsGLLift j ψ s c) {t : GL ι F}
    (hS : ∀ c ∈ S, ∀ s, IsGLLift j ψ s c → Commute s t) :
    ∀ c ∈ Subgroup.closure S, ∀ s, IsGLLift j ψ s c → Commute s t := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem c hc => exact hS c hc
  | one =>
      intro s hs
      exact commute_of_inv_mul_eq_scalar (Commute.one_left t) (huniq hs isGLLift_one)
  | mul x y hx hy ihx ihy =>
      intro s hs
      obtain ⟨sx, hsx⟩ := hlift x hx
      obtain ⟨sy, hsy⟩ := hlift y hy
      exact commute_of_inv_mul_eq_scalar ((ihy sy hsy).mul_left (ihx sx hsx))
        (huniq hs (hsx.mul hsy))
  | inv x hx ihx =>
      intro s hs
      obtain ⟨sx, hsx⟩ := hlift x hx
      have hk : x ^ (orderOf x - 1) = x⁻¹ :=
        eq_inv_of_mul_eq_one_left (by
          rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one])
      have hpow := hsx.pow (orderOf x - 1)
      rw [hk] at hpow
      exact commute_of_inv_mul_eq_scalar ((ihx sx hsx).pow_left _) (huniq hs hpow)

theorem odd_orderOf_of_pow_eq_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {s : GL ι F} {p : ℕ} (hp : Odd p) {a : F}
    (hs : ((s ^ p : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a) : Odd (orderOf s) := by
  classical
  have fF : Fintype F := Fintype.ofFinite F
  by_cases hι : Nonempty ι
  · have hunit : IsUnit (Matrix.scalar ι a) := ⟨s ^ p, hs⟩
    have ha : a ≠ 0 := by
      rintro rfl
      exact hunit.ne_zero (map_zero (Matrix.scalar ι))
    obtain ⟨k, -, hq⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (k : ℕ) := by
      rw [Nat.card_eq_fintype_card, hq]
    have hpos : 1 ≤ Nat.card F := by
      rw [hcard]
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hEven : Even (Nat.card F) := by
      rw [hcard, Nat.even_pow]
      exact ⟨even_two, k.pos.ne'⟩
    have hOdd : Odd (Fintype.card F - 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.Even.sub_odd hpos hEven odd_one
    have hpow : s ^ (p * (Fintype.card F - 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, ← Units.val_pow_eq_pow_val s p, hs,
        ← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
      simp
    exact (hp.mul hOdd).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · have hι' : IsEmpty ι := not_nonempty_iff.mp hι
    have hs1 : s = 1 := Subsingleton.elim s 1
    rw [hs1, orderOf_one]
    exact odd_one

section Ctx


theorem map_conj_le_ggG1 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hSt : GGSteinbergCorrectionAt t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) {g : G}
    (hg : g ∈ ggM p B x L D J) {H : Subgroup G} (hH : H ≤ ggG1 ψ) :
    H.map (MulAut.conj g⁻¹).toMonoidHom ≤ ggG1 ψ := by
  have hP : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
    ⟨hctx.2.2.2.1, ⟨hctx.range_eq, hctx.2.2.2.2.1.2⟩, hctx.perfect, hctx.lieModel⟩
  have hSt' : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible (ggU t n f).D ψ (m * g) := by
    intro m hm
    rw [hctx.range_eq] at hm ⊢
    exact hSt G n f ψ _ hP m hm
  have hNorm := ggG1_conj_mem_of_steinberg hctx.range_eq hSt'
  rintro _ ⟨h, hh, rfl⟩
  have hc := hNorm g⁻¹ (inv_mem hg) h (hH hh)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hc

end Ctx

private theorem card_bstar_inf_centralizer_le_of_sstar {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hS : LargeEvenSStar p B x L) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p ^ 2 := by
  have hpow : ∀ z : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)), z ^ p = 1 := fun z =>
    Subtype.ext (by simpa using hBs.2 (z : G) z.2.1)
  have hSp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    fun z => ⟨1, by simpa using hpow z⟩
  have hcyc : IsCyclic ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    hS.2.2.2.2 _ inf_le_right hSp
  have hexp : Monoid.exponent ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have hle : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  exact hle.trans (by rw [sq]; exact Nat.le_mul_of_pos_right p hp.pos)

theorem ggE0_rigid_generators {G : Type} [Group G] [Finite G] {U : Type} [Group U]
    {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {g : G} (hg : g ∈ ggM p B x L D J) :
    ∃ x' y' : G, D.map (MulAut.conj g⁻¹).toMonoidHom = Subgroup.closure {x', y'} ∧
      ∀ z ∈ ({x', y'} : Set G), z ∈ Bs.map (MulAut.conj g⁻¹).toMonoidHom ∧
        ∃ L' : Subgroup G, IsComponentOf L' (ggG0 p B x L D J ⊓ Subgroup.centralizer {z}) ∧
          Nat.card ↥(Bs.map (MulAut.conj g⁻¹).toMonoidHom ⊓
            Subgroup.centralizer (L' : Set G)) ≤ p ^ 2 := by
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hctx.stdType hctx.stdSub
  have hyB : y ∈ B := hnbr.1.2.1
  have hxBs : x ∈ Bs := hctx.d_le_bstar hctx.x_mem_d
  have hyBs : y ∈ Bs := hctx.bstar.1 hyB
  have hgN : g⁻¹ ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := Subgroup.inv_mem _ hg
  refine ⟨(MulAut.conj g⁻¹) x, (MulAut.conj g⁻¹) y, ?_, ?_⟩
  · rw [hnbr.2.1, MonoidHom.map_closure]
    simp
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · refine ⟨Subgroup.mem_map.mpr ⟨x, hxBs, rfl⟩, L.map (MulAut.conj g⁻¹).toMonoidHom,
        ?_, ?_⟩
      · have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
          (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).2
          hctx.l_isComponentOf_inf
        rw [CFSG.centralizer_inter_map,
          CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_mem_normalizer hgN] at h
        exact h
      · rw [CFSG.GroupTheory.centralizer_map_conj g⁻¹ L,
          ← Subgroup.map_inf Bs (Subgroup.centralizer (L : Set G))
            (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective,
          Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
        exact card_bstar_inf_centralizer_le_of_sstar hctx.prime hctx.bstar.2.1 hctx.sstar
    · refine ⟨Subgroup.mem_map.mpr ⟨y, hyBs, rfl⟩, K.map (MulAut.conj g⁻¹).toMonoidHom,
        ?_, ?_⟩
      · have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
          (isComponentOf_of_isNeighborOf hctx.stdType
            (isNeighborOf_of_ggNbr hctx.stdSub hnbr)).1
        have hKinf : IsComponentOf K
            (ggG0 p B x L D J ⊓ Subgroup.centralizer ({y} : Set G)) :=
          CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKc
            (le_inf (le_ggG0_of_ggNbr hnbr) hKc.1) inf_le_right
        have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
          (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).2 hKinf
        rw [CFSG.centralizer_inter_map,
          CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_mem_normalizer hgN] at h
        exact h
      · rw [CFSG.GroupTheory.centralizer_map_conj g⁻¹ K,
          ← Subgroup.map_inf Bs (Subgroup.centralizer (K : Set G))
            (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective,
          Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
        exact card_bstar_inf_centralizer_le hctx.config hnbr

end CFSG.StandardType
