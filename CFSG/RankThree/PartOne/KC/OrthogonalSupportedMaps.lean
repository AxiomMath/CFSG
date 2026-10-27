module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer
public import CFSG.ClassicalGroups.Orthogonal.IsometryConj

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem map_orthDerived_orthExtend_eq_supportedDerived {A : Submodule K V}
    (hcompl : IsCompl A (suppPerp Q A)) :
    (orthDerived (Q.comp A.subtype)).map (orthExtend hcompl) = supportedDerived Q A := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    refine mem_supportedDerived.mpr ⟨fun v hv => ?_, h, hh, fun w => ?_⟩
    · simpa using orthExtend_apply hcompl h (0 : A) ⟨v, hv⟩
    · simpa using (orthExtend_apply hcompl h w (0 : suppPerp Q A)).symm
  · intro g hg
    obtain ⟨hgp, h, hh, hgA⟩ := mem_supportedDerived.mp hg
    refine ⟨h, hh, ?_⟩
    ext x
    obtain ⟨a, ha, w, hw, rfl⟩ := suppExists_add_of_isCompl hcompl x
    rw [orthExtend_apply hcompl h ⟨a, ha⟩ ⟨w, hw⟩, map_add, hgp w hw, ← hgA ⟨a, ha⟩]

theorem map_orthDerived_orthExtend_eq_supportedDerived_of_regular {A : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate) :
    (orthDerived (Q.comp A.subtype)).map
        (orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hA))) =
      supportedDerived Q A :=
  map_orthDerived_orthExtend_eq_supportedDerived _

theorem supportedDerived_le_orthDerived_of_regular {A : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate) :
    supportedDerived Q A ≤ orthDerived Q := by
  have hcompl : IsCompl A (suppPerp Q A) :=
    isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)
  have horth : ∀ a ∈ A, ∀ w ∈ suppPerp Q A, polar Q a w = 0 :=
    fun a ha w hw => mem_suppPerp.mp hw a ha
  have hO : (TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype)).map
      (orthExtend hcompl) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, hg, rfl⟩
    exact (orthogonal_complement_elementary_embedding Q hcompl horth).2.1 g hg
  rw [← map_orthDerived_orthExtend_eq_supportedDerived hcompl, orthDerived,
    Subgroup.map_commutator]
  exact Subgroup.commutator_mono hO hO

@[expose] noncomputable def orthDerivedSupportedEquiv {A : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate) :
    orthDerived (Q.comp A.subtype) ≃* supportedDerived Q A := by
  let hcompl := isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)
  let horth : ∀ a ∈ A, ∀ w ∈ suppPerp Q A, polar Q a w = 0 :=
    fun a ha w hw => mem_suppPerp.mp hw a ha
  let hinj : Function.Injective (orthExtend hcompl) :=
    (orthogonal_complement_elementary_embedding Q hcompl horth).1
  let eMap := Subgroup.equivMapOfInjective
    (orthDerived (Q.comp A.subtype)) (orthExtend hcompl) hinj
  let hrange := map_orthDerived_orthExtend_eq_supportedDerived hcompl
  exact eMap.trans (MulEquiv.subgroupCongr hrange)

theorem orthDerivedSupportedEquiv_apply {A : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (g : orthDerived (Q.comp A.subtype)) :
    ((orthDerivedSupportedEquiv hA g : supportedDerived Q A) : V ≃ₗ[K] V) =
      orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hA))
        (g : A ≃ₗ[K] A) :=
  rfl

theorem map_supportedDerived_comap_subtype_eq_supportedDerived {A B : Submodule K V}
    (hAB : A ≤ B)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate) :
    (supportedDerived (Q.comp B.subtype) (A.comap B.subtype)).map
        (orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hB))) =
      supportedDerived Q A := by
  classical
  have hcomplA : IsCompl A (suppPerp Q A) :=
    isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)
  have hcomplB : IsCompl B (suppPerp Q B) :=
    isCompl_suppPerp (polarNondegOn_of_nondegenerate hB)
  let e : A.comap B.subtype ≃ₗ[K] A := Submodule.comapSubtypeEquivOfLe hAB
  let Qi : QuadraticForm K (A.comap B.subtype) :=
    (Q.comp B.subtype).comp (A.comap B.subtype).subtype
  let ei : Qi.IsometryEquiv (Q.comp A.subtype) :=
    { e with map_app' := fun _ => rfl }
  have he_coe : ∀ x : A.comap B.subtype,
      ((e x : A) : V) = ((x : A.comap B.subtype) : V) := fun _ => rfl
  have he_symm_coe : ∀ a : A,
      ((e.symm a : A.comap B.subtype) : V) = (a : V) := fun _ => rfl
  have he_symm_B : ∀ a : A,
      ((e.symm a : A.comap B.subtype) : B) = (⟨a, hAB a.2⟩ : B) := fun _ => rfl
  have hmapB_of_mem : ∀ f ∈ supportedDerived Q A, ∀ b ∈ B, f b ∈ B := by
    intro f hf b hb
    obtain ⟨hfperp, hf', _, hfact⟩ := mem_supportedDerived.mp hf
    obtain ⟨a, ha, c, hc, hbc⟩ := suppExists_add_of_isCompl hcomplA b
    have hcB : (c : V) ∈ B := by
      have hc_eq : (c : V) = (b : V) - (a : V) := by rw [← hbc]; abel
      rw [hc_eq]
      exact B.sub_mem hb (hAB ha)
    rw [← hbc, map_add, hfperp c hc, ← hfact ⟨a, ha⟩]
    exact B.add_mem (hAB (hf' ⟨a, ha⟩).2) hcB
  apply le_antisymm
  · rintro G ⟨g, hg, rfl⟩
    obtain ⟨hgfix, h', hh', hgact⟩ := mem_supportedDerived.mp hg
    refine mem_supportedDerived.mpr ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨b, hb, c, hc, hbc⟩ := suppExists_add_of_isCompl hcomplB x
      rw [← hbc] at hx
      have hbperp : b ∈ suppPerp Q A := by
        rw [mem_suppPerp]
        intro a ha
        have hxa : polar Q a ((b : V) + (c : V)) = 0 := mem_suppPerp.mp hx a ha
        have hca : polar Q a (c : V) = 0 := mem_suppPerp.mp hc a (hAB ha)
        simpa [polar_add_right, hca] using hxa
      have hb' : (⟨b, hb⟩ : B) ∈
          suppPerp (Q.comp B.subtype) (A.comap B.subtype) := by
        rw [mem_suppPerp]
        intro a' ha'
        rw [polar_comp_subtype_eq]
        exact mem_suppPerp.mp hbperp (a' : B) ha'
      rw [← hbc, orthExtend_apply hcomplB g ⟨b, hb⟩ ⟨c, hc⟩, hgfix ⟨b, hb⟩ hb']
    · refine ⟨LinearEquiv.autCongr e h', ?_, fun a => ?_⟩
      · have hmap := map_autCongr_commutator_orthogonalGroup ei
        change LinearEquiv.autCongr e h' ∈
          ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype),
            TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype)⁆
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hh'
      · have hGa : orthExtend hcomplB g (a : V) = (g ⟨a, hAB a.2⟩ : V) := by
          simpa using orthExtend_apply hcomplB g ⟨a, hAB a.2⟩ (0 : suppPerp Q B)
        rw [hGa, LinearEquiv.autCongr_apply_apply]
        have := congrArg (fun x : B => (x : V)) (hgact (e.symm a))
        simpa [he_coe, he_symm_B] using this
  · intro g hg
    obtain ⟨hgfix, h, hh, hgact⟩ := mem_supportedDerived.mp hg
    have hmapB : B.map (g : V →ₗ[K] V) = B := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨b, hb, rfl⟩
        exact hmapB_of_mem g hg b hb
      · intro b hb
        exact ⟨g.symm b, hmapB_of_mem g.symm (inv_mem hg) b hb, g.apply_symm_apply b⟩
    let gB : B ≃ₗ[K] B := LinearEquiv.ofSubmodules (e := g) B B hmapB
    have hgB_apply : ∀ b : B, ((gB b : B) : V) = g (b : V) := fun b =>
      LinearEquiv.ofSubmodules_apply (e := g) (p := B) (q := B) hmapB b
    have hgB : gB ∈ supportedDerived (Q.comp B.subtype) (A.comap B.subtype) := by
      refine mem_supportedDerived.mpr ⟨fun v hv => ?_, ?_⟩
      · apply Subtype.ext
        rw [hgB_apply v]
        apply hgfix
        rw [mem_suppPerp]
        intro a ha
        have hva : polar (Q.comp B.subtype) (⟨a, hAB ha⟩ : B) v = 0 :=
          mem_suppPerp.mp hv ⟨a, hAB ha⟩ ha
        rw [polar_comp_subtype_eq] at hva
        simpa using hva
      · refine ⟨LinearEquiv.autCongr e.symm h, ?_, fun w => ?_⟩
        · have hmap := map_autCongr_commutator_orthogonalGroup ei.symm
          change LinearEquiv.autCongr e.symm h ∈
            ⁅TauCeti.QuadraticMap.orthogonalGroup Qi,
              TauCeti.QuadraticMap.orthogonalGroup Qi⁆
          rw [← hmap]
          exact Subgroup.mem_map_of_mem _ hh
        · apply Subtype.ext
          rw [hgB_apply w, LinearEquiv.autCongr_apply_apply]
          simpa [he_symm_coe, he_coe] using hgact (e w)
    have hG : orthExtend hcomplB gB = g := by
      ext x
      obtain ⟨b, hb, c, hc, hbc⟩ := suppExists_add_of_isCompl hcomplB x
      have hcA : (c : V) ∈ suppPerp Q A := by
        rw [mem_suppPerp]
        intro a ha
        exact mem_suppPerp.mp hc a (hAB ha)
      rw [← hbc, orthExtend_apply hcomplB gB ⟨b, hb⟩ ⟨c, hc⟩, hgB_apply ⟨b, hb⟩,
        map_add, hgfix c hcA]
    rw [← hG]
    exact Subgroup.mem_map_of_mem _ hgB

omit [FiniteDimensional K V] in
theorem nondegenerate_comap_of_le {A B : Submodule K V} (hAB : A ≤ B)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate) :
    (polarBilin ((Q.comp B.subtype).comp (A.comap B.subtype).subtype)).Nondegenerate := by
  let e : A.comap B.subtype ≃ₗ[K] A := Submodule.comapSubtypeEquivOfLe hAB
  have hcongr : LinearMap.BilinForm.congr e
      (polarBilin ((Q.comp B.subtype).comp (A.comap B.subtype).subtype)) =
      polarBilin (Q.comp A.subtype) := by
    ext x y
    simp only [LinearMap.BilinForm.congr_apply, polar_comp_subtype_eq]
    rfl
  have h1 : (LinearMap.BilinForm.congr e
      (polarBilin ((Q.comp B.subtype).comp (A.comap B.subtype).subtype))).Nondegenerate := by
    rw [hcongr]
    exact hA
  exact (LinearMap.BilinForm.nondegenerate_congr_iff e).mp h1

theorem orthDerivedSupportedEquiv_map_supportedDerived {A B : Submodule K V}
    (hAB : A ≤ B)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate) :
    ((supportedDerived (Q.comp B.subtype) (A.comap B.subtype)).subgroupOf
      (orthDerived (Q.comp B.subtype))).map
        (orthDerivedSupportedEquiv hB).toMonoidHom =
      (supportedDerived Q A).subgroupOf (supportedDerived Q B) := by
  let H : Subgroup (B ≃ₗ[K] B) :=
    supportedDerived (Q.comp B.subtype) (A.comap B.subtype)
  let hcomplB := isCompl_suppPerp (polarNondegOn_of_nondegenerate hB)
  have hHle : H ≤ orthDerived (Q.comp B.subtype) :=
    supportedDerived_le_orthDerived_of_regular (nondegenerate_comap_of_le hAB hA)
  have hmapH : H.map (orthExtend hcomplB) = supportedDerived Q A :=
    map_supportedDerived_comap_subtype_eq_supportedDerived hAB hA hB
  have hmem : ∀ x : supportedDerived Q B,
      x ∈ ((H.subgroupOf (orthDerived (Q.comp B.subtype))).map
        (orthDerivedSupportedEquiv hB).toMonoidHom) ↔
      (x : V ≃ₗ[K] V) ∈ supportedDerived Q A := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : (orthExtend hcomplB (y : B ≃ₗ[K] B)) ∈ supportedDerived Q A := by
        have := Subgroup.mem_map_of_mem (orthExtend hcomplB) (show (y : B ≃ₗ[K] B) ∈ H from hy)
        rwa [hmapH] at this
      change ((orthDerivedSupportedEquiv hB y : supportedDerived Q B) : V ≃ₗ[K] V) ∈
        supportedDerived Q A
      rwa [orthDerivedSupportedEquiv_apply hB]
    · intro hx
      have hx' : (x : V ≃ₗ[K] V) ∈ H.map (orthExtend hcomplB) := by
        rwa [hmapH]
      obtain ⟨y, hy, hyx⟩ := hx'
      refine ⟨⟨y, hHle hy⟩, hy, ?_⟩
      apply Subtype.ext
      change ((orthDerivedSupportedEquiv hB ⟨y, hHle hy⟩ : supportedDerived Q B) : V ≃ₗ[K] V) =
        (x : V ≃ₗ[K] V)
      rw [orthDerivedSupportedEquiv_apply hB]
      exact hyx
  ext x
  exact hmem x

theorem supportedDerived_le_supportedDerived_of_le {A B : Submodule K V}
    (hAB : A ≤ B)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate) :
    supportedDerived Q A ≤ supportedDerived Q B := by
  have hA' := nondegenerate_comap_of_le hAB hA
  have hle : supportedDerived (Q.comp B.subtype) (A.comap B.subtype) ≤
      orthDerived (Q.comp B.subtype) := supportedDerived_le_orthDerived_of_regular hA'
  have hmono := Subgroup.map_mono hle (f := orthExtend
    (isCompl_suppPerp (polarNondegOn_of_nondegenerate hB)))
  rw [map_supportedDerived_comap_subtype_eq_supportedDerived hAB hA hB] at hmono
  rw [map_orthDerived_orthExtend_eq_supportedDerived_of_regular hB] at hmono
  exact hmono

section CrossSpace

variable {V1 V2 : Type*} [AddCommGroup V1] [Module K V1] [AddCommGroup V2] [Module K V2]
variable {Q1 : QuadraticForm K V1} {Q2 : QuadraticForm K V2}
variable {σ : K ≃+* K}
variable [hpair1 : RingHomInvPair (σ : K →+* K) (σ.symm : K →+* K)]
variable [hpair2 : RingHomInvPair (σ.symm : K →+* K) (σ : K →+* K)]

theorem autCongr_mem_supportedDerived_of_map_eq
    (e : V1 ≃ₛₗ[(σ : K →+* K)] V2) (μ : K) (hμ : μ ≠ 0)
    (hQ : ∀ v, Q2 (e v) = μ * σ (Q1 v))
    {R1 : Submodule K V1} {R2 : Submodule K V2} (hR : R1.map e.toLinearMap = R2)
    {g : V1 ≃ₗ[K] V1} (hg : g ∈ supportedDerived Q1 R1) :
    LinearEquiv.autCongr e g ∈ supportedDerived Q2 R2 := by
  obtain ⟨hgp, h, hh, he⟩ := mem_supportedDerived.mp hg
  let eR : R1 ≃ₛₗ[(σ : K →+* K)] R2 := e.ofSubmodules R1 R2 hR
  have hO : ∀ a ∈ TauCeti.QuadraticMap.orthogonalGroup (Q1.comp R1.subtype),
      LinearEquiv.autCongr eR a ∈ TauCeti.QuadraticMap.orthogonalGroup (Q2.comp R2.subtype) := by
    intro a ha
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at ha ⊢
    intro y
    rw [LinearEquiv.autCongr_apply_apply]
    simp only [QuadraticMap.comp_apply, Submodule.coe_subtype]
    rw [show ((eR (a (eR.symm y)) : R2) : V2) = e ((a (eR.symm y) : R1) : V1) from rfl]
    have hy : e ((eR.symm y : R1) : V1) = (y : V2) := by
      change e (e.symm (y : V2)) = (y : V2)
      rw [LinearEquiv.apply_symm_apply]
    rw [← hy, hQ, hQ]
    congr 2
    simpa using ha (eR.symm y)
  have hh' : LinearEquiv.autCongr eR h ∈ orthDerived (Q2.comp R2.subtype) := by
    have hOle : (TauCeti.QuadraticMap.orthogonalGroup (Q1.comp R1.subtype)).map
        (LinearEquiv.autCongr eR).toMonoidHom ≤
        TauCeti.QuadraticMap.orthogonalGroup (Q2.comp R2.subtype) := by
      rintro _ ⟨a, ha, rfl⟩
      exact hO a ha
    have hmap : ⁅TauCeti.QuadraticMap.orthogonalGroup (Q1.comp R1.subtype),
        TauCeti.QuadraticMap.orthogonalGroup (Q1.comp R1.subtype)⁆.map
        (LinearEquiv.autCongr eR).toMonoidHom ≤
        ⁅TauCeti.QuadraticMap.orthogonalGroup (Q2.comp R2.subtype),
          TauCeti.QuadraticMap.orthogonalGroup (Q2.comp R2.subtype)⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hOle hOle
    rw [orthDerived]
    exact hmap (Subgroup.mem_map_of_mem _ hh)
  refine mem_supportedDerived.mpr ⟨?_, LinearEquiv.autCongr eR h, hh', ?_⟩
  · intro v hv
    rw [LinearEquiv.autCongr_apply_apply]
    have hmem : e.symm v ∈ suppPerp Q1 R1 := by
      rw [mem_suppPerp]
      intro w hw
      have hew : e w ∈ R2 := by
        have := Submodule.mem_map_of_mem (f := e.toLinearMap) hw
        rwa [hR] at this
      have hpolar : polar Q2 (e w) v = 0 := mem_suppPerp.mp hv (e w) hew
      have hp := polar_map_semilin (e := e.toAddEquiv) (Q₂ := Q2) σ μ hQ w (e.symm v)
      have hsymm : e.toAddEquiv (e.symm v) = v := by
        change e (e.symm v) = v
        rw [LinearEquiv.apply_symm_apply]
      rw [hsymm] at hp
      change polar Q2 (e w) v = μ * σ (polar Q1 w (e.symm v)) at hp
      rw [hpolar] at hp
      have h0 : σ (polar Q1 w (e.symm v)) = 0 :=
        (mul_eq_zero.mp hp.symm).resolve_left hμ
      exact σ.injective (by rw [h0, map_zero])
    rw [hgp (e.symm v) hmem, LinearEquiv.apply_symm_apply]
  · intro w
    rw [LinearEquiv.autCongr_apply_apply]
    conv_rhs => rw [LinearEquiv.autCongr_apply_apply]
    change ((eR (h (eR.symm w)) : R2) : V2) = e (g (e.symm (w : V2)))
    rw [show ((eR (h (eR.symm w)) : R2) : V2) =
        e (((h (eR.symm w) : R1) : V1)) from rfl]
    rw [he (eR.symm w)]
    rfl

theorem map_supportedDerived_autCongr_of_map_eq
    (e : V1 ≃ₛₗ[(σ : K →+* K)] V2) (μ : K) (hμ : μ ≠ 0)
    (hQ : ∀ v, Q2 (e v) = μ * σ (Q1 v))
    {R1 : Submodule K V1} {R2 : Submodule K V2} (hR : R1.map e.toLinearMap = R2) :
    (supportedDerived Q1 R1).map (LinearEquiv.autCongr e).toMonoidHom =
      supportedDerived Q2 R2 := by
  have hR' : R2.map e.symm.toLinearMap = R1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ R1.map e.toLinearMap := by rw [hR]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      change e.symm y ∈ R1
      rw [← hzy]
      change e.symm (e z) ∈ R1
      rw [LinearEquiv.symm_apply_apply]
      exact hz
    · intro hx
      refine ⟨e x, ?_, LinearEquiv.symm_apply_apply e x⟩
      have h : e x ∈ R1.map e.toLinearMap := Submodule.mem_map_of_mem hx
      rwa [hR] at h
  have hQ' : ∀ v : V2, Q1 (e.symm v) = (σ.symm μ)⁻¹ * σ.symm (Q2 v) := by
    intro v
    have h := congrArg σ.symm (hQ (e.symm v))
    rw [LinearEquiv.apply_symm_apply, map_mul, RingEquiv.symm_apply_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ.symm).mpr hμ), one_mul]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact autCongr_mem_supportedDerived_of_map_eq e μ hμ hQ hR hg
  · intro g hg
    have h' : (LinearEquiv.autCongr e).symm g ∈ supportedDerived Q1 R1 := by
      have heq : (LinearEquiv.autCongr e).symm g = LinearEquiv.autCongr e.symm g := by
        ext x
        rw [LinearEquiv.autCongr_symm_apply_apply, LinearEquiv.autCongr_apply_apply]
        rfl
      haveI : RingHomInvPair ((σ.symm).symm : K →+* K) (σ.symm : K →+* K) := by
        rw [RingEquiv.symm_symm]
        exact hpair1
      haveI : RingHomInvPair (σ.symm : K →+* K) ((σ.symm).symm : K →+* K) := by
        rw [RingEquiv.symm_symm]
        exact hpair2
      rw [heq]
      exact autCongr_mem_supportedDerived_of_map_eq (σ := σ.symm) e.symm ((σ.symm μ)⁻¹)
        (inv_ne_zero ((map_ne_zero σ.symm).mpr hμ)) hQ' hR' hg
    exact Subgroup.mem_map.mpr ⟨_, h', (LinearEquiv.autCongr e).apply_symm_apply g⟩

theorem map_supportedDerived_isometryEquiv (e : Q1.IsometryEquiv Q2)
    {R : Submodule K V1} :
    (supportedDerived Q1 R).map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      supportedDerived Q2 (R.map e.toLinearEquiv.toLinearMap) := by
  letI : RingHomInvPair ((RingEquiv.refl K : K ≃+* K) : K →+* K)
      (((RingEquiv.refl K : K ≃+* K).symm : K →+* K)) :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl K)
  letI : RingHomInvPair (((RingEquiv.refl K : K ≃+* K).symm : K →+* K))
      ((RingEquiv.refl K : K ≃+* K) : K →+* K) :=
    RingHomInvPair.of_ringEquiv_symm (RingEquiv.refl K)
  have hQ : ∀ v : V1, Q2 (e.toLinearEquiv v) = (1 : K) * (RingEquiv.refl K) (Q1 v) := by
    intro v
    rw [one_mul]
    exact e.map_app v
  simpa using map_supportedDerived_autCongr_of_map_eq (σ := RingEquiv.refl K)
    (e := e.toLinearEquiv) 1 one_ne_zero hQ
    (rfl : R.map e.toLinearEquiv.toLinearMap = R.map e.toLinearEquiv.toLinearMap)

end CrossSpace

end CFSG.RankThree.PartOne.KCOrthogonal
