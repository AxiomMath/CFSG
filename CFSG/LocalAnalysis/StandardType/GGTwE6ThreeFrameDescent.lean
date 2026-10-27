module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofCore
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Basic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Entry

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne


section Entrywise

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem units_map_entrywiseHom_mem_twistedE6DiagGL {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ twistedE6DiagGL K σ) :
    Units.map (entrywiseHom δ.toRingHom) x ∈ twistedE6DiagGL K σ := by
  obtain ⟨u, rfl⟩ := hx
  change Units.map (entrywiseHom δ.toRingHom)
    (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∈ twistedE6DiagGL K σ
  rw [units_map_entrywiseHom_rootDiagUnit, ← compatDiag_orbitUnitsMap hδ]
  exact ⟨orbitUnitsMap σ.toRingHom hδ u, rfl⟩

theorem units_map_entrywiseHom_mem_twistedE6InndiagGL {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedE6InndiagGL K σ) :
    Units.map (entrywiseHom δ.toRingHom) g ∈ twistedE6InndiagGL K σ := by
  rw [mem_twistedE6InndiagGL_iff] at hg ⊢
  refine Subgroup.closure_induction (p := fun x _ =>
    Units.map (entrywiseHom δ.toRingHom) x ∈ Subgroup.closure
      ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
        (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K)))) ?_ ?_ ?_ ?_ hg
  · rintro x (hx | hx)
    · exact Subgroup.subset_closure (Or.inl
        (units_map_entrywiseHom_mem_graphFixedRootGroup (σ := σ.toRingHom) hδ hx))
    · exact Subgroup.subset_closure (Or.inr (units_map_entrywiseHom_mem_twistedE6DiagGL σ hδ hx))
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ ihx ihy
    rw [map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x _ ihx
    rw [map_inv]
    exact Subgroup.inv_mem _ ihx

private theorem entrywiseAdjointAut_mul_e6InndiagConj_mul_inv {K : Type} [Field K]
    (x : ↥(e6InndiagGL K)) (δ : K ≃+* K)
    (hx : Units.map (entrywiseHom δ.toRingHom) (x : ModGL Tag.E6 K) ∈ e6InndiagGL K) :
    entrywiseAdjointAut Tag.E6 δ * e6InndiagConj K x *
        (entrywiseAdjointAut Tag.E6 δ)⁻¹ =
      e6InndiagConj K
        ⟨Units.map (entrywiseHom δ.toRingHom) (x : ModGL Tag.E6 K), hx⟩ := by
  refine MulEquiv.ext fun z => Subtype.ext ?_
  set w : adjointGroup Tag.E6 K :=
    (MulEquiv.symm (entrywiseAdjointAut Tag.E6 δ)) z with hw
  have hψ : ((e6InndiagConj K x) w).1 = (x : ModGL Tag.E6 K) * w.1 *
      (x : ModGL Tag.E6 K)⁻¹ := by
    rw [e6InndiagConj_apply]
  have hEsymm : Units.map (entrywiseHom δ.toRingHom) (w.1 : ModGL Tag.E6 K) =
      (z : ModGL Tag.E6 K) := by
    have h := congrArg (fun u : adjointGroup Tag.E6 K => u.1)
      (MulEquiv.apply_symm_apply (entrywiseAdjointAut Tag.E6 δ) z)
    rwa [coe_entrywiseAdjointAut (τ := Tag.E6)] at h
  calc ((entrywiseAdjointAut Tag.E6 δ * e6InndiagConj K x *
        (entrywiseAdjointAut Tag.E6 δ)⁻¹) z).1
      = ((entrywiseAdjointAut Tag.E6 δ) ((e6InndiagConj K x) w)).1 := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, hw]
    _ = Units.map (entrywiseHom δ.toRingHom) ((e6InndiagConj K x) w).1 :=
        coe_entrywiseAdjointAut (τ := Tag.E6) δ _
    _ = Units.map (entrywiseHom δ.toRingHom)
          ((x : ModGL Tag.E6 K) * w.1 * (x : ModGL Tag.E6 K)⁻¹) := by
        rw [hψ]
    _ = Units.map (entrywiseHom δ.toRingHom) (x : ModGL Tag.E6 K) * (z : ModGL Tag.E6 K) *
          (Units.map (entrywiseHom δ.toRingHom) (x : ModGL Tag.E6 K))⁻¹ := by
        rw [map_mul, map_mul, map_inv, hEsymm]
    _ = ((e6InndiagConj K
          ⟨Units.map (entrywiseHom δ.toRingHom) (x : ModGL Tag.E6 K), hx⟩) z).1 := by
        rw [e6InndiagConj_apply]

end Entrywise

section Lift

variable {f : ℕ} (hf : 1 ≤ f)

@[expose] noncomputable def idEntrywise (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f))
    (frobQEquiv hf))) (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) :
    ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
  ⟨Units.map (entrywiseHom δ.toRingHom) d,
    units_map_entrywiseHom_mem_twistedE6InndiagGL _ (ringEquiv_comm_of_finite _ _) d.2⟩

theorem entrywiseAdjointAut_mul_twLiftHom_mul_inv
    (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)))
    (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) :
    entrywiseAdjointAut Tag.E6 δ * twLiftHom hf d *
        (entrywiseAdjointAut Tag.E6 δ)⁻¹ =
      twLiftHom hf (idEntrywise hf d δ) := by
  have hxmem : Units.map (entrywiseHom δ.toRingHom)
      (Subgroup.inclusion (twistedE6InndiagGL_le_e6InndiagGL (GaloisField 2 (2 * f))
        (frobQEquiv hf)) d).1 ∈
      e6InndiagGL (GaloisField 2 (2 * f)) :=
    twistedE6InndiagGL_le_e6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)
      (idEntrywise hf d δ).2
  refine (entrywiseAdjointAut_mul_e6InndiagConj_mul_inv
    (x := Subgroup.inclusion (twistedE6InndiagGL_le_e6InndiagGL (GaloisField 2 (2 * f))
      (frobQEquiv hf)) d) δ hxmem).trans ?_
  refine congrArg (e6InndiagConj (GaloisField 2 (2 * f))) ?_
  refine Subtype.ext ?_
  rfl

theorem exists_normalForm_cube {f : ℕ} (hf : 1 ≤ f)
    {α : MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))}
    (hα : α ^ 3 = 1) :
    ∃ (a : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)))
      (u : (i : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom i)ˣ)
      (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)),
      α = MulAut.conj a *
            compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom u *
            fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ ∧
      δ ^ 3 = 1 := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ (2 ^ f) :=
    fun c => frobQ_apply 2 f c
  obtain ⟨-, -, -, -, -, -, -, hnf, hΘ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (frobQEquiv hf) hσ
  obtain ⟨Θ, hΘ⟩ := hΘ
  obtain ⟨a, u, δ, hαeq⟩ := hnf α
  exact ⟨a, u, δ, hαeq, by rw [← hΘ.1 α a u δ hαeq, ← map_pow, hα, map_one]⟩

theorem twIncl_fieldActor_eq_entrywiseAdjointAut {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (η : K ≃+* K)
    (g : ↥(twistedE6RootGroup K σ)) :
    twIncl σ (fieldActor (t := TwistTag.E6) σ η g) =
      entrywiseAdjointAut Tag.E6 η (twIncl σ g) :=
  rfl

theorem twIncl_twistedE6InndiagConj {f : ℕ} (hf : 1 ≤ f)
    (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)))
    (z : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
    twIncl (frobQEquiv hf)
        (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) d z) =
      twLiftHom hf d (twIncl (frobQEquiv hf) z) :=
  rfl

theorem twLiftHom_mul_entrywiseAdjointAut_apply_twIncl {f : ℕ} (hf : 1 ≤ f)
    (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)))
    (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f))
    (z : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
    (twLiftHom hf d * entrywiseAdjointAut Tag.E6 δ)
        (twIncl (frobQEquiv hf) z) =
      twIncl (frobQEquiv hf)
        ((twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) d *
          fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ) z) := by
  calc (twLiftHom hf d * entrywiseAdjointAut Tag.E6 δ) (twIncl (frobQEquiv hf) z)
      = twLiftHom hf d (entrywiseAdjointAut Tag.E6 δ (twIncl (frobQEquiv hf) z)) := rfl
    _ = twLiftHom hf d (twIncl (frobQEquiv hf)
          (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ z)) := by
        rw [twIncl_fieldActor_eq_entrywiseAdjointAut (σ := frobQEquiv hf)]
    _ = twIncl (frobQEquiv hf)
          (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) d
            (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ z)) :=
        (twIncl_twistedE6InndiagConj hf d
          (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ z)).symm
    _ = twIncl (frobQEquiv hf)
          ((twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) d *
            fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ) z) := rfl

private theorem mul_pow_three_eq_of_conj {G : Type} [Group G] (A B A₁ A₂ : G)
    (hBA : B * A * B⁻¹ = A₁) (hBA2 : B * A₁ * B⁻¹ = A₂) (hB3 : B ^ 3 = 1) :
    (A * B) ^ 3 = A * A₁ * A₂ := by
  have hBA' : B * A = A₁ * B := by
    calc B * A = (B * A * B⁻¹) * B := by group
      _ = A₁ * B := by rw [hBA]
  have hBA2' : B * A₁ = A₂ * B := by
    calc B * A₁ = (B * A₁ * B⁻¹) * B := by group
      _ = A₂ * B := by rw [hBA2]
  calc (A * B) ^ 3 = A * (B * A) * (B * A) * B := by
        rw [pow_succ, pow_two]; simp only [mul_assoc]
    _ = A * (A₁ * B) * (A₁ * B) * B := by rw [hBA']
    _ = A * A₁ * (B * A₁) * B * B := by simp only [mul_assoc]
    _ = A * A₁ * (A₂ * B) * B * B := by rw [hBA2']
    _ = A * A₁ * A₂ * (B * B * B) := by simp only [mul_assoc]
    _ = A * A₁ * A₂ * B ^ 3 := by rw [pow_succ, pow_two]
    _ = A * A₁ * A₂ * 1 := by rw [hB3]
    _ = A * A₁ * A₂ := by rw [mul_one]

theorem exists_pow_three_eq_twLiftHom {f : ℕ} (hf : 1 ≤ f)
    (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)))
    (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) (hδ3 : δ ^ 3 = 1) :
    ∃ v : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      (twLiftHom hf d * entrywiseAdjointAut Tag.E6 δ) ^ 3 = twLiftHom hf v := by
  have hE3 : entrywiseAdjointAut Tag.E6 δ ^ 3 = 1 := by
    rw [← entrywiseAdjointAut_pow, hδ3, entrywiseAdjointAut_one]
  refine ⟨d * idEntrywise hf d δ * idEntrywise hf (idEntrywise hf d δ) δ, ?_⟩
  rw [mul_pow_three_eq_of_conj (twLiftHom hf d) (entrywiseAdjointAut Tag.E6 δ)
    (twLiftHom hf (idEntrywise hf d δ))
    (twLiftHom hf (idEntrywise hf (idEntrywise hf d δ) δ))
    (entrywiseAdjointAut_mul_twLiftHom_mul_inv hf d δ)
    (entrywiseAdjointAut_mul_twLiftHom_mul_inv hf (idEntrywise hf d δ) δ) hE3]
  rw [← map_mul, ← map_mul]


theorem twLiftHom_injective {f : ℕ} (hf : 1 ≤ f) :
    Function.Injective (twLiftHom hf) :=
  (e6InndiagConj_injective_galoisField hf).comp (Subgroup.inclusion_injective _)

private theorem mul_mul_inv_mul_mul_inv {G : Type} [Group G] (x y z : G) :
    (x * z) * y * (x * z)⁻¹ = x * (z * y * z⁻¹) * x⁻¹ := by
  rw [mul_inv_rev]
  group

private theorem map_mul_mul_inv {M N : Type} [Group M] [Group N] (ψ : M →* N) (x y z : M) :
    ψ (x * y * z⁻¹) = ψ x * ψ y * (ψ z)⁻¹ := by
  rw [show x * y * z⁻¹ = (x * y) / z by rw [div_eq_mul_inv], map_div, map_mul,
    div_eq_mul_inv]

theorem fieldActor_mul_twistedE6InndiagConj_mul_inv {f : ℕ} (hf : 1 ≤ f)
    (d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)))
    (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) :
    fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ *
        twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) d *
        (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ)⁻¹ =
      twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) (idEntrywise hf d δ) := by
  have hEin : ∀ z : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      twIncl (frobQEquiv hf)
          ((MulEquiv.symm (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ)) z) =
        (entrywiseAdjointAut Tag.E6 δ)⁻¹ (twIncl (frobQEquiv hf) z) := by
    intro z
    have h := twIncl_fieldActor_eq_entrywiseAdjointAut (σ := frobQEquiv hf) δ
      ((MulEquiv.symm (fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ)) z)
    simp only [MulEquiv.apply_symm_apply] at h
    have h' := congrArg (fun u => ((entrywiseAdjointAut Tag.E6 δ)⁻¹) u) h
    simpa only [MulAut.inv_apply, MulEquiv.symm_apply_apply] using h'.symm
  have hincl : Function.Injective (twIncl (frobQEquiv hf)) :=
    Subgroup.inclusion_injective _
  refine MulEquiv.ext fun z => hincl ?_
  simp only [MulAut.mul_apply, MulAut.inv_apply]
  rw [twIncl_fieldActor_eq_entrywiseAdjointAut (σ := frobQEquiv hf) δ]
  rw [twIncl_twistedE6InndiagConj hf d]
  rw [hEin]
  rw [← MulAut.mul_apply, ← MulAut.mul_apply]
  rw [entrywiseAdjointAut_mul_twLiftHom_mul_inv]
  rw [twIncl_twistedE6InndiagConj hf]

end Lift


private theorem frobQEquiv_toRingHom {f : ℕ} (hf : 1 ≤ f) :
    (frobQEquiv hf).toRingHom = frobQ 2 f := rfl

set_option maxHeartbeats 1000000 in
theorem ggBstarModelFrame_of_twLift_sigma {W V : Type} [Group W] [AddCommGroup V]
    {ρ : W →* Equiv.Perm V} {f : ℕ} (hf : 1 ≤ f)
    {M' S : Subgroup (MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)))}
    (hS : S ≤ LayerSixE.twInndiagAut f)
    (h : GGBstarModelFrame ρ 3 ⊤ (twLift hf S)) : GGBstarModelFrame ρ 3 M' S := by
  classical
  let φ : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) →*
      MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf)
  have hφinj : Function.Injective φ := twistedE6InndiagConj_injective_galoisField hf
  let L : Subgroup (MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) :=
    (S.comap φ).map (twLiftHom hf)
  have hmemL : ∀ {x : MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))},
      x ∈ L ↔ ∃ d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)),
        φ d ∈ S ∧ twLiftHom hf d = x := by
    intro x
    dsimp only [L]
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, hx⟩
      exact ⟨d, hd, hx⟩
    · rintro ⟨d, hd, hx⟩
      exact ⟨d, hd, hx⟩
  have hL : GGBstarModelFrame ρ 3 ⊤ L := h
  obtain ⟨ι', hι'inj, hι'range, hact⟩ := hL
  let Ŝ : Subgroup ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    S.comap φ
  have hSle : S ≤ φ.range := by
    rw [twInndiagAut_eq_range_twistedE6InndiagConj hf] at hS
    exact hS
  let L : Subgroup (MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) :=
    (S.comap φ).map (twLiftHom hf)
  have hmemL : ∀ {x : MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))},
      x ∈ L ↔ ∃ d : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)),
        φ d ∈ S ∧ twLiftHom hf d = x := by
    intro x
    dsimp only [L]
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, hx⟩
      exact ⟨d, hd, hx⟩
    · rintro ⟨d, hd, hx⟩
      exact ⟨d, hd, hx⟩
  have hφmap : Ŝ.map φ = S := by
    dsimp only [Ŝ]
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hSle]
  let eφ : ↥Ŝ ≃* ↥S :=
    (Subgroup.equivMapOfInjective Ŝ φ hφinj).trans (MulEquiv.subgroupCongr hφmap)
  let eψ : ↥Ŝ ≃* ↥L :=
    Subgroup.equivMapOfInjective Ŝ (twLiftHom hf) (twLiftHom_injective hf)
  let e : ↥S ≃* ↥(L) := eφ.symm.trans eψ
  let ι'cod : Multiplicative V →* ↥(L) :=
    ι'.codRestrict (L) fun v => by
      have hr : L = ι'.range := by
        rw [show L = twLift hf S from rfl]
        exact hι'range.symm
      rw [hr]
      exact ⟨v, rfl⟩
  let ιS : Multiplicative V →* ↥S := (e.symm.toMonoidHom).comp ι'cod
  let ι : Multiplicative V →* MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
      (frobQEquiv hf)) := (Subgroup.subtype S).comp ιS
  have hιinj : Function.Injective ι := by
    intro v w hvw
    have h1 : ιS v = ιS w := Subtype.ext hvw
    have h2 : ι'cod v = ι'cod w := e.symm.injective h1
    exact hι'inj (congrArg (fun x : ↥(L) => (x : MulAut
      (adjointGroup Tag.E6 (GaloisField 2 (2 * f))))) h2)
  have hιrange : ι.range = S := by
    have hιmem : ∀ v, ι v ∈ S := fun v => (ιS v).2
    have hιsurj : ∀ s ∈ S, ∃ v, ι v = s := by
      intro s hs
      have hmem : ((e ⟨s, hs⟩ : ↥(L)) : MulAut
          (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) ∈ ι'.range := by
        rw [hι'range]
        exact (e ⟨s, hs⟩).2
      obtain ⟨v, hv⟩ := hmem
      refine ⟨v, ?_⟩
      have hv' : ι'cod v = e ⟨s, hs⟩ := Subtype.ext hv
      have h2 : ιS v = ⟨s, hs⟩ := by
        dsimp only [ιS]
        rw [MonoidHom.comp_apply, hv']
        exact e.symm_apply_apply ⟨s, hs⟩
      exact congrArg (fun x : ↥S => (x : MulAut
        ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)))) h2
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact hιmem v
    · intro s hs
      exact hιsurj s hs
  refine ⟨ι, hιinj, hιrange, ?_⟩
  intro g _ hgN hg3
  let gσ : MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) := g
  have hg3σ : gσ ^ 3 = 1 := hg3
  have hgNσ : gσ ∈ Subgroup.normalizer (S : Set (MulAut
      ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)))) := hgN
  obtain ⟨a, u, δ, hgeq, hδ3⟩ := exists_normalForm_cube hf hg3σ
  have hDmem : (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 (frobQEquiv hf).toRingHom u) ∈
      twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf) := by
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.mem_sup_left a.2
    · exact Subgroup.mem_sup_right ⟨u, rfl⟩
  let D : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    ⟨(a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 (frobQEquiv hf).toRingHom u),
      hDmem⟩
  have hφD : φ D = MulAut.conj a * compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQEquiv hf).toRingHom u := by
    refine MulEquiv.ext fun z => Subtype.ext ?_
    dsimp only [φ, D]
    rw [twistedE6InndiagConj_apply, MulAut.mul_apply, MulAut.conj_apply]
    change (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 (frobQEquiv hf).toRingHom u) *
        ↑z * ((a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
            (frobQEquiv hf).toRingHom u))⁻¹ =
      (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
          (frobQEquiv hf).toRingHom u) * ↑z *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
            (frobQEquiv hf).toRingHom u))⁻¹) *
        (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹
    exact mul_mul_inv_mul_mul_inv _ _ _
  let E0 : MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    fieldActor (t := TwistTag.E6) (frobQEquiv hf) δ
  have hgeq' : gσ = φ D * E0 := by
    rw [hgeq, ← hφD]
  let E : MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :=
    entrywiseAdjointAut Tag.E6 δ
  let ĝ : MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :=
    twLiftHom hf D * E
  have hĝrestrict : ∀ z : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      ĝ (twIncl (frobQEquiv hf) z) = twIncl (frobQEquiv hf) (gσ z) := by
    intro z
    rw [twLiftHom_mul_entrywiseAdjointAut_apply_twIncl, ← hgeq']
  have hiter : ∀ n : ℕ, ∀ z, (ĝ ^ n) (twIncl (frobQEquiv hf) z) =
      twIncl (frobQEquiv hf) ((gσ ^ n) z) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
        intro z
        rw [pow_succ, MulAut.mul_apply, hĝrestrict, ih (gσ z), pow_succ, MulAut.mul_apply]
  obtain ⟨v, hv⟩ := exists_pow_three_eq_twLiftHom hf D δ hδ3
  have hφv : φ v = 1 := by
    refine MulEquiv.ext fun z => ?_
    have hincl : Function.Injective (twIncl (frobQEquiv hf)) :=
      Subgroup.inclusion_injective _
    refine hincl ?_
    rw [twIncl_twistedE6InndiagConj hf v z, ← hv, hiter 3 z, hg3σ]
  have hv1 : v = 1 := hφinj (by rw [hφv, map_one])
  have hĝ3 : ĝ ^ 3 = 1 := by rw [hv, hv1, map_one]
  have hDconj : ∀ d : ↥Ŝ,
      twLiftHom hf (D * idEntrywise hf d δ * D⁻¹) = ĝ * twLiftHom hf d * ĝ⁻¹ := by
    intro d
    calc twLiftHom hf (D * idEntrywise hf d δ * D⁻¹)
        = twLiftHom hf D * twLiftHom hf (idEntrywise hf d δ) * (twLiftHom hf D)⁻¹ :=
          map_mul_mul_inv (twLiftHom hf) D (idEntrywise hf d δ) D
      _ = twLiftHom hf D * (E * twLiftHom hf d * E⁻¹) * (twLiftHom hf D)⁻¹ := by
          rw [← entrywiseAdjointAut_mul_twLiftHom_mul_inv]
      _ = (twLiftHom hf D * E) * twLiftHom hf d * (twLiftHom hf D * E)⁻¹ :=
          (mul_mul_inv_mul_mul_inv _ _ _).symm
      _ = ĝ * twLiftHom hf d * ĝ⁻¹ := rfl
  have hSconj : ∀ d : ↥Ŝ, φ (D * idEntrywise hf d δ * D⁻¹) = gσ * φ d * gσ⁻¹ := by
    intro d
    rw [map_mul_mul_inv, ← fieldActor_mul_twistedE6InndiagConj_mul_inv, hgeq']
    exact (mul_mul_inv_mul_mul_inv _ _ _).symm
  have hĝnorm : ĝ ∈ Subgroup.normalizer (L :
      Set (MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f))))) :=
    Subgroup.mem_normalizer_fintype (fun h hh => by
      obtain ⟨d, hdS, rfl⟩ := hmemL.1 hh
      let d' : ↥Ŝ := ⟨d, hdS⟩
      refine hmemL.2
        ⟨D * idEntrywise hf d' δ * D⁻¹, ?_, ?_⟩
      · rw [hSconj d']
        exact (Subgroup.mem_normalizer_iff.1 hgNσ (φ d')).1 d'.2
      · rw [hDconj d'])
  obtain ⟨w, hw⟩ := hact ĝ (Subgroup.mem_top _) hĝnorm hĝ3
  let dOf : V → ↥Ŝ := fun v => eψ.symm (ι'cod (Multiplicative.ofAdd v))
  have hι_dOf : ∀ v, ι (Multiplicative.ofAdd v) = φ (dOf v) := fun v => rfl
  have hdOf_spec : ∀ v, eψ (dOf v) = ι'cod (Multiplicative.ofAdd v) := fun v =>
    eψ.apply_symm_apply _
  refine ⟨w, fun v => ?_⟩
  have hψd : ∀ u : V, twLiftHom hf (dOf u) =
      ((ι'cod (Multiplicative.ofAdd u) : ↥(L)) : MulAut
        (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) := by
    intro u
    rw [← Subgroup.coe_equivMapOfInjective_apply Ŝ (twLiftHom hf)
      (twLiftHom_injective hf) (dOf u), hdOf_spec u]
  have hι'cod_coe : ∀ u : V,
      ((ι'cod (Multiplicative.ofAdd u) : ↥L) : MulAut
        (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) =
      ι' (Multiplicative.ofAdd u) := fun u => rfl
  have hψeq : twLiftHom hf (D * idEntrywise hf (dOf v) δ * D⁻¹) =
      twLiftHom hf (dOf (ρ w v)) := by
    rw [hDconj (dOf v), hψd v, hι'cod_coe v, hw v, hψd (ρ w v), hι'cod_coe (ρ w v)]
  have heq : D * idEntrywise hf (dOf v) δ * D⁻¹ = dOf (ρ w v) :=
    twLiftHom_injective hf hψeq
  calc gσ * ι (Multiplicative.ofAdd v) * gσ⁻¹
      = gσ * φ (dOf v) * gσ⁻¹ := by rw [hι_dOf]
    _ = φ (D * idEntrywise hf (dOf v) δ * D⁻¹) := (hSconj (dOf v)).symm
    _ = φ (dOf (ρ w v)) := by rw [heq]
    _ = ι (Multiplicative.ofAdd (ρ w v)) := (hι_dOf (ρ w v)).symm


theorem ggBstarModelFrame_of_twLift {W V : Type} [Group W] [AddCommGroup V]
    {ρ : W →* Equiv.Perm V} {f : ℕ} (hf : 1 ≤ f)
    {M' S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hS : S ≤ LayerSixE.twInndiagAut f)
    (h : GGBstarModelFrame ρ 3 ⊤ (twLift hf S)) : GGBstarModelFrame ρ 3 M' S :=
  ggBstarModelFrame_of_twLift_sigma hf hS h

end CFSG.StandardType.NoOffTwE6Three
