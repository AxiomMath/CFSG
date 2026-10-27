module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSumSec
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSzConj
public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz
import all CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import CFSG.RankThree.GF2n.Tim77Prop24TwoL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section SumSecSz

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isNatSzSection_of_native_sub {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (σ : G →* LGL 2 X) (N : Subgroup G) {a : ℕ} (ha : 1 ≤ a)
    (ε : G →* ↥(CFSG.Open.Sz a)) (hε : Function.Surjective ε) (hker : ε.ker = N)
    (U : Submodule (ZMod 2) X) (hU : ∀ g : G, ∀ u ∈ U, σ g u ∈ U)
    (θ : (Fin 4 → GaloisField 2 (2 * a + 1)) ≃+ ↥U)
    (hθ : ∀ (g : G) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
      ((θ (((ε g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).mulVec v) : ↥U) : X) =
        σ g ((θ v : ↥U) : X)) :
    IsNatSzSection σ N U ⊥ (2 * a + 1) := by
  let e : CFSG.Open.GLASzGroup a (GaloisField 2 (2 * a + 1)) ≃* ↥(CFSG.Open.Sz a) :=
    CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative a
  let c : ↥(CFSG.Open.Sz a) ≃* ↥(CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1))) :=
    e.symm.trans (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1))).symm)
  let φ : G →* ↥(CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1))) :=
    c.toMonoidHom.comp ε
  let J : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
    CFSG.Blueprint.suzukiW (GaloisField 2 (2 * a + 1))
  have hJJ : J * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J, CFSG.Blueprint.suzukiW, Matrix.mul_apply, Fin.sum_univ_four]
  have hφ : ∀ g : G, ((φ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) =
      J * ((ε g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) * J := by
    intro g
    have hconj := inverseTranspose_eq_suzukiW_conj a (c (ε g)).2
    have hinv : Matrix.GeneralLinearGroup.inverseTranspose
        ((c (ε g) : ↥(CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)))) :
          GL (Fin 4) (GaloisField 2 (2 * a + 1))) =
        ((ε g : ↥(CFSG.Open.Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :=
      congrArg Subtype.val (e.apply_symm_apply (ε g))
    rw [hinv] at hconj
    have h3 : ((ε g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) =
        J * ((φ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) * J := hconj
    rw [h3]
    calc ((φ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)))
        = (J * J) * ((φ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) * (J * J) := by
          rw [hJJ, Matrix.one_mul, Matrix.mul_one]
      _ = J * (J * ((φ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) * J) * J := by
          simp only [Matrix.mul_assoc]
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let Jlin : (Fin 4 → GaloisField 2 (2 * a + 1)) →+ (Fin 4 → GaloisField 2 (2 * a + 1)) :=
    (Matrix.mulVecLin J).toAddMonoidHom
  let ψ : ↥U →+ (Fin 4 → GaloisField 2 (2 * a + 1)) :=
    Jlin.comp θ.symm.toAddMonoidHom
  have hψ : ∀ w : ↥U, ψ w = J.mulVec (θ.symm w) := fun w => rfl
  refine ⟨bot_le, hU, ?_, a, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, φ, ψ,
    ha, rfl, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  · exact c.surjective.comp hε
  · rw [← hker]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact map_eq_one_iff c c.injective
  · intro f
    refine ⟨θ (J.mulVec f), ?_⟩
    rw [hψ]
    simp only [AddEquiv.symm_apply_apply, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
  · intro w
    rw [hψ, Submodule.mem_bot]
    constructor
    · intro h
      have h1 : θ.symm w = 0 := by
        have := congrArg (fun v => J.mulVec v) h
        simpa [Matrix.mulVec_mulVec, hJJ] using this
      exact congrArg Subtype.val ((map_eq_zero_iff θ.symm θ.symm.injective).mp h1)
    · intro h
      have hw : w = 0 := Subtype.ext h
      rw [hw, map_zero, Matrix.mulVec_zero]
  · intro g w hw
    rw [hψ, hψ, hφ]
    have h1 : θ.symm ⟨σ g (w : X), hw⟩ =
        ((ε g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).mulVec (θ.symm w) := by
      apply θ.injective
      apply Subtype.ext
      rw [AddEquiv.apply_symm_apply, hθ g (θ.symm w), AddEquiv.apply_symm_apply]
    simp only [Matrix.mulVec_mulVec]
    show J.mulVec (θ.symm ⟨σ g (w : X), hw⟩) = _
    rw [h1, Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc (J * _) J J, hJJ, Matrix.mul_one]

theorem isNatSzSection_secLift (ρ : G →* LGL 2 V) (N : Subgroup G) {n : ℕ}
    {W₁ W₂ : Submodule (ZMod 2) V} (hW : W₂ ≤ W₁) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) {U : Submodule (ZMod 2) (SecMod W₁ W₂)}
    (hnat : IsNatSzSection (sectionRep ρ W₁ W₂ h₁ h₂) N U ⊥ n) :
    IsNatSzSection ρ N (secLift W₁ W₂ U) W₂ n := by
  obtain ⟨-, hUinv, -, a, K, hK, hKfin, φ, ψ, ha, hn, hcard, hφs, hker, hψs, hψ0, hψeq⟩ := hnat
  let p : Submodule (ZMod 2) ↥W₁ := W₂.comap W₁.subtype
  let inc : ↥(secLift W₁ W₂ U) →+ ↥W₁ :=
    { toFun := fun v => ⟨(v : V), secLift_le W₁ W₂ U v.2⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  let f : ↥(secLift W₁ W₂ U) →+ ↥U :=
    AddMonoidHom.codRestrict ((Submodule.mkQ p).toAddMonoidHom.comp inc) U (fun v => by
      obtain ⟨h, hh⟩ := mem_secLift.mp v.2
      have hEq : (⟨(v : V), h⟩ : ↥W₁) = inc v := Subtype.ext rfl
      rw [hEq] at hh
      simpa [p, Submodule.mkQ_apply] using hh)
  have hfsurj : Function.Surjective f := by
    intro u
    obtain ⟨w, hw⟩ :=
      Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) (u : SecMod W₁ W₂)
    have hmem : (w : V) ∈ secLift W₁ W₂ U := mem_secLift.mpr ⟨w.2, by
      show Submodule.Quotient.mk w ∈ U
      exact hw ▸ u.2⟩
    refine ⟨⟨(w : V), hmem⟩, ?_⟩
    · apply Subtype.ext
      change Submodule.mkQ p (inc ⟨(w : V), hmem⟩) = (u : SecMod W₁ W₂)
      rw [Submodule.mkQ_apply, ← hw]
      exact congrArg (Submodule.Quotient.mk (p := W₂.comap W₁.subtype)) (Subtype.ext rfl)
  refine ⟨le_secLift hW U, secLift_invariant ρ h₁ h₂ hUinv, h₂, a, K, hK, hKfin, φ,
    ψ.comp f, ha, hn, hcard, hφs, hker, hψs.comp hfsurj, ?_, ?_⟩
  · intro w
    have h := hψ0 (f w)
    rw [AddMonoidHom.comp_apply, h, Submodule.mem_bot]
    show Submodule.mkQ p (inc w) = 0 ↔ (w : V) ∈ W₂
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    rfl
  · intro g w hw
    have h := hψeq g (f w) (hUinv g (f w) (f w).2)
    have hfw : f ⟨ρ g (w : V), hw⟩ =
        ⟨sectionRep ρ W₁ W₂ h₁ h₂ g (f w), hUinv g (f w) (f w).2⟩ := by
      apply Subtype.ext
      have h1 : (f ⟨ρ g (w : V), hw⟩ : SecMod W₁ W₂) =
          Submodule.Quotient.mk (⟨ρ g (w : V), secLift_le W₁ W₂ U hw⟩ : ↥W₁) := rfl
      have h2 : ((f w : ↥U) : SecMod W₁ W₂) =
          Submodule.Quotient.mk (⟨(w : V), secLift_le W₁ W₂ U w.2⟩ : ↥W₁) := rfl
      simp only [h1, h2, sectionRep_mk]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hfw]
    exact h

theorem isSumNatSection_of_fpf_sz (hMart : CFSG.RankThree.GF2n.MartineauSzInput) [Finite G]
    {n : ℕ} (hG : CFSG.Quasithin.IsSz n G) (ρ : G →* LGL 2 V) {W₁ W₂ : Submodule (ZMod 2) V}
    (hW : W₂ ≤ W₁) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂)
    {x : G} (hx : orderOf x = 5) (hfpf : fixMod W₂ (ρ x) ⊓ W₁ ≤ W₂) :
    IsSumNatSection ρ ⊥ W₁ W₂ n := by
  classical
  obtain ⟨-, a, ha, K, hfield, hfinite, hn, hcard, ⟨e0⟩⟩ := hG
  subst hn
  let ε₀ : G ≃* ↥(CFSG.Open.Sz a) :=
    e0.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  let X := SecMod W₁ W₂
  haveI : Finite X :=
    Finite.of_surjective (Submodule.Quotient.mk (p := W₂.comap W₁.subtype))
      (Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype))
  let σ : G →* LGL 2 X := sectionRep ρ W₁ W₂ h₁ h₂
  let τ : Representation (ZMod 2) ↥(CFSG.Open.Sz a) X :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := X)).comp
      (σ.comp ε₀.symm.toMonoidHom)
  have hτ : ∀ (g : G) (v : X), τ (ε₀ g) v = σ g v := by
    intro g v
    show σ (ε₀.symm (ε₀ g)) v = σ g v
    rw [MulEquiv.symm_apply_apply]
  have hord : orderOf (ε₀ x) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  have hfix : ∀ v : X, τ (ε₀ x) v = v → v = 0 := by
    intro v hv
    rw [hτ x v] at hv
    obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective (W₂.comap W₁.subtype) v
    change sectionRep ρ W₁ W₂ h₁ h₂ x (Submodule.Quotient.mk e) = Submodule.Quotient.mk e at hv
    rw [sectionRep_mk] at hv
    have hdiff : ρ x (e : V) - (e : V) ∈ W₂ := by
      have h1 := (Submodule.Quotient.eq (W₂.comap W₁.subtype)).mp hv
      rw [Submodule.mem_comap] at h1
      simpa using h1
    have hmem : (e : V) ∈ fixMod W₂ (ρ x) := by
      rw [mem_fixMod]
      exact hdiff
    have hW₂ : (e : V) ∈ W₂ := hfpf (Submodule.mem_inf.mpr ⟨hmem, e.2⟩)
    exact (Submodule.Quotient.mk_eq_zero (W₂.comap W₁.subtype)).mpr (by
      rw [Submodule.mem_comap]
      simpa using hW₂)
  obtain ⟨s, hind, hsup, hs⟩ := hMart a ha X τ ⟨ε₀ x, hord, hfix⟩
  have hnat' : ∀ U ∈ s, IsNatSection ρ ⊥ (secLift W₁ W₂ U) W₂ (2 * a + 1) := by
    intro U hU
    obtain ⟨θ₀, hθinj, hθrange, hθeq⟩ := hs U hU
    have hσU : ∀ g : G, ∀ u ∈ U, σ g u ∈ U := by
      intro g u hu
      have hu' : u ∈ θ₀.range := by
        rwa [hθrange, Submodule.mem_toAddSubgroup]
      obtain ⟨v, rfl⟩ := hu'
      have hstep : σ g (θ₀ v) = θ₀ (((ε₀ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).mulVec v) := by
        rw [← hτ g (θ₀ v), ← hθeq (ε₀ g) v]
      rw [hstep, ← Submodule.mem_toAddSubgroup, ← hθrange]
      exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hcod : ∀ v : Fin 4 → GaloisField 2 (2 * a + 1), θ₀ v ∈ U := fun v => by
      rw [← Submodule.mem_toAddSubgroup, ← hθrange]
      exact AddMonoidHom.mem_range.mpr ⟨v, rfl⟩
    have hinj : Function.Injective (θ₀.codRestrict U hcod) := by
      intro v w hvw
      apply hθinj
      exact congrArg Subtype.val hvw
    have hsurj : Function.Surjective (θ₀.codRestrict U hcod) := by
      intro u
      have hu : (u : X) ∈ θ₀.range := by
        rw [hθrange, Submodule.mem_toAddSubgroup]
        exact u.2
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, Subtype.ext hv⟩
    let θ : (Fin 4 → GaloisField 2 (2 * a + 1)) ≃+ ↥U :=
      AddEquiv.ofBijective (θ₀.codRestrict U hcod) ⟨hinj, hsurj⟩
    have hθ' : ∀ (g : G) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
        ((θ (((ε₀ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).mulVec v) : ↥U) : X) =
          σ g ((θ v : ↥U) : X) := by
      intro g v
      show θ₀ (((ε₀ g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).mulVec v) = σ g (θ₀ v)
      rw [hθeq (ε₀ g) v, hτ g (θ₀ v)]
    have hker : ε₀.toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact ε₀.injective
    have hnatU : IsNatSzSection σ ⊥ U ⊥ (2 * a + 1) :=
      isNatSzSection_of_native_sub σ ⊥ ha ε₀.toMonoidHom ε₀.surjective hker U hσU θ hθ'
    exact Or.inr (isNatSzSection_secLift ρ ⊥ hW h₁ h₂ hnatU)
  have hind' : ∀ U ∈ s, U ⊓ (s.erase U).sup id = ⊥ := by
    intro U hU
    have h := (Finset.supIndep_iff_disjoint_erase.mp hind) U hU
    rwa [disjoint_iff] at h
  exact isSumNatSection_of_family ρ ⊥ hW h₁ h₂ s hsup hind' hnat'

end SumSecSz

end CFSG.LocalAnalysis.WeakClosure81
