module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open Module
open CFSG.Quasithin.G11 (GLV)
open scoped TensorProduct

section Abstract

variable {ι K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

def jointEigenspace (f : ι → End K W) (χ : ι → K) : Submodule K W :=
  ⨅ i, (f i).eigenspace (χ i)

omit [IsAlgClosed K] in
theorem jointEigenspace_eq_of_semisimple (f : ι → End K W) (hf : ∀ i, (f i).IsSemisimple)
    (χ : ι → K) : jointEigenspace f χ = ⨅ i, (f i).maxGenEigenspace (χ i) := by
  unfold jointEigenspace
  congr 1; ext1 i
  exact ((Module.End.isFinitelySemisimple_iff_isSemisimple.mpr (hf i)).maxGenEigenspace_eq_eigenspace
    _).symm

omit [IsAlgClosed K] in
theorem jointEigenspace_independent (f : ι → End K W) (hf : ∀ i, (f i).IsSemisimple)
    (hc : ∀ i j, Commute (f i) (f j)) : iSupIndep (jointEigenspace f) := by
  have : jointEigenspace f = fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) := by
    ext1 χ; exact jointEigenspace_eq_of_semisimple f hf χ
  rw [this]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j _ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) _)

theorem jointEigenspace_iSup (f : ι → End K W) (hf : ∀ i, (f i).IsSemisimple)
    (hc : ∀ i j, Commute (f i) (f j)) : ⨆ χ, jointEigenspace f χ = ⊤ := by
  have : jointEigenspace f = fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) := by
    ext1 χ; exact jointEigenspace_eq_of_semisimple f hf χ
  rw [this]
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f
    (fun i j _ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) _)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))

end Abstract

section Concrete

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev ExtSpace (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Type :=
  AlgebraicClosure (ZMod 2) ⊗[ZMod 2] V

noncomputable def bcHom (V : Type) [AddCommGroup V] [Module (ZMod 2) V] :
    GLV V →* (ExtSpace V ≃ₗ[AlgebraicClosure (ZMod 2)] ExtSpace V) where
  toFun g := g.baseChange (ZMod 2) (AlgebraicClosure (ZMod 2)) V V
  map_one' := LinearEquiv.baseChange_one ..
  map_mul' _ _ := LinearEquiv.baseChange_mul ..

noncomputable def bcOp (g : GLV V) : Module.End (AlgebraicClosure (ZMod 2)) (ExtSpace V) :=
  (bcHom V g).toLinearMap

theorem bcOp_mul (g h : GLV V) : bcOp (g * h) = bcOp g * bcOp h := by
  refine LinearMap.ext fun w => ?_
  simp [bcOp, map_mul]

theorem bcOp_one : bcOp (1 : GLV V) = 1 := by
  refine LinearMap.ext fun w => ?_
  simp [bcOp]

theorem bcOp_pow (g : GLV V) (n : ℕ) : bcOp (g ^ n) = bcOp g ^ n := by
  induction n with
  | zero => simpa using bcOp_one
  | succ n ih => rw [pow_succ, bcOp_mul, ih, pow_succ]

theorem bcOp_tmul (g : GLV V) (a : AlgebraicClosure (ZMod 2)) (v : V) :
    bcOp g (a ⊗ₜ v) = a ⊗ₜ g v := by
  simp [bcOp, bcHom]

theorem eq_one_of_bcOp_eq_one (g : GLV V) (h : bcOp g = 1) : g = 1 := by
  ext v
  have h1 := congrArg (fun T => T ((1 : AlgebraicClosure (ZMod 2)) ⊗ₜ[ZMod 2] v)) h
  simp only [bcOp_tmul, Module.End.one_apply] at h1
  have := Module.Flat.tensorProduct_mk_injective (ZMod 2) V (AlgebraicClosure (ZMod 2)) h1
  simpa using this

end Concrete

section Main

open Polynomial

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {p : ℕ} [Fact p.Prime]

omit [Finite V] in
theorem bcOp_isSemisimple (hp2 : p ≠ 2) (g : GLV V) (hg : g ^ p = 1) :
    (bcOp g).IsSemisimple := by
  have hp : (p : AlgebraicClosure (ZMod 2)) ≠ 0 := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    have h2 : (2 : AlgebraicClosure (ZMod 2)) = 0 := CharTwo.two_eq_zero
    rw [hk]; push_cast; rw [h2]; simp
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ p - 1)
    ((X_pow_sub_one_separable_iff.mpr hp).squarefree) ?_
  simp [map_sub, ← bcOp_pow, hg, bcOp_one]

omit [Finite V] in
theorem weight_hom (P : Subgroup (GLV V)) (hP : CFSG.Open.IsElemAbelian p P)
    (lam : ↥P → AlgebraicClosure (ZMod 2))
    (hne : jointEigenspace (fun x : ↥P => bcOp (x : GLV V)) lam ≠ ⊥) :
    ∃ χ : ↥P →* (AlgebraicClosure (ZMod 2))ˣ, ∀ x, lam x = χ x := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hev : ∀ x : ↥P, (bcOp (x : GLV V)).HasEigenvector (lam x) w := fun x =>
    ⟨(Submodule.mem_iInf _).1 hw x, hw0⟩
  have hw' : ∀ x : ↥P, bcOp (x : GLV V) w = lam x • w := fun x =>
    Module.End.mem_eigenspace_iff.1 (hev x).1
  have hpow : ∀ x : ↥P, lam x ^ p = 1 := by
    intro x
    have h1 := (hev x).pow_apply p
    have hxp : (x : GLV V) ^ p = 1 := hP.2 x x.2
    rw [← bcOp_pow, hxp, bcOp_one] at h1
    have h2 : (1 : AlgebraicClosure (ZMod 2)) • w = lam x ^ p • w := by simpa using h1
    exact (smul_left_injective _ hw0 h2).symm
  have hne0 : ∀ x : ↥P, lam x ≠ 0 := by
    intro x h
    have := hpow x
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact zero_ne_one this
  have hmul : ∀ x y : ↥P, lam (x * y) = lam x * lam y := by
    intro x y
    have h1 : bcOp ((x * y : ↥P) : GLV V) w = (lam x * lam y) • w := by
      rw [Subgroup.coe_mul, bcOp_mul]
      simp [hw', mul_smul, smul_comm (lam x)]
    rw [hw'] at h1
    exact smul_left_injective _ hw0 h1
  refine ⟨MonoidHom.mk' (fun x => Units.mk0 (lam x) (hne0 x)) ?_, fun x => rfl⟩
  intro x y
  exact Units.ext (hmul x y)

omit [Finite V] in
theorem twist_ne_bot (P : Subgroup (GLV V)) (s : GLV V)
    (hs : ∀ x ∈ P, s⁻¹ * x * s ∈ P) (lam : ↥P → AlgebraicClosure (ZMod 2))
    (hne : jointEigenspace (fun x : ↥P => bcOp (x : GLV V)) lam ≠ ⊥) :
    jointEigenspace (fun x : ↥P => bcOp (x : GLV V))
      (fun x => lam ⟨s⁻¹ * (x : GLV V) * s, hs x x.2⟩) ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw' : ∀ x : ↥P, bcOp (x : GLV V) w = lam x • w := fun x =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hw x)
  refine Submodule.ne_bot_iff _ |>.2 ⟨bcOp s w, ?_, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun x => Module.End.mem_eigenspace_iff.2 ?_
    have hxs : (x : GLV V) * s = s * (s⁻¹ * x * s) := by group
    have : bcOp (x : GLV V) (bcOp s w) =
        bcOp s (bcOp ((⟨s⁻¹ * (x : GLV V) * s, hs x x.2⟩ : ↥P) : GLV V) w) := by
      show (bcOp (x : GLV V) * bcOp s) w = (bcOp s * bcOp (s⁻¹ * (x : GLV V) * s)) w
      rw [← bcOp_mul, ← bcOp_mul, hxs]
    rw [this, hw']
    simp
  · intro h0
    apply hw0
    have := congrArg (bcOp s⁻¹) h0
    have h3 : bcOp s⁻¹ (bcOp s w) = w := by
      show (bcOp s⁻¹ * bcOp s) w = w
      rw [← bcOp_mul]; simp [bcOp_one]
    rw [h3] at this
    simpa using this

theorem finrank_ge_card_of_free_action
    (hp2 : p ≠ 2)
    (P : Subgroup (GLV V)) (hP : CFSG.Open.IsElemAbelian p P) (hPne : P ≠ ⊥)
    (S : Finset (GLV V))
    (_hS : ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ ∈ P)
    (hS' : ∀ s ∈ S, ∀ x ∈ P, s⁻¹ * x * s ∈ P)
    (hfree : ∀ s (hs : s ∈ S), ∀ t (ht : t ∈ S), s ≠ t →
      ∀ χ : ↥P →* (AlgebraicClosure (ZMod 2))ˣ, χ ≠ 1 →
        ∃ x : ↥P, χ ⟨s⁻¹ * (x : GLV V) * s, hS' s hs x x.2⟩ ≠
          χ ⟨t⁻¹ * (x : GLV V) * t, hS' t ht x x.2⟩) :
    S.card ≤ Module.finrank (ZMod 2) V := by
  classical
  let f : ↥P → Module.End (AlgebraicClosure (ZMod 2)) (ExtSpace V) :=
    fun x => bcOp (x : GLV V)
  have hcomm : ∀ x y, Commute (f x) (f y) := by
    intro x y
    show bcOp _ * bcOp _ = bcOp _ * bcOp _
    rw [← bcOp_mul, ← bcOp_mul]
    congr 1
    have := hP.1
    exact setLike_mul_comm x.2 y.2
  have hss : ∀ x, (f x).IsSemisimple := fun x => bcOp_isSemisimple hp2 _ (hP.2 x x.2)
  have hind := jointEigenspace_independent f hss hcomm
  have htop := jointEigenspace_iSup f hss hcomm
  have hex : ∃ lam, jointEigenspace f lam ≠ ⊥ ∧
      ∃ χ : ↥P →* (AlgebraicClosure (ZMod 2))ˣ, χ ≠ 1 ∧ ∀ x, lam x = χ x := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ lam, jointEigenspace f lam ≤ jointEigenspace f (fun _ => 1) := by
      intro lam
      by_cases hb : jointEigenspace f lam = ⊥
      · rw [hb]; exact bot_le
      · obtain ⟨χ, hχ⟩ := weight_hom P hP lam hb
        have h1 : χ = 1 := by
          by_contra h
          obtain ⟨x, hx⟩ := hcon lam hb χ h
          exact hx (hχ x)
        have : lam = fun _ => 1 := by
          funext x; rw [hχ x, h1]; simp
        rw [this]
    have htop' : jointEigenspace f (fun _ => 1) = ⊤ :=
      top_unique (htop ▸ iSup_le hle)
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hPne
    have h1 : bcOp (x : GLV V) = 1 := by
      refine LinearMap.ext fun w => ?_
      have hw : w ∈ jointEigenspace f (fun _ => 1) := htop' ▸ Submodule.mem_top
      have := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hw x)
      simpa using this
    exact hx1 (Subtype.ext (eq_one_of_bcOp_eq_one _ h1))
  obtain ⟨lam0, hl0, χ0, hχ0, hlχ⟩ := hex
  have := hind.fintypeNeBotOfFiniteDimensional
  have hinj : S.card ≤ Fintype.card {lam // jointEigenspace f lam ≠ ⊥} := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective
      (fun s : S => ⟨fun x => lam0 ⟨(s : GLV V)⁻¹ * (x : GLV V) * s, hS' s s.2 x x.2⟩,
        twist_ne_bot P s (hS' s s.2) lam0 hl0⟩) ?_
    intro s t hst
    by_contra hne
    have hne' : (s : GLV V) ≠ t := fun h => hne (Subtype.ext h)
    obtain ⟨x, hx⟩ := hfree s s.2 t t.2 hne' χ0 hχ0
    have h1 := congrFun (congrArg Subtype.val hst) x
    apply hx
    apply Units.ext
    rw [← hlχ, ← hlχ]
    exact h1
  calc S.card ≤ _ := hinj
    _ ≤ Module.finrank (AlgebraicClosure (ZMod 2)) (ExtSpace V) := hind.subtype_ne_bot_le_finrank
    _ = Module.finrank (ZMod 2) V := Module.finrank_baseChange

end Main

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
