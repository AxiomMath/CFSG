module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22Lin
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.CharacterTheory.SteinbergBY
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def repOfIso {G : Type} [Group G] (L : Subgroup (GLV V))
    (θ : ↥L ≃* G) : Representation (ZMod 2) G V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp θ.symm.toMonoidHom)

theorem repOfIso_apply {G : Type} [Group G] (L : Subgroup (GLV V)) (θ : ↥L ≃* G) (g : G)
    (v : V) : repOfIso L θ g v = ((θ.symm g : ↥L) : GLV V) v := rfl

theorem repOfIso_isIrreducible {G : Type} [Group G] {L : Subgroup (GLV V)} (θ : ↥L ≃* G)
    (hL : IsIrr L ⊤) : (repOfIso L θ).IsIrreducible := by
  obtain ⟨-, hlt, hirr⟩ := hL
  have hv : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (bot_lt_iff_ne_bot.1 hlt).symm.symm
    exact ⟨v, 0, hv⟩
  have hnt : Nontrivial (Subrepresentation (repOfIso L θ)) := by
    refine ⟨⊥, ⊤, fun h' => ?_⟩
    obtain ⟨x, y, hxy⟩ := hv
    have h1 : (⊥ : Subrepresentation (repOfIso L θ)).toSubmodule =
        (⊤ : Subrepresentation (repOfIso L θ)).toSubmodule := congrArg _ h'
    have h2 : (⊥ : Submodule (ZMod 2) V) = ⊤ := h1
    have h3 : x - y ∈ (⊥ : Submodule (ZMod 2) V) := h2 ▸ Submodule.mem_top
    exact hxy (sub_eq_zero.mp ((Submodule.mem_bot _).mp h3))
  refine ⟨fun Z => ?_⟩
  have hinv : Invariant L Z.toSubmodule := fun l hl u hu => by
    have := Z.apply_mem_toSubmodule (θ ⟨l, hl⟩) hu
    simpa [repOfIso_apply] using this
  rcases hirr Z.toSubmodule hinv bot_le le_top with h1 | h1
  · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

theorem endIsField_one_of_natCard [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    (hcard : Nat.card (endCommutant L) = 2) : EndIsField L 1 := by
  classical
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_nontrivial hL
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_noZeroDivisors hL
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  let alg : Algebra (ZMod 2) (endCommutant L) := inferInstance
  let _ : Field (endCommutant L) := (Finite.isDomain_to_isField (endCommutant L)).toField
  let _ : Algebra (ZMod 2) (endCommutant L) := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField.algEquivGaloisField 2 1 (by rw [hcard]; norm_num)⟩

section Data

theorem trace_eq_of_equiv {K : Type*} [Field K] {W G : Type} [AddCommGroup W] [Module K W]
    [Group G] {n : ℕ} (ρ : Representation K G W) (M : G →* Matrix (Fin n) (Fin n) K)
    (e : ρ.Equiv (matrixBaseChange (RingHom.id K) M)) (g' : G) :
    LinearMap.trace K W (ρ g') = Matrix.trace (M g') := by
  have h1 := Representation.Equiv.conj_apply_self g' e
  have h2 : LinearMap.trace K W (ρ g') =
      LinearMap.trace K (Fin n → K) (matrixBaseChange (RingHom.id K) M g') := by
    rw [← h1]
    exact (LinearMap.trace_conj' (ρ g') e.toLinearEquiv).symm
  rw [h2, trace_matrixBaseChange]
  rfl

variable {G : Type} [Group G] {n : ℕ}

theorem equiv_apply {L : Subgroup (GLV V)} {θ : ↥L ≃* G}
    {M : G →* Matrix (Fin n) (Fin n) (ZMod 2)}
    (e : (repOfIso L θ).Equiv (matrixBaseChange (RingHom.id (ZMod 2)) M)) (g : G) (v : V) :
    e.toLinearEquiv (((θ.symm g : ↥L) : GLV V) v) = M g *ᵥ e.toLinearEquiv v := by
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id] at h1
  exact h1

theorem data_of_equiv [Finite V] {L : Subgroup (GLV V)} (θ : ↥L ≃* G) (hL : IsIrr L ⊤)
    [NeZero n] (M : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (habs : (matrixBaseChange (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) M).IsIrreducible)
    (he : Nonempty ((repOfIso L θ).Equiv (matrixBaseChange (RingHom.id (ZMod 2)) M)))
    (g : G) (hg : Matrix.trace (M g⁻¹) ≠ Matrix.trace (M g)) :
    Module.finrank (ZMod 2) V = n ∧ EndIsField L 1 ∧ ¬ SelfDual L ⊤ := by
  classical
  obtain ⟨e⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  · set ε := e.toLinearEquiv with hε
    have hscal : ∀ f ∈ endCommutant L, f = 0 ∨ f = 1 := by
      intro f hf
      let Tlin : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
        ε.toLinearMap ∘ₗ f ∘ₗ ε.symm.toLinearMap
      let T := LinearMap.toMatrix' Tlin
      have hTlin : ∀ x, Tlin x = ε (f (ε.symm x)) := fun x => rfl
      have hcomm : ∀ g : G, T * M g = M g * T := by
        intro g
        refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
        rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply,
          Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
        rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hTlin, hTlin]
        have hx : M g *ᵥ x = ε (((θ.symm g : ↥L) : GLV V) (ε.symm x)) := by
          have := equiv_apply e g (ε.symm x)
          simp only [← hε, ε.apply_symm_apply] at this
          exact this.symm
        have hf' := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm hf
          (θ.symm g).2 (ε.symm x)
        rw [hx, ε.symm_apply_apply, hf', equiv_apply e g]
      obtain ⟨c, hc⟩ := matrix_scalar_of_commute M habs T hcomm
      have hfv : ∀ v, f v = c • v := by
        intro v
        have h1 : T *ᵥ ε v = ε (f v) := by
          rw [LinearMap.toMatrix'_mulVec, hTlin, ε.symm_apply_apply]
        rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
        apply ε.injective
        rw [← h1, map_smul]
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h1
      · left
        ext v
        rw [hfv, h0]
        simp
      · right
        ext v
        rw [hfv, h1]
        simp
    have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_nontrivial hL
    refine endIsField_one_of_natCard hL ?_
    rw [Nat.card_eq_two_iff]
    refine ⟨0, 1, zero_ne_one, Set.eq_univ_of_forall fun z => ?_⟩
    rcases hscal z z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro ⟨B, hB, hinv⟩
    set k : GLV V := ((θ.symm g : ↥L) : GLV V) with hk
    have hkL : k ∈ L := (θ.symm g).2
    let tE : (↥(⊤ : Submodule (ZMod 2) V)) ≃ₗ[ZMod 2] V := Submodule.topEquiv
    let Tn : (↥(⊤ : Submodule (ZMod 2) V)) ≃ₗ[ZMod 2] (↥(⊤ : Submodule (ZMod 2) V)) :=
      tE.trans (k.trans tE.symm)
    have hTn : ∀ x : ↥(⊤ : Submodule (ZMod 2) V), ((Tn x : ↥(⊤ : Submodule (ZMod 2) V)) : V) =
        k (x : V) := fun x => rfl
    have hT : ∀ x y, B (Tn x) (Tn y) = B x y := fun x y =>
      hinv k hkL x y (Tn x) (Tn y) (hTn x).symm (hTn y).symm
    have h1 := trace_symm_eq_of_invariant B hB Tn hT
    have h2 : (Tn : (↥(⊤ : Submodule (ZMod 2) V)) →ₗ[ZMod 2] _) =
        tE.symm.conj (k : V →ₗ[ZMod 2] V) := by
      ext x
      rfl
    have h3 : (Tn.symm : (↥(⊤ : Submodule (ZMod 2) V)) →ₗ[ZMod 2] _) =
        tE.symm.conj (k.symm : V →ₗ[ZMod 2] V) := by
      ext x
      rfl
    rw [h2, h3, LinearMap.trace_conj', LinearMap.trace_conj'] at h1
    have h4 : ∀ g' : G, LinearMap.trace (ZMod 2) V (repOfIso L θ g') =
        Matrix.trace (M g') := fun g' => trace_eq_of_equiv _ M e g'
    have h5 : repOfIso L θ g⁻¹ = (k.symm : V →ₗ[ZMod 2] V) := by
      ext v
      rw [repOfIso_apply, map_inv]
      rfl
    apply hg
    rw [← h4, ← h4, h5]
    exact h1

end Data

section M22

open CFSG.Quasithin.B45Mat.M22 CFSG.Blueprint

set_option maxRecDepth 100000 in
theorem trace_rep10a_g7_inv :
    Matrix.trace (rep10a g7⁻¹) = 1 := by
  rw [← untab_tab10a]
  decide +kernel

set_option maxRecDepth 100000 in
theorem trace_rep10b_g7_inv :
    Matrix.trace (rep10b g7⁻¹) = 0 := by
  rw [← untab_tab10b]
  decide +kernel

theorem m22_repData
    [Finite V] {L : Subgroup (GLV V)} (θ : ↥L ≃* G22)
    (hL : IsIrr L ⊤) (hd : Module.finrank (ZMod 2) V ≤ 33) :
    Module.finrank (ZMod 2) V = 10 ∧ EndIsField L 1 ∧ ¬ SelfDual L ⊤ := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  rcases m22_binary_cases V (repOfIso L θ) (repOfIso_isIrreducible θ hL) hd with
    he | he | he
  · exfalso
    obtain ⟨e⟩ := he
    have htriv : ∀ g : G22, g = 1 := by
      intro g
      have h1 : ∀ v : V, ((θ.symm g : ↥L) : GLV V) v = v := by
        intro v
        have h2 := equiv_apply e g v
        have h3 : rep1 g = 1 := rfl
        rw [h3, Matrix.one_mulVec] at h2
        exact e.toLinearEquiv.injective h2
      have h5 : θ.symm g = 1 := Subtype.ext (LinearEquiv.ext h1)
      exact θ.symm.injective (h5.trans (map_one θ.symm).symm)
    have hcardG : Nat.card G22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
    have : Subsingleton G22 := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
    rw [Nat.card_of_subsingleton (1 : G22)] at hcardG
    norm_num at hcardG
  · refine data_of_equiv θ hL rep10a (isIrreducible_rep10a _) he g7 ?_
    rw [trace_rep10a_g7_inv, trace_rep10a_g7]
    decide
  · refine data_of_equiv θ hL rep10b (isIrreducible_rep10b _) he g7 ?_
    rw [trace_rep10b_g7_inv, trace_rep10b_g7]
    decide

end M22

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
