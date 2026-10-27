module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSL3Module
public import CFSG.Quasithin.Background.L34BinPair
public import CFSG.Quasithin.Background.SmithB42G2TenProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.QuasithinUnique.Setup.X7 (matRep matMap)
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7b
open scoped MatrixGroups Matrix

section Rep
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
@[expose] def IsTwistedNatural (ρ : Representation (ZMod 2) SL(3, F) U) : Prop :=
  ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
    E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u
@[expose] def IsTwistedHerm (ρ : Representation (ZMod 2) SL(3, F) U) : Prop :=
  ∃ hK : Nat.card F = (2 ^ 1) ^ 2, ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
    ∃ E : Multiplicative U ≃* H.L3Nine.HMod 1 F, ∀ g u,
      E (Multiplicative.ofAdd (ρ g u)) = H.L3Nine.rho hK (ψ g) (E (Multiplicative.ofAdd u))
private theorem exists_frobPair {n : ℕ} (hF : Fintype.card F = 2 ^ 2)
    (ρ₀ : SL(3, F) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    {a b : Fin 2 → Bool}
    (W : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)))
    (hW : W.toRepresentation.IsIrreducible)
    (eW : Representation.Equiv (matRep (tensorRep (F := F) F a b)) W.toRepresentation) :
    ∃ Y' : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)),
      Nonempty (Representation.Equiv Y'.toRepresentation
        (matRep (tensorRep (F := F) F (shiftBits 2 a) (shiftBits 2 b)))) ∧
      W.toSubmodule ⊔ Y'.toSubmodule = ⊤ := by
  classical
  have hfour : ∀ x : F, x ^ 2 ^ 2 = x := by
    intro x
    rw [← hF]
    exact FiniteField.pow_card x
  have hτ : matMap (frobPowEquiv F 1 : F →+* F)
      (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀) =
      matMap (ZMod.castHom (dvd_refl 2) F) ρ₀ := by
    rw [← matMap_comp_ringHom]
    congr 1
    exact RingHom.ext_zmod _ _
  let Ψ : TwistEquiv (frobPowEquiv F 1)
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀))
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)) :=
    { e := (matRepTwist (frobPowEquiv F 1)
        (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)).e
      comm := fun g v => by
        have hent : ∀ i' j', (frobPowEquiv F 1)
            (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀ g i' j') =
            matMap (ZMod.castHom (dvd_refl 2) F) ρ₀ g i' j' := fun i' j' =>
          congrFun (congrFun (congrArg (fun R => R g) hτ) i') j'
        funext i
        show frobPowEquiv F 1 (((matMap (ZMod.castHom (dvd_refl 2) F) ρ₀ g).mulVec v) i) =
          ((matMap (ZMod.castHom (dvd_refl 2) F) ρ₀ g).mulVec
            (fun i' => frobPowEquiv F 1 (v i'))) i
        simp [Matrix.mulVec, dotProduct, map_sum, hent] }
  have hΨ : ∀ (w : Fin n → F) (i : Fin n), Ψ.e w i = w i ^ 2 := by
    intro w i
    show frobPowEquiv F 1 (w i) = w i ^ 2
    simpa using frobPowEquiv_apply 1 (w i)
  let Y' : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)) := Ψ.mapSub W
  have hY' : Nonempty (Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F) F (shiftBits 2 a) (shiftBits 2 b)))) := by
    have h1 := ((Ψ.sub W).nonempty_equiv_iff
      (matRepTwist (frobPowEquiv F 1) (tensorRep (F := F) F a b)))
    have h2 : Nonempty (Representation.Equiv (Ψ.mapSub W).toRepresentation
        (matRep (matMap (frobPowEquiv F 1 : F →+* F) (tensorRep (F := F) F a b)))) :=
      h1.mpr ⟨eW.symm⟩
    rw [matMap_frobPowEquiv_tensorRep] at h2
    obtain ⟨P', Q', hM⟩ := tensorRep_comp_frobPow F hF 1 a b
    exact ⟨h2.some.trans hM.equiv.some⟩
  refine ⟨Y', hY', ?_⟩
  let M : Submodule F (Fin n → F) := W.toSubmodule ⊔ Y'.toSubmodule
  have hG : ∀ g, ∀ v ∈ M, ((ρ₀ g).map (ZMod.castHom (dvd_refl 2) F)).mulVec v ∈ M := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (W.apply_mem_toSubmodule g hx) (Y'.apply_mem_toSubmodule g hy)
  have hΦ : ∀ v ∈ M, (fun i => v i ^ 2) ∈ M := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hxy : (fun i => (x + y) i ^ 2) = (fun i => y i ^ 2) + (fun i => x i ^ 2) := by
      funext i
      simp [CharTwo.add_sq, add_comm]
    rw [hxy]
    refine Submodule.add_mem_sup ?_ ?_
    · obtain ⟨x0, hx0, hyeq⟩ := Submodule.mem_map.mp hy
      have hy2 : (fun i => y i ^ 2) = x0 := by
        funext i
        have h1 : y i = x0 i ^ 2 := by
          rw [← hyeq]
          exact hΨ x0 i
        rw [h1]
        show (x0 i ^ 2) ^ 2 = x0 i
        rw [← pow_mul]
        exact hfour (x0 i)
      rw [hy2]
      exact hx0
    · have hmem : Ψ.e x ∈ Y'.toSubmodule := Submodule.mem_map_of_mem hx
      have hx2 : (fun i => x i ^ 2) = Ψ.e x := by
        funext i
        rw [hΨ]
      rw [hx2]
      exact hmem
  have hWne : W.toSubmodule ≠ ⊥ := by
    intro hbot
    haveI hnt : Nontrivial ↥W.toSubmodule := (X7.isIrreducible_iff W.toRepresentation |>.mp hW).1
    rw [hbot] at hnt
    exact not_subsingleton_iff_nontrivial.mpr hnt (by infer_instance)
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hle : W.toSubmodule ≤ M := le_sup_left
    rw [hbot] at hle
    exact hWne (le_bot_iff.mp hle)
  exact descent hF ρ₀ hirr M hG hΦ hMne

private theorem dT_self_eq_scalarElement {c : Fˣ} (hc : c ^ 3 = 1) :
    X7a.dT c c = LinearFlag.scalarElement c hc := by
  apply Subtype.ext
  rw [X7a.dT_coe, LinearFlag.coe_scalarElement]
  have hcc : c * c * c = 1 := by
    rw [mul_assoc, ← pow_three]
    exact hc
  have hinv : (c * c)⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7a.dTMat, Matrix.scalar_apply, Matrix.one_apply, hinv]

private theorem tensorRep_dT_self (hF : Fintype.card F = 2 ^ 2) {a b : Fin 2 → Bool}
    {c : Fˣ} (hc : c ^ 3 = 1) :
    tensorRep (F := F) F a b (X7a.dT c c) =
      ((c : F) ^ (mBits a + 2 * mBits b)) •
        (1 : Matrix (X7a.TIdx 2 a b) (X7a.TIdx 2 a b) F) := by
  classical
  have hchar : (tensorRep (F := F) F a b (X7a.dT c c)).mulVec (X7a.hw F a b) =
      ((c : F) ^ (mBits a + 2 * mBits b)) • X7a.hw F a b := by
    rw [X7a.tensorRep_dT_hw]
    congr 1
    simp only [Algebra.algebraMap_self, RingHom.id_apply, ← pow_add]
    congr 1
    ring
  have hcomm : ∀ u : X7a.lowerUni F,
      X7a.dT c c * (u : SL(3, F)) = (u : SL(3, F)) * X7a.dT c c := by
    intro u
    have hmem : LinearFlag.scalarElement c hc ∈ Subgroup.center (SL(3, F)) :=
      LinearFlag.scalars_le_center 3 F (LinearFlag.scalarElement_mem_scalars c hc)
    have h1 := Subgroup.mem_center_iff.mp hmem (u : SL(3, F))
    rw [← dT_self_eq_scalarElement hc] at h1
    exact h1.symm
  have hkill : ∀ u : X7a.lowerUni F,
      (tensorRep (F := F) F a b (X7a.dT c c) -
        ((c : F) ^ (mBits a + 2 * mBits b)) • 1) *ᵥ
        (matRep (tensorRep (F := F) F a b) (u : SL(3, F)) (X7a.hw F a b)) = 0 := by
    intro u
    rw [X7.matRep_apply]
    calc (tensorRep (F := F) F a b (X7a.dT c c) -
          ((c : F) ^ (mBits a + 2 * mBits b)) • 1) *ᵥ
          ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b)
        = (tensorRep (F := F) F a b (X7a.dT c c)) *ᵥ
            ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = ((tensorRep (F := F) F a b (X7a.dT c c)) *
            (tensorRep (F := F) F a b (u : SL(3, F)))) *ᵥ X7a.hw F a b -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [Matrix.mulVec_mulVec]
      _ = (tensorRep (F := F) F a b (X7a.dT c c * (u : SL(3, F)))) *ᵥ X7a.hw F a b -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [← map_mul]
      _ = (tensorRep (F := F) F a b ((u : SL(3, F)) * X7a.dT c c)) *ᵥ X7a.hw F a b -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [hcomm u]
      _ = ((tensorRep (F := F) F a b (u : SL(3, F))) *
            (tensorRep (F := F) F a b (X7a.dT c c))) *ᵥ X7a.hw F a b -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [map_mul]
      _ = (tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ
            ((tensorRep (F := F) F a b (X7a.dT c c)) *ᵥ X7a.hw F a b) -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [Matrix.mulVec_mulVec]
      _ = (tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ
            (((c : F) ^ (mBits a + 2 * mBits b)) • X7a.hw F a b) -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [hchar]
      _ = ((c : F) ^ (mBits a + 2 * mBits b)) •
            ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) -
            ((c : F) ^ (mBits a + 2 * mBits b)) •
              ((tensorRep (F := F) F a b (u : SL(3, F))) *ᵥ X7a.hw F a b) := by
          rw [Matrix.mulVec_smul]
      _ = 0 := sub_self _
  have hzero : ∀ v : X7a.TIdx 2 a b → F,
      (tensorRep (F := F) F a b (X7a.dT c c) -
        ((c : F) ^ (mBits a + 2 * mBits b)) • 1) *ᵥ v = 0 := by
    intro v
    have hle : Submodule.span F (Set.range fun u : X7a.lowerUni F =>
        matRep (tensorRep (F := F) F a b) (u : SL(3, F)) (X7a.hw F a b)) ≤
        LinearMap.ker (Matrix.mulVecLin (tensorRep (F := F) F a b (X7a.dT c c) -
          ((c : F) ^ (mBits a + 2 * mBits b)) • 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      exact hkill u
    rw [X7a.mixed_span (F := F) (k := F) hF a b] at hle
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hle Submodule.mem_top
  refine Matrix.mulVec_injective (funext fun v => ?_)
  have h := hzero v
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  exact h

private theorem sub_rep_eq_smul {n : ℕ} {R : SL(3, F) →* Matrix (Fin n) (Fin n) F}
    {a b : Fin 2 → Bool} (W : Subrepresentation (matRep R))
    (eW : Representation.Equiv W.toRepresentation (matRep (tensorRep (F := F) F a b)))
    {g : SL(3, F)} {s : F}
    (hg : tensorRep (F := F) F a b g =
      s • (1 : Matrix (X7a.TIdx 2 a b) (X7a.TIdx 2 a b) F)) :
    ∀ w : ↥W.toSubmodule, R g *ᵥ (w : Fin n → F) = s • (w : Fin n → F) := by
  intro w
  have heq : (matRep (tensorRep (F := F) F a b)) g (eW w) = eW (W.toRepresentation g w) :=
    (Representation.IntertwiningMap.isIntertwining _ _ eW.toIntertwiningMap g w).symm
  have h2 : eW (W.toRepresentation g w) = s • eW w := by
    rw [← heq, X7.matRep_apply, hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h3 : W.toRepresentation g w = s • w := by
    apply eW.injective
    change eW ((W.toRepresentation g) w) = eW (s • w)
    rw [h2, map_smul]
  have h4 : (matRep R g) (w : Fin n → F) = s • (w : Fin n → F) := congrArg Subtype.val h3
  simpa only [X7.matRep_apply] using h4

private theorem matRep_eq_one_of_span {n : ℕ} {R : SL(3, F) →* Matrix (Fin n) (Fin n) F}
    {Y Y' : Subrepresentation (matRep R)} (htop : Y.toSubmodule ⊔ Y'.toSubmodule = ⊤)
    {g : SL(3, F)}
    (hY : ∀ y : ↥Y.toSubmodule, R g *ᵥ (y : Fin n → F) = (y : Fin n → F))
    (hY' : ∀ y : ↥Y'.toSubmodule, R g *ᵥ (y : Fin n → F) = (y : Fin n → F)) :
    R g = 1 := by
  refine Matrix.mulVec_injective (funext fun v => ?_)
  rw [Matrix.one_mulVec]
  have hv : v ∈ Y.toSubmodule ⊔ Y'.toSubmodule := by rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add]
  have h1 : R g *ᵥ y = y := hY ⟨y, hy⟩
  have h2 : R g *ᵥ z = z := hY' ⟨z, hz⟩
  rw [h1, h2]

private theorem eq_zero_of_fixed_of_smul_ne_one {n : ℕ}
    {R : SL(3, F) →* Matrix (Fin n) (Fin n) F}
    {Y Y' : Subrepresentation (matRep R)} (htop : Y.toSubmodule ⊔ Y'.toSubmodule = ⊤)
    (hbot : Y.toSubmodule ⊓ Y'.toSubmodule = ⊥)
    {g : SL(3, F)} {s s' : F}
    (hY : ∀ y : ↥Y.toSubmodule, R g *ᵥ (y : Fin n → F) = s • (y : Fin n → F))
    (hY' : ∀ y : ↥Y'.toSubmodule, R g *ᵥ (y : Fin n → F) = s' • (y : Fin n → F))
    (hs : s ≠ 1) (hs' : s' ≠ 1) :
    ∀ v : Fin n → F, R g *ᵥ v = v → v = 0 := by
  intro v hv
  have hmem : v ∈ Y.toSubmodule ⊔ Y'.toSubmodule := by rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hmem
  have h1 : R g *ᵥ y = s • y := hY ⟨y, hy⟩
  have h2 : R g *ᵥ z = s' • z := hY' ⟨z, hz⟩
  rw [Matrix.mulVec_add, h1, h2] at hv
  have hE : (s - 1) • y + (s' - 1) • z = 0 := by
    have h3 : s • y + s' • z - (y + z) = 0 := sub_eq_zero.mpr hv
    have h4 : (s - 1) • y + (s' - 1) • z = s • y + s' • z - (y + z) := by
      rw [sub_smul, sub_smul, one_smul, one_smul]
      abel
    rw [h4]
    exact h3
  have hmy : (s - 1) • y ∈ Y.toSubmodule := Submodule.smul_mem _ _ hy
  have hmz : (s' - 1) • z ∈ Y'.toSubmodule := Submodule.smul_mem _ _ hz
  have hzy : (s - 1) • y = -((s' - 1) • z) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hE
  have hy0 : y = 0 := by
    have hmem' : (s - 1) • y ∈ Y.toSubmodule ⊓ Y'.toSubmodule := by
      rw [Submodule.mem_inf]
      refine ⟨hmy, ?_⟩
      rw [hzy]
      exact Submodule.neg_mem _ hmz
    rw [hbot] at hmem'
    have hzero : (s - 1) • y = 0 := (Submodule.mem_bot F).mp hmem'
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hs
    · exact h
  have hz0 : z = 0 := by
    have hzy' : (s' - 1) • z = -((s - 1) • y) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hE
    have hmem' : (s' - 1) • z ∈ Y.toSubmodule ⊓ Y'.toSubmodule := by
      rw [Submodule.mem_inf]
      refine ⟨?_, hmz⟩
      rw [hzy']
      exact Submodule.neg_mem _ hmy
    rw [hbot] at hmem'
    have hzero : (s' - 1) • z = 0 := (Submodule.mem_bot F).mp hmem'
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hs'
    · exact h
  rw [hy0, hz0, add_zero]

private theorem cnt_shiftBits_two :
    ∀ a b : Fin 2 → Bool,
      cntS (shiftBits 2 a) (shiftBits 2 b) = cntS a b ∧
        cntH (shiftBits 2 a) (shiftBits 2 b) = cntH a b := by decide

private theorem shiftPair_ne_of_card_eq_two {a b : Fin 2 → Bool}
    (h : (pairOrbit 2 (a, b)).card = 2) : shiftPair 2 (a, b) ≠ (a, b) := by
  intro hfix
  have h1 : (pairOrbit 2 (a, b)).card ≤ 1 := by
    refine B45SL3.card_pairOrbit_le_of_fixed (a, b) le_rfl ?_
    simpa [shiftPair, Function.iterate_one] using hfix
  omega

private theorem inf_eq_bot_of_shift_ne {n : ℕ} (hF : Fintype.card F = 2 ^ 2)
    {R : SL(3, F) →* Matrix (Fin n) (Fin n) F}
    {a b : Fin 2 → Bool} {Y Y' : Subrepresentation (matRep R)}
    (hY : Y.toRepresentation.IsIrreducible)
    (eY : Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F) F a b)))
    (eY' : Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F) F (shiftBits 2 a) (shiftBits 2 b))))
    (hshift : shiftPair 2 (a, b) ≠ (a, b)) :
    Y.toSubmodule ⊓ Y'.toSubmodule = ⊥ := by
  classical
  have hshift' : (shiftBits 2 a, shiftBits 2 b) ≠ (a, b) := hshift
  rcases CFSG.Quasithin.L34Bin.inf_eq_bot_or_le hY Y' with h | hle
  · exact h
  · exfalso
    have h1 : Module.finrank F ↥Y.toSubmodule = 3 ^ cntS a b * 8 ^ cntH a b := by
      rw [eY.toLinearEquiv.finrank_eq]
      exact ((tensorRep_absolutely_irreducible_and_distinct F hF (by norm_num)).1 a b).2
    have h2 : Module.finrank F ↥Y'.toSubmodule = 3 ^ cntS a b * 8 ^ cntH a b := by
      rw [eY'.toLinearEquiv.finrank_eq,
        ((tensorRep_absolutely_irreducible_and_distinct F hF (by norm_num)).1
          (shiftBits 2 a) (shiftBits 2 b)).2, (cnt_shiftBits_two a b).1, (cnt_shiftBits_two a b).2]
    have hsub : Y.toSubmodule = Y'.toSubmodule :=
      Submodule.eq_of_le_of_finrank_eq hle (h1.trans h2.symm)
    have heq : Y = Y' := Subrepresentation.toSubmodule_injective hsub
    subst heq
    have e : Nonempty (Representation.Equiv (matRep (tensorRep (F := F) F a b))
        (matRep (tensorRep (F := F) F (shiftBits 2 a) (shiftBits 2 b)))) :=
      ⟨eY.symm.trans eY'⟩
    obtain ⟨hlab1, hlab2⟩ :=
      (tensorRep_absolutely_irreducible_and_distinct F hF (by norm_num)).2 a b
        (shiftBits 2 a) (shiftBits 2 b) e
    exact hshift' (Prod.ext hlab1 hlab2).symm

private theorem finrank_eq_two_mul_of_frobPair {n : ℕ} (hF : Fintype.card F = 2 ^ 2)
    {R : SL(3, F) →* Matrix (Fin n) (Fin n) F} {a b : Fin 2 → Bool}
    {Y Y' : Subrepresentation (matRep R)}
    (eY : Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F) F a b)))
    (eY' : Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F) F (shiftBits 2 a) (shiftBits 2 b))))
    (htop : Y.toSubmodule ⊔ Y'.toSubmodule = ⊤)
    (hbot : Y.toSubmodule ⊓ Y'.toSubmodule = ⊥) :
    n = 2 * (3 ^ cntS a b * 8 ^ cntH a b) := by
  classical
  have h1 : Module.finrank F ↥Y.toSubmodule = 3 ^ cntS a b * 8 ^ cntH a b := by
    rw [eY.toLinearEquiv.finrank_eq]
    exact ((tensorRep_absolutely_irreducible_and_distinct F hF (by norm_num)).1 a b).2
  have h2 : Module.finrank F ↥Y'.toSubmodule = 3 ^ cntS a b * 8 ^ cntH a b := by
    rw [eY'.toLinearEquiv.finrank_eq,
      ((tensorRep_absolutely_irreducible_and_distinct F hF (by norm_num)).1
        (shiftBits 2 a) (shiftBits 2 b)).2, (cnt_shiftBits_two a b).1, (cnt_shiftBits_two a b).2]
  have htop' : Module.finrank F ↥(Y.toSubmodule ⊔ Y'.toSubmodule) = n := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have hsum : Module.finrank F ↥(Y.toSubmodule ⊔ Y'.toSubmodule) +
      Module.finrank F ↥(Y.toSubmodule ⊓ Y'.toSubmodule) =
      Module.finrank F ↥Y.toSubmodule + Module.finrank F ↥Y'.toSubmodule :=
    Submodule.finrank_sup_add_finrank_inf_eq Y.toSubmodule Y'.toSubmodule
  rw [hbot, finrank_bot, add_zero, htop', h1, h2] at hsum
  omega

private lemma rep_eq_one_of_matMap_eq_one {n : ℕ}
    {ρ : Representation (ZMod 2) SL(3, F) U} (bas : Module.Basis (Fin n) (ZMod 2) U)
    {x : SL(3, F)}
    (h : matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas) x = 1) : ρ x = 1 := by
  have h0 : X7b.toMatRep ρ bas x = 1 := by
    have hmap1 : (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) F) = 1 :=
      Matrix.map_one (ZMod.castHom (dvd_refl 2) F) (map_zero _) (map_one _)
    apply Matrix.map_injective (ZMod.castHom (dvd_refl 2) F).injective
    change (X7b.toMatRep ρ bas x).map (ZMod.castHom (dvd_refl 2) F) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) F)
    rw [hmap1]
    simpa only [X7.matMap_apply] using h
  have h3 : LinearMap.toMatrix bas bas (ρ x) = LinearMap.toMatrix bas bas 1 := by
    rw [LinearMap.toMatrix_one]
    exact h0
  exact (LinearMap.toMatrix bas bas).injective h3

private lemma eq_zero_of_rep_fixed {n : ℕ}
    {ρ : Representation (ZMod 2) SL(3, F) U} (bas : Module.Basis (Fin n) (ZMod 2) U)
    {x : SL(3, F)}
    (h : ∀ v : Fin n → F,
      matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas) x *ᵥ v = v → v = 0)
    {u : U} (hu : ρ x u = u) : u = 0 := by
  classical
  have hw : X7b.toMatRep ρ bas x *ᵥ bas.equivFun u = bas.equivFun u := by
    have h1 : bas.equivFun (ρ x u) = (matRep (X7b.toMatRep ρ bas) x) (bas.equivFun u) :=
      Representation.IntertwiningMap.isIntertwining _ _
        (X7b.matRepEquiv ρ bas).toIntertwiningMap x u
    rw [hu] at h1
    simpa only [X7.matRep_apply] using h1.symm
  have h2 : matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas) x *ᵥ
      (fun i => ZMod.castHom (dvd_refl 2) F (bas.equivFun u i)) =
      fun i => ZMod.castHom (dvd_refl 2) F (bas.equivFun u i) := by
    change (X7b.toMatRep ρ bas x).map (ZMod.castHom (dvd_refl 2) F) *ᵥ
      (fun i => ZMod.castHom (dvd_refl 2) F (bas.equivFun u i)) = _
    rw [CFSG.Quasithin.B42G2Ten.matMap_mulVec_map, hw]
  have h3 : (fun i => ZMod.castHom (dvd_refl 2) F (bas.equivFun u i)) = 0 := h _ h2
  have hw0 : bas.equivFun u = 0 := by
    funext i
    have hi := congrFun h3 i
    rw [Pi.zero_apply] at hi
    exact (ZMod.castHom (dvd_refl 2) F).injective (hi.trans (map_zero _).symm)
  exact bas.equivFun.injective (hw0.trans (map_zero _).symm)

theorem sl3Four_cases_of_rank_le (hF : Fintype.card F = 2 ^ 2)
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible) (hnt : ∃ x, ρ x ≠ 1)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F)
    (a : U ≃ₗ[ZMod 2] U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haN : ∀ x : SL(3, F), ∃ y, X7a.Intertwines ρ a x y)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 4) :
    IsTwistedNatural ρ ∨ IsTwistedHerm ρ ∨
      (Module.finrank (ZMod 2) U = 16 ∧ ∀ x ∈ LinearFlag.scalars 3 F, ρ x = 1) ∨
      (Module.finrank (ZMod 2) U = 18 ∧
        (∀ x ∈ LinearFlag.scalars 3 F, x ≠ 1 → ∀ u, ρ x u = u → u = 0) ∧
        8 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (X7a.up3 0 0 1) - 1))) := by
  classical
  let bas := Module.finBasis (ZMod 2) U
  have hirr₀ := X7a.invariant_dichotomy ρ hirr bas
  obtain ⟨labA, labB, W, hne, hWirr, heq, -, hO, -⟩ :=
    B45SL3.exists_label_pkg (f := 2) hF (by norm_num) ρ bas hirr hnt
  have heq0 : Representation.Equiv (W 0).toRepresentation
      (matRep (tensorRep (F := F) F labA labB)) := (heq 0).some
  have hR := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.rank_up3_le_two_mul
    hF (by norm_num) ρ hirr hker a ha2 ha1 haN
  have hR8 : Module.finrank (ZMod 2) (LinearMap.range (ρ (X7a.up3 0 0 1) - 1)) ≤ 8 := by
    calc Module.finrank (ZMod 2) (LinearMap.range (ρ (X7a.up3 0 0 1) - 1))
        ≤ 2 * Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := hR
      _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 hrk
      _ = 8 := by norm_num
  have hdim : ∀ c : (Fin 2 → Bool) × (Fin 2 → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (X7a.up3 0 0 1) - 1).rank + 1 :=
    fun c => X7a.dim_le_two_mul_rank_tensorRep c.1 c.2
  have hsum := B45SL3.sum_rank_le hF (by norm_num) ρ bas (pairOrbit 2 (labA, labB)) hO
    (X7a.up3 0 0 1)
  have hcases := B45SL3.label_cases' (f := 2) (by norm_num) labA labB hne
    (fun c => (tensorRep (F := F) F c.1 c.2 (X7a.up3 0 0 1) - 1).rank) hdim
    (R := 8) (hsum.trans hR8)
  rcases hcases with hnat | hrow | hdouble | hbig
  · exact Or.inl
      (B42SL3.exists_natural_of_single hF ρ bas hirr hnat.1 hnat.2 (W 0) heq0)
  ·
    by_cases hlt : (pairOrbit 2 (labA, labB)).card < 2
    ·
      obtain ⟨m, hm, hfm, hK, psi, hpsi, E, hE⟩ :=
        B45SL3.exists_herm_of_row hF ρ bas hirr hrow.1 hrow.2.1 hlt (W 0) heq0
      have hm1 : m = 1 := by omega
      subst hm1
      exact Or.inr (Or.inl ⟨hK, psi, hpsi, E, hE⟩)
    ·
      have hcard2 : (pairOrbit 2 (labA, labB)).card = 2 :=
        le_antisymm (B45SL3.card_pairOrbit_le (labA, labB)) (not_lt.mp hlt)
      have hshiftne : shiftPair 2 (labA, labB) ≠ (labA, labB) :=
        shiftPair_ne_of_card_eq_two hcard2
      obtain ⟨Y', hY'eq, htop⟩ := exists_frobPair hF (X7b.toMatRep ρ bas) hirr₀
        (W 0) (hWirr 0) heq0.symm
      have hbot := inf_eq_bot_of_shift_ne hF (hWirr 0) heq0 hY'eq.some hshiftne
      have hdim18 : Module.finrank (ZMod 2) U = 18 := by
        have h := finrank_eq_two_mul_of_frobPair hF heq0 hY'eq.some htop hbot
        rw [hrow.1, hrow.2.1] at h
        norm_num at h
        exact h
      have hR8le : 8 ≤ Module.finrank (ZMod 2)
          (LinearMap.range (ρ (X7a.up3 0 0 1) - 1)) := by
        have h4 : ∀ c ∈ pairOrbit 2 (labA, labB),
            4 ≤ (tensorRep (F := F) F c.1 c.2 (X7a.up3 0 0 1) - 1).rank := by
          intro c hc
          obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
          have h := X7a.dim_le_two_mul_rank_tensorRep (F := F)
            ((shiftPair 2)^[s] (labA, labB)).1 ((shiftPair 2)^[s] (labA, labB)).2
          have e1 : cntS ((shiftPair 2)^[s] (labA, labB)).1
              ((shiftPair 2)^[s] (labA, labB)).2 = cntS labA labB :=
            X7a.card_feat_iterate (fun x : Bool × Bool => x.1 ≠ x.2) (labA, labB) s
          have e2 : cntH ((shiftPair 2)^[s] (labA, labB)).1
              ((shiftPair 2)^[s] (labA, labB)).2 = cntH labA labB :=
            X7a.card_feat_iterate (fun x : Bool × Bool => x.1 = true ∧ x.2 = true)
              (labA, labB) s
          rw [e1, e2, hrow.1, hrow.2.1] at h
          norm_num at h
          omega
        have h8 : 8 ≤ ∑ c ∈ pairOrbit 2 (labA, labB),
            (tensorRep (F := F) F c.1 c.2 (X7a.up3 0 0 1) - 1).rank := by
          calc 8 = ∑ _c ∈ pairOrbit 2 (labA, labB), 4 := by
                rw [Finset.sum_const, hcard2]
                norm_num
            _ ≤ _ := Finset.sum_le_sum h4
        exact h8.trans hsum
      have hexp : ∀ a b : Fin 2 → Bool, cntS a b = 2 → cntH a b = 0 →
          shiftPair 2 (a, b) ≠ (a, b) →
          (mBits a + 2 * mBits b = 5 ∧
              mBits (shiftBits 2 a) + 2 * mBits (shiftBits 2 b) = 4) ∨
            (mBits a + 2 * mBits b = 4 ∧
              mBits (shiftBits 2 a) + 2 * mBits (shiftBits 2 b) = 5) := by decide
      have hfpf : ∀ x ∈ LinearFlag.scalars 3 F, x ≠ 1 → ∀ u, ρ x u = u → u = 0 := by
        intro x hx hx1 u hu
        obtain ⟨c, hc3, hxmat⟩ := LinearFlag.mem_scalars.mp hx
        have hxeq : x = X7a.dT c c := by
          rw [dT_self_eq_scalarElement hc3]
          exact Subtype.ext (hxmat.trans (LinearFlag.coe_scalarElement c hc3).symm)
        have hc1 : c ≠ 1 := by
          intro hc1
          apply hx1
          rw [hxeq, hc1, X7a.dT_one]
        have hc2 : c ^ 2 ≠ 1 := by
          intro h2
          apply hc1
          have h3 : c ^ 3 = c ^ 2 * c := by rw [pow_succ, pow_two]
          rw [hc3, h2, one_mul] at h3
          exact h3.symm
        have hc3F : (c : F) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
        have hc2F : (c : F) ^ 2 ≠ 1 := by
          intro h2
          apply hc2
          exact Units.val_injective (by simpa [Units.val_pow_eq_pow_val] using h2)
        have hc5 : (c : F) ^ 5 ≠ 1 := by
          intro h5
          have hsplit : (c : F) ^ 5 = (c : F) ^ 2 * (c : F) ^ 3 := by ring
          rw [h5, hc3F, mul_one] at hsplit
          have h : (c : F) ^ 2 = 1 := hsplit.symm
          exact hc2F h
        have hc4 : (c : F) ^ 4 ≠ 1 := by
          intro h4
          have hsplit : (c : F) ^ 4 = (c : F) * (c : F) ^ 3 := by ring
          rw [h4, hc3F, mul_one] at hsplit
          exact hc1 (Units.val_injective (by simpa using hsplit.symm))
        have hchar := hexp labA labB hrow.1 hrow.2.1 hshiftne
        have hYW : ∀ y : ↥(W 0).toSubmodule,
            (matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas)) (X7a.dT c c) *ᵥ
              (y : Fin (Module.finrank (ZMod 2) U) → F) =
              ((c : F) ^ (mBits labA + 2 * mBits labB)) •
                (y : Fin (Module.finrank (ZMod 2) U) → F) :=
          sub_rep_eq_smul (W 0) heq0 (tensorRep_dT_self hF hc3)
        have hYY' : ∀ y : ↥Y'.toSubmodule,
            (matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas)) (X7a.dT c c) *ᵥ
              (y : Fin (Module.finrank (ZMod 2) U) → F) =
              ((c : F) ^ (mBits (shiftBits 2 labA) + 2 * mBits (shiftBits 2 labB))) •
                (y : Fin (Module.finrank (ZMod 2) U) → F) :=
          sub_rep_eq_smul Y' hY'eq.some (tensorRep_dT_self hF hc3)
        have hs : ((c : F) ^ (mBits labA + 2 * mBits labB)) ≠ 1 := by
          rcases hchar with ⟨hE, -⟩ | ⟨hE, -⟩
          · rw [hE]; exact hc5
          · rw [hE]; exact hc4
        have hs' : ((c : F) ^
            (mBits (shiftBits 2 labA) + 2 * mBits (shiftBits 2 labB))) ≠ 1 := by
          rcases hchar with ⟨-, hE⟩ | ⟨-, hE⟩
          · rw [hE]; exact hc4
          · rw [hE]; exact hc5
        have hzero := eq_zero_of_fixed_of_smul_ne_one htop hbot hYW hYY' hs hs'
        rw [hxeq] at hu
        exact eq_zero_of_rep_fixed bas hzero hu
      exact Or.inr (Or.inr (Or.inr ⟨hdim18, hfpf, hR8le⟩))
  ·
    have hshiftne : shiftPair 2 (labA, labB) ≠ (labA, labB) :=
      shiftPair_ne_of_card_eq_two hdouble.2.2.1
    obtain ⟨Y', hY'eq, htop⟩ := exists_frobPair hF (X7b.toMatRep ρ bas) hirr₀
      (W 0) (hWirr 0) heq0.symm
    have hbot := inf_eq_bot_of_shift_ne hF (hWirr 0) heq0 hY'eq.some hshiftne
    have hdim16 : Module.finrank (ZMod 2) U = 16 := by
      have h := finrank_eq_two_mul_of_frobPair hF heq0 hY'eq.some htop hbot
      rw [hdouble.1, hdouble.2.1] at h
      norm_num at h
      exact h
    have hexp : ∀ a b : Fin 2 → Bool, cntS a b = 0 → cntH a b = 1 →
        mBits a + 2 * mBits b = 3 ∨ mBits a + 2 * mBits b = 6 := by decide
    have htriv : ∀ x ∈ LinearFlag.scalars 3 F, ρ x = 1 := by
      intro x hx
      obtain ⟨c, hc3, hxmat⟩ := LinearFlag.mem_scalars.mp hx
      have hxeq : x = X7a.dT c c := by
        rw [dT_self_eq_scalarElement hc3]
        exact Subtype.ext (hxmat.trans (LinearFlag.coe_scalarElement c hc3).symm)
      have hc3F : (c : F) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
      have hc6F : (c : F) ^ 6 = 1 := by
        have h : (c : F) ^ 6 = ((c : F) ^ 3) ^ 2 := by ring
        rw [h, hc3F, one_pow]
      have hcnt : cntS (shiftBits 2 labA) (shiftBits 2 labB) = 0 ∧
          cntH (shiftBits 2 labA) (shiftBits 2 labB) = 1 := by
        have h := X7a.card_feat_iterate (fun x : Bool × Bool => x.1 ≠ x.2) (labA, labB) 1
        have h' := X7a.card_feat_iterate (fun x : Bool × Bool => x.1 = true ∧ x.2 = true)
          (labA, labB) 1
        rw [Function.iterate_one] at h h'
        exact ⟨h.trans hdouble.1, h'.trans hdouble.2.1⟩
      have hYW : ∀ y : ↥(W 0).toSubmodule,
          (matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas)) (X7a.dT c c) *ᵥ
            (y : Fin (Module.finrank (ZMod 2) U) → F) =
            (y : Fin (Module.finrank (ZMod 2) U) → F) := by
        intro y
        rw [sub_rep_eq_smul (W 0) heq0 (tensorRep_dT_self hF hc3)]
        rcases hexp labA labB hdouble.1 hdouble.2.1 with h | h
        · rw [h, hc3F, one_smul]
        · rw [h, hc6F, one_smul]
      have hYY' : ∀ y : ↥Y'.toSubmodule,
          (matMap (ZMod.castHom (dvd_refl 2) F) (X7b.toMatRep ρ bas)) (X7a.dT c c) *ᵥ
            (y : Fin (Module.finrank (ZMod 2) U) → F) =
            (y : Fin (Module.finrank (ZMod 2) U) → F) := by
        intro y
        rw [sub_rep_eq_smul Y' hY'eq.some (tensorRep_dT_self hF hc3)]
        rcases hexp (shiftBits 2 labA) (shiftBits 2 labB) hcnt.1 hcnt.2 with h | h
        · rw [h, hc3F, one_smul]
        · rw [h, hc6F, one_smul]
      have hPF1 := matRep_eq_one_of_span htop hYW hYY'
      rw [hxeq]
      exact rep_eq_one_of_matMap_eq_one bas hPF1
    exact Or.inr (Or.inr (Or.inl ⟨hdim16, htriv⟩))
  · omega
end Rep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
