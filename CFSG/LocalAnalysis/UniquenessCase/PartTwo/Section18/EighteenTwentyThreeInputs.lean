module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyThree
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HeisLocal
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShape
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusAsetIsometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBarHyp18
public import CFSG.Quasithin.Background.SmithB51G2DExcl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Comm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4Over

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Blueprint (LieModel)
open Matrix
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified

theorem eq_of_isOmegaMinus_six {X : Type} [Group X] {n f : ℕ}
    (hn : IsOmegaMinus X 6 n) (hf : IsOmegaMinus X 6 f) : n = f := by
  have hUn : IsU4 X n := isU4_of_isOmegaMinus hn
  have hUf : IsU4 X f := isU4_of_isOmegaMinus hf
  exact (CFSG.ComponentClassification.CatLeafProof.fieldExponent_eq_of_isChar2LieShape
    (X := X) (t := StatedLieTag.PSU) (n := 4) (f := f) hUf
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.isChar2LieShape_PSU_four hUn)

theorem mSub_eq_six_mul_of_natOmegaMinus {V₀ V : Subgroup G} {n : ℕ}
    (hV : IsElemAbelian 2 V) {H : Subgroup (MulAut (Vtil V₀ V hV))} (hV₀ : V₀ = ⊥)
    (hNat : NatOmegaMinus H ⊤ ⊥ 6 n) : mSub V = 6 * n := by
  subst hV₀
  obtain ⟨-, K, hKf, hKfin, b, c, hK2, hbc, ⟨π, hπ⟩⟩ := hNat
  letI := hKf
  letI := hKfin
  have h1 : Nat.card (Vtil ⊥ V hV) =
      Nat.card (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))).Mod :=
    CFSG.Quasithin.B5.G2D.card_eq_mod hπ
  have hcard : Nat.card (Vtil ⊥ V hV) = 2 ^ (6 * n) := by
    rw [h1, CFSG.Quasithin.B5.G2D.card_natMod_fin, hK2]
    norm_num [← pow_mul, Nat.mul_comm]
  have hVcard : Nat.card V = Nat.card (Vtil ⊥ V hV) := by
    rw [card_Vtil_eq ⊥ V hV bot_le]
    simp
  have hp : IsPGroup 2 V := hV.isPGroup
  have hcardV : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hp
  have hpow : 2 ^ mSub V = 2 ^ (6 * n) := by
    rw [← hcardV, hVcard, hcard]
  exact Nat.pow_right_injective (by norm_num) hpow

theorem Mbar_le_normalizer_barSub {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hXL : UC22.conjClosure D.M L = L) :
    Mbar D.M V₀ V h.hyp125.isElemAbelian ≤
      Subgroup.normalizer (barSub V₀ V h.hyp125.isElemAbelian L : Set
        (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) := by
  intro φ hφ
  obtain ⟨m, hm, rfl⟩ := (mem_barSub V₀ V h.hyp125.isElemAbelian D.M φ).1 hφ
  have hMleN : D.M ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hXL]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hmN : (m : G) ∈ Subgroup.normalizer (L : Set G) := hMleN hm
  have hmap : L.map (MulAut.conj (m : G)).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmN
  have hLstab : L ≤ stabTil V₀ V :=
    h.hL.1.1.le.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
      h.hyp125.pairFacts.le_normalizer₀)
  have hbar := TwelveTwentyThree.barSub_map_conj (V₀ := V₀) (V := V)
    h.hyp125.isElemAbelian hLstab m.2
  rw [hmap] at hbar
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hbar.symm

theorem exists_natOmegaMinus_of_P18_13_2 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h22 : P18_13_2 D V₀ V p L h 1) :
    ∃ f : ℕ,
      IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f ∧
        NatOmegaMinus
          (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 6 f := by
  obtain ⟨-, -, f, hΩ, I, hZI, -, hsup, hNI⟩ := h22
  have hI : I 0 = ⊤ := by
    simpa using hsup
  exact ⟨f, hΩ, hI ▸ hNI 0⟩

theorem barSub_gammaTwo_mem_calABar {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h22 : R18_22At D V₀ V p L h)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) (h1742 : S17.R17_42At D V₀ V)
    (hV0 : V₀ = ⊥) {n : ℕ}
    (hnOmega : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L)) 6 n)
    (hnU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (hNatn : NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L)) ⊤ ⊥ 6 n)
    {A : Subgroup G} (hA : A ∈ F12.Gam 2 D.T V)
    (hA1 : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) :
    barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar (2 * n - 2) D.M V₀ V h.hyp125.isElemAbelian := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hAM : A ∈ F12.Gam 2 D.M V := ⟨hA.1.trans D.sylowM.le, hA.2⟩
  obtain ⟨-, hnOf, -, -⟩ := isU4_barSub_cong h h1742 hnU4
  have hδ : ((2 * n : ℕ) : ℕ∞) ≤ deltaInf D.M V := by
    have h := h17 1 h22
    rw [hnOf] at h
    simpa using h
  have hV0m : mSub V₀ = 0 := by
    rw [hV0]
    simp [mSub, rk_bot]
  have hr : (((2 * n - 1 + mSub V₀ : ℕ)) : ℕ∞) < rMV D.M V := by
    rw [hV0m, Nat.add_zero]
    have h := h16 1 h22
    rw [hnOf] at h
    refine lt_of_lt_of_le (by exact_mod_cast (by omega : 2 * n - 1 < 4 * n + 1)) h
  obtain ⟨U, g, hUV, hcard, hAeq⟩ := hA.2
  have hmSubV : mSub V = 6 * n := mSub_eq_six_mul_of_natOmegaMinus hV hV0 hNatn
  have hj3 : 3 ≤ 2 * n := by
    have := (isU4_barSub_cong h h1742 hnU4).2.2.1
    omega
  have hjU : 2 * n ≤ mSub V := by omega
  obtain ⟨B, hB⟩ := eighteen_twenty_exists_gamma hV hUV hcard hAeq hj3 hjU
  exact (h18 2 A hAM hA1 (2 * n) hδ hr B hB).1

@[expose] def K_Omega6Minus_singularPointStabilizer : Prop :=
  ∀ {F : Type} [Field F] [Finite F] {b c : F} {n : ℕ}, Nat.card F = 2 ^ n →
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
    ∀ w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, w ≠ 0 →
      StatedQuadMinus 3 F b c w = 0 →
      ∃ Q : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)),
        (∀ g ∈ Q,
          (((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
            GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w ∈
            Submodule.span F {w}) ∧
          IsParabolicTwo ↥(StatedOmega (StatedQuadMinus 3 F b c)) Q ∧
          pCoreOf 2 Q ≠ ⊥ ∧
          IsL2 (Bar2 (F07.DerInf Q)) (2 * n) ∧
          pCoreOf 2 (F07.DerInf Q) ≠ ⊥ ∧
          (Even n →
            ∃ B P₃ : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)),
              Nat.card B = 3 ∧ B ≤ P₃ ∧
                CFSG.ABGLocalTools.IsSylowOf 3 P₃ ⊤ ∧
                P₃ ≤ Subgroup.centralizer (B : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∧
                P₃ ≤ Q ∧ F08.KOf8103 ⊤ B ≤ Q ∧
                IsL2 (Bar2 (F08.KOf8103 ⊤ B)) (2 * n))

theorem singularLine_18_23_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (h22 : R18_22At D V₀ V p L h)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) (h1742 : S17.R17_42At D V₀ V) :
    SingularLine_18_23 D V₀ V p L h := by
  intro hP12
  dsimp only
  intro n hnOmega hnU4 hV0
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  obtain ⟨f, hΩf, hNatf⟩ := exists_natOmegaMinus_of_P18_13_2 h hP12
  have hnf : n = f := eq_of_isOmegaMinus_six hnOmega hΩf
  have hNatn : NatOmegaMinus (barSub V₀ V hV (UC22.conjClosure D.M L)) ⊤ ⊥ 6 n := by
    rw [hnf]
    exact hNatf
  obtain ⟨F, hFfield, hFfinite, b, c, hFcardf, hbc, ε, ψ, hcoords⟩ :=
    exists_natCoords_of_natOmegaMinus hNatf
  letI := hFfield
  letI := hFfinite
  have hFcard : Nat.card F = 2 ^ n := by
    rw [hnf]
    exact hFcardf
  obtain ⟨hXL, hnOf, hn1, -⟩ := isU4_barSub_cong h h1742 hnU4
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  let W2 : Subgroup G := E3.wClos V 2 D.T
  have hW2T : W2 ≤ D.T := E3.wClos_le 2 D.T
  have hW2_2 : IsPGroup 2 W2 := (TwelveTwentyTwo.isPGroup_T D).to_le hW2T
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hW2stab : W2 ≤ stabTil V₀ V :=
    (hW2T.trans D.sylowM.le).trans hMstab
  have hMbarNorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) := by
    simpa [H, hXL] using Mbar_le_normalizer_barSub h hXL
  have hW2eq : W2 = ⨆ A ∈ F12.Gam 2 D.T V, A := by
    unfold W2
    rw [E3.wClos, ← S17.gam_eq_gammaSet 2 D.T V hV]
  let Iso : Subgroup (MulAut (Vtil V₀ V hV)) :=
    { carrier := {x | ∃ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
        (∀ s : ↥(⊤ : Subgroup (Vtil V₀ V hV)),
          ψ ⟨x s.1, Subgroup.mem_top _⟩ = Multiplicative.ofAdd
            ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
              (Multiplicative.toAdd (ψ s)))) ∧
        ∀ v, StatedQuadMinus 3 F b c
          ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec v) =
          StatedQuadMinus 3 F b c v}
      one_mem' := by
        refine ⟨1, ?_, ?_⟩
        · intro s
          simp [MulAut.one_apply]
        · intro v
          rw [Units.val_one, Matrix.one_mulVec]
      mul_mem' := by
        rintro x y ⟨gx, hgx, hQx⟩ ⟨gy, hgy, hQy⟩
        refine ⟨gx * gy, ?_, ?_⟩
        · intro s
          rw [MulAut.mul_apply]
          calc ψ ⟨x (y s.1), Subgroup.mem_top _⟩
              = Multiplicative.ofAdd (gx *ᵥ Multiplicative.toAdd
                  (ψ ⟨y s.1, Subgroup.mem_top _⟩)) :=
                hgx ⟨y s.1, Subgroup.mem_top _⟩
            _ = Multiplicative.ofAdd (gx *ᵥ (gy *ᵥ Multiplicative.toAdd (ψ s))) := by
                rw [hgy s, toAdd_ofAdd]
            _ = Multiplicative.ofAdd ((gx * gy) *ᵥ Multiplicative.toAdd (ψ s)) := by
                rw [Units.val_mul, Matrix.mulVec_mulVec]
        · intro v
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hQx, hQy]
      inv_mem' := by
        rintro x ⟨gx, hgx, hQx⟩
        refine ⟨gx⁻¹, ?_, ?_⟩
        · intro s
          have h := hgx ⟨x⁻¹ s.1, Subgroup.mem_top _⟩
          rw [MulAut.apply_inv_self] at h
          have hto := congrArg Multiplicative.toAdd h
          simp only [toAdd_ofAdd] at hto
          have hw : Multiplicative.toAdd (ψ ⟨x⁻¹ s.1, Subgroup.mem_top _⟩) =
              ((gx⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
                Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                  (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
                Multiplicative.toAdd (ψ s) := by
            rw [hto, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
              Units.val_one, Matrix.one_mulVec]
          exact congrArg Multiplicative.ofAdd hw
        · intro v
          have h := hQx ((gx⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v)
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec] at h
          exact h.symm }
  have memIso : ∀ x : ↥Iso, ∃ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      (∀ s : ↥(⊤ : Subgroup (Vtil V₀ V hV)),
        ψ ⟨(x : MulAut (Vtil V₀ V hV)) s.1, Subgroup.mem_top _⟩ =
          Multiplicative.ofAdd ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (ψ s)))) ∧
      ∀ v, StatedQuadMinus 3 F b c
        ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec v) =
        StatedQuadMinus 3 F b c v :=
    fun x => x.2
  have huniq : ∀ (x : ↥Iso) (g h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      (∀ s : ↥(⊤ : Subgroup (Vtil V₀ V hV)),
        ψ ⟨(x : MulAut (Vtil V₀ V hV)) s.1, Subgroup.mem_top _⟩ =
          Multiplicative.ofAdd ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (ψ s)))) →
      (∀ s : ↥(⊤ : Subgroup (Vtil V₀ V hV)),
        ψ ⟨(x : MulAut (Vtil V₀ V hV)) s.1, Subgroup.mem_top _⟩ =
          Multiplicative.ofAdd ((h : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (ψ s)))) →
      g = h := by
    intro x g h hg hh
    refine Units.ext (Matrix.ext_of_mulVec_single fun j => ?_)
    let s0 : ↥(⊤ : Subgroup (Vtil V₀ V hV)) :=
      ψ.symm (Multiplicative.ofAdd (Pi.single j (1 : F)))
    have h1 := hg s0
    have h2 := hh s0
    simp only [s0] at h1 h2
    rw [ψ.apply_symm_apply] at h1 h2
    simp only [toAdd_ofAdd] at h1 h2
    simpa using congrArg Multiplicative.toAdd (h1.symm.trans h2)
  let toGL : ↥Iso →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    { toFun := fun x => Classical.choose (memIso x)
      map_one' := by
        exact huniq 1 (Classical.choose (Iso.one_mem')) 1
          (Classical.choose_spec (Iso.one_mem')).1
          (by
            intro s
            simp [MulAut.one_apply])
      map_mul' := fun x y => by
        exact huniq (x * y) (Classical.choose (Iso.mul_mem' x.2 y.2))
          (Classical.choose (memIso x) * Classical.choose (memIso y))
          (Classical.choose_spec (Iso.mul_mem' x.2 y.2)).1
          (by
            intro s
            rw [Subgroup.coe_mul, MulAut.mul_apply]
            calc ψ ⟨(x : MulAut (Vtil V₀ V hV)) ((y : MulAut (Vtil V₀ V hV)) s.1),
                    Subgroup.mem_top _⟩
                = Multiplicative.ofAdd ((Classical.choose (memIso x) :
                    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
                    Multiplicative.toAdd (ψ ⟨(y : MulAut (Vtil V₀ V hV)) s.1,
                      Subgroup.mem_top _⟩)) :=
                  (Classical.choose_spec (memIso x)).1 ⟨(y : MulAut (Vtil V₀ V hV)) s.1,
                    Subgroup.mem_top _⟩
              _ = Multiplicative.ofAdd ((Classical.choose (memIso x) :
                    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
                    (Classical.choose (memIso y) :
                      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
                    Multiplicative.toAdd (ψ s)) := by
                  rw [(Classical.choose_spec (memIso y)).1 s, toAdd_ofAdd]
              _ = Multiplicative.ofAdd (((Classical.choose (memIso x) *
                    Classical.choose (memIso y)) : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
                    Multiplicative.toAdd (ψ s)) := by
                  rw [Units.val_mul, Matrix.mulVec_mulVec]) }
  have toGL_spec : ∀ (x : ↥Iso) (s : ↥(⊤ : Subgroup (Vtil V₀ V hV))),
      ψ ⟨(x : MulAut (Vtil V₀ V hV)) s.1, Subgroup.mem_top _⟩ =
        Multiplicative.ofAdd (((toGL x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          Multiplicative.toAdd (ψ s)) := by
    intro x s
    exact (Classical.choose_spec (memIso x)).1 s
  have toGL_Q : ∀ (x : ↥Iso) (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      quadMinus 3 F b c (((toGL x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v) =
        quadMinus 3 F b c v := by
    intro x v
    have h := (Classical.choose_spec (memIso x)).2 v
    simpa [toGL, ← coe_quadMinus] using h
  have hgen : ∀ A ∈ F12.Gam 2 D.T V, barSub V₀ V hV A ≤ Iso := by
    intro A hA
    by_cases hAbot : barSub V₀ V hV A = ⊥
    · rw [hAbot]
      exact bot_le
    · have hres := barSub_gammaTwo_mem_calABar h h22 h16 h17 h18 h1742 hV0 hnOmega hnU4
        hNatn (A := A) hA hAbot
      have hk : 3 ≤ 2 * n - 2 ∨ (Nat.card F = 4 ∧ 2 ≤ 2 * n - 2) := by
        by_cases hn2 : n = 2
        · right
          refine ⟨?_, by omega⟩
          rw [hFcard, hn2]
          norm_num
        · left
          omega
      exact k_Omega6Minus_aSet_isometry_holds hFcard hbc ε ψ hcoords
        (Mbar D.M V₀ V hV) hMbarNorm (2 * n - 2) hk (barSub V₀ V hV A) hres
  let K : Subgroup G :=
    (Subgroup.comap (actTil V₀ V hV) Iso).map (stabTil V₀ V).subtype
  have hAK : ∀ A ∈ F12.Gam 2 D.T V, A ≤ K := by
    intro A hA g hg
    have hAg : A ∈ E3.gammaSet V 2 D.T := by
      rwa [S17.gam_eq_gammaSet] at hA
    have hgstab : g ∈ stabTil V₀ V := hW2stab (E3.le_wClos hAg hg)
    refine Subgroup.mem_map.2 ⟨⟨g, hgstab⟩, ?_, rfl⟩
    exact hgen A hA (actTil_mem_barSub V₀ V hV hg hgstab)
  have hW2K : W2 ≤ K := by
    rw [hW2eq]
    exact iSup_le fun A => iSup_le fun hA => hAK A hA
  have hbarW2Iso : barSub V₀ V hV W2 ≤ Iso := by
    intro φ hφ
    obtain ⟨a, ha, rfl⟩ := (mem_barSub V₀ V hV W2 φ).1 hφ
    obtain ⟨bb, hbb, hbba⟩ := Subgroup.mem_map.1 (hW2K ha)
    have hba : bb = a := Subtype.ext hbba
    rwa [hba] at hbb
  have hE2 : IsPGroup 2 (barSub V₀ V hV W2) := s15_LP_isPGroup_barSub hV hW2_2
  haveI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := n)
      Nat.prime_two hFcard
  let Φ : ↥(barSub V₀ V hV W2) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    toGL.comp (Subgroup.inclusion hbarW2Iso)
  let E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := Φ.range
  have hE'Q : ∀ g ∈ E', ∀ v, quadMinus 3 F b c
      (((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v) = quadMinus 3 F b c v := by
    rintro - ⟨e, rfl⟩ v
    exact toGL_Q (Subgroup.inclusion hbarW2Iso e) v
  have hE'2 : IsPGroup 2 E' := hE2.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  obtain ⟨w, hw0, hwq, hwfix⟩ :=
    exists_fixed_singular_iso hbc hFcard (by omega) hE'Q hE'2
  have hfixline : ∀ (a : G) (ha : a ∈ W2), ∀ q : Vtil V₀ V hV,
      (⟨q, Subgroup.mem_top q⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV))) ∈ lineCoords ψ w →
        actTil V₀ V hV ⟨a, hW2stab ha⟩ q = q := by
    intro a ha q hq
    have hastab : a ∈ stabTil V₀ V := hW2stab ha
    let Aa : ↥(barSub V₀ V hV W2) :=
      ⟨actTil V₀ V hV ⟨a, hastab⟩, actTil_mem_barSub V₀ V hV ha hastab⟩
    have hfix : (Φ Aa : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w = w :=
      hwfix (Φ Aa) (Set.mem_range_self Aa)
    obtain ⟨u, hu, huq⟩ := Subgroup.mem_map.1 hq
    have hψq : ψ ⟨q, Subgroup.mem_top q⟩ = u := by
      have h := congrArg ψ huq
      change ψ (ψ.symm u) = ψ ⟨q, Subgroup.mem_top q⟩ at h
      rw [ψ.apply_symm_apply] at h
      exact h.symm
    have hu' : Multiplicative.toAdd u ∈ Submodule.span F {w} := hu
    obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hu'
    have hψqadd : Multiplicative.toAdd (ψ ⟨q, Subgroup.mem_top q⟩) = cc • w := by
      rw [hψq]
      exact hcc.symm
    have hψact : Multiplicative.toAdd
        (ψ ⟨actTil V₀ V hV ⟨a, hastab⟩ q, Subgroup.mem_top _⟩) =
        ((Φ Aa : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          Multiplicative.toAdd (ψ ⟨q, Subgroup.mem_top q⟩) := by
      have h := toGL_spec (Subgroup.inclusion hbarW2Iso Aa) ⟨q, Subgroup.mem_top q⟩
      simpa [Φ, Aa] using congrArg Multiplicative.toAdd h
    have hgoal : ψ ⟨actTil V₀ V hV ⟨a, hastab⟩ q, Subgroup.mem_top _⟩ =
        ψ ⟨q, Subgroup.mem_top q⟩ := by
      rw [hψq]
      have h : Multiplicative.toAdd
          (ψ ⟨actTil V₀ V hV ⟨a, hastab⟩ q, Subgroup.mem_top _⟩) =
          Multiplicative.toAdd u := by
        rw [hψact, hψqadd, Matrix.mulVec_smul, hfix, hcc]
      simpa using congrArg Multiplicative.ofAdd h
    change actTil V₀ V hV ⟨a, hastab⟩ q = q
    have htop : (⟨actTil V₀ V hV ⟨a, hastab⟩ q, Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Vtil V₀ V hV))) = ⟨q, Subgroup.mem_top q⟩ :=
      ψ.injective hgoal
    exact congrArg Subtype.val htop
  have hWi : F12.Wi 2 D.T V = W2 := by
    unfold F12.Wi W2 E3.wClos
    rw [S17.gam_eq_gammaSet 2 D.T V hV]
  have hwq' : StatedQuadMinus 3 F b c w = 0 := by
    rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact hwq
  refine ⟨F, hFfield, hFfinite, b, c, hFcard, hbc, ε, ψ, hcoords, w, hw0, hwq', ?_⟩
  rw [hWi]
  refine le_inf (preTil_le V₀ V hV _) ?_
  intro x hx
  have hxV : x ∈ V := preTil_le V₀ V hV _ hx
  have hqline : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
      (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V hV)).subtype :=
    (mem_preTil_iff_of_mem V₀ V hV _ hxV).1 hx
  obtain ⟨qt, hqt, hqtval⟩ := Subgroup.mem_map.1 hqline
  have hqt' : (⟨qt.1, Subgroup.mem_top qt.1⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV))) =
      qt := Subtype.ext rfl
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hastab : a ∈ stabTil V₀ V := hW2stab ha
  have hmkTil : mkTil V₀ V hV (actStab V₀ V hV ⟨a, hastab⟩ (IntMod.mk hV ⟨x, hxV⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) := by
    rw [← actTil_mk]
    have hfixq : actTil V₀ V hV ⟨a, hastab⟩ qt.1 = qt.1 := by
      refine hfixline a ha qt.1 ?_
      rwa [hqt']
    rw [← hqtval]
    exact hfixq
  have hinj : Function.Injective (mkTil V₀ V hV) := by
    intro p q hpq
    rw [mkTil_eq_iff] at hpq
    rw [hV0] at hpq
    have h1 : p.val * (q.val)⁻¹ = 1 := by simpa using hpq
    exact IntMod.val_injective (mul_inv_eq_one.mp h1)
  have hstab_eq : actStab V₀ V hV ⟨a, hastab⟩ (IntMod.mk hV ⟨x, hxV⟩) =
      IntMod.mk hV ⟨x, hxV⟩ := hinj hmkTil
  have hval := congrArg IntMod.val hstab_eq
  simp only [actStab_apply_val] at hval
  have hconj : a * x * a⁻¹ = x := hval
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [hconj]

theorem exists_parabolic_of_Q
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (Z : Subgroup G)
    (hΩ : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 n)
    (hnU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (hV0 : V₀ = ⊥) (hFcard : Nat.card F = 2 ^ n)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcoords : NatCoordsOmegaMinusOn
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤
      (fun _ _ _ _ => trivial) F b c ε ψ)
    (hw0 : w ≠ 0) (hwq : StatedQuadMinus 3 F b c w = 0)
    (hZdef : Z = lineTil V₀ V h.hyp125.isElemAbelian ψ w)
    (Q : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (hQw : ∀ g ∈ Q,
      (((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w ∈
        Submodule.span F {w})
    (hQpar : IsParabolicTwo ↥(StatedOmega (StatedQuadMinus 3 F b c)) Q) :
    ∃ (Φ : Bar2 L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c))) (P₁ : Subgroup G),
      ParabolicOf L P₁ ∧ pCoreOf 2 L ≤ P₁ ∧
        (P₁.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) = Q.comap Φ.toMonoidHom ∧
        P₁ ≤ normalizer (Z : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian)) :=
    barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)
  have hsimple : IsSimpleGroup ↥H :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hnU4
  obtain ⟨hXL, -⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  have hH : H = barSub V₀ V h.hyp125.isElemAbelian L := by
    simp [H, hXL]
  have hLstab : L ≤ stabTil V₀ V :=
    h.hL.1.1.le.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
      h.hyp125.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V h.hyp125.isElemAbelian (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.hyp125.isElemAbelian h.hL.1.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
  have hLsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_hyp18 h hXL
  have hLbar1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ := by
    rw [← hH]
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hsimple.toNontrivial
  let ψ0 : ↥L →* ↥H :=
    ((actTil V₀ V h.hyp125.isElemAbelian).comp (Subgroup.inclusion hLstab)).codRestrict H
      (fun x => by
        rw [hH]
        exact actTil_mem_barSub V₀ V h.hyp125.isElemAbelian x.2 (hLstab x.2))
  have hψ0ker : pCore 2 ↥L ≤ ψ0.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V h.hyp125.isElemAbelian ⟨(x : G), hLstab x.2⟩ ∈
        barSub V₀ V h.hyp125.isElemAbelian (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V h.hyp125.isElemAbelian hxP (hLstab x.2)
    rw [h2] at h1
    exact Subtype.ext h1
  let Ψ : Bar2 L →* ↥H := QuotientGroup.lift (pCore 2 ↥L) ψ0 hψ0ker
  have hΨmk : ∀ l : ↥L, Ψ (QuotientGroup.mk l) =
      ⟨actTil V₀ V h.hyp125.isElemAbelian ⟨(l : G), hLstab l.2⟩,
        (by
          change actTil V₀ V h.hyp125.isElemAbelian ⟨(l : G), hLstab l.2⟩ ∈ H
          rw [hH]
          exact actTil_mem_barSub V₀ V h.hyp125.isElemAbelian l.2 (hLstab l.2))⟩ := by
    intro l
    change Ψ (QuotientGroup.mk' (pCore 2 ↥L) l) = _
    rw [show Ψ = QuotientGroup.lift (pCore 2 ↥L) ψ0 hψ0ker from rfl]
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨l, hl, hly⟩ := (mem_barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L) y).1 y.2
    rw [hXL] at hl
    refine ⟨QuotientGroup.mk ⟨(l : G), hl⟩, ?_⟩
    rw [hΨmk ⟨(l : G), hl⟩]
    exact Subtype.ext hly
  have hΨker : Ψ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top Ψ.ker with hk | hk
    · exact hk
    · refine absurd ?_ hLbar1
      rw [eq_bot_iff]
      intro x hx
      have hxH : x ∈ H := by rwa [hH]
      obtain ⟨y, hy⟩ := hΨsurj ⟨x, hxH⟩
      have hy1 : Ψ y = 1 := (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top y)
      have hval : ((Ψ y : ↥H) : MulAut (Vtil V₀ V h.hyp125.isElemAbelian)) = x :=
        congrArg Subtype.val hy
      rw [hy1] at hval
      simpa using hval.symm
  let Ψe : Bar2 L ≃* ↥H :=
    MulEquiv.ofBijective Ψ ⟨(MonoidHom.ker_eq_bot_iff Ψ).1 hΨker, hΨsurj⟩
  let Φ : Bar2 L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)) := Ψe.trans ε
  have hΦmk : ∀ l : ↥L, Φ (QuotientGroup.mk l) =
      ε ⟨actTil V₀ V h.hyp125.isElemAbelian ⟨(l : G), hLstab l.2⟩,
        (by
          change actTil V₀ V h.hyp125.isElemAbelian ⟨(l : G), hLstab l.2⟩ ∈ H
          rw [hH]
          exact actTil_mem_barSub V₀ V h.hyp125.isElemAbelian l.2 (hLstab l.2))⟩ := by
    intro l
    show ε (Ψe (QuotientGroup.mk l)) = _
    rw [show Ψe (QuotientGroup.mk l) = Ψ (QuotientGroup.mk l) from rfl, hΨmk l]
  let P : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)) := Q
  have hPw : ∀ g ∈ P,
      (((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w ∈
        Submodule.span F {w} := by
    simpa [P] using hQw
  have hPpar : IsParabolicTwo ↥(StatedOmega (StatedQuadMinus 3 F b c)) P := by
    simpa [P] using hQpar
  obtain ⟨S, hSP⟩ := hPpar
  let Sbar : Sylow 2 (Bar2 L) := S.mapSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective
  let Sb : Subgroup (Bar2 L) := Sbar
  have hmapS : (Sb.map Φ.toMonoidHom) =
      (S : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c))) := by
    have hcoee : Sb = (S : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c))).map
        Φ.symm.toMonoidHom := Sylow.coe_mapSurjective (f := Φ.symm.toMonoidHom)
      Φ.symm.surjective S
    rw [hcoee, Subgroup.map_map]
    ext x
    simp [Function.comp_def]
  have hNbar : Subgroup.normalizer (Sb : Set (Bar2 L)) ≤ P.comap Φ := by
    intro x hx
    rw [Subgroup.mem_comap]
    apply hSP
    change Φ x ∈ Subgroup.normalizer ((S : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      Set ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 (hmapS.symm ▸ hy)
      have hz' : x * z * x⁻¹ ∈ Sb := (Subgroup.mem_normalizer_iff.1 hx z).1 hz
      have hmap : Φ (x * z * x⁻¹) ∈ Sb.map Φ.toMonoidHom :=
        Subgroup.mem_map.2 ⟨x * z * x⁻¹, hz', rfl⟩
      rw [hmapS] at hmap
      simpa using hmap
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hmapS.symm ▸ hy)
      have hz0 : x⁻¹ * z * x ∈ Sb :=
        (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * z * x)).2 (by simpa [mul_assoc] using hz)
      have hmap : Φ (x⁻¹ * z * x) ∈ Sb.map Φ.toMonoidHom :=
        Subgroup.mem_map.2 ⟨x⁻¹ * z * x, hz0, rfl⟩
      have hzy' : Φ z = Φ x * y * (Φ x)⁻¹ := hzy
      have hy' : Φ (x⁻¹ * z * x) = y := by
        calc Φ (x⁻¹ * z * x) = Φ x⁻¹ * Φ z * Φ x := by simp
          _ = Φ x⁻¹ * (Φ x * y * (Φ x)⁻¹) * Φ x := by rw [hzy']
          _ = y := by
            rw [map_inv]
            group
      rw [hmapS] at hmap
      rwa [hy'] at hmap
  let Pbar : Subgroup (Bar2 L) := P.comap Φ
  have hPbarPar : IsParabolicTwo (Bar2 L) Pbar := ⟨Sbar, hNbar⟩
  let mkL : ↥L →* Bar2 L := QuotientGroup.mk' (pCore 2 ↥L)
  let P₁ : Subgroup G := (Pbar.comap mkL).map L.subtype
  have hOQ : pCoreOf 2 L ≤ P₁ := by
    rw [Assembly.pCoreOf_eq_map_pCore]
    rintro - ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hy1 : mkL y = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) y).2 hy
    rw [hy1]
    simpa using P.one_mem
  have hsub : P₁.subgroupOf L = Pbar.comap mkL :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hpre : (P₁.subgroupOf L).map mkL = P.comap Φ.toMonoidHom := by
    rw [hsub]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pCore 2 ↥L)) Pbar
  have hpar : ParabolicOf L P₁ := by
    refine ⟨hOQ, Subgroup.map_subtype_le _, ?_⟩
    show IsParabolicTwo (Bar2 L) ((P₁.subgroupOf L).map mkL)
    rw [hsub, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pCore 2 ↥L))]
    exact hPbarPar
  have hPnorm : P₁ ≤ normalizer (Z : Set G) := by
    rw [hZdef]
    intro l hl
    have hstab_line : ∀ u ∈ P₁, ∀ z : G,
        z ∈ preTil V₀ V h.hyp125.isElemAbelian
          ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype) →
        u * z * u⁻¹ ∈ preTil V₀ V h.hyp125.isElemAbelian
          ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype) := by
      intro u hu z hz
      obtain ⟨u0, hu0, rfl⟩ := Subgroup.mem_map.1 hu
      have hPbar_mem : mkL u0 ∈ Pbar := hu0
      have hΦP : Φ (mkL u0) ∈ P := hPbar_mem
      have hΦeq := hΦmk u0
      have hmat : (((Φ (mkL u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w ∈ Submodule.span F {w} :=
        hPw (Φ (mkL u0)) hΦP
      have hmat' : (((Φ (QuotientGroup.mk u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w ∈ Submodule.span F {w} := by
        simpa [mkL] using hmat
      have hfixline : ∀ q : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)),
          q ∈ lineCoords ψ w →
            (actTil V₀ V h.hyp125.isElemAbelian ⟨(u0 : G), hLstab u0.2⟩) q.1 ∈
              (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype := by
        intro q hq
        obtain ⟨u, hu, huq⟩ := Subgroup.mem_map.1 hq
        have hψq : ψ q = u := by
          have h := congrArg ψ huq
          change ψ (ψ.symm u) = ψ q at h
          rw [ψ.apply_symm_apply] at h
          exact h.symm
        have hu' : Multiplicative.toAdd u ∈ Submodule.span F {w} := hu
        obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hu'
        have hψqadd : Multiplicative.toAdd (ψ q) = cc • w := by
          rw [hψq]
          exact hcc.symm
        have hco := hcoords ⟨actTil V₀ V h.hyp125.isElemAbelian ⟨(u0 : G), hLstab u0.2⟩,
            (by
              change actTil V₀ V h.hyp125.isElemAbelian ⟨(u0 : G), hLstab u0.2⟩ ∈ H
              rw [hH]
              exact actTil_mem_barSub V₀ V h.hyp125.isElemAbelian u0.2 (hLstab u0.2))⟩ q
        rw [← hΦeq] at hco
        have hco' : Multiplicative.toAdd
            (ψ ⟨(actTil V₀ V h.hyp125.isElemAbelian ⟨(u0 : G), hLstab u0.2⟩) q.1,
              Subgroup.mem_top _⟩) =
            (((Φ (QuotientGroup.mk u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
              GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
              Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ (cc • w) := by
          have h := congrArg Multiplicative.toAdd hco
          simp only [toAdd_ofAdd] at h
          rw [h, hψqadd]
        refine Subgroup.mem_map.2 ⟨⟨(actTil V₀ V h.hyp125.isElemAbelian
            ⟨(u0 : G), hLstab u0.2⟩) q.1, Subgroup.mem_top _⟩, ?_, rfl⟩
        refine Subgroup.mem_map.2 ⟨(Multiplicative.ofAdd
          ((((Φ (QuotientGroup.mk u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
            GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ (cc • w)) :
          Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)), ?_, ?_⟩
        · change (((Φ (QuotientGroup.mk u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
            GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ (cc • w) ∈
            Submodule.span F {w}
          rw [Matrix.mulVec_smul]
          change cc • ((((Φ (QuotientGroup.mk u0) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
            GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w) ∈ Submodule.span F {w}
          obtain ⟨dd, hdd⟩ := Submodule.mem_span_singleton.mp hmat'
          rw [← hdd, smul_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
        · rw [← hco']
          simp
      have hqline : mkTil V₀ V h.hyp125.isElemAbelian
          (IntMod.mk h.hyp125.isElemAbelian
            ⟨z, preTil_le V₀ V h.hyp125.isElemAbelian _ hz⟩) ∈
          (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype :=
        (mem_preTil_iff_of_mem V₀ V h.hyp125.isElemAbelian _
          (preTil_le _ _ _ _ hz)).1 hz
      obtain ⟨qt, hqt, hqtval⟩ := Subgroup.mem_map.1 hqline
      have hqt' : (⟨qt.1, Subgroup.mem_top qt.1⟩ :
          ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian))) = qt := Subtype.ext rfl
      have hline : (actTil V₀ V h.hyp125.isElemAbelian
          ⟨(u0 : G), hLstab u0.2⟩) qt.1 ∈
          (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype :=
        hfixline ⟨qt.1, Subgroup.mem_top qt.1⟩ (by rwa [hqt'])
      have hzV : z ∈ V := preTil_le V₀ V h.hyp125.isElemAbelian _ hz
      have huNorm : (u0 : G) ∈ Subgroup.normalizer (V : Set G) :=
        stabTil_le_normalizer V₀ V (hLstab u0.2)
      have hxV : (u0 : G) * z * (u0 : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 huNorm z).1 hzV
      refine (mem_preTil_iff_of_mem V₀ V h.hyp125.isElemAbelian
        ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype)
        (g := (u0 : G) * z * (u0 : G)⁻¹) hxV).2 ?_
      have hmk : mkTil V₀ V h.hyp125.isElemAbelian
          (IntMod.mk h.hyp125.isElemAbelian ⟨(u0 : G) * z * (u0 : G)⁻¹,
            hxV⟩) =
          (actTil V₀ V h.hyp125.isElemAbelian ⟨(u0 : G), hLstab u0.2⟩)
            (mkTil V₀ V h.hyp125.isElemAbelian
              (IntMod.mk h.hyp125.isElemAbelian
                ⟨z, preTil_le _ _ _ _ hz⟩)) := by
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
        change (IntMod.mk h.hyp125.isElemAbelian
            ⟨↑u0 * z * (↑u0)⁻¹, hxV⟩).val *
          ((IntMod.mk h.hyp125.isElemAbelian
            ⟨↑u0 * z * (↑u0)⁻¹, hxV⟩).val)⁻¹ ∈ V₀
        rw [mul_inv_cancel]
        exact V₀.one_mem
      rw [hmk, ← hqtval]
      exact hline
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hstab_line l hl z hz
    · intro hz
      have hstab := hstab_line (l⁻¹) (P₁.inv_mem hl) (l * z * l⁻¹) hz
      change z ∈ preTil V₀ V h.hyp125.isElemAbelian
        ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)).subtype)
      simpa [mul_assoc] using hstab
  exact ⟨Φ, P₁, hpar, hOQ, hpre, hPnorm⟩

theorem exists_isSylowOf_three (L : Subgroup G) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S : Sylow 3 ↥L⟩ := Sylow.nonempty (p := 3) (G := ↥L)
  refine ⟨(S : Subgroup ↥L).map L.subtype,
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨Subgroup.map_subtype_le _, ?_, ?_⟩⟩
  · exact (Sylow.isPGroup' S).map L.subtype
  · rw [Subgroup.relIndex]
    have hsub : (Subgroup.map L.subtype (S : Subgroup ↥L)).subgroupOf L =
        (S : Subgroup ↥L) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [L.subtype_injective hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hsub]
    exact Sylow.not_dvd_index S

theorem exists_hyp8102_of_isU4 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (hsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∃ P : Subgroup G, CFSG.LocalAnalysis.UniquenessCase.UC22.F08.Hyp8102 D L P p n := by
  have hsimple : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  rw [hXL] at hU4
  have hU4L : IsU4 (Bar2 L) n := LieModel.of_mulEquiv e.symm hU4
  obtain ⟨P, hP⟩ := exists_isSylowOf_three (G := G) L
  exact ⟨P, h.hL.1, Or.inr hU4L, hsp, h.hp, hP⟩

theorem data924_first_conjuncts {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hnU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (h1742 : S17.R17_42At D V₀ V) :
    1 < n ∧ IsU4 (Bar2 L) n := by
  have hsimple : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hnU4
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  have hU4L : IsU4 (Bar2 L) n := by
    rw [hXL] at hnU4
    exact LieModel.of_mulEquiv e.symm hnU4
  exact ⟨(isU4_barSub_cong h h1742 hnU4).2.2.1, hU4L⟩

@[expose] noncomputable def bar2SingularPreimage {Ω : Type} [Group Ω] (L : Subgroup G)
    (Φ : Bar2 L ≃* Ω) (R : Subgroup Ω) : Subgroup G :=
  ((R.comap Φ.toMonoidHom).comap (QuotientGroup.mk' (pCore 2 ↥L))).map L.subtype

theorem bar2SingularPreimage_map {Ω : Type} [Group Ω] (L : Subgroup G) (Φ : Bar2 L ≃* Ω)
    (R : Subgroup Ω) :
    ((bar2SingularPreimage L Φ R).subgroupOf L).map
      (Φ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L))) = R := by
  unfold bar2SingularPreimage
  change Subgroup.map (Φ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L)))
    (Subgroup.comap L.subtype (Subgroup.map L.subtype
      (Subgroup.comap (QuotientGroup.mk' (pCore 2 ↥L)) (Subgroup.comap Φ.toMonoidHom R)))) = R
  rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective,
    ← Subgroup.map_map,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (pCore 2 ↥L))]
  exact Subgroup.map_comap_eq_self_of_surjective Φ.surjective R

theorem pCoreOf_le_bar2SingularPreimage {Ω : Type} [Group Ω] (L : Subgroup G) (Φ : Bar2 L ≃* Ω)
    (R : Subgroup Ω) : pCoreOf 2 L ≤ bar2SingularPreimage L Φ R := by
  rw [Assembly.pCoreOf_eq_map_pCore]
  rintro - ⟨y, hy, rfl⟩
  refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have hy1 : QuotientGroup.mk' (pCore 2 ↥L) y = 1 :=
    (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) y).2 hy
  rw [hy1]
  exact (R.comap Φ.toMonoidHom).one_mem

theorem data924_18_23 (hK : K_Omega6Minus_singularPointStabilizer)
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (Z : Subgroup G)
    (hΩ : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 n)
    (hnU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (hV0 : V₀ = ⊥) (hFcard : Nat.card F = 2 ^ n)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcoords : NatCoordsOmegaMinusOn
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤
      (fun _ _ _ _ => trivial) F b c ε ψ)
    (hw0 : w ≠ 0) (hwq : StatedQuadMinus 3 F b c w = 0)
    (hZdef : Z = lineTil V₀ V h.hyp125.isElemAbelian ψ w) :
    ∃ P₁ X : Subgroup G,
      ParabolicOf L P₁ ∧ P₁ ≤ normalizer (Z : Set G) ∧ 1 < n ∧ IsU4 (Bar2 L) n ∧
        X = F07.DerInf P₁ ∧ IsL2 (Bar2 X) (2 * n) ∧ pCoreOf 2 X ≠ ⊥ ∧
          X ≤ normalizer (Z : Set G) := by
  obtain ⟨Q, hQw, hQpar, hQO2, hQl2, hQp, -⟩ := hK hFcard hbc w hw0 hwq
  obtain ⟨Φ, P₁, hPparL, -, hpre, hPnorm⟩ :=
    exists_parabolic_of_Q D V₀ V p L h ε ψ w Z hΩ hnU4 hV0 hFcard hbc hcoords
      hw0 hwq hZdef Q hQw hQpar
  have hPl2 : IsL2 (Bar2 (F07.DerInf Q)) (2 * n) := hQl2
  have hPp : pCoreOf 2 (F07.DerInf Q) ≠ ⊥ := hQp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let mkL : ↥L →* Bar2 L := QuotientGroup.mk' (pCore 2 ↥L)
  let ΦL : ↥L →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) := Φ.toMonoidHom.comp mkL
  have hP₁L : P₁ ≤ L := hPparL.2.1
  have hmapP : (P₁.subgroupOf L).map ΦL = Q := by
    rw [show ΦL = Φ.toMonoidHom.comp mkL from rfl, ← Subgroup.map_map, hpre,
      Subgroup.map_comap_eq_self_of_surjective Φ.surjective]
  have hkerΦL : ΦL.ker = pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : mkL x = 1 := Φ.injective (by simpa [ΦL] using hx)
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) x).1 h1
    · intro hx
      have h1 : mkL x = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) x).2 hx
      simp [ΦL, h1]
  let X : Subgroup G := F07.DerInf P₁
  have hXL : X ≤ L := (Subgroup.map_subtype_le _).trans hP₁L
  have hmapX : (X.subgroupOf L).map ΦL = F07.DerInf Q := by
    change Subgroup.map ΦL (((perfectResidual ↥P₁).map P₁.subtype).subgroupOf L) = F07.DerInf Q
    rw [perfectResidual_subtype_subgroupOf P₁ L hP₁L, ← hmapP]
    exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ΦL (P₁.subgroupOf L)
  let g : ↥(X.subgroupOf L) →* ↥(F07.DerInf Q) :=
    (ΦL.comp (X.subgroupOf L).subtype).codRestrict (F07.DerInf Q)
      (fun z => hmapX ▸ Subgroup.mem_map_of_mem ΦL z.2)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∈
        (X.subgroupOf L).map ΦL := by rw [hmapX]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hgker : g.ker = (pCore 2 ↥L).comap (X.subgroupOf L).subtype := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hz
      have h1 : ΦL (z : ↥L) = 1 := congrArg Subtype.val hz
      have h2 : (z : ↥L) ∈ ΦL.ker := (MonoidHom.mem_ker).2 h1
      rwa [hkerΦL] at h2
    · intro hz
      apply Subtype.ext
      have h2 : (z : ↥L) ∈ ΦL.ker := by rw [hkerΦL]; exact hz
      simpa [g] using (MonoidHom.mem_ker).1 h2
  have hg2 : IsPGroup 2 g.ker := by
    rw [hgker]
    exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
      (Subgroup.subtype_injective _)
  let eX : ↥(X.subgroupOf L) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXL
  let f : ↥X →* ↥(F07.DerInf Q) := g.comp eX.symm.toMonoidHom
  have hfsurj : Function.Surjective f :=
    hgsurj.comp eX.symm.surjective
  have hf2 : IsPGroup 2 f.ker := by
    have hker : f.ker = g.ker.comap eX.symm.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      rfl
    rw [hker]
    exact IsPGroup.comap_of_injective hg2 _ eX.symm.injective
  obtain ⟨eBar⟩ :=
    nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hf2
  have hL2X : IsL2 (Bar2 X) (2 * n) := LieModel.of_mulEquiv eBar.symm hPl2
  have hYp : pCore 2 ↥(F07.DerInf Q) ≠ ⊥ := by
    intro hbot
    apply hPp
    rw [CFSG.openPCoreOf_eq_map_pCore, hbot, Subgroup.map_bot]
  have hXp : pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_surjective_of_isPGroup_ker f hfsurj hf2 hYp
  have hXpOf : pCoreOf 2 X ≠ ⊥ := by
    rw [CFSG.Open.pCoreOf]
    intro hb
    exact hXp ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb)
  obtain ⟨hn1, hU4L⟩ := data924_first_conjuncts h hnU4 h1742
  have hXleP₁ : X ≤ P₁ := Subgroup.map_subtype_le _
  exact ⟨P₁, X, hPparL, hPnorm, hn1, hU4L, rfl, hL2X, hXpOf, hXleP₁.trans hPnorm⟩

theorem data8105_18_23 {D : Data G} (hK : K_Omega6Minus_singularPointStabilizer)
    (h8103 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R8103 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (Z : Subgroup G)
    (hΩ : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 n)
    (hnU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n)
    (hV0 : V₀ = ⊥) (hFcard : Nat.card F = 2 ^ n)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcoords : NatCoordsOmegaMinusOn
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤
      (fun _ _ _ _ => trivial) F b c ε ψ)
    (hw0 : w ≠ 0) (hwq : StatedQuadMinus 3 F b c w = 0)
    (hZdef : Z = lineTil V₀ V h.hyp125.isElemAbelian ψ w)
    (hsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∃ P B H' : Subgroup G,
      CFSG.LocalAnalysis.UniquenessCase.UC22.F08.Hyp8102 D L P p n ∧
        CFSG.LocalAnalysis.UniquenessCase.UC22.F08.NotationB8103 L P n B ∧
          H' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.calK8104 D P
            (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.KOf8103 L B) ∧
            H' ≤ normalizer (Z : Set G) := by
  obtain ⟨Q, hQw, hQpar, hQO2, hQl2, hQp, hQB⟩ := hK hFcard hbc w hw0 hwq
  obtain ⟨P₀, hP₀⟩ := exists_hyp8102_of_isU4 h hnU4 hsp
  have hEven : Even n := (h8103 L P₀ p n hP₀).1
  obtain ⟨Bbar, Pbar3, hBbarCard, hBbarLe, hPbarSyl, hPbarCent, hPbarQ, hKbarQ,
    hKbarL2⟩ := hQB hEven
  obtain ⟨Φ, P₁, hP₁par, hP₁O2, hP₁pre, hP₁N⟩ :=
    exists_parabolic_of_Q D V₀ V p L h ε ψ w Z hΩ hnU4 hV0 hFcard hbc hcoords
      hw0 hwq hZdef Q hQw hQpar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let mkL : ↥L →* Bar2 L := QuotientGroup.mk' (pCore 2 ↥L)
  let ΦL : ↥L →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) := Φ.toMonoidHom.comp mkL
  have hP₁L : P₁ ≤ L := hP₁par.2.1
  have hΦLsurj : Function.Surjective ΦL := Φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerΦL : ΦL.ker = pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : mkL x = 1 := Φ.injective (by simpa [ΦL] using hx)
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) x).1 h1
    · intro hx
      have h1 : mkL x = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 ↥L) x).2 hx
      simp [ΦL, h1]
  have hmapQ : (P₁.subgroupOf L).map ΦL = Q := by
    rw [show ΦL = Φ.toMonoidHom.comp mkL from rfl, ← Subgroup.map_map, hP₁pre,
      Subgroup.map_comap_eq_self_of_surjective Φ.surjective]
  let S : Subgroup G := bar2SingularPreimage L Φ Pbar3
  have hSL : S ≤ L := Subgroup.map_subtype_le _
  have hSmap : (S.subgroupOf L).map ΦL = Pbar3 := bar2SingularPreimage_map L Φ Pbar3
  have hO2S : pCoreOf 2 L ≤ S := pCoreOf_le_bar2SingularPreimage L Φ Pbar3
  have hSsub : S.subgroupOf L = (Pbar3.comap Φ.toMonoidHom).comap mkL := by
    unfold S bar2SingularPreimage
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hP₁sub : P₁.subgroupOf L = (Q.comap Φ.toMonoidHom).comap mkL := by
    rw [← hP₁pre]
    refine (Subgroup.comap_map_eq_self ?_).symm
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hP₁O2 ⟨x, hx, rfl⟩)
  have hSP₁ : S ≤ P₁ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSL,
      ← Subgroup.map_subgroupOf_eq_of_le hP₁L]
    exact Subgroup.map_mono (by
      rw [hSsub, hP₁sub]
      exact Subgroup.comap_mono (Subgroup.comap_mono hPbarQ))
  have hSindex : S.relIndex L = Pbar3.index := by
    change (S.subgroupOf L).index = Pbar3.index
    rw [hSsub, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 ↥L))]
    exact Subgroup.index_comap_of_surjective Pbar3 Φ.surjective
  have hndvdS : ¬ 3 ∣ S.relIndex L := by
    rw [hSindex]
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hPbarSyl).2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨P, hPSyl⟩ := exists_isSylowOf_three (G := G) S
  have hPS : P ≤ S := hPSyl.le
  have hPL : P ≤ L := hPS.trans hSL
  have hP3 : IsPGroup 3 P := hPSyl.isPGroup
  have hPSylL : CFSG.ABGLocalTools.IsSylowOf 3 P L := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hPSyl ⊢
    obtain ⟨-, -, hndvdPS⟩ := hPSyl
    refine ⟨hPL, hP3, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P S L hPS hSL]
    intro hdvd
    rcases (Nat.prime_three.dvd_mul.mp hdvd) with h | h
    · exact hndvdPS h
    · exact hndvdS h
  have hsimple : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hnU4
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  have hU4L : IsU4 (Bar2 L) n := by
    rw [hXL] at hnU4
    exact LieModel.of_mulEquiv e.symm hnU4
  have hHyp : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.Hyp8102 D L P p n :=
    ⟨h.hL.1, Or.inr hU4L, hsp, h.hp, hPSylL⟩
  have hPimSyl : CFSG.ABGLocalTools.IsSylowOf 3
      ((P.subgroupOf L).map ΦL) ⊤ := by
    obtain ⟨Q', hQ'⟩ := hPSylL.exists_sylow_eq_subgroupOf
    let S' : Sylow 3 ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
      Sylow.mapSurjective (f := ΦL) hΦLsurj Q'
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    have hPsub3 : IsPGroup 3 (P.subgroupOf L) := hP3.comap_subtype (K := L)
    refine ⟨le_top, hPsub3.map ΦL, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have hS' : (S' : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c))) =
        (P.subgroupOf L).map ΦL := by
      rw [Sylow.coe_mapSurjective, hQ']
    rw [← hS']
    exact S'.not_dvd_index
  have himle : (P.subgroupOf L).map ΦL ≤ Pbar3 := by
    rw [← hSmap]
    refine Subgroup.map_mono ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hPS (Subgroup.mem_subgroupOf.mp hx))
  have hPmap : (P.subgroupOf L).map ΦL = Pbar3 :=
    (CFSG.ABGLocalTools.IsSylowOf.eq_of_le hPimSyl himle le_top hPbarSyl.isPGroup).symm
  let φP : ↥P →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    ΦL.comp (Subgroup.inclusion hPL)
  have hφPrange : φP.range = Pbar3 := by
    ext y
    rw [MonoidHom.range_eq_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, -, rfl⟩
      rw [← hPmap]
      exact Subgroup.mem_map.mpr ⟨⟨(x : G), hPL x.2⟩,
        Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · intro hy
      have hy' : (y : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∈
          (P.subgroupOf L).map ΦL := by rwa [hPmap]
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subgroup.mem_top _, hxy⟩
  have hdisj : Disjoint P (pCoreOf 2 L) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hφPker : φP.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : ΦL ((Subgroup.inclusion hPL) x) = 1 := by
      simpa [φP] using congrArg Subtype.val hx
    have hx2 : ((Subgroup.inclusion hPL) x) ∈ ΦL.ker := (MonoidHom.mem_ker).2 hx1
    rw [hkerΦL] at hx2
    have hx3 : ((x : ↥P) : G) ∈ pCoreOf 2 L := ⟨_, hx2, rfl⟩
    have hxP : ((x : ↥P) : G) ∈ P := x.2
    have hbot : ((x : ↥P) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj.eq_bot]
      exact ⟨hxP, hx3⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  let φPinj : Function.Injective φP := (MonoidHom.ker_eq_bot_iff φP).mp hφPker
  let BP : Subgroup ↥P := Bbar.comap φP
  let B : Subgroup G := BP.map P.subtype
  have hBle : B ≤ P := Subgroup.map_subtype_le _
  have hBcard : Nat.card B = 3 := by
    rw [show B = BP.map P.subtype from rfl, Subgroup.card_map_of_injective P.subtype_injective]
    have hcomap : BP.map φP = Bbar := by
      rw [Subgroup.map_comap_eq, hφPrange, inf_eq_right.mpr hBbarLe]
    calc Nat.card BP = Nat.card (BP.map φP) := (Subgroup.card_map_of_injective φPinj).symm
      _ = Nat.card Bbar := by rw [hcomap]
      _ = 3 := hBbarCard
  have hPB : P ≤ Subgroup.centralizer (B : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbP : b ∈ P := hBle hb
    have hcomm : ⁅p, b⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hp hbP) (P.inv_mem hp)) (P.inv_mem hbP)
    have hbBP : (⟨b, hbP⟩ : ↥P) ∈ BP := by
      obtain ⟨bp, hbp, hbpeq⟩ := Subgroup.mem_map.mp hb
      have hEq : (⟨b, hbP⟩ : ↥P) = bp := Subtype.ext hbpeq.symm
      rwa [hEq]
    have hbBbar : φP ⟨b, hbP⟩ ∈ Bbar := hbBP
    have hpPbar : φP ⟨p, hp⟩ ∈ Pbar3 := by
      rw [← hφPrange, MonoidHom.range_eq_map]
      exact Subgroup.mem_map.mpr ⟨⟨p, hp⟩, trivial, rfl⟩
    have hcent : φP ⟨b, hbP⟩ * φP ⟨p, hp⟩ = φP ⟨p, hp⟩ * φP ⟨b, hbP⟩ :=
      Subgroup.mem_centralizer_iff.mp (hPbarCent hpPbar) (φP ⟨b, hbP⟩) hbBbar
    have him : φP ⟨⁅p, b⁆, hcomm⟩ = 1 := by
      rw [show (⟨⁅p, b⁆, hcomm⟩ : ↥P) = ⁅(⟨p, hp⟩ : ↥P), (⟨b, hbP⟩ : ↥P)⁆ from Subtype.ext rfl,
        map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcent.symm
    have h1 : ⁅p, b⁆ = 1 := by
      by_contra hne
      have hmem : (⟨⁅p, b⁆, hcomm⟩ : ↥P) ∈ φP.ker := him
      rw [hφPker] at hmem
      exact hne (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hBL : B ≤ L := hBle.trans hPL
  have hB_L3 : IsPGroup 3 (B.subgroupOf L) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hBcard]
    norm_num
  have hN3 : ¬ 3 ∣ Nat.card (pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    exact (by norm_num : (3 : ℕ) ≠ 2)
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h))
  have hBbarMap : (B.subgroupOf L).map ΦL = Bbar := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
      have hbP : (b : G) ∈ P := hBle hbB
      have hbBP : (⟨(b : G), hbP⟩ : ↥P) ∈ BP := by
        rw [show BP = B.subgroupOf P from
          (Subgroup.comap_map_eq_self_of_injective P.subtype_injective BP).symm]
        exact Subgroup.mem_subgroupOf.mpr hbB
      have := hbBP
      rw [show BP = Bbar.comap φP from rfl] at this
      exact this
    · intro hy
      have hBP : BP.map φP = Bbar := by
        rw [Subgroup.map_comap_eq, hφPrange, inf_eq_right.mpr hBbarLe]
      obtain ⟨bp, hbp, hbpy⟩ := Subgroup.mem_map.mp (by rwa [← hBP] at hy)
      refine ⟨⟨(bp : G), Subgroup.mem_subgroupOf.mpr (hPL bp.2)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem P.subtype hbp), ?_⟩
      change ΦL ⟨(bp : G), hPL bp.2⟩ = y
      rw [show (⟨(bp : G), hPL bp.2⟩ : ↥L) = (Subgroup.inclusion hPL) bp from
        Subtype.ext rfl]
      exact hbpy
  have hcent1 : (Subgroup.centralizer (B.subgroupOf L : Set ↥L)).map mkL =
      Subgroup.centralizer (((B.subgroupOf L).map mkL : Subgroup (Bar2 L)) : Set (Bar2 L)) :=
    CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 (pCore 2 ↥L) hN3
      (B.subgroupOf L) hB_L3
  have hcent2 : (Subgroup.centralizer
      (((B.subgroupOf L).map mkL : Subgroup (Bar2 L)) : Set (Bar2 L))).map Φ.toMonoidHom =
      Subgroup.centralizer (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) := by
    rw [← CFSG.AGLEmbeddingD2.map_centralizer_equiv Φ ((B.subgroupOf L).map mkL)]
    congr 1
    rw [Subgroup.map_map, hBbarMap]
  have hcentMap : (Subgroup.centralizer (B.subgroupOf L : Set ↥L)).map ΦL =
      Subgroup.centralizer (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) := by
    rw [show ΦL = Φ.toMonoidHom.comp mkL from rfl, ← Subgroup.map_map, hcent1, hcent2]
  have hC_Lsub : (L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf L =
      Subgroup.centralizer (B.subgroupOf L : Set ↥L) := by
    have h := CFSG.OddStandard.Solomon75.map_centralizer_subgroupOf L B hBL
    rw [Subgroup.subgroupOf, ← h]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  let C : Subgroup G := L ⊓ Subgroup.centralizer (B : Set G)
  have hCL : C ≤ L := inf_le_left
  have hCmap : (C.subgroupOf L).map ΦL =
      Subgroup.centralizer (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) := by
    rw [show C.subgroupOf L = Subgroup.centralizer (B.subgroupOf L : Set ↥L) from hC_Lsub,
      hcentMap]
  let K : Subgroup G := F08.KOf8103 L B
  let Kbar : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    F07.DerInf (Subgroup.centralizer (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))))
  have hKmap : (K.subgroupOf L).map ΦL = Kbar := by
    dsimp only [K, Kbar]
    change Subgroup.map ΦL (((perfectResidual ↥C).map C.subtype).subgroupOf L) =
      (perfectResidual ↥(Subgroup.centralizer
        (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))))).map
        (Subgroup.centralizer (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c)))).subtype
    rw [perfectResidual_subtype_subgroupOf C L hCL, ← hCmap]
    exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ΦL (C.subgroupOf L)
  have hKeq : F08.KOf8103 ⊤ Bbar = Kbar := by
    change F07.DerInf (⊤ ⊓ Subgroup.centralizer
      (Bbar : Set ↥(StatedOmega (StatedQuadMinus 3 F b c)))) = Kbar
    rw [top_inf_eq]
  have hKbarL2' : IsL2 (Bar2 Kbar) (2 * n) := by
    rw [← hKeq]
    exact hKbarL2
  have hKL : K ≤ L := (Subgroup.map_subtype_le _).trans hCL
  let gK : ↥(K.subgroupOf L) →* ↥Kbar :=
    (ΦL.comp (K.subgroupOf L).subtype).codRestrict Kbar
      (fun z => hKmap ▸ Subgroup.mem_map_of_mem ΦL z.2)
  have hgKsurj : Function.Surjective gK := by
    intro y
    have hy : (y : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∈
        (K.subgroupOf L).map ΦL := by rw [hKmap]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hgKker : gK.ker = (pCore 2 ↥L).comap (K.subgroupOf L).subtype := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hz
      have h1 : ΦL (z : ↥L) = 1 := congrArg Subtype.val hz
      have h2 : (z : ↥L) ∈ ΦL.ker := (MonoidHom.mem_ker).2 h1
      rwa [hkerΦL] at h2
    · intro hz
      apply Subtype.ext
      have h2 : (z : ↥L) ∈ ΦL.ker := by rw [hkerΦL]; exact hz
      simpa [gK] using (MonoidHom.mem_ker).1 h2
  have hgK2 : IsPGroup 2 gK.ker := by
    rw [hgKker]
    exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
      (Subgroup.subtype_injective _)
  let eK : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  let fK : ↥K →* ↥Kbar := gK.comp eK.symm.toMonoidHom
  have hfKsurj : Function.Surjective fK := hgKsurj.comp eK.symm.surjective
  have hfK2 : IsPGroup 2 fK.ker := by
    have hker : fK.ker = gK.ker.comap eK.symm.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      rfl
    rw [hker]
    exact IsPGroup.comap_of_injective hgK2 _ eK.symm.injective
  obtain ⟨eKbar⟩ :=
    nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker fK hfKsurj hfK2
  have hL2K : IsL2 (Bar2 K) (2 * n) := LieModel.of_mulEquiv eKbar.symm hKbarL2'
  have hKP₁ : K ≤ P₁ := by
    intro x hx
    have hxL : x ∈ L := hKL hx
    have hxKbar : ΦL ⟨x, hxL⟩ ∈ Kbar := by
      have hmem : ΦL ⟨x, hxL⟩ ∈ (K.subgroupOf L).map ΦL := by
        exact (Subgroup.mem_map (f := ΦL) (K := K.subgroupOf L)).mpr
          ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rwa [hKmap] at hmem
    have hxQ : ΦL ⟨x, hxL⟩ ∈ Q := hKbarQ (hKeq.symm ▸ hxKbar)
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ P₁.subgroupOf L := by
      rw [hP₁sub, Subgroup.mem_comap]
      exact hxQ
    exact Subgroup.mem_subgroupOf.mp hxsub
  let fP : ↥P₁ →* ↥Q :=
    (ΦL.comp (Subgroup.inclusion hP₁L)).codRestrict Q
      (fun z => hmapQ ▸ Subgroup.mem_map.mpr
        ⟨(Subgroup.inclusion hP₁L z), Subgroup.mem_subgroupOf.mpr z.2, rfl⟩)
  have hfPsurj : Function.Surjective fP := by
    intro y
    have hy : (y : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∈
        (P₁.subgroupOf L).map ΦL := by rw [hmapQ]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
    apply Subtype.ext
    change ΦL ((Subgroup.inclusion hP₁L) _) = y
    rwa [show (Subgroup.inclusion hP₁L) _ = z from Subtype.ext rfl]
  have hfPker : fP.ker = (pCore 2 ↥L).comap (Subgroup.inclusion hP₁L) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hz
      have h1 : ΦL ((Subgroup.inclusion hP₁L) z) = 1 := congrArg Subtype.val hz
      have h2 : (Subgroup.inclusion hP₁L z) ∈ ΦL.ker := (MonoidHom.mem_ker).2 h1
      rwa [hkerΦL] at h2
    · intro hz
      apply Subtype.ext
      have h2 : (Subgroup.inclusion hP₁L z) ∈ ΦL.ker := by rw [hkerΦL]; exact hz
      simpa [fP] using (MonoidHom.mem_ker).1 h2
  have hfP2 : IsPGroup 2 fP.ker := by
    rw [hfPker]
    exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
      (Subgroup.inclusion_injective hP₁L)
  have hQ2 : pCore 2 ↥Q ≠ ⊥ := by
    intro hbot
    apply hQO2
    rw [CFSG.openPCoreOf_eq_map_pCore, hbot, Subgroup.map_bot]
  have hP₁core : pCoreOf 2 P₁ ≠ ⊥ := by
    have h := pCore_ne_bot_of_surjective_of_isPGroup_ker fP hfPsurj hfP2 hQ2
    rw [CFSG.Open.pCoreOf]
    intro hb
    exact h ((Subgroup.map_eq_bot_iff_of_injective _ P₁.subtype_injective).mp hb)
  let H' : Subgroup G := pCoreOf 2 P₁ ⊔ K ⊔ P
  have hO2P₁leH' : pCoreOf 2 P₁ ≤ H' := le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have hKH' : K ≤ H' := le_sup_of_le_left le_sup_right
  have hPH' : P ≤ H' := le_sup_right
  have hPP₁ : P ≤ P₁ := hPS.trans hSP₁
  have hH'leP₁ : H' ≤ P₁ := sup_le (sup_le (CFSG.openPCoreOf_le 2 P₁) hKP₁) hPP₁
  have hH'leM : H' ≤ D.M := hH'leP₁.trans (hP₁L.trans h.hL.1.1.le)
  have hH'N : H' ≤ normalizer (Z : Set G) := hH'leP₁.trans hP₁N
  have hH'normO2 : H' ≤ normalizer (pCoreOf 2 P₁ : Set G) :=
    hH'leP₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁)
  have hO2H' : pCoreOf 2 P₁ ≤ pCoreOf 2 H' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2P₁leH' hH'normO2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P₁)
  have hH'core : pCoreOf 2 H' ≠ ⊥ := by
    intro hbot
    apply hP₁core
    rw [hbot] at hO2H'
    exact le_bot_iff.mp hO2H'
  have hPC : P ≤ C := le_inf hPL hPB
  have hPK : P ≤ normalizer (K : Set G) := by
    have hchar : (CFSG.perfectResidual ↥C).Characteristic :=
      CFSG.perfectResidual_characteristic'
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm1.le_normalizer_of_characteristic
      (L := C) (H := P) (hPC.trans Subgroup.le_normalizer) (CFSG.perfectResidual ↥C)
    have hKdef : K = (CFSG.perfectResidual ↥C).map C.subtype := rfl
    rw [hKdef]
    exact h
  have hKO2 : K ≤ normalizer (pCoreOf 2 P₁ : Set G) :=
    hKP₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁)
  have hPO2 : P ≤ normalizer (pCoreOf 2 P₁ : Set G) :=
    hPP₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁)
  have hAK : ((pCoreOf 2 P₁ ⊔ K : Subgroup G) : Set G) =
      (pCoreOf 2 P₁ : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKO2
  have hPA : P ≤ normalizer ((pCoreOf 2 P₁ ⊔ K : Subgroup G) : Set G) := by
    have hfwd : ∀ q : G, q ∈ P → ∀ y ∈ (pCoreOf 2 P₁ ⊔ K : Subgroup G),
        q * y * q⁻¹ ∈ (pCoreOf 2 P₁ ⊔ K : Subgroup G) := by
      intro q hq y hy
      change y ∈ ((pCoreOf 2 P₁ ⊔ K : Subgroup G) : Set G) at hy
      change q * y * q⁻¹ ∈ ((pCoreOf 2 P₁ ⊔ K : Subgroup G) : Set G)
      rw [hAK] at hy ⊢
      obtain ⟨o, ho, k, hk, rfl⟩ := hy
      have hqo : q * o * q⁻¹ ∈ pCoreOf 2 P₁ :=
        (Subgroup.mem_normalizer_iff.mp (hPO2 hq) o).mp ho
      have hqk : q * k * q⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPK hq) k).mp hk
      exact ⟨_, hqo, _, hqk, by group⟩
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hfwd q hq y
    · intro hy
      have h := hfwd q⁻¹ (P.inv_mem hq) (q * y * q⁻¹) hy
      simpa [mul_assoc] using h
  have hAP : ((pCoreOf 2 P₁ ⊔ K ⊔ P : Subgroup G) : Set G) =
      ((pCoreOf 2 P₁ ⊔ K : Subgroup G) : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPA
  have hH'prod : (H' : Set G) =
      (pCoreOf 2 P₁ : Set G) * (K : Set G) * (P : Set G) := by
    dsimp only [H']
    rw [hAP, hAK]
  have hKH'in : K ⊓ H' = K := inf_eq_left.mpr hKH'
  have hH'eq : (H' : Set G) =
      (pCoreOf 2 H' : Set G) * ((K ⊓ H' : Subgroup G) : Set G) * (P : Set G) := by
    rw [hKH'in, hH'prod]
    apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_mul] at hz
      obtain ⟨w, hw, c, hc, rfl⟩ := hz
      rw [Set.mem_mul] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      rw [Set.mem_mul]
      exact ⟨a * b, ⟨a, hO2H' ha, b, hb, rfl⟩, c, hc, rfl⟩
    · intro z hz
      rw [Set.mem_mul] at hz
      obtain ⟨w, hw, c, hc, rfl⟩ := hz
      rw [Set.mem_mul] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      rw [← hH'prod]
      exact H'.mul_mem (H'.mul_mem (CFSG.openPCoreOf_le 2 H' ha) (hKH' hb)) (hPH' hc)
  have hH'mem : H' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.calK8104
      D P K := ⟨hH'leM, hH'core, hKH', hH'eq⟩
  have hBnot : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.NotationB8103 L P n B :=
    ⟨hBcard, hBle, by simpa [K] using hL2K⟩
  exact ⟨P, B, H', hHyp, hBnot, hH'mem, hH'N⟩

theorem eighteen_twentythree_of_K (hKpar : K_Omega6Minus_singularPointStabilizer)
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h22 : R18_22At D V₀ V p L h)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) (h1742 : S17.R17_42At D V₀ V)
    (h8103 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R8103 D)
    (h8_105 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.R8_105 D)
    (h924 : R9_24X D) :
    R18_23At D V₀ V p L := by
  unfold R18_23At
  by_cases hV₀ : V₀ = ⊥
  · have hP12 : P18_13_2 D V₀ V p L h 1 := h22
    have h22' : R18_22At D V₀ V p L h := h22
    obtain ⟨-, -, n, hΩ, -⟩ := h22
    have hU4H : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n := by
      obtain ⟨-, K, hKf, hKfin, b, c, hcard, hnonsing, ⟨e⟩⟩ := hΩ
      exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kOmega6MinusU4_holds
        _ n K b c hcard hnonsing ⟨e⟩
    obtain ⟨F, hF, hFfin, b, c, hFcard, hbc, ε, ψ, hcoords, w, hw, hsing, hline⟩ :=
      singularLine_18_23_of_K D V₀ V p L h h22' h16 h17 h18 h1742 hP12 n hΩ hU4H hV₀
    letI := hF
    letI := hFfin
    set Z : Subgroup G := lineTil V₀ V h.hyp125.isElemAbelian ψ w with hZdef
    have hZC : Z ≤ V ⊓ centralizer ((F12.Wi 2 D.T V : Subgroup G) : Set G) := hline
    have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.hyp125.inCalV
    have hZCi : Z ≤ F12.Ci 2 D.T V := by
      intro x hx
      exact ⟨hVT (hZC hx).1, (hZC hx).2⟩
    have hZne : Z ≠ ⊥ := by
      rw [hZdef]
      exact lineTil_ne_bot V₀ V h.hyp125.isElemAbelian ψ hw
    have hZ2 : IsPGroup 2 Z :=
      h.hyp125.isElemAbelian.isPGroup.to_le (fun x hx => (hZC hx).1)
    have hNZ : normalizer (Z : Set G) ≤ D.M := by
      by_cases hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M
      · obtain ⟨P₁, X, hpar, -, hn, hU4L, hX, hL2, hO2, hXZ⟩ :=
          data924_18_23 hKpar D h h1742 ε ψ w Z hΩ hU4H hV₀ hFcard hbc hcoords hw hsing hZdef
        have hLN : D.M ≤ normalizer (L : Set G) := by
          have hXL := (conjClosure_eq_and_bar2_equiv_of_hyp18 h
            (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4H)).1
          rw [← hXL]
          exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
        have hcomm := s16c6_comm D h.hL.1 hLN hn hU4L
          (fun {_ _ _} hP' hX' hL2' hXR' => s16c6_u4_overgroup hn hU4L hP' hX' hL2' hXR')
          hpar hX hL2 hO2
        exact CFSG.LocalAnalysis.WeakClosure81.normalizer_le_of_uniqueMax
          (h924 L P₁ X n h.hL.1 hLN hn hU4L hpar hX hL2 hO2 hcomm hsp) hZne hZ2 hXZ
      · obtain ⟨P, B, H', h102, hB, hHK, hHZ⟩ :=
          data8105_18_23 hKpar h8103 h ε ψ w Z hΩ hU4H hV₀ hFcard hbc hcoords hw hsing
            hZdef hsp
        exact CFSG.LocalAnalysis.WeakClosure81.normalizer_le_of_uniqueMax
          (h8_105 L P p n h102 B hB H' hHK) hZne hZ2 hHZ
    refine (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hZCi)).trans ?_
    exact (Subgroup.centralizer_le_normalizer (Z : Set G)).trans hNZ
  · have hCi : F12.Ci 2 D.T V = CFSG.Quasithin.E3.cClos V 2 D.T :=
      S17.Ci_eq_cClos 2 D.T V h.hyp125.isElemAbelian
    rw [hCi]
    exact centralizer_cClos_le_of_ne_bot D h.hyp125 hV₀ 2

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
