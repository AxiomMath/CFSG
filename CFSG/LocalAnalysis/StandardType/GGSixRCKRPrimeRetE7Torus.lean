module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Frame
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Ree.Endo
import CFSG.Mathlib.RingTheory.UnitOrderOf

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley



private theorem rootChar_eq_of_eq_simple {τ σ : Tag} {K : Type} [Field K]
    (j : (Fin τ.rank → ℤ) →+ (Fin σ.rank → ℤ))
    {a : Fin τ.rank → Kˣ} {b : Fin σ.rank → Kˣ}
    (h : ∀ k, rootChar (τ := τ) a (Pi.single k 1) =
      rootChar (τ := σ) b (j (Pi.single k 1))) (v : Fin τ.rank → ℤ) :
    rootChar (τ := τ) a v = rootChar (τ := σ) b (j v) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hjv : j v = ∑ i, v i • j (Pi.single i 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul j (v i) _
  conv_lhs => rw [hv]
  conv_rhs => rw [hjv]
  rw [rootChar_sum (τ := τ), rootChar_sum (τ := σ)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [rootChar_zsmul (τ := τ), rootChar_zsmul (τ := σ), h]

theorem exists_rckE7_torus_transfer {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {b : ModGL τ GGL} (hb : b ∈ torusGroup τ GGL) :
    ∃ t : adjointGroup Tag.E7 GGL, (t : ModGL Tag.E7 GGL) ∈ torusGroup Tag.E7 GGL ∧
      (∀ y : adjointGroup Tag.E7 GGL, (F.ε (t * y * t⁻¹) : ModGL τ GGL) = b * F.ε y * b⁻¹) ∧
      ∀ δ, rckRootVal (t : ModGL Tag.E7 GGL) δ = rckRootVal b (F.j δ) := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hb
  have hcoord : rckTorusCoord b = a := by
    rw [ha]
    exact Function.leftInverse_invFun
      (f := (rootDiagUnitHom τ GGL : (Fin τ.rank → GGLˣ) → ModGL τ GGL))
      CFSG.LieType.Chevalley.rootDiagUnit_injective a
  let a' : Fin Tag.E7.rank → GGLˣ := fun k => rckRootVal b (F.j (Pi.single k 1))
  have hchar : ∀ k, rootChar (τ := Tag.E7) a' (Pi.single k 1) =
        rootChar (τ := τ) a (F.j (Pi.single k 1)) := by
    intro k
    rw [show rootChar (τ := Tag.E7) a' (Pi.single k 1) = a' k from by
      simpa using rootChar_nsmul_single a' k 1]
    show rckRootVal b (F.j (Pi.single k 1)) =
      rootChar (τ := τ) a (F.j (Pi.single k 1))
    rw [rckRootVal, hcoord]
    rfl
  have hchar' : ∀ v, rootChar (τ := Tag.E7) a' v = rootChar (τ := τ) a (F.j v) :=
    rootChar_eq_of_eq_simple F.j hchar
  have hcoord' : rckTorusCoord (rootDiagUnit Tag.E7 a') = a' :=
    Function.leftInverse_invFun
      (f := (rootDiagUnitHom Tag.E7 GGL : (Fin Tag.E7.rank → GGLˣ) → ModGL Tag.E7 GGL))
      CFSG.LieType.Chevalley.rootDiagUnit_injective a'
  let t0 : ModGL Tag.E7 GGL := rootDiagUnit Tag.E7 a'
  have ht_tg : t0 ∈ torusGroup Tag.E7 GGL := rootDiagUnit_mem_torusGroup_E7 a'
  have ht_adj : t0 ∈ adjointGroup Tag.E7 GGL :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup ht_tg
  let T : adjointGroup Tag.E7 GGL := ⟨t0, ht_adj⟩
  have hmain : ∀ y : adjointGroup Tag.E7 GGL,
      (F.ε (T * y * T⁻¹) : ModGL τ GGL) = b * F.ε y * b⁻¹ := by
    let f : adjointGroup Tag.E7 GGL →* ModGL τ GGL :=
      (Subgroup.subtype _).comp (F.ε.toMonoidHom.comp (MulAut.conj T).toMonoidHom)
    let g : adjointGroup Tag.E7 GGL →* ModGL τ GGL :=
      (MulAut.conj b).toMonoidHom.comp ((Subgroup.subtype _).comp F.ε.toMonoidHom)
    have hfg : f = g := by
      refine CFSG.LieType.Ree.adjointGroup_hom_ext ?_ ?_
      · intro i c
        have hx : (xElement i c : adjointGroup Tag.E7 GGL) =
            ⟨pinnedX Tag.E7 GGL (Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ :=
          Subtype.ext (pinnedX_single (τ := Tag.E7) (R := GGL) i c).symm
        have hconj : T * (xElement i c) * T⁻¹ =
            ⟨pinnedX Tag.E7 GGL (Pi.single i 1)
                ((rootChar a' (Pi.single i 1) : GGL) * c), pinnedX_mem_adjointGroup _ _⟩ := by
          rw [hx]
          exact Subtype.ext (rootDiagUnit_conj_pinnedX a' (isRoot_single Tag.E7 i) c)
        have hrootγ : IsRoot τ (F.j (Pi.single i 1)) :=
          F.isRoot _ (F.bijOn.mapsTo (isRoot_single Tag.E7 i))
        change (F.ε (T * xElement i c * T⁻¹) : ModGL τ GGL) =
          b * (F.ε (xElement i c) : ModGL τ GGL) * b⁻¹
        rw [hconj, F.pinned (Pi.single i 1) (isRoot_single Tag.E7 i) _, hx,
          F.pinned (Pi.single i 1) (isRoot_single Tag.E7 i) _, ha,
          rootDiagUnit_conj_pinnedX a hrootγ c, hchar' (Pi.single i 1)]
      · intro i c
        have hy : (yElement i c : adjointGroup Tag.E7 GGL) =
            ⟨pinnedX Tag.E7 GGL (-Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ :=
          Subtype.ext (pinnedX_neg_single (τ := Tag.E7) (R := GGL) i c).symm
        have hconj : T * (yElement i c) * T⁻¹ =
            ⟨pinnedX Tag.E7 GGL (-Pi.single i 1)
                ((rootChar a' (-Pi.single i 1) : GGL) * c), pinnedX_mem_adjointGroup _ _⟩ := by
          rw [hy]
          exact Subtype.ext (rootDiagUnit_conj_pinnedX a' (isRoot_neg_single Tag.E7 i) c)
        have hrootγ : IsRoot τ (F.j (-Pi.single i 1)) :=
          F.isRoot _ (F.bijOn.mapsTo (isRoot_neg_single Tag.E7 i))
        change (F.ε (T * yElement i c * T⁻¹) : ModGL τ GGL) =
          b * (F.ε (yElement i c) : ModGL τ GGL) * b⁻¹
        rw [hconj, F.pinned (-Pi.single i 1) (isRoot_neg_single Tag.E7 i) _, hy,
          F.pinned (-Pi.single i 1) (isRoot_neg_single Tag.E7 i) _, ha,
          rootDiagUnit_conj_pinnedX a hrootγ c, hchar' (-Pi.single i 1)]
    intro y
    exact DFunLike.congr_fun hfg y
  refine ⟨T, ht_tg, hmain, ?_⟩
  intro δ
  have hroot : rootChar (τ := Tag.E7) a' δ = rootChar (τ := τ) a (F.j δ) := hchar' δ
  calc rckRootVal (T : ModGL Tag.E7 GGL) δ = rootChar (τ := Tag.E7) a' δ := by
        rw [show (T : ModGL Tag.E7 GGL) = rootDiagUnit Tag.E7 a' from rfl, rckRootVal, hcoord']
        rfl
    _ = rootChar (τ := τ) a (F.j δ) := hroot
    _ = rckRootVal b (F.j δ) := by
        rw [rckRootVal, hcoord]
        rfl

theorem rckE7_torusClause
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ) (SK : LangSetup Tag.E7 GGL 5)
    (hsurj : (adjointGroup Tag.E7 GGL).map SK.D.step = adjointGroup Tag.E7 GGL)
    (htr : ∀ y : adjointGroup Tag.E7 GGL, ∃ hy : SK.D.step y ∈ adjointGroup Tag.E7 GGL,
      (F.ε ⟨SK.D.step y, hy⟩ : ModGL τ GGL) = S.D.step (F.ε y))
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) :
    ∀ b ∈ S.D.torus, ∃ t ∈ SK.D.torus,
      (∀ (x : ↥R) (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ R),
        rckE7Kappa F hR ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * rckE7Kappa F hR x * t⁻¹) ∧
      ∀ γ ∈ Ψ, rckRootVal t (F.ι γ) = rckRootVal b γ := by
  intro b hb
  have hbH : b ∈ torusGroup τ GGL :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
  have hbF : S.D.step b = b :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).2
  obtain ⟨t0, ht_tg, htrans, hroot⟩ := exists_rckE7_torus_transfer F hbH
  have hstep_adj : SK.D.step (t0 : ModGL Tag.E7 GGL) ∈ adjointGroup Tag.E7 GGL := by
    have h : SK.D.step (t0 : ModGL Tag.E7 GGL) ∈
        (adjointGroup Tag.E7 GGL).map SK.D.step := ⟨t0, t0.2, rfl⟩
    rwa [hsurj] at h
  let tstep : adjointGroup Tag.E7 GGL :=
    ⟨SK.D.step (t0 : ModGL Tag.E7 GGL), hstep_adj⟩
  have hsurj' : ∀ w : adjointGroup Tag.E7 GGL, ∃ y : adjointGroup Tag.E7 GGL,
      SK.D.step (y : ModGL Tag.E7 GGL) = (w : ModGL Tag.E7 GGL) := by
    intro w
    have hw : (w : ModGL Tag.E7 GGL) ∈
        (adjointGroup Tag.E7 GGL).map SK.D.step := by
      rw [hsurj]
      exact w.2
    obtain ⟨y, hy, hyw⟩ := hw
    exact ⟨⟨y, hy⟩, hyw⟩
  have hconj_all : ∀ w : adjointGroup Tag.E7 GGL,
      t0 * w * t0⁻¹ = tstep * w * tstep⁻¹ := by
    intro w
    obtain ⟨y, hyw⟩ := hsurj' w
    obtain ⟨hy, hεy⟩ := htr y
    have hεw : (F.ε w : ModGL τ GGL) = S.D.step (F.ε y) := by
      have hsub : (⟨SK.D.step (y : ModGL Tag.E7 GGL), hy⟩ : adjointGroup Tag.E7 GGL) = w :=
        Subtype.ext hyw
      rw [← hsub]
      exact hεy
    have h1 : (F.ε (t0 * w * t0⁻¹) : ModGL τ GGL) =
        b * (F.ε w : ModGL τ GGL) * b⁻¹ := htrans w
    have h2 : b * (F.ε w : ModGL τ GGL) * b⁻¹ =
        S.D.step (b * (F.ε y : ModGL τ GGL) * b⁻¹) := by
      rw [map_mul, map_mul, map_inv, hbF, ← hεw]
    have h3 : b * (F.ε y : ModGL τ GGL) * b⁻¹ =
        (F.ε (t0 * y * t0⁻¹) : ModGL τ GGL) := (htrans y).symm
    obtain ⟨hz, hεz⟩ := htr (t0 * y * t0⁻¹)
    have hstep_eq : SK.D.step ((t0 * y * t0⁻¹ : adjointGroup Tag.E7 GGL) :
        ModGL Tag.E7 GGL) = ((tstep * w * tstep⁻¹ : adjointGroup Tag.E7 GGL) :
          ModGL Tag.E7 GGL) := by
      change SK.D.step ((t0 : ModGL Tag.E7 GGL) * (y : ModGL Tag.E7 GGL) *
        (t0 : ModGL Tag.E7 GGL)⁻¹) = _
      rw [map_mul, map_mul, map_inv, hyw]
      rfl
    have hsubz : (⟨SK.D.step ((t0 * y * t0⁻¹ : adjointGroup Tag.E7 GGL) :
          ModGL Tag.E7 GGL), hz⟩ : adjointGroup Tag.E7 GGL) = tstep * w * tstep⁻¹ :=
      Subtype.ext hstep_eq
    apply F.ε.injective
    apply Subtype.ext
    calc (F.ε (t0 * w * t0⁻¹) : ModGL τ GGL)
        = b * (F.ε w : ModGL τ GGL) * b⁻¹ := h1
      _ = S.D.step (b * (F.ε y : ModGL τ GGL) * b⁻¹) := h2
      _ = S.D.step (F.ε (t0 * y * t0⁻¹)) := by rw [h3]
      _ = (F.ε ⟨SK.D.step ((t0 * y * t0⁻¹ : adjointGroup Tag.E7 GGL) :
            ModGL Tag.E7 GGL), hz⟩ : ModGL τ GGL) := hεz.symm
      _ = (F.ε (tstep * w * tstep⁻¹) : ModGL τ GGL) := by rw [hsubz]
  have hcenter : tstep⁻¹ * t0 ∈ Subgroup.center (adjointGroup Tag.E7 GGL) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have hw := congrArg (fun q : adjointGroup Tag.E7 GGL =>
      tstep⁻¹ * q * t0) (hconj_all w)
    simpa [mul_assoc] using hw.symm
  have hz : tstep⁻¹ * t0 = 1 := by
    have hbot : tstep⁻¹ * t0 ∈ (⊥ : Subgroup (adjointGroup Tag.E7 GGL)) := by
      rw [← CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E7 GGL]
      exact hcenter
    simpa using hbot
  have htfix : SK.D.step (t0 : ModGL Tag.E7 GGL) = (t0 : ModGL Tag.E7 GGL) := by
    have h : t0 = tstep := by
      calc t0 = tstep * (tstep⁻¹ * t0) := by group
        _ = tstep * 1 := by rw [hz]
        _ = tstep := mul_one _
    exact (congrArg Subtype.val h).symm
  have ht_torus : (t0 : ModGL Tag.E7 GGL) ∈ SK.D.torus := by
    refine CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨ht_tg, ?_⟩
    simpa [LangDatum.step, MulAut.conj_apply] using htfix
  refine ⟨(t0 : ModGL Tag.E7 GGL), ht_torus, ?_, ?_⟩
  · intro x hx
    let y : adjointGroup Tag.E7 GGL := F.ε.symm (Subgroup.inclusion hR x)
    have hyε : F.ε y = Subgroup.inclusion hR x := MulEquiv.apply_symm_apply F.ε _
    have hε : F.ε (t0 * y * t0⁻¹) =
        Subgroup.inclusion hR ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ := by
      apply Subtype.ext
      rw [htrans y, hyε]
      rfl
    have hEq : F.ε.symm (Subgroup.inclusion hR ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩) =
        t0 * F.ε.symm (Subgroup.inclusion hR x) * t0⁻¹ := by
      apply F.ε.injective
      rw [MulEquiv.apply_symm_apply]
      exact hε.symm
    have hval := congrArg Subtype.val hEq
    rw [rckE7Kappa_apply, rckE7Kappa_apply]
    simpa using hval
  · intro γ hγ
    rw [hroot (F.ι γ), F.j_ι γ hγ]

theorem rckE7_psiInnerDiag {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    (SK : LangSetup Tag.E7 GGL 5) {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ)
    (hrange : (rckE7Kappa F hR).range = SK.Γ)
    (hodd : ∀ x ∈ SK.D.model, (∃ N : ℕ, Odd N ∧ x ^ N = 1) → x ∈ SK.Γ)
    {b : ModGL τ GGL} (hbR : ∀ x ∈ R, b * x * b⁻¹ ∈ R)
    {t : ModGL Tag.E7 GGL} (ht : t ∈ SK.D.torus)
    (hconj : ∀ (x : ↥R) (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ R),
      rckE7Kappa F hR ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * rckE7Kappa F hR x * t⁻¹)
    (M : LieUniversal) (φ : M.K →* ↥R) (hφ : Function.Surjective φ) :
    GGPsiInnerDiag M.D (R.subtype.comp φ) b := by
  have ht_tg : t ∈ torusGroup Tag.E7 GGL :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht).1
  have ht_fix : SK.D.step t = t :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht).2
  have ht_model : t ∈ SK.D.model :=
    ⟨CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup ht_tg, ht_fix⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht_tg
  obtain ⟨N, hNodd, hNa⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e.exists_odd_pow_eq_one
      (K := ZMod 2) (L := GGL) (by rw [ZMod.ringChar_zmod_n]) a
  have ht_pow : t ^ N = 1 := by
    rw [ha]
    have hmap : rootDiagUnit Tag.E7 a ^ N = rootDiagUnit Tag.E7 (a ^ N) :=
      ((rootDiagUnitHom Tag.E7 GGL).map_pow a N).symm
    rw [hmap]
    have hpow : a ^ N = 1 := funext fun i => hNa i
    rw [hpow, rootDiagUnit_one]
  have htΓ : t ∈ SK.Γ := hodd t ht_model ⟨N, hNodd, ht_pow⟩
  have ht_range : t ∈ (rckE7Kappa F hR).range := by rw [hrange]; exact htΓ
  obtain ⟨r, hr⟩ := ht_range
  have hconjR : ∀ (x : ↥R) (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ R),
      (⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ : ↥R) = r * x * r⁻¹ := by
    intro x hx
    apply rckE7Kappa_injective F hR
    rw [hconj x hx, ← hr, map_mul, map_mul, map_inv]
  obtain ⟨g0, hg0⟩ := hφ (r⁻¹ : ↥R)
  refine ⟨(r⁻¹ : ↥R), ⟨g0, ?_⟩, ?_⟩
  · simp only [MonoidHom.comp_apply]
    rw [hg0]
    rfl
  · intro γ hγ
    refine ⟨1, one_mem _, ?_⟩
    intro z hz
    let w : ↥R := φ z
    have hbw : ∀ x ∈ R, b * x * b⁻¹ =
        (r : ModGL τ GGL) * x * (r : ModGL τ GGL)⁻¹ := by
      intro x hx
      have h := congrArg Subtype.val (hconjR ⟨x, hx⟩ (hbR x hx))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    let c : ModGL τ GGL := (r : ModGL τ GGL)⁻¹ * b
    have hc : ∀ x ∈ R, c * x * c⁻¹ = x := by
      intro x hx
      calc c * x * c⁻¹
          = (r : ModGL τ GGL)⁻¹ * b * x * b⁻¹ * (r : ModGL τ GGL) := by rfl
        _ = (r : ModGL τ GGL)⁻¹ * (b * x * b⁻¹) * (r : ModGL τ GGL) := by group
        _ = (r : ModGL τ GGL)⁻¹ *
              ((r : ModGL τ GGL) * x * (r : ModGL τ GGL)⁻¹) *
              (r : ModGL τ GGL) := by rw [hbw x hx]
        _ = x := by group
    have hcr : c * (r : ModGL τ GGL) = (r : ModGL τ GGL) * c := by
      calc c * (r : ModGL τ GGL) = (c * (r : ModGL τ GGL) * c⁻¹) * c := by group
        _ = (r : ModGL τ GGL) * c := by rw [hc (r : ModGL τ GGL) r.2]
    have hcr' : c * (r : ModGL τ GGL)⁻¹ = (r : ModGL τ GGL)⁻¹ * c := by
      calc c * (r : ModGL τ GGL)⁻¹
          = ((r : ModGL τ GGL)⁻¹ * (r : ModGL τ GGL)) * c *
              (r : ModGL τ GGL)⁻¹ := by group
        _ = (r : ModGL τ GGL)⁻¹ * ((r : ModGL τ GGL) * c) *
              (r : ModGL τ GGL)⁻¹ := by group
        _ = (r : ModGL τ GGL)⁻¹ * (c * (r : ModGL τ GGL)) *
              (r : ModGL τ GGL)⁻¹ := by rw [← hcr]
        _ = (r : ModGL τ GGL)⁻¹ * c := by group
    have hbr : b * (r : ModGL τ GGL)⁻¹ = c := by
      calc b * (r : ModGL τ GGL)⁻¹
          = ((r : ModGL τ GGL) * c) * (r : ModGL τ GGL)⁻¹ := by
              rw [show (r : ModGL τ GGL) * c = b from by
                change (r : ModGL τ GGL) * ((r : ModGL τ GGL)⁻¹ * b) = b
                group]
        _ = (r : ModGL τ GGL) * (c * (r : ModGL τ GGL)⁻¹) := by group
        _ = (r : ModGL τ GGL) * ((r : ModGL τ GGL)⁻¹ * c) := by rw [hcr']
        _ = c := by group
    have hcalc : (b * (r : ModGL τ GGL)⁻¹)⁻¹ * (w : ModGL τ GGL) *
        (b * (r : ModGL τ GGL)⁻¹) = (w : ModGL τ GGL) := by
      rw [hbr]
      have h := hc (w : ModGL τ GGL) w.2
      have h' : c⁻¹ * (w : ModGL τ GGL) * c = (w : ModGL τ GGL) := by
        have := congrArg (fun q : ModGL τ GGL => c⁻¹ * q * c) h
        simpa [mul_assoc] using this.symm
      exact h'
    simpa [w, MonoidHom.comp_apply] using hcalc

end CFSG.StandardType.RCKRP

end
