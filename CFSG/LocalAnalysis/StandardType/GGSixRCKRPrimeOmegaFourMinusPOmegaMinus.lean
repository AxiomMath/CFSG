module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDPlane
public import Mathlib.LinearAlgebra.Projection

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem exists_liftHom_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (B : Subgroup X) [IsMulCommutative ↥B]
    (hB : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b) :
    ∃ ℓ : ↥B →* ↥(spinGroup (Spin.quadMinus n F bq cq)),
      ∀ (b : ↥B) (u : ↥(spinGroup (Spin.quadMinus n F bq cq))),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹) := by
  classical
  have hchoose : ∀ b : ↥B, ∃ s : ↥(spinGroup (Spin.quadMinus n F bq cq)),
      ∀ u : ↥(spinGroup (Spin.quadMinus n F bq cq)),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (s * u * s⁻¹) :=
    fun b => exists_conj_eq_POmegaMinus n hirr hn ψ hψ (hB b b.2)
  let ℓ₀ : ↥B → ↥(spinGroup (Spin.quadMinus n F bq cq)) := fun b => Classical.choose (hchoose b)
  have hℓ₀ : ∀ (b : ↥B) (u : ↥(spinGroup (Spin.quadMinus n F bq cq))),
      (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ₀ b * u * (ℓ₀ b)⁻¹) :=
    fun b => Classical.choose_spec (hchoose b)
  have hone : ℓ₀ 1 = 1 := by
    apply conj_eq_unique_POmegaMinus n hirr hn ψ hψ (s' := 1)
    intro u
    rw [← hℓ₀ 1 u]
    simp
  have hmul : ∀ b b' : ↥B, ℓ₀ (b * b') = ℓ₀ b * ℓ₀ b' := by
    intro b b'
    have hanti : ℓ₀ (b' * b) = ℓ₀ b * ℓ₀ b' := by
      apply conj_eq_unique_POmegaMinus n hirr hn ψ hψ (s' := ℓ₀ b * ℓ₀ b')
      intro u
      calc ψ (ℓ₀ (b' * b) * u * (ℓ₀ (b' * b))⁻¹)
          = (↑(b' * b) : X)⁻¹ * ψ u * (↑(b' * b) : X) := (hℓ₀ (b' * b) u).symm
        _ = (b : X)⁻¹ * ((b' : X)⁻¹ * ψ u * (b' : X)) * (b : X) := by
              rw [Subgroup.coe_mul]; group
        _ = (b : X)⁻¹ * ψ (ℓ₀ b' * u * (ℓ₀ b')⁻¹) * (b : X) := by rw [hℓ₀ b' u]
        _ = ψ (ℓ₀ b * (ℓ₀ b' * u * (ℓ₀ b')⁻¹) * (ℓ₀ b)⁻¹) := by
              rw [hℓ₀ b (ℓ₀ b' * u * (ℓ₀ b')⁻¹)]
        _ = ψ ((ℓ₀ b * ℓ₀ b') * u * (ℓ₀ b * ℓ₀ b')⁻¹) := by congr 1; group
    calc ℓ₀ (b * b') = ℓ₀ (b' * b) := by
          rw [isMulCommutative_iff.mp inferInstance b b']
      _ = ℓ₀ b * ℓ₀ b' := hanti
  exact ⟨{ toFun := ℓ₀, map_one' := hone, map_mul' := hmul }, hℓ₀⟩

theorem rckF_POmegaMinus_not_omegaFourMinus
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J B : Subgroup X}
    {d : X} (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (φ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hφk : φ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) φ b)
    (s : ↥(spinGroup (Spin.quadMinus n F bq cq))) (hs : ∀ u, d⁻¹ * φ u * d = φ (s * u * s⁻¹))
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (he : IsPrimIdemIn
      (Algebra.adjoin F
        (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    (hadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) ε = ε)
    (hm4 : ε.rank = 4 ∧ ∀ x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      ε.mulVec x = x → ε.mulVec y = y → Spin.quadMinus n F bq cq x = 0 →
      Spin.quadMinus n F bq cq y = 0 →
      QuadraticMap.polar (Spin.quadMinus n F bq cq) x y = 0 →
      ¬ LinearIndependent F ![x, y])
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hJe : J' ≤ (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
      {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε :
        Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))))
    (hJmap : J'.map φ = J) : False := by
  classical
  let V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F
  let Q : QuadraticForm F V := Spin.quadMinus n F bq cq
  let U' : Type := ↥(spinGroup (Spin.quadMinus n F bq cq))
  let ψ : U' →* X := φ
  let sS : U' := s
  let toS : ↥(spinGroup (Spin.quadMinus n F bq cq)) → U' := fun u => u
  have hψk : ψ.ker ≤ Subgroup.center U' := hφk
  have hsS : ∀ u : U', d⁻¹ * ψ u * d = ψ (sS * u * sS⁻¹) := hs
  have hdiag' : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b :=
    fun b hb => hdiag b hb
  have hjinj : Function.Injective (Spin.spinMatrix Q) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2)
  have : IsMulCommutative ↥B := hBab.1
  obtain ⟨ℓ, hℓ⟩ := exists_liftHom_POmegaMinus n hirr hn ψ hψk B hdiag'
  have hℓd : ℓ ⟨d, hdB⟩ = sS := by
    apply conj_eq_unique_POmegaMinus n hirr hn ψ hψk (s' := sS)
    intro u
    rw [← hℓ ⟨d, hdB⟩ u]
    exact hsS u
  have hcommℓ : ∀ b : ↥B, Commute (ℓ b) sS := by
    intro b
    have hbd : Commute (b : X) d := by
      have h := isMulCommutative_iff.mp hBab.1 b ⟨d, hdB⟩
      exact congrArg Subtype.val h
    have h' := conj_eq_commute_POmegaMinus n hirr hn ψ hψk hbd (hℓ b)
      (hℓ ⟨d, hdB⟩)
    rwa [hℓd] at h'
  have hcommM : ∀ b : ↥B,
      Commute ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
        ((Spin.spinMatrix Q sS : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := by
    intro b
    have h1 : Spin.spinMatrix Q (ℓ b) * Spin.spinMatrix Q sS =
        Spin.spinMatrix Q sS * Spin.spinMatrix Q (ℓ b) := by
      rw [← map_mul (Spin.spinMatrix Q) (ℓ b) sS,
        ← map_mul (Spin.spinMatrix Q) sS (ℓ b), (hcommℓ b).eq]
    exact congrArg Units.val h1
  have hmemε : ε ∈ Algebra.adjoin F
      {((Spin.spinMatrix Q sS : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)} := by
    have h := he.1
    rw [Set.image_singleton] at h
    exact h
  have hcommε : ∀ b : ↥B,
      Commute ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ε :=
    fun b => Algebra.commute_of_mem_adjoin_singleton_of_commute hmemε (hcommM b)
  let W : Submodule F V := LinearMap.range (Matrix.mulVecLin ε)
  have hidem : IsIdempotentElem (Matrix.mulVecLin ε) := by
    rw [isIdempotentElem_iff]
    apply LinearMap.ext
    intro v
    change Matrix.mulVecLin ε (Matrix.mulVecLin ε v) = Matrix.mulVecLin ε v
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  have hWmem : ∀ x : V, x ∈ W ↔ ε.mulVec x = x := by
    intro x
    simpa only [W, Matrix.mulVecLin_apply] using
      (LinearMap.IsIdempotentElem.mem_range_iff (p := Matrix.mulVecLin ε) hidem (x := x))
  have hdimW : Module.finrank F W = 4 := by
    simpa only [W, Matrix.rank] using hm4.1
  have hGdet : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det :=
    CFSG.StandardType.ClassicalPosition.Geo.isUnit_det_toMatrix₂'_polarBilin Q
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr)
  have hself : ∀ x y : V, QuadraticMap.polar Q (ε.mulVec x) y =
      QuadraticMap.polar Q x (ε.mulVec y) := by
    intro x y
    rw [CFSG.StandardType.ClassicalPosition.Geo.polar_mulVec_eq_polar_formAdj_mulVec Q hGdet ε x y,
      hadj]
  have hcompl : IsCompl W (LinearMap.ker (Matrix.mulVecLin ε)) :=
    LinearMap.IsIdempotentElem.isCompl hidem
  have horth : ∀ u ∈ W, ∀ w ∈ LinearMap.ker (Matrix.mulVecLin ε),
      QuadraticMap.polar Q u w = 0 := by
    intro u hu w hw
    have hu' : ε.mulVec u = u := (hWmem u).mp hu
    have hw' : ε.mulVec w = 0 := by
      have h := hw
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
      exact h
    rw [← hu', hself, hw', QuadraticMap.polar_zero_right]
  have hreg : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype
      (Q := Q) (W := W) (W' := LinearMap.ker (Matrix.mulVecLin ε))
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr) hcompl horth
  have hV : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype) := by
    rintro ⟨W', hW'dim, hW'sing⟩
    have hdim' : Module.finrank F W' = 2 := by omega
    have hne : W' ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim'
      omega
    obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let x' : ↥W' := ⟨x, hxW'⟩
    have hx'0 : x' ≠ 0 := by
      intro h
      exact hx0 (congrArg Subtype.val h)
    obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank
      (R := F) (M := ↥W') (x := x') (by omega : 1 < Module.finrank F W') hx'0
    have hindW : LinearIndependent F ![(x' : W), (y : W)] := by
      have h := hxy.map' W'.subtype (by simp)
      convert h using 1
      ext i
      fin_cases i <;> rfl
    have hindV : LinearIndependent F ![((x' : W) : V), ((y : W) : V)] := by
      have h := hindW.map' W.subtype (by simp)
      convert h using 1
      ext i
      fin_cases i <;> rfl
    have hQx : Q ((x' : W) : V) = 0 := by simpa using hW'sing x' x'.2
    have hQy : Q ((y : W) : V) = 0 := by simpa using hW'sing y y.2
    have hWx : ε.mulVec ((x' : W) : V) = ((x' : W) : V) := (hWmem _).mp (x' : W).2
    have hWy : ε.mulVec ((y : W) : V) = ((y : W) : V) := (hWmem _).mp (y : W).2
    have hQxy : Q (((x' : W) : V) + ((y : W) : V)) = 0 := by
      have hmem : (x' : W) + (y : W) ∈ W' := W'.add_mem x'.2 y.2
      simpa using hW'sing ((x' : W) + (y : W)) hmem
    have hpol : QuadraticMap.polar Q ((x' : W) : V) ((y : W) : V) = 0 := by
      have h := QuadraticMap.map_add Q ((x' : W) : V) ((y : W) : V)
      rw [hQx, hQy, hQxy, zero_add, zero_add] at h
      exact h.symm
    exact (hm4.2 ((x' : W) : V) ((y : W) : V) hWx hWy hQx hQy hpol) hindV
  let actℓ : ↥B →* (V ≃ₗ[F] V) := (Spin.spinAction Q).comp ℓ
  let T₀ : Subgroup (V ≃ₗ[F] V) := actℓ.range
  have hpres : ∀ g ∈ T₀, ∀ s ∈ W, g s ∈ W := by
    rintro g ⟨b, rfl⟩ s hs
    change (Spin.spinAction Q (ℓ b)) s ∈ W
    rw [hWmem ((Spin.spinAction Q (ℓ b)) s), ← Spin.spinMatrix_mulVec,
      Matrix.mulVec_mulVec, (hcommε b).eq.symm, ← Matrix.mulVec_mulVec, (hWmem s).mp hs]
  let ρ : ↥B →* (W ≃ₗ[F] W) :=
    (CFSG.StandardType.OrthRestOdd.resHom T₀ W hpres).comp actℓ.rangeRestrict
  let T : Subgroup (W ≃ₗ[F] W) := ρ.range
  have hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
    rintro _ ⟨b, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun s => ?_
    change Q (((ρ b) s : W) : V) = Q (s : V)
    have h2 : (((ρ b) s : W) : V) = (Spin.spinAction Q (ℓ b)) (s : V) := by
      change ((CFSG.StandardType.OrthRestOdd.resHom T₀ W hpres
        (actℓ.rangeRestrict b)) s : V) = (Spin.spinAction Q (ℓ b)) (s : V)
      rw [CFSG.StandardType.OrthRestOdd.resHom_apply]
      rfl
    rw [h2, Spin.map_spinAction]
  have hTc : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← map_mul ρ b b', ← map_mul ρ b' b]
    exact congrArg ρ (isMulCommutative_iff.mp hBab.1 b b')
  have hTp : ∀ g ∈ T, g ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow ρ b p]
    have hbp : b ^ p = 1 := Subtype.ext (by simpa using hBab.2 b b.2)
    rw [hbp, map_one]
  have hcardrange : Nat.card T ≤ p :=
    CFSG.StandardType.SmallOrthUn.card_le_of_four_minus hreg hdimW hV hp hp2 T hTO hTc hTp
  have hkermap : ρ.ker.map B.subtype ≤ B ⊓ Subgroup.centralizer (J : Set X) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb1 : ρ b = 1 := MonoidHom.mem_ker.mp hb
    have hfixW : ∀ s : W, (Spin.spinAction Q (ℓ b)) (s : V) = (s : V) := by
      intro s
      have h1 : (ρ b) s = s := by rw [hb1]; rfl
      have h2 : (((ρ b) s : W) : V) = (Spin.spinAction Q (ℓ b)) (s : V) := by
        change ((CFSG.StandardType.OrthRestOdd.resHom T₀ W hpres
          (actℓ.rangeRestrict b)) s : V) = (Spin.spinAction Q (ℓ b)) (s : V)
        rw [CFSG.StandardType.OrthRestOdd.resHom_apply]
        rfl
      calc (Spin.spinAction Q (ℓ b)) (s : V) = (((ρ b) s : W) : V) := h2.symm
        _ = (s : V) := congrArg Subtype.val h1
    have hMε : ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          ε = ε := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
        Spin.spinMatrix_mulVec]
      exact hfixW ⟨ε.mulVec v, ⟨v, rfl⟩⟩
    have hkey : ∀ u ∈ J', ℓ b * toS u = toS u * ℓ b := by
      intro u hu
      have hmem : Spin.spinMatrix Q u ∈ (Subgroup.centralizer {Spin.spinMatrix Q s} ⊓
          glFixing (1 - ε) : Subgroup (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) := hJe hu
      have hcomm : Commute (Spin.spinMatrix Q u) (Spin.spinMatrix Q s) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).1
      have hMu1e : ((Spin.spinMatrix Q u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          (1 - ε) = 1 - ε := (Subgroup.mem_inf.mp hmem).2
      have hcommuε : Commute ((Spin.spinMatrix Q u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ε :=
        Algebra.commute_of_mem_adjoin_singleton_of_commute hmemε
          (congrArg Units.val hcomm.eq)
      let a : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
        ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : Matrix _ _ F)
      let c : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
        ((Spin.spinMatrix Q u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : Matrix _ _ F)
      let e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F := ε
      have hae : a * e = e := hMε
      have hce : c * e = e * c := hcommuε.eq
      have hc1e : c * (1 - e) = 1 - e := hMu1e
      have hcomm_ae : Commute a e := hcommε b
      have hea : e * a = e := hcomm_ae.eq.symm.trans hae
      have ha1e : a * (1 - e) = (1 - e) * a :=
        ((Commute.one_right a).sub_right hcomm_ae).eq
      have h1a : a * (1 - e) = a - e := by rw [mul_sub, mul_one, hae]
      have h1c : (1 - e) * a = a - e := by rw [sub_mul, one_mul, hea]
      have hca : c * a = e * c + (a - e) := by
        calc c * a
            = c * (a * e + a * (1 - e)) := by
                rw [← mul_add, show e + (1 - e) = 1 by abel, mul_one]
          _ = c * (a * e) + c * (a * (1 - e)) := by rw [mul_add]
          _ = c * e + c * ((1 - e) * a) := by rw [hae, ha1e]
          _ = c * e + (c * (1 - e)) * a := by rw [mul_assoc]
          _ = c * e + (1 - e) * a := by rw [hc1e]
          _ = e * c + (a - e) := by rw [hce, h1c]
      have hac : a * c = c * a := by
        calc a * c
            = a * c * (e + (1 - e)) := by
                rw [show e + (1 - e) = 1 by abel, mul_one]
          _ = a * c * e + a * c * (1 - e) := by rw [mul_add]
          _ = a * (c * e) + a * (c * (1 - e)) := by simp only [mul_assoc]
          _ = a * (e * c) + a * (1 - e) := by rw [hce, hc1e]
          _ = (a * e) * c + a * (1 - e) := by rw [mul_assoc]
          _ = e * c + (a - e) := by rw [hae, h1a]
          _ = c * a := by rw [hca]
      have hfinal : ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          ((Spin.spinMatrix Q u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
          ((Spin.spinMatrix Q u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          ((Spin.spinMatrix Q (ℓ b) : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := hac
      apply hjinj
      apply Units.ext
      rw [map_mul (Spin.spinMatrix Q) (ℓ b) (toS u),
        map_mul (Spin.spinMatrix Q) (toS u) (ℓ b), Units.val_mul, Units.val_mul]
      exact hfinal
    refine ⟨b.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [← hJmap] at hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
    have hconj : (b : X)⁻¹ * ψ (toS u) * (b : X) = ψ (toS u) := by
      rw [hℓ b (toS u), hkey u hu]
      congr 1
      group
    change ψ (toS u) * (b : X) = (b : X) * ψ (toS u)
    calc ψ (toS u) * (b : X) = (b : X) * ((b : X)⁻¹ * ψ (toS u) * (b : X)) := by group
      _ = (b : X) * ψ (toS u) := by rw [hconj]
  have hcardker : Nat.card ρ.ker ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := by
    have hmap : Nat.card (ρ.ker.map B.subtype) = Nat.card ρ.ker :=
      Subgroup.card_map_of_injective B.subtype_injective
    rw [← hmap]
    exact Subgroup.card_le_of_le hkermap
  have h1 : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) * p := by
    calc p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X))
        ≤ Nat.card B := hrank
      _ = Nat.card ↥B := rfl
      _ = Nat.card ρ.ker * Nat.card ρ.range := (Subgroup.card_ker_mul_card_range ρ).symm
      _ ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) * p :=
          Nat.mul_le_mul hcardker hcardrange
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := Nat.card_pos
  have h2 : p ^ 2 ≤ p := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [Nat.mul_comm (Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X))) p] at h1
    exact h1
  have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
  exact (not_le.mpr h3) h2

end CFSG.StandardType.RCKRP
