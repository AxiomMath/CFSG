module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDPlane
public import Mathlib.LinearAlgebra.Projection

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckF_POmegaPlus_not_omegaFourMinus
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J B : Subgroup X}
    {d : X} (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    {k f : ℕ} (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaPlus (k + 3) f).D φ b)
    (s : (ggU .POmegaPlus (k + 3) f).K) (hs : ∀ u, d⁻¹ * φ u * d = φ (s * u * s⁻¹))
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s})) ε)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ε = ε)
    (hm4 : ε.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      ε.mulVec x = x → ε.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y])
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : J' ≤ (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
      {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K))
    (hJmap : J'.map φ = J) : False := by
  classical
  let F := GaloisField 2 f
  let V := Fin (k + 3) ⊕ Fin (k + 3) → F
  let Q : QuadraticForm F V := Spin.quadPlus (k + 3) F
  let U' : Type := ↥(spinGroup (Spin.quadPlus (k + 3) F))
  let ψ : U' →* X := φ
  let sS : U' := s
  let toS : (ggU .POmegaPlus (k + 3) f).K → U' := fun u => u
  have hψk : ψ.ker ≤ Subgroup.center U' := hφk
  have hsS : ∀ u : U', d⁻¹ * ψ u * d = ψ (sS * u * sS⁻¹) := hs
  have hdiag' : ∀ b ∈ B, GGPsiInnerDiag (Spin.plusDatum (k + 3) F (by omega)) ψ b :=
    fun b hb => hdiag b hb
  have hjinj : Function.Injective (Spin.spinMatrix Q) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Spin.ker_spinMatrix_quadPlus_eq_bot (n := k + 3) (K := F)
      (CharP.cast_eq_zero F 2)
  have : IsMulCommutative ↥B := hBab.1
  obtain ⟨ℓ, hℓ⟩ := exists_liftHom_POmegaPlus (k + 3) F (by omega) ψ hψk B hdiag'
  have hℓd : ℓ ⟨d, hdB⟩ = sS := by
    apply conj_eq_unique_POmegaPlus (k + 3) F (by omega) ψ hψk (s' := sS)
    intro u
    rw [← hℓ ⟨d, hdB⟩ u]
    exact hsS u
  have hcommℓ : ∀ b : ↥B, Commute (ℓ b) sS := by
    intro b
    have hbd : Commute (b : X) d := by
      have h := isMulCommutative_iff.mp hBab.1 b ⟨d, hdB⟩
      exact congrArg Subtype.val h
    have h' := conj_eq_commute_POmegaPlus (k + 3) F (by omega) ψ hψk hbd (hℓ b)
      (hℓ ⟨d, hdB⟩)
    rwa [hℓd] at h'
  have hcommM : ∀ b : ↥B,
      Commute ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F)
        ((Spin.spinMatrix Q sS : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) := by
    intro b
    have h1 : Spin.spinMatrix Q (ℓ b) * Spin.spinMatrix Q sS =
        Spin.spinMatrix Q sS * Spin.spinMatrix Q (ℓ b) := by
      rw [← map_mul (Spin.spinMatrix Q) (ℓ b) sS,
        ← map_mul (Spin.spinMatrix Q) sS (ℓ b), (hcommℓ b).eq]
    exact congrArg Units.val h1
  have hmemε : ε ∈ Algebra.adjoin F
      {((Spin.spinMatrix Q sS : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F)} := by
    have h := he.1
    rw [Set.image_singleton] at h
    exact h
  have hcommε : ∀ b : ↥B,
      Commute ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) ε :=
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
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) F)
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
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) F) hcompl horth
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
    have hMε : ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) * ε = ε := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
        Spin.spinMatrix_mulVec]
      exact hfixW ⟨ε.mulVec v, ⟨v, rfl⟩⟩
    have hkey : ∀ u ∈ J', ℓ b * toS u = toS u * ℓ b := by
      intro u hu
      have hmem : Spin.spinMatrix Q u ∈ (Subgroup.centralizer {Spin.spinMatrix Q s} ⊓
          glFixing (1 - ε) : Subgroup (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)) := hJe hu
      have hcomm : Commute (Spin.spinMatrix Q u) (Spin.spinMatrix Q s) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).1
      have hMu1e : ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) *
          (1 - ε) = 1 - ε := (Subgroup.mem_inf.mp hmem).2
      have hcommuε : Commute ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) ε :=
        Algebra.commute_of_mem_adjoin_singleton_of_commute hmemε
          (congrArg Units.val hcomm.eq)
      let a : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F :=
        ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) : Matrix _ _ F)
      let c : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F :=
        ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) : Matrix _ _ F)
      let e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F := ε
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
      have hfinal : ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) *
          ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) =
          ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) *
          ((Spin.spinMatrix Q (ℓ b) : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) := hac
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
