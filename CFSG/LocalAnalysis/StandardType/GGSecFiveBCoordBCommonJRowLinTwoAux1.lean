module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentFrame
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGLinTwoCent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9C1Lin
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreStd
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveLift
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthSymp
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import Certificates.Certificate41501

public section

namespace CFSG.StandardType.CommonJRowLinTwo

open CFSG.Assembly
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf
open CFSG.StandardType.SlNsRootGen
open Matrix

noncomputable abbrev ggCommonJRowLinTwo_torus {d m : ℕ}
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) :
    Multiplicative (Fin m → ZMod 3) →* Matrix.SpecialLinearGroup (Fin d) F2 :=
  torusSL (K := F2) (g := phi3) (n := d) (s := m) (r := d - 2 * m) (p := 3)
    ε det_rootMat_phi3 rootMat_phi3_pow_three

theorem ggCommonJRowLinTwo_hτ {d m : ℕ}
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) :
    Function.Injective (ggCommonJRowLinTwo_torus ε) := by
  unfold ggCommonJRowLinTwo_torus torusSL
  refine CoordSL.frameHom_injective (ψ := MonoidHom.id _) (A₀ := 1) (ε := ε)
    (C := rootMat phi3) (hC := det_rootMat_phi3) (hCp := rootMat_phi3_pow_three) ?_ ?_ ?_
  · intro x hx
    have hx1 : x = 1 := by simpa using (MonoidHom.mem_ker.mp hx)
    rw [hx1]
    exact Subgroup.one_mem _
  · exact CoordSL.rootPB_dim_pos phi3
  · intro j hj c
    have hnsplit : ¬ 3 ∣ Nat.card F2 - 1 := by
      rw [show Nat.card F2 = 2 by
        simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)]
      norm_num
    exact CoordSL.isUnit_rootMat_pow_sub (K := F2) (g := phi3) (ℓ := 3)
      Nat.prime_three hnsplit natCast_three_ne_zero phi3_dvd_cyclotomic j hj c

theorem ggCommonJRowLinTwo_hsc {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (hm : 3 ≤ m)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ m) :
    ∀ c : Matrix.SpecialLinearGroup (Fin d) F2, (∀ e ∈ E, c * e = e * c) → c ∈ E := by
  have hd6 : 6 ≤ d := by omega
  have hdm : d / 2 = m := by omega
  have hcard' : 3 ^ (d / 2) ≤ Nat.card E := by rw [hcard, hdm]
  exact LinTwoGen.cent_le_of_maxRank (K := F2) (by
    simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)) hd6 hE hcard' 


private theorem exists_stdCoords {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (_hm : 3 ≤ m)
    {E : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ m) :
    ∃ Φ : (Fin d → ZMod 2) ≃ₗ[ZMod 2]
        ((Fin m → GaloisField 2 2) × (Fin (d - 2 * m) → ZMod 2)),
      ∀ x : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2),
        x ∈ E ↔ ∃ c : Fin m → GaloisField 2 2, (∀ i, c i ≠ 0) ∧
          ∀ v, Φ (x v) = ((fun i => c i * (Φ v).1 i), (Φ v).2) := by
  classical
  obtain ⟨t, d0, Φ, hΦ⟩ := FrameRoute.P9_C1_linear E hE
  let χ : E → (Fin t → (GaloisField 2 2)ˣ) := fun x =>
    fun i => Units.mk0 ((Classical.choose (hΦ x.1 x.2)) i) (by
      have hc := (Classical.choose_spec (hΦ x.1 x.2)).1 i
      intro h0
      rw [h0] at hc
      simp at hc)
  have hχspec : ∀ (x : E) (v : Fin d → ZMod 2),
      Φ (x.1 v) = ((fun i => (χ x i : GaloisField 2 2) * (Φ v).1 i), (Φ v).2) := by
    intro x v
    have h := (Classical.choose_spec (hΦ x.1 x.2)).2 v
    simpa only [χ, Units.val_mk0] using h
  have hχinj : Function.Injective χ := by
    intro x y hxy
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Φ.injective
    rw [hχspec x v, hχspec y v, hxy]
  have : Fintype E := Fintype.ofFinite E
  have hcard_le : Nat.card E ≤ Nat.card (Fin t → (GaloisField 2 2)ˣ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective χ hχinj
  have hpi : Nat.card (Fin t → (GaloisField 2 2)ˣ) = 3 ^ t := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std.card_units_F4]
  have hmt : m ≤ t := by
    have hle : 3 ^ m ≤ 3 ^ t := by
      rw [← hcard, ← hpi]
      exact hcard_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hdimV : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hdimW : Module.finrank (ZMod 2)
      ((Fin t → GaloisField 2 2) × (Fin d0 → ZMod 2)) = 2 * t + d0 :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std.finrank_block t d0
  have hdt : d = 2 * t + d0 := by
    have h := Φ.finrank_eq
    rw [hdimV, hdimW] at h
    omega
  have ht : t = m := by omega
  have hd0 : d0 = d - 2 * m := by omega
  subst t
  subst d0
  have hχbij : Function.Bijective χ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hχinj, ?_⟩
    have hEcard : Fintype.card E = 3 ^ m := by
      rw [← Nat.card_eq_fintype_card, hcard]
    have hCcard : Fintype.card (Fin m → (GaloisField 2 2)ˣ) = 3 ^ m := by
      rw [Fintype.card_fun, Fintype.card_fin]
      have h3 : Fintype.card (GaloisField 2 2)ˣ = 3 := by
        simpa using CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std.card_units_F4
      rw [h3]
    rw [hEcard, hCcard]
  have hχsurj : Function.Surjective χ := hχbij.2
  refine ⟨Φ, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact ⟨fun i => (χ ⟨x, hx⟩ i : GaloisField 2 2), fun i => Units.ne_zero _,
      hχspec ⟨x, hx⟩⟩
  · rintro ⟨c, hc0, hact⟩
    let u : Fin m → (GaloisField 2 2)ˣ := fun i => Units.mk0 (c i) (hc0 i)
    obtain ⟨y, hy⟩ := hχsurj u
    have hyact : ∀ v, Φ (y.1 v) = ((fun i => c i * (Φ v).1 i), (Φ v).2) := by
      intro v
      have h := hχspec y v
      rw [hy] at h
      simpa only [u, Units.val_mk0] using h
    have hxy : x = y.1 := by
      apply LinearEquiv.ext
      intro v
      apply Φ.injective
      rw [hact v, hyact v]
    rw [hxy]
    exact y.2

private theorem exists_conj_of_maxRank {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (hm : 3 ≤ m)
    {E E' : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))}
    (hE : IsElemAbelian 3 E) (hcardE : Nat.card E = 3 ^ m)
    (hE' : IsElemAbelian 3 E') (hcardE' : Nat.card E' = 3 ^ m) :
    ∃ g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2),
      E = E'.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨ΦE, hΦE⟩ := exists_stdCoords hd hm hE hcardE
  obtain ⟨ΦE', hΦE'⟩ := exists_stdCoords hd hm hE' hcardE'
  let g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) := ΦE'.trans ΦE.symm
  have hle : E'.map (MulAut.conj g).toMonoidHom ≤ E := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨c, hc0, hyact⟩ := (hΦE' y).mp hy
    refine (hΦE (g * y * g⁻¹)).mpr ⟨c, hc0, fun v => ?_⟩
    have hcalc : ΦE ((g * y * g⁻¹) v) =
        ((fun i => c i * (ΦE v).1 i), (ΦE v).2) := by
      change ΦE (ΦE.symm (ΦE' (y (ΦE'.symm (ΦE v))))) =
        ((fun i => c i * (ΦE v).1 i), (ΦE v).2)
      rw [LinearEquiv.apply_symm_apply, hyact]
      simp
    exact hcalc
  have hcardmap : Nat.card (E'.map (MulAut.conj g).toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : E'.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardmap, hcardE', hcardE])
  exact ⟨g, heq.symm⟩

private theorem isElemAbelian_torus_range {d m : ℕ}
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) :
    IsElemAbelian 3 (ggCommonJRowLinTwo_torus ε).range := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    obtain ⟨u, hu⟩ := a.2
    obtain ⟨v, hv⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
  · intro x hx
    obtain ⟨u, hu⟩ := hx
    rw [← hu, ← map_pow]
    have hu3 : u ^ 3 = 1 :=
      CFSG.AGLEmbedding.KFactProofs.AlphaFive.pow_eq_one_zmod u
    rw [hu3, map_one]

private theorem card_torus_range {d m : ℕ}
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) :
    Nat.card (ggCommonJRowLinTwo_torus ε).range = 3 ^ m := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (ggCommonJRowLinTwo_hτ ε)).toEquiv]
  simp [ZMod.card]

theorem ggCommonJRowLinTwo_hconj {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (hm : 3 ≤ m)
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m))
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ m) :
    ∃ g : Matrix.SpecialLinearGroup (Fin d) F2,
      E = (ggCommonJRowLinTwo_torus ε).range.map (MulAut.conj g).toMonoidHom := by
  have hF2 : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)
  obtain ⟨σ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2 F2 hF2
  let eSL : Matrix.SpecialLinearGroup (Fin d) F2 ≃*
      Matrix.SpecialLinearGroup (Fin d) (ZMod 2) :=
    CFSG.ClassicalModels.specialLinearFieldEquiv σ (Fin d)
  let eLinZ : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ≃*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    (LinTwoTB.glEquivSL (by norm_num : Nat.card (ZMod 2) = 2)).symm.trans
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin d) (ZMod 2))
  let eLin : Matrix.SpecialLinearGroup (Fin d) F2 ≃*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := eSL.trans eLinZ
  let E_lin : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    E.map eLin.toMonoidHom
  let T_lin : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    (ggCommonJRowLinTwo_torus ε).range.map eLin.toMonoidHom
  have hE_lin : IsElemAbelian 3 E_lin := by
    simpa only [E_lin] using CFSG.Open.IsElemAbelian.map hE eLin.toMonoidHom
  have hcardE_lin : Nat.card E_lin = 3 ^ m := by
    dsimp only [E_lin]
    rw [Subgroup.card_map_of_injective eLin.injective, hcard]
  have hT_lin : IsElemAbelian 3 T_lin := by
    simpa only [T_lin] using
      CFSG.Open.IsElemAbelian.map (isElemAbelian_torus_range ε) eLin.toMonoidHom
  have hcardT_lin : Nat.card T_lin = 3 ^ m := by
    dsimp only [T_lin]
    rw [Subgroup.card_map_of_injective eLin.injective, card_torus_range ε]
  obtain ⟨gLin, hgLin⟩ :=
    exists_conj_of_maxRank hd hm hE_lin hcardE_lin hT_lin hcardT_lin
  refine ⟨eLin.symm gLin, ?_⟩
  have hleft : E_lin.map eLin.symm.toMonoidHom = E := by
    dsimp only [E_lin]
    rw [Subgroup.map_map]
    have hcomp : eLin.symm.toMonoidHom.comp eLin.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hright : (T_lin.map (MulAut.conj gLin).toMonoidHom).map eLin.symm.toMonoidHom =
      (ggCommonJRowLinTwo_torus ε).range.map
        (MulAut.conj (eLin.symm gLin)).toMonoidHom := by
    dsimp only [T_lin]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have hmap := congrArg (Subgroup.map eLin.symm.toMonoidHom) hgLin
  rw [hleft, hright] at hmap
  exact hmap

end CFSG.StandardType.CommonJRowLinTwo

end
