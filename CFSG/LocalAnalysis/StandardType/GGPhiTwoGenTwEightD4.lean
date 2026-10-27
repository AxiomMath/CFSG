module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightTorusW
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwD4
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLargeReeTits

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.StandardType.TableBExcTwoFusion


private lemma frameLang_mem_adjointGroup {K : Type} [Field K] [CharP K 2] {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    frameLang ζ hζ ∈ adjointGroup TwistTag.E6.tag K := by
  unfold frameLang
  exact mul_mem (mul_mem (mul_mem
    (CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup (frameRoot 0) _)
    (CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup (frameRoot 1) _))
    (CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup (frameRoot 2) _))
    (CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup (frameRoot 3) _)

theorem centerCut_frameLang {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hK : Nat.card K = 64) (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    CenterCut K σ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ)) := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    have h1 : (1 : K) = 0 := by simp at hζ
    exact one_ne_zero h1
  let ζu : Kˣ := Units.mk0 ζ hζ0
  have hζu3 : ζu ^ 3 = 1 := by
    apply Units.ext
    change (ζu : K) ^ 3 = (1 : K)
    exact pow_three_of_sq_add (x := (ζu : K)) (by simpa [ζu] using hζ)
  have hζu1 : ζu ≠ 1 := by
    intro h
    have hval : ζ = 1 := by simpa [ζu] using congrArg Units.val h
    rw [hval] at hζ
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h1 : (1 : K) = 0 := by linear_combination hζ - h2
    exact one_ne_zero h1
  have hζo : orderOf ζu = 3 := by
    have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hp := h3) hζu3 hζu1
  let ζ' : (AlgebraicClosure K)ˣ :=
    Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζu
  have hζ'3 : ζ' ^ 3 = 1 := by
    change (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζu) ^ 3 = 1
    rw [← map_pow, hζu3, map_one]
  have hζ'o : orderOf ζ' = 3 := by
    change orderOf (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζu) = 3
    rw [orderOf_injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom)
      (Units.map_injective fun a b h => (algebraMap K (AlgebraicClosure K)).injective h) ζu]
    exact hζo
  let a : ModGL TwistTag.E6.tag K := frameLang ζ hζ
  let a' : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) a
  have haC : a ∈ adjointGroup TwistTag.E6.tag K := frameLang_mem_adjointGroup hζ
  have hg0C : a' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup
      (algebraMap K (AlgebraicClosure K)) haC
  let VG : Submodule (ZMod 3) (Fin TwistTag.E6.tag.rank → ZMod 3) := frameVG
  let W : Submodule (ZMod 3) (Fin TwistTag.E6.tag.rank → ZMod 3) := frameW
  have hVW : IsCompl VG W := frameVG_isCompl_frameW
  have hdim : Module.finrank (ZMod 3) VG = 4 := frameVG_finrank
  let T0 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3) →*
      ModGL TwistTag.E6.tag K := frameTorusHom ζu hζu3 a
  have hmem : ∀ t : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3),
      T0 t ∈ twistedE6RootGroup K σ := by
    intro t
    change T0 (Multiplicative.ofAdd t.toAdd) ∈ twistedE6RootGroup K σ
    have hsup : VG ⊔ W = ⊤ := codisjoint_iff.mp frameVG_isCompl_frameW.codisjoint
    have ht : t.toAdd ∈ VG ⊔ W := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp ht
    rw [← hvw, ofAdd_add, map_mul]
    refine mul_mem ?_ ?_
    · have h := frameTorusHom_mem_frame hζ hζo hζu3 σ hv
      obtain ⟨x, hx, hxT⟩ := Subgroup.mem_map.mp h
      rw [show T0 (Multiplicative.ofAdd v) = (x : ModGL TwistTag.E6.tag K) from hxT.symm]
      exact x.2
    · have h := frameTorusHom_W hK σ hσ hζ hζu3 hw
      obtain ⟨x, hx, hxT⟩ := Subgroup.mem_map.mp h
      rw [show T0 (Multiplicative.ofAdd w) = (x : ModGL TwistTag.E6.tag K) from hxT.symm]
      exact x.2
  let T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3) →*
      twistedE6RootGroup K σ := T0.codRestrict (twistedE6RootGroup K σ) hmem
  have hTinj0 : Function.Injective T0 := frameTorusHom_injective hζo hζu3
  have hTinj : Function.Injective T := fun x y h =>
    hTinj0 (by simpa [T] using congrArg Subtype.val h)
  have hzeta : ∀ t : Fin TwistTag.E6.tag.rank → ZMod 3,
      (fun k => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
        (TableBExc.E6Three.zetaVec ζu hζu3 t k)) =
      TableBExc.E6Three.zetaVec ζ' hζ'3 t := by
    intro t
    funext k
    rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply]
    rw [show ζ' = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζu from rfl,
      map_pow]
  have hT : ∀ t : Fin TwistTag.E6.tag.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (Multiplicative.ofAdd t) : twistedE6RootGroup K σ) :
            ModGL TwistTag.E6.tag K) =
        a' * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ' hζ'3 t) * a'⁻¹ := by
    intro t
    change baseChangeGL (algebraMap K (AlgebraicClosure K)) (T0 (Multiplicative.ofAdd t)) =
      a' * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ' hζ'3 t) * a'⁻¹
    rw [frameTorusHom_apply]
    change baseChangeGL (algebraMap K (AlgebraicClosure K))
        (a * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζu hζu3 t) * a⁻¹) = _
    rw [map_mul, map_mul, map_inv,
      CFSG.TauCetiBridge.BigCell.baseChangeGL_rootDiagUnit]
    change a' * rootDiagUnit TwistTag.E6.tag
        (fun k => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
          (TableBExc.E6Three.zetaVec ζu hζu3 t k)) * a'⁻¹ = _
    rw [hzeta t]
  have hVG : ∀ t ∈ VG, T (Multiplicative.ofAdd t) ∈
      ⨆ i, (frameHom σ.toRingHom i).range := by
    intro t ht
    have h := frameTorusHom_mem_frame hζ hζo hζu3 σ ht
    obtain ⟨x, hx, hxT⟩ := Subgroup.mem_map.mp h
    have hTx : T (Multiplicative.ofAdd t) = x := Subtype.ext (by
      change T0 (Multiplicative.ofAdd t) = (x : ModGL TwistTag.E6.tag K)
      exact hxT.symm)
    rw [hTx]
    exact hx
  have hW : ∀ t ∈ W, T (Multiplicative.ofAdd t) ∈ (torusG σ.toRingHom).range := by
    intro t ht
    have h := frameTorusHom_W hK σ hσ hζ hζu3 ht
    obtain ⟨x, hx, hxT⟩ := Subgroup.mem_map.mp h
    have hTx : T (Multiplicative.ofAdd t) = x := Subtype.ext (by
      change T0 (Multiplicative.ofAdd t) = (x : ModGL TwistTag.E6.tag K)
      exact hxT.symm)
    rw [hTx]
    exact hx
  have hD4 := CFSG.StandardType.PhiTwoRootGen.orbitRankOneGroup_three_le_iSup_phiTwoCompIn_d4
    (n := 3) (hn := by norm_num) (K := K) (hK := by norm_num; exact hK) (σ := σ)
    (hσ := by intro c; rw [show 2 ^ 3 = 8 by norm_num]; exact hσ c)
    (p := 3) (hp2 := by norm_num) (hpq := by norm_num)
    (ζ := ζ') (hζo := hζ'o) (hζ := hζ'3) (g0 := a') (hg0C := hg0C)
    (T := T) (hTinj := hTinj) (hT := hT) (VG := VG) (W := W)
    (hVW := hVW) (hdim := hdim) (hVG := hVG) (hW := hW)
  intro y hy
  obtain ⟨A, rfl⟩ := hy
  have hA : (centerHom σ.toRingHom A : ModGL TwistTag.E6.tag K) ∈
      orbitRankOneGroup TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ := by
    rw [coe_centerHom]
    exact rankOneFix_mem_orbitRankOneGroup σ.toRingHom orbCenter orbCenter_card A
  have hmemD4 := hD4 hA
  rw [Subgroup.mem_map] at hmemD4
  obtain ⟨z, hz, hzy⟩ := hmemD4
  have hzy' : z = centerHom σ.toRingHom A := Subtype.ext hzy
  rw [← hzy']
  exact hz

end CFSG.StandardType.PhiTwoRootGen

end
