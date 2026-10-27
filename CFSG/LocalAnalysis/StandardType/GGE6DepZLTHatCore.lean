module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLScBase
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowA
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowC

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement


private theorem zl_pi_nt {k : Type} [Field k] [Finite k] (i : Fin 6) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.nt k i s) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
      weylElt Tag.E6 k i s :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_nt_eq i s

private theorem zl_pi_hm {k : Type} [Field k] [Finite k] (i : Fin 6) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.hm k i s) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
      torusElt Tag.E6 k i s :=
  (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_hm_eq i s).trans
    (torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := k) i s).symm

theorem zl_hat_core {F E : Type} [Field F] [Finite F] [Field E] [Finite E] (ι : F →+* E)
    (hF3 : 3 ∣ Nat.card F - 1) (ζ : Eˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (gE : ↥(adjointGroup Tag.E6 E)) (û b : Fin 6 → ↥(e6Data_valid.minGroup F))
    (hû : ∀ i, ((e6Isogeny E (scBase ι (û i)) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
      (gE : ModGL Tag.E6 E) * weylElt Tag.E6 E i 1 * (gE : ModGL Tag.E6 E)⁻¹)
    (hb : ∀ i, ((e6Isogeny E (scBase ι (b i)) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
      (gE : ModGL Tag.E6 E) * torusElt Tag.E6 E i ζ * (gE : ModGL Tag.E6 E)⁻¹) :
    (∀ i, ⁅û i, ⁅û i, b i⁆⁆ = ⁅û i, b i⁆) ∧
    (∀ i, ((e6Isogeny E (scBase ι ⁅û i, b i⁆) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
      (gE : ModGL Tag.E6 E) * torusElt Tag.E6 E i ζ * (gE : ModGL Tag.E6 E)⁻¹) ∧
    ∀ z : ↥(e6Data_valid.minGroup F), e6Isogeny F z = 1 →
      z ∈ Subgroup.closure (Set.range fun i => ⁅û i, b i⁆) := by
  classical
  obtain ⟨ĝ, hĝ⟩ := e6Isogeny_surjective E gE
  set uE : Fin 6 → ↥(e6Data_valid.minGroup E) :=
    fun i => ĝ * e6Data_valid.nm E i * ĝ⁻¹ with huE
  set bE : Fin 6 → ↥(e6Data_valid.minGroup E) :=
    fun i => ĝ * e6Data_valid.hm E i ζ * ĝ⁻¹ with hbE
  have hπuE : ∀ i,
      ((e6Isogeny E (uE i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
        (gE : ModGL Tag.E6 E) * weylElt Tag.E6 E i 1 * (gE : ModGL Tag.E6 E)⁻¹ := by
    intro i
    have hnm : e6Data_valid.nm E i = e6Data_valid.nt E i 1 := rfl
    simp only [huE, hnm]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hĝ, zl_pi_nt]
  have hπbE : ∀ i,
      ((e6Isogeny E (bE i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
        (gE : ModGL Tag.E6 E) * torusElt Tag.E6 E i ζ * (gE : ModGL Tag.E6 E)⁻¹ := by
    intro i
    rw [hbE]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hĝ, zl_pi_hm]
  set c : Fin 6 → ↥(e6Data_valid.minGroup E) := fun i => (uE i)⁻¹ * scBase ι (û i) with hc
  set d : Fin 6 → ↥(e6Data_valid.minGroup E) := fun i => (bE i)⁻¹ * scBase ι (b i) with hd
  have hc_ker : ∀ i, e6Isogeny E (c i) = 1 := by
    intro i
    apply Subtype.ext
    have hco : ((e6Isogeny E (c i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
        ((e6Isogeny E (uE i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E)⁻¹ *
          ((e6Isogeny E (scBase ι (û i)) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) := by
      simp only [hc]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hco, hπuE i, hû i]
    group
    rfl
  have hd_ker : ∀ i, e6Isogeny E (d i) = 1 := by
    intro i
    apply Subtype.ext
    have hdo : ((e6Isogeny E (d i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
        ((e6Isogeny E (bE i) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E)⁻¹ *
          ((e6Isogeny E (scBase ι (b i)) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) := by
      simp only [hd]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hdo, hπbE i, hb i]
    group
    rfl
  have hc_center : ∀ i, c i ∈ Subgroup.center ↥(e6Data_valid.minGroup E) := by
    intro i
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := E),
      MonoidHom.mem_ker]
    exact hc_ker i
  have hd_center : ∀ i, d i ∈ Subgroup.center ↥(e6Data_valid.minGroup E) := by
    intro i
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := E),
      MonoidHom.mem_ker]
    exact hd_ker i
  have hsc_u : ∀ i, scBase ι (û i) = uE i * c i := by
    intro i
    simp only [hc]
    group
  have hsc_b : ∀ i, scBase ι (b i) = bE i * d i := by
    intro i
    simp only [hd]
    group
  have hcommE : ∀ i, ⁅uE i, bE i⁆ =
      ĝ * ⁅e6Data_valid.nm E i, e6Data_valid.hm E i ζ⁆ * ĝ⁻¹ := by
    intro i
    simp only [huE, hbE, commutatorElement_def]
    group
  have hcommUE : ∀ i, ⁅uE i, bE i⁆ = bE i := by
    intro i
    rw [hcommE i, zl_comm_nm_hm ζ hζ i]
  have hsc_comm : ∀ i, scBase ι ⁅û i, b i⁆ = bE i := by
    intro i
    rw [map_commutatorElement, hsc_u i, hsc_b i,
      CFSG.LieType.Steinberg.Isogeny.commutatorElement_mul_mul_of_mem_center (uE i) (bE i)
        (hc_center i) (hd_center i)]
    exact hcommUE i
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i
    apply scBase_injective ι
    rw [map_commutatorElement, hsc_comm i, hsc_u i]
    have h := CFSG.LieType.Steinberg.Isogeny.commutatorElement_mul_mul_of_mem_center
      (a := uE i) (b := bE i) (z := c i) (w := 1) (hc_center i) (Subgroup.one_mem _)
    rw [mul_one] at h
    rw [h, hcommUE i]
  ·
    intro i
    rw [hsc_comm i]
    exact hπbE i
  ·
    intro z hz
    set S : Subgroup ↥(e6Data_valid.minGroup F) :=
      Subgroup.closure (Set.range fun i => ⁅û i, b i⁆) with hS
    set SE : Subgroup ↥(e6Data_valid.minGroup E) := Subgroup.closure (Set.range bE) with hSE
    let zE := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid E
      (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ kappa)
    have hzE_ker : e6Isogeny E zE = 1 := zl_isogeny_minTorus_kappa ζ hζ
    have hzE_ne : zE ≠ 1 := zl_minTorus_kappa_ne_one ζ hζ hζo
    have hzE_center : zE ∈ Subgroup.center ↥(e6Data_valid.minGroup E) := by
      rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := E),
        MonoidHom.mem_ker]
      exact hzE_ker
    have hconj_zE : MulAut.conj ĝ zE = zE := by
      have hc : ĝ * zE = zE * ĝ := (Subgroup.mem_center_iff.1 hzE_center) ĝ
      calc MulAut.conj ĝ zE = ĝ * zE * ĝ⁻¹ := MulAut.conj_apply ĝ zE
        _ = zE * ĝ * ĝ⁻¹ := by rw [hc]
        _ = zE := by group
    have hzE_SE : zE ∈ SE := by
      have hS' : ∀ i, e6Data_valid.hm E i ζ ∈ SE.comap (MulAut.conj ĝ).toMonoidHom := by
        intro i
        rw [Subgroup.mem_comap]
        change MulAut.conj ĝ (e6Data_valid.hm E i ζ) ∈ SE
        rw [MulAut.conj_apply]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      have h := zl_minTorus_kappa_mem ζ hζ (SE.comap (MulAut.conj ĝ).toMonoidHom) hS'
      rw [Subgroup.mem_comap] at h
      rwa [show (MulAut.conj ĝ).toMonoidHom zE = zE from by
        change MulAut.conj ĝ zE = zE
        exact hconj_zE] at h
    have hmap_le : SE ≤ S.map (scBase ι) := by
      rw [hSE, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_map.2 ⟨⁅û i, b i⁆, Subgroup.subset_closure ⟨i, rfl⟩, hsc_comm i⟩
    obtain ⟨s, hsS, hsc_s⟩ := Subgroup.mem_map.1 (hmap_le hzE_SE)
    have hpi_s : e6Isogeny F s = 1 := by
      apply Subtype.ext
      have hE : ((e6Isogeny E (scBase ι s) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) = 1 := by
        rw [hsc_s]
        simpa using congrArg Subtype.val hzE_ker
      rw [scBase_isogeny ι s] at hE
      exact baseChangeGL_injective (τ := Tag.E6) (f := ι) (hE.trans (map_one _).symm)
    have hs_ne : s ≠ 1 := by
      intro h
      rw [h, map_one] at hsc_s
      exact hzE_ne hsc_s.symm
    haveI hFact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI hFinF : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := F) e6Data_valid
    have hkerF : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
    have hcardF : Nat.card ((e6Isogeny F).ker) = 3 := by
      rw [hkerF, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1,
        Nat.gcd_eq_left hF3]
    have hs_ker : s ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker]
      exact hpi_s
    have hdvd : orderOf s ∣ 3 := by
      have h1 := Subgroup.orderOf_dvd_natCard (e6Isogeny F).ker hs_ker
      rwa [hcardF] at h1
    have horder : orderOf s = 3 :=
      orderOf_eq_prime ((orderOf_dvd_iff_pow_eq_one).mp hdvd) hs_ne
    have hcardzp : Nat.card (Subgroup.zpowers s) = 3 := by
      rw [Nat.card_zpowers, horder]
    have hker_eq : (e6Isogeny F).ker = Subgroup.zpowers s :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hs_ker)
        (by rw [hcardF, hcardzp])).symm
    have hz_ker : z ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker]
      exact hz
    rw [hker_eq] at hz_ker
    exact Subgroup.zpowers_le.2 hsS hz_ker

end CFSG.StandardType.E6Dep.ZL

end
