module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrameData
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeEmbed
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeRational
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.RankThree.PartOne.KE6.EqpFrame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

private theorem pow_eq_sq_of_three_dvd_add_one {q : ℕ} (h3 : 3 ∣ q + 1) {M : Type*} [Monoid M]
    {ζ : M} (hζ : ζ ^ 3 = 1) : ζ ^ q = ζ ^ 2 := by
  have hq : q % 3 = 2 := by
    obtain ⟨k, hk⟩ := h3
    omega
  calc ζ ^ q = ζ ^ (q % 3 + 3 * (q / 3)) :=
        (congrArg (fun e => ζ ^ e) (Nat.mod_add_div q 3)).symm
    _ = ζ ^ (q % 3) * (ζ ^ 3) ^ (q / 3) := by rw [pow_add, pow_mul]
    _ = ζ ^ 2 := by rw [hq, hζ, one_pow, mul_one]

private theorem exists_orderOf_eq_three (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ζ : Lˣ, orderOf ζ = 3 := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have e : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
    rw [e, h2, zero_add]
    exact one_ne_zero
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot ((hu.unit : Lˣ) : L) 3 := by simpa using hζ₀
  exact ⟨hu.unit, (IsPrimitiveRoot.coe_units_iff.1 hζ).eq_orderOf.symm⟩

section Certs

theorem exists_e6QPlusThreeFrame_with_coordinates
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL .E6 (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1)
      (F : E6QPlusThreeFrame K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .E6 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 = g0 * eqpN (AlgebraicClosure K) ∧ orderOf ζ = 3 ∧
      Units.map Fr.toMonoidHom ζ = ζ ^ 2 ∧ Function.Surjective F.weyl ∧
      ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.frame s : ModGL .E6 K) =
          g0 * e6ThreeDiag ζ hζ s * g0⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, _h2prime, hcard⟩ := FiniteField.card K 2
  have h3' : ¬ 3 ∣ Nat.card K - 1 := by
    obtain ⟨k, hk⟩ := h3
    intro h
    obtain ⟨m, hm⟩ := h
    omega
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    show (iterateFrobenius L 2 f) c = c ^ Nat.card K
    rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  obtain ⟨g0, hg0C, hg0F2, hg0Fr⟩ := exists_lang_eqpN K h3 L Fr hFr
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_three L
  have hζ : ζ ^ 3 = 1 := by simpa [hζo] using pow_orderOf_eq_one ζ
  have hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ 2 := by
    ext
    rw [Units.val_pow_eq_pow_val]
    show Fr (ζ : L) = (ζ : L) ^ 2
    rw [hFr]
    exact pow_eq_sq_of_three_dvd_add_one h3
      (by simpa using congrArg (fun u : Lˣ => (u : L)) hζ)
  have hF2ζ : Units.map (frobenius L 2).toMonoidHom ζ = ζ ^ 2 := by
    ext
    rw [Units.val_pow_eq_pow_val]
    show (frobenius L 2) (ζ : L) = (ζ : L) ^ 2
    rw [frobenius_def]
  obtain ⟨ι, hι, hbc, hrange⟩ := exists_nfixEmb h3' Fr hFr hg0C hg0Fr
  let e0' : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* NFix (eqpN L) Fr :=
    (e6ThreeDiag ζ hζ).codRestrict (NFix (eqpN L) Fr)
      (fun s => e6ThreeDiag_mem_NFix Fr hζ hFrζ s)
  let wE : NFix (eqpN L) Fr →* relWeylTwist TwistTag.E6 :=
    (NFixToWeyl (eqpN L) Fr).codRestrict (relWeylTwist TwistTag.E6)
      (fun y => by rw [← centralizer_e6W0]; exact NFixToWeyl_mem_centralizer Fr e6W0 y)
  let frame : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K := ι.comp e0'
  let weyl : ι.range →* WeylGroup .F4 :=
    (foldedWeylEquiv TwistTag.E6).toMonoidHom.comp
      (wE.comp (MonoidHom.ofInjective hι).symm.toMonoidHom)
  have he0'inj : Function.Injective e0' := by
    intro a b h
    exact e6ThreeDiag_injective hζo hζ (congrArg Subtype.val h)
  have hsurj : Function.Surjective weyl := by
    intro v
    have hu : ((foldedWeylEquiv TwistTag.E6).symm v).1 ∈
        Subgroup.centralizer ({e6W0} : Set (WeylGroup Tag.E6)) :=
      (SetLike.ext_iff.mp centralizer_e6W0 _).2 ((foldedWeylEquiv TwistTag.E6).symm v).2
    obtain ⟨x, hx⟩ := NFixToWeyl_surjective_centralizer Fr e6W0 Finite.one_lt_card hFr hu
    refine ⟨MonoidHom.ofInjective hι x, ?_⟩
    have hwE : wE x = (foldedWeylEquiv TwistTag.E6).symm v := Subtype.ext hx
    have h2 : weyl (MonoidHom.ofInjective hι x) = (foldedWeylEquiv TwistTag.E6)
        (wE ((MonoidHom.ofInjective hι).symm (MonoidHom.ofInjective hι x))) := rfl
    rw [h2, MulEquiv.symm_apply_apply, hwE]
    exact (foldedWeylEquiv TwistTag.E6).apply_symm_apply v
  refine ⟨Fr, g0, ζ, hζ, ⟨ι.range, weyl, frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hFr, hg0C, hg0Fr, hζo, hFrζ, hsurj, fun s => hbc (e0' s)⟩
  · exact hι.comp he0'inj
  · rintro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    exact ⟨e0' s, rfl⟩
  · intro a s
    let y : NFix (eqpN L) Fr := (MonoidHom.ofInjective hι).symm a
    have hιy : (ι y : adjointGroup .E6 K) = (a : adjointGroup .E6 K) := by
      have h1 : ((MonoidHom.ofInjective hι) y : ι.range) = a :=
        MulEquiv.apply_symm_apply (MonoidHom.ofInjective hι) a
      have h2 : (((MonoidHom.ofInjective hι) y : ι.range) : adjointGroup .E6 K) = ι y :=
        MonoidHom.ofInjective_apply hι
      rw [← h2, h1]
    have hu : NFixToWeyl (eqpN L) Fr y ∈ relWeylTwist TwistTag.E6 := by
      rw [← centralizer_e6W0]
      exact NFixToWeyl_mem_centralizer Fr e6W0 y
    have hyu : MapsRootLines (y : ModGL .E6 L) (NFixToWeyl (eqpN L) Fr y) :=
      mapsRootLines_weylQuotientHom
        (⟨y, NFix_le_monomialSubgroup (eqpN L) Fr y.2⟩ : monomialSubgroup Tag.E6 L)
    have hmono := monomial_conj_e6ThreeDiag hζ
      (NFix_le_monomialSubgroup (eqpN L) Fr y.2) hyu hu s
    have hwEy : wE y = (⟨NFixToWeyl (eqpN L) Fr y, hu⟩ : relWeylTwist TwistTag.E6) :=
      Subtype.ext rfl
    have hweyl : weyl a = foldedWeylEquiv TwistTag.E6 ⟨NFixToWeyl (eqpN L) Fr y, hu⟩ := by
      show (foldedWeylEquiv TwistTag.E6) (wE y) = _
      rw [hwEy]
    have hstep : (a : adjointGroup .E6 K) * frame (Multiplicative.ofAdd s)
          * (a : adjointGroup .E6 K)⁻¹
        = ι (y * e0' (Multiplicative.ofAdd s) * y⁻¹) := by
      rw [← hιy]
      change ι y * ι (e0' (Multiplicative.ofAdd s)) * (ι y)⁻¹
        = ι (y * e0' (Multiplicative.ofAdd s) * y⁻¹)
      rw [← map_mul, ← map_inv, ← map_mul]
    rw [hstep]
    have htarget : frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (weyl a) s))
        = ι (e0' (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (weyl a) s))) := rfl
    rw [htarget]
    congr 1
    apply Subtype.ext
    rw [hweyl]
    change (y : ModGL .E6 L) * e6ThreeDiag ζ hζ (Multiplicative.ofAdd s)
        * (y : ModGL .E6 L)⁻¹
      = e6ThreeDiag ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3
          (foldedWeylEquiv TwistTag.E6 ⟨NFixToWeyl (eqpN L) Fr y, hu⟩) s))
    exact hmono
  · intro a hweyl1 ha3
    let y : NFix (eqpN L) Fr := (MonoidHom.ofInjective hι).symm a
    have hιy : (ι y : adjointGroup .E6 K) = (a : adjointGroup .E6 K) := by
      have h1 : ((MonoidHom.ofInjective hι) y : ι.range) = a :=
        MulEquiv.apply_symm_apply (MonoidHom.ofInjective hι) a
      have h2 : (((MonoidHom.ofInjective hι) y : ι.range) : adjointGroup .E6 K) = ι y :=
        MonoidHom.ofInjective_apply hι
      rw [← h2, h1]
    have hwEy1 : wE y = 1 := by
      have h1 : (foldedWeylEquiv TwistTag.E6) (wE y) = 1 := by
        have h2 : weyl a = (foldedWeylEquiv TwistTag.E6) (wE y) := rfl
        rw [h2] at hweyl1
        exact hweyl1
      exact (foldedWeylEquiv TwistTag.E6).map_eq_one_iff.mp h1
    have hker : NFixToWeyl (eqpN L) Fr y = 1 := by
      have h := congrArg (fun z : relWeylTwist TwistTag.E6 => z.1) hwEy1
      change (NFixToWeyl (eqpN L) Fr y : WeylGroup Tag.E6) = 1 at h
      exact h
    have hmemker : y ∈ (NFixToWeyl (eqpN L) Fr).ker := MonoidHom.mem_ker.mpr hker
    rw [NFixToWeyl_ker (eqpN L) Fr] at hmemker
    rw [Subgroup.mem_subgroupOf] at hmemker
    have htor : (y : ModGL .E6 L) ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN L) Fr :=
      hmemker
    have hy3 : y ^ 3 = 1 := by
      apply hι
      rw [map_pow, hιy, ha3, map_one]
    have hy3M : ((y : ModGL .E6 L)) ^ 3 = 1 := by
      have h := congrArg (fun z : NFix (eqpN L) Fr => (z : ModGL .E6 L)) hy3
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    obtain ⟨s, hs⟩ := exists_e6ThreeDiag_eq Fr hζo hζ hFrζ htor hy3M
    refine ⟨s, ?_⟩
    show ι (e0' s) = (a : adjointGroup .E6 K)
    rw [show e0' s = y from Subtype.ext hs, hιy]
  · exact exists_sylow_le_nfixEmb_range h3 Fr hFr ι hι
  · intro c hc hc3
    have hzC : (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0)
        ∈ adjointGroup .E6 L :=
      mul_mem (mul_mem (inv_mem hg0C)
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) c.2)) hg0C
    have hcomm : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
        (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0) * e6ThreeDiag ζ hζ s
          = e6ThreeDiag ζ hζ s
            * (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0) := by
      intro s
      have hbc_s : baseChangeGL (algebraMap K L)
            (((frame s : adjointGroup .E6 K)) : ModGL .E6 K)
          = g0 * e6ThreeDiag ζ hζ s * g0⁻¹ := hbc (e0' s)
      have hcM : (c : ModGL .E6 K) * (((frame s : adjointGroup .E6 K)) : ModGL .E6 K)
          = (((frame s : adjointGroup .E6 K)) : ModGL .E6 K) * (c : ModGL .E6 K) :=
        congrArg Subtype.val (hc s)
      have hcm : baseChangeGL (algebraMap K L) (c : ModGL .E6 K)
              * (g0 * e6ThreeDiag ζ hζ s * g0⁻¹)
          = (g0 * e6ThreeDiag ζ hζ s * g0⁻¹)
              * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) := by
        have h := congrArg (baseChangeGL (algebraMap K L)) hcM
        rw [map_mul, map_mul, hbc_s] at h
        exact h
      calc (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0)
              * e6ThreeDiag ζ hζ s
          = g0⁻¹ * (baseChangeGL (algebraMap K L) (c : ModGL .E6 K)
                * (g0 * e6ThreeDiag ζ hζ s * g0⁻¹)) * g0 := by group
        _ = g0⁻¹ * ((g0 * e6ThreeDiag ζ hζ s * g0⁻¹)
                * baseChangeGL (algebraMap K L) (c : ModGL .E6 K)) * g0 := by rw [hcm]
        _ = e6ThreeDiag ζ hζ s
              * (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0) := by group
    have hztorus : (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0)
        ∈ torusGroup .E6 L :=
      mem_torusGroup_of_commute_e6ThreeDiag hζo hζ hzC hcomm
    have hzmono : (g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0)
        ∈ monomialSubgroup .E6 L := torusGroup_le_monomialSubgroup' hztorus
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hrange c hzmono)
    have hy_eq : (y : ModGL .E6 L)
        = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0 := by
      have h := hbc y
      rw [hy] at h
      rw [h]
      group
    have hytor : (y : ModGL .E6 L)
        ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN L) Fr := by
      exact mem_twistedTorusOf_iff_negPhi.mpr ⟨by rw [hy_eq]; exact hztorus, y.2.2⟩
    have hy3 : y ^ 3 = 1 := by
      apply hι
      rw [map_pow, hy, hc3, map_one]
    have hy3M : ((y : ModGL .E6 L)) ^ 3 = 1 := by
      have h := congrArg (fun z : NFix (eqpN L) Fr => (z : ModGL .E6 L)) hy3
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    obtain ⟨s, hs⟩ := exists_e6ThreeDiag_eq Fr hζo hζ hFrζ hytor hy3M
    refine ⟨s, ?_⟩
    show ι (e0' s) = c
    rw [show e0' s = y from Subtype.ext hs, hy]
  · intro x hx
    have hzC : (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0)
        ∈ adjointGroup .E6 L :=
      mul_mem (mul_mem (inv_mem hg0C)
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) x.2)) hg0C
    have hznorm : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
        (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0) * e6ThreeDiag ζ hζ s
            * (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0)⁻¹
          ∈ (e6ThreeDiag ζ hζ).range := by
      intro s
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hx s)
      have hbc_s : baseChangeGL (algebraMap K L)
            (((frame s : adjointGroup .E6 K)) : ModGL .E6 K)
          = g0 * e6ThreeDiag ζ hζ s * g0⁻¹ := hbc (e0' s)
      have hbc_t : baseChangeGL (algebraMap K L)
            (((frame t : adjointGroup .E6 K)) : ModGL .E6 K)
          = g0 * e6ThreeDiag ζ hζ t * g0⁻¹ := hbc (e0' t)
      have htM : ((frame t : adjointGroup .E6 K) : ModGL .E6 K)
          = (x : ModGL .E6 K) * ((frame s : adjointGroup .E6 K) : ModGL .E6 K)
              * (x : ModGL .E6 K)⁻¹ := congrArg Subtype.val ht
      have h1 : g0 * e6ThreeDiag ζ hζ t * g0⁻¹
          = baseChangeGL (algebraMap K L) (x : ModGL .E6 K)
              * (g0 * e6ThreeDiag ζ hζ s * g0⁻¹)
              * (baseChangeGL (algebraMap K L) (x : ModGL .E6 K))⁻¹ := by
        have h := congrArg (baseChangeGL (algebraMap K L)) htM
        rw [map_mul, map_mul, map_inv, hbc_t, hbc_s] at h
        exact h
      refine ⟨t, ?_⟩
      calc e6ThreeDiag ζ hζ t
          = g0⁻¹ * (g0 * e6ThreeDiag ζ hζ t * g0⁻¹) * g0 := by group
        _ = g0⁻¹ * (baseChangeGL (algebraMap K L) (x : ModGL .E6 K)
                * (g0 * e6ThreeDiag ζ hζ s * g0⁻¹)
                * (baseChangeGL (algebraMap K L) (x : ModGL .E6 K))⁻¹) * g0 := by rw [h1]
        _ = (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0)
                * e6ThreeDiag ζ hζ s
                * (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0)⁻¹ := by
              group
    exact hrange x (mem_monomialSubgroup_of_conj_e6ThreeDiag hζo hζ hzC hznorm)
  · intro σ s
    exact entrywise_eq_self_of_baseChangeGL_eq (K := K) (L := L) hg0F2
      (negPhi_eqpN_e6ThreeDiag (frobenius L 2) hζ hF2ζ s) (hbc (e0' s)) σ

theorem exists_e6QPlusThreeFrame_weyl_surjective
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) : ∃ F : E6QPlusThreeFrame K, Function.Surjective F.weyl := by
  obtain ⟨Fr, g0, ζ, hζ, F, -, -, -, -, -, hsurj, -⟩ :=
    exists_e6QPlusThreeFrame_with_coordinates h3
  exact ⟨F, hsurj⟩

theorem nonempty_e6QPlusThreeFrame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) : Nonempty (E6QPlusThreeFrame K) :=
  (exists_e6QPlusThreeFrame_weyl_surjective h3).elim fun F _ => ⟨F⟩

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
