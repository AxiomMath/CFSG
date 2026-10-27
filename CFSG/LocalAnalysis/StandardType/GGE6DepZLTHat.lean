module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTFin
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTHatCore
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTQGeo
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTV0
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLScBase
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Lang.E6Descent
open scoped commutatorElement


theorem tFrame_hat {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) :
    ∃ (q : twistedE6Group 2 n →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (û ĥ : Fin 6 → twistedE6Group 2 n),
      Function.Surjective q ∧ q.ker ≤ Subgroup.center (twistedE6Group 2 n) ∧
      (∀ i, q (û i) = D.nb i) ∧ (∀ i, q (ĥ i) ∈ D.V0) ∧ (∀ i, ⁅û i, ĥ i⁆ = ĥ i) ∧
      q.ker ≤ Subgroup.closure (Set.range ĥ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      card_galoisField_two_mul 2 n hn, hK]
  set τ : GaloisField 2 (2 * n) ≃+* K := FiniteField.ringEquivOfCardEq hcard
  have hτ : τ.toRingHom.comp (frobQ 2 n) = σ.toRingHom.comp τ.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, frobQ_apply, map_pow]
      exact (hσ (τ c)).symm
  obtain ⟨q, hqsurj, hqcenter, hqb⟩ := exists_qGeo (Ω := Ω) hn hK σ hσ τ hτ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨E, hEfin, hζE_mem, hKE, gE, hgE_mem, hgEeq⟩ :=
    exists_finiteData (K := K) hL.1 ζ
  haveI : Finite E := hEfin
  let ι : GaloisField 2 (2 * n) →+* E :=
    (((algebraMap K Ω).comp τ.toRingHom).codRestrict E fun c => hKE ⟨τ c, rfl⟩)
  have hι : E.subtype.comp ι = (algebraMap K Ω).comp τ.toRingHom := by
    ext c
    rfl
  let ζE : Eˣ :=
    ⟨⟨ζ, hζE_mem⟩, ⟨ζ⁻¹, inv_mem hζE_mem⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hζE_coe : Units.map E.subtype.toMonoidHom ζE = ζ := Units.ext rfl
  have hζE3 : ζE ^ 3 = 1 := by
    apply Units.map_injective (f := E.subtype.toMonoidHom) E.subtype.injective
    rw [map_pow, hζE_coe, hζ, map_one]
  have hζEo : orderOf ζE = 3 := by
    have h := orderOf_injective (Units.map E.subtype.toMonoidHom)
      (Units.map_injective (f := E.subtype.toMonoidHom) E.subtype.injective) ζE
    rw [hζE_coe, hζo] at h
    exact h.symm
  have hs : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [hm, pow_mul, hζ, one_pow]
  have hC : ∀ i, g * torusElt Tag.E6 Ω i ζ * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
    fun i => torusElt_mem_Cgrp hn hK σ hσ Fr hFr h3 hL hζ hD i ζ hs
  let r0 : Fin 6 → ModGL TwistTag.E6.tag K := fun i =>
    Classical.choose (Subgroup.mem_map.1 (hC i))
  have hr0mem : ∀ i, r0 i ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := fun i =>
    (Classical.choose_spec (Subgroup.mem_map.1 (hC i))).1
  have hr0eq : ∀ i, baseChangeGL (algebraMap K Ω) (r0 i) =
      g * torusElt Tag.E6 Ω i ζ * g⁻¹ := fun i =>
    (Classical.choose_spec (Subgroup.mem_map.1 (hC i))).2
  let r : Fin 6 → ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := fun i => ⟨r0 i, hr0mem i⟩
  have hreq : ∀ i, baseChangeGL (algebraMap K Ω)
      ((r i : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      g * torusElt Tag.E6 Ω i ζ * g⁻¹ := fun i => hr0eq i
  let û : Fin 6 → twistedE6Group 2 n := fun i => Classical.choose (hqsurj (D.nb i))
  have hûq : ∀ i, q (û i) = D.nb i := fun i => Classical.choose_spec (hqsurj (D.nb i))
  let b : Fin 6 → twistedE6Group 2 n := fun i => Classical.choose (hqsurj (r i))
  have hbq : ∀ i, q (b i) = r i := fun i => Classical.choose_spec (hqsurj (r i))
  have hstep3 : ∀ u : twistedE6Group 2 n,
      baseChangeGL E.subtype
        (((e6Isogeny E (scBase ι (u : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))) :
            ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E)) =
      baseChangeGL (algebraMap K Ω)
        ((q u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) := by
    intro u
    rw [scBase_isogeny ι (u : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))]
    rw [baseChangeGL_baseChangeGL]
    rw [hι]
    exact (hqb u).symm
  let gE' : ↥(adjointGroup Tag.E6 E) := ⟨gE, hgE_mem⟩
  have hw6 : ∀ i : Fin 6, baseChangeGL E.subtype (weylElt Tag.E6 (↥E) i 1) =
      weylElt Tag.E6 Ω i 1 := by
    intro i
    let j : Fin (Tag.rank .E6) := i
    change baseChangeGL E.subtype (weylElt Tag.E6 (↥E) j 1) = weylElt Tag.E6 Ω j 1
    rw [baseChangeGL_weylElt_one]
  have ht6 : ∀ i : Fin 6, baseChangeGL E.subtype (torusElt Tag.E6 (↥E) i ζE) =
      torusElt Tag.E6 Ω i (Units.map E.subtype.toMonoidHom ζE) := by
    intro i
    let j : Fin (Tag.rank .E6) := i
    change baseChangeGL E.subtype (torusElt Tag.E6 (↥E) j ζE) =
      torusElt Tag.E6 Ω j (Units.map E.subtype.toMonoidHom ζE)
    rw [baseChangeGL_torusElt]
  have hû : ∀ i, ((e6Isogeny E (scBase ι (û i)) : ↥(adjointGroup Tag.E6 E)) :
        ModGL Tag.E6 E) =
      (gE' : ModGL Tag.E6 E) * weylElt Tag.E6 E i 1 * (gE' : ModGL Tag.E6 E)⁻¹ := by
    intro i
    apply baseChangeGL_injective (τ := Tag.E6) (f := E.subtype)
    rw [hstep3 (û i), hûq i, hD.nb_eq i, map_mul, map_mul, map_inv,
      hw6 i, hgEeq]
  have hb : ∀ i, ((e6Isogeny E (scBase ι (b i)) : ↥(adjointGroup Tag.E6 E)) :
        ModGL Tag.E6 E) =
      (gE' : ModGL Tag.E6 E) * torusElt Tag.E6 E i ζE * (gE' : ModGL Tag.E6 E)⁻¹ := by
    intro i
    apply baseChangeGL_injective (τ := Tag.E6) (f := E.subtype)
    rw [hstep3 (b i), hbq i, hreq i, map_mul, map_mul, map_inv,
      ht6 i, hζE_coe, hgEeq]
  have hFcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 :=
    card_galoisField_two_mul 2 n hn
  have hF3 : 3 ∣ Nat.card (GaloisField 2 (2 * n)) - 1 := by
    rw [hFcard]
    obtain ⟨m, hm⟩ := h3
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac]
    exact ⟨(2 ^ n - 1) * m, by rw [hm]; ring⟩
  obtain ⟨hcomm, hiso, hker⟩ :=
    zl_hat_core ι hF3 ζE hζE3 hζEo gE'
      (fun i => (û i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))))
      (fun i => (b i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))) hû hb
  let ĥ : Fin 6 → twistedE6Group 2 n := fun i => ⁅û i, b i⁆
  have hcoe : ∀ i, ((ĥ i : twistedE6Group 2 n) :
        ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) =
      ⁅(û i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))),
        (b i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))⁆ := by
    intro i
    rfl
  have hV0 : ∀ i, q (ĥ i) ∈ D.V0 := by
    intro i
    refine tFrame_mem_V0_of_baseChange hn hK σ hσ Fr hFr hζ hD i (q (ĥ i)) ?_
    rw [← hstep3 (ĥ i), hcoe i, hiso i]
    rw [map_mul, map_mul, map_inv, ht6 i, hζE_coe, hgEeq]
  have hcommu : ∀ i, ⁅û i, ĥ i⁆ = ĥ i := by
    intro i
    apply Subtype.ext
    have hcm : ((⁅û i, ĥ i⁆ : twistedE6Group 2 n) :
        ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) =
        ⁅(û i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))),
          (ĥ i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))⁆ := rfl
    rw [hcm, hcoe i]
    exact hcomm i
  have hker_le : q.ker ≤ Subgroup.closure (Set.range ĥ) := by
    intro z hz
    let H : Subgroup (↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) :=
      CFSG.LieType.Steinberg.TwistedE6.fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)
    have hzq : q z = 1 := MonoidHom.mem_ker.1 hz
    have hzpi : e6Isogeny (GaloisField 2 (2 * n))
        (z : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) = 1 := by
      have hq1 : baseChangeGL (algebraMap K Ω)
          ((q z : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
            ModGL TwistTag.E6.tag K) = 1 := by
        rw [congrArg Subtype.val hzq]
        exact map_one (baseChangeGL (algebraMap K Ω))
      have h := hqb z
      rw [hq1] at h
      apply Subtype.ext
      apply baseChangeGL_injective (τ := TwistTag.E6.tag) (f := (algebraMap K Ω).comp τ.toRingHom)
      have h1 : baseChangeGL ((algebraMap K Ω).comp τ.toRingHom)
          (1 : ModGL TwistTag.E6.tag (GaloisField 2 (2 * n))) = 1 := map_one _
      exact h.symm.trans h1.symm
    have hzcl := hker (z : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) hzpi
    have himg : (Subgroup.subtype H) '' Set.range ĥ =
        Set.range (fun i => ⁅(û i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))),
          (b i : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n))))⁆) := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hcoe i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ĥ i, ⟨i, rfl⟩, hcoe i⟩
    have hzmap : (z : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) ∈
        (Subgroup.closure (Set.range ĥ)).map (Subgroup.subtype H) := by
      rw [MonoidHom.map_closure, himg]
      exact hzcl
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hzmap
    have hwz' : w = z := Subtype.ext hwz
    rwa [hwz'] at hw
  exact ⟨q, û, ĥ, hqsurj, hqcenter, hûq, hV0, hcommu, hker_le⟩

end CFSG.StandardType.E6Dep.ZL

end
