module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockA
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockD

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open scoped MatrixGroups
open Matrix


section Helpers

private theorem frobenius_algebraMap {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K) (c : K) :
    Fr (algebraMap K Ω c) = algebraMap K Ω c := by
  rw [hFr, ← map_pow]
  have hpow : c ^ Nat.card K = c := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rw [hpow]

private theorem frobE6_baseChangeGL_apply {K Ω : Type} [Field K] [Finite K] [Field Ω]
    [Algebra K Ω] {Fr : Ω →+* Ω} (hFr : ∀ c : Ω, Fr c = c ^ Nat.card K)
    (g : ModGL Tag.E6 K) :
    frobE6 Fr (baseChangeGL (algebraMap K Ω) g) = baseChangeGL (algebraMap K Ω) g := by
  unfold frobE6
  refine Units.ext ?_
  rw [Units.coe_map, coe_baseChangeGL]
  change entrywise Fr
      (baseChangeEnd (algebraMap K Ω) (g : Module.End K (RootModule Tag.E6 K))) =
    baseChangeEnd (algebraMap K Ω) (g : Module.End K (RootModule Tag.E6 K))
  unfold entrywise
  have hfam : (fun b : Label Tag.E6 => Finsupp.mapRange Fr Fr.map_zero
        (baseChangeEnd (algebraMap K Ω) (g : Module.End K (RootModule Tag.E6 K))
          (Finsupp.single b 1))) =
      (fun b : Label Tag.E6 => Finsupp.mapRange (algebraMap K Ω) (algebraMap K Ω).map_zero
        ((g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single b 1))) := by
    funext b
    rw [baseChangeEnd_single]
    apply Finsupp.ext
    intro l
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact frobenius_algebraMap hFr _
  rw [hfam]
  unfold baseChangeEnd
  rfl

private theorem zetaVec_unitsMap {K Ω : Type} [Field K] [Field Ω] (ι : K →+* Ω)
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : Units.map ι.toMonoidHom ζ ^ 3 = 1)
    (v : Fin Tag.E6.rank → ZMod 3) :
    (fun i => Units.map ι.toMonoidHom (zetaVec ζ hζ v i)) =
      zetaVec (Units.map ι.toMonoidHom ζ) hζ' v := by
  funext i
  rw [zetaVec_apply, zetaVec_apply]
  exact map_pow (Units.map ι.toMonoidHom) ζ (v i).val

private theorem mapRange_smul {K Ω : Type} [Field K] [Field Ω] (ι : K →+* Ω) (c : Kˣ)
    (v : RootModule Tag.E6 K) :
    Finsupp.mapRange ι ι.map_zero ((c : K) • v) =
      (Units.map ι.toMonoidHom c : Ω) • Finsupp.mapRange ι ι.map_zero v := by
  ext b
  simp [Finsupp.mapRange_apply, Finsupp.smul_apply, Units.coe_map]

private theorem mapRange_rootVec {K Ω : Type} [Field K] [Field Ω] (ι : K →+* Ω)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    Finsupp.mapRange ι ι.map_zero (rootVec Tag.E6 K β) = rootVec Tag.E6 Ω β := by
  rw [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot hβ]
  ext b
  simp [Finsupp.mapRange_apply]

private theorem mapsRootLines_baseChangeGL {K Ω : Type} [Field K] [Field Ω] (ι : K →+* Ω)
    {g : ModGL Tag.E6 K} {w : WeylGroup Tag.E6} (hg : MapsRootLines g w) :
    MapsRootLines (baseChangeGL ι g) w := by
  intro α hα
  obtain ⟨c, hc⟩ := hg α hα
  refine ⟨Units.map ι.toMonoidHom c, ?_⟩
  rw [rootVec_eq_single_of_isRoot hα, baseChangeGL_apply_single,
    ← rootVec_eq_single_of_isRoot hα, hc, mapRange_smul,
    mapRange_rootVec ι (IsRoot.smul hα w)]

private theorem mem_xHat_baseChangeGL {K Ω : Type} [Field K] [Field Ω] (ι : K →+* Ω)
    {S : Subgroup (WeylGroup Tag.E6)} {x : ModGL Tag.E6 K}
    (hx : x ∈ xHat Tag.E6 K S) :
    baseChangeGL ι x ∈ xHat Tag.E6 Ω S := by
  obtain ⟨hxM, hxψ⟩ := mem_xHat.mp hx
  have hmaps : MapsRootLines (baseChangeGL ι x) (psiHat Tag.E6 K ⟨x, hxM⟩) :=
    mapsRootLines_baseChangeGL ι (mapsRootLines_psiHat ⟨x, hxM⟩)
  have hxMΩ : baseChangeGL ι x ∈ monoHat Tag.E6 Ω := by
    obtain ⟨n, hn, a, rfl⟩ := hxM
    refine ⟨baseChangeGL ι n, baseChangeGL_mem_monomialSubgroup ι hn,
      fun i => Units.map ι.toMonoidHom (a i), ?_⟩
    rw [map_mul, baseChangeGL_rootDiagUnit]
  refine mem_xHat.mpr ⟨hxMΩ, ?_⟩
  rw [psiHat_eq hmaps]
  exact hxψ

private theorem conj_inv_rootDiagUnit_of_mem_monoHat {K : Type} [Field K] (x : monoHat Tag.E6 K)
    (b : Fin Tag.E6.rank → Kˣ) :
    (↑x)⁻¹ * rootDiagUnit Tag.E6 b * ↑x =
      rootDiagUnit Tag.E6 (weylTuple (psiHat Tag.E6 K x⁻¹) b) := by
  have h := conj_rootDiagUnit_of_mem_monoHat x⁻¹ b
  rw [Subgroup.coe_inv] at h
  rw [inv_inv] at h
  exact h

private theorem a2BlockSplit_i2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL Tag.E6 K)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEX : E ≤ xHat Tag.E6 K (Subgroup.zpowers (gE6 2))) :
    ∃ z ∈ hatGroup Tag.E6 K, ∀ e ∈ E, ∃ v,
      z * e * z⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
  classical
  let Ω := AlgebraicClosure K
  let ι : K →+* Ω := algebraMap K Ω
  haveI : IsAlgClosure K Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hkcard⟩ := FiniteField.card K 2
  have hk : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hkcard]
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 (n : ℕ)
  have hFr : ∀ c : Ω, Fr c = c ^ Nat.card K := by
    intro c
    show (iterateFrobenius Ω 2 (n : ℕ)) c = c ^ Nat.card K
    rw [coe_iterateFrobenius, iterate_frobenius, hk]
  have hq : (Nat.card K : Ω) = 0 := by
    rw [hk, Nat.cast_pow, CharP.cast_eq_zero Ω 2]
    exact zero_pow n.ne_zero
  have hζ' : Units.map ι.toMonoidHom ζ ^ 3 = 1 := by
    rw [← map_pow, hζ, map_one]
  have hinj : Function.Injective (Units.map ι.toMonoidHom) := by
    intro u v h
    refine Units.ext ?_
    have h1 := congrArg (fun z : Ωˣ => (z : Ω)) h
    simp only [Units.coe_map] at h1
    exact ι.injective h1
  have hζo' : orderOf (Units.map ι.toMonoidHom ζ) = 3 := by
    rw [orderOf_injective (Units.map ι.toMonoidHom) hinj ζ, hζo]
  let E' : Subgroup (ModGL Tag.E6 Ω) := E.map (baseChangeGL ι)
  have hE' : CFSG.Open.IsElemAbelian 3 E' := TableB.isElemAbelian_map hE (baseChangeGL ι)
  have hE'X : E' ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 2)) := by
    rintro _ ⟨e, he, rfl⟩
    exact mem_xHat_baseChangeGL ι (hEX he)
  have hEF : ∀ e ∈ E', frobE6 Fr e = e := by
    rintro _ ⟨e, he, rfl⟩
    exact frobE6_baseChangeGL_apply hFr e
  obtain ⟨z', hz'Q, hz'F, hz'conj⟩ :=
    a2BlockSplitInput_holds hFr hq h3 hζ' hζo' hE' hEF hE'X
  obtain ⟨y, hyQ, hyz⟩ := fixed_blockGroup_eq hFr 2 hz'Q hz'F
  refine ⟨y, ?_, ?_⟩
  · change y ∈ hatGroup Tag.E6 K
    exact adjointGroup_le_hatGroup (rootSpan_le_adjointGroup K _ hyQ)
  · intro e he
    have hmem : baseChangeGL ι e ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨v, hv⟩ := hz'conj (baseChangeGL ι e) hmem
    refine ⟨v, ?_⟩
    have hbc : baseChangeGL ι (y * e * y⁻¹) =
        rootDiagUnit Tag.E6 (zetaVec (Units.map ι.toMonoidHom ζ) hζ' v) := by
      rw [map_mul, map_mul, map_inv, hyz]
      exact hv
    have hnat : baseChangeGL ι (rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) =
        rootDiagUnit Tag.E6 (zetaVec (Units.map ι.toMonoidHom ζ) hζ' v) := by
      rw [baseChangeGL_rootDiagUnit]
      congr 1
      exact zetaVec_unitsMap ι hζ hζ' v
    exact baseChangeGL_injective ι (hbc.trans hnat.symm)

end Helpers

theorem a2BlockSplit_holds {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (i : Fin 3)
    {E : Subgroup (ModGL Tag.E6 K)} (hE : CFSG.Open.IsElemAbelian 3 E) (hEH : E ≤ hatGroup Tag.E6 K)
    (hEX : E ≤ xHat Tag.E6 K (Subgroup.zpowers (gE6 i))) :
    ∃ z ∈ hatGroup Tag.E6 K, ∀ e ∈ E, ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
  classical
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  ·
    let m : ModGL Tag.E6 K := canonicalRep (coxeterSystem Tag.E6) K cE6 ^ 2
    have hmAdj : m ∈ adjointGroup Tag.E6 K := by
      change canonicalRep (coxeterSystem Tag.E6) K cE6 ^ 2 ∈ adjointGroup Tag.E6 K
      exact pow_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) K cE6) 2
    have hmHat : m ∈ hatGroup Tag.E6 K := adjointGroup_le_hatGroup hmAdj
    have hmMono : m ∈ monomialSubgroup Tag.E6 K := by
      change canonicalRep (coxeterSystem Tag.E6) K cE6 ^ 2 ∈ monomialSubgroup Tag.E6 K
      exact pow_mem (canonicalRep_mem_monomialSubgroup K cE6) 2
    have hmMonoHat : m ∈ monoHat Tag.E6 K := monomial_le_monoHat hmMono
    have hmψ : psiHat Tag.E6 K ⟨m, hmMonoHat⟩ = cE6 ^ 2 := by
      refine psiHat_eq ?_
      change MapsRootLines (canonicalRep (coxeterSystem Tag.E6) K cE6 ^ 2) (cE6 ^ 2)
      rw [sq, sq]
      exact (mapsRootLines_canonicalRep (R := K) cE6).mul (mapsRootLines_canonicalRep (R := K) cE6)
    let E' : Subgroup (ModGL Tag.E6 K) := E.map (MulAut.conj m).toMonoidHom
    have hE' : CFSG.Open.IsElemAbelian 3 E' :=
      TableB.isElemAbelian_map hE (MulAut.conj m).toMonoidHom
    have hE'X : E' ≤ xHat Tag.E6 K (Subgroup.zpowers (gE6 2)) := by
      rintro _ ⟨e, he, rfl⟩
      have h1 := conj_mem_xHat_zpowers hmMonoHat hmψ (hEX he)
      rwa [cE6_pow_two_conj_zero] at h1
    obtain ⟨z', hz'H, hz'⟩ := a2BlockSplit_i2 h3 hζ hζo hE' hE'X
    refine ⟨m⁻¹ * z' * m, ?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hmHat) hz'H) hmHat
    · intro e he
      have hmem : m * e * m⁻¹ ∈ E' := ⟨e, he, rfl⟩
      obtain ⟨v, hv⟩ := hz' _ hmem
      refine ⟨adAct Tag.E6 3 (psiHat Tag.E6 K (⟨m, hmMonoHat⟩⁻¹)) v, ?_⟩
      have hconj : m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
          m⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * m := by
        rw [show m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
          m⁻¹ * (z' * (m * e * m⁻¹) * z'⁻¹) * m by group, hv]
      rw [hconj,
        show m⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * m =
          (↑(⟨m, hmMonoHat⟩ : monoHat Tag.E6 K))⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) *
            ↑(⟨m, hmMonoHat⟩ : monoHat Tag.E6 K) from rfl,
        conj_inv_rootDiagUnit_of_mem_monoHat, weylTuple_zetaVec]
  ·
    let m : ModGL Tag.E6 K := canonicalRep (coxeterSystem Tag.E6) K cE6
    have hmAdj : m ∈ adjointGroup Tag.E6 K := by
      change canonicalRep (coxeterSystem Tag.E6) K cE6 ∈ adjointGroup Tag.E6 K
      exact canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) K cE6
    have hmHat : m ∈ hatGroup Tag.E6 K := adjointGroup_le_hatGroup hmAdj
    have hmMono : m ∈ monomialSubgroup Tag.E6 K := by
      change canonicalRep (coxeterSystem Tag.E6) K cE6 ∈ monomialSubgroup Tag.E6 K
      exact canonicalRep_mem_monomialSubgroup K cE6
    have hmMonoHat : m ∈ monoHat Tag.E6 K := monomial_le_monoHat hmMono
    have hmψ : psiHat Tag.E6 K ⟨m, hmMonoHat⟩ = cE6 := by
      refine psiHat_eq ?_
      change MapsRootLines (canonicalRep (coxeterSystem Tag.E6) K cE6) cE6
      exact mapsRootLines_canonicalRep (R := K) cE6
    let E' : Subgroup (ModGL Tag.E6 K) := E.map (MulAut.conj m).toMonoidHom
    have hE' : CFSG.Open.IsElemAbelian 3 E' :=
      TableB.isElemAbelian_map hE (MulAut.conj m).toMonoidHom
    have hE'X : E' ≤ xHat Tag.E6 K (Subgroup.zpowers (gE6 2)) := by
      rintro _ ⟨e, he, rfl⟩
      have h1 := conj_mem_xHat_zpowers hmMonoHat hmψ (hEX he)
      rw [cE6_conj] at h1
      have hpi : TableBExc.Three.piE7 1 = 2 := rfl
      rw [hpi] at h1
      exact h1
    obtain ⟨z', hz'H, hz'⟩ := a2BlockSplit_i2 h3 hζ hζo hE' hE'X
    refine ⟨m⁻¹ * z' * m, ?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hmHat) hz'H) hmHat
    · intro e he
      have hmem : m * e * m⁻¹ ∈ E' := ⟨e, he, rfl⟩
      obtain ⟨v, hv⟩ := hz' _ hmem
      refine ⟨adAct Tag.E6 3 (psiHat Tag.E6 K (⟨m, hmMonoHat⟩⁻¹)) v, ?_⟩
      have hconj : m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
          m⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * m := by
        rw [show m⁻¹ * z' * m * e * (m⁻¹ * z' * m)⁻¹ =
          m⁻¹ * (z' * (m * e * m⁻¹) * z'⁻¹) * m by group, hv]
      rw [hconj,
        show m⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * m =
          (↑(⟨m, hmMonoHat⟩ : monoHat Tag.E6 K))⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) *
            ↑(⟨m, hmMonoHat⟩ : monoHat Tag.E6 K) from rfl,
        conj_inv_rootDiagUnit_of_mem_monoHat, weylTuple_zetaVec]
  ·
    exact a2BlockSplit_i2 h3 hζ hζo hE hEX

end CFSG.StandardType.E6ThreeModel
