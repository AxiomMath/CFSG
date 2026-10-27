module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenConj
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Step
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Torus
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Glue
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof

theorem iSup_phiTwoComp_eq_top_E7
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .E7} (hlong : ExcIsLongest .E7 w)
    {g0 : ModGL .E7 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .E7 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp g0 γ.1) = ⊤ := by
  classical
  haveI hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI hFinG : Finite (adjointGroup .E7 K) := inferInstance
  set w0 : WeylGroup .E7 :=
    (coxeterSystem .E7).wordProd ((RootOps.longestWord .E7).map (Tag.idx .E7)) with hw0
  have w0_smul_single : ∀ i : Fin Tag.E7.rank,
      w0 • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) = -Pi.single i 1 := by
    intro i
    fin_cases i <;> (rw [hw0, wordProd_smul] <;> decide +kernel)
  have w0_neg : ∀ v : Fin Tag.E7.rank → ℤ, w0 • v = -v := by
    intro v
    have h : CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan .E7) w0 =
        -LinearMap.id := by
      refine LinearMap.pi_ext fun i x => ?_
      rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
        w0_smul_single i]
      simp
    have hv := congrArg (fun f : Module.End ℤ (Fin Tag.E7.rank → ℤ) => f v) h
    simpa [smul_def] using hv
  have hneg : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ → w • γ = -γ := by
    have hw : w = w0 := by
      refine ReversesSigns.eq ?_ ?_
      · intro α hα hpos
        refine (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j => ?_
        exact hlong α hα ((IsRoot.height_pos_iff hα).1 hpos) j
      · intro α hα hpos
        rw [w0_neg, height_neg]
        omega
    intro γ hγ
    rw [hw, w0_neg]
  have hcent : ∀ u : WeylGroup .E7, u * w = w * u := by
    intro u
    refine ext_single fun i => ?_
    change (u * w) • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) =
      (w * u) • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)
    rw [mul_smul, mul_smul, hneg (Pi.single i 1) (isRoot_single .E7 i), smul_neg,
      hneg (u • Pi.single i 1) (IsRoot.smul (isRoot_single .E7 i) u)]
  obtain ⟨h, z, hz, hg0z⟩ := exists_mul_eq_kernelGroup (τ := .E7) e7ChiC hFr (hrat_E7 hFr)
    hg0C hg0 (canonicalRep_mem_kernelGroup_e7ChiC (AlgebraicClosure K) hneg)
  set Mz : Subgroup (adjointGroup .E7 K) :=
    ⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp z γ.1 with hMz
  have hMg0 : (⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp g0 γ.1) =
      Mz.map (MulAut.conj h).toMonoidHom := by
    rw [hg0z, hMz]
    exact iSup_phiTwoComp_baseChange_mul h z
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨fv, -, hfv⟩ := FiniteField.card K 2
  have hfK : Nat.card K = 2 ^ (fv : ℕ) := by rw [Nat.card_eq_fintype_card, hfv]
  set p := Nat.minFac (Nat.card K + 1) with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpq : p ∣ Nat.card K + 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card K + 1 := h2 ▸ hpq
    have hfv0 : (fv : ℕ) ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hfK
      omega
    have h2q : 2 ∣ Nat.card K := by
      rw [hfK]
      exact dvd_pow_self 2 hfv0
    have h3 : 2 ∣ (Nat.card K + 1) - Nat.card K := Nat.dvd_sub h2dvd h2q
    rw [Nat.add_sub_cancel_left] at h3
    exact absurd h3 (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_orderOf_eq_of_dvd_add_one K
      (L := AlgebraicClosure K) (N := p) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hzC : z ∈ adjointGroup .E7 (AlgebraicClosure K) :=
    torus_sup_rootSpan_le_adjointGroup (kernelRoots e7ChiC) hz
  have hbaseh : Units.map (entrywiseHom Fr)
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .E7 K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .E7 K) :=
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (h : ModGL .E7 K)
  have hzLang : Units.map (entrywiseHom Fr) z =
      z * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w := by
    have h1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .E7 K) *
        Units.map (entrywiseHom Fr) z =
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .E7 K) * z) *
          canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w := by
      have h2 := hg0
      rw [hg0z, map_mul, hbaseh] at h2
      exact h2
    rw [mul_assoc] at h1
    exact mul_left_cancel h1
  have hzA : z ∈ phiTwoA1D6Subgroup (AlgebraicClosure K) :=
    kernelGroup_e7ChiC_le_phiTwoA1D6Subgroup (AlgebraicClosure K) hz
  obtain ⟨T, hTinj, hTcoe⟩ :=
    exists_phiTwoTorus_of_neg (n := p) hpq hFr (hrat_E7 hFr) hneg hzC hzLang hζo hζ
  obtain ⟨hV6, hV1, hθ⟩ :=
    e7_torus_of_mem_phiTwoA1D6Subgroup hp2 hpq hzC hzA hζo hζ hTcoe
  have hA_le : e7A1D6 K ≤ Mz := by
    rw [hMz]
    exact e7A1D6_le_iSup_phiTwoComp hK4 hp2 hpq hzC hζo hζ hTcoe hTinj hV6 hV1 hθ
  set nv : ModGL .E7 (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem .E7) (AlgebraicClosure K)
      ((coxeterSystem .E7).wordProd e7Word) with hnv
  set nw : ModGL .E7 (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w with hnw
  set N : adjointGroup .E7 K := weylWordElt .E7 K e7Word with hN
  have hNbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (N : ModGL .E7 K) = nv := by
    rw [hN, hnv]
    have hcoeeq : ((weylWordElt .E7 K e7Word : adjointGroup .E7 K) : ModGL .E7 K) =
        (e7Word.map (fun i => weylElt .E7 K i 1)).prod := by
      rw [weylWordElt]
      exact map_list_prod (Subgroup.subtype (adjointGroup .E7 K))
        (e7Word.map (weylElement .E7 K))
    have hnv_eq : canonicalRep (coxeterSystem .E7) (AlgebraicClosure K)
          ((coxeterSystem .E7).wordProd e7Word) =
        (e7Word.map (fun i => weylElt .E7 (AlgebraicClosure K) i 1)).prod :=
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo
        (τ := .E7) (M := AlgebraicClosure K) e7Word
    rw [hcoeeq, hnv_eq, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ =>
      baseChangeGL_weylElt_one (τ := .E7) (algebraMap K (AlgebraicClosure K)) i)
  have hnv_adj : nv ∈ adjointGroup .E7 (AlgebraicClosure K) :=
    canonicalRep_mem_adjointGroup (coxeterSystem .E7) (AlgebraicClosure K)
      ((coxeterSystem .E7).wordProd e7Word)
  have hnv_fixed : Units.map (entrywiseHom Fr) nv = nv := by
    rw [hnv]
    exact CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (τ := .E7) Fr
      ((coxeterSystem .E7).wordProd e7Word)
  have hnw_nv : nw * nv = nv * nw := by
    have h1 := CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo
      (τ := .E7) (M := AlgebraicClosure K) w ((coxeterSystem .E7).wordProd e7Word)
    have h2 := CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo
      (τ := .E7) (M := AlgebraicClosure K) ((coxeterSystem .E7).wordProd e7Word) w
    have h3 : w * ((coxeterSystem .E7).wordProd e7Word) =
        ((coxeterSystem .E7).wordProd e7Word) * w := (hcent _).symm
    rw [← h1, ← h2, h3]
  set hv : ModGL .E7 (AlgebraicClosure K) := z * nv * z⁻¹ with hhv
  have hhv_adj : hv ∈ adjointGroup .E7 (AlgebraicClosure K) := by
    rw [hhv]
    exact mul_mem (mul_mem hzC hnv_adj) (inv_mem hzC)
  have hv_fixed : Units.map (entrywiseHom Fr) hv = hv := by
    rw [hhv, map_mul, map_mul, map_inv, hzLang, hnv_fixed]
    have hc : nw * nv * nw⁻¹ = nv := by rw [hnw_nv]; group
    calc (z * nw) * nv * (z * nw)⁻¹ = z * (nw * nv * nw⁻¹) * z⁻¹ := by group
      _ = z * nv * z⁻¹ := by rw [hc]
  have hNfin : IsOfFinOrder N := isOfFinOrder_of_finite N
  have hv_pow : hv ^ orderOf N = 1 := by
    have hbN_pow : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (N : ModGL .E7 K)) ^
        orderOf N = 1 := by
      rw [← map_pow (baseChangeGL (algebraMap K (AlgebraicClosure K))),
        ← Subgroup.coe_pow, pow_orderOf_eq_one N]
      simp
    rw [hhv, ← hNbase]
    change ((MulAut.conj z).toMonoidHom
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (N : ModGL .E7 K))) ^ orderOf N = 1
    rw [← map_pow (MulAut.conj z).toMonoidHom, hbN_pow, map_one]
  have hfo : IsOfFinOrder hv :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf N, hNfin.orderOf_pos, hv_pow⟩
  have hv_fin : Finite (Subgroup.zpowers hv) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hfo.orderOf_pos.ne')
  have hzpow_adj : Subgroup.zpowers hv ≤ adjointGroup .E7 (AlgebraicClosure K) :=
    Subgroup.zpowers_le.mpr hhv_adj
  have hzpow_fixed : ∀ x ∈ Subgroup.zpowers hv, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, hv_fixed]
  have hmem : Subgroup.zpowers hv ≤
      (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    hrat_E7 hFr (Subgroup.zpowers hv) hv_fin hzpow_adj hzpow_fixed
  obtain ⟨h', hh'⟩ : ∃ h' : adjointGroup .E7 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (h' : ModGL .E7 K) = hv := by
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (hmem (Subgroup.mem_zpowers hv))
    exact ⟨⟨x, hx⟩, hxeq⟩
  have hMznv : (⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ},
      phiTwoComp (z * nv) γ.1) = Mz := by
    rw [hMz]
    exact iSup_phiTwoComp_mul_canonicalRep z ((coxeterSystem .E7).wordProd e7Word)
  have hMbaz : (⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ},
      phiTwoComp (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h' : ModGL .E7 K) * z)
        γ.1) = Mz.map (MulAut.conj h').toMonoidHom := by
    rw [hMz]
    exact iSup_phiTwoComp_baseChange_mul h' z
  have hbaz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (h' : ModGL .E7 K) * z =
      z * nv := by
    rw [hh', hhv]
    group
  have hMinv : Mz.map (MulAut.conj h').toMonoidHom = Mz := by
    rw [← hMbaz, hbaz, hMznv]
  have h_le : (e7A1D6 K).map (MulAut.conj h').toMonoidHom ≤ Mz := by
    calc (e7A1D6 K).map (MulAut.conj h').toMonoidHom
        ≤ Mz.map (MulAut.conj h').toMonoidHom := Subgroup.map_mono hA_le
      _ = Mz := hMinv
  set u : adjointGroup .E7 K := N⁻¹ * h' with hu
  have hker : kernelRoots (maskChar (τ := .E7) e7BitsTheta) = e7A1D6Roots := by
    ext α
    rw [mem_kernelRoots_maskChar]
    have hpair : maskPairing e7BitsTheta α = α 0 := by simp [maskPairing, e7BitsTheta]
    rw [hpair]
    rfl
  have hu_base : baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) ∈
      torusGroup .E7 (AlgebraicClosure K) ⊔
        rootSpan .E7 (AlgebraicClosure K)
          (kernelRoots (maskChar (τ := .E7) e7BitsTheta)) := by
    rw [hker]
    have hzconj : z ∈ (phiTwoA1D6Subgroup (AlgebraicClosure K)).map
        (MulAut.conj nv).toMonoidHom :=
      kernelGroup_e7ChiC_le_conj (AlgebraicClosure K) hz
    have hnvz : nv⁻¹ * z * nv ∈ phiTwoA1D6Subgroup (AlgebraicClosure K) := by
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hzconj
      have : nv⁻¹ * z * nv = a := by
        rw [← haeq]
        change nv⁻¹ * (nv * a * nv⁻¹) * nv = a
        group
      rw [this]; exact ha
    have hbaseu : baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) =
        (nv⁻¹ * z * nv) * z⁻¹ := by
      have hcoe : (u : ModGL .E7 K) = (N : ModGL .E7 K)⁻¹ * (h' : ModGL .E7 K) := by
        rw [hu, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe, map_mul, map_inv, hNbase, hh', hhv]
      group
    rw [hbaseu]
    exact Subgroup.mul_mem _ hnvz (Subgroup.inv_mem _ hzA)
  have hu_phi : (u : ModGL .E7 K) ∈ phiTwoA1D6Subgroup K := by
    have h := mem_torus_sup_rootSpan_of_baseChangeGL_mem (K := K) (L := AlgebraicClosure K)
      (algebraMap K (AlgebraicClosure K)) (maskChar (τ := .E7) e7BitsTheta) u.2 hu_base
    rw [hker] at h
    exact h
  have hu_mem : u ∈ e7A1D6 K := by
    have hmap : (u : ModGL .E7 K) ∈ (e7A1D6 K).map (adjointGroup .E7 K).subtype := by
      rw [← phiTwoA1D6Subgroup_eq_e7A1D6]
      exact hu_phi
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp hmap
    have hxueq : x = u := Subtype.ext hxu
    rwa [hxueq] at hx
  have hAu : (e7A1D6 K).map (MulAut.conj u).toMonoidHom = e7A1D6 K := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu_mem hy) (Subgroup.inv_mem _ hu_mem)
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu_mem) hx) hu_mem
      · change u * (u⁻¹ * x * u) * u⁻¹ = x
        group
  have eh : h' = N * u := by
    rw [hu]; group
  have hAconj : (e7A1D6 K).map (MulAut.conj h').toMonoidHom =
      (e7A1D6 K).map (MulAut.conj N).toMonoidHom := by
    rw [eh, mulAut_conj_mul_toMonoidHom, ← Subgroup.map_map, hAu]
  have hn : (e7A1D6 K).map (MulAut.conj N).toMonoidHom ≤ Mz := by
    rw [← hAconj]; exact h_le
  have hztop : Mz = ⊤ :=
    eq_top_of_e7A1D6_le_of_conj_le Mz hA_le (by simpa only [hN] using hn)
  rw [hMg0, hztop]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective

theorem phiTwoGenAt_E7
    : PhiTwoGenAt .E7 :=
  fun _ _ _ _ hK _ _ _ hlong hFr hg0C hg0 => iSup_phiTwoComp_eq_top_E7 hK hFr hlong hg0C hg0

end CFSG.StandardType.PhiTwoRootGen

end
