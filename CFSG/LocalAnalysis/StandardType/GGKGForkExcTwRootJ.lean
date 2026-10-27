module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootDefs
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

private theorem ggKGTj_smul_zsmul (w : WeylGroup TwistTag.E6.tag) (n : ℤ)
    (x : Fin TwistTag.E6.tag.rank → ℤ) : w • (n • x) = n • (w • x) :=
  AddMonoidHom.map_zsmul (DistribMulAction.toAddMonoidEnd (WeylGroup TwistTag.E6.tag)
    (Fin TwistTag.E6.tag.rank → ℤ) w) n x

private noncomputable def ggKGTj_w0 : WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd ((RootOps.longestWord TwistTag.E6.tag).map
    (TwistTag.E6.tag).idx)

private theorem ggKGTj_w0_smul_single
    (i : Fin TwistTag.E6.tag.rank) :
    ggKGTj_w0 • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      -Pi.single (TwistTag.E6.perm i) 1 := by
  rw [ggKGTj_w0, wordProd_smul]
  funext j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem ggKGTj_w0_reversesSigns :
    ReversesSigns ggKGTj_w0 := by
  have hsingle : ∀ i : Fin TwistTag.E6.tag.rank,
      height (ggKGTj_w0 • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) < 0 := by
    intro i
    rw [ggKGTj_w0_smul_single i]
    rw [height]
    simp
  intro α hα hpos
  exact height_smul_neg_of_forall_single hsingle hα hpos

private theorem ggKGTj_reversesSigns_of_excIsLongest
    {w : WeylGroup TwistTag.E6.tag}
    (hw : ExcIsLongest TwistTag.E6.tag w) : ReversesSigns w := by
  intro α hα hpos
  exact (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j =>
    hw α hα ((IsRoot.height_pos_iff hα).1 hpos) j

private theorem ggKGTj_w0_smul
    (β : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTj_w0 • β = -permLattice TwistTag.E6.perm β := by
  conv_lhs => rw [show β = ∑ i, β i • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) from by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Pi.smul_apply]
      simp [Pi.single_apply, hi]
    · intro hj
      simp at hj]
  rw [Finset.smul_sum]
  simp only [ggKGTj_smul_zsmul, ggKGTj_w0_smul_single, smul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [permLattice]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single (TwistTag.E6.perm.symm j)]
  · simp [Pi.smul_apply]
  · intro x _ hx
    have hpx : TwistTag.E6.perm x ≠ j := fun h => hx (by rw [← h, Equiv.symm_apply_apply])
    simp [Pi.smul_apply, Pi.single_apply, hpx]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem ggKGTj_perm_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by
  ext i
  fin_cases i <;> decide +kernel

private theorem ggKGTj_smul_permLattice
    (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTj_w0 • permLattice TwistTag.E6.perm γ = -γ := by
  rw [ggKGTj_w0_smul]
  have h := permLattice_symm_permLattice (π := TwistTag.E6.perm) γ
  rw [ggKGTj_perm_symm] at h
  rw [h]

private theorem ggKGTj_twistHom_pinnedX
    {K : Type} [Field K] [CharP K 2] (σ : K →+* K)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (c : K) :
    twistHom TwistTag.E6 K σ (pinnedX TwistTag.E6.tag K α c) =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) (σ c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.E6 hα
  have hσ : Units.map (entrywiseHom σ) (pinnedX TwistTag.E6.tag K α c) =
      pinnedX TwistTag.E6.tag K α (σ c) := Units.ext (entrywise_pinnedX σ α c)
  rw [twistHom_apply, hσ, h (σ c),
    CFSG.RankThree.Chevalley.eq_one_of_mul_self_eq_one_of_charTwo hε, one_mul]

private theorem ggKGTj_WSL_mul_uSL_mul_WSL {K : Type} [Field K] [CharP K 2] (c : K) :
    WSL * uSL c * WSL = (vSL c : SL2 K) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem ggKGTj_WSL_mul_vSL_mul_WSL {K : Type} [Field K] [CharP K 2] (c : K) :
    WSL * vSL c * WSL = (uSL c : SL2 K) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem ggKGTj_WSL_mul_self {K : Type} [Field K] [CharP K 2] :
    (WSL : SL2 K) * WSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem ggKGTj_WSL_inv {K : Type} [Field K] [CharP K 2] :
    (WSL : SL2 K)⁻¹ = WSL :=
  inv_eq_of_mul_eq_one_right ggKGTj_WSL_mul_self

private theorem ggKGTj_conj_WSL_apply {K : Type} [Field K] [CharP K 2] (y : SL2 K) :
    (MulAut.conj WSL).toMonoidHom y = WSL * y * WSL := by
  show WSL * y * WSL⁻¹ = WSL * y * WSL
  rw [ggKGTj_WSL_inv]

private theorem ggKGTj_step_rootSL2
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (M : SL2 (AlgebraicClosure K)) :
    ggKGTwStep F (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ M) =
      rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ
        (WSL * Matrix.SpecialLinearGroup.map F.Fr M * WSL) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hv0 : F.v = ggKGTj_w0 :=
    (ggKGTj_reversesSigns_of_excIsLongest hv).eq ggKGTj_w0_reversesSigns
  have h2L : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero (AlgebraicClosure K) 2
  have h : (ggKGTwStep F).comp (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ) =
      (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ).comp
        ((MulAut.conj WSL).toMonoidHom.comp (Matrix.SpecialLinearGroup.map F.Fr)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := AlgebraicClosure K)) ?_
    intro g hg
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Upper (AlgebraicClosure K) c =
          (uSL c : SL2 (AlgebraicClosure K)) from rfl]
      simp only [MonoidHom.comp_apply, ggKGTj_conj_WSL_apply]
      rw [CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hγ c]
      rw [show ggKGTwStep F (pinnedX TwistTag.E6.tag (AlgebraicClosure K) γ c) =
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
            twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
              (pinnedX TwistTag.E6.tag (AlgebraicClosure K) γ c) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ from rfl]
      rw [ggKGTj_twistHom_pinnedX F.Fr hγ c]
      rw [CFSG.LieType.Chevalley.map_uSL, ggKGTj_WSL_mul_uSL_mul_WSL,
        CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hγ (F.Fr c)]
      rw [hv0]
      rw [CFSG.LieType.Chevalley.canonicalRep_mul_pinnedX_mul_inv_of_two h2L ggKGTj_w0
        (hγ.permLattice TwistTag.E6.cartan_perm) (F.Fr c)]
      rw [ggKGTj_smul_permLattice γ]
    · rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Lower (AlgebraicClosure K) c =
          (vSL c : SL2 (AlgebraicClosure K)) from rfl]
      simp only [MonoidHom.comp_apply, ggKGTj_conj_WSL_apply]
      rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hγ c]
      rw [show ggKGTwStep F (pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-γ) c) =
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
            twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
              (pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-γ) c) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ from rfl]
      rw [ggKGTj_twistHom_pinnedX F.Fr (IsRoot.neg hγ) c, permLattice_neg]
      rw [CFSG.LieType.Chevalley.map_vSL, ggKGTj_WSL_mul_vSL_mul_WSL,
        CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hγ (F.Fr c)]
      rw [hv0]
      rw [CFSG.LieType.Chevalley.canonicalRep_mul_pinnedX_mul_inv_of_two h2L ggKGTj_w0
        (IsRoot.neg (hγ.permLattice TwistTag.E6.cartan_perm)) (F.Fr c)]
      rw [smul_neg, ggKGTj_smul_permLattice γ, neg_neg]
  have hM := congrArg (fun f : SL2 (AlgebraicClosure K) →*
    ModGL TwistTag.E6.tag (AlgebraicClosure K) => f M) h
  simpa only [MonoidHom.comp_apply, ggKGTj_conj_WSL_apply] using hM


private theorem ggKGTj_mem_image_of_sq_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {r : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hr : r ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hrF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr r = r) (hr2 : r * r = 1) :
    r ∈ (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hc : Nat.card K = 1 := by rw [hK, hn0]; norm_num
    haveI : Fintype K := Fintype.ofFinite K
    have : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      Nat.prime_two hn1 K hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  have hder' : ⁅CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
      CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := hder
  set R := CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr with hR
  set C' := (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))
    with hC'
  have hle : C' ≤ R := by
    rw [← hder']
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder', h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]; infer_instance
  haveI : (C'.subgroupOf R).Normal := hnormal
  have hrR : r ∈ R := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
    ⟨hr, hrF⟩
  let P : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) := Subgroup.zpowers r
  have hPR : P ≤ R := Subgroup.zpowers_le.2 hrR
  have hr2' : r ^ 2 = 1 := by rwa [pow_two]
  have hPfin : Finite P := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hr2') Nat.prime_two.pos).ne')
  haveI : Finite P := hPfin
  have hPp : IsPGroup 2 P := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hr2') with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hPC' : P ≤ C' :=
    le_of_isPGroup_of_index_eq_pow hPR Nat.prime_two Nat.prime_three (by norm_num) hk hPp
  exact hPC' (Subgroup.mem_zpowers r)

private theorem ggKGTj_mem_range_of_sq_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E)
    {y : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hyG : y ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hyF : ggKGTwStep F y = y) (hy2 : y * y = 1) :
    y ∈ (ggKGTwY F).range := by
  set nv := canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v with hnv
  set x : ModGL TwistTag.E6.tag (AlgebraicClosure K) := F.g0 * y * F.g0⁻¹ with hx
  have hxC : x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem F.g0_mem hyG) (inv_mem F.g0_mem)
  have hyF' : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr y = nv⁻¹ * y * nv := by
    have h := hyF
    rw [show ggKGTwStep F y = nv * twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr y * nv⁻¹
      from rfl] at h
    calc twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr y
        = nv⁻¹ * (nv * twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr y * nv⁻¹) * nv := by group
      _ = nv⁻¹ * y * nv := by rw [h]
  have hxF : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr x = x := by
    rw [hx, map_mul, map_mul, map_inv, F.lang, hyF', ← hnv]
    group
  have hx2 : x * x = 1 := by
    rw [hx]
    calc (F.g0 * y * F.g0⁻¹) * (F.g0 * y * F.g0⁻¹)
        = F.g0 * (y * y) * F.g0⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  obtain ⟨r, hrC, hrx⟩ := Subgroup.mem_map.1
    (ggKGTj_mem_image_of_sq_one hK hσ F.Fr F.fr_eq hxC hxF hx2)
  refine ⟨⟨r, hrC⟩, ?_⟩
  rw [ggKGTwY_apply, hrx, hx]
  group


private theorem ggKGTj_pinnedData_of_not_isRoot
    {γ : Fin Tag.E6.rank → ℤ} (hγ : ¬ IsRoot Tag.E6 γ) :
    pinnedData Tag.E6 γ = (0, [], 1) := by
  classical
  have h1 : ¬ ∃ j, γ = Pi.single j 1 := by
    rintro ⟨j, rfl⟩
    exact hγ (isRoot_single Tag.E6 j)
  have h2 : ¬ ∃ j, γ = -Pi.single j 1 := by
    rintro ⟨j, rfl⟩
    exact hγ (IsRoot.neg (isRoot_single Tag.E6 j))
  simp only [pinnedData, dif_neg h1, dif_neg h2]
  have hfind : (Tag.E6.witnesses.roots.findIdx
      (fun c => decide (decodeVec (τ := Tag.E6) c = γ))) =
      Tag.E6.witnesses.roots.length := by
    apply Nat.le_antisymm (List.findIdx_le_length)
    by_contra h
    rw [not_le] at h
    obtain ⟨x, hx, hpx⟩ := (List.findIdx_lt_length).1 h
    rw [decide_eq_true_eq] at hpx
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hx
    have hroot : IsRoot Tag.E6 (decodeVec (Tag.E6.witnesses.roots[b])) := by
      rw [← List.getD_eq_getElem Tag.E6.witnesses.roots 0 hb]
      exact CFSG.LieType.Chevalley.isRoot_decodeVec_witness (τ := Tag.E6) hb
    exact hγ (hpx ▸ hroot)
  rw [hfind]
  have hs : Tag.E6.witnesses.seeds.length = Tag.E6.witnesses.roots.length := rfl
  have hw : Tag.E6.witnesses.words.length = Tag.E6.witnesses.roots.length := rfl
  rw [List.getD_eq_default _ _ (by rw [hs]), List.getD_eq_default _ _ (by rw [hw])]
  constructor <;> simp [Tag.idx, decodeWord]

private theorem ggKGTj_rootSL2_of_not_isRoot
    {K : Type} [Field K] {γ : Fin Tag.E6.rank → ℤ} (hγ : ¬ IsRoot Tag.E6 γ) :
    rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ =
      rootSL2 TwistTag.E6.tag (AlgebraicClosure K) (Pi.single (0 : Fin Tag.E6.rank) 1) := by
  have hpd := ggKGTj_pinnedData_of_not_isRoot hγ
  have hpd0 : pinnedData Tag.E6 (Pi.single (0 : Fin Tag.E6.rank) 1) = (0, [], 1) :=
    pinnedData_single 0
  have hpd' : pinnedData TwistTag.E6.tag γ = (0, [], 1) := hpd
  have hpd0' : pinnedData TwistTag.E6.tag (Pi.single (0 : Fin Tag.E6.rank) 1) = (0, [], 1) := hpd0
  have hw : pinnedWeyl TwistTag.E6.tag (AlgebraicClosure K) γ = 1 := by
    simp only [pinnedWeyl]
    rw [hpd']
    rfl
  have hw0 : pinnedWeyl TwistTag.E6.tag (AlgebraicClosure K)
      (Pi.single (0 : Fin Tag.E6.rank) 1) = 1 := by
    simp only [pinnedWeyl]
    rw [hpd0']
    rfl
  unfold rootSL2
  rw [hpd', hpd0', hw, hw0]

private theorem ggKGTj_Lhat_of_not_isRoot
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : ¬ IsRoot Tag.E6 γ) :
    ggKGTwLhat F γ = ggKGTwLhat F (Pi.single (0 : Fin Tag.E6.rank) 1) := by
  simp only [ggKGTwLhat, CFSG.LieType.Chevalley.rootRankOneGroup, ggKGTj_rootSL2_of_not_isRoot hγ]
  rfl

private theorem ggKGTj_J_of_not_isRoot
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : ¬ IsRoot Tag.E6 γ) :
    ggKGTwJ F γ = ggKGTwJ F (Pi.single (0 : Fin Tag.E6.rank) 1) := by
  change Subgroup.comap (ggKGTwY F) (ggKGTwLhat F γ) =
    Subgroup.comap (ggKGTwY F) (ggKGTwLhat F (Pi.single (0 : Fin Tag.E6.rank) 1))
  rw [ggKGTj_Lhat_of_not_isRoot F hγ]

private theorem ggKGTj_map_eq_of_isRoot
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    (ggKGTwJ F γ).map (ggKGTwY F) = ggKGTwLhat F γ := by
  have hgen : ggKGTwLhat F γ ≤ (ggKGTwY F).range := by
    intro y hy
    rw [ggKGTwLhat] at hy
    obtain ⟨hyL, hyF⟩ := Subgroup.mem_inf.1 hy
    simp only [CFSG.LieType.Chevalley.rootRankOneGroup] at hyL
    obtain ⟨M, rfl⟩ := hyL
    have hMcond : WSL * Matrix.SpecialLinearGroup.map F.Fr M * WSL = M := by
      have h := ggKGTj_step_rootSL2 hK F hv hγ M
      exact (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
        (K := AlgebraicClosure K) (β := γ)) (h.symm.trans hyF)
    have hcl := ggKGTj_D_gen hK hσ F.Fr F.fr_eq M hMcond
    have hle : Subgroup.closure {X : SL2 (AlgebraicClosure K) | X * X = 1 ∧
        WSL * Matrix.SpecialLinearGroup.map F.Fr X * WSL = X} ≤
        Subgroup.comap (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ) ((ggKGTwY F).range) := by
      rw [Subgroup.closure_le]
      intro X hX
      refine ggKGTj_mem_range_of_sq_one hK hσ F ?_ ?_ ?_
      · exact (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_data
          TwistTag.E6.tag (AlgebraicClosure K) γ).2.2.2.2.1 X
      · rw [ggKGTj_step_rootSL2 hK F hv hγ X, hX.2]
      · rw [← map_mul, hX.1, map_one]
    exact hle hcl
  refine le_antisymm ?_ ?_
  · rw [ggKGTwJ]; exact Subgroup.map_comap_le _ _
  · rw [ggKGTwJ, Subgroup.map_comap_eq]; exact le_inf hgen le_rfl


theorem ggKGTwJ_map_eq
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (γ : Fin Tag.E6.rank → ℤ) :
    (ggKGTwJ F γ).map (ggKGTwY F) = ggKGTwLhat F γ := by
  by_cases hγ : IsRoot Tag.E6 γ
  · exact ggKGTj_map_eq_of_isRoot hK hσ F hv hγ
  · rw [ggKGTj_J_of_not_isRoot F hγ, ggKGTj_Lhat_of_not_isRoot F hγ]
    exact ggKGTj_map_eq_of_isRoot hK hσ F hv (isRoot_single Tag.E6 (0 : Fin Tag.E6.rank))

private theorem ggKGTj_Y_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    Function.Injective (ggKGTwY F) := by
  intro a b h
  have h' := congrArg (fun g : ModGL TwistTag.E6.tag (AlgebraicClosure K) =>
    F.g0 * g * F.g0⁻¹) h
  simp only [ggKGTwY_apply] at h'
  have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL TwistTag.E6.tag K) := by
    have h3 := h'
    group at h3
    exact h3
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h2)

private theorem ggKGTj_Phi_range
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {P : SL2 (AlgebraicClosure K)} (hPq : Matrix.SpecialLinearGroup.map F.Fr P = WSL * P) :
    ((rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ).comp
      (ggKGTj_phi1 F.Fr F.fr_eq P)).range = ggKGTwLhat F γ := by
  haveI : CharP (AlgebraicClosure K) 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
    exact charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  refine le_antisymm ?_ ?_
  · rintro x ⟨N, rfl⟩
    rw [ggKGTwLhat]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact ⟨ggKGTj_phi1 F.Fr F.fr_eq P N, rfl⟩
    · change ggKGTwStep F (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ
          (ggKGTj_phi1 F.Fr F.fr_eq P N)) =
        rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ (ggKGTj_phi1 F.Fr F.fr_eq P N)
      rw [ggKGTj_step_rootSL2 (M := ggKGTj_phi1 F.Fr F.fr_eq P N) hK F hv hγ,
        ggKGTj_phi1_fixed F.Fr F.fr_eq hPq N]
  · intro x hx
    rw [ggKGTwLhat] at hx
    obtain ⟨hxL, hxF⟩ := Subgroup.mem_inf.1 hx
    simp only [CFSG.LieType.Chevalley.rootRankOneGroup] at hxL
    obtain ⟨M, rfl⟩ := hxL
    have hM : WSL * Matrix.SpecialLinearGroup.map F.Fr M * WSL = M := by
      have h := ggKGTj_step_rootSL2 hK F hv hγ M
      exact (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
        (K := AlgebraicClosure K) (β := γ)) (h.symm.trans hxF)
    have hM' : Matrix.SpecialLinearGroup.map F.Fr M = WSL * M * WSL := by
      have h := congrArg (fun X => WSL * X * WSL) hM
      rw [show WSL * (WSL * Matrix.SpecialLinearGroup.map F.Fr M * WSL) * WSL =
          Matrix.SpecialLinearGroup.map F.Fr M from ?_] at h
      · exact h
      · rw [show WSL * (WSL * Matrix.SpecialLinearGroup.map F.Fr M * WSL) * WSL =
            (WSL * WSL) * Matrix.SpecialLinearGroup.map F.Fr M * (WSL * WSL) from by group,
          ggKGTj_WSL_mul_self, one_mul, mul_one]
    have hYfix : Matrix.SpecialLinearGroup.map F.Fr (P⁻¹ * M * P) = P⁻¹ * M * P := by
      rw [map_mul, map_mul, map_inv, hPq, hM']
      rw [show (WSL * P)⁻¹ = P⁻¹ * WSL by rw [mul_inv_rev, ggKGTj_WSL_inv]]
      rw [show P⁻¹ * WSL * (WSL * M * WSL) * (WSL * P) =
          P⁻¹ * (WSL * WSL) * M * (WSL * WSL) * P from by group, ggKGTj_WSL_mul_self]
      group
    obtain ⟨N, hN⟩ := ggKGTj_mem_range_mapF F.Fr F.fr_eq (P⁻¹ * M * P) hYfix
    refine ⟨N, ?_⟩
    show rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ (ggKGTj_phi1 F.Fr F.fr_eq P N) =
      rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ M
    rw [ggKGTj_phi1_apply, hN]
    group

private noncomputable def ggKGTj_SL2_equiv_Lhat
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {P : SL2 (AlgebraicClosure K)} (hPq : Matrix.SpecialLinearGroup.map F.Fr P = WSL * P) :
    SL2 ↥(ggKGTj_F F.Fr F.fr_eq) ≃* ggKGTwLhat F γ :=
  (MonoidHom.ofInjective
    (f := (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ).comp (ggKGTj_phi1 F.Fr F.fr_eq P))
    ((CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := AlgebraicClosure K) (β := γ)).comp (ggKGTj_phi1_injective F.Fr F.fr_eq P))).trans
    (MulEquiv.subgroupCongr (ggKGTj_Phi_range hK F hv hγ hPq))

private theorem ggKGTj_exists_P_and_pow
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    ∃ P : SL2 (AlgebraicClosure K), Matrix.SpecialLinearGroup.map Fr P = WSL * P := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ω₀, hω₀⟩ := ggKGTj_exists_omega hK hσ
  obtain ⟨s, hs, hss⟩ := ggKGTj_exists_s hK Fr hFr ω₀
  have hωne : Fr (algebraMap K (AlgebraicClosure K) ω₀) ≠ algebraMap K (AlgebraicClosure K) ω₀ := by
    intro h
    apply hω₀
    have h1 : algebraMap K (AlgebraicClosure K) (σ ω₀) =
        Fr (algebraMap K (AlgebraicClosure K) ω₀) := by rw [hσ, map_pow, hFr]
    exact (algebraMap K (AlgebraicClosure K)).injective (by rw [h1, h])
  have ht : algebraMap K (AlgebraicClosure K) ω₀ +
      (algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n) ≠ 0 := by
    intro h
    apply hωne
    have h2 : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero (AlgebraicClosure K) 2
    have h' : (algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n) =
        algebraMap K (AlgebraicClosure K) ω₀ := by
      linear_combination h - (algebraMap K (AlgebraicClosure K) ω₀) * h2
    rw [hFr, h']
  have hω2 : Fr ((algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n)) =
      algebraMap K (AlgebraicClosure K) ω₀ := by
    rw [hFr, ← pow_mul, show 2 ^ n * 2 ^ n = Nat.card K by rw [hK]; ring, ← map_pow,
      ggKGTj_pow_card' ω₀]
  exact ⟨ggKGTj_P hK s (algebraMap K (AlgebraicClosure K) ω₀) ht hss,
    ggKGTj_P_pow hK Fr hs (hFr _) hω2 ht hss⟩

private noncomputable def ggKGTj_J_equiv_Lhat
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (γ : Fin Tag.E6.rank → ℤ) :
    ggKGTwJ F γ ≃* ggKGTwLhat F γ :=
  (Subgroup.equivMapOfInjective (ggKGTwJ F γ) (ggKGTwY F) (ggKGTj_Y_injective F)).trans
    (MulEquiv.subgroupCongr (ggKGTwJ_map_eq hK hσ F hv γ))


theorem ggKGTwJ_quasisimple
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hq : 4 ≤ 2 ^ n) : IsQuasisimple (ggKGTwJ F γ) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite ↥(ggKGTj_F F.Fr F.fr_eq) :=
    (Nat.card_ne_zero.mp (by
      rw [ggKGTj_card_F hK hσ F.Fr F.fr_eq]
      exact pow_ne_zero n (by norm_num))).2
  obtain ⟨P, hPq⟩ := ggKGTj_exists_P_and_pow hK hσ F.Fr F.fr_eq
  refine (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((ggKGTj_J_equiv_Lhat hK hσ F hv γ).trans
      (ggKGTj_SL2_equiv_Lhat hK F hv hγ hPq).symm)).mpr ?_
  refine CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (m := 2) le_rfl ?_
  rw [ggKGTj_card_F hK hσ F.Fr F.fr_eq]
  exact hq

theorem ggKGTwJ_weyl
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ r ∈ ggKGTwJ F γ, ggKGTwY F r =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmem : rootWeylSL2 TwistTag.E6.tag (AlgebraicClosure K) γ 1 ∈ ggKGTwLhat F γ := by
    rw [ggKGTwLhat]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · change rootWeylSL2 TwistTag.E6.tag (AlgebraicClosure K) γ 1 ∈
          (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ).range
      exact ⟨WSL, by simp only [rootWeylSL2, nSL_one]⟩
    · have hwsl : rootWeylSL2 TwistTag.E6.tag (AlgebraicClosure K) γ 1 =
          rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL := by
        simp only [rootWeylSL2, nSL_one]
      rw [hwsl]
      change ggKGTwStep F (rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL) =
        rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL
      rw [ggKGTj_step_rootSL2 hK F hv hγ WSL,
        CFSG.LieType.Chevalley.map_WSL, ggKGTj_WSL_mul_self, one_mul]
  have hcanon : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ)
      ∈ ggKGTwLhat F γ :=
    (CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := AlgebraicClosure K) hγ) ▸ hmem
  rw [← ggKGTwJ_map_eq hK hσ F hv γ] at hcanon
  obtain ⟨r, hr, hrY⟩ := Subgroup.mem_map.1 hcanon
  exact ⟨r, hr, hrY⟩

theorem ggKGTwJ_dvd_card
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hpq : p ∣ 2 ^ n + 1) : p ∣ Nat.card (ggKGTwJ F γ) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite ↥(ggKGTj_F F.Fr F.fr_eq) :=
    (Nat.card_ne_zero.mp (by
      rw [ggKGTj_card_F hK hσ F.Fr F.fr_eq]
      exact pow_ne_zero n (by norm_num))).2
  obtain ⟨P, hPq⟩ := ggKGTj_exists_P_and_pow hK hσ F.Fr F.fr_eq
  have eJ : ggKGTwJ F γ ≃* SL2 ↥(ggKGTj_F F.Fr F.fr_eq) :=
    (ggKGTj_J_equiv_Lhat hK hσ F hv γ).trans (ggKGTj_SL2_equiv_Lhat hK F hv hγ hPq).symm
  rw [Nat.card_congr eJ.toEquiv, CFSG.Wreathed.CentralSL2.card_SL_two,
    ggKGTj_card_F hK hσ F.Fr F.fr_eq]
  have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h := Nat.sq_sub_sq (2 ^ n) 1
    simp only [one_pow] at h
    rw [h, mul_comm]
  rw [h1, ← mul_assoc]
  exact hpq.trans (dvd_mul_left _ _)

theorem nonempty_ggKGTwJ_mulEquiv_SL2
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nonempty (ggKGTwJ F γ ≃* SL2 ↥(ggKGTj_F F.Fr F.fr_eq)) := by
  obtain ⟨P, hPq⟩ := ggKGTj_exists_P_and_pow hK hσ F.Fr F.fr_eq
  exact ⟨(ggKGTj_J_equiv_Lhat hK hσ F hv γ).trans (ggKGTj_SL2_equiv_Lhat hK F hv hγ hPq).symm⟩

end CFSG.StandardType
