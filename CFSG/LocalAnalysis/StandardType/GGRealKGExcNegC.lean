module

public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegJ
public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootC
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality


private theorem ggRKC_exists_rootDiagUnit_of_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] {g : ModGL τ L} (hg : g ∈ torusGroup τ L) :
    ∃ b : Fin τ.rank → Lˣ, rootDiagUnit τ b = g := by
  refine Subgroup.closure_induction (p := fun g _ => ∃ b : Fin τ.rank → Lˣ, rootDiagUnit τ b = g)
    ?_ ?_ ?_ ?_ hg
  · rintro x ⟨⟨i, u⟩, rfl⟩
    exact ⟨fun j => u ^ τ.cartan i j, (torusElt_eq_rootDiagUnit i u).symm⟩
  · exact ⟨1, rootDiagUnit_one⟩
  · rintro x y _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b * c, by rw [rootDiagUnit_mul]⟩
  · rintro x _ ⟨b, rfl⟩
    exact ⟨b⁻¹, map_inv (rootDiagUnitHom τ L) b⟩

private theorem ggRKC_rootChar_pow
    {τ : Tag} {L : Type} [Field L] (b : Fin τ.rank → Lˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (b ^ n) v = (rootChar b v) ^ n := by
  simp only [rootChar, Pi.pow_apply]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast (b i) n, ← zpow_natCast (b i ^ (v i)) n, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

private theorem ggRKC_weylTuple_rootReflection
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {b : Fin τ.rank → Lˣ} (hχ : rootChar b γ = 1) :
    weylTuple (rootReflection γ) b = b := by
  funext i
  rw [weylTuple, inv_eq_of_mul_eq_one_right (rootReflection_mul_self hγ),
    rootReflection_smul hγ (Pi.single i 1), rootChar_sub, rootChar_zsmul, hχ, one_zpow,
    inv_one, mul_one]
  simpa using rootChar_nsmul_single b i 1

private theorem ggRKC_rootSpan_pair
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootRankOneGroup τ L γ = rootSpan τ L ({γ, -γ} : Set (Fin τ.rank → ℤ)) := by
  have hpair : rootSpan τ L ({γ, -γ} : Set (Fin τ.rank → ℤ)) =
      rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
    apply le_antisymm
    · rw [rootSpan]
      refine iSup_le fun α => iSup_le fun hα => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
      rcases hα with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · refine sup_le ?_ ?_
      · exact le_iSup_of_le γ (le_iSup_of_le (by simp) le_rfl)
      · exact le_iSup_of_le (-γ) (le_iSup_of_le (by simp) le_rfl)
  rw [rootRankOneGroup, range_rootSL2_of_isRoot hγ, hpair]

private theorem ggRKC_torusGroup_le_normalizer
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    torusGroup τ L ≤ Subgroup.normalizer
      ((rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  rw [ggRKC_rootSpan_pair hγ]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  change torusElt τ L i u ∈ Subgroup.normalizer
    ((rootSpan τ L ({γ, -γ} : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ L)) : Set (ModGL τ L))
  rw [torusElt_eq_rootDiagUnit]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  refine map_rootSpan_of_forall ?_
  intro α hα
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl
  · exact map_conj_rootDiagUnit_rootSubgroup _ hγ
  · exact map_conj_rootDiagUnit_rootSubgroup _ (IsRoot.neg hγ)

private theorem ggRKC_canonicalRep_mem_normalizer
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {w : WeylGroup τ} (hw : w = 1 ∨ w = rootReflection γ) :
    canonicalRep (coxeterSystem τ) L w ∈ Subgroup.normalizer
      ((rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  rcases hw with rfl | hw
  · rw [canonicalRep_one]
    exact Subgroup.one_mem _
  · rw [hw, ggRKC_rootSpan_pair hγ]
    have hS : (fun α : Fin τ.rank → ℤ => rootReflection γ • α) ''
        ({γ, -γ} : Set (Fin τ.rank → ℤ)) = ({γ, -γ} : Set (Fin τ.rank → ℤ)) := by
      ext α
      constructor
      · rintro ⟨β, hβ, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ ⊢
        rcases hβ with hβ | hβ
        · rw [hβ]; right; exact rootReflection_smul_self hγ
        · rw [hβ]; left; rw [smul_neg, rootReflection_smul_self hγ, neg_neg]
      · intro hα
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
        rcases hα with hα | hα
        · rw [hα]
          refine ⟨-γ, by simp, ?_⟩
          change rootReflection γ • (-γ) = γ
          rw [smul_neg, rootReflection_smul_self hγ, neg_neg]
        · rw [hα]
          exact ⟨γ, by simp, rootReflection_smul_self hγ⟩
    have hroot : ∀ α ∈ ({γ, -γ} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
      intro α hα
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
      rcases hα with hα | hα
      · rw [hα]; exact hγ
      · rw [hα]; exact IsRoot.neg hγ
    have hmain := (canonical_weyl_root_transport τ L).1 (rootReflection γ)
      ({γ, -γ} : Set (Fin τ.rank → ℤ)) hroot
    rw [hS] at hmain
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmain

private def ggRKC_Sγ (K : Type) [Field K] (p : ℕ) (τ : Tag) (γ : Fin τ.rank → ℤ) : Type :=
  {b : Fin τ.rank → (AlgebraicClosure K)ˣ // (∀ i, b i ^ p = 1) ∧ rootChar b γ = 1}

private def ggRKC_af (K : Type) [Field K] (p : ℕ) (τ : Tag) (γ : Fin τ.rank → ℤ) :
    ggRKC_Sγ K p τ γ → Fin τ.rank → (AlgebraicClosure K)ˣ := fun b => b.1

private theorem ggRKC_hyp_coord_surj
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp3 : 3 ≤ p) (F : ExcFrame τ K p E) (hlong : ExcIsLongest τ F.w)
    (hpq : p ∣ Nat.card K + 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ} (hb : ∀ i, b i ^ p = 1)
    (hχ : rootChar b γ = 1) :
    ∃ h ∈ ggKGExcHyp F γ, rootDiagUnit τ b = ggKGExcY F h := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  have hτ6 : τ = .E6 → 5 ≤ p := fun h => by
    rcases hτ' with h' | h' | h' <;> rw [h'] at h <;> cases h
  have hact : weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b :=
    ggKGEx_hact_w_neg F hFr hτ' hlong hpq hb
  obtain ⟨e, heE, heq⟩ := ggKGEx_exists_conj_of_hact hp hp3 hτ6 (Or.inr hτ') F hΦ hb hact
  have heq' : rootDiagUnit τ b = ggKGExcY F e := by
    rw [ggKGExcY_apply]
    exact heq
  have hweyl : weylTuple (rootReflection γ) b = b := ggRKC_weylTuple_rootReflection hγ hχ
  have hmem : e ∈ ggKGExcHyp F γ := by
    refine Subgroup.mem_inf.2 ⟨heE, ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hconj : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
        ggKGExcY F e *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ =
        ggKGExcY F e := by
      rw [← heq', canonicalRep_conj_rootDiagUnit, hweyl]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  exact ⟨e, hmem, heq'⟩

private theorem ggRKC_mem_familyCentralizer
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp3 : 3 ≤ p) (F : ExcFrame τ K p E) (hlong : ExcIsLongest τ F.w)
    (hpq : p ∣ Nat.card K + 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {c : adjointGroup τ K}
    (hc : c ∈ Subgroup.centralizer (ggKGExcHyp F γ : Set (adjointGroup τ K))) :
    ggKGExcY F c ∈ familyCentralizer τ (AlgebraicClosure K) (ggRKC_af K p τ γ) := by
  rw [mem_familyCentralizer]
  refine ⟨?_, fun i => ?_⟩
  · refine mul_mem (mul_mem (inv_mem F.D.g0_mem) ?_) F.D.g0_mem
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
      (algebraMap K (AlgebraicClosure K)) c.property
  · obtain ⟨h, hh, hheq⟩ := ggRKC_hyp_coord_surj hτ' hp hp3 F hlong hpq hγ
      (b := ggRKC_af K p τ γ i) i.property.1 i.property.2
    have hY : ggKGExcY F h * ggKGExcY F c * (ggKGExcY F h)⁻¹ = ggKGExcY F c := by
      have hcomm : ggKGExcY F h * ggKGExcY F c = ggKGExcY F c * ggKGExcY F h := by
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hc) h hh]
      rw [hcomm]
      group
    change rootDiagUnit τ (ggRKC_af K p τ γ i) * ggKGExcY F c *
      (rootDiagUnit τ (ggRKC_af K p τ γ i))⁻¹ = ggKGExcY F c
    rw [hheq]
    exact hY

theorem ggRealKGNegJ_le_centralizer
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hp : p.Prime)
    (hp3 : 3 ≤ p) (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ggRealKGNegJ F γ ≤ Subgroup.centralizer ((ggKGExcHyp F γ : Subgroup (adjointGroup τ K)) :
      Set (adjointGroup τ K)) := by
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhE : h ∈ E := (Subgroup.mem_inf.1 hh).1
  have hhcent := (Subgroup.mem_inf.1 hh).2
  have hhp : h ^ p = 1 := ((F.mem_iff h).1 hhE).1
  have hhtorus : ggKGExcY F h ∈ F.D.torus := ((F.mem_iff h).1 hhE).2
  have hhtG : ggKGExcY F h ∈ torusGroup τ (AlgebraicClosure K) :=
    CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hhtorus |>.1
  obtain ⟨b, hb⟩ := ggRKC_exists_rootDiagUnit_of_mem_torusGroup hhtG
  have hbp : b ^ p = 1 := by
    refine rootDiagUnit_injective (τ := τ) ?_
    calc rootDiagUnit τ (b ^ p) = (rootDiagUnit τ b) ^ p :=
          map_pow (rootDiagUnitHom τ (AlgebraicClosure K)) b p
      _ = (ggKGExcY F h) ^ p := by rw [hb]
      _ = ggKGExcY F (h ^ p) := (map_pow (ggKGExcY F) h p).symm
      _ = ggKGExcY F 1 := by rw [hhp]
      _ = 1 := map_one (ggKGExcY F)
      _ = rootDiagUnit τ 1 := rootDiagUnit_one.symm
  have hcomm := (Subgroup.mem_centralizer_iff.1 hhcent)
    (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))
    (Set.mem_singleton _)
  have hfix : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
      rootDiagUnit τ b * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ =
      rootDiagUnit τ b := by
    rw [hb, hcomm]
    group
  have hweyl : weylTuple (rootReflection γ) b = b := by
    refine rootDiagUnit_injective (τ := τ) ?_
    rw [← canonicalRep_conj_rootDiagUnit (rootReflection γ) b]
    exact hfix
  have hinv : (rootReflection γ)⁻¹ = rootReflection γ :=
    inv_eq_of_mul_eq_one_right (rootReflection_mul_self hγ)
  have hχinv : rootChar b γ = (rootChar b γ)⁻¹ := by
    calc rootChar b γ = rootChar (weylTuple (rootReflection γ) b) γ := by rw [hweyl]
      _ = rootChar b ((rootReflection γ)⁻¹ • γ) := rootChar_weylTuple (rootReflection γ) b γ
      _ = rootChar b (rootReflection γ • γ) := by rw [hinv]
      _ = rootChar b (-γ) := by rw [rootReflection_smul_self hγ]
      _ = (rootChar b γ)⁻¹ := rootChar_neg' b γ
  have hχ2 : rootChar b γ * rootChar b γ = 1 :=
    (eq_inv_iff_mul_eq_one).1 hχinv
  have hχpow : (rootChar b γ) ^ p = 1 := by
    rw [← ggRKC_rootChar_pow b p γ, hbp]
    simp [rootChar]
  have hχ : rootChar b γ = 1 := by
    have h2 : orderOf (rootChar b γ) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 (by rwa [pow_two])
    have hp' : orderOf (rootChar b γ) ∣ p := orderOf_dvd_iff_pow_eq_one.2 hχpow
    have hndvd : ¬ p ∣ 2 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hcop : Nat.gcd 2 p = 1 := (hp.coprime_iff_not_dvd.2 hndvd).symm
    have hgcd : orderOf (rootChar b γ) ∣ 1 := by
      have := Nat.dvd_gcd h2 hp'
      rwa [hcop] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hgcd)
  obtain ⟨M, hM⟩ := (Subgroup.mem_inf.1 (show ggKGExcY F j ∈ ggRealKGNegLhat F γ from hj)).1
  have hcommd : rootDiagUnit τ b * ggKGExcY F j * (rootDiagUnit τ b)⁻¹ = ggKGExcY F j := by
    rw [← hM, rootDiagUnit_conj_rootSL2 b hγ M, hχ, conjSL_diagUnitOne_one]
  have hYcomm : ggKGExcY F h * ggKGExcY F j = ggKGExcY F j * ggKGExcY F h := by
    have h1 : rootDiagUnit τ b * ggKGExcY F j = ggKGExcY F j * rootDiagUnit τ b := by
      have := congrArg (· * rootDiagUnit τ b) hcommd
      simpa [mul_assoc] using this
    rw [← hb]
    exact h1
  exact ggKGExcY_injective F (by rw [map_mul, map_mul, hYcomm])

theorem ggRealKGNegJ_subnormal
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card K + 1) (F : ExcFrame τ K p E) (hlong : ExcIsLongest τ F.w)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    Assembly.IsSubnormal (ggRealKGNegJ F γ) (Subgroup.centralizer
      ((ggKGExcHyp F γ : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K))) := by
  have hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := Or.inr hτ'
  have hτ6 : τ = .E6 → 5 ≤ p := fun h => by
    rcases hτ' with h' | h' | h' <;> rw [h'] at h <;> cases h
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  obtain ⟨ζu, hζu⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) (by norm_num) hp (by omega)
  let ζ : AlgebraicClosure K := ζu
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
  have hall : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ j, b j ^ p = 1) →
      rootChar b γ = 1 → ∃ i : ggRKC_Sγ K p τ γ, ggRKC_af K p τ γ i = b :=
    fun b hb hχ => ⟨⟨b, hb, hχ⟩, rfl⟩
  have hker : ∀ i : ggRKC_Sγ K p τ γ, rootChar (ggRKC_af K p τ γ i) γ = 1 :=
    fun i => i.property.2
  have hstab : familyStabilizer (ggRKC_af K p τ γ) = {1, rootReflection γ} :=
    ggKGExc_familyStabilizer_killRoot hτ hp hp3 hτ6 hζ (ggRKC_af K p τ γ) hγ hker
      hall
  have hfker : familyKernel (ggRKC_af K p τ γ) = {γ, -γ} :=
    ggKGExc_familyKernel_killRoot hτ hp (by omega) hζ (ggRKC_af K p τ γ) hγ hker hall
  refine Assembly.IsSubnormal.step (ggRealKGNegJ_le_centralizer hp hp3 F hγ) ?_
    (Assembly.IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff (ggRealKGNegJ_le_centralizer hp hp3 F hγ)]
  intro j c hj hc
  have hYj : ggKGExcY F j ∈ ggRealKGNegLhat F γ := hj
  have hYj_root : ggKGExcY F j ∈ rootRankOneGroup τ (AlgebraicClosure K) γ :=
    (Subgroup.mem_inf.1 hYj).1
  have hfam : ggKGExcY F c ∈ familyCentralizer τ (AlgebraicClosure K) (ggRKC_af K p τ γ) :=
    ggRKC_mem_familyCentralizer hτ' hp hp3 F hlong hpq hγ hc
  obtain ⟨w, hwstab, m, hm, hc_eq⟩ :=
    familyCentralizer_le_mul τ (AlgebraicClosure K) (ggRKC_af K p τ γ) hfam
  rw [hstab] at hwstab
  have hw' : w = 1 ∨ w = rootReflection γ := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hwstab
  have hm_norm : m ∈ Subgroup.normalizer
      ((rootRankOneGroup τ (AlgebraicClosure K) γ : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    rw [familyGroup, hfker] at hm
    refine (sup_le (ggRKC_torusGroup_le_normalizer hγ) ?_) hm
    rw [← ggRKC_rootSpan_pair hγ]
    exact Subgroup.le_normalizer
  have hnorm : ggKGExcY F c ∈ Subgroup.normalizer
      ((rootRankOneGroup τ (AlgebraicClosure K) γ : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    rw [hc_eq]
    exact Subgroup.mul_mem _ hm_norm (ggRKC_canonicalRep_mem_normalizer hγ hw')
  have hconj_root : ggKGExcY F c * ggKGExcY F j * (ggKGExcY F c)⁻¹ ∈
      rootRankOneGroup τ (AlgebraicClosure K) γ :=
    ((Subgroup.mem_normalizer_iff.1 hnorm) (ggKGExcY F j)).1 hYj_root
  have hfix : F.D.step (ggKGExcY F (c * j * c⁻¹)) = ggKGExcY F (c * j * c⁻¹) :=
    ggRealKGNeg_step_Y F hFr hΦ _
  rw [ggRealKGNegJ, Subgroup.mem_comap]
  refine Subgroup.mem_inf.2 ⟨?_, hfix⟩
  simpa only [map_mul, map_inv] using hconj_root

theorem ggRealKGNegJ_layer
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (F : ExcFrame τ K p E) (hlong : ExcIsLongest τ F.w) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hq : 4 ≤ Nat.card K) {a : adjointGroup τ K} (ha : a ∈ ggKGExcHyp F γ) :
    ggRealKGNegJ F γ ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set (adjointGroup τ K))) := by
  have hτ'' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ' with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
  have hS := (LayerCores.adjointGroup_isSimple_nonabelian hτ'' K).1
  have hnc := (LayerCores.adjointGroup_isSimple_nonabelian hτ'' K).2
  have hchev := LayerCores.isChevSimple_adjointGroup_charTwo hτ'' K
  have haE : a ∈ E := (Subgroup.mem_inf.1 ha).1
  have hap : a ^ p = 1 := ((F.mem_iff a).1 haE).1
  have hJperf : ⁅ggRealKGNegJ F γ, ggRealKGNegJ F γ⁆ = ggRealKGNegJ F γ :=
    LayerFacts.ggCommutator_eq_of_isQuasisimple (ggRealKGNegJ_quasisimple
        (hτ'.imp id (fun h => h.imp id Or.inl)) F hγ
        (ggRealKGNeg_smul_eq_neg hτ' hlong γ) hq)
  have hJle : ggRealKGNegJ F γ ≤ Subgroup.centralizer ({a} : Set (adjointGroup τ K)) :=
    (ggRealKGNegJ_le_centralizer hp hp3 F hγ).trans
      (Subgroup.centralizer_le (by rintro x rfl; exact ha))
  exact ggKG_layer_of_chevSimple hS hnc hchev hp (by omega) hap hJperf hJle

private theorem ggRKC_mem_centralizer_iff {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {γ : Fin τ.rank → ℤ} {w : adjointGroup τ K}
    (hwγ : ggKGExcY F w =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))
    (e : adjointGroup τ K) :
    e ∈ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) ↔
      ggKGExcY F e ∈ Subgroup.centralizer
        ({canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ)} :
          Set (ModGL τ (AlgebraicClosure K))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← hwγ, ← map_mul, ← map_mul, h]
  · intro h
    apply ggKGExcY_injective F
    rw [map_mul, map_mul, hwγ]
    exact h

private theorem ggRKC_inf_centralizer_eq_hyp {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {γ : Fin τ.rank → ℤ} {w : adjointGroup τ K}
    (hwγ : ggKGExcY F w =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ)) :
    E ⊓ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) = ggKGExcHyp F γ := by
  ext e
  unfold ggKGExcHyp
  simp only [Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggRKC_mem_centralizer_iff F hwγ e).mp hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggRKC_mem_centralizer_iff F hwγ e).mpr hc⟩

theorem ggRealKGNeg_rootDatumAt
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card K + 1) (hq : 4 ≤ Nat.card K) (F : ExcFrame τ K p E)
    (hlong : ExcIsLongest τ F.w) :
    GGKGRootDatumAt p E := by
  intro w₀ hrefl
  obtain ⟨γ, hγ, hγeq⟩ := ggKGExc_reflection_isRoot_neg hτ' hp hp3 hpq F hlong hrefl
  obtain ⟨w, hwJ, hwγ⟩ := ggRealKGNegJ_weyl (hτ'.imp id (fun h => h.imp id Or.inl)) F hγ
    (ggRealKGNeg_smul_eq_neg hτ' hlong γ) hq
  have hinf : E ⊓ Subgroup.centralizer ({w} : Set (adjointGroup τ K)) = ggKGExcHyp F γ :=
    ggRKC_inf_centralizer_eq_hyp F hwγ
  refine ⟨w, ?_, ggRealKGNegJ F γ, hwJ, ?_, ?_, ?_⟩
  · intro e he
    have hleft : ggKGExcY F (w * e * w⁻¹) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
          ggKGExcY F e *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hwγ]
    have hright : ggKGExcY F (w₀ * e * w₀⁻¹) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
          ggKGExcY F e *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ := by
      rw [ggKGExcY_apply, ggKGExcY_apply]
      exact hγeq e he
    exact ggKGExcY_injective F (hleft.trans hright.symm)
  · rw [hinf]
    have hQ := ggRealKGNegJ_quasisimple (hτ'.imp id (fun h => h.imp id Or.inl)) F hγ
      (ggRealKGNeg_smul_eq_neg hτ' hlong γ) hq
    exact ⟨ggRealKGNegJ_le_centralizer hp hp3 F hγ,
      ggRealKGNegJ_subnormal hτ' hp hp3 hpq F hlong hγ, ⟨hQ.1.commutator_eq_top, hQ.2.1⟩⟩
  · exact ggRealKGNegJ_dvd_card (hτ'.imp id (fun h => h.imp id Or.inl)) F hγ
      (ggRealKGNeg_smul_eq_neg hτ' hlong γ) hq hpq
  · intro a ha haw
    apply ggRealKGNegJ_layer hτ' hp hp3 F hlong hγ hq
    rw [← hinf]
    exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr haw.symm⟩

end CFSG.StandardType
