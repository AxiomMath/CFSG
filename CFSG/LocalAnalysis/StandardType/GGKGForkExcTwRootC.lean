module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.LocalAnalysis.StandardType.GGLayerChevAdjoint
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LieType.SeitzGeneration.HyperCoverE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

private theorem ggKGTcc_Y_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    Function.Injective (ggKGTwY F) := by
  intro x y hxy
  have h : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) := by
    have h' := hxy
    rw [ggKGTwY_apply, ggKGTwY_apply] at h'
    exact mul_left_cancel (mul_right_cancel h')
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h)

private theorem ggKGTcc_exists_rootDiagUnit_of_mem_torusGroup
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

private theorem ggKGTcc_rootChar_pow
    {τ : Tag} {L : Type} [Field L] (b : Fin τ.rank → Lˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (b ^ n) v = (rootChar b v) ^ n := by
  simp only [rootChar, Pi.pow_apply]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast (b i) n, ← zpow_natCast (b i ^ (v i)) n, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

private theorem ggKGTcc_weylTuple_rootReflection
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {b : Fin τ.rank → Lˣ} (hχ : rootChar b γ = 1) :
    weylTuple (rootReflection γ) b = b := by
  funext i
  rw [weylTuple, inv_eq_of_mul_eq_one_right (rootReflection_mul_self hγ),
    rootReflection_smul hγ (Pi.single i 1), rootChar_sub, rootChar_zsmul, hχ, one_zpow,
    inv_one, mul_one]
  simpa using rootChar_nsmul_single b i 1

private theorem ggKGTcc_hyp_coord_surj
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ)
    {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ} (hb : ∀ i, b i ^ p = 1)
    (hχ : rootChar b γ = 1) :
    ∃ h ∈ ggKGTwHyp F γ, rootDiagUnit TwistTag.E6.tag b = ggKGTwY F h := by
  have hact : weylTuple F.v
      (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b :=
    ggKGTc_hact_w_w0 F hv hpq hb
  obtain ⟨e, heE, heq⟩ := ggKGTc_exists_conj_of_hact hK hσ hp hp5 F hb hact
  have heq' : rootDiagUnit TwistTag.E6.tag b = ggKGTwY F e := by
    rw [ggKGTwY_apply]
    exact heq
  have hweyl : weylTuple (rootReflection γ) b = b := ggKGTcc_weylTuple_rootReflection hγ hχ
  have hmem : e ∈ ggKGTwHyp F γ := by
    refine Subgroup.mem_inf.2 ⟨heE, ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hconj : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
      (rootReflection γ) *
        ggKGTwY F e *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ))⁻¹ =
        ggKGTwY F e := by
      rw [← heq', canonicalRep_conj_rootDiagUnit, hweyl]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  exact ⟨e, hmem, heq'⟩

private theorem ggKGTcc_rootSpan_pair
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

private theorem ggKGTcc_torusGroup_le_normalizer
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    torusGroup τ L ≤ Subgroup.normalizer
      ((rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  rw [ggKGTcc_rootSpan_pair hγ]
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

private theorem ggKGTcc_canonicalRep_mem_normalizer
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {w : WeylGroup τ} (hw : w • γ = γ ∨ w • γ = -γ) :
    canonicalRep (coxeterSystem τ) L w ∈ Subgroup.normalizer
      ((rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  have hS : (fun α : Fin τ.rank → ℤ => w • α) '' ({γ, -γ} : Set (Fin τ.rank → ℤ)) =
      ({γ, -γ} : Set (Fin τ.rank → ℤ)) := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ ⊢
      rcases hβ with hβ | hβ
      · rw [hβ]; exact hw
      · rw [hβ]
        rcases hw with h | h
        · right; rw [smul_neg, h]
        · left; rw [smul_neg, h, neg_neg]
    · intro hα
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
      rcases hα with hα | hα
      · rw [hα]
        rcases hw with h | h
        · exact ⟨γ, Or.inl rfl, h⟩
        · exact ⟨-γ, Or.inr rfl, by show w • (-γ) = γ; rw [smul_neg, h, neg_neg]⟩
      · rw [hα]
        rcases hw with h | h
        · exact ⟨-γ, Or.inr rfl, by show w • (-γ) = -γ; rw [smul_neg, h]⟩
        · exact ⟨γ, Or.inl rfl, h⟩
  rw [ggKGTcc_rootSpan_pair hγ]
  have hroot : ∀ α ∈ ({γ, -γ} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
    intro α hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with hα | hα
    · rw [hα]; exact hγ
    · rw [hα]; exact IsRoot.neg hγ
  have hmain := (canonical_weyl_root_transport τ L).1 w
    ({γ, -γ} : Set (Fin τ.rank → ℤ)) hroot
  rw [hS] at hmain
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmain

private def ggKGTcc_Sγ (K : Type) [Field K] (p : ℕ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) : Type :=
  {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ //
    (∀ i, b i ^ p = 1) ∧ rootChar b γ = 1}

private def ggKGTcc_af (K : Type) [Field K] (p : ℕ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTcc_Sγ K p γ → Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := fun b => b.1

private theorem ggKGTcc_mem_familyCentralizer
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) {c : twistedE6RootGroup K σ}
    (hc : c ∈ Subgroup.centralizer (ggKGTwHyp F γ : Set (twistedE6RootGroup K σ))) :
    ggKGTwY F c ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K)
      (ggKGTcc_af K p γ) := by
  rw [mem_familyCentralizer]
  refine ⟨?_, fun i => ?_⟩
  · refine mul_mem (mul_mem (inv_mem F.g0_mem) ?_) F.g0_mem
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
      (algebraMap K (AlgebraicClosure K)) (ggKGTc_coe_mem_adjointGroup c)
  · obtain ⟨h, hh, hheq⟩ := ggKGTcc_hyp_coord_surj hK hσ hp hp5 hpq F hv hγ
      (b := ggKGTcc_af K p γ i) i.property.1 i.property.2
    have hY : ggKGTwY F h * ggKGTwY F c * (ggKGTwY F h)⁻¹ = ggKGTwY F c := by
      have hcomm : ggKGTwY F h * ggKGTwY F c = ggKGTwY F c * ggKGTwY F h := by
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hc) h hh]
      rw [hcomm]
      group
    change rootDiagUnit TwistTag.E6.tag (ggKGTcc_af K p γ i) * ggKGTwY F c *
      (rootDiagUnit TwistTag.E6.tag (ggKGTcc_af K p γ i))⁻¹ = ggKGTwY F c
    rw [hheq]
    exact hY

private theorem ggKGTcc_twStep_Y_eq
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (x : twistedE6RootGroup K σ) :
    ggKGTwStep F (ggKGTwY F x) = ggKGTwY F x := by
  change canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
      twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr (ggKGTwY F x) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ = ggKGTwY F x
  rw [ggKGTwY_apply]
  rw [show twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
        (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          F.g0) =
      (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0)⁻¹ *
        twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)) *
        twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0 by rw [map_mul, map_mul, map_inv]]
  rw [F.lang, ggKGTc_twistHom_baseChange_eq_self F hσ x]
  group

theorem ggKGTwJ_le_centralizer
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggKGTwJ F γ ≤ Subgroup.centralizer ((ggKGTwHyp F γ : Subgroup (twistedE6RootGroup K σ)) :
      Set (twistedE6RootGroup K σ)) := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change ggKGTwJ F γT ≤ Subgroup.centralizer
    ((ggKGTwHyp F γT : Subgroup (twistedE6RootGroup K σ)) :
      Set (twistedE6RootGroup K σ))
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhE : h ∈ E := (Subgroup.mem_inf.1 hh).1
  have hhcent := (Subgroup.mem_inf.1 hh).2
  have hhp : h ^ p = 1 := ((F.mem_iff h).1 hhE).1
  have hhtorus : ggKGTwY F h ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) :=
    ((F.mem_iff h).1 hhE).2
  have hhtG : ggKGTwY F h ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mem_twistedTorusOf.1 hhtorus |>.1
  obtain ⟨b, hb⟩ := ggKGTcc_exists_rootDiagUnit_of_mem_torusGroup hhtG
  have hbp : b ^ p = 1 := by
    refine rootDiagUnit_injective (τ := TwistTag.E6.tag) ?_
    calc rootDiagUnit TwistTag.E6.tag (b ^ p) =
          (rootDiagUnit TwistTag.E6.tag b) ^ p :=
          map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) b p
      _ = (ggKGTwY F h) ^ p := by rw [hb]
      _ = ggKGTwY F (h ^ p) := (map_pow (ggKGTwY F) h p).symm
      _ = ggKGTwY F 1 := by rw [hhp]
      _ = 1 := map_one (ggKGTwY F)
      _ = rootDiagUnit TwistTag.E6.tag 1 := rootDiagUnit_one.symm
  have hcomm := (Subgroup.mem_centralizer_iff.1 hhcent)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γT))
    (Set.mem_singleton _)
  have hfix : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
    (rootReflection γT) *
      rootDiagUnit TwistTag.E6.tag b *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γT))⁻¹ =
      rootDiagUnit TwistTag.E6.tag b := by
    rw [hb, hcomm]
    group
  have hweyl : weylTuple (rootReflection γT) b = b := by
    refine rootDiagUnit_injective (τ := TwistTag.E6.tag) ?_
    rw [← canonicalRep_conj_rootDiagUnit (rootReflection γT) b]
    exact hfix
  have hinv : (rootReflection γT)⁻¹ = rootReflection γT :=
    inv_eq_of_mul_eq_one_right (rootReflection_mul_self hγT)
  have hχinv : rootChar b γT = (rootChar b γT)⁻¹ := by
    calc rootChar b γT = rootChar (weylTuple (rootReflection γT) b) γT := by rw [hweyl]
      _ = rootChar b ((rootReflection γT)⁻¹ • γT) := rootChar_weylTuple (rootReflection γT) b γT
      _ = rootChar b (rootReflection γT • γT) := by rw [hinv]
      _ = rootChar b (-γT) := by rw [rootReflection_smul_self hγT]
      _ = (rootChar b γT)⁻¹ := rootChar_neg' b γT
  have hχ2 : rootChar b γT * rootChar b γT = 1 :=
    (eq_inv_iff_mul_eq_one).1 hχinv
  have hχpow : (rootChar b γT) ^ p = 1 := by
    rw [← ggKGTcc_rootChar_pow b p γT, hbp]
    simp [rootChar]
  have hχ : rootChar b γT = 1 := by
    have h2 : orderOf (rootChar b γT) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 (by rwa [pow_two])
    have hp' : orderOf (rootChar b γT) ∣ p := orderOf_dvd_iff_pow_eq_one.2 hχpow
    have hndvd : ¬ p ∣ 2 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hcop : Nat.gcd 2 p = 1 := (hp.coprime_iff_not_dvd.2 hndvd).symm
    have hgcd : orderOf (rootChar b γT) ∣ 1 := by
      have := Nat.dvd_gcd h2 hp'
      rwa [hcop] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hgcd)
  have hjL : ggKGTwY F j ∈ ggKGTwLhat F γT := hj
  have hYj_root : ggKGTwY F j ∈
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := hjL.1
  obtain ⟨M, hM⟩ := MonoidHom.mem_range.1 hYj_root
  have hYj : ggKGTwY F j = rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γT M := hM.symm
  have hcommd : rootDiagUnit TwistTag.E6.tag b * ggKGTwY F j * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      ggKGTwY F j := by
    rw [hYj, rootDiagUnit_conj_rootSL2 b hγT M, hχ, conjSL_diagUnitOne_one]
  have hYcomm : ggKGTwY F h * ggKGTwY F j = ggKGTwY F j * ggKGTwY F h := by
    have h1 : rootDiagUnit TwistTag.E6.tag b * ggKGTwY F j =
        ggKGTwY F j * rootDiagUnit TwistTag.E6.tag b := by
      have := congrArg (· * rootDiagUnit TwistTag.E6.tag b) hcommd
      simpa [mul_assoc] using this
    rw [← hb]
    exact h1
  exact ggKGTcc_Y_injective F (by rw [map_mul, map_mul, hYcomm])

theorem ggKGTwJ_subnormal
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Assembly.IsSubnormal (ggKGTwJ F γ) (Subgroup.centralizer
      ((ggKGTwHyp F γ : Subgroup (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change Assembly.IsSubnormal (ggKGTwJ F γT) (Subgroup.centralizer
    ((ggKGTwHyp F γT : Subgroup (twistedE6RootGroup K σ)) :
      Set (twistedE6RootGroup K σ)))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζu, hζu⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two hp (by omega)
  let ζ : AlgebraicClosure K := ζu
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
  have hall : ∀ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ, (∀ j, b j ^ p = 1) →
      rootChar b γT = 1 → ∃ i : ggKGTcc_Sγ K p γT, ggKGTcc_af K p γT i = b :=
    fun b hb hχ => ⟨⟨b, hb, hχ⟩, rfl⟩
  have hker : ∀ i : ggKGTcc_Sγ K p γT, rootChar (ggKGTcc_af K p γT i) γT = 1 :=
    fun i => i.property.2
  have hfker : familyKernel (ggKGTcc_af K p γT) = {γT, -γT} :=
    ggKGExc_familyKernel_killRoot (Or.inl rfl) hp (by omega) hζ (ggKGTcc_af K p γT) hγT hker hall
  refine Assembly.IsSubnormal.step (ggKGTwJ_le_centralizer hp hp5 F hγT) ?_
    (Assembly.IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff (ggKGTwJ_le_centralizer hp hp5 F hγT)]
  intro j c hj hc
  have hYj : ggKGTwY F j ∈ ggKGTwLhat F γT := hj
  have hYj_root : ggKGTwY F j ∈
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := hYj.1
  have hfam : ggKGTwY F c ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K)
      (ggKGTcc_af K p γT) :=
    ggKGTcc_mem_familyCentralizer hK hσ hp hp5 hpq F hv hγT hc
  obtain ⟨w, hwstab, m, hm, hc_eq⟩ :=
    familyCentralizer_le_mul TwistTag.E6.tag (AlgebraicClosure K) (ggKGTcc_af K p γT) hfam
  have himg := image_familyKernel (a := ggKGTcc_af K p γT) hwstab
  rw [hfker] at himg
  have hwγ : w • γT = γT ∨ w • γT = -γT := by
    have hmem : w • γT ∈ ({γT, -γT} : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
      rw [← himg]
      exact ⟨γT, by simp, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hm_norm : m ∈ Subgroup.normalizer
      ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT : Subgroup
        (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [familyGroup, hfker] at hm
    refine (sup_le (ggKGTcc_torusGroup_le_normalizer hγT) ?_) hm
    rw [← ggKGTcc_rootSpan_pair hγT]
    exact Subgroup.le_normalizer
  have hnorm : ggKGTwY F c ∈ Subgroup.normalizer
      ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT : Subgroup
        (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [hc_eq]
    exact Subgroup.mul_mem _ hm_norm (ggKGTcc_canonicalRep_mem_normalizer hγT hwγ)
  have hconj_root : ggKGTwY F c * ggKGTwY F j * (ggKGTwY F c)⁻¹ ∈
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT :=
    ((Subgroup.mem_normalizer_iff.1 hnorm) (ggKGTwY F j)).1 hYj_root
  have hfix : ggKGTwStep F (ggKGTwY F c * ggKGTwY F j * (ggKGTwY F c)⁻¹) =
      ggKGTwY F c * ggKGTwY F j * (ggKGTwY F c)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ggKGTcc_twStep_Y_eq F hσ c, ggKGTcc_twStep_Y_eq F hσ j]
  have hYmem : ggKGTwY F (c * j * c⁻¹) ∈ ggKGTwLhat F γT := by
    rw [ggKGTwLhat]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa only [map_mul, map_mul, map_inv] using hconj_root
    · rw [map_mul, map_mul, map_inv]
      exact hfix
  rw [ggKGTwJ, Subgroup.mem_comap]
  exact hYmem

theorem ggKGTwJ_layer
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hq : 4 ≤ 2 ^ n)
    {a : twistedE6RootGroup K σ} (ha : a ∈ ggKGTwHyp F γ) :
    ggKGTwJ F γ ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ))) := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change ggKGTwJ F γT ≤ LargeEvenLayer
    (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ)))
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hq
    norm_num at hq
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, hn⟩
  have hqcard : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
  have hvq : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  have hσ' : ∀ c, σ c = c ^ q.card := by intro c; rw [hqcard]; exact hσ c
  have hKq : Nat.card K = q.card ^ 2 := by rw [hqcard]; exact hK
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field
    q hvq K hKq σ hσ'
  haveI hsimpleC : IsSimpleGroup
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.twistedE6 q, hvq⟩) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_cat_twistedE6' hvq
  haveI hsimpleR : IsSimpleGroup ↥(twistedE6RootGroup K σ) := e.symm.isSimpleGroup
  have hchar : (⟨TauCeti.LieTypeIndex.twistedE6 q, hvq⟩ :
      TauCeti.ValidLieTypeIndex).1.characteristic = 2 := by
    show (TauCeti.LieTypeIndex.twistedE6 q).characteristic = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 ↥(twistedE6RootGroup K σ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie
      ⟨TauCeti.LieTypeIndex.twistedE6 q, hvq⟩ hchar e.symm
  have hqJ : CFSG.IsQuasisimple (ggKGTwJ F γT) := ggKGTwJ_quasisimple hK hσ F hv hγT hq
  have hnc : ∃ x y : ↥(twistedE6RootGroup K σ), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy⟩ := hqJ.2.2
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (congrArg (QuotientGroup.mk' (Subgroup.center ↥(ggKGTwJ F γT)))
      (Subtype.ext (hcon x' y')))
  have haE : a ∈ E := (Subgroup.mem_inf.1 ha).1
  have hap : a ^ p = 1 := ((F.mem_iff a).1 haE).1
  have hJperf : ⁅ggKGTwJ F γT, ggKGTwJ F γT⁆ = ggKGTwJ F γT :=
    LayerFacts.ggCommutator_eq_of_isQuasisimple hqJ
  have hJle : ggKGTwJ F γT ≤ Subgroup.centralizer ({a} : Set ↥(twistedE6RootGroup K σ)) :=
    (ggKGTwJ_le_centralizer hp hp5 F hγT).trans
      (Subgroup.centralizer_le (by rintro x rfl; exact ha))
  exact ggKG_layer_of_chevSimple hsimpleR hnc hchev hp (by omega) hap hJperf hJle

end CFSG.StandardType
