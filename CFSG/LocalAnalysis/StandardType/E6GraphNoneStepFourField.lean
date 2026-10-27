module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvLangDatumThrough
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneF4Transport
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFour
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close


theorem coe_embE6F4 {L : Type} [Field L] (y : adjointGroup Tag.F4 L) :
    ((embE6F4 L y : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      (((e6FixedF4EquivAll L).symm y :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : ModGL TwistTag.E6.tag L) := by
  unfold embE6F4 isoE6F4
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rfl

private theorem e6_frobenius_fixed_f4_point {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {p : ℕ}
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K))
    (hbp : b ^ p = 1) :
    ∃ bL : twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
        (RingHom.id (AlgebraicClosure K)),
      (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) b ∧
      (e6FixedF4EquivAll (AlgebraicClosure K) bL :
        ModGL Tag.F4 (AlgebraicClosure K)) ^ p = 1 ∧
      entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f
          (e6FixedF4EquivAll (AlgebraicClosure K) bL :
            ModGL Tag.F4 (AlgebraicClosure K)) =
        (e6FixedF4EquivAll (AlgebraicClosure K) bL :
          ModGL Tag.F4 (AlgebraicClosure K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι := algebraMap K L
  set Fr := iterateFrobenius L 2 f
  have hFrι : Fr.comp ι = ι := by
    ext c
    simp only [RingHom.comp_apply, Fr, iterateFrobenius_def, ← map_pow]
    congr 1
    rw [← hK, ← Fintype.card_eq_nat_card, FiniteField.pow_card]
  set bL : twistedFixedGroup TwistTag.E6 L (RingHom.id L) :=
    ⟨baseChangeGL ι b, baseChangeGL_mem_twistedFixedGroup ι hb⟩
  have hbL : (bL : ModGL TwistTag.E6.tag L) = baseChangeGL ι b := rfl
  set u := e6FixedF4EquivAll L bL
  have hbLp : bL ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change (baseChangeGL ι b) ^ p = 1
    rw [← map_pow, hbp, map_one])
  have hup : (u : ModGL Tag.F4 L) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hbLp, map_one]; rfl
  have hfix : entrywiseFrobGL Tag.F4 L 2 f (u : ModGL Tag.F4 L) = u := by
    change Units.map (entrywiseHom Fr) (u : ModGL Tag.F4 L) = u
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, coe_e6FixedF4EquivAll,
      ← e6FixedToF4_baseChangeGL Fr bL]
    have hsub : (⟨baseChangeGL Fr (bL : ModGL TwistTag.E6.tag L),
        baseChangeGL_mem_twistedFixedGroup Fr bL.2⟩ :
          twistedFixedGroup TwistTag.E6 L (RingHom.id L)) = bL :=
      Subtype.ext (by
        change baseChangeGL Fr (baseChangeGL ι b) = baseChangeGL ι b
        rw [baseChangeGL_baseChangeGL, hFrι])
    rw [hsub]
  exact ⟨bL, hbL, hup, hfix⟩

private theorem e6_antidiagonal_decomposition {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} (hq : q = 2 ^ f)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {bL : twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
      (RingHom.id (AlgebraicClosure K))}
    (hup : (e6FixedF4EquivAll (AlgebraicClosure K) bL :
      ModGL Tag.F4 (AlgebraicClosure K)) ^ p = 1)
    (hfix : entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f
        (e6FixedF4EquivAll (AlgebraicClosure K) bL :
          ModGL Tag.F4 (AlgebraicClosure K)) =
      (e6FixedF4EquivAll (AlgebraicClosure K) bL :
        ModGL Tag.F4 (AlgebraicClosure K))) :
    ∃ (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (ω : List (Fin Tag.F4.rank))
      (c : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      g ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
        (RingHom.id (AlgebraicClosure K)) ∧
      weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω) ∈
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
          (RingHom.id (AlgebraicClosure K)) ∧
      Units.map (entrywiseHom Fr) g =
        g * weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω) ∧
      (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
        g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set Fr₀ := iterateFrobenius L 2 f
  have hFr₀ : Fr = Fr₀ := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  obtain ⟨D, hΦ, -, hmem⟩ :=
    CFSG.StandardType.exc_langDatum_through_fixed
      (τ := Tag.F4) (Or.inr (Or.inl rfl)) hf hp hp2
      (e6FixedF4EquivAll L bL : ModGL Tag.F4 L) (e6FixedF4EquivAll L bL).2 hup hfix
  have hΦ' : D.Φ = Units.map (entrywiseHom Fr) := by rw [hΦ, hFr₀]
  obtain ⟨t, ht, htu⟩ := hmem
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_of_mem_torusGroup ((mem_twistedTorusOf.1 ht).1)
  obtain ⟨ω, -, hgP, hn, hlang, hconj, -⟩ :=
    CFSG.StandardType.E6GraphNoneSteps.f4LangDatum_transport D Fr hΦ'
  have hc := rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := Tag.F4) (L := L) c
  have hbg := hconj c hc
  have hy : (⟨D.g0, D.g0_mem⟩ * ⟨_, hc⟩ * ⟨D.g0, D.g0_mem⟩⁻¹ :
      adjointGroup Tag.F4 L) = e6FixedF4EquivAll L bL :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact htu)
  rw [hy, coe_embE6F4, MulEquiv.symm_apply_apply] at hbg
  exact ⟨_, ω, c, (embE6F4 L ⟨D.g0, D.g0_mem⟩).2, hgP, hn, hlang, hbg⟩

private theorem e6_moved_centralizer_of_antidiagonal {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {b : ModGL TwistTag.E6.tag K}
    {bL : twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
      (RingHom.id (AlgebraicClosure K))}
    (hbL : (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) b)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
      (RingHom.id (AlgebraicClosure K)))
    {ω : List (Fin Tag.F4.rank)}
    (hn : weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω) ∈
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
        (RingHom.id (AlgebraicClosure K)))
    (hlang : Units.map (entrywiseHom Fr) g =
      g * weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω))
    {c : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ}
    (hbg : (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
      g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) :
    ∃ z ∈ adjointGroup TwistTag.E6.tag K, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  classical
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hbL' : (bL : ModGL TwistTag.E6.tag L) = baseChangeGL (algebraMap K L) b := hbL
  have hbij : Function.Bijective Fr := ⟨Fr.injective, fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2 ^ f) (by positivity)
    exact ⟨z, by rw [hFr, hK]; exact hz⟩⟩
  have hq : 4 ≤ Nat.card K := by
    rw [hK]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqe : Even (Nat.card K) := by rw [hK]; exact (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨z, hzC, hcomm, hne⟩ :=
    CFSG.StandardType.E6GraphNoneSteps.e6_step4 (K := K) (L := L) Fr hFr hbij hq hqe hg hgP
      (unfoldF4 ω) hn hlang
  obtain ⟨zK, hzK, rfl⟩ := hzC
  refine ⟨zK, hzK, ?_, fun heq => hne ?_⟩
  · have h2 : Commute (baseChangeGL (algebraMap K L) zK : ModGL Tag.E6 L)
        (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) :=
      hcomm (fun i => c (e6IndexToF4 i))
    rw [← hbg, hbL'] at h2
    apply baseChangeGL_injective (algebraMap K L)
    rw [map_mul, map_mul]
    exact h2.eq
  · rw [← baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6, ← map_inv, ← map_mul,
      ← map_mul, heq]

theorem e6_step4_K {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K))
    (hbp : b ^ p = 1) :
    ∃ z ∈ adjointGroup TwistTag.E6.tag K, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨bL, hbL, hup, hfix⟩ := e6_frobenius_fixed_f4_point hK hb hbp
  obtain ⟨g, ω, c, hg, hgP, hn, hlang, hbg⟩ :=
    e6_antidiagonal_decomposition (Fr := iterateFrobenius (AlgebraicClosure K) 2 f)
      (by omega) hp hp2 hK (fun c => by rw [hK]; rfl) hup hfix
  exact e6_moved_centralizer_of_antidiagonal hf hK
    (Fr := iterateFrobenius (AlgebraicClosure K) 2 f) (hFr := fun c => by rw [hK]; rfl)
    hbL hg hgP hn hlang hbg

private theorem twisted_e6_baseChange_fixed {K : Type} [Field K] {n : ℕ} {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbP : diagramMap TwistTag.E6 K * b = b * diagramMap TwistTag.E6 K) :
    baseChangeGL (algebraMap K (AlgebraicClosure K)) b ∈
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
          (RingHom.id (AlgebraicClosure K)) ∧
      Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) b) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) b := by
  classical
  set L := AlgebraicClosure K
  set ι := algebraMap K L
  have hισ : ∀ c, ι (σ.toRingHom c) = Fr (ι c) := fun c => by
    rw [hFr, ← map_pow]; congr 1; exact hσ c
  have hbR : baseChangeGL ι b ∈ twistedFixedGroup TwistTag.E6 L Fr :=
    CFSG.StandardType.TableBExcSmallRanks.baseChangeGL_mem_twistedFixedGroup TwistTag.E6 ι
      σ.toRingHom Fr hισ (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hb)
  have hbPL : diagramMap TwistTag.E6 L * baseChangeGL ι b =
      baseChangeGL ι b * diagramMap TwistTag.E6 L := by
    rw [← baseChangeGL_diagramMap ι TwistTag.E6, ← map_mul, ← map_mul, hbP]
  have hbΓ : baseChangeGL ι b ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) :=
    mem_twistedFixedGroup_id_iff.2 ⟨hbR.1, hbPL⟩
  have hbFr : Units.map (entrywiseHom Fr) (baseChangeGL ι b) = baseChangeGL ι b := by
    have h := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hbR).2
    rw [twistHom_apply] at h
    have h' : diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) (baseChangeGL ι b) =
        diagramMap TwistTag.E6 L * baseChangeGL ι b := by
      rw [hbPL]; exact (eq_mul_inv_iff_mul_eq.1 h.symm).symm
    exact mul_left_cancel h'
  exact ⟨hbΓ, hbFr⟩

private theorem twisted_e6_frobenius_fixed_f4_point {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbP : diagramMap TwistTag.E6 K * b = b * diagramMap TwistTag.E6 K) (hbp : b ^ p = 1) :
    ∃ bL : twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
        (RingHom.id (AlgebraicClosure K)),
      (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) b ∧
      (e6FixedF4EquivAll (AlgebraicClosure K) bL :
        ModGL Tag.F4 (AlgebraicClosure K)) ^ p = 1 ∧
      entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 n
          (e6FixedF4EquivAll (AlgebraicClosure K) bL :
            ModGL Tag.F4 (AlgebraicClosure K)) =
        (e6FixedF4EquivAll (AlgebraicClosure K) bL :
          ModGL Tag.F4 (AlgebraicClosure K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι := algebraMap K L
  set Fr := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => rfl
  obtain ⟨hbΓ, hbFr⟩ := twisted_e6_baseChange_fixed hσ hFr hb hbP
  set bL : twistedFixedGroup TwistTag.E6 L (RingHom.id L) := ⟨baseChangeGL ι b, hbΓ⟩
  have hbL : (bL : ModGL TwistTag.E6.tag L) = baseChangeGL ι b := rfl
  set u := e6FixedF4EquivAll L bL
  have hbLp : bL ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change (baseChangeGL ι b) ^ p = 1
    rw [← map_pow, hbp, map_one])
  have hup : (u : ModGL Tag.F4 L) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hbLp, map_one]; rfl
  have hfix : entrywiseFrobGL Tag.F4 L 2 n (u : ModGL Tag.F4 L) = u := by
    change Units.map (entrywiseHom Fr) (u : ModGL Tag.F4 L) = u
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, coe_e6FixedF4EquivAll,
      ← e6FixedToF4_baseChangeGL Fr bL]
    have hsub : (⟨baseChangeGL Fr (bL : ModGL TwistTag.E6.tag L),
        baseChangeGL_mem_twistedFixedGroup Fr bL.2⟩ :
          twistedFixedGroup TwistTag.E6 L (RingHom.id L)) = bL :=
      Subtype.ext (by
        change baseChangeGL Fr (baseChangeGL ι b) = baseChangeGL ι b
        rw [← units_map_entrywiseHom_eq_baseChangeGL_self, hbFr])
    rw [hsub]
  exact ⟨bL, hbL, hup, hfix⟩

private theorem twisted_e6_moved_centralizer_of_antidiagonal {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {b : ModGL TwistTag.E6.tag K}
    {bL : twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
      (RingHom.id (AlgebraicClosure K))}
    (hbL : (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) b)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
      (RingHom.id (AlgebraicClosure K)))
    {ω : List (Fin Tag.F4.rank)}
    (hn' : weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω) ∈
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K)
        (RingHom.id (AlgebraicClosure K)))
    (hlang : Units.map (entrywiseHom Fr) g =
      g * weylWord (τ := TwistTag.E6.tag) (AlgebraicClosure K) (unfoldF4 ω))
    {c : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ}
    (hbg : (bL : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
      g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) :
    ∃ z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  classical
  set L := AlgebraicClosure K
  have hbL' : (bL : ModGL TwistTag.E6.tag L) = baseChangeGL (algebraMap K L) b := hbL
  obtain ⟨z, hzC, hcomm, hne⟩ :=
    CFSG.StandardType.E6GraphNoneSteps.twE6_step4 (K := K) (L := L) hn hK hσ hFr hg hgP
      (unfoldF4 ω) hn' hlang
  obtain ⟨zK, hzK, rfl⟩ := hzC
  refine ⟨zK, hzK, ?_, fun heq => hne ?_⟩
  · have h2 : Commute (baseChangeGL (algebraMap K L) zK : ModGL Tag.E6 L)
        (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) :=
      hcomm (fun i => c (e6IndexToF4 i))
    rw [← hbg, hbL'] at h2
    apply baseChangeGL_injective (algebraMap K L)
    rw [map_mul, map_mul]
    exact h2.eq
  · rw [← baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6, ← map_inv, ← map_mul,
      ← map_mul, heq]

theorem twE6_step4_K {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {b : ModGL TwistTag.E6.tag K} (hb : b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbP : diagramMap TwistTag.E6 K * b = b * diagramMap TwistTag.E6 K) (hbp : b ^ p = 1) :
    ∃ z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, Commute z b ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ (n * 2) := by rw [Fintype.card_eq_nat_card, hK, pow_mul]
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  obtain ⟨bL, hbL, hup, hfix⟩ := twisted_e6_frobenius_fixed_f4_point hσ hb hbP hbp
  obtain ⟨g, ω, c, hg, hgP, hn', hlang, hbg⟩ :=
    e6_antidiagonal_decomposition (f := n) (Fr := iterateFrobenius (AlgebraicClosure K) 2 n)
      (by omega) hp hp2 rfl (fun c => rfl) hup hfix
  exact twisted_e6_moved_centralizer_of_antidiagonal hn hK hσ
    (Fr := iterateFrobenius (AlgebraicClosure K) 2 n) (hFr := fun c => rfl)
    hbL hg hgP hn' hlang hbg

end CFSG.StandardType.E6GraphNoneSteps
