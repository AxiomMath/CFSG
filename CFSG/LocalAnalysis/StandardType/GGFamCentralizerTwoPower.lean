module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual
import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
import CFSG.RankThree.Classical2.TwistedE6RationalOrder
import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType.LayerSixE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE LayerExc

open scoped Pointwise

variable
  {τ : Tag} {K : Type} [Field K]

private theorem exists_pow_mem_famReflectionGroup [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    {w : WeylGroup τ} (hw : w ∈ famStabilizerSubgroup F) :
    ∃ e : ℕ, w ^ p ^ e ∈ famReflectionGroup F := by
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' p hp.ne_one
  refine ⟨e, ?_⟩
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hord : orderOf (w ^ p ^ e) = m := by
    rw [orderOf_pow_of_dvd hpe (by rw [hem]; exact dvd_mul_right _ _), hem,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpe)]
  exact mem_famReflectionGroup_of_coprime_orderOf hp F hF
    (Subgroup.pow_mem (famStabilizerSubgroup F) hw (p ^ e)) (by
    rw [hord]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm)

private theorem eq_one_of_pow_two_pow_of_odd_prime {G : Type*} [Group G] {p a b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {g : G} (h2 : g ^ (2 ^ a) = 1) (hodd : g ^ (p ^ b) = 1) :
    g = 1 := by
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow _ _
  have hdvd : orderOf g ∣ Nat.gcd (2 ^ a) (p ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hodd)
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem famCentralizer_twoPower_mem_rootSpan [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    {x : ↥(adjointGroup τ K)} (hx : x ∈ famCentralizer F)
    (hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    (x : ModGL τ K) ∈ rootSpan τ K (famKernel F) := by
  classical
  obtain ⟨k, hk⟩ := hx2
  set H : Subgroup (ModGL τ K) := torusGroup τ K
  set Q : Subgroup (ModGL τ K) := rootSpan τ K (famKernel F)
  set M : Subgroup (ModGL τ K) := H ⊔ Q
  set N : Subgroup (ModGL τ K) := (famWeylReps F).map (monomialSubgroup τ K).subtype
  have hxMN : (x : ModGL τ K) ∈ M ⊔ N :=
    map_famCentralizer_le_sup (K := K) F ⟨x, hx, rfl⟩
  have hNM : N ≤ Subgroup.normalizer (M : Set (ModGL τ K)) := by
    simpa [H, Q, M, N] using map_famWeylReps_le_normalizer (K := K) F
  have hxMul : (x : ModGL τ K) ∈ (M : Set (ModGL τ K)) * (N : Set (ModGL τ K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M N hNM]
    exact hxMN
  obtain ⟨m, hm, n, hn, hmn⟩ := hxMul
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  have hw : weylQuotientHom τ K n₀ ∈ famStabilizerSubgroup F :=
    map_weylQuotientHom_famWeylReps_le (K := K) F ⟨n₀, hn₀, rfl⟩
  obtain ⟨e, he⟩ := exists_pow_mem_famReflectionGroup (K := K) hp F hF hw
  have hnpow : (n₀ : ModGL τ K) ^ (p ^ e) ∈ M := by
    have hmem : weylQuotientHom τ K (n₀ ^ p ^ e) ∈ famReflectionGroup F := by
      rw [map_pow]
      exact he
    simpa [H, Q, M, Subgroup.coe_pow] using coe_mem_torus_sup_rootSpan_of_mem (K := K) hmem
  have hxNM : (x : ModGL τ K) ∈ N ⊔ M := by
    rw [sup_comm]
    exact hxMN
  let A : Subgroup (ModGL τ K) := N ⊔ M
  let xA : A := ⟨(x : ModGL τ K), hxNM⟩
  haveI hMnorm : (M.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hNM
  have hmA : m ∈ A := Subgroup.mem_sup_right hm
  have hnA : (n₀ : ModGL τ K) ∈ A := Subgroup.mem_sup_left ⟨n₀, hn₀, rfl⟩
  have hx2A : xA ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa [xA, Subgroup.coe_pow] using
      congrArg (fun y : ↥(adjointGroup τ K) => (y : ModGL τ K)) hk
  have hxA_eq : xA = (⟨m, hmA⟩ : A) * (⟨(n₀ : ModGL τ K), hnA⟩ : A) := by
    apply Subtype.ext
    simpa [xA] using hmn.symm
  have hq_m : QuotientGroup.mk' (M.subgroupOf A) (⟨m, hmA⟩ : A) = 1 :=
    (QuotientGroup.eq_one_iff (⟨m, hmA⟩ : A)).2 hm
  have hq_eq : QuotientGroup.mk' (M.subgroupOf A) xA =
      QuotientGroup.mk' (M.subgroupOf A) (⟨(n₀ : ModGL τ K), hnA⟩ : A) := by
    rw [hxA_eq, map_mul, hq_m, one_mul]
  have hq2 : (QuotientGroup.mk' (M.subgroupOf A) xA) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hx2A, map_one]
  have hqp : (QuotientGroup.mk' (M.subgroupOf A) xA) ^ (p ^ e) = 1 := by
    rw [hq_eq, ← map_pow]
    exact (QuotientGroup.eq_one_iff ((⟨(n₀ : ModGL τ K), hnA⟩ : A) ^ (p ^ e))).2 (by
      rw [Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_pow] using hnpow)
  have hq_one : QuotientGroup.mk' (M.subgroupOf A) xA = 1 :=
    eq_one_of_pow_two_pow_of_odd_prime hp hp2 hq2 hqp
  have hxM : (x : ModGL τ K) ∈ M := by
    have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff xA).1 hq_one)
    simpa [xA] using this
  have hHQ : H ≤ Subgroup.normalizer (Q : Set (ModGL τ K)) := by
    simpa [H, Q] using
      torusGroup_le_normalizer_rootSpan (K := K) (S := famKernel F) (fun α hα => hα.1)
  haveI hQnorm : (Q.subgroupOf M).Normal := by
    simpa [M, H] using Subgroup.normal_subgroupOf_sup_of_le_normalizer hHQ
  let xM : M := ⟨(x : ModGL τ K), hxM⟩
  have hxM2 : xM ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa [xM, Subgroup.coe_pow] using
      congrArg (fun y : ↥(adjointGroup τ K) => (y : ModGL τ K)) hk
  have hqQ2 : (QuotientGroup.mk' (Q.subgroupOf M) xM) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hxM2, map_one]
  have hcardodd : ¬ 2 ∣ Nat.card H := by
    simpa [H] using not_dvd_card_torusGroup (τ := τ) (K := K) 2
  have hdvdH : orderOf (QuotientGroup.mk' (Q.subgroupOf M) xM) ∣ Nat.card H := by
    refine (orderOf_dvd_natCard _).trans ?_
    haveI hQH : (Q.subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hHQ
    haveI hQs : (Q.subgroupOf (H ⊔ Q)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hHQ
    have hiso := (QuotientGroup.quotientInfEquivProdNormalizerQuotient H Q hHQ).toEquiv
    rw [show M = H ⊔ Q from rfl, ← Nat.card_congr hiso]
    exact Subgroup.card_quotient_dvd_card _
  have hcopH : Nat.Coprime (Nat.card H) (2 ^ k) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hcardodd).symm.pow_right k
  have hone : orderOf (QuotientGroup.mk' (Q.subgroupOf M) xM) = 1 := by
    have h := Nat.dvd_gcd hdvdH (orderOf_dvd_of_pow_eq_one hqQ2)
    rw [hcopH.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  have hqQ1 : QuotientGroup.mk' (Q.subgroupOf M) xM = 1 := orderOf_eq_one_iff.mp hone
  have hxQ : (x : ModGL τ K) ∈ Q := by
    have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff xM).1 hqQ1)
    simpa [xM] using this
  simpa [Q] using hxQ

theorem famCentralizer_twoPower_mem_rootSpan_of_algebraic
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    {I : Type*} [Finite I] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : I → Fin τ.rank → Lˣ) (ha : ∀ i, ∃ n : ℕ, (a i) ^ (p ^ n) = 1)
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcomm : ∀ i, x * rootDiagUnit τ (a i) = rootDiagUnit τ (a i) * x)
    (hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    x ∈ rootSpan τ L (famKernel (Set.range a)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨S, hS⟩ := CFSG.LieType.Chevalley.exists_finset_descent hx
  obtain ⟨M, hMf, hSM, _hbase⟩ := exists_finite_subfield_of_finset
    (K := ZMod 2) (L := L)
    (S ∪ Finset.univ.image fun ij : I × Fin τ.rank => (a ij.1 ij.2 : L))
  have : Finite M := hMf
  have hS_M : (S : Set L) ⊆ M := fun c hc =>
    hSM (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hc)))
  have haM (i : I) (j : Fin τ.rank) : (a i j : L) ∈ M :=
    hSM (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)))
  let a' : I → Fin τ.rank → Mˣ := fun i j =>
    Units.mk0 ⟨(a i j : L), haM i j⟩ (by
      intro h
      have : (a i j : L) = 0 := congrArg Subtype.val h
      exact (Units.ne_zero (a i j)) this)
  have htuple (i : I) :
      (fun j => Units.map M.subtype.toMonoidHom (a' i j)) = a i := by
    ext j
    rfl
  have huinj : Function.Injective (Units.map M.subtype.toMonoidHom) :=
    Units.map_injective M.subtype.injective
  obtain ⟨y, hy, hye⟩ := hS M hS_M
  have hMinj : Function.Injective (baseChangeGL (τ := τ) M.subtype) :=
    baseChangeGL_injective M.subtype
  have hap : ∀ b ∈ Set.range a', ∃ n : ℕ, b ^ (p ^ n) = 1 := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := ha i
    refine ⟨n, funext fun j => ?_⟩
    apply huinj
    change Units.map M.subtype.toMonoidHom ((a' i j) ^ (p ^ n)) =
      Units.map M.subtype.toMonoidHom 1
    rw [map_pow, map_one, congrFun (htuple i) j]
    exact congrFun hn j
  have hyfam : (⟨y, hy⟩ : ↥(adjointGroup τ M)) ∈ famCentralizer (Set.range a') := by
    rintro _ ⟨i, rfl⟩
    apply hMinj
    simp only [map_mul, map_inv, baseChangeGL_rootDiagUnit, htuple, hye]
    rw [← hcomm i]
    simp [mul_assoc]
  have hy2 : ∃ k : ℕ, (⟨y, hy⟩ : ↥(adjointGroup τ M)) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hx2
    refine ⟨k, Subtype.ext ?_⟩
    apply hMinj
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one, map_pow, map_one, hye] using hk
  have hkernel : famKernel (Set.range a') = famKernel (Set.range a) := by
    ext α
    simp only [famKernel, Set.mem_setOf_eq, Set.forall_mem_range]
    apply and_congr_right
    intro _
    constructor
    · intro h i
      have h' := congrArg (Units.map M.subtype.toMonoidHom) (h i)
      rw [← rootChar_map_tuple, htuple i, map_one] at h'
      exact h'
    · intro h i
      apply huinj
      rw [← rootChar_map_tuple, htuple i, h i, map_one]
  have hroot := famCentralizer_twoPower_mem_rootSpan hp hp2 (Set.range a') hap hyfam hy2
  rw [hkernel] at hroot
  have hbc := CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan (ι := M.subtype) hroot
  simpa only [hye] using hbc

theorem oTwoPrime_famCentralizer_le_rootSpan_of_algebraic
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    {I : Type*} [Finite I] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : I → Fin τ.rank → Lˣ) (ha : ∀ i, ∃ n : ℕ, (a i) ^ (p ^ n) = 1)
    (Y : Subgroup (ModGL τ L)) (hY : Y ≤ adjointGroup τ L) :
    ggOTwoPrime (Y ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit τ (a i))) ≤
      rootSpan τ L (famKernel (Set.range a)) ⊓ Y := by
  refine le_inf ?_ ((ggOTwoPrime_le _).trans inf_le_left)
  rw [ggOTwoPrime, Subgroup.closure_le]
  rintro x ⟨hx, k, hk⟩
  refine famCentralizer_twoPower_mem_rootSpan_of_algebraic hp hp2 a ha
    (hY hx.1) ?_ ⟨k, hk⟩
  intro i
  exact ((Subgroup.mem_centralizer_iff.mp hx.2) _ ⟨i, rfl⟩).symm

theorem oTwoPrime_famCentralizer_eq_su_range_of_rootSpan
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    {I : Type*} [Finite I] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : I → Fin τ.rank → Lˣ) (ha : ∀ i, ∃ k : ℕ, (a i) ^ (p ^ k) = 1)
    (Y : Subgroup (ModGL τ L)) (hY : Y ≤ adjointGroup τ L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (θ : CFSG.ClassicalInvolution.Phan.Su K 2 f n →* ModGL τ L)
    (hrange : θ.range = rootSpan τ L (famKernel (Set.range a)) ⊓ Y) :
    ggOTwoPrime (Y ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit τ (a i))) =
      θ.range := by
  refine le_antisymm
    ((oTwoPrime_famCentralizer_le_rootSpan_of_algebraic hp hp2 a ha Y hY).trans hrange.ge) ?_
  apply ggSu_range_le_ggOTwoPrime hK hn θ
  rw [hrange]
  refine le_inf inf_le_right ?_
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp
    ((rootSpan_le_centralizer (a i) (famKernel_subset (Set.range a) ⟨i, rfl⟩)) hx.1)) _
      (by simp)

end CFSG.StandardType.LayerSixE

end
