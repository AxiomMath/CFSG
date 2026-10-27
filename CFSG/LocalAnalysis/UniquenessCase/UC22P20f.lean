module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.LieType.Multipliers.U43
import CFSG.Quasithin.Background.A318PC7
import CFSG.Adapters.LinearCatalogStated
import CFSG.Models.Blueprint
import CFSG.RankThree.PartTwo.Census.NineCoverU43
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

theorem uc22p20f_lift_normalizer {X G : Type} [Group X] [Finite X] [Group G] (φ : X →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker = Subgroup.center X) (hZ : IsPGroup 2 φ.ker)
    (Q₀ : Sylow 2 G) {d₀ : G}
    (hd₀N : d₀ ∈ Subgroup.normalizer ((Q₀ : Subgroup G) : Set G))
    (hd₀1 : d₀ ≠ 1) (hd₀odd : Odd (orderOf d₀)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ P : Sylow 2 X,
      ∃ x ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), orderOf x = p ∧
        x ∉ Subgroup.center X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G := Finite.of_surjective φ hφ
  have hord1 : orderOf d₀ ≠ 1 := fun h => hd₀1 (orderOf_eq_one_iff.mp h)
  have hord0 : orderOf d₀ ≠ 0 := (orderOf_pos d₀).ne'
  have hpprime : (orderOf d₀).minFac.Prime := Nat.minFac_prime hord1
  have hpdvd : (orderOf d₀).minFac ∣ orderOf d₀ := Nat.minFac_dvd _
  have hp2 : (orderOf d₀).minFac ≠ 2 := by
    intro h
    rw [h] at hpdvd
    exact (Nat.not_even_iff_odd.mpr hd₀odd) (even_iff_two_dvd.mpr hpdvd)
  refine ⟨(orderOf d₀).minFac, hpprime, hp2, fun P => ?_⟩
  set p := (orderOf d₀).minFac
  have hdp : orderOf (d₀ ^ (orderOf d₀ / p)) = p := orderOf_pow_orderOf_div hord0 hpdvd
  set Q : Sylow 2 G := Sylow.mapSurjective hφ P
  have hQ : (Q : Subgroup G) = (P : Subgroup X).map φ := Sylow.coe_mapSurjective hφ P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ Q
  have hnorm : ∀ n : ℕ, g * d₀ ^ n * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro n
    have h1 : (d₀ ^ n) • Q₀ = Q₀ :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.pow_mem _ hd₀N n)
    refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
    calc (g * d₀ ^ n * g⁻¹) • Q = (g * d₀ ^ n * g⁻¹) • (g • Q₀) := by rw [hg]
      _ = g • ((d₀ ^ n) • Q₀) := by simp [mul_smul]
      _ = Q := by rw [h1, hg]
  obtain ⟨y, hy⟩ := hφ (g * d₀ ^ (orderOf d₀ / p) * g⁻¹)
  have hkerP : φ.ker ≤ (P : Subgroup X) := hZ.le_sylow_of_normal P
  have hmemP : ∀ u : X, u ∈ (P : Subgroup X) ↔ φ u ∈ (Q : Subgroup G) := by
    intro u
    rw [hQ]
    constructor
    · intro hu
      exact Subgroup.mem_map_of_mem φ hu
    · intro hu
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
      have hker' : v⁻¹ * u ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hvu, inv_mul_cancel]
      have : u = v * (v⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ hv (hkerP hker')
  have hyN : y ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [hmemP u, hmemP (y * u * y⁻¹), map_mul, map_mul, map_inv, hy]
    exact Subgroup.mem_normalizer_iff.mp (hnorm (orderOf d₀ / p)) (φ u)
  have hdy : orderOf (φ y) = p := by
    rw [hy]
    have : g * d₀ ^ (orderOf d₀ / p) * g⁻¹ = (MulAut.conj g) (d₀ ^ (orderOf d₀ / p)) := by
      simp [MulAut.conj_apply]
    rw [this, MulEquiv.orderOf_eq, hdp]
  have hpy : p ∣ orderOf y := hdy ▸ orderOf_map_dvd φ y
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  refine ⟨y ^ (orderOf y / p), Subgroup.pow_mem _ hyN _, orderOf_pow_orderOf_div hy0 hpy, ?_⟩
  intro hcen
  rw [← hker] at hcen
  have hord := orderOf_pow_orderOf_div hy0 hpy
  obtain ⟨k, hk⟩ := (hZ ⟨_, hcen⟩ : ∃ k : ℕ, (⟨_, hcen⟩ : φ.ker) ^ 2 ^ k = 1)
  have hdvd : p ∣ 2 ^ k := by
    have h1 : orderOf (⟨_, hcen⟩ : φ.ker) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, hord] at h1
    exact h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp (hpprime.dvd_of_dvd_pow hdvd))

theorem uc22p20f_isPGroup_two_ker {X J : Type} [Group X] [Finite X] [Group.IsPerfect X] [Group J]
    (f : X →* J) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X)
    (hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ R : Sylow r J, IsCyclic R) :
    IsPGroup 2 f.ker := by
  haveI : Finite J := Finite.of_surjective f hf
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card f.ker).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) Nat.card_pos.ne' ?_⟩
  intro r hr hrdvd
  by_contra hr2
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) r hrdvd
  have hzp : IsPGroup r (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  obtain ⟨C, hC⟩ := hzp.exists_le_sylow
  obtain ⟨Q⟩ : Nonempty (Sylow r J) := inferInstance
  have hbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hf hker C Q
    (hcyc r hr2 Q)
  have hz1 : z = 1 := by
    have : z ∈ (C : Subgroup f.ker) := hC (Subgroup.mem_zpowers z)
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  rw [hz1, orderOf_one] at hz
  exact hr.one_lt.ne hz

theorem uc22p20f_sz_normalizer_odd (m : ℕ) (hm : 0 < m) :
    ∃ Q : Sylow 2 (SuzukiMatrixGroup m),
      ∃ d ∈ Subgroup.normalizer ((Q : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)),
        d ≠ 1 ∧ Odd (orderOf d) := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let G := SuzukiMatrixGroup m
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, hpi_formula, hFp, _hF_pow_four,
      _hF_order_four, _hF_class, hFcard, _hF_typeA, _hroot_mul,
      _hcommutator, _hcommutator_coordinates, htorus_equiv, _htorus_conjugation, _hdisjoint,
      _hfixed_point_free⟩
  rcases htorus_equiv with ⟨eH, _heH⟩
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hHcard : Nat.card H = q - 1 := by
    calc
      Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hKcard]
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let R : Subgroup G := F.subgroupOf (SuzukiMatrixGroup m)
  let T : Subgroup G := H.subgroupOf (SuzukiMatrixGroup m)
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hT_le_normalizerR : T ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hg_normalizes :
        ((g : G) : GL (Fin 4) K) ∈
          Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
      hH_le_normalizerF hg
    rw [Subgroup.mem_normalizer_iff] at hg_normalizes ⊢
    intro r
    exact hg_normalizes ((r : G) : GL (Fin 4) K)
  let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
  let eT : T ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G
  have hRp : IsPGroup 2 R := hFp.of_equiv eR.symm
  have hRcard : Nat.card R = q ^ 2 := by
    calc
      Nat.card R = Nat.card F := Nat.card_congr eR.toEquiv
      _ = q ^ 2 := hFcard
  have hTcard : Nat.card T = q - 1 := by
    calc
      Nat.card T = Nat.card H := Nat.card_congr eT.toEquiv
      _ = q - 1 := hHcard
  have hq_even : Even q := by
    dsimp only [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hq8 : 8 ≤ q := by
    dsimp only [q]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq_sub_one_odd : Odd (q - 1) :=
    Nat.Even.sub_odd hq_pos hq_even odd_one
  have hB := CFSG.Open.bender_suzukiMatrixGroup_borel m hm
  obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup G) = q ^ 2 := (hB Q).2.2.2.2
  have hRQeq : R = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hRQ (by rw [hRcard, hQcard])
  have hTne : Nontrivial T :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; omega)
  obtain ⟨d, hd⟩ := exists_ne (1 : T)
  refine ⟨Q, (d : G), ?_, ?_, ?_⟩
  · rw [← hRQeq]
    exact hT_le_normalizerR d.2
  · intro h
    exact hd (Subtype.ext h)
  · have hdvd : orderOf d ∣ Nat.card T := orderOf_dvd_natCard d
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (hTcard ▸ hq_sub_one_odd) hdvd

theorem uc22p20f_suzukiCoverFact : SuzukiCoverFact := by
  intro X _ _ hq ⟨f, hf⟩
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hf
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  let φ : X →* SuzukiMatrixGroup m :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center X := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hZ : IsPGroup 2 φ.ker :=
    uc22p20f_isPGroup_two_ker φ hφ hker.le fun r _ hr R =>
      lemma114_suzuki_oddSylow_isCyclic_of_equiv (MulEquiv.refl _) r hr R
  obtain ⟨Q₀, d₀, hd₀N, hd₀1, hd₀odd⟩ := uc22p20f_sz_normalizer_odd m hm
  exact uc22p20f_lift_normalizer φ hφ hker hZ Q₀ hd₀N hd₀1 hd₀odd


theorem uc22p20f_threeNoncentral_of_threeFree {X : Type} [Group X] [Finite X]
    (h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X)) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X)) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : 3 ∣ Nat.card X := h3.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 hX
  refine ⟨x, hx, fun hxZ => hZ ?_⟩
  have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hxZ
  rwa [hx] at this

theorem uc22p20f_threeNoncentral_of_uniqueThree {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    (hu : ∀ a b : X, a ∈ Subgroup.center X → b ∈ Subgroup.center X → orderOf a = 3 →
      orderOf b = 3 → b ∈ Subgroup.zpowers a) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect X := ⟨hX⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 h3
  have hz3 : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzcard : Nat.card (Subgroup.zpowers (z : X)) = 3 := by rw [Nat.card_zpowers, hz3]
  have hzp : IsPGroup 3 (Subgroup.zpowers (z : X)) := IsPGroup.of_card (n := 1) (by rw [hzcard, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hScyc : IsCyclic (S : Subgroup X) :=
    CFSG.Quasithin.A318P.isCyclic_of_unique_three (Z := Subgroup.zpowers (z : X)) S.isPGroup'
      hzcard fun r _ hr3 => hu (z : X) r z.2 (hcon r hr3) hz3 hr3
  have hzS : (z : X) ∈ (S : Subgroup X) := hS (Subgroup.mem_zpowers _)
  have hder := CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived S ⟨z, hzS⟩ z.2
  haveI : IsMulCommutative (S : Subgroup X) := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  rw [commutator_eq_bot] at hder
  have hz1 : (z : X) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hder)
  rw [hz1, orderOf_one] at hz3
  exact absurd hz3 (by norm_num)

@[expose] def ThreeNoncentralNoncyclicCentre : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    CFSG.Assembly.InCatalog (X ⧸ Subgroup.center X) →
    (∃ a b : X, a ∈ Subgroup.center X ∧ b ∈ Subgroup.center X ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ Subgroup.zpowers a) →
    ∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X

theorem uc22p20f_threeNoncentralFact_of_residual (h : ThreeNoncentralNoncyclicCentre) :
    ThreeNoncentralFact := by
  intro X _ _ hq hcat h3
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
  · by_cases hnc : ∃ a b : X, a ∈ Subgroup.center X ∧ b ∈ Subgroup.center X ∧ orderOf a = 3 ∧
        orderOf b = 3 ∧ b ∉ Subgroup.zpowers a
    · exact h X hq hcat hnc
    · refine uc22p20f_threeNoncentral_of_uniqueThree hq.1 hZ fun a b ha hb hao hbo => ?_
      by_contra hb'
      exact hnc ⟨a, b, ha, hb, hao, hbo, hb'⟩
  · exact uc22p20f_threeNoncentral_of_threeFree h3 hZ


section Tables

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem uc22p20f_pow_self_eq_one (m : ℕ) (u : Multiplicative (ZMod m)) : u ^ m = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

theorem uc22p20f_pow_eq_one_of_dvd (m k : ℕ) (hk : m ∣ k) (u : Multiplicative (ZMod m)) :
    u ^ k = 1 := by
  obtain ⟨c, rfl⟩ := hk
  rw [pow_mul, uc22p20f_pow_self_eq_one, one_pow]

theorem uc22p20f_zpowers_of_pow_mem_cyclic {A G B : Type*} [Group A] [Group G] [Group B]
    [IsCyclic B] (ψ : A →* G) (f : B →* A) (N : ℕ) (hN : ¬ 3 ∣ N)
    (hC : ∀ x : A, ∃ y : B, x ^ N = f y) {a b : G} (ha : a ∈ ψ.range) (hb : b ∈ ψ.range)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) : b ∈ Subgroup.zpowers a := by
  let Y : Subgroup G := (ψ.comp f).range
  haveI : IsCyclic Y := isCyclic_of_surjective (ψ.comp f).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have hmem : ∀ z : G, z ∈ ψ.range → orderOf z = 3 → z ∈ Y := by
    intro z hz hz3
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy⟩ := hC x
    have hzN : (ψ x) ^ N ∈ Y := ⟨y, by simp [← map_pow, hy]⟩
    have hcop : Nat.Coprime N 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN |>.symm
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := ψ x) (n := N) (by rw [hz3]; exact hcop)
    have : ψ x = ((ψ x) ^ N) ^ k := hk.symm
    rw [this]
    exact Subgroup.pow_mem _ hzN k
  have haY := hmem a ha ha3
  have hbY := hmem b hb hb3
  let a' : Y := ⟨a, haY⟩
  let b' : Y := ⟨b, hbY⟩
  have hca : Nat.card (Subgroup.zpowers a') = 3 := by
    rw [Nat.card_zpowers]
    have : orderOf a' = 3 := by rw [← ha3]; exact Subgroup.orderOf_mk a haY
    exact this
  have hcb : Nat.card (Subgroup.zpowers b') = 3 := by
    rw [Nat.card_zpowers]
    have : orderOf b' = 3 := by rw [← hb3]; exact Subgroup.orderOf_mk b hbY
    exact this
  haveI : Finite ↥(Subgroup.zpowers a') := by
    have : Nat.card (Subgroup.zpowers a') ≠ 0 := by rw [hca]; norm_num
    exact Nat.finite_of_card_ne_zero this
  haveI : Finite ↥(Subgroup.zpowers b') := by
    have : Nat.card (Subgroup.zpowers b') ≠ 0 := by rw [hcb]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have heq : Subgroup.zpowers a' = Subgroup.zpowers b' :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [hca, hcb])
  have hb'mem : b' ∈ Subgroup.zpowers a' := heq ▸ Subgroup.mem_zpowers b'
  obtain ⟨k, hk⟩ := hb'mem
  exact ⟨k, congrArg Subtype.val hk⟩

theorem uc22p20f_nine_dvd_card_of_central {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : a ∈ Subgroup.center G) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hba : b ∉ Subgroup.zpowers a) : 9 ∣ Nat.card G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ha)
  have hmk : (QuotientGroup.mk b : G ⧸ Subgroup.zpowers a) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hba
  have hmk3 : (QuotientGroup.mk b : G ⧸ Subgroup.zpowers a) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hb3, pow_orderOf_eq_one]
    rfl
  have hord : orderOf (QuotientGroup.mk b : G ⧸ Subgroup.zpowers a) = 3 :=
    orderOf_eq_prime hmk3 hmk
  have h3q : 3 ∣ Nat.card (G ⧸ Subgroup.zpowers a) := hord ▸ orderOf_dvd_natCard _
  have h3H : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers a), h3H]
  exact (mul_dvd_mul_right h3q 3 : 3 * 3 ∣ _ * 3)

theorem uc22p20f_nine_dvd_card_center {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (hb3 : orderOf b = 3) (hba : b ∉ Subgroup.zpowers a) :
    9 ∣ Nat.card (Subgroup.center G) := by
  refine uc22p20f_nine_dvd_card_of_central (a := (⟨a, ha⟩ : Subgroup.center G))
    (b := (⟨b, hb⟩ : Subgroup.center G)) ?_ ?_ ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp g.2 a).symm)
  · rw [← ha3, ← Subgroup.orderOf_coe]
  · rw [← hb3, ← Subgroup.orderOf_coe]
  · intro h
    apply hba
    obtain ⟨k, hk⟩ := h
    exact ⟨k, congrArg Subtype.val hk⟩

theorem uc22p20f_genericOrders_snd_not_three (t : StatedLieTag) (n p f : ℕ) :
    ¬ 3 ∣ (genericOrders t n p f).2 := by
  unfold genericOrders
  cases t <;> simp <;> split_ifs <;> omega

theorem uc22p20f_exceptionalOrders_snd_not_three (t : StatedLieTag) (n p f : ℕ)
    (h : ¬ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1)) : ¬ 3 ∣ (exceptionalOrders t n p f).2 := by
  unfold exceptionalOrders
  split <;> simp_all

theorem uc22p20f_exceptionalOrders_fst_three (t : StatedLieTag) (n p f : ℕ)
    (h : 3 ∣ (exceptionalOrders t n p f).1) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
    (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  unfold exceptionalOrders at h
  split at h <;> simp_all

theorem uc22p20f_genericOrders_fst_not_three (t : StatedLieTag) (n p f : ℕ)
    (h : (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1)) : ¬ 3 ∣ (genericOrders t n p f).1 := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp [genericOrders]

theorem uc22p20f_zpowers_of_table (t : StatedLieTag) (n p f : ℕ)
    (htuple : ¬ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1))
    {G : Type*} [Group G] (ψ : generic t n p f × exceptional t n p f →* G)
    {a b : G} (ha : a ∈ ψ.range) (hb : b ∈ ψ.range) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    b ∈ Subgroup.zpowers a := by
  have hg2 := uc22p20f_genericOrders_snd_not_three t n p f
  have he2 := uc22p20f_exceptionalOrders_snd_not_three t n p f htuple
  by_cases he1 : 3 ∣ (exceptionalOrders t n p f).1
  ·
    have hg1 : ¬ 3 ∣ (genericOrders t n p f).1 := by
      refine uc22p20f_genericOrders_fst_not_three t n p f ?_
      rcases uc22p20f_exceptionalOrders_fst_three t n p f he1 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h htuple
    have hN : ¬ 3 ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        (exceptionalOrders t n p f).2 := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · exact hg1 h
        · exact hg2 h
      · exact he2 h
    refine uc22p20f_zpowers_of_pow_mem_cyclic ψ
      ((MonoidHom.inr (generic t n p f) (exceptional t n p f)).comp
        (MonoidHom.inl (Multiplicative (ZMod (exceptionalOrders t n p f).1))
          (Multiplicative (ZMod (exceptionalOrders t n p f).2)))) _ hN ?_ ha hb ha3 hb3
    rintro ⟨⟨u₁, u₂⟩, ⟨v₁, v₂⟩⟩
    refine ⟨v₁ ^ ((genericOrders t n p f).1 * (genericOrders t n p f).2 *
        (exceptionalOrders t n p f).2), ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.inl_apply, Prod.pow_mk]
    rw [uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) u₁,
      uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _) u₂,
      uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_left dvd_rfl _) v₂]
    rfl
  ·
    have hN : ¬ 3 ∣ (genericOrders t n p f).2 * (exceptionalOrders t n p f).1 *
        (exceptionalOrders t n p f).2 := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · exact hg2 h
        · exact he1 h
      · exact he2 h
    refine uc22p20f_zpowers_of_pow_mem_cyclic ψ
      ((MonoidHom.inl (generic t n p f) (exceptional t n p f)).comp
        (MonoidHom.inl (Multiplicative (ZMod (genericOrders t n p f).1))
          (Multiplicative (ZMod (genericOrders t n p f).2)))) _ hN ?_ ha hb ha3 hb3
    rintro ⟨⟨u₁, u₂⟩, ⟨v₁, v₂⟩⟩
    refine ⟨u₁ ^ ((genericOrders t n p f).2 * (exceptionalOrders t n p f).1 *
        (exceptionalOrders t n p f).2), ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, Prod.pow_mk]
    rw [uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) u₂,
      uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _) v₁,
      uc22p20f_pow_eq_one_of_dvd _ _ (Dvd.dvd.mul_left dvd_rfl _) v₂]
    rfl

theorem uc22p20f_exists_surj_centre {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    (hGA : CFSG.Open.GriessAllModelsStatement) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) t n p f) :
    ∃ ψ : generic t n p f × exceptional t n p f →* X,
      ∀ z ∈ Subgroup.center X, z ∈ ψ.range := by
  haveI : Group.IsPerfect X := ⟨hX⟩
  let q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  obtain ⟨-, ⟨eM⟩⟩ := hGA _ t n p f hm
  let φ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hker.le
  have hφ : Function.Surjective φ :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker.le
  let ψ : generic t n p f × exceptional t n p f →* X :=
    q.ker.subtype.comp (φ.comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom.comp
        eM.symm.toMonoidHom))
  refine ⟨ψ, fun z hz => ?_⟩
  have hz' : z ∈ q.ker := by rw [hker]; exact hz
  obtain ⟨w, hw⟩ := hφ ⟨z, hz'⟩
  obtain ⟨u, hu⟩ := (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (X ⧸ Subgroup.center X)).surjective w
  refine ⟨eM u, ?_⟩
  change ((φ ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _)
    (eM.symm (eM u))) : q.ker) : X) = z
  rw [eM.symm_apply_apply, hu, hw]

theorem uc22p20f_exists_lieModel_of_index {G : Type} [Group G] (d : TauCeti.ValidLieTypeIndex)
    (e : G ≃* d.Group) :
    ∃ (t : StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel G t n p f := by
  obtain ⟨d, hv⟩ := d
  have hcl : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedClassicalModel G t n p f →
      ∃ (t : StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel G t n p f :=
    fun {t n p f} h => ⟨t, n, p, f, ⟨h.1, .inl h⟩⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q => exact hcl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
  | twistedA r q => exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
    · by_cases hp : q.p = 2
      · exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e)
      · exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3 e)
  | C r q => exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)
  | D r q => exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
  | twistedD r q =>
    exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
  | E6 q =>
    exact ⟨.E6, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.E6 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | E7 q =>
    exact ⟨.E7, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.E7 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | E8 q =>
    exact ⟨.E8, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.E8 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | F4 q =>
    exact ⟨.F4, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.F4 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | G2 q =>
    have h3 : 3 ≤ q.p ^ q.exponent := by
      simpa only [TauCeti.PrimePower.card_def] using hrange
    exact ⟨.G2, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      .inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | twistedE6 q =>
    exact ⟨.twistedE6, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.twistedE6 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | trialityD4 q =>
    exact ⟨.trialityD4, 0, q.p, q.exponent, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      .inr ⟨rfl, ⟨.trialityD4 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | suzuki m =>
    have hm : 1 ≤ m := hrange
    exact ⟨.twistedB2, 0, 2, 2 * m + 1, ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
      .inr ⟨rfl, ⟨.suzuki m, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | reeG2 m =>
    have hm : 1 ≤ m := hrange
    exact ⟨.twistedG2, 0, 3, 2 * m + 1, ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
      .inr ⟨rfl, ⟨.reeG2 m, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | reeF4 m =>
    have hm : 1 ≤ m := hrange
    exact ⟨.twistedF4, 0, 2, 2 * m + 1, ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
      .inr ⟨rfl, ⟨.reeF4 m, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  | tits =>
    exact ⟨.Tits, 0, 2, 1, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      .inr ⟨rfl, ⟨.tits, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩

end Tables

open CFSG.RankThree.PartTwo.Sec4.Census in
theorem uc22p20f_noncentral_of_u43 {X : Type} [Group X]
    (eX : X ⧸ Subgroup.center X ≃* CFSG.LieType.Multipliers.U43.X₀) :
    ∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X := by
  let φ : X →* CFSG.LieType.Multipliers.U43.X₀ :=
    eX.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφ : Function.Surjective φ := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center X := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hu1 : NineCoverU43.u1 ∈ NineCoverU43.theta.range := ⟨_, rfl⟩
  obtain ⟨y, hy, hy3⟩ := NineCoverU43.exists_lift_of_mem_range hφ hker.le hu1
  have hu1ne : NineCoverU43.u1 ≠ 1 := by
    intro h
    have := NineCoverU43.theta_injective (a₁ := Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)))
      (a₂ := 1) (by rw [map_one]; exact h)
    have h2 := congrArg Multiplicative.toAdd this
    simp at h2
  have hy1 : y ≠ 1 := by
    intro h
    apply hu1ne
    rw [← hy, h, map_one]
  refine ⟨y, orderOf_eq_prime hy3 hy1, ?_⟩
  intro hc
  rw [← hker] at hc
  exact hu1ne (hy ▸ hc)

theorem uc22p20f_threeNoncentralNoncyclicCentre_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    ThreeNoncentralNoncyclicCentre := by
  intro X _ _ hq hcat ⟨a, b, ha, hb, ha3, hb3, hba⟩
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have h9 : 9 ∣ Nat.card (Subgroup.center X) := uc22p20f_nine_dvd_card_center ha hb ha3 hb3 hba
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ =>
    exfalso
    obtain ⟨u, v, huv⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian X hq
    exact huv (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn =>
    exfalso
    have hdvd :=
      CFSG.ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier (Q := X) e
    rw [(hAlt n hn).2] at hdvd
    split_ifs at hdvd <;> (have := Nat.le_of_dvd (by norm_num) (h9.trans hdvd); omega)
  | sporadic s =>
    exfalso
    have hdvd :=
      CFSG.ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier (Q := X) e
    rw [hSpor.1 s] at hdvd
    have h9' := h9.trans hdvd
    unfold CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder at h9'
    split at h9' <;> omega
  | lie d =>
    obtain ⟨t, n, p, f, hmodel⟩ := uc22p20f_exists_lieModel_of_index d e
    obtain ⟨ψ, hψ⟩ := uc22p20f_exists_surj_centre hq.1 hGA hmodel
    by_cases htuple : t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := htuple
      have hbp : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 4 3 1 :=
        CFSG.Models.LieModel.toBlueprint (by decide) hmodel
      obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hbp
      exact uc22p20f_noncentral_of_u43 eX
    · exact absurd
        (uc22p20f_zpowers_of_table t n p f htuple ψ (hψ a ha) (hψ b hb) ha3 hb3) hba

theorem uc22p20f_threeNoncentralFact_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    ThreeNoncentralFact :=
  uc22p20f_threeNoncentralFact_of_residual
    (uc22p20f_threeNoncentralNoncyclicCentre_of_tables hGA hAlt hSpor)


theorem uc22p20f_quasisimpleDichotomy_of_tables
    (hKPSz : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.Assembly.InCatalog S → ¬ 3 ∣ Nat.card S → ∃ f : ℕ, CFSG.Blueprint.SuzukiModel S 2 f)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    QuasisimpleDichotomy :=
  quasisimpleDichotomy_of_parts hKPSz uc22p20f_suzukiCoverFact
    (uc22p20f_threeNoncentralFact_of_tables hGA hAlt hSpor)

end CFSG.LocalAnalysis.UniquenessCase.UC22
