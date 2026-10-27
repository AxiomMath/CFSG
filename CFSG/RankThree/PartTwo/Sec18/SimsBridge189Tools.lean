module

public import CFSG.RankThree.PartTwo.Sec18.SimsBridge189Setting
public import CFSG.RankThree.PartTwo.Sec18.Item189StepMKNormalizer
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

theorem map_fourChar_subgroupOf189 {G : Type*} [Group G] [Finite G] {R X : Subgroup G}
    (hRX : R ≤ X) (i : Fin 4) :
    (fourChar (R.subgroupOf X) i).map X.subtype = fourChar R i := by
  by_cases hi : i = 3
  · subst hi
    rw [Item181ThreeProof.fourChar_three, Item181ThreeProof.fourChar_three,
      Sec20.Res5.map_omegaG_of_injective _ X.subtype_injective,
      Sec20.Res5.map_jG_of_injective _ X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  · exact Sec20.Res5.map_fourChar_subgroupOf hRX i hi

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem sk189_le_normalizer_fourChar189 (i : Fin 4)
    (hn : (fourChar (sSK189 M H c) i).Normal) :
    sk189 M H c ≤ Subgroup.normalizer (fourChar (s189 M H) i : Set G) := by
  intro g hg
  rw [← map_fourChar_subgroupOf189 (le_sup_left : s189 M H ≤ sk189 M H c) i]
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hn.conj_mem y hy ⟨g, hg⟩, by simp⟩

theorem coveredMod189_of_normal (i : Fin 4) (hn : (fourChar (sSK189 M H c) i).Normal) :
    CoveredMod189 M H c (fourChar (s189 M H) i) :=
  le_sup_of_le_left (le_inf le_rfl ((le_sup_right : normalClosureIn M c ≤ sk189 M H c).trans
    (sk189_le_normalizer_fourChar189 i hn)))

section Certified


theorem normalizer_zpowers_le_n189_of_sec18 (h1812 : Item181_2) (hAlt : Item182Alt1C)
    (h1841 : Item184_1) (h1842 : Item184_2) (hset : Setting189 G A M H c) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H := by
  by_cases hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
  · exact normalizerLeN189OfO2Trivial_of_alt1C h1812 hAlt h1841 h1842 G A M H c hset.toSec18H
      hset.hyp187.1 hset.hyp187.2.1 hO
  · exact normalizer_zpowers_le189 hset.hyp187 hO

end Certified

theorem false_of_sup_normalizer_eq_top189 (hset : Setting189 G A M H c)
    (hcN : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H) {i j : Fin 4} (hij : i ≠ j)
    (hi : Subgroup.normalizer (Subgroup.zpowers (cSK189 M H c) : Set ↥(sk189 M H c)) ⊔
      Subgroup.normalizer (fourChar (sSK189 M H c) i : Set ↥(sk189 M H c)) = ⊤)
    (hj : Subgroup.normalizer (Subgroup.zpowers (cSK189 M H c) : Set ↥(sk189 M H c)) ⊔
      Subgroup.normalizer (fourChar (sSK189 M H c) j : Set ↥(sk189 M H c)) = ⊤) : False := by
  have key : ∀ k : Fin 4,
      Subgroup.normalizer (Subgroup.zpowers (cSK189 M H c) : Set ↥(sk189 M H c)) ⊔
          Subgroup.normalizer (fourChar (sSK189 M H c) k : Set ↥(sk189 M H c)) = ⊤ →
        Subgroup.normalizer (fourChar (s189 M H) k : Set G) ≤ n189 H → False := by
    intro k hk hkN
    apply hset.not_le
    have hmap := congrArg (Subgroup.map (sk189 M H c).subtype) hk
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    refine (le_sup_right : normalClosureIn M c ≤ sk189 M H c).trans (hmap.symm.le.trans ?_)
    refine sup_le ((Subgroup.le_normalizer_map _).trans ?_)
      ((Subgroup.le_normalizer_map _).trans ?_)
    · rw [MonoidHom.map_zpowers]
      exact hcN
    · rw [map_fourChar_subgroupOf189 (le_sup_left : s189 M H ≤ sk189 M H c) k]
      exact hkN
  rcases hset.three i j hij with h | h
  · exact key i hi h
  · exact key j hj h

theorem false_of_kAlpha_projSL_two_three189 (hset : Setting189 G A M H c) {f : ℕ}
    (hf : 9 < 3 ^ f) (e : ↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 3 f)) : False := by
  have hf3 : 3 ≤ f := by
    by_contra hlt
    have : 3 ^ f ≤ 9 :=
      calc 3 ^ f ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 := by norm_num
    omega
  have : Finite ↥(projSL 2 (GaloisField 3 f)) := Finite.of_equiv _ e.toEquiv
  have h1 : f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(projSL 2 (GaloisField 3 f))) :=
    (Sec6.Res611Res3.le_pRank_projSL_two (by omega)).trans_eq
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 _)
  have hker : Nat.Coprime 3 (Nat.card (kToKAlpha189 M H c).ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply not_three_dvd_card_theta189 M H c
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective (K := (kToKAlpha189 M H c).ker)
      (normalClosureIn M c).subtype_injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_ker_kToKAlpha189 k).mp hk
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3
    Nat.prime_three (kToKAlpha189 M H c) kToKAlpha189_surjective hker
  have h3 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_equiv 3 (by norm_num) e
  have h4 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3
    (by norm_num) (normalClosureIn M c)
  have h5 := hset.pRank_eq
  omega

private theorem le_centralizer_of_le_normalizer_zpowers189 {Q : Type*} [Group Q]
    {P : Subgroup Q} {x : Q} (hP : IsPGroup 2 P) (hx : x ^ 3 = 1)
    (hxP : ∀ t ∈ P, x * t * x⁻¹ ∈ P)
    (hPN : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Q)) :
    P ≤ Subgroup.centralizer ({x} : Set Q) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hu1 : t * x * t⁻¹ * x⁻¹ ∈ P := by
    have := P.mul_mem ht (hxP t⁻¹ (P.inv_mem ht))
    simpa only [mul_assoc] using this
  have hu2 : t * x * t⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hPN ht) x).mp (Subgroup.mem_zpowers x))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hu3 : (t * x * t⁻¹ * x⁻¹) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu2
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨n, hn⟩ := hP ⟨_, hu1⟩
  have hun : (t * x * t⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hu := (pow_eq_one_iff_of_coprime
    (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3))).mp ⟨hun, hu3⟩
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hu
  exact hu

private theorem exists_conj_sKAlpha189 {a : G}
    (ha : a ∈ Subgroup.normalizer (sk189 M H c : Set G)) :
    ∃ φ : SKAlpha189 M H c ≃* SKAlpha189 M H c, ∀ (y : ↥(sk189 M H c))
      (hy : a * y * a⁻¹ ∈ sk189 M H c),
        φ (alpha189 M H c y) = alpha189 M H c ⟨a * y * a⁻¹, hy⟩ := by
  have hθ : (aschbacherSolvableCore 3 ↥(sk189 M H c)).Characteristic :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.1
  let ψ : ↥(sk189 M H c) ≃* ↥(sk189 M H c) := (sk189 M H c).normalizerMonoidHom ⟨a, ha⟩
  refine ⟨QuotientGroup.congr _ _ ψ (Subgroup.characteristic_iff_map_eq.mp hθ ψ),
    fun y hy => ?_⟩
  have hψ : ψ y = ⟨a * y * a⁻¹, hy⟩ :=
    Subtype.ext ((sk189 M H c).normalizerMonoidHom_apply_apply_coe ⟨a, ha⟩ y)
  rw [← hψ]
  rfl

private theorem map_imAlpha189_le_of_conj {a : G} {φ : SKAlpha189 M H c ≃* SKAlpha189 M H c}
    (haX : a ∈ Subgroup.normalizer (sk189 M H c : Set G))
    (hφ : ∀ (y : ↥(sk189 M H c)) (hy : a * y * a⁻¹ ∈ sk189 M H c),
      φ (alpha189 M H c y) = alpha189 M H c ⟨a * y * a⁻¹, hy⟩)
    {Z : Subgroup G} (haZ : a ∈ Subgroup.normalizer (Z : Set G)) :
    (imAlpha189 M H c Z).map φ.toMonoidHom ≤ imAlpha189 M H c Z := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hyX : a * (y : G) * a⁻¹ ∈ sk189 M H c := (Subgroup.mem_normalizer_iff.mp haX y).mp y.2
  exact ⟨⟨_, hyX⟩, (Subgroup.mem_normalizer_iff.mp haZ y).mp hy, (hφ y hyX).symm⟩

private theorem map_pCoreOf_le_of_map_le189 {Q : Type*} [Group Q] [Finite Q] (p : ℕ)
    (φ : Q ≃* Q) {Y : Subgroup Q} (hY : Y.map φ.toMonoidHom ≤ Y) :
    (CFSG.Open.pCoreOf p Y).map φ.toMonoidHom ≤ CFSG.Open.pCoreOf p Y := by
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p φ Y, Subgroup.eq_of_le_of_card_ge hY
    (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge]

theorem pCoreOf_kAlpha_inf_centralizer_le189
    (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) (hset : Setting189 G A M H c)
    (hθS : theta189 M H c ≤ s189 M H)
    (hSN : sAlpha189 M H c ≤ Subgroup.normalizer
      (Subgroup.zpowers (alpha189 M H c (cSK189 M H c)) : Set (SKAlpha189 M H c))) :
    CFSG.Open.pCoreOf 2 (kAlpha189 M H c ⊓
        Subgroup.centralizer ({alpha189 M H c (cSK189 M H c)} : Set (SKAlpha189 M H c))) ≤
      sAlpha189 M H c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hset.toSec18H
  have hcA : c ∈ A := mem_of_sec18H189 h
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hc3 : alpha189 M H c (cSK189 M H c) ^ 3 = 1 := by
    have : (⟨c, mem_sk189_self M H c⟩ : ↥(sk189 M H c)) ^ 3 = 1 :=
      Subtype.ext (by simpa using pow_three_of_sec18H189 h)
    rw [← map_pow, this, map_one]
  have hcS : ∀ t ∈ sAlpha189 M H c, alpha189 M H c (cSK189 M H c) * t *
      (alpha189 M H c (cSK189 M H c))⁻¹ ∈ sAlpha189 M H c := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨cSK189 M H c * s * (cSK189 M H c)⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_s189 h hcA) s).mp hs
  have hSC := le_centralizer_of_le_normalizer_zpowers189 (isPGroup_sAlpha189 M H c) hc3 hcS hSN
  set Y := kAlpha189 M H c ⊓
    Subgroup.centralizer ({alpha189 M H c (cSK189 M H c)} : Set (SKAlpha189 M H c)) with hYdef
  set T := CFSG.Open.pCoreOf 2 Y with hTdef
  have hSY : sAlpha189 M H c ≤ Subgroup.normalizer (Y : Set (SKAlpha189 M H c)) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs y hy
    rw [hYdef, Subgroup.mem_inf] at hy ⊢
    exact ⟨(kAlpha189_normal M H c).conj_mem y hy.1 s,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSC hs) hy.2) (Subgroup.inv_mem _ (hSC hs))⟩
  have hST : sAlpha189 M H c ≤ Subgroup.normalizer (T : Set (SKAlpha189 M H c)) :=
    hSY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAinv : ∀ a ∈ A, ∀ y : ↥(sk189 M H c), alpha189 M H c y ∈ sAlpha189 M H c ⊔ T →
      ∀ hy : a * y * a⁻¹ ∈ sk189 M H c,
        alpha189 M H c ⟨a * y * a⁻¹, hy⟩ ∈ sAlpha189 M H c ⊔ T := by
    intro a ha y hyT hy
    have haX := le_normalizer_sk189 h ha
    obtain ⟨φ, hφ⟩ := exists_conj_sKAlpha189 haX
    have hac : a * c = c * a := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
    have hcφ : φ (alpha189 M H c (cSK189 M H c)) = alpha189 M H c (cSK189 M H c) := by
      rw [hφ (cSK189 M H c) ((Subgroup.mem_normalizer_iff.mp haX c).mp (mem_sk189_self M H c))]
      exact congrArg (alpha189 M H c)
        (Subtype.ext (show a * c * a⁻¹ = c by rw [hac, mul_inv_cancel_right]))
    have hYφ : Y.map φ.toMonoidHom ≤ Y := by
      rw [hYdef]
      refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf
        (map_imAlpha189_le_of_conj haX hφ
          (Sec20.le_normalizer_normalClosureIn M c (sec18Std_le h.toSec18Std ha))) ?_)
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      change φ z * _ = _ * φ z
      rw [← hcφ, ← map_mul, ← map_mul, hz]
    have hSTφ : (sAlpha189 M H c ⊔ T).map φ.toMonoidHom ≤ sAlpha189 M H c ⊔ T := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (map_imAlpha189_le_of_conj haX hφ (le_normalizer_s189 h ha))
        (map_pCoreOf_le_of_map_le189 2 φ hYφ)
    rw [← hφ y hy]
    exact hSTφ ⟨_, hyT, rfl⟩
  set U : Subgroup G :=
    ((sAlpha189 M H c ⊔ T).comap (alpha189 M H c)).map (sk189 M H c).subtype with hUdef
  have hSU : s189 M H ≤ U := by
    intro s hs
    have hsX : s ∈ sk189 M H c := (le_sup_left : s189 M H ≤ sk189 M H c) hs
    exact ⟨⟨s, hsX⟩,
      (le_sup_left : sAlpha189 M H c ≤ sAlpha189 M H c ⊔ T) ⟨⟨s, hsX⟩, hs, rfl⟩, rfl⟩
  have hθ2 : IsPGroup 2 (alpha189 M H c).ker := by
    rw [alpha189, QuotientGroup.ker_mk']
    exact ((isPGroup_s189 M H).to_le hθS).of_equiv
      (Subgroup.equivMapOfInjective (aschbacherSolvableCore 3 ↥(sk189 M H c)) _
        (sk189 M H c).subtype_injective).symm
  have hU2 : IsPGroup 2 U :=
    (((isPGroup_sAlpha189 M H c).to_sup_of_normal_right'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hST).comap_of_ker_isPGroup _ hθ2).map _
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : a * (y : G) * a⁻¹ ∈ sk189 M H c :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_sk189 h ha) y).mp y.2
    exact ⟨⟨_, hy'⟩, hAinv a ha y hy hy', rfl⟩
  have hUS : U = s189 M H :=
    (mem_maxInvariantPiSubgroups_iff.mp hmax).2 U
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hAU⟩) hSU
  intro t ht
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥(sk189 M H c)) t
  have hyU : (y : G) ∈ U := ⟨y, (le_sup_right : T ≤ sAlpha189 M H c ⊔ T) ht, rfl⟩
  rw [hUS] at hyU
  exact ⟨y, hyU, rfl⟩

end CFSG.RankThree.PartTwo.Sec18
