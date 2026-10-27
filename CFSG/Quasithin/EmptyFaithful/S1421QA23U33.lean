module

public import CFSG.Quasithin.EmptyFaithful.S1421QA23Small
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Bend
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

namespace QA23

theorem exists_simple_bender_quotient {B : Type} [Group B] {n : ℕ} (hn : 2 ≤ n)
    (h : IsBenderQuot n B) :
    ∃ (B0 : Type) (_ : Group B0) (f : B →* B0) (i e : ℕ),
      Function.Surjective f ∧ BenderType B0 n i e := by
  rcases h with hL | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · obtain ⟨e⟩ := hL
    exact ⟨B, inferInstance, MonoidHom.id B, 1, 1, Function.surjective_id,
      BenderType.linear n hn e⟩
  · have ha : 1 ≤ a := by omega
    exact ⟨B, inferInstance, MonoidHom.id B, 2, 1, Function.surjective_id,
      BenderType.suzuki a ha
        (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))⟩
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    refine ⟨StatedProj (StatedSU 3 (2 ^ n) F), inferInstance,
      (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))).comp
        e.toMonoidHom, 3, e', ?_, hB⟩
    exact (QuotientGroup.mk'_surjective _).comp e.surjective
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact ⟨StatedProj (StatedSU 3 (2 ^ n) F), inferInstance, e.toMonoidHom, 3, e',
      e.surjective, hB⟩

theorem benderOrder_dvd_card_map_center {X : Type} [Group X]
    [Finite X] {K : Subgroup X} (hB : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)) :
    ∃ n i : ℕ, 2 ≤ n ∧ (i = 1 ∨ i = 2 ∨ i = 3) ∧ (i = 2 → n % 2 = 1) ∧
      QA19.benderOrder n i ∣ Nat.card (K.map (QuotientGroup.mk' (Subgroup.center X))) := by
  obtain ⟨n, hn, hBq⟩ := hB
  obtain ⟨B0, _, f, i, e, hf, hBT⟩ := exists_simple_bender_quotient hn hBq
  have : Finite B0 := Finite.of_surjective f hf
  have hc : Subgroup.center B0 = ⊥ := by
    have hs := hBT.isSimple
    have hnc := hBT.isSimpleBenderGroup.not_commutative
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B0) with hbot | htop
    · exact hbot
    · exfalso
      apply hnc
      intro x y
      have : x ∈ Subgroup.center B0 := by rw [htop]; trivial
      exact (Subgroup.mem_center_iff.mp this y).symm
  let q : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)
  let φ : ↥K →* ↥(K.map (QuotientGroup.mk' (Subgroup.center X))) :=
    (QuotientGroup.mk' (Subgroup.center X)).subgroupMap K
  have hφ : Function.Surjective φ := MonoidHom.subgroupMap_surjective _ _
  have hker : φ.ker ≤ (f.comp q).ker := by
    intro x hx
    have hx1 : QuotientGroup.mk' (Subgroup.center X) (x : X) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxz : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hx1
    have hqz : q x ∈ Subgroup.center (OTwoQuot K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H y =>
        show (QuotientGroup.mk y : OTwoQuot K) * QuotientGroup.mk x =
          QuotientGroup.mk x * QuotientGroup.mk y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_center_iff.mp hxz (y : X))
    have hfz : f (q x) ∈ Subgroup.center B0 := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨b', rfl⟩ := hf b
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hqz b']
    rw [hc, Subgroup.mem_bot] at hfz
    exact hfz
  let ψ : ↥K ⧸ φ.ker →* B0 := QuotientGroup.lift φ.ker (f.comp q) hker
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨k, hk⟩ := (hf.comp (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥K))) b
    exact ⟨QuotientGroup.mk k, hk⟩
  have hdvd : Nat.card B0 ∣ Nat.card (↥K ⧸ φ.ker) := Subgroup.card_dvd_of_surjective hψ
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    QA19.benderOrder_of_benderType hBT] at hdvd
  refine ⟨n, i, hn, ?_, ?_, hdvd⟩
  · rcases hBT.cases' with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · intro hi2
    rcases hBT.cases' with ⟨hi, -, -⟩ | ⟨hi, -, a, -, hna⟩ | ⟨hi, -, -⟩
    · omega
    · omega
    · omega

theorem bender_dvd_6048 {n i : ℕ} (hn : 2 ≤ n) (hi : i = 1 ∨ i = 2 ∨ i = 3)
    (hodd : i = 2 → n % 2 = 1) (h : QA19.benderOrder n i ∣ 6048) :
    QA19.benderOrder n i = 504 := by
  have h1 := QA19.two_pow_le_benderOrder (by omega : 1 ≤ n) i
  have h2 := Nat.le_of_dvd (by norm_num) h
  have hn13 : n < 13 := by
    by_contra hge
    push Not at hge
    have : 2 ^ 13 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    omega
  interval_cases n <;> rcases hi with rfl | rfl | rfl <;> simp_all [QA19.benderOrder]

theorem card_of_isPSU_three_three {X : Type} [Group X] (h : IsPSU 3 3 1 X) :
    Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem false_of_card_6048 {p m : ℕ} (h504 : 504 ∣ p) (h32 : 32 ∣ p) (hpm : 6048 = p * m)
    (hm : m ≠ 1) (hf : 6048 ∣ m.factorial) : False := by
  have h2016 : 2016 ∣ p := by omega
  obtain ⟨c, rfl⟩ := h2016
  have hc : c = 1 := by
    have : 2016 * c * m = 2016 * 3 := by omega
    have hcm : c * m = 3 := by nlinarith
    rcases (Nat.dvd_prime Nat.prime_three).mp ⟨m, hcm.symm⟩ with h | h
    · exact h
    · subst h
      omega
  subst hc
  have hm3 : m = 3 := by omega
  subst hm3
  norm_num [Nat.factorial] at hf

theorem false_of_isPSU_three_three {X : Type} [Group X] [Finite X]
    (hXq : CFSG.IsQuasisimple X) (hl : IsPSU 3 3 1 (X ⧸ Subgroup.center X)) {U K : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hKU : K ⊔ U ≠ ⊤)
    (hB : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)) : False := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hXq.2.1
  obtain ⟨P, hKP, hUP, hP⟩ := exists_overgroup_bar hXq hKU
  obtain ⟨h60, hcard, hm, hfac, hUd⟩ :=
    overgroup_numbers hP hKP hUP (sixty_le_card_map_center hKp hKne)
  have hN : Nat.card (X ⧸ Subgroup.center X) = 6048 := card_of_isPSU_three_three hl
  have hUc : Nat.card (U.map (QuotientGroup.mk' (Subgroup.center X))) = 32 := by
    have := card_eq_of_isSylowTwoOf_top
      (isSylowTwoOf_top_map_of_surjective hU _ (QuotientGroup.mk'_surjective _))
      (a := 5) (c := 189) (by norm_num) (by rw [hN]; norm_num)
    simpa using this
  obtain ⟨n, i, hn, hi, hodd, hdvd⟩ := benderOrder_dvd_card_map_center hB
  have h1 : QA19.benderOrder n i ∣ Nat.card P := hdvd.trans (Subgroup.card_dvd_of_le hKP)
  rw [hN] at hcard hfac
  have h2 : Nat.card P ∣ 6048 := ⟨P.index, hcard⟩
  have h504 := bender_dvd_6048 hn hi hodd (h1.trans h2)
  rw [h504] at h1
  rw [hUc] at hUd
  exact false_of_card_6048 h1 hUd hcard hm hfac

end QA23

end CFSG.Quasithin
