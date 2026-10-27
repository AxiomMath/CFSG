module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.Monster.B.TwoA.Fischer.M22Aut
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2117Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Perfect

variable {X : Type*} [Group X]

theorem eq_one_of_mulAutQuotientHom_center_eq_one (hX : commutator X = ⊤) {σ : MulAut X}
    (hσ : mulAutQuotientHom (Subgroup.center X) σ = 1) : σ = 1 := by
  have hc : ∀ x : X, σ x * x⁻¹ ∈ Subgroup.center X := fun x => by
    have h1 := congrArg (fun τ : MulAut (X ⧸ Subgroup.center X) =>
      τ (x : X ⧸ Subgroup.center X)) hσ
    simp only [mulAutQuotientHom_mk, MulAut.one_apply] at h1
    have h2 := Subgroup.inv_mem _ (QuotientGroup.eq.mp h1)
    rw [mul_inv_rev, inv_inv] at h2
    have h3 : σ x * x⁻¹ = x⁻¹ * σ x := by
      have h4 := Subgroup.mem_center_iff.mp h2 x
      calc σ x * x⁻¹ = (x * (x⁻¹ * σ x)) * x⁻¹ := by group
        _ = ((x⁻¹ * σ x) * x) * x⁻¹ := by rw [h4]
        _ = x⁻¹ * σ x := by group
    rw [h3]
    exact h2
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨σ x * x⁻¹, hc x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change σ (x * y) * (x * y)⁻¹ = σ x * x⁻¹ * (σ y * y⁻¹)
        have h := Subgroup.mem_center_iff.mp (hc y) x⁻¹
        calc σ (x * y) * (x * y)⁻¹ = σ x * ((σ y * y⁻¹) * x⁻¹) := by
              rw [map_mul, mul_inv_rev]; group
          _ = σ x * (x⁻¹ * (σ y * y⁻¹)) := by rw [h]
          _ = σ x * x⁻¹ * (σ y * y⁻¹) := by group }
  ext x
  have hx : x ∈ f.ker := Abelianization.commutator_subset_ker f (hX ▸ Subgroup.mem_top x)
  have h1 : σ x * x⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

theorem mulAutQuotientHom_center_injective (hX : commutator X = ⊤) :
    Function.Injective (mulAutQuotientHom (Subgroup.center X)) := by
  rw [injective_iff_map_eq_one]
  exact fun σ hσ => eq_one_of_mulAutQuotientHom_center_eq_one hX hσ

end Perfect

section ThreeGroups

theorem card_center_eq_three_of_card_eq {P : Type*} [Group P] (h27 : Nat.card P = 27)
    (hnc : ¬ IsMulCommutative P) : Nat.card (Subgroup.center P) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [h27]; norm_num)
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)
  have hnt : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [h27]; norm_num)
  have hZnt := hP3.center_nontrivial
  have hdvd : Nat.card (Subgroup.center P) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    exact not_subsingleton _ (Nat.card_eq_one_iff_unique.mp hk).1
  · simpa using hk
  · exfalso
    apply hnc
    have hQ : Nat.card (P ⧸ Subgroup.center P) = 3 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
      rw [h27, hk] at h1
      omega
    have : IsCyclic (P ⧸ Subgroup.center P) := isCyclic_of_prime_card hQ
    exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center P)) (by rw [QuotientGroup.ker_mk'])
  · exfalso
    apply hnc
    have htop : Subgroup.center P = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk, h27]; norm_num)
    exact ⟨⟨fun a b => Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩

theorem nine_le_card_of_not_mem_zpowers {X : Type*} [Group X] {S : Subgroup X} [Finite S]
    (hS : IsPGroup 3 S) {τ₁ τ₂ : X} (h₁ : τ₁ ∈ S) (h₂ : τ₂ ∈ S) (h1 : τ₁ ≠ 1)
    (h12 : τ₂ ∉ Subgroup.zpowers τ₁) : 9 ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKS : Subgroup.zpowers τ₁ ≤ S := Subgroup.zpowers_le.mpr h₁
  set K := (Subgroup.zpowers τ₁).subgroupOf S with hK
  have hKne : K ≠ ⊤ := by
    intro htop
    have : (⟨τ₂, h₂⟩ : S) ∈ K := htop ▸ Subgroup.mem_top _
    exact h12 (Subgroup.mem_subgroupOf.mp this)
  have hcardK : Nat.card K = orderOf τ₁ := by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS
  have hord3 : 3 ≤ orderOf τ₁ := by
    have hdvd : orderOf τ₁ ∣ 3 ^ a := by
      rw [← ha, ← Subgroup.orderOf_mk τ₁ h₁]
      exact orderOf_dvd_natCard _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hi)) h1
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  have hidx : 3 ≤ K.index := by
    have hdvd : K.index ∣ 3 ^ a := ha ▸ K.index_dvd_card
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (Subgroup.index_eq_one.mp (by simpa using hi)) hKne
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  calc 9 = 3 * 3 := by norm_num
    _ ≤ Nat.card K * K.index := Nat.mul_le_mul (hcardK ▸ hord3) hidx
    _ = Nat.card S := K.card_mul_index

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_closure_pair_le_nine {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) : Nat.card (Subgroup.closure ({c, d} : Set G)) ≤ 9 := by
  have hcK : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdK : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 → Subgroup.closure ({c, d} : Set G) := fun p =>
    ⟨c ^ p.1.val * d ^ p.2.val, Subgroup.mul_mem _ (Subgroup.pow_mem _ hcK _)
      (Subgroup.pow_mem _ hdK _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hz
    have hc3' : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
    have hd3' : d ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
    have hm0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
    have hn0 : 0 ≤ n % 3 := Int.emod_nonneg _ (by norm_num)
    refine ⟨(⟨(m % 3).toNat, by omega⟩, ⟨(n % 3).toNat, by omega⟩), Subtype.ext ?_⟩
    simp only [f]
    rw [zpow_eq_zpow_emod m hc3', zpow_eq_zpow_emod n hd3', ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0]
  calc Nat.card (Subgroup.closure ({c, d} : Set G)) ≤ Nat.card (Fin 3 × Fin 3) :=
        Nat.card_le_card_of_surjective f hf
    _ = 9 := by simp

theorem closure_triple_eq_of_card {A : Subgroup G} (hA3 : IsPGroup 3 A) (h27 : Nat.card A = 27)
    {c x y : G} (hcA : c ∈ A) (hxA : x ∈ A) (hyA : y ∈ A) (hc3 : orderOf c = 3)
    (hxc : x ∉ Subgroup.zpowers c) (hy : y ∉ Subgroup.closure ({c, x} : Set G)) :
    Subgroup.closure ({c, x, y} : Set G) = A := by
  have hB : Subgroup.closure ({c, x} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hcA, hxA]
  have hT : Subgroup.closure ({c, x, y} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    exacts [hcA, hxA, hyA]
  have hcB : Subgroup.zpowers c ≤ Subgroup.closure ({c, x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hBT : Subgroup.closure ({c, x} : Set G) ≤ Subgroup.closure ({c, x, y} : Set G) :=
    Subgroup.closure_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have h1 := Item211Proof.three_mul_card_le_of_lt (hA3.to_le hB) hcB (fun h => hxc (by
    rw [h]
    exact Subgroup.subset_closure (by simp)))
  have h2 := Item211Proof.three_mul_card_le_of_lt (hA3.to_le hT) hBT (fun h => hy (by
    rw [h]
    exact Subgroup.subset_closure (by simp)))
  rw [Nat.card_zpowers, hc3] at h1
  exact Subgroup.eq_of_le_of_card_ge hT (by omega)

end ThreeGroups

section M22

theorem card_le_nine_of_isPGroup
    {X : Type*} [Group X] (hX : commutator X = ⊤)
    (hT : Sec4.IsTripleCover X Blueprint.NativeSporadic.M22) {Y : Subgroup (MulAut X)}
    (hY : IsPGroup 3 Y) : Nat.card Y ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, ⟨e⟩⟩ := hT
  set ι : MulAut X →* MulAut Blueprint.NativeSporadic.M22 :=
    (MulAut.congr e).toMonoidHom.comp (mulAutQuotientHom (Subgroup.center X)) with hι
  have hιinj : Function.Injective ι :=
    (MulAut.congr e).injective.comp (mulAutQuotientHom_center_injective hX)
  have hcard : Nat.card (Y.map ι) = Nat.card Y := Subgroup.card_map_of_injective hιinj
  have hdvd : Nat.card Y ∣ 887040 := by
    rw [← hcard, ← (CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order).1]
    exact Subgroup.card_subgroup_dvd_card _
  have hfin : Finite Y := Nat.finite_of_card_ne_zero fun h => by
    rw [h] at hdvd
    norm_num at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk] at hdvd ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h27 : 3 ^ 3 ∣ 887040 := (pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd
    norm_num at h27
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem factorization_card_eq_three {L : Type*} [Group L]
    [Finite L]
    (hT : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.M22) :
    (Nat.card L).factorization 3 = 3 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 L)
  have h2 := KFacts.card_of_isTripleCover hT
  rw [CFSG.Sporadic.Mathieu.card_M22] at h2
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hθ0 : Nat.card (aschbacherSolvableCore 3 L) ≠ 0 := Nat.card_pos.ne'
  rw [h1, h2, Nat.factorization_mul (by norm_num) hθ0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h3, add_zero,
    show (443520 : ℕ) = 9 * 49280 by norm_num]
  exact KFacts.factorization_three_mul_nine_mul (by norm_num)

end M22

section Config

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_thetaQuotCentralizer {A L : Subgroup G}
    (hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {x a : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hxA : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) ∈ Sec4.autThetaQuot A L)
    (ha : a ∈ A) : x * a * x⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
  obtain ⟨h, hhN, hhA, hh⟩ := Sec4.mem_autThetaQuot_iff.mp hxA
  set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set x' : Subgroup.normalizer (L : Set G) := ⟨x, hx⟩ with hx'
  set a' : Subgroup.normalizer (L : Set G) := ⟨a, hAL ha⟩ with ha'
  have hxh : φ x' = φ ⟨h, hhN⟩ := hh.symm
  have hcomm : φ x' * φ a' = φ a' * φ x' := by
    rw [hxh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommA h hhA a ha)
  refine ⟨x' * a' * x'⁻¹ * a'⁻¹, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  change φ (x' * a' * x'⁻¹ * a'⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
  group


theorem normalizer_le_of_isTripleCover (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hT : Sec4.IsTripleCover (lBar L) Blueprint.NativeSporadic.M22) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcE : c ∈ E := hpairs.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAF : A ∈ partTwoF G := hpair.mem_S.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hexpA a a.2)⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c hcA) hc1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hG4 : TheoremFourHyp G := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
    exact SetLike.coe_injective hsc
  have hLperf : commutator (lBar L) = ⊤ := by
    have h1 := (Sec12.isQuasisimple_thetaQuot_of_mem hLc).1
    rwa [Group.isPerfect_def] at h1
  have hmax : ∀ z : G, z ^ 3 = 1 → (∀ a ∈ A, a * z = z * a) → z ∈ A := fun z hz3 hz => by
    have hab := Item211Proof.isElemAbelian_sup_zpowers hAe hz3 hz
    have heq := hAF.2.1 _ hab le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hAut3 : ∀ X : Subgroup G, IsPGroup 3 X → IsPGroup 3 (Sec4.autThetaQuot X L) := by
    intro X hX
    have h1 : IsPGroup 3 ((X ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
        (Subgroup.normalizer (L : Set G))) := (hX.to_le inf_le_left).comap_subtype
    exact (h1.map _).map _
  have hle9 : ∀ X : Subgroup G, IsPGroup 3 X → Nat.card (Sec4.autThetaQuot X L) ≤ 9 :=
    fun X hX => card_le_nine_of_isPGroup hLperf hT (hAut3 X hX)
  have hkA := Sec13.card_inf_mul_card_autThetaQuot hAL
  rw [hCA, Nat.card_zpowers, hc3] at hkA
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have h27le : 27 ≤ Nat.card A := hE27 ▸ Subgroup.card_le_of_le hpair.mem_E.2
  have hA9 := hle9 A hA3
  have hA27 : Nat.card A = 27 := by omega
  have hAut9 : Nat.card (Sec4.autThetaQuot A L) = 9 := by omega
  have hAutEq : ∀ X : Subgroup G, IsPGroup 3 X → A ≤ X →
      Sec4.autThetaQuot X L = Sec4.autThetaQuot A L := fun X hX hAX =>
    (Subgroup.eq_of_le_of_card_ge (Sec13.autThetaQuot_mono hAX L)
      (by rw [hAut9]; exact hle9 X hX)).symm
  set K : Subgroup G := L ⊔ A with hK
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hAL
  obtain ⟨Q₀, hQ₀⟩ := (hA3.comap_subtype (K := K)).exists_le_sylow
  set Q : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hQdef
  have hQ : IsSylowOf 3 Q K := ⟨Q₀, rfl⟩
  have hAQ : A ≤ Q := fun a ha =>
    ⟨⟨a, le_sup_right (a := L) ha⟩, hQ₀ (Subgroup.mem_comap.mpr ha), rfl⟩
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  set S : Subgroup G := Q ⊓ L with hSdef
  have hS : IsSylowOf 3 S L := hQ.inf_of_le_normalizer le_sup_left hKN
  have hS27 : Nat.card S = 27 := by
    rw [hS.card_eq, factorization_card_eq_three hT]
    norm_num
  have hS3 : IsPGroup 3 S := hS.isPGroup
  have hSL : S ≤ L := inf_le_right
  have hSQ : S ≤ Q := inf_le_left
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := hSL.trans Subgroup.le_normalizer
  have hAS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs =>
    ⟨Q.mul_mem (Q.mul_mem (hAQ ha) hs.1) (Q.inv_mem (hAQ ha)),
      (Subgroup.mem_normalizer_iff.mp (hAL ha) s).mp hs.2⟩
  have hAutQ := hAutEq Q hQ3 hAQ
  have hAutSle : Sec4.autThetaQuot S L ≤ Sec4.autThetaQuot A L :=
    hAutQ ▸ Sec13.autThetaQuot_mono hSQ L
  have hkS := Sec13.card_inf_mul_card_autThetaQuot hSN
  rw [hS27] at hkS
  have hSC3le : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≤ 3 := by
    have h1 := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer
      (hS3.to_le inf_le_left) (inf_le_right : S ⊓ Sec4.thetaQuotCentralizer L ≤ _)
    rwa [inf_eq_left.mpr (inf_le_left.trans hSL), hT.1] at h1
  have hAutS9le : Nat.card (Sec4.autThetaQuot S L) ≤ 9 :=
    (Subgroup.card_le_of_le hAutSle).trans hAut9.le
  have hSC3 : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    have hpos : 0 < Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := Nat.card_pos
    interval_cases h : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) <;> omega
  have hAutS9 : Nat.card (Sec4.autThetaQuot S L) = 9 := by
    rw [hSC3] at hkS
    omega
  have hAutS : Sec4.autThetaQuot S L = Sec4.autThetaQuot A L :=
    Subgroup.eq_of_le_of_card_ge hAutSle (by rw [hAut9, hAutS9])
  have hSCeq : S ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    obtain ⟨z, hz⟩ : ∃ z : (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G), orderOf z = 3 :=
      exists_prime_orderOf_dvd_card' 3 (by rw [hSC3])
    have hz3 : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have hZeq : Subgroup.zpowers (z : G) = S ⊓ Sec4.thetaQuotCentralizer L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2)
        (by rw [hSC3, Nat.card_zpowers, hz3])
    have hzA : (z : G) ∈ A := hmax z (by rw [← hz3]; exact pow_orderOf_eq_one _) fun a ha => by
      have hconj : a * z * a⁻¹ ∈ Subgroup.zpowers (z : G) := by
        rw [hZeq]
        exact ⟨hAS a ha z z.2.1, Sec12.conj_mem_thetaQuotCentralizer (hAL ha) z.2.2⟩
      exact Sec12.commute_of_conj_mem_zpowers hz3 hconj (k := 1)
        (by rw [pow_one]; exact hexpA a ha)
    have hzc : Subgroup.zpowers (z : G) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hc3])
      rw [Subgroup.zpowers_le, ← hCA]
      exact ⟨hzA, z.2.2⟩
    rw [← hZeq, hzc]
  have hcSC : c ∈ S ⊓ Sec4.thetaQuotCentralizer L := by
    rw [hSCeq]
    exact Subgroup.mem_zpowers c
  have hcS : c ∈ S := hcSC.1
  have hcL : c ∈ L := hcS.2
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := hcSC.2
  have hφS : ∀ s (hs : s ∈ S), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨s, hSN hs⟩) ∈
      Sec4.autThetaQuot A L := fun s hs => by
    rw [← hAutS]
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨s, hSN hs, hs, rfl⟩
  have hcommS : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := fun s hs a ha => by
    rw [← hSCeq]
    refine ⟨?_, comm_mem_thetaQuotCentralizer hcommA hAL (hSN hs) (hφS s hs) ha⟩
    have h1 : a * s⁻¹ * a⁻¹ ∈ S := hAS a ha _ (S.inv_mem hs)
    have h2 : s * a * s⁻¹ * a⁻¹ = s * (a * s⁻¹ * a⁻¹) := by group
    rw [h2]
    exact S.mul_mem hs h1
  have hSA : S ≤ Subgroup.normalizer (A : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun a ha => by
      have h1 : s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
      rw [h1]
      exact A.mul_mem ((Subgroup.zpowers_le.mpr hcA) (hcommS s hs a ha)) ha
  have hSnc : ¬ IsMulCommutative S := by
    intro hcomm
    obtain ⟨S₀, hS₀⟩ := hS.exists_sylow_eq_subgroupOf
    have hLperf' : commutator L = ⊤ := by
      have h1 := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
      rwa [Group.isPerfect_def] at h1
    have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2))
    have hc3' : orderOf (⟨c, hcL⟩ : L) = 3 := by rw [Subgroup.orderOf_mk]; exact hc3
    apply KFacts.not_isMulCommutative_sylow_of_perfect hLperf' hcZ hc3' S₀
    rw [hS₀]
    refine ⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩
    have hx : ((x : L) : G) ∈ S := Subgroup.mem_subgroupOf.mp x.2
    have hy : ((y : L) : G) ∈ S := Subgroup.mem_subgroupOf.mp y.2
    have h := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simpa using h
  have hZS : Nat.card (Subgroup.center S) = 3 := card_center_eq_three_of_card_eq hS27 hSnc
  have hcZS : (⟨c, hcS⟩ : S) ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun s =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC (hSL s.2)))
  have hZSeq : Subgroup.zpowers (⟨c, hcS⟩ : S) = Subgroup.center S := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZS) ?_
    rw [hZS, Nat.card_zpowers, Subgroup.orderOf_mk, hc3]
  have hnondeg : ∀ x ∈ A, (∀ s ∈ S, s * x = x * s) → x ∈ Subgroup.zpowers c := by
    intro x hx hxS
    have hxφ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hAL hx⟩) ∈
        Sec4.autThetaQuot S L := by
      rw [hAutS]
      exact Sec4.mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩
    obtain ⟨s₀, hs₀N, hs₀S, hs₀⟩ := Sec4.mem_autThetaQuot_iff.mp hxφ
    set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
    have hk : s₀⁻¹ * x ∈ Sec4.thetaQuotCentralizer L := by
      refine ⟨(⟨s₀, hs₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hAL hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change φ ((⟨s₀, hs₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hAL hx⟩) = 1
      rw [map_mul, map_inv]
      rw [show φ ⟨s₀, hs₀N⟩ = φ ⟨x, hAL hx⟩ from hs₀, inv_mul_cancel]
    have hkQ : s₀⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hSQ hs₀S)) (hAQ hx)
    have hkS : ∀ s ∈ S, Commute s (s₀⁻¹ * x) := by
      intro s hs
      have h1 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈
          inSubgroup (aschbacherSolvableCore 3) L :=
        (Sec6.mem_thetaQuotCentralizer_iff.mp hk).2 s (hSL hs)
      have h2 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈ Q :=
        Q.mul_mem (Q.inv_mem (hSQ hs)) (Q.mul_mem (Q.mul_mem hkQ (hSQ hs)) (Q.inv_mem hkQ))
      have h3 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈ (⊥ : Subgroup G) := by
        rw [← Sec12.inf_inSubgroup_theta_eq_bot hQ3 (L := L)]
        exact ⟨h2, h1⟩
      rw [Subgroup.mem_bot] at h3
      have h4 : (s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹ = s := (inv_mul_eq_one.mp h3).symm
      change s * (s₀⁻¹ * x) = (s₀⁻¹ * x) * s
      calc s * (s₀⁻¹ * x) = ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) * (s₀⁻¹ * x) := by rw [h4]
        _ = (s₀⁻¹ * x) * s := by group
    have hs₀Z : (⟨s₀, hs₀S⟩ : S) ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun s => by
      apply Subtype.ext
      change (s : G) * s₀ = s₀ * s
      have hc1' : Commute (s : G) x := hxS s s.2
      have hc2' : Commute (s : G) (s₀⁻¹ * x) := hkS s s.2
      have hc3' : Commute (s : G) (x * (s₀⁻¹ * x)⁻¹) := hc1'.mul_right hc2'.inv_right
      rw [show x * (s₀⁻¹ * x)⁻¹ = s₀ by group] at hc3'
      exact hc3'.eq
    rw [← hZSeq] at hs₀Z
    have hs₀c : s₀ ∈ Subgroup.zpowers c := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs₀Z
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hs₀C : s₀ ∈ Sec4.thetaQuotCentralizer L := (Subgroup.zpowers_le.mpr hcC) hs₀c
    have hxC : x ∈ Sec4.thetaQuotCentralizer L := by
      have h1 := (Sec4.thetaQuotCentralizer L).mul_mem hs₀C hk
      rwa [mul_inv_cancel_left] at h1
    rw [← hCA]
    exact ⟨hx, hxC⟩
  set WH := Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)
    with hWH
  have hAWH : A ≤ WH := fun a ha =>
    ⟨Subgroup.le_normalizer ha, Sec12.mem_normalizer_zpowers_of_commute (hcommA a ha c hcA)⟩
  have hSWH : S ≤ WH := fun s hs =>
    ⟨hSA hs, Sec12.mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC (hSL hs)))⟩
  have hAS3 : IsPGroup 3 (A ⊔ S : Subgroup G) := hQ3.to_le (sup_le hAQ hSQ)
  obtain ⟨P₀, hP₀⟩ := (hAS3.comap_subtype (K := WH)).exists_le_sylow
  set P : Subgroup G := (P₀ : Subgroup WH).map WH.subtype with hPdef
  have hP : IsSylowOf 3 P WH := ⟨P₀, rfl⟩
  have hASP : A ⊔ S ≤ P := fun g hg =>
    ⟨⟨g, sup_le hAWH hSWH hg⟩, hP₀ (Subgroup.mem_comap.mpr hg), rfl⟩
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPWH : P ≤ WH := hP.le
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hc3 hLc hP3 (hPWH.trans inf_le_right)
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec12.le_centralizer_of_isPGroup hc3 hP3 (hPWH.trans inf_le_right)
  have hAutP := hAutEq P hP3 (le_sup_left.trans hASP)
  have hPT : Sec4.autIn P A ≤ Sec12.transvectionGroup A ⟨c, hcA⟩ := by
    intro σ hσ
    obtain ⟨g, hgN, hgP, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp (hPC hgP)
    refine ⟨Subtype.ext ?_, fun x => ?_⟩
    · rw [Sec4.normalizerMonoidHom_apply_coe]
      change g * c * g⁻¹ = c
      rw [hgc, mul_inv_cancel_right]
    · rw [Sec12.mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
        Subgroup.coe_inv]
      rw [← hCA]
      refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN x).mp x.2) (A.inv_mem x.2), ?_⟩
      refine comm_mem_thetaQuotCentralizer hcommA hAL (hPN hgP) ?_ x.2
      rw [← hAutP]
      exact Sec4.mem_autThetaQuot_iff.mpr ⟨g, hPN hgP, hgP, rfl⟩
  obtain ⟨x₁, hx₁A, hx₁c⟩ : ∃ x ∈ A, x ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers c from hcon)
    rw [hA27, Nat.card_zpowers, hc3] at h1
    omega
  obtain ⟨s₁, hs₁S, hs₁x⟩ : ∃ s ∈ S, s * x₁ ≠ x₁ * s := by
    by_contra hcon
    push Not at hcon
    exact hx₁c (hnondeg x₁ hx₁A hcon)
  set τ₁ := A.normalizerMonoidHom ⟨s₁, hSA hs₁S⟩ with hτ₁
  have hτ₁P : τ₁ ∈ Sec4.autIn P A :=
    Sec4.mem_autIn_iff.mpr ⟨s₁, hSA hs₁S, hASP (Subgroup.mem_sup_right hs₁S), rfl⟩
  have hτ₁T := hPT hτ₁P
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h1
    apply hs₁x
    have h2 := congrArg (fun σ : MulAut A => ((σ ⟨x₁, hx₁A⟩ : A) : G)) h1
    simp only [hτ₁, Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply] at h2
    calc s₁ * x₁ = (s₁ * x₁ * s₁⁻¹) * s₁ := by group
      _ = x₁ * s₁ := by rw [h2]
  obtain ⟨x₂, hx₂A, hx₂c, hx₂fix⟩ :
      ∃ x ∈ A, x ∉ Subgroup.zpowers c ∧ s₁ * x * s₁⁻¹ = x := by
    have hcommA' : ∀ y z : A, y * z = z * y := fun y z => hAe.1.is_comm.comm y z
    let f : A →* A :=
      { toFun := fun y => τ₁ y * y⁻¹
        map_one' := by simp
        map_mul' := fun y z => by
          change τ₁ (y * z) * (y * z)⁻¹ = τ₁ y * y⁻¹ * (τ₁ z * z⁻¹)
          calc τ₁ (y * z) * (y * z)⁻¹ = τ₁ y * ((τ₁ z * z⁻¹) * y⁻¹) := by
                rw [map_mul, mul_inv_rev]; group
            _ = τ₁ y * (y⁻¹ * (τ₁ z * z⁻¹)) := by rw [hcommA' (τ₁ z * z⁻¹) y⁻¹]
            _ = τ₁ y * y⁻¹ * (τ₁ z * z⁻¹) := by group }
    have hrange : f.range ≤ Subgroup.zpowers (⟨c, hcA⟩ : A) := by
      rintro _ ⟨y, rfl⟩
      exact hτ₁T.2 y
    have hc3A : orderOf (⟨c, hcA⟩ : A) = 3 := by rw [Subgroup.orderOf_mk]; exact hc3
    have hker : 9 ≤ Nat.card f.ker := by
      have h1 := f.ker.card_mul_index
      rw [Subgroup.index_ker, hA27] at h1
      have h2 : Nat.card f.range ≤ 3 :=
        (Subgroup.card_le_of_le hrange).trans (by rw [Nat.card_zpowers, hc3A])
      have h3 : 0 < Nat.card f.range := Nat.card_pos
      nlinarith
    obtain ⟨y, hyker, hyc⟩ : ∃ y ∈ f.ker, y ∉ Subgroup.zpowers (⟨c, hcA⟩ : A) := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show f.ker ≤ _ from hcon)
      rw [Nat.card_zpowers, hc3A] at h1
      omega
    refine ⟨y, y.2, fun h => hyc (Sec12.mem_zpowers_subtype_iff.mpr h), ?_⟩
    have h1 : τ₁ y * y⁻¹ = 1 := MonoidHom.mem_ker.mp hyker
    have h2 : τ₁ y = y := mul_inv_eq_one.mp h1
    exact congrArg Subtype.val h2
  obtain ⟨s₂, hs₂S, hs₂x⟩ : ∃ s ∈ S, s * x₂ ≠ x₂ * s := by
    by_contra hcon
    push Not at hcon
    exact hx₂c (hnondeg x₂ hx₂A hcon)
  set τ₂ := A.normalizerMonoidHom ⟨s₂, hSA hs₂S⟩ with hτ₂
  have hτ₂P : τ₂ ∈ Sec4.autIn P A :=
    Sec4.mem_autIn_iff.mpr ⟨s₂, hSA hs₂S, hASP (Subgroup.mem_sup_right hs₂S), rfl⟩
  have hτ₁x₂ : τ₁ ⟨x₂, hx₂A⟩ = ⟨x₂, hx₂A⟩ := Subtype.ext hx₂fix
  have hτ₂x₂ : τ₂ ⟨x₂, hx₂A⟩ ≠ ⟨x₂, hx₂A⟩ := by
    intro h1
    apply hs₂x
    have h2 : s₂ * x₂ * s₂⁻¹ = x₂ := congrArg Subtype.val h1
    calc s₂ * x₂ = (s₂ * x₂ * s₂⁻¹) * s₂ := by group
      _ = x₂ * s₂ := by rw [h2]
  have hτ₂τ₁ : τ₂ ∉ Subgroup.zpowers τ₁ := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hτ₂x₂
    rw [← hn]
    have hfix : ∀ m : ℤ, (τ₁ ^ m) ⟨x₂, hx₂A⟩ = ⟨x₂, hx₂A⟩ := by
      intro m
      induction m using Int.induction_on with
      | zero => simp
      | succ m ih => rw [zpow_add_one, MulAut.mul_apply, hτ₁x₂, ih]
      | pred m ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : τ₁⁻¹ ⟨x₂, hx₂A⟩ = ⟨x₂, hx₂A⟩ := by
          conv_lhs => rw [← hτ₁x₂]
          exact MulEquiv.symm_apply_apply _ _
        rw [this, ih]
    exact hfix n
  have hPA3 : IsPGroup 3 (Sec4.autIn P A) := by
    have h1 : IsPGroup 3 ((P ⊓ Subgroup.normalizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G))) := (hP3.to_le inf_le_left).comap_subtype
    exact h1.map _
  have h9le : 9 ≤ Nat.card (Sec4.autIn P A) :=
    nine_le_card_of_not_mem_zpowers hPA3 hτ₁P hτ₂P hτ₁1 hτ₂τ₁
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y ∈ A, y ∉ Subgroup.closure ({c, x₁} : Set G) := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.closure ({c, x₁} : Set G) from hcon)
    have h2 := card_closure_pair_le_nine (hcommA c hcA x₁ hx₁A) (hexpA c hcA) (hexpA x₁ hx₁A)
    omega
  have hgen : Subgroup.closure ({c, x₁, y₀} : Set G) = A :=
    closure_triple_eq_of_card hA3 hA27 hcA hx₁A hy₀A hc3 hx₁c hy₀
  have hTle := Sec12.card_transvectionGroup_le hcA hx₁A hy₀A hgen hc3
  have hPaut : Sec4.autIn P A = Sec12.transvectionGroup A ⟨c, hcA⟩ :=
    Subgroup.eq_of_le_of_card_ge hPT (hTle.trans h9le)
  have hP9 : Nat.card (Sec4.autIn P A) = 9 :=
    le_antisymm ((Subgroup.card_le_of_le hPT).trans hTle) h9le
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ :=
    Sec12.exists_coords_module hAe (show Nat.card A = 3 ^ 3 by rw [hA27]; norm_num)
  exact Sec12.normalizer_le_of_autIn_eq hcA hc1 hP hPaut hP9 hV f

end Config

end CFSG.RankThree.PartTwo.Sec21.Item2117Proof

namespace CFSG.RankThree.PartTwo.Sec21

theorem item2117_of
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h2115 : Item2115) : Item2117 :=
  fun G _ _ A E U c L hpair hT =>
    h2115 G A E U c L hpair (Item2117Proof.normalizer_le_of_isTripleCover h45 h66 hpair hT)

end CFSG.RankThree.PartTwo.Sec21
