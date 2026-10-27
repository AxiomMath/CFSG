module

public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec17.F17Leaf

open CFSG CFSG.RankThree.PartTwo CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_sup {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G))
    (hH : ¬ 3 ∣ Nat.card H) (hK3 : ¬ 3 ∣ Nat.card K) : ¬ 3 ∣ Nat.card (H ⊔ K : Subgroup G) := by
  rw [sup_comm H K]
  have hset : ((K ⊔ H : Subgroup G) : Set G) = (K : Set G) * (H : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K H hK
  haveI : (H.subgroupOf (K ⊔ H)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
  let φ : K →* (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) :=
    (QuotientGroup.mk' (H.subgroupOf (K ⊔ H))).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ H))
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    have hs : (s : G) ∈ ((K ⊔ H : Subgroup G) : Set G) := s.2
    rw [hset] at hs
    obtain ⟨k, hk, h, hh, hkh⟩ := hs
    refine ⟨⟨k, hk⟩, ?_⟩
    have hφapp : φ ⟨k, hk⟩ =
        (QuotientGroup.mk (⟨k, (le_sup_left : K ≤ K ⊔ H) hk⟩ : ↥(K ⊔ H)) :
          ↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) := rfl
    have hkh' : k * h = (s : G) := hkh
    rw [hφapp, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (k : G)⁻¹ * (s : G) ∈ H
    rw [← hkh', inv_mul_cancel_left]
    exact hh
  have hQ : Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) ∣ Nat.card K := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := φ) hφ).toEquiv]
    exact Subgroup.card_quotient_dvd_card φ.ker
  have hN : Nat.card (H.subgroupOf (K ⊔ H)) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : H ≤ K ⊔ H)).toEquiv
  have hsplit : Nat.card ↥(K ⊔ H) =
      Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) * Nat.card H := by
    rw [← hN]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  intro h3
  rw [hsplit] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h1 | h1
  · exact hK3 (h1.trans hQ)
  · exact hH h1

theorem le_pPrimeCoreOf_of_normal {Y X M : Subgroup G}
    (hXY : X ≤ Y) (hXN : Y ≤ Subgroup.normalizer ((X ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G))
    (hM : M ≤ X ⊔ pPrimeCoreOf 3 Y) (hM3 : ¬ 3 ∣ Nat.card M)
    (hMn : X ⊔ pPrimeCoreOf 3 Y ≤ Subgroup.normalizer (M : Set G)) :
    M ≤ pPrimeCoreOf 3 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup G, Z = X ⊔ pPrimeCoreOf 3 Y := ⟨_, rfl⟩
  rw [← hZ] at hXN hM hMn
  have hcopM : Nat.Coprime 3 (Nat.card M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3
  have hMP : M ≤ pPrimeCoreOf 3 Z :=
    CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf hM hMn hcopM
  have hZY : Z ≤ Y := by
    rw [hZ]
    exact sup_le hXY (CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 Y)
  have hPZ : pPrimeCoreOf 3 Z ≤ Z := CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 Z
  have hYP : Y ≤ Subgroup.normalizer (pPrimeCoreOf 3 Z : Set G) :=
    hXN.trans (CFSG.RankThree.PartTwo.Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 Z)
  have hcopP : Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 Z)) :=
    CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 Z
  have hPY : pPrimeCoreOf 3 Z ≤ Y := hPZ.trans hZY
  have hPle : pPrimeCoreOf 3 Z ≤ pPrimeCoreOf 3 Y :=
    CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf hPY hYP hcopP
  exact hMP.trans hPle


theorem h2b_not_three_dvd_card {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {U : Subgroup G}
    (hU : IsPGroup p U) : ¬ 3 ∣ Nat.card U := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  rw [hn]
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm

theorem h2b_le_sup_inf (N U M : Subgroup G) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hUNM : U ≤ N ⊔ M) : U ≤ ((N ⊔ U) ⊓ M) ⊔ N := by
  intro u hu
  have hu' : u ∈ ((N ⊔ M : Subgroup G) : Set G) := hUNM hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N M hMN] at hu'
  obtain ⟨n, hn, m, hm, rfl⟩ := Set.mem_mul.mp hu'
  have hn' : n ∈ N := hn
  have hm' : m ∈ M := hm
  have hm'' : m ∈ (N ⊔ U) ⊓ M := by
    refine Subgroup.mem_inf.mpr ⟨?_, hm'⟩
    have h1 : n⁻¹ ∈ N ⊔ U := Subgroup.mem_sup_left (inv_mem hn')
    have h2 : n * m ∈ N ⊔ U := Subgroup.mem_sup_right hu
    simpa using mul_mem h1 h2
  exact mul_mem (Subgroup.mem_sup_right hn') (Subgroup.mem_sup_left hm'')

theorem h2b_index_eq_pow {p : ℕ} [Fact p.Prime] {N U F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (N : Set G)) (hUN : U ≤ Subgroup.normalizer (N : Set G))
    (hU : IsPGroup p U) (hUF : U ≤ F ⊔ N) (hFU : F ≤ U ⊔ N) :
    ∃ k : ℕ, (N.subgroupOf F).index = p ^ k := by
  haveI : (N.subgroupOf (F ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hFN
  haveI : (N.subgroupOf F).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hFN
  have hcard : (N.subgroupOf F).index =
      Nat.card ((F ⊔ N : Subgroup G) ⧸ N.subgroupOf (F ⊔ N)) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient F N hFN).toEquiv
  have hQ : IsPGroup p ((F ⊔ N : Subgroup G) ⧸ N.subgroupOf (F ⊔ N)) := by
    let ψ : U →* ((F ⊔ N : Subgroup G) ⧸ N.subgroupOf (F ⊔ N)) :=
      (QuotientGroup.mk' (N.subgroupOf (F ⊔ N))).comp (Subgroup.inclusion hUF)
    refine hU.of_surjective ψ ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (F ⊔ N)) q
    have hx : (x : G) ∈ ((U ⊔ N : Subgroup G) : Set G) := sup_le hFU le_sup_right x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U N hUN] at hx
    obtain ⟨u, hu, n, hn, hxun⟩ := Set.mem_mul.mp hx
    refine ⟨⟨u, hu⟩, ?_⟩
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hxun] using hn
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  exact ⟨k, by rw [hcard, hk]⟩

theorem h2b_sup_eq_top {p : ℕ} [Fact p.Prime] {K : Type*} [Group K] {P Q : Subgroup K}
    (hP : ¬ p ∣ P.index) (hQ : ∃ k : ℕ, Q.index = p ^ k) : P ⊔ Q = ⊤ := by
  obtain ⟨k, hk⟩ := hQ
  have h1 : (P ⊔ Q).index ∣ p ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_of_le le_sup_right
  have h2 : (P ⊔ Q).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_left
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp h1
  have hj0 : j = 0 := by
    by_contra hne
    apply hP
    have h3 : p ^ j ∣ P.index := by
      rw [← hj]
      exact h2
    exact (dvd_pow_self p hne).trans h3
  rw [← Subgroup.index_eq_one, hj, hj0, pow_zero]

theorem h2b_le_sup_sylow {p : ℕ} [Fact p.Prime] {N F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (N : Set G)) (P : Sylow p F)
    (hidx : ∃ k : ℕ, (N.subgroupOf F).index = p ^ k) :
    F ≤ N ⊔ (P : Subgroup F).map F.subtype := by
  haveI : (N.subgroupOf F).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hFN
  have hP : ¬ p ∣ (P : Subgroup F).index := Sylow.not_dvd_index P
  have htop : (P : Subgroup F) ⊔ N.subgroupOf F = ⊤ := h2b_sup_eq_top hP hidx
  intro f hf
  have hmem : (⟨f, hf⟩ : F) ∈ (P : Subgroup F) ⊔ N.subgroupOf F := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  have hf' : f = (y : G) * (z : G) := (congrArg Subtype.val hyz).symm
  rw [hf']
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz))

theorem exists_invariant_pSubgroup_le_sup {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {A N T M U : Subgroup G} (hA3 : IsPGroup 3 A)
    (hNT : N ≤ T) (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N)
    (hMT : M ≤ T) (hU : IsPGroup p U) (hUNM : U ≤ N ⊔ M)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    ∃ S : Subgroup G, S ≤ M ∧ IsPGroup p S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      U ≤ N ⊔ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hUT : U ≤ T := hUNM.trans (sup_le hNT hMT)
  have hUN : U ≤ Subgroup.normalizer (N : Set G) := hUT.trans hTN
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := hMT.trans hTN
  have hK3 : ¬ 3 ∣ Nat.card (N ⊔ U : Subgroup G) :=
    not_three_dvd_card_sup hUN hN3 (h2b_not_three_dvd_card hp hp3 hU)
  have hAK : A ≤ Subgroup.normalizer ((N ⊔ U : Subgroup G) : Set G) :=
    (le_inf hAN hAU).trans (Subgroup.inf_normalizer_le_normalizer_sup N U)
  have hAF : A ≤ Subgroup.normalizer (((N ⊔ U) ⊓ M : Subgroup G) : Set G) :=
    (le_inf hAK hAM).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hF3 : ¬ 3 ∣ Nat.card ((N ⊔ U) ⊓ M : Subgroup G) := fun h =>
    hK3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcop : Nat.Coprime 3 (Nat.card ((N ⊔ U) ⊓ M : Subgroup G)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hF3
  obtain ⟨sylow, hsylow⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow
    3 p Nat.prime_three hp A ((N ⊔ U) ⊓ M) hA3 hAF hcop
  have hFM : (N ⊔ U) ⊓ M ≤ M := inf_le_right
  have hFN : (N ⊔ U) ⊓ M ≤ Subgroup.normalizer (N : Set G) := hFM.trans hMN
  have hUF : U ≤ ((N ⊔ U) ⊓ M) ⊔ N := h2b_le_sup_inf N U M hMN hUNM
  have hFU : (N ⊔ U) ⊓ M ≤ U ⊔ N := inf_le_left.trans (le_of_eq (sup_comm N U))
  obtain ⟨k, hk⟩ := h2b_index_eq_pow hFN hUN hU hUF hFU
  have hF_le := h2b_le_sup_sylow hFN sylow ⟨k, hk⟩
  refine ⟨(sylow : Subgroup ((N ⊔ U) ⊓ M : Subgroup G)).map ((N ⊔ U) ⊓ M).subtype, ?_, ?_,
    hsylow, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hFM x.2
  · exact sylow.isPGroup'.map ((N ⊔ U) ⊓ M).subtype
  · exact hUF.trans (sup_le hF_le le_sup_left)


theorem commutator_le_of_le_sup_centralizer {A S K V : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hV : V ≤ Subgroup.centralizer (A : Set G))
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hS : S ≤ K ⊔ V) : ⁅S, A⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro s hs a ha
  have hsKV : s ∈ (K : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K V hVK]
    exact hS hs
  obtain ⟨k, hk, v, hv, rfl⟩ := Set.mem_mul.mp hsKV
  have hva : v * a = a * v :=
    ((Subgroup.mem_centralizer_iff.mp (hV hv)) a ha).symm
  have hconj : v * a * v⁻¹ = a := by
    rw [hva, mul_inv_cancel_right]
  have hkk : ⁅k * v, a⁆ = k * (a * k⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc k * v * a * (k * v)⁻¹ * a⁻¹ = k * (v * a * v⁻¹) * k⁻¹ * a⁻¹ := by group
      _ = k * a * k⁻¹ * a⁻¹ := by rw [hconj]
      _ = k * (a * k⁻¹ * a⁻¹) := by group
  have hnorm : a * k⁻¹ * a⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hAK ha) k⁻¹).mp (K.inv_mem hk)
  rw [hkk]
  exact K.mul_mem hk hnorm

theorem commutator_le_sup_of_le_sup {A N S U : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hUNS : U ≤ N ⊔ S)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) :
    ⁅U, A⁆ ≤ N ⊔ ⁅S, A⁆ := by
  rw [Subgroup.commutator_le]
  intro u hu a ha
  have huNS : u ∈ (N : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N S hSN]
    exact hUNS hu
  obtain ⟨n, hn, s, hs, rfl⟩ := Set.mem_mul.mp huNS
  have hcomm : ⁅s, a⁆ ∈ ⁅S, A⁆ := Subgroup.commutator_mem_commutator hs ha
  have hnorm : a * n⁻¹ * a⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hAN ha) n⁻¹).mp (N.inv_mem hn)
  have key : ⁅n * s, a⁆ = n * ⁅s, a⁆ * (a * n⁻¹ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact (N ⊔ ⁅S, A⁆).mul_mem
    ((N ⊔ ⁅S, A⁆).mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hcomm))
    (Subgroup.mem_sup_left hnorm)

theorem le_normalizer_commutator {A S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup G) : Set G) := by
  have hconj : ∀ b ∈ A, ∀ c ∈ ⁅S, A⁆, b * c * b⁻¹ ∈ ⁅S, A⁆ := by
    intro b hb
    have hle : ⁅S, A⁆ ≤ Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj b)) ⁅S, A⁆ := by
      rw [Subgroup.commutator_le]
      intro s hs a' ha'
      show b * ⁅s, a'⁆ * b⁻¹ ∈ ⁅S, A⁆
      have e : b * ⁅s, a'⁆ * b⁻¹ = ⁅b * s * b⁻¹, b * a' * b⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hAS hb) s).mp hs)
        (A.mul_mem (A.mul_mem hb ha') (A.inv_mem hb))
    intro c hc
    exact hle hc
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj a ha h hh
  · intro hh
    have h' := hconj a⁻¹ (A.inv_mem ha) (a * h * a⁻¹) hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem commutator_le_self {A S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) : ⁅S, A⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro s hs a ha
  have hn : a * s⁻¹ * a⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hAS ha) s⁻¹).mp (S.inv_mem hs)
  have key : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  rw [key]
  exact S.mul_mem hs hn


theorem le_normalizer_sup_of_normal_image {Y X : Subgroup G} (hXY : X ≤ Y)
    (hn : ((X.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 3 ↥Y))).Normal) :
    Y ≤ Subgroup.normalizer ((X ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G) := by
  have hcomap : ((X.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 3 ↥Y))).comap
      (QuotientGroup.mk' (pPrimeCore 3 ↥Y)) = X.subgroupOf Y ⊔ pPrimeCore 3 ↥Y := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hMnormal : (X.subgroupOf Y ⊔ pPrimeCore 3 ↥Y).Normal := by
    rw [← hcomap]
    exact hn.comap (QuotientGroup.mk' (pPrimeCore 3 ↥Y))
  have hmap : X ⊔ pPrimeCoreOf 3 Y = (X.subgroupOf Y ⊔ pPrimeCore 3 ↥Y).map Y.subtype := by
    unfold pPrimeCoreOf
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXY]
  have hHeq : (X ⊔ pPrimeCoreOf 3 Y).subgroupOf Y = X.subgroupOf Y ⊔ pPrimeCore 3 ↥Y := by
    rw [hmap]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective Y) _
  have hO : pPrimeCoreOf 3 Y ≤ Y := by
    unfold pPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hsub : X ⊔ pPrimeCoreOf 3 Y ≤ Y := sup_le hXY hO
  rw [← hHeq] at hMnormal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mp hMnormal

theorem commutator_commutator_eq {A S : Subgroup G} (hA3 : IsPGroup 3 A)
    (hS3 : ¬ 3 ∣ Nat.card S) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ⁅⁅S, A⁆, A⁆ = ⁅S, A⁆ := by
  have hfact : S = ⁅S, A⁆ ⊔ (S ⊓ Subgroup.centralizer (A : Set G)) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A S hA3 hS3 hAS
  have hCK : S ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (⁅S, A⁆ : Subgroup G) :=
    le_trans inf_le_left (Subgroup.normalizer_commutator_ge_left S A)
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.normalizer_commutator_ge_right S A)
  · apply Subgroup.commutator_le.mpr
    intro s hs a ha
    have hsK : s ∈ ((⁅S, A⁆ ⊔ (S ⊓ Subgroup.centralizer (A : Set G)) : Subgroup G) : Set G) := by
      rw [← hfact]
      exact hs
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCK] at hsK
    obtain ⟨u, hu, c, hc, hsc⟩ := Set.mem_mul.mp hsK
    subst hsc
    have hc' : c ∈ S ⊓ Subgroup.centralizer (A : Set G) := hc
    have hcomm : ∀ x ∈ (A : Set G), x * c = c * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc').2
    have hac : a * c = c * a := hcomm a ha
    have hcac : c * a * c⁻¹ = a := by
      rw [← hac, mul_inv_cancel_right]
    have hkey : ⁅u * c, a⁆ = ⁅u, a⁆ := by
      simp only [commutatorElement_def]
      calc u * c * a * (u * c)⁻¹ * a⁻¹ = u * (c * a * c⁻¹) * u⁻¹ * a⁻¹ := by group
        _ = u * a * u⁻¹ * a⁻¹ := by rw [hcac]
    rw [hkey]
    exact Subgroup.commutator_mem_commutator hu ha

theorem normalizer_ne_top_of_simple {D : Subgroup G} (hG : IsSimpleGroup G)
    (hab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (hD : IsPGroup p D) (hD1 : D ≠ ⊥) :
    Subgroup.normalizer (D : Set G) ≠ ⊤ := by
  intro hnorm
  have hDnormal : D.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  have hDtop : D = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top D).resolve_left hD1
  subst hDtop
  have hGp : IsPGroup p G := hD.of_equiv Subgroup.topEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center G = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G)).resolve_left
      (IsPGroup.bot_lt_center hGp).ne'
  obtain ⟨a, b, hne⟩ := hab
  apply hne
  have hb : b ∈ Subgroup.center G := by
    rw [hcen]
    exact Subgroup.mem_top b
  exact (Subgroup.mem_center_iff.mp hb) a


theorem key_core {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {A Y X F K N₁ V U : Subgroup G}
    (hA3 : IsPGroup 3 A) (hAY : A ≤ Y) (hXY : X ≤ Y)
    (hXN : Y ≤ Subgroup.normalizer ((X ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G))
    (hXF : X = pPrimeCoreOf 3 X ⊔ F)
    (hAF : A ≤ Subgroup.normalizer (F : Set G))
    (hFK : F ≤ K ⊔ V)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hV : V ≤ Subgroup.centralizer (A : Set G))
    (hVK : V ≤ Subgroup.normalizer (K : Set G))
    (hN₁3 : ¬ 3 ∣ Nat.card N₁) (hFN₁ : F ≤ Subgroup.normalizer (N₁ : Set G))
    (hEnv : ∀ U' : Subgroup G, IsPGroup p U' → U' ≤ K → A ≤ Subgroup.normalizer (U' : Set G) →
      U' ≤ N₁)
    (hU : IsPGroup p U) (hUX : U ≤ X) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hUA : ⁅U, A⁆ = U) : U ≤ pPrimeCoreOf 3 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 Y with hN
  have hNY : N ≤ Y := pPrimeCoreOf_le 3 Y
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := hAY.trans hYN
  have hFX : F ≤ X := hXF ▸ le_sup_right
  have hFY : F ≤ Y := hFX.trans hXY
  have hX₀X : pPrimeCoreOf 3 X ≤ X := pPrimeCoreOf_le 3 X
  have hX₀Y : pPrimeCoreOf 3 X ≤ Y := hX₀X.trans hXY
  have hX₀3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
  have hX₀N : pPrimeCoreOf 3 X ≤ N := by
    have hM : N ⊔ pPrimeCoreOf 3 X ≤ N := by
      refine le_pPrimeCoreOf_of_normal (Y := Y) (X := X) hXY hXN ?_ ?_ ?_
      · exact sup_le le_sup_right (hX₀X.trans le_sup_left)
      · exact not_three_dvd_card_sup (hX₀Y.trans hYN) hN3 hX₀3
      · refine sup_le ?_ ?_
        · exact Sec14.le_normalizer_sup (hXY.trans hYN) (le_normalizer_pPrimeCoreOf 3 X)
        · exact le_sup_left.trans Subgroup.le_normalizer
    exact le_sup_right.trans hM
  have hXNF : X ≤ N ⊔ F := by
    rw [hXF]
    exact sup_le_sup_right hX₀N F
  obtain ⟨S, hSF, hSp, hAS, hUNS⟩ := exists_invariant_pSubgroup_le_sup hp hp3 hA3 hNY hYN hN3 hFY
    hU (hUX.trans hXNF) hAN hAF hAU
  have hSK : ⁅S, A⁆ ≤ K := commutator_le_of_le_sup_centralizer hAK hV hVK (hSF.trans hFK)
  have hUc : U ≤ N ⊔ ⁅S, A⁆ := by
    calc U = ⁅U, A⁆ := hUA.symm
      _ ≤ N ⊔ ⁅S, A⁆ := commutator_le_sup_of_le_sup hAN hUNS ((hSF.trans hFY).trans hYN)
  have hU'p : IsPGroup p (⁅S, A⁆ : Subgroup G) := hSp.to_le (commutator_le_self hAS)
  have hAU' : A ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hAS
  have hU'N₁ : ⁅S, A⁆ ≤ N₁ := hEnv _ hU'p hSK hAU'
  have hU'F : ⁅S, A⁆ ≤ F := (commutator_le_self hAS).trans hSF
  have hFN₁3 : ¬ 3 ∣ Nat.card (F ⊓ N₁ : Subgroup G) := fun h =>
    hN₁3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hM : N ⊔ (F ⊓ N₁) ≤ N := by
    refine le_pPrimeCoreOf_of_normal (Y := Y) (X := X) hXY hXN ?_ ?_ ?_
    · exact sup_le le_sup_right ((inf_le_left.trans hFX).trans le_sup_left)
    · exact not_three_dvd_card_sup ((inf_le_left.trans hFY).trans hYN) hN3 hFN₁3
    · have hFM : F ≤ Subgroup.normalizer ((N ⊔ (F ⊓ N₁) : Subgroup G) : Set G) :=
        Sec14.le_normalizer_sup (hFY.trans hYN)
          (Late.le_normalizer_inf (Subgroup.le_normalizer) hFN₁)
      have hX₀M : pPrimeCoreOf 3 X ≤ Subgroup.normalizer ((N ⊔ (F ⊓ N₁) : Subgroup G) : Set G) :=
        (hX₀N.trans le_sup_left).trans Subgroup.le_normalizer
      refine sup_le ?_ (le_sup_left.trans Subgroup.le_normalizer)
      rw [hXF]
      exact sup_le hX₀M hFM
  exact hUc.trans ((sup_le_sup_left (le_inf hU'F hU'N₁) N).trans hM)

end CFSG.RankThree.PartTwo.Sec17.F17Leaf
