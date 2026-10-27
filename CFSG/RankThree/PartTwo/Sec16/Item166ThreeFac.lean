module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2
public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec20.SimsYKO3FiveFac
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CoverA
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CoverB

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_mem_normalizer_map {H : Type} [Group H] [Finite H]
    {N K : Subgroup H} [N.Normal] (hN : ¬ 2 ∣ Nat.card N) (hK : IsPGroup 2 K) {x : H}
    (hx : (x : H ⧸ N) ∈ Subgroup.normalizer
      ((K.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))) :
    ∃ z ∈ N, ∃ n ∈ Subgroup.normalizer (K : Set H), x = z * n := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N : H →* H ⧸ N) :=
    QuotientGroup.mk'_surjective N
  have hnorm : x ∈ Subgroup.normalizer ((K ⊔ N : Subgroup H) : Set H) := by
    have h1 : x ∈ (Subgroup.normalizer
        ((K.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))).comap
        (QuotientGroup.mk' N) := Subgroup.mem_comap.2 hx
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hsurj] at h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.frattini_odd_normal hN hK hnorm

theorem exists_mul_mul_mem_normalizer_of_map_mem_normalizer {H : Type} [Group H] [Finite H]
    {N K₁ K₂ : Subgroup H} [N.Normal] (hN : ¬ 2 ∣ Nat.card N)
    (hK₁ : IsPGroup 2 K₁) (hK₂ : IsPGroup 2 K₂) {r x y : H}
    (hxy : (x : H ⧸ N) * (y : H ⧸ N) = (r : H ⧸ N))
    (hx : (x : H ⧸ N) ∈ Subgroup.normalizer
      ((K₁.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)))
    (hy : (y : H ⧸ N) ∈ Subgroup.normalizer
      ((K₂.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))) :
    ∃ o ∈ N, ∃ n ∈ Subgroup.normalizer (K₁ : Set H),
      ∃ m ∈ Subgroup.normalizer (K₂ : Set H), r = o * n * m := by
  have hker : x * y * r⁻¹ ∈ N := by
    refine (QuotientGroup.eq_one_iff (N := N) (x * y * r⁻¹)).mp ?_
    have h1 : (QuotientGroup.mk' N) (x * y) = (QuotientGroup.mk' N) r := by
      rw [map_mul]; exact hxy
    calc (QuotientGroup.mk' N) (x * y * r⁻¹)
        = (QuotientGroup.mk' N) (x * y) * ((QuotientGroup.mk' N) r)⁻¹ := by
          rw [map_mul, map_inv]
      _ = (QuotientGroup.mk' N) r * ((QuotientGroup.mk' N) r)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  set n₀ : H := x * y * r⁻¹ with hn₀
  have hn₀N : n₀ ∈ N := by rw [hn₀]; exact hker
  have hr : r = n₀⁻¹ * x * y := by
    rw [hn₀]; group
  obtain ⟨z₁, hz₁, n, hn, hxeq⟩ := exists_mul_mem_normalizer_of_mem_normalizer_map
    (N := N) (K := K₁) hN hK₁ hx
  obtain ⟨z₂, hz₂, m, hm, hyeq⟩ := exists_mul_mem_normalizer_of_mem_normalizer_map
    (N := N) (K := K₂) hN hK₂ hy
  have hconj : n * z₂ * n⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem z₂ hz₂ n
  have hoN : n₀⁻¹ * z₁ * (n * z₂ * n⁻¹) ∈ N :=
    N.mul_mem (N.mul_mem (N.inv_mem hn₀N) hz₁) hconj
  refine ⟨n₀⁻¹ * z₁ * (n * z₂ * n⁻¹), hoN, n, hn, m, hm, ?_⟩
  rw [hr, hxeq, hyeq]
  group

private theorem quotient_hypotheses {R : Subgroup G} (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R) :
    ¬ 3 ∣ Nat.card (⊤ : Subgroup (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) ∧
      ∀ K : Subgroup (↥R ⧸ CFSG.pPrimeCore 2 ↥R), K ≤ ⊤ →
        ⊤ ≤ Subgroup.normalizer (K : Set (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) →
          ¬ 2 ∣ Nat.card K → K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥R := hRs
  have h3Q : ¬ 3 ∣ Nat.card (↥R ⧸ CFSG.pPrimeCore 2 ↥R) := by
    intro h
    apply h3
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 ↥R)]
    exact dvd_mul_of_dvd_left h _
  refine ⟨?_, ?_⟩
  · rwa [Subgroup.card_top]
  · intro K _ hKn hK
    have hOcore : CFSG.pPrimeCore 2 (↥R ⧸ CFSG.pPrimeCore 2 ↥R) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥R) 2
    rw [CFSG.pPrimeCore_eq_bot_iff] at hOcore
    exact hOcore K (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKn))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hK)

private theorem exists_quotient_factor {R S : Subgroup G} (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R) (hSR : S ≤ R) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex R) (rR : ↥R) :
    ∃ x y : ↥R,
      ((QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) x *
        (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) y =
          (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) rR) ∧
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) x ∈ Subgroup.normalizer
        (((jOf (S.subgroupOf R)).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) :
          Subgroup (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) :
            Set (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) ∧
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) y ∈ Subgroup.normalizer
        (((omegaOneZ (jOneOf (S.subgroupOf R))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥R)) :
          Subgroup (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) :
            Set (↥R ⧸ CFSG.pPrimeCore 2 ↥R)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥R := CFSG.pPrimeCore 2 ↥R
  haveI hNn : N.Normal := CFSG.pPrimeCore_normal
  have hNcop : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  let S₁ : Subgroup ↥R := S.subgroupOf R
  have hS₁2 : IsPGroup 2 S₁ := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSR).symm
  have hS₁idx : ¬ 2 ∣ S₁.index := hSidx
  have hcopS : Nat.Coprime (Nat.card S₁) (Nat.card N) := by
    obtain ⟨n, hn⟩ := hS₁2.exists_card_eq
    rw [hn]
    exact hNcop.pow_left n
  have hdisj : Disjoint S₁ N := Subgroup.disjoint_of_coprime_natCard hcopS
  have hinj : ∀ x ∈ S₁, (QuotientGroup.mk' N) x = 1 → x = 1 := by
    intro x hxS hx1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 hx1
    exact Subgroup.mem_bot.1 (hdisj.le_bot ⟨hxS, hxN⟩)
  obtain ⟨h3top, hO⟩ := quotient_hypotheses hRs h3
  have hSbar2 : IsPGroup 2 (S₁.map (QuotientGroup.mk' N)) := hS₁2.map _
  have hSbaridx : ¬ 2 ∣ (S₁.map (QuotientGroup.mk' N)).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    exact fun h => hS₁idx (h.trans (Subgroup.index_map_dvd (H := S₁)
      (QuotientGroup.mk'_surjective N)))
  have hsolvTop : Group.IsSolvable ↥(⊤ : Subgroup (↥R ⧸ N)) := inferInstance
  have hfac := CFSG.RankThree.PartTwo.Sec20.SimsYKO3.fac_zero_one_three
    (G := ↥R ⧸ N) (R := ⊤) (S := S₁.map (QuotientGroup.mk' N)) hsolvTop h3top hO le_top
    hSbar2 hSbaridx
  unfold CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.Fac at hfac
  have hrq : (QuotientGroup.mk' N) rR ∈
      ((Subgroup.normalizer (jOf (S₁.map (QuotientGroup.mk' N)) : Set (↥R ⧸ N)) ⊓
        ⊤ : Subgroup (↥R ⧸ N)) : Set (↥R ⧸ N)) *
      ((Subgroup.normalizer (omegaOneZ (jOneOf (S₁.map (QuotientGroup.mk' N))) :
        Set (↥R ⧸ N)) ⊓ ⊤ : Subgroup (↥R ⧸ N)) : Set (↥R ⧸ N)) := by
    rw [hfac]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hrq
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hJq : jOf (S₁.map (QuotientGroup.mk' N)) =
      (jOf S₁).map (QuotientGroup.mk' N) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.jOf_map hinj
  have hΩq : omegaOneZ (jOneOf (S₁.map (QuotientGroup.mk' N))) =
      (omegaOneZ (jOneOf S₁)).map (QuotientGroup.mk' N) := by
    have h1 : jOneOf (S₁.map (QuotientGroup.mk' N)) =
        (jOneOf S₁).map (QuotientGroup.mk' N) :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.jOneOf_map hinj
    rw [h1]
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.omegaOneZ_map hinj
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.jOneOf_le S₁)
  have hx' : (QuotientGroup.mk' N) x₀ ∈ Subgroup.normalizer
      (((jOf S₁).map (QuotientGroup.mk' N) : Subgroup (↥R ⧸ N)) : Set (↥R ⧸ N)) := by
    rw [← hJq]
    exact hx.1
  have hy' : (QuotientGroup.mk' N) y₀ ∈ Subgroup.normalizer
      (((omegaOneZ (jOneOf S₁)).map (QuotientGroup.mk' N) : Subgroup (↥R ⧸ N)) :
        Set (↥R ⧸ N)) := by
    rw [← hΩq]
    exact hy.1
  exact ⟨x₀, y₀, hxy, hx', hy'⟩

private theorem exists_mul_mul_mem_normalizer {R S : Subgroup G} (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R) (hSR : S ≤ R) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex R) (rR : ↥R) :
    ∃ o ∈ CFSG.pPrimeCore 2 ↥R,
      ∃ n ∈ Subgroup.normalizer (jOf (S.subgroupOf R) : Set ↥R),
        ∃ m ∈ Subgroup.normalizer (omegaOneZ (jOneOf (S.subgroupOf R)) : Set ↥R),
          rR = o * n * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥R := CFSG.pPrimeCore 2 ↥R
  haveI : N.Normal := CFSG.pPrimeCore_normal
  have hNcop : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hNodd : ¬ 2 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hNcop
  let S₁ : Subgroup ↥R := S.subgroupOf R
  have hS₁2 : IsPGroup 2 S₁ := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSR).symm
  have hJ₁2 : IsPGroup 2 (jOf S₁) := by
    have h := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_isPGroup hS₁2 0
    rwa [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_zero] at h
  have hΩ₁2 : IsPGroup 2 (omegaOneZ (jOneOf S₁)) := by
    have h := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_isPGroup hS₁2 1
    rwa [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_one] at h
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_quotient_factor hRs h3 hSR hS2 hSidx rR
  exact exists_mul_mul_mem_normalizer_of_map_mem_normalizer hNodd hJ₁2 hΩ₁2 hxy hx hy

private theorem jOf_omegaOneZ_subgroupOf_map {R S : Subgroup G} (hSR : S ≤ R) :
    jOf S = (jOf (S.subgroupOf R)).map R.subtype ∧
      omegaOneZ (jOneOf S) = (omegaOneZ (jOneOf (S.subgroupOf R))).map R.subtype := by
  have hS₁map : (S.subgroupOf R).map R.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSR
  have hinj : ∀ x ∈ S.subgroupOf R, R.subtype x = 1 → x = 1 := fun x _ hx => Subtype.ext hx
  constructor
  · have h := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.jOf_map
      (f := R.subtype) (T₁ := S.subgroupOf R) hinj
    rwa [hS₁map] at h
  · have h1 : jOneOf S = (jOneOf (S.subgroupOf R)).map R.subtype := by
      have h := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.jOneOf_map
        (f := R.subtype) (T₁ := S.subgroupOf R) hinj
      rwa [hS₁map] at h
    rw [h1]
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.omegaOneZ_map hinj
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.jOneOf_le (S.subgroupOf R))

theorem mem_pPrimeCoreOf_mul_normalizer {R S : Subgroup G} (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R) (hSR : S ≤ R) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex R) {r : G} (hr : r ∈ R) :
    ∃ o ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 R,
      ∃ x ∈ Subgroup.normalizer (jOf S : Set G) ⊓ R,
        ∃ y ∈ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R, r = o * x * y := by
  obtain ⟨rR, rfl⟩ : ∃ rR : ↥R, (rR : G) = r := ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨o, ho, n, hn, m, hm, hrR⟩ := exists_mul_mul_mem_normalizer hRs h3 hSR hS2 hSidx rR
  obtain ⟨hJG, hΩG⟩ := jOf_omegaOneZ_subgroupOf_map hSR
  refine ⟨(o : G), ?_, (n : G), ⟨?_, n.2⟩, (m : G), ⟨?_, m.2⟩, ?_⟩
  · exact Subgroup.mem_map_of_mem R.subtype ho
  · rw [hJG]
    exact CFSG.HardMathSupport.Solomon.Coordinator.I28_8.mem_normalizer_map_subtype hn
  · rw [hΩG]
    exact CFSG.HardMathSupport.Solomon.Coordinator.I28_8.mem_normalizer_map_subtype hm
  · simpa using congrArg Subtype.val hrR

theorem le_of_normalizer_le {R S M : Subgroup G} (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R) (hSR : S ≤ R) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex R) (hO : CFSG.GH74.GLS.pPrimeCoreOf 2 R ≤ M)
    (hJ : Subgroup.normalizer (jOf S : Set G) ⊓ R ≤ M)
    (hΩ : Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R ≤ M) : R ≤ M := by
  intro r hr
  obtain ⟨o, ho, x, hx, y, hy, hr_eq⟩ :=
    mem_pPrimeCoreOf_mul_normalizer hRs h3 hSR hS2 hSidx hr
  rw [hr_eq]
  exact M.mul_mem (M.mul_mem (hO ho) (hJ hx)) (hΩ hy)

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
