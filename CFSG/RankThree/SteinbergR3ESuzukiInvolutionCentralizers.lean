module

public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

public section

namespace CFSG.RankThree

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
open scoped LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g y : G) :
    y ∈ (g • P : Sylow p G) ↔ g⁻¹ * y * g ∈ P := by
  change y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem card_suzukiU_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiU a K) = 2 ^ (Nat.card (suzukiGroup a K)).factorization 2 := by
  rw [(suzuki_unipotent_structure hK).2.1, suzuki_order hK]
  set q := 2 ^ (2 * a + 1) with hq
  have h2 : 2 ≤ q := two_le_two_pow_odd a
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hq0 : q ^ 2 ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by omega
  have hodd1 : ¬ 2 ∣ q - 1 := by
    have h : ∀ m : ℕ, 2 ∣ m → 2 ≤ m → ¬ 2 ∣ m - 1 := by omega
    exact h q hq2 h2
  have hodd2 : ¬ 2 ∣ q ^ 2 + 1 := by
    have h : ∀ m : ℕ, 2 ∣ m → ¬ 2 ∣ m + 1 := by omega
    exact h _ (dvd_pow hq2 two_ne_zero)
  rw [Nat.factorization_mul (mul_ne_zero hq0 hq1) (by positivity), Nat.factorization_mul hq0 hq1,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd1,
    Nat.factorization_eq_zero_of_not_dvd hodd2, add_zero, add_zero, hq, ← pow_mul,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    smul_eq_mul, mul_one, mul_comm]

theorem eq_suzukiSElt_zero_of_sq_eq_one [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : suzukiGroup a K} (hzU : z ∈ suzukiU a K) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ v : K, v ≠ 0 ∧ z = suzukiSElt a K 0 v := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hzU
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  rw [sq, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hz2
  have hu : u = 0 := by
    have h : u ^ 2 ^ (a + 1) * u = 0 := by
      have := hz2.2
      linear_combination this - v * h2
    rcases mul_eq_zero.1 h with h | h
    · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h
    · exact h
  subst hu
  refine ⟨v, fun hv => hz1 ?_, rfl⟩
  rw [hv, suzukiSElt_zero_zero hK]

theorem suzukiSElt_zero_smul_ne [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {v : K}
    (hv : v ≠ 0) (c d : K) : suzukiSElt a K 0 v • suzukiLine a K c d ≠ suzukiLine a K c d := by
  rw [suzukiSElt_smul_suzukiLine hK, zero_add, zero_pow (pow_ne_zero _ two_ne_zero), zero_mul,
    add_zero, Ne, suzukiLine_eq_iff]
  rintro ⟨-, h⟩
  exact hv (by linear_combination h)

theorem centralizer_eq_suzukiU [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : suzukiGroup a K} (hzU : z ∈ suzukiU a K) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    Subgroup.centralizer {z} = suzukiU a K := by
  obtain ⟨v, hv, rfl⟩ := eq_suzukiSElt_zero_of_sq_eq_one hK hzU hz2 hz1
  have hcomm : ∀ g ∈ suzukiU a K, g * suzukiSElt a K 0 v = suzukiSElt a K 0 v * g := by
    intro g hg
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    exact (suzukiSElt_zero_commute hK v c d).symm
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hzinf : suzukiSElt a K 0 v • suzukiInfty K = suzukiInfty K :=
      suzukiB_le_stabilizer hK (le_sup_left (a := suzukiU a K) hzU)
    have hfix : suzukiSElt a K 0 v • (g • suzukiInfty K) = g • suzukiInfty K := by
      rw [← mul_smul, ← hg, mul_smul, hzinf]
    have hginf : g • suzukiInfty K = suzukiInfty K := by
      rcases mem_suzukiOmega_iff.1 (suzuki_smul_mem_suzukiOmega hK g
        (suzukiInfty_mem_suzukiOmega a K)) with h | ⟨c, d, h⟩
      · exact h
      · rw [← h] at hfix
        exact absurd hfix (suzukiSElt_zero_smul_ne hK hv c d)
    have hgB : g ∈ suzukiB a K := by
      rw [← (suzuki_ovoid_stabilizer hK).1]
      exact hginf
    obtain ⟨c, d, l, rfl⟩ := (mem_suzukiB_iff hK).1 hgB
    have hSU : suzukiSElt a K c d ∈ suzukiU a K := (mem_suzukiU_iff hK).2 ⟨c, d, rfl⟩
    have hD : suzukiDElt a K l * suzukiSElt a K 0 v = suzukiSElt a K 0 v * suzukiDElt a K l := by
      have h1 := hcomm _ hSU
      have h2 : suzukiSElt a K c d * (suzukiDElt a K l * suzukiSElt a K 0 v) =
          suzukiSElt a K c d * (suzukiSElt a K 0 v * suzukiDElt a K l) := by
        rw [← mul_assoc, hg, ← mul_assoc, ← mul_assoc, h1]
      exact mul_left_cancel h2
    by_cases hl : l = 1
    · rw [hl, suzukiDElt_one, mul_one]
      exact hSU
    · exfalso
      have hzT : suzukiSElt a K 0 v ∈ suzukiT a K := by
        rw [← centralizer_suzukiDElt hK hl, Subgroup.mem_centralizer_singleton_iff]
        exact hD.symm
      have hzUT : suzukiSElt a K 0 v ∈ suzukiU a K ⊓ suzukiT a K :=
        ⟨(mem_suzukiU_iff hK).2 ⟨0, v, rfl⟩, hzT⟩
      rw [(suzuki_borel_structure hK).2.2.2.2.1, Subgroup.mem_bot, ← suzukiSElt_zero_zero hK,
        suzukiSElt_inj] at hzUT
      exact hv hzUT.2
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm g hg

theorem centralizer_eq_sylow [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : suzukiGroup a K} (hz : orderOf z = 2) (Q : Sylow 2 (suzukiGroup a K)) (hzQ : z ∈ Q) :
    Subgroup.centralizer {z} = Q := by
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := Sylow.ofCard (suzukiU a K) (card_suzukiU_eq hK)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P Q
  rw [mem_smul_sylow_iff] at hzQ
  have hz2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    rw [show g⁻¹ * z * g = (MulAut.conj g⁻¹) z by simp, ← map_pow,
      ← hz, pow_orderOf_eq_one, map_one]
  have hz1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    have : z = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hC := centralizer_eq_suzukiU hK hzQ hz2 hz1
  ext y
  change y ∈ Subgroup.centralizer {z} ↔ y ∈ (g • P : Sylow 2 (suzukiGroup a K))
  rw [mem_smul_sylow_iff, Subgroup.mem_centralizer_singleton_iff]
  change y * z = z * y ↔ g⁻¹ * y * g ∈ suzukiU a K
  rw [← hC, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [h]
      _ = g⁻¹ * z * g * (g⁻¹ * y * g) := by group
  · intro h
    calc y * z = g * (g⁻¹ * y * g * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = z * y := by group

theorem Suzuki_involution_centralizers_and_inner_odd_centralizers (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ z : suzukiGroup a K, orderOf z = 2 → ∃ P : Sylow 2 (suzukiGroup a K), z ∈ P ∧
      Subgroup.centralizer {z} = P ∧ ∀ Q : Sylow 2 (suzukiGroup a K), z ∈ Q → Q = P) ∧
    ∀ x : suzukiGroup a K, x ≠ 1 → Odd (orderOf x) →
      Odd (Nat.card (Subgroup.centralizer {x})) ∧
      Odd (Nat.card (Subgroup.centralizer {MulAut.conj x})) := by
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ z : suzukiGroup a K, orderOf z = 2 → ∃ P : Sylow 2 (suzukiGroup a K), z ∈ P ∧
      Subgroup.centralizer {z} = P ∧ ∀ Q : Sylow 2 (suzukiGroup a K), z ∈ Q → Q = P := by
    intro z hz
    have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
    obtain ⟨P, hP⟩ := hzp.exists_le_sylow
    have hzP : z ∈ P := hP (Subgroup.mem_zpowers z)
    refine ⟨P, hzP, centralizer_eq_sylow hK hz P hzP, fun Q hzQ => ?_⟩
    apply Sylow.ext
    rw [← centralizer_eq_sylow hK hz Q hzQ, centralizer_eq_sylow hK hz P hzP]
  refine ⟨hinv, fun x hx1 hxodd => ?_⟩
  have hCodd : Odd (Nat.card (Subgroup.centralizer {x})) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hz' : orderOf (z : suzukiGroup a K) = 2 := by rw [Subgroup.orderOf_coe, hz]
    obtain ⟨P, -, hPC, -⟩ := hinv z hz'
    have hxz : x ∈ Subgroup.centralizer {(z : suzukiGroup a K)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 z.2).symm
    rw [hPC] at hxz
    have hdvd : orderOf x ∣ 2 ^ (Nat.card (suzukiGroup a K)).factorization 2 := by
      rw [← Sylow.card_eq_multiplicity P, ← Subgroup.orderOf_mk x hxz]
      exact orderOf_dvd_natCard _
    have h1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (hxodd.coprime_two_right.pow_right _) hdvd
    exact hx1 (orderOf_eq_one_iff.1 h1)
  refine ⟨hCodd, ?_⟩
  obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
  have hcenter : Subgroup.center (suzukiGroup a K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with
      h | h
    · exact h
    · have h1 := (suzuki_perfect ha hK).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  have hconj : Function.Injective (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center (suzukiGroup a K) := Subgroup.mem_center_iff.2 fun y => by
      have := congrArg (fun α : MulAut (suzukiGroup a K) => α y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hcenter, Subgroup.mem_bot] at hgZ
    exact hgZ
  obtain ⟨-, -, -, -, -, hOcard, -⟩ :=
    Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  have : Finite (MulAut (suzukiGroup a K)) := inferInstance
  by_contra hev
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have hα2 : orderOf (α : MulAut (suzukiGroup a K)) = 2 := by rw [Subgroup.orderOf_coe, hα]
  have hαinner : (α : MulAut (suzukiGroup a K)) ∈ inner (suzukiGroup a K) := by
    have h1 : orderOf (QuotientGroup.mk (s := inner (suzukiGroup a K))
        (α : MulAut (suzukiGroup a K))) ∣ 2 := by
      rw [← hα2]
      exact orderOf_map_dvd (QuotientGroup.mk' (inner (suzukiGroup a K))) _
    have h2 : orderOf (QuotientGroup.mk (s := inner (suzukiGroup a K))
        (α : MulAut (suzukiGroup a K))) ∣ 2 * a + 1 := by
      rw [← hOcard]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk (s := inner (suzukiGroup a K))
        (α : MulAut (suzukiGroup a K))) = 1 := by
      have hcop : Nat.Coprime 2 (2 * a + 1) := by
        rw [Nat.coprime_two_left]
        exact odd_two_mul_add_one a
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨z, hz⟩ := hαinner
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective _ hconj z]
    change orderOf (MulAut.conj z) = 2
    rw [hz, hα2]
  have hzx : z * x = x * z := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 α.2
    rw [← hz, ← map_mul, ← map_mul] at h
    exact hconj h
  have hzC : z ∈ Subgroup.centralizer {x} := Subgroup.mem_centralizer_singleton_iff.2 hzx
  have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer {x}) := by
    rw [← hz2, ← Subgroup.orderOf_mk z hzC]
    exact orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.2 hCodd) (even_iff_two_dvd.2 h2dvd)

end CFSG.RankThree
