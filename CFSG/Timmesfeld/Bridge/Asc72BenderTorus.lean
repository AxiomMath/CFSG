module

public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.BenderSuzuki CFSG.Open

variable {K : Type*} [Group K] [Finite K]

private theorem center_conj_mem_complement (hK : IsBenderGroup K) (Q : Sylow 2 K)
    {D : Subgroup K}
    (hDleN : D ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K))
    (hsupN : (Q : Subgroup K) ⊔ D = Subgroup.normalizer ((Q : Subgroup K) : Set K))
    {z z' : ↥(Q : Subgroup K)}
    (hz : z ∈ Subgroup.center ↥(Q : Subgroup K))
    (hz' : z' ∈ Subgroup.center ↥(Q : Subgroup K))
    (hz1 : (z : K) ≠ 1) (hz'1 : (z' : K) ≠ 1)
    (hsq : ∀ w ∈ Subgroup.center ↥(Q : Subgroup K), w ^ 2 = 1) :
    ∃ d ∈ D, (d : K) * (z : K) * (d : K)⁻¹ = (z' : K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentZ : ∀ w : ↥(Subgroup.center ↥(Q : Subgroup K)),
      ((w : ↥(Q : Subgroup K)) : K) ∈
        Subgroup.centralizer ((Q : Subgroup K) : Set K) := fun w =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (IsBenderGroup.commute_of_mul_self_eq_one hK Q w.1.2
        (by simpa [pow_two] using congrArg Subtype.val (hsq w.1 w.2)) y hy).symm
  have hzord : orderOf (z : K) = 2 :=
    orderOf_eq_prime (congrArg Subtype.val (hsq z hz)) hz1
  have hz'ord : orderOf (z' : K) = 2 :=
    orderOf_eq_prime (congrArg Subtype.val (hsq z' hz')) hz'1
  obtain ⟨g, hg⟩ := isConj_iff.1
    (IsBenderGroup.isConj_of_orderOf_eq_two hK hzord hz'ord)
  have hg' : g⁻¹ * (z' : K) * g = (z : K) := by
    rw [← hg]
    group
  obtain ⟨n, hn, hnconj⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer Q
    (z' : K) g (hcentZ ⟨z', hz'⟩) (by rw [hg']; exact hcentZ ⟨z, hz⟩)
  have hnz : n * (z : K) * n⁻¹ = (z' : K) := by
    have h1 : (z : K) = n⁻¹ * (z' : K) * n := by
      rw [← hg']
      exact hnconj
    calc n * (z : K) * n⁻¹ = n * (n⁻¹ * (z' : K) * n) * n⁻¹ := by rw [h1]
      _ = (z' : K) := by group
  have hsupQ : ((Q : Subgroup K).subgroupOf
        (Subgroup.normalizer ((Q : Subgroup K) : Set K))) ⊔
      (D.subgroupOf (Subgroup.normalizer ((Q : Subgroup K) : Set K))) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hDleN, hsupN,
      Subgroup.subgroupOf_self]
  have hmemN : (⟨n, hn⟩ : ↥(Subgroup.normalizer ((Q : Subgroup K) : Set K))) ∈
      ((Q : Subgroup K).subgroupOf (Subgroup.normalizer ((Q : Subgroup K) : Set K))) ⊔
        (D.subgroupOf (Subgroup.normalizer ((Q : Subgroup K) : Set K))) := by
    rw [hsupQ]
    exact Subgroup.mem_top _
  obtain ⟨q, hq, d, hd, hqd⟩ := Subgroup.mem_sup_of_normal_left.mp hmemN
  have hqQ : (q : K) ∈ Q := hq; have hdD : (d : K) ∈ D := hd
  have hqdK : n = (q : K) * (d : K) := by
    simpa using (congrArg Subtype.val hqd).symm
  have hdN : (d : K) ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := hDleN hdD
  have hdinv : ∀ y ∈ (Q : Subgroup K), (d : K)⁻¹ * y * (d : K) ∈ (Q : Subgroup K) := by
    intro y hy
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) y).mp hy
  have hXcentQ : (d : K) * (z : K) * (d : K)⁻¹ ∈
      Subgroup.centralizer ((Q : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (d : K)⁻¹ * y * (d : K) ∈ Q := hdinv y hy
    have hc : ((d : K)⁻¹ * y * (d : K)) * (z : K) =
        (z : K) * ((d : K)⁻¹ * y * (d : K)) :=
      (Subgroup.mem_centralizer_iff.1 (hcentZ ⟨z, hz⟩)) _ hy'
    calc
      y * ((d : K) * (z : K) * (d : K)⁻¹) =
          (d : K) * (((d : K)⁻¹ * y * (d : K)) * (z : K)) * (d : K)⁻¹ := by
        group
      _ = (d : K) * ((z : K) * ((d : K)⁻¹ * y * (d : K))) * (d : K)⁻¹ := by
        rw [hc]
      _ = ((d : K) * (z : K) * (d : K)⁻¹) * y := by group
  have hXcent : Commute (q : K) ((d : K) * (z : K) * (d : K)⁻¹) :=
    (Subgroup.mem_centralizer_iff.1 hXcentQ) (q : K) hqQ
  refine ⟨(d : K), hdD, ?_⟩
  rw [← hnz, hqdK]
  symm
  calc
    ((q : K) * (d : K)) * (z : K) * ((q : K) * (d : K))⁻¹ =
        (q : K) * ((d : K) * (z : K) * (d : K)⁻¹) * (q : K)⁻¹ := by group
    _ = (d : K) * (z : K) * (d : K)⁻¹ := by
      rw [hXcent.eq]
      group

private theorem center_eq_one_of_commute (hK : IsBenderGroup K) (Q : Sylow 2 K) {t : K}
    (htrans : ∀ z ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
      ∀ z' ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
        z ≠ 1 → z' ≠ 1 → ∃ k : ℕ, t ^ k * z * (t ^ k)⁻¹ = z')
    (hsq : ∀ w ∈ Subgroup.center ↥(Q : Subgroup K), w ^ 2 = 1)
    {z : K} (hz : z ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype)
    (hcomm : Commute t z) : z = 1 := by
  classical
  by_contra hz1
  rcases Subgroup.mem_map.1 hz with ⟨z0, hz0, rfl⟩
  have hz0sq : (z0 : K) ^ 2 = 1 := congrArg Subtype.val (hsq z0 hz0)
  have hz0ord : orderOf (z0 : K) = 2 := orderOf_eq_prime hz0sq hz1
  have hz0Z : (z0 : K) ∈ (Subgroup.center ↥(Q : Subgroup K)).map
      (Q : Subgroup K).subtype :=
    Subgroup.mem_map_of_mem (Q : Subgroup K).subtype hz0
  have hsub : (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype ≤
      Subgroup.zpowers (z0 : K) := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    · obtain ⟨m, hm⟩ := htrans w hw (z0 : K) hz0Z hw1 hz1
      have hpow : Commute (t ^ m) (z0 : K) := hcomm.pow_left m
      have hfixm : t ^ m * (z0 : K) * (t ^ m)⁻¹ = (z0 : K) := by
        rw [hpow.eq]
        group
      have hwz : w = (z0 : K) := by
        have hm' : t ^ m * w * (t ^ m)⁻¹ = t ^ m * (z0 : K) * (t ^ m)⁻¹ := by
          rw [hm, hfixm]
        have h := congrArg (fun x => (t ^ m)⁻¹ * x * (t ^ m)) hm'
        simpa using h
      rw [hwz]
      exact Subgroup.mem_zpowers _
  have hle : Nat.card ((Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype) ≤
      Nat.card (Subgroup.zpowers (z0 : K)) := Subgroup.card_le_of_le hsub
  have htwo : Nat.card (Subgroup.zpowers (z0 : K)) = 2 := by
    rw [Nat.card_zpowers, hz0ord]
  have hfour : 4 ≤ Nat.card ((Subgroup.center ↥(Q : Subgroup K)).map
      (Q : Subgroup K).subtype) := by
    rw [Subgroup.card_map_of_injective (K := Subgroup.center ↥(Q : Subgroup K))
      (Q : Subgroup K).subtype_injective]
    exact IsBenderGroup.four_le_card_center hK Q
  rw [htwo] at hle
  omega

theorem IsBenderGroup.exists_torus (hK : IsBenderGroup K) (Q : Sylow 2 K) :
    ∃ t ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K),
      (∀ z ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
        ∀ z' ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
          z ≠ 1 → z' ≠ 1 → ∃ k : ℕ, t ^ k * z * (t ^ k)⁻¹ = z') ∧
      ∀ z ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
        Commute t z → z = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hB, hq, hk⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  obtain ⟨-, ⟨D, hDcyc, hDodd, hQD, hsupN⟩, hsq, hZcard, hQcard⟩ := hB Q
  let Z : Subgroup K := (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype
  letI : IsCyclic ↥D := hDcyc
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥D)
  have htN : (t : K) ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    have h : (t : K) ∈ (Q : Subgroup K) ⊔ D := Subgroup.mem_sup_right t.2
    rwa [hsupN] at h
  have hDleN : D ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    rw [← hsupN]
    exact le_sup_right
  have htrans : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 →
      ∃ m : ℕ, (t : K) ^ m * z * ((t : K) ^ m)⁻¹ = z' := by
    intro z hz z' hz' hz1 hz'1
    rcases Subgroup.mem_map.1 hz with ⟨z0, hz0, rfl⟩
    rcases Subgroup.mem_map.1 hz' with ⟨z0', hz0', rfl⟩
    obtain ⟨d, hdD, hdz⟩ := center_conj_mem_complement hK Q hDleN hsupN
      hz0 hz0' hz1 hz'1 hsq
    have hdmem' : (⟨d, hdD⟩ : ↥D) ∈ Submonoid.powers t :=
      mem_powers_iff_mem_zpowers.mpr (ht _)
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (⟨d, hdD⟩ : ↥D) t).mp hdmem'
    have hmK : (t : K) ^ m = d := congrArg Subtype.val hm
    exact ⟨m, by simpa [hmK] using hdz⟩
  have htrans' : ∀ z ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
      ∀ z' ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype,
        z ≠ 1 → z' ≠ 1 → ∃ k : ℕ, (t : K) ^ k * z * ((t : K) ^ k)⁻¹ = z' := by
    simpa [Z] using htrans
  have hfix : ∀ z ∈ Z, Commute (t : K) z → z = 1 := by
    intro z hz hcomm
    exact center_eq_one_of_commute hK Q htrans' hsq (by simpa [Z] using hz) hcomm
  exact ⟨(t : K), htN, htrans', by simpa [Z] using hfix⟩

end CFSG.Timmesfeld.Bridge.Asc72
