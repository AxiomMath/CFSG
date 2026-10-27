module

public import CFSG.Sporadic.Recognition.HNMult3
public import Certificates.Certificate26963
public import CFSG.Sporadic.HN

public section

namespace CFSG.Sporadic.Recognition.HNMult3

open CFSG.CosetTable CFSG.Sporadic.GLQ.HNTwoRank CFSG.Blueprint

theorem hn3_rels_of_certificate :
    (∀ r ∈ hn3Rels, FreeGroup.lift gN (FreeGroup.mk r) = 1) ∧
      (∀ i, hn3Ord i = 0 → FreeGroup.lift gN (FreeGroup.mk (hn3Cw i)) = gN i) ∧
      (∀ i, hn3Ord i ≠ 0 → gN i ^ hn3Ord i = 1) :=
  (Certificates.certificate26963.1 : _ ∧ _).1

theorem hn3_card_ge_of_certificate :
    58320 ≤ Nat.card Nsub :=
  (Certificates.certificate26963.1 : _ ∧ _).2

theorem hn3_cover_of_certificate :
    Finite (PG 3 hn3Cover) ∧ Nat.card (PG 3 hn3Cover) ≤ 58320 :=
  Certificates.certificate26963.2

theorem factorization_card_HN_three : (Nat.factorization 273030912000000) 3 = 6 := by
  rw [show 273030912000000 = 3 ^ 6 * (2 ^ 14 * 5 ^ 6 * 7 * 11 * 19) by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem ker_eq_bot_of_certificate
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.HN) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  let e : NativeSporadic.HN ≃* J := hnEquivJ
  let ι₀ : NativeSporadic.HN →* GLHN := J.subtype.comp (e : NativeSporadic.HN →* J)
  let ι : E →* GLHN := ι₀.comp π
  have hker : ι.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change ((e (π x) : J) : GLHN) = 1 ↔ _
    rw [← Subgroup.coe_one J, Subtype.coe_inj, ← map_one e, e.injective.eq_iff]
  have hNle : Nsub ≤ ι.range := by
    intro y hy
    obtain ⟨z, hz⟩ := e.surjective ⟨y, Nsub_le_J hy⟩
    obtain ⟨x, rfl⟩ := hπ z
    exact ⟨x, congrArg Subtype.val hz⟩
  have hrange : ι.range ≤ J := by
    rintro _ ⟨x, rfl⟩
    exact (e (π x)).2
  have hJcard : Nat.card J = 273030912000000 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.Sporadic.HN.card_HN]
  have hsyl : (Nat.card ι.range).factorization 3 ≤ 6 := by
    have hdvd : Nat.card ι.range ∣ Nat.card J := Subgroup.card_dvd_of_le hrange
    have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 3
    rw [hJcard, factorization_card_HN_three] at h1
    exact h1
  have := ker_eq_bot_of_hn3 hn3_rels_of_certificate hn3_card_ge_of_certificate
    hn3_cover_of_certificate ι hNle hsyl (hker ▸ hC) (hker ▸ hp)
  rwa [hker] at this

end CFSG.Sporadic.Recognition.HNMult3
