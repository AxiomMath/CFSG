module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Group
public import CFSG.Quasithin.EmptyFaithful.S153D51
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure312Transport

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_of_le_sup_gen {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P T B : Subgroup G}
    (hP : IsPGroup p P) (hT : IsPGroup 2 T)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s) (hB : B ≤ P ⊔ T) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p := by
  intro q hq hqB
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hT
  have hle : Nat.card (P ⊔ T : Subgroup G) ≤ Nat.card P * Nat.card T := by
    let f : P × T → (P ⊔ T : Subgroup G) := fun ys =>
      ⟨(ys.1 : G) * ys.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left ys.1.2)
        (Subgroup.mem_sup_right ys.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨y, hy, s, hs, rfl⟩ := P134.exists_mul_of_mem_sup hmul hg
      exact ⟨(⟨y, hy⟩, ⟨s, hs⟩), rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at this
  have hcop : Nat.Coprime (Nat.card P) (Nat.card T) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  have h1 : Nat.card P ∣ Nat.card (P ⊔ T : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card T ∣ Nat.card (P ⊔ T : Subgroup G) := Subgroup.card_dvd_of_le le_sup_right
  have hdvd : Nat.card P * Nat.card T ∣ Nat.card (P ⊔ T : Subgroup G) :=
    hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have heq : Nat.card (P ⊔ T : Subgroup G) = Nat.card P * Nat.card T :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have hq' : q ∣ p ^ a * 2 ^ b := by
    rw [← ha, ← hb, ← heq]
    exact hqB.trans (Subgroup.card_dvd_of_le hB)
  rcases (Nat.Prime.dvd_mul hq).1 hq' with h | h
  · right
    exact (Nat.prime_dvd_prime_iff_eq hq Fact.out).1 (hq.dvd_of_dvd_pow h)
  · left
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)

theorem false_of_card_sixty {p : ℕ} [Fact p.Prime] (hp : p = 5) {Mc T L P : Subgroup G}
    (hsyl : IsSylowTwoOf T Mc) (hL : L ∈ cComp Mc)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hPp : IsPGroup p P) (hPL : P ⊓ L ≠ ⊥)
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60)
    (hno3 : ∀ A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), A.index ≠ 3) : False := by
  have hp2 : p ≠ 2 := by rw [hp]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsSylowTwoOf (T ⊓ L) L :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hL) hsyl
  let π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let B : Subgroup G := (P ⊔ T) ⊓ L
  let B' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (B.subgroupOf L).map π
  let U' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := ((T ⊓ L).subgroupOf L).map π
  let P' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := ((P ⊓ L).subgroupOf L).map π
  have hTLB : T ⊓ L ≤ B := inf_le_inf_right L le_sup_right
  have hPLB : P ⊓ L ≤ B := inf_le_inf_right L le_sup_left
  have hUB : U' ≤ B' := Subgroup.map_mono (Subgroup.comap_mono hTLB)
  have hPB : P' ≤ B' := Subgroup.map_mono (Subgroup.comap_mono hPLB)
  have hBcard : Nat.card (B.subgroupOf L) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ≤ L)).toEquiv
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card B' → q = 2 ∨ q = p := by
    intro q hq hqB'
    have h1 : q ∣ Nat.card B := hBcard ▸ hqB'.trans (Subgroup.card_map_dvd _ π)
    exact prime_dvd_of_le_sup_gen hp2 hPp hsyl.2.1 hmul (inf_le_left : B ≤ P ⊔ T) q hq h1
  have hUtop : IsSylowTwoOf ((T ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) := by
    rw [A312.isSylowTwoOf_top_iff_map]
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hU'syl : IsSylowTwoOf U' (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    A312.isSylowTwoOf_top_map π hπs hUtop
  have hU'card : Nat.card U' = 4 := by
    rw [hU'syl.card_eq, twoPart, Subgroup.card_top, hcard]
    have : Nat.factorization 60 2 = 2 := by
      rw [Nat.factorization_def 60 Nat.prime_two]
      decide +kernel
    rw [this]
    norm_num
  have hPLp : IsPGroup p ↥(P ⊓ L) := hPp.to_le inf_le_left
  have hPLp' : IsPGroup p ↥((P ⊓ L).subgroupOf L) :=
    hPLp.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ L ≤ L)).symm
  have hP'p : IsPGroup p P' := hPLp'.map π
  have hP'ne : P' ≠ ⊥ := by
    intro hbot
    apply hPL
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hx.2
    have hmem : π ⟨x, hxL⟩ ∈ P' := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hmem
    have hx2 : x ∈ pCoreOf 2 L := by
      have hx' : (⟨x, hxL⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L := by
        assumption
      exact ⟨⟨x, hxL⟩, hx', rfl⟩
    have hdis := IsPGroup.disjoint_of_ne p 2 hp2 P (pCoreOf 2 L) hPp (pCoreOf_isPGroup 2 L)
    have hxx : x ∈ P ⊓ pCoreOf 2 L := ⟨hx.1, hx2⟩
    rwa [hdis.eq_bot] at hxx
  have h5 : 5 ∣ Nat.card P' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP'p
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hP'ne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn, hp]
    exact dvd_pow_self 5 hn0
  have h5B : 5 ∣ Nat.card B' := h5.trans (Subgroup.card_dvd_of_le hPB)
  have h4B : 4 ∣ Nat.card B' := hU'card ▸ Subgroup.card_dvd_of_le hUB
  have h20 : 20 ∣ Nat.card B' := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4B h5B
  have h60 : Nat.card B' ∣ 60 := hcard ▸ Subgroup.card_subgroup_dvd_card B'
  have h3 : ¬ 3 ∣ Nat.card B' := by
    intro h
    rcases hprime 3 Nat.prime_three h with h' | h'
    · omega
    · omega
  have h20' : Nat.card B' = 20 := by
    obtain ⟨k, hk⟩ := h20
    have hk60 : 20 * k ∣ 60 := hk ▸ h60
    have hk3 : k ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) hk60
      omega
    interval_cases k
    · omega
    · omega
    · omega
    · exact absurd (hk ▸ (by norm_num : 3 ∣ 20 * 3)) h3
  apply hno3 B'
  have hidx := Subgroup.index_mul_card B'
  rw [h20', hcard] at hidx
  omega

end CFSG.Quasithin.S146zX
