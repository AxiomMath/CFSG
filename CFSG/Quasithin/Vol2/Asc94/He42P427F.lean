module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.A94.He42

theorem p427_mem_zpowers_involution {X : Type} [Group X] {x y : X} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  rw [← zpow_mod_orderOf, hord]
  push_cast
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem p427_pow_odd_of_involution {X : Type} [Group X] {y : X} (hy : y * y = 1) {d : ℕ}
    (hd : Odd d) : y ^ d = y := by
  obtain ⟨j, rfl⟩ := hd
  rw [pow_succ, pow_mul, sq, hy, one_pow, one_mul]

theorem p427_odd_orderOf_of_mem {X : Type} [Group X] [Finite X] (K : Subgroup X)
    (hK : Odd (Nat.card K)) {x : X} (hx : x ∈ K) : Odd (orderOf x) := by
  have h1 : orderOf (⟨x, hx⟩ : K) = orderOf x := Subgroup.orderOf_mk x hx
  rw [← h1]
  exact Odd.of_dvd_nat hK (orderOf_dvd_natCard _)

theorem p427_zstar_trivial {H : Type} [Group H] [Finite H] (t0 : H) (ht0 : t0 * t0 = 1)
    (ht1 : t0 ≠ 1) (hcent : ∀ h : H, h * t0 = t0 * h) [(Subgroup.zpowers t0).Normal]
    (N : Subgroup (H ⧸ Subgroup.zpowers t0)) [N.Normal] (hNodd : Odd (Nat.card N))
    (hK : ∀ K : Subgroup H, (∀ h : H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → Odd (Nat.card K) → K = ⊥) :
    N = ⊥ := by
  classical
  have ht0ord : orderOf t0 = 2 := orderOf_eq_prime (by rw [sq]; exact ht0) ht1
  have hQcard : Nat.card ↥(Subgroup.zpowers t0) = 2 := by
    rw [Nat.card_zpowers, ht0ord]
  let P : Subgroup H := N.comap (QuotientGroup.mk' (Subgroup.zpowers t0))
  haveI hPnorm : P.Normal := ⟨fun n hn g => by
    show QuotientGroup.mk' (Subgroup.zpowers t0) (g * n * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.Normal.conj_mem inferInstance _ hn _⟩
  have hQP : Subgroup.zpowers t0 ≤ P := by
    intro q hq
    show QuotientGroup.mk' (Subgroup.zpowers t0) q ∈ N
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hq]
    exact N.one_mem
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥N := by
    have h := QuotientGroup.card_preimage_mk (Subgroup.zpowers t0) (N : Set (H ⧸ Subgroup.zpowers t0))
    rw [hQcard] at h
    exact h
  haveI hQ'norm : ((Subgroup.zpowers t0).subgroupOf P).Normal := inferInstance
  have hQ'card : Nat.card ↥((Subgroup.zpowers t0).subgroupOf P) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]
  have hQ'idx : ((Subgroup.zpowers t0).subgroupOf P).index = Nat.card ↥N := by
    have h := Subgroup.index_mul_card (H := (Subgroup.zpowers t0).subgroupOf P)
    rw [hQ'card, hPcard] at h
    omega
  have hcop : Nat.Coprime (Nat.card ↥((Subgroup.zpowers t0).subgroupOf P))
      ((Subgroup.zpowers t0).subgroupOf P).index := by
    rw [hQ'card, hQ'idx]
    exact Nat.coprime_two_left.2 hNodd
  obtain ⟨K, hKc⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have htop : (Subgroup.zpowers t0).subgroupOf P ⊔ K = ⊤ := hKc.sup_eq_top
  have hdisj : Disjoint ((Subgroup.zpowers t0).subgroupOf P) K := hKc.disjoint
  have hKcard : Nat.card ↥K = Nat.card ↥N := by
    have h := hKc.card_mul_card
    rw [hQ'card, hPcard] at h
    omega
  have hodd_mem : ∀ p : ↥P, Odd (orderOf p) → p ∈ K := by
    intro p hp
    have hpmem : p ∈ (Subgroup.zpowers t0).subgroupOf P ⊔ K := by
      rw [htop]
      exact Subgroup.mem_top p
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left).1 hpmem
    have hyQ : (y : H) ∈ Subgroup.zpowers t0 := Subgroup.mem_subgroupOf.1 hy
    rcases p427_mem_zpowers_involution ht0 ht1 hyQ with h1 | h2
    · have hy1 : y = 1 := Subtype.ext h1
      rw [← hyz, hy1, one_mul]
      exact hz
    · exfalso
      have hyy : y * y = 1 := Subtype.ext (by simp [h2, ht0])
      have hcomm : Commute y z := Subtype.ext (by
        show (y : H) * (z : H) = (z : H) * (y : H)
        rw [h2]
        exact (hcent _).symm)
      have hpd : (y * z) ^ orderOf p = 1 := by
        rw [← hyz]
        exact pow_orderOf_eq_one _
      rw [hcomm.mul_pow, p427_pow_odd_of_involution hyy hp] at hpd
      have hzd : z ^ orderOf p = y := by
        calc z ^ orderOf p = y⁻¹ * (y * z ^ orderOf p) := by group
          _ = y⁻¹ := by rw [hpd, mul_one]
          _ = y := inv_eq_of_mul_eq_one_right hyy
      have hyK : y ∈ K := by
        rw [← hzd]
        exact K.pow_mem hz _
      have hyb : y ∈ (⊥ : Subgroup ↥P) := by
        rw [← disjoint_iff.1 hdisj]
        exact Subgroup.mem_inf.2 ⟨hy, hyK⟩
      have hy1 : y = 1 := Subgroup.mem_bot.1 hyb
      apply ht1
      have := congrArg Subtype.val hy1
      simpa [h2] using this
  have hKodd : Odd (Nat.card ↥K) := by rw [hKcard]; exact hNodd
  let KH : Subgroup H := K.map P.subtype
  have hKHcard : Nat.card ↥KH = Nat.card ↥N := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hKcard]
  have hKHnorm : ∀ h : H, ∀ k ∈ KH, h * k * h⁻¹ ∈ KH := by
    intro h k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
    have hconjP : h * (k' : H) * h⁻¹ ∈ P := hPnorm.conj_mem _ k'.2 h
    refine Subgroup.mem_map.2 ⟨⟨h * (k' : H) * h⁻¹, hconjP⟩, ?_, rfl⟩
    apply hodd_mem
    have hk'odd : Odd (orderOf k') := p427_odd_orderOf_of_mem K hKodd hk'
    have e1 : orderOf (⟨h * (k' : H) * h⁻¹, hconjP⟩ : ↥P) = orderOf (h * (k' : H) * h⁻¹) :=
      Subgroup.orderOf_mk _ hconjP
    have e2 : orderOf (h * (k' : H) * h⁻¹) = orderOf (k' : H) :=
      orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective (k' : H)
    have e3 : orderOf (k' : H) = orderOf k' := Subgroup.orderOf_coe k'
    rw [e1, e2, e3]
    exact hk'odd
  have hKH_bot : KH = ⊥ := hK KH hKHnorm (by rw [hKHcard]; exact hNodd)
  have hK_bot : K = ⊥ := by
    have h1 : Nat.card ↥K = 1 := by rw [hKcard, ← hKHcard, hKH_bot, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq K h1
  have hQtop : (Subgroup.zpowers t0).subgroupOf P = ⊤ := by
    rw [hK_bot, sup_bot_eq] at htop
    exact htop
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective n
  have hpP : p ∈ P := hn
  have hmem : (⟨p, hpP⟩ : ↥P) ∈ (Subgroup.zpowers t0).subgroupOf P := by
    rw [hQtop]
    exact Subgroup.mem_top _
  have hpQ : p ∈ Subgroup.zpowers t0 := Subgroup.mem_subgroupOf.1 hmem
  exact (QuotientGroup.eq_one_iff _).2 hpQ

end CFSG.Quasithin.A94.He42
