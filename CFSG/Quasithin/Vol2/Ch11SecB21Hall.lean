module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_hall {X B P : Subgroup G} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B X) (hPX : P ≤ X) (hP : IsPGroup p P) :
    ∃ x ∈ X, P ≤ conjSub x B := by
  obtain ⟨S, hS, -⟩ := exists_isSylowIn_ge p (bot_le : (⊥ : Subgroup G) ≤ B)
    IsPGroup.of_bot
  have hSX : IsSylowIn p S X := by
    refine ⟨hS.le.trans hB.1, hS.isPGroup, fun hd => ?_⟩
    obtain ⟨k, hk⟩ := hB.2.2
    rw [← Subgroup.relIndex_mul_relIndex S B X hS.le hB.1, hk] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
    · exact hS.not_dvd_relIndex h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
        (hp.out.dvd_of_dvd_pow h))
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowIn_ge p hPX hP
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥X hSX.toSylow hS'.toSylow
  refine ⟨(x : G), x.2, hPS'.trans ?_⟩
  have h1 : ((x • hSX.toSylow : Sylow p ↥X) : Subgroup ↥X) = (hS'.toSylow : Subgroup ↥X) := by
    rw [hx]
  rw [Sylow.coe_subgroup_smul, IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow] at h1
  intro y hy
  have hy' : (⟨y, hS'.le hy⟩ : ↥X) ∈ S'.subgroupOf X := hy
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  have hy'' := (Subgroup.mem_subgroupOf.mp hy')
  rw [mem_conjSub]
  have : (x : G)⁻¹ * y * (x : G) ∈ S := by simpa [MulAut.conj_apply] using hy''
  exact hS.le this

theorem isPGroup_inf_centralizer_of_hall {X B V : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B X)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hBV : B ⊓ Subgroup.centralizer (V : Set G) = ⊥) :
    IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) := by
  have key : ∀ c ∈ X ⊓ Subgroup.centralizer (V : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf c = p → False := by
    intro c hc p hp hp2 hcp
    have : Fact p.Prime := ⟨hp⟩
    have hP : IsPGroup p (Subgroup.zpowers c) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hcp, pow_one]
    obtain ⟨x, hx, hle⟩ := exists_conj_le_hall hp2 hB
      (Subgroup.zpowers_le.mpr hc.1) hP
    have hc' := hle (Subgroup.mem_zpowers c)
    rw [mem_conjSub] at hc'
    have hxV : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem (hXV hx)
    have hcC : x⁻¹ * c * x ∈ Subgroup.centralizer (V : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (B2F.le_normalizer_centralizer (le_refl _) hxV) c).mp hc.2
      simpa using this
    have h1 : x⁻¹ * c * x = 1 := by
      have : x⁻¹ * c * x ∈ B ⊓ Subgroup.centralizer (V : Set G) := ⟨hc', hcC⟩
      rw [hBV, Subgroup.mem_bot] at this
      exact this
    have hc1 : c = 1 := by
      have : c = x * (x⁻¹ * c * x) * x⁻¹ := by group
      rw [this, h1]; group
    rw [hc1, orderOf_one] at hcp
    exact hp.one_lt.ne hcp
  have hodd : ∀ c ∈ X ⊓ Subgroup.centralizer (V : Set G), Odd (orderOf c) → c = 1 := by
    intro c hc hco
    by_contra hne
    have h1 : orderOf c ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hco) (even_iff_two_dvd.mpr hpd)
    have hmem : c ^ (orderOf c / p) ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hc _
    refine key _ hmem p hp hp2 ?_
    rw [orderOf_pow' c (Nat.div_ne_zero_iff_of_dvd hpd |>.mpr
      ⟨(orderOf_pos c).ne', hp.ne_zero⟩), Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpd),
      Nat.div_div_self hpd (orderOf_pos c).ne']
  intro c
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : G)).ne'
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  refine hodd _ ((X ⊓ Subgroup.centralizer (V : Set G)).pow_mem c.2 _) ?_
  rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hkm, Nat.gcd_mul_right_left]
  simpa [hkm, Nat.mul_div_cancel_left _ (pow_pos two_pos k)] using hm

omit [Finite G] in
theorem mul_comm_sylow_of_normalizes {X Q T B A : Subgroup G} (hQX : X ≤
    Subgroup.normalizer (Q : Set G)) (hQT : Q ≤ T) (hTX : T ≤ X) (hAX : A ≤ X)
    (hT : T ≤ Q ⊔ (T ⊓ Subgroup.normalizer (B : Set G)))
    (hA : T ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) := by
  set N := T ⊓ Subgroup.normalizer (B : Set G)
  have hTeq : (T : Set G) = (Q : Set G) * (N : Set G) := by
    have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := inf_le_left.trans (hTX.trans hQX)
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q N hNQ]
    exact congrArg _ (le_antisymm hT (sup_le hQT inf_le_left))
  have hAQ : (A : Set G) * (Q : Set G) = (Q : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q (hAX.trans hQX),
      ← Subgroup.coe_mul_of_right_le_normalizer_left Q A (hAX.trans hQX), sup_comm]
  have hAN : (A : Set G) * (N : Set G) = (N : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A N hA,
      ← Subgroup.coe_mul_of_left_le_normalizer_right N A hA, sup_comm]
  rw [hTeq, ← mul_assoc, hAQ, mul_assoc, hAN, ← mul_assoc]

end CFSG.Quasithin.Vol2.Ch11.SecB
