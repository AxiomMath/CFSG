module

public import CFSG.Quasithin.Background.F918Z4bDef
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem rk_le_of_isElemAb2_suzukiGroup {a : ℕ} {K : Type}
    [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {E : Subgroup (suzukiGroup a K)} (hE : IsElemAb2 E) : rk E ≤ 2 * (2 * a + 1) - 1 := by
  classical
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hS : rk (suzukiGroup a K) = 2 * (2 * a + 1) := by
    unfold rk
    rw [suzuki_order hK]
    have h2 : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
    have hq : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have h1 : ¬ 2 ∣ 2 ^ (2 * a + 1) - 1 := by omega
    have h3 : ¬ 2 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      have : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow hq two_ne_zero
      omega
    have h4 : (2 ^ (2 * a + 1)) ^ 2 ≠ 0 := by positivity
    have h5 : 2 ^ (2 * a + 1) - 1 ≠ 0 := by omega
    have h6 : (2 ^ (2 * a + 1)) ^ 2 + 1 ≠ 0 := by omega
    rw [padicValNat.mul (mul_ne_zero h4 h5) h6, padicValNat.mul h4 h5,
      padicValNat.pow, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h3]
    ring
  have hU2 : IsPGroup 2 (suzukiU a K) :=
    IsPGroup.of_card (n := 2 * (2 * a + 1)) (by
      rw [(suzuki_unipotent_structure hK).2.1, ← pow_mul, mul_comm])
  obtain ⟨Q₀, hQ₀⟩ := hU2.exists_le_sylow
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  have hy : suzukiSElt a K 1 0 ∈ (Q₀ : Subgroup (suzukiGroup a K)) :=
    hQ₀ ((mem_suzukiU_iff hK).2 ⟨1, 0, rfl⟩)
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2 * a + 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have hy2 : suzukiSElt a K 1 0 ^ 2 ≠ 1 := by
    intro h
    rw [sq, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h
    simp at h
  obtain ⟨z, hzQ, hz2⟩ : ∃ z ∈ (Q : Subgroup (suzukiGroup a K)), z ^ 2 ≠ 1 := by
    refine ⟨(Sylow.equiv Q₀ Q ⟨_, hy⟩ : suzukiGroup a K), (Sylow.equiv Q₀ Q ⟨_, hy⟩).2, ?_⟩
    intro h
    apply hy2
    have h' : Sylow.equiv Q₀ Q ((⟨_, hy⟩ : Q₀) ^ 2) = 1 := by
      rw [map_pow]
      exact Subtype.ext h
    have := (Sylow.equiv Q₀ Q).map_eq_one_iff.mp h'
    simpa using congrArg Subtype.val this
  have hlt : Nat.card E < Nat.card (Q : Subgroup (suzukiGroup a K)) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hEQ) fun h => ?_
    have heq : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (le_of_eq h.symm)
    exact hz2 (hE.2 z (heq ▸ hzQ))
  have hQ2 : IsPGroup 2 (Q : Subgroup (suzukiGroup a K)) := Q.isPGroup'
  rw [hE.card_eq_two_pow, card_eq_two_pow_of_isPGroup hQ2] at hlt
  have hrk : rk E < rk (Q : Subgroup (suzukiGroup a K)) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hQS : rk (Q : Subgroup (suzukiGroup a K)) ≤ rk (suzukiGroup a K) := by
    have := rk_mono (le_top : (Q : Subgroup (suzukiGroup a K)) ≤ ⊤)
    rwa [rk_top] at this
  omega

theorem suzuki_conj_injective_of_isSimple {a : ℕ} {K : Type}
    [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center (suzukiGroup a K) := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun α : MulAut (suzukiGroup a K) => α y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  have hcenter : Subgroup.center (suzukiGroup a K) = ⊥ := by
    obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with
      h | h
    · exact h
    · have h1 := (suzuki_perfect ha hK).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  rw [hcenter, Subgroup.mem_bot] at hgZ
  exact hgZ

theorem autRankLe_suzukiGroup {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    AutRankLe (suzukiGroup a K) (2 * (2 * a + 1) - 1) := by
  classical
  intro E hE
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hOut : Nat.card (Outer (suzukiGroup a K)) ∣ 2 * a + 1 :=
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2
  have hinner : E ≤ (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range := by
    intro α hα
    let x : Outer (suzukiGroup a K) := QuotientGroup.mk' (inner (suzukiGroup a K)) α
    have h1 : x ^ 2 = 1 := by
      rw [← map_pow, hE.2 α hα, map_one]
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf x ∣ 2 * a + 1 := (orderOf_dvd_natCard _).trans hOut
    have h4 : orderOf x = 1 := by
      have h5 := Nat.dvd_gcd h2 h3
      have h6 : Nat.gcd 2 (2 * a + 1) = 1 := Nat.coprime_two_left.mpr (odd_two_mul_add_one a)
      rwa [h6, Nat.dvd_one] at h5
    exact (QuotientGroup.eq_one_iff (N := inner (suzukiGroup a K)) α).mp (orderOf_eq_one_iff.mp h4)
  have hinj := suzuki_conj_injective_of_isSimple ha hK
  rw [← rk_comap_eq_of_le_range _ hinj hinner]
  exact rk_le_of_isElemAb2_suzukiGroup ha hK (hE.comap _ hinj)

theorem autRankLe_sz {L : Type} [Group L] [Finite L] {n : ℕ}
    (hn : 3 ≤ n) (h : IsSz n L) : AutRankLe L (2 * n - 1) := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hna, hK, ⟨e⟩⟩ := h
  subst hna
  exact AutRankLe.of_mulEquiv e (autRankLe_suzukiGroup ha hK)

end CFSG.Quasithin
