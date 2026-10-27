module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {H : Type} [Group H]

theorem pCoreOf_le_of_normal_in [Finite H] {N K : Subgroup H} (hNK : N ≤ K)
    (hn : (N.subgroupOf K).Normal) : pCoreOf 2 N ≤ pCoreOf 2 K := by
  have hK : K ≤ Subgroup.normalizer (N : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hn
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 N).trans hNK)
    (hK.trans (normalizer_le_normalizer_pCoreOf 2 N)) (pCoreOf_isPGroup 2 N)

theorem comm_eq_of_commutator_eq_top (K : Subgroup H) (h : commutator ↥K = ⊤) : ⁅K, K⁆ = K := by
  have h1 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h1, h, Subgroup.map_top, Subgroup.range_subtype]

theorem subgroupOf_map_subtype_eq (K : Subgroup H) (M : Subgroup ↥K) :
    (M.map K.subtype).subgroupOf K = M := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_of_two_pow_of_quotient_odd_prime {G : Type} [Group G] (M : Subgroup G) [M.Normal]
    {y : G} {n : ℕ} (hy : y ^ 2 ^ n = 1) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (hcard : Nat.card (G ⧸ M) = p) : y ∈ M := by
  have h1 : ((y : G ⧸ M)) ^ 2 ^ n = 1 := by rw [← QuotientGroup.mk_pow, hy]; rfl
  have h2 : ((y : G ⧸ M)) ^ p = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hcop : Nat.Coprime p (2 ^ n) := by
    apply Nat.Coprime.pow_right
    rcases hp with rfl | rfl <;> norm_num
  have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rw [hcop] at h3
  exact (QuotientGroup.eq_one_iff y).mp (by simpa using h3)

variable [Finite H]

theorem hsru_perfect {P K : Subgroup H} (hPK : P ≤ K) (hP2 : IsPGroup 2 ↥P)
    (hcard : Nat.card K = 21 * Nat.card P) (hO2 : Nat.card (pCoreOf 2 K) * 8 = Nat.card P)
    (hrows : ∀ N : Subgroup H, P ≤ N → N ≤ K → N ≠ K → Nat.card N = Nat.card P ∨
      (Nat.card N = 3 * Nat.card P ∧ Nat.card (pCoreOf 2 N) * 2 = Nat.card P))
    (hodd : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → Nat.card (↥K ⧸ N) ≤ 1) :
    ⁅K, K⁆ = K := by
  classical
  refine comm_eq_of_commutator_eq_top K ?_
  by_contra hne
  obtain ⟨M, hM, hDM⟩ := (eq_top_or_exists_le_coatom (commutator ↥K)).resolve_left hne
  have hMn : M.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : ⁅g, x⁆ ∈ M := hDM (Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top x))
    have : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact M.mul_mem h1 hx
  have hsimple : IsSimpleGroup (↥K ⧸ M) := Group.isSimpleGroup_of_isCoatom hM
  have hcomm : IsMulCommutative (↥K ⧸ M) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    induction a using QuotientGroup.induction_on with | _ x
    induction b using QuotientGroup.induction_on with | _ y
    have h1 : ⁅x, y⁆ ∈ M := hDM (Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top y))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact hDM (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hp : (Nat.card (↥K ⧸ M)).Prime := Group.is_simple_iff_prime_card.mp hsimple
  obtain ⟨a, ha⟩ := hP2.exists_card_eq
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hKM : Nat.card ↥K = Nat.card (↥K ⧸ M) * Nat.card M :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hdvd : Nat.card (↥K ⧸ M) ∣ 3 * 7 * 2 ^ a := by
    rw [mul_assoc, ← ha, show (3 * (7 * Nat.card P)) = 21 * Nat.card P by ring, ← hcard]
    exact Subgroup.card_quotient_dvd_card M
  have hcases : Nat.card (↥K ⧸ M) = 2 ∨ Nat.card (↥K ⧸ M) = 3 ∨ Nat.card (↥K ⧸ M) = 7 := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hodd37 : Nat.card (↥K ⧸ M) = 3 ∨ Nat.card (↥K ⧸ M) = 7 → False := by
    intro hp37
    set Mh : Subgroup H := M.map K.subtype with hMh
    have hMhK : Mh ≤ K := Subgroup.map_subtype_le M
    have hMhcard : Nat.card Mh = Nat.card M := Subgroup.card_map_of_injective K.subtype_injective
    have hMhn : (Mh.subgroupOf K).Normal := by
      rw [hMh, subgroupOf_map_subtype_eq]
      exact hMn
    have hPMh : P ≤ Mh := by
      intro x hx
      obtain ⟨n, hn⟩ := hP2 ⟨x, hx⟩
      have hxn : x ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hy : (⟨x, hPK hx⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext hxn
      exact ⟨⟨x, hPK hx⟩, mem_of_two_pow_of_quotient_odd_prime M hy hp37 rfl, rfl⟩
    have hMpos : 0 < Nat.card M := Nat.card_pos
    have hne' : Mh ≠ K := by
      intro h
      have h1 : Nat.card M = Nat.card K := by rw [← hMhcard, h]
      rcases hp37 with h3 | h7
      · rw [h3] at hKM; omega
      · rw [h7] at hKM; omega
    have hr := hrows Mh hPMh hMhK hne'
    have hle : Nat.card (pCoreOf 2 Mh) ≤ Nat.card (pCoreOf 2 K) :=
      Subgroup.card_le_of_le (pCoreOf_le_of_normal_in hMhK hMhn)
    rcases hp37 with h3 | h7
    · rw [h3] at hKM
      rw [hMhcard] at hr
      omega
    · rw [h7] at hKM
      rw [hMhcard] at hr
      omega
  rcases hcases with h2 | h3 | h7
  · have h2g : IsPGroup 2 (↥K ⧸ M) := IsPGroup.of_card (n := 1) (by rw [h2]; simp)
    have := hodd M h2g
    omega
  · exact (hodd37 (Or.inl h3)).elim
  · exact (hodd37 (Or.inr h7)).elim

end CFSG.Quasithin.HSRuLoc.Mod
