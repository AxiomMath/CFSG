module

public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.A4Bridge
public import CFSG.Quasithin.Vol2.Ch10SecD33C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_odd_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (ho : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  have hodd := ho
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

theorem quasithinIsLocal_of_mem_cComp {T K Y H : Subgroup G} (hK : K ∈ cComp Y)
    (hKT : K ⊔ T = H) (hHY : H ≤ Y) (hT : IsSylowTwoOf T H) (hH : pCoreOf 2 H ≠ ⊥) :
    quasithinIsLocal T K := by
  subst hKT
  exact ⟨hT.2.1, cComp_mem_of_le hK le_sup_left hHY, hT.2.2, hH⟩

theorem quasithinIsFaithfulLocal_of_isTwoReducedIn {T K Y V : Subgroup G}
    (hloc : quasithinIsLocal T K) (hK : K ∈ cComp Y) (hY : CharTwo Y) (hV : IsTwoReducedIn Y V)
    (hVK : ⁅V, K⁆ ≠ ⊥) : quasithinIsFaithfulLocal T K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := perfect_of_mem_cComp hK
  have hO : K = oTwoUpper K := (C2Nine.oTwoUpper_eq_of_perfect hperf).symm
  have hXf := A4.isXf_of_isTwoReducedIn hY hO (subnormal_of_mem_cComp hK) hV hVK
  refine ⟨hloc, fun N hNK hN hpow => C2Nine.eq_of_perfect_of_pow_mem hperf hNK hN hpow, ?_, ?_⟩
  · exact (quasithinGenFitting_eq_pCoreOf_iff K 2).mpr hXf.1.2.2
  · rw [← VY_eq_quasithinV2]
    exact hXf.2

theorem false_of_le_aut (hAut : FactAutSL) {H Y : Subgroup G} (hHY : H ≤ Y)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) {k : ℕ} (hk : k = 4 ∨ k = 5)
    (e' : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) :
    False := by
  have h1 : 25 ∣ Nat.card ↥H := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
    rw [Nat.card_congr e.toEquiv, card_symFiveWrTwo] at this
    rw [this]
    exact Dvd.dvd.mul_right (by norm_num) _
  have h2 : Nat.card ↥H ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hHY
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
  rw [hn] at h3
  have h4 := h1.trans h2
  rw [h3] at h4
  have h25 := (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 25 2)).dvd_of_dvd_mul_right h4
  rw [Nat.card_congr e'.toEquiv, hAut k hk] at h25
  rcases hk with rfl | rfl
  · rw [Matrix.card_SL_field] at h25
    simp [Fin.prod_univ_four] at h25
  · rw [Matrix.card_SL_field] at h25
    simp [Fin.prod_univ_five] at h25

end CFSG.Quasithin.Vol2.Ch10.SecD
