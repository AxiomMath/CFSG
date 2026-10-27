module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuGrp
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocV

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits U42F431
open scoped Pointwise

@[expose] def chkKer : Bool := (List.range 64).all fun j =>
  !fixL0 (comp (Tl.getD j []) c3L) && !fixL0 (comp (Tl.getD j []) (comp c3L c3L))

theorem chkKer_true : chkKer = true := by decide +kernel

theorem mem_L0S_iff (p : Fin 45) : p ∈ L0S ↔ p = 0 ∨ p = 15 ∨ p = 16 ∨ p = 20 ∨ p = 24 := by
  have h : p ∈ L0S ↔ p ∈ ({0, 15, 16, 20, 24} : Finset (Fin 45)) := by rw [L0S_eq]; simp
  rw [h]
  simp

theorem B0_eq_sup :
    T ⊔ Subgroup.zpowers c3Y = B0 :=
  Subgroup.eq_of_le_of_card_ge K_le_B0 (by rw [card_B0]; exact card_K_ge)

theorem B0_elem {b : Y}
    (hb : b ∈ B0) : ∃ t ∈ T, ∃ k < 3, b = t * c3Y ^ k := by
  have hle : Subgroup.zpowers c3Y ≤ Subgroup.normalizer (T : Set Y) :=
    (Subgroup.zpowers_le).2 c3_mem_normalizer
  have h := Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers c3Y) hle
  rw [B0_eq_sup] at h
  have hb' : b ∈ ((T : Set Y) * (Subgroup.zpowers c3Y : Set Y)) := by rw [← h]; exact hb
  obtain ⟨t, ht, c, hc, rfl⟩ := hb'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  refine ⟨t, ht, (n % 3).toNat, ?_, ?_⟩
  · omega
  · have h3 : c3Y ^ (3 : ℤ) = 1 := by
      have := c3_pow_three
      simpa using this
    have h1 : c3Y ^ n = c3Y ^ (n % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
      rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
    have h2 : (n % 3).toNat = n % 3 := by omega
    rw [h1, ← zpow_natCast]
    congr 2
    omega

theorem fix_mem_Vsub {g : Y}
    (hg : ∀ p : Fin 45, p ∈ L0S → (g : P45) p = p) : g ∈ Vsub := by
  have hgB : g ∈ B0 := by
    rw [mem_B0_iff]
    refine ⟨hg 0 zero_mem_L0S, ?_⟩
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hg p hp]
      exact hp
    · intro hq
      exact ⟨q, hq, hg q hq⟩
  obtain ⟨t, ht, k, hk, rfl⟩ := B0_elem hgB
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · simp only [pow_zero, mul_one] at hg ⊢
    exact mem_Vsub_of_fix ht hg
  · exfalso
    obtain ⟨j, hj, hrep⟩ := (mem_T_iff t).1 ht
    have hr := repL_mul hrep repL_c3
    have hf : fixL0 (comp (Tl.getD j []) c3L) = true := by
      refine (fixL0_iff (by simpa [compL, comp] using hr)).2 ?_
      intro p hp
      simpa using hg p hp
    have h := chkKer_true
    simp only [chkKer, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [(h j hj).1] at hf
    exact absurd hf (by simp)
  · exfalso
    obtain ⟨j, hj, hrep⟩ := (mem_T_iff t).1 ht
    have hr := repL_mul hrep (repL_mul repL_c3 repL_c3)
    have hf : fixL0 (comp (Tl.getD j []) (comp c3L c3L)) = true := by
      refine (fixL0_iff (by simpa [compL, comp] using hr)).2 ?_
      intro p hp
      have := hg p hp
      simpa [pow_two] using this
    have h := chkKer_true
    simp only [chkKer, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [(h j hj).2] at hf
    exact absurd hf (by simp)

theorem pCoreOf_P2_fix {q : Y} (hq : q ∈ pCoreOf 2 P2)
    {u : Fin 45} (hu : u ∈ L0S) : (q : P45) u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ((pCoreOf 2 P2).subgroupOf P2) :=
    IsPGroup.of_equiv (pCoreOf_isPGroup 2 P2) (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 P2)).symm
  have hnorm : ((pCoreOf 2 P2).subgroupOf P2).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 P2)).2 (le_normalizer_pCoreOf 2 P2)
  have hd : ¬ 2 ∣ Nat.card (MulAction.orbit ↥P2 (0 : Fin 45)) := by
    rw [Nat.card_coe_set_eq, orbit_P2, L0S_ncard]
    norm_num
  have huo : u ∈ MulAction.orbit ↥P2 (0 : Fin 45) := by
    rw [orbit_P2]
    exact hu
  have hfin : Finite (MulAction.orbit ↥P2 (0 : Fin 45)) :=
    (Set.finite_range (fun g : ↥P2 => g • (0 : Fin 45))).to_subtype
  have := CFSG.Quasithin.H13.F45Ru.normal_pgroup_fixes
    (Ω := MulAction.orbit ↥P2 (0 : Fin 45)) ((pCoreOf 2 P2).subgroupOf P2) hpg hd
    ⟨q, pCoreOf_le 2 P2 hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨u, huo⟩
  exact congrArg Subtype.val this

theorem pCoreOf_P2 :
    pCoreOf 2 P2 = Vsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro q hq
    exact fix_mem_Vsub fun p hp => pCoreOf_P2_fix hq hp
  · refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ Vsub_isPGroup
    · exact (Vsub_le_T).trans (T_le_B0.trans B0_le_P2)
    · exact normalizer_V.symm.le

end CFSG.Quasithin.H13.F431.U42
