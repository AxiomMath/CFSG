module

public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

theorem false_of_cyclic_four {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : ∃ w, Odd w ∧ Nat.card K = 2 ^ 2 * w) {C : Subgroup K} (hC : Nat.card C = 4)
    (hcyc : IsCyclic C) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw, hKw⟩ := hK
  have hCp : IsPGroup 2 C := IsPGroup.of_card (n := 2) (by rw [hC]; norm_num)
  obtain ⟨S, hCS⟩ := hCp.exists_le_sylow
  have hSle : Nat.card S ≤ 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 S.isPGroup'
    have hdvd : 2 ^ n ∣ 2 ^ 2 * w := hKw ▸ hn ▸ Subgroup.card_subgroup_dvd_card (S : Subgroup K)
    have hcop : Nat.Coprime (2 ^ n) w := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hw)
    have h4 : 2 ^ n ∣ 2 ^ 2 := hcop.dvd_of_dvd_mul_right hdvd
    rw [hn]
    exact Nat.le_of_dvd (by norm_num) h4
  have hCS' : C = (S : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hCS (by rw [hC]; exact hSle)
  subst hCS'
  have : Fintype K := Fintype.ofFinite K
  have hG : Even (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, hKw]
    exact ⟨2 * w, by ring⟩
  obtain ⟨-, -, hn, hidx⟩ := CFSG.LinearGroups.cyclic_sylow_index_two hG S hcyc
  have key : ∀ N : Subgroup K, N.Normal → N.index = 2 → False := by
    intro N hN hNi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h, Subgroup.index_bot] at hNi
      have hw1 : 1 ≤ w := hw.pos
      omega
    · rw [h, Subgroup.index_top] at hNi
      exact absurd hNi (by norm_num)
  exact key _ hn hidx

theorem four_le_card_inf_centralizer {D : Type} [Group D] [Finite D] {Z T : Subgroup D}
    [Z.Normal] (hZ : Nat.card Z = 3) (hT : Nat.card T = 8) :
    4 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer (Z : Set D)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic Z := isCyclic_of_prime_card hZ
  let φ : T →* MulAut Z := (MulAut.conjNormal : D →* MulAut Z).comp T.subtype
  have hker : φ.ker = (T ⊓ Subgroup.centralizer (Z : Set D)).subgroupOf T := by
    ext t
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro h
      refine ⟨t.2, fun z hz => ?_⟩
      have := congrArg (fun σ : MulAut Z => (σ ⟨z, hz⟩ : D)) h
      simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun z => Subtype.ext ?_
      simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h z z.2).symm
  have h1 : Nat.card φ.ker * φ.ker.index = Nat.card T := Subgroup.card_mul_index _
  have h2 : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have h3 : Nat.card φ.range ≤ 2 := by
    calc Nat.card φ.range ≤ Nat.card (MulAut Z) := Subgroup.card_le_card_group _
      _ = 2 := by rw [IsCyclic.card_mulAut, hZ, Nat.totient_prime Nat.prime_three]
  have h4 : Nat.card ↥(φ.ker) = Nat.card ↥(T ⊓ Subgroup.centralizer (Z : Set D)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h4]
  rw [h2, hT] at h1
  by_contra hlt
  have : Nat.card φ.ker ≤ 3 := by omega
  nlinarith [Nat.card_pos (α := φ.range)]

theorem false_of_cyclic_kernel {D : Type} [Group D] [Finite D] {K Z T : Subgroup D} [Z.Normal]
    (hZ : Nat.card Z = 3) (hT : Nat.card T = 8)
    (hTK : ∀ t ∈ T, (∀ z ∈ Z, z * t = t * z) → t ∈ K) [IsSimpleGroup ↥K]
    (hK : ∃ w, Odd w ∧ Nat.card ↥K = 2 ^ 2 * w)
    (hcyc : IsCyclic ↥(T ⊓ Subgroup.centralizer (Z : Set D))) : False := by
  set C := T ⊓ Subgroup.centralizer (Z : Set D) with hCdef
  have h4 : 4 ≤ Nat.card C := four_le_card_inf_centralizer hZ hT
  have hCK : C ≤ K := fun t ht => hTK t ht.1 fun z hz => Subgroup.mem_centralizer_iff.mp ht.2 z hz
  obtain ⟨w, hw, hKw⟩ := hK
  have hCT : Nat.card C ∣ 8 := hT ▸ Subgroup.card_dvd_of_le inf_le_left
  have hCK' : Nat.card C ∣ 2 ^ 2 * w := hKw ▸ Subgroup.card_dvd_of_le hCK
  have hC4 : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hCT
    have hcases : Nat.card C = 4 ∨ Nat.card C = 8 := by
      interval_cases h : Nat.card C <;> omega
    rcases hcases with h | h
    · exact h
    · exfalso
      rw [h] at hCK'
      obtain ⟨a, ha⟩ := hw
      omega
  refine false_of_cyclic_four ⟨w, hw, hKw⟩ (C := C.subgroupOf K) ?_ ?_
  · rw [← hC4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv
  · exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hCK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hCK).injective

theorem dih12_exists_r_of_comm : ∀ a x : DihedralGroup 12, a ^ 3 = 1 → a ≠ 1 → x * a = a * x →
    ∃ i : ZMod 12, x = DihedralGroup.r i := by decide

theorem dih12_mem_zpowers_of_comm {a x : DihedralGroup 12} (ha : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hx : x * a = a * x) : x ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 12) := by
  obtain ⟨i, rfl⟩ := dih12_exists_r_of_comm a x ha ha1 hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
  rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]

theorem perm4_two_cycles : ∃ c₁ c₂ : Equiv.Perm (Fin 4), c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧
    c₂ ≠ 1 ∧ c₂ ≠ c₁ ∧ c₂ ≠ c₁ ^ 2 := by decide

variable {D : Type} [Group D] [Finite D]

theorem mem_of_pow_three_of_twoResidual_le {X Z : Subgroup D} (h : twoResidual X ≤ Z) {x : D}
    (hx : x ∈ X) (hx3 : x ^ 3 = 1) : x ∈ Z := by
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X x hx
  have hk' : x ^ 2 ^ k ∈ Z := h hk
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  obtain ⟨q, hq⟩ : ∃ q, 4 ^ k = 3 * q + 1 := ⟨4 ^ k / 3, by omega⟩
  have : x = (x ^ 2 ^ k) ^ 2 ^ k := by
    rw [← pow_mul, show (2 : ℕ) ^ k * 2 ^ k = 4 ^ k by rw [← mul_pow]; norm_num, hq, pow_succ,
      pow_mul, hx3, one_pow, one_mul]
  rw [this]
  exact Z.pow_mem hk' _

theorem not_twoResidual_le_of_perm {X Z : Subgroup D} (hZ3 : Nat.card Z = 3)
    (e : ↥X ≃* Equiv.Perm (Fin 4)) : ¬ twoResidual X ≤ Z := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c₁, c₂, h1, h2, h1', h2', h21, h22⟩ := perm4_two_cycles
  have key : ∀ c : Equiv.Perm (Fin 4), c ^ 3 = 1 → ((e.symm c : ↥X) : D) ∈ Z := by
    intro c hc
    refine mem_of_pow_three_of_twoResidual_le h (e.symm c).2 ?_
    rw [← Subgroup.coe_pow, ← map_pow, hc, map_one]
    rfl
  have hg1 : (e.symm c₁ : D) ≠ 1 := by
    intro h'
    apply h1'
    have : e.symm c₁ = 1 := Subtype.ext h'
    simpa using congrArg e this
  have htop : Subgroup.zpowers (⟨(e.symm c₁ : D), key c₁ h1⟩ : ↥Z) = ⊤ :=
    zpowers_eq_top_of_prime_card hZ3 (fun h' => hg1 (by simpa using congrArg Subtype.val h'))
  have hmem : (⟨(e.symm c₂ : D), key c₂ h2⟩ : ↥Z) ∈
      Subgroup.zpowers (⟨(e.symm c₁ : D), key c₁ h1⟩ : ↥Z) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm' : (e.symm c₁ : ↥X) ^ m = e.symm c₂ :=
    Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hm'' : c₁ ^ m = c₂ := by
    simpa using congrArg e hm'
  have h3 : c₁ ^ 3 = 1 := h1
  have hmod : c₁ ^ m = c₁ ^ (m % 3) := by
    conv_lhs =>
      rw [← Int.emod_add_mul_ediv m 3, zpow_add, zpow_mul, zpow_ofNat, h3, one_zpow, mul_one]
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · apply h2'
    rw [← hm'', hmod, hr]; rfl
  · apply h21
    rw [← hm'', hmod, hr]; simp
  · apply h22
    rw [← hm'', hmod, hr]; simp

end Struct

end Gold14610

end CFSG.Quasithin
