module

public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.Vol2.Ch3E213MOS1

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

omit [Finite F] [Finite K] in
theorem mul_conj_mul_inv (u : MulAut K) (x : K) :
    u * MulAut.conj x * u⁻¹ = MulAut.conj (u x) := by
  ext y
  simp [MulAut.conj_apply]

omit [Finite F] [Finite K] in
theorem conj_mem_centralizer_iff (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (u : MulAut K) (x : K) :
    MulAut.conj x ∈ Subgroup.centralizer ({u} : Set (MulAut K)) ↔ u x = x := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply hinj
    rw [← mul_conj_mul_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    have h1 := mul_conj_mul_inv u x
    rw [h] at h1
    calc MulAut.conj x * u = u * MulAut.conj x * u⁻¹ * u := by rw [h1]
      _ = u * MulAut.conj x := by group

theorem exists_eq_of_card_eq_two {X : Type*} [Group X] {S : Subgroup X} (h2 : Nat.card S = 2) :
    ∃ f₀ ∈ S, orderOf f₀ = 2 ∧ ∀ x ∈ S, x = 1 ∨ x = f₀ := by
  have hne : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨f₀, hf₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hord : orderOf (f₀ : X) = 2 := by
    have hdvd : orderOf (f₀ : X) ∣ 2 := h2 ▸ Subgroup.orderOf_dvd_natCard S f₀.2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun h' => hf₀1 (Subtype.ext h'))
    · exact h
  refine ⟨f₀, f₀.2, hord, fun x hx => ?_⟩
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hz : Subgroup.zpowers (f₀ : X) = S := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr f₀.2)
    rw [h2, Nat.card_zpowers, hord]
  rw [← hz] at hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

omit [Finite K] in
theorem fieldAutSub_le_T (N : L2Notation e) (h2 : Nat.card (fieldAutSub e) = 2) :
    fieldAutSub e ≤ (N.T : Subgroup (MulAut K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 (fieldAutSub e) := IsPGroup.of_card (n := 1) (by rw [h2, pow_one])
  have hsup : IsPGroup 2 ↥(fieldAutSub e ⊔ (N.T : Subgroup (MulAut K))) :=
    hF2.to_sup_of_normal_right' N.T.isPGroup' N.T_inv
  have heq := N.T.is_maximal' hsup le_sup_right
  rw [← heq]
  exact le_sup_left

omit [Finite K] in
theorem mem_innDiag_or {f₀ : MulAut K} (hf₀2 : orderOf f₀ = 2)
    (hF : ∀ x ∈ fieldAutSub e, x = 1 ∨ x = f₀) (x : MulAut K) :
    x ∈ innDiagSub e ∨ x * f₀ ∈ innDiagSub e := by
  have hn := innDiagSub_normal e
  have hFN : fieldAutSub e ≤ Subgroup.normalizer (innDiagSub e : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hn]
    exact le_top
  obtain ⟨d, hd, φ, hφ, rfl⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer' hFN
    ((innDiagSub_sup_fieldAutSub e).symm ▸ Subgroup.mem_top x)
  have hff : f₀ * f₀ = 1 := by rw [← pow_two, ← hf₀2, pow_orderOf_eq_one]
  rcases hF φ hφ with h | h
  · left
    rw [h, mul_one]
    exact hd
  · right
    rw [h, mul_assoc, hff, mul_one]
    exact hd

theorem exists_zOf_eq_of_dihedral {X : Type} [Group X] {S : Subgroup X} {k : ℕ}
    (φ : ↥S ≃* DihedralGroup k) (hk : Even k) (hk3 : 3 ≤ k) :
    ∃ w ∈ S, orderOf w = 2 ∧ E2P.zOf S = Subgroup.zpowers w := by
  set c : DihedralGroup k := DihedralGroup.r ((k / 2 : ℕ) : ZMod k) with hc
  have hcZ : c ∈ Subgroup.center (DihedralGroup k) :=
    (Dih.mem_center_iff' hk hk3).mpr (Or.inr rfl)
  set w : X := (φ.symm c : X) with hw
  have hmem : ∀ x : ↥S, x ∈ Subgroup.center ↥S ↔ φ x ∈ Subgroup.center (DihedralGroup k) := by
    intro x
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro h y
      obtain ⟨y', rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, h y']
    · intro h y
      apply φ.injective
      rw [map_mul, map_mul, h (φ y)]
  have hzOf : ∀ x : X, x ∈ E2P.zOf S ↔ ∃ hx : x ∈ S, (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S := by
    intro x
    constructor
    · rintro ⟨hxS, hxC⟩
      exact ⟨hxS, Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)⟩
    · rintro ⟨hxS, hxC⟩
      refine ⟨hxS, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxC ⟨y, hy⟩)
  have hword : orderOf w = 2 := by
    rw [hw, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc, Dih.orderOf_r_half hk hk3]
  refine ⟨w, (φ.symm c).2, hword, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨hxS, hxC⟩ := (hzOf x).mp hx
    have h1 := (Dih.mem_center_iff' hk hk3).mp ((hmem _).mp hxC)
    rcases h1 with h1 | h1
    · have : (⟨x, hxS⟩ : ↥S) = 1 := φ.injective (by rw [h1, map_one])
      rw [show x = 1 from congrArg Subtype.val this]
      exact Subgroup.one_mem _
    · have : (⟨x, hxS⟩ : ↥S) = φ.symm c := by rw [hc, ← h1, MulEquiv.symm_apply_apply]
      rw [show x = w from congrArg Subtype.val this]
      exact Subgroup.mem_zpowers w
  · rw [Subgroup.zpowers_le]
    refine (hzOf w).mpr ⟨(φ.symm c).2, (hmem _).mpr ?_⟩
    have : (⟨w, (φ.symm c).2⟩ : ↥S) = φ.symm c := rfl
    rw [this, MulEquiv.apply_symm_apply]
    exact hcZ

theorem exists_z₀ (h12c : IVK_1_2c) (hF : L2Field F) (N : L2Notation e) (h8 : 8 ≤ Nat.card N.P) :
    ∃ z₀ : K, orderOf z₀ = 2 ∧ E2P.zOf N.P = Subgroup.zpowers (MulAut.conj z₀) := by
  obtain ⟨n, -, k, hk, -, ⟨φ⟩⟩ := h12c F hF K e N
  have hcard : Nat.card N.P = 2 * k := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hk4 : 4 ≤ k := by omega
  have hkeven : Even k := by
    have hn : 3 ≤ n := by
      by_contra h
      interval_cases n <;> omega
    refine ⟨2 ^ (n - 2), ?_⟩
    have : 2 ^ n = 2 * (2 * 2 ^ (n - 2)) := by
      rw [← mul_assoc, ← pow_two, ← pow_add]
      congr 1
      omega
    omega
  obtain ⟨w, hwP, hw2, hwZ⟩ := exists_zOf_eq_of_dihedral φ hkeven (by omega)
  obtain ⟨z₀, rfl⟩ := (inf_le_right : N.P ≤ innAut K) hwP
  refine ⟨z₀, ?_, hwZ⟩
  rw [← hw2]
  exact (orderOf_injective _ (conj_injective_of_L2 e) z₀).symm

end CFSG.Quasithin.Ch3E213M.OS
