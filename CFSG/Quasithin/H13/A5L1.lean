module

public import Certificates.Certificate17038
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.A5Producer

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

theorem InK4_mul : ∀ σ τ : Equiv.Perm (Fin 5), InK4 σ → InK4 τ → InK4 (σ * τ) :=
  Certificates.certificate17038.1

theorem InK4_inv : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → InK4 σ⁻¹ :=
  Certificates.certificate17038.2.1

theorem InK4_conj' : ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → σ.sign = 1 → InK4 τ →
    InK4 (σ * τ * σ⁻¹) :=
  Certificates.certificate17038.2.2.1

theorem InK4_sq : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ * σ = 1 :=
  Certificates.certificate17038.2.2.2.1

theorem not_InK4_c3p' : ¬ InK4 c3p := by decide

theorem A4_decomp' : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ 4 = 4 →
    InK4 σ ∨ InK4 (c3p * c3p * σ) ∨ InK4 (c3p * σ) :=
  Certificates.certificate17038.2.2.2.2

@[expose] def K4sub : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | InK4 σ}
  mul_mem' := fun {a b} ha hb => InK4_mul a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => InK4_inv a ha

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem rho_L1' {x : ↥(Subgroup.normalizer (V : Set G))} (hx : (x : G) ∈ S.L1) :
    (S.frame.ρ x).sign = 1 ∧ S.frame.ρ x 4 = 4 :=
  ⟨(S.frame.image_L _).1 ⟨x, S.L1_le_L hx, rfl⟩,
    S.rho_four_of_conj_z x.2 (S.conj_z_of_normalizes (S.L1_le_NV1 hx))⟩

@[expose] noncomputable def L1K4 : Subgroup G :=
  ((K4sub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype) ⊓ S.L1

theorem mem_L1K4
    {x : G} : x ∈ S.L1K4 ↔ ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
    InK4 (S.frame.ρ ⟨x, hx⟩) ∧ x ∈ S.L1 := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
    exact ⟨y.2, hy, hyL⟩
  · rintro ⟨hx, hK, hL⟩
    exact ⟨⟨⟨x, hx⟩, hK, rfl⟩, hL⟩

theorem isPGroup_L1K4 : IsPGroup 2 S.L1K4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, hx⟩
  obtain ⟨hxN, hK, hL⟩ := S.mem_L1K4.1 hx
  have hsq : S.frame.ρ (⟨x, hxN⟩ * ⟨x, hxN⟩) = 1 := by
    rw [map_mul]
    exact InK4_sq _ hK
  have hC := S.frame.mem_centralizer_of_rho _ hsq
  have hO : x * x ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cLT]
    exact ⟨le_sup_left (a := L) (S.L1_le_L (S.L1.mul_mem hL hL)), hC⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hO⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : (x * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  show x ^ 2 ^ (k + 1) = 1
  rw [pow_succ', pow_mul, ← hk', sq]

theorem L1_le_normalizer_L1K4
    : S.L1 ≤ Subgroup.normalizer (S.L1K4 : Set G) := by
  refine le_normalizer_of_conj_mem fun l hl x hx => ?_
  obtain ⟨hxN, hK, hL⟩ := S.mem_L1K4.1 hx
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hl)
  obtain ⟨hs, h4⟩ := S.rho_L1' (x := ⟨l, hlN⟩) hl
  refine S.mem_L1K4.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN) (Subgroup.inv_mem _ hlN),
    ?_, S.L1.mul_mem (S.L1.mul_mem hl hL) (S.L1.inv_mem hl)⟩
  have e : (⟨l * x * l⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN)
      (Subgroup.inv_mem _ hlN)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact InK4_conj' _ _ h4 hs hK

theorem L1K4_le : S.L1K4 ≤ pCoreOf 2 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right S.L1_le_normalizer_L1K4 S.isPGroup_L1K4

theorem mem_pCoreOf_L1_of_InK4
    {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : (x : G) ∈ S.L1) (hK : InK4 (S.frame.ρ x)) : (x : G) ∈ pCoreOf 2 S.L1 :=
  S.L1K4_le (S.mem_L1K4.2 ⟨x.2, hK, hx⟩)

theorem exists_L1_c3p_cube :
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
    S.frame.ρ g = c3p ∧ (g : G) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_c3p
  have h3 : ((c ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 S.L1 :=
    S.mem_pCoreOf_L1_of_InK4 (S.L1.pow_mem hcL 3)
      (by rw [map_pow, hc, c3p_cube]; exact Or.inl rfl)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, h3⟩
  have hk' : ((c : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨c ^ 4 ^ k, by simpa using S.L1.pow_mem hcL (4 ^ k), ?_, ?_⟩
  · rw [map_pow, hc, c3p_pow_four_pow]
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]

@[expose] noncomputable def cL1 :
    ↥(Subgroup.normalizer (V : Set G)) :=
  Classical.choose S.exists_L1_c3p_cube

theorem cL1_mem
    : (S.cL1 : G) ∈ S.L1 := (Classical.choose_spec S.exists_L1_c3p_cube).1

theorem cL1_rho
    : S.frame.ρ S.cL1 = c3p := (Classical.choose_spec S.exists_L1_c3p_cube).2.1

theorem cL1_cube
    : (S.cL1 : G) ^ 3 = 1 := (Classical.choose_spec S.exists_L1_c3p_cube).2.2

theorem cL1_not_mem : (S.cL1 : G) ∉ pCoreOf 2 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, h⟩
  have hk' : (S.cL1 : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (S.cL1 : G) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one S.cL1_cube) (orderOf_dvd_of_pow_eq_one hk')
  have h2 : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  have := S.cL1_rho
  have h3 : S.cL1 = 1 := Subtype.ext h1
  rw [h3, map_one] at this
  exact absurd this.symm (by decide)

theorem L1_decomp {x : G} (hx : x ∈ S.L1) :
    x ∈ pCoreOf 2 S.L1 ∨ (S.cL1 : G) * S.cL1 * x ∈ pCoreOf 2 S.L1 ∨
      (S.cL1 : G) * x ∈ pCoreOf 2 S.L1 := by
  obtain ⟨xn, rfl⟩ : ∃ xn : ↥(Subgroup.normalizer (V : Set G)), (xn : G) = x :=
    ⟨⟨x, S.frame.L_le (S.L1_le_L hx)⟩, rfl⟩
  obtain ⟨hs, h4⟩ := S.rho_L1' hx
  rcases A4_decomp' _ hs h4 with h | h | h
  · exact Or.inl (S.mem_pCoreOf_L1_of_InK4 hx h)
  · refine Or.inr (Or.inl ?_)
    exact S.mem_pCoreOf_L1_of_InK4 (x := S.cL1 * S.cL1 * xn)
      (S.L1.mul_mem (S.L1.mul_mem S.cL1_mem S.cL1_mem) hx)
      (by rw [map_mul, map_mul, S.cL1_rho]; exact h)
  · refine Or.inr (Or.inr ?_)
    exact S.mem_pCoreOf_L1_of_InK4 (x := S.cL1 * xn) (S.L1.mul_mem S.cL1_mem hx)
      (by rw [map_mul, S.cL1_rho]; exact h)

theorem L1_le_H {H : Subgroup G} (hH : H ∈ S.Hz) : S.L1 ≤ H := le_sup_left.trans hH.1.1

theorem cL1_not_mem_Q
    {H : Subgroup G} : (S.cL1 : G) ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, h⟩
  have hk' : (S.cL1 : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (S.cL1 : G) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one S.cL1_cube) (orderOf_dvd_of_pow_eq_one hk')
  have h2 : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  have := S.cL1_rho
  have h3 : S.cL1 = 1 := Subtype.ext h1
  rw [h3, map_one] at this
  exact absurd this.symm (by decide)

end Setting

end CFSG.Quasithin.H13.A5
