module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.H13.L34Orders

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped Pointwise

theorem exists_card_sup_eq_mul_pow {Γ : Type*} [Group Γ] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup Γ} [Finite ↥(A ⊔ B)] (hB : IsPGroup p ↥B)
    (hBA : B ≤ Subgroup.normalizer (A : Set Γ)) :
    ∃ k : ℕ, Nat.card ↥(A ⊔ B) = Nat.card ↥A * p ^ k := by
  have hAX : A ≤ A ⊔ B := le_sup_left
  have hBX : B ≤ A ⊔ B := le_sup_right
  have hXA : A ⊔ B ≤ Subgroup.normalizer (A : Set Γ) := sup_le Subgroup.le_normalizer hBA
  have hN : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hXA
  have hQ : IsPGroup p (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : Γ) ∈ (A : Set Γ) * (B : Set Γ) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
        exact x.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx
      obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
      refine ⟨k, ?_⟩
      have hxe : x = ⟨a, hAX ha⟩ * ⟨b, hBX hb⟩ := Subtype.ext hab.symm
      have ha' : ((⟨a, hAX ha⟩ : ↥(A ⊔ B)) : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
      have hb' : (⟨b, hBX hb⟩ : ↥(A ⊔ B)) ^ p ^ k = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact congrArg Subtype.val hk)
      rw [hxe, QuotientGroup.mk_mul, ha', one_mul, ← QuotientGroup.mk_pow, hb',
        QuotientGroup.mk_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (A ⊔ B)), hk, mul_comm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]

variable {G : Type} [Group G] [Finite G]

theorem exists_card_autOn_sup {K T V : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT : IsPGroup 2 ↥T) :
    ∃ k : ℕ, Nat.card ↥(autOn (K ⊔ T) V) = Nat.card ↥(autOn K V) * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥(autOn (K ⊔ T) V) :=
    Finite.of_surjective _ (InternalSec.autOnHom_surjective (sup_le hKV hTV))
  rw [autOn_sup hKV hTV] at hfin ⊢
  exact exists_card_sup_eq_mul_pow (Lem328.isPGroup_autOn hT) (autOn_le_normalizer hKV hTV hTK)

omit [Finite G] in
theorem autOn_eq_of_card_eq {K T V : Subgroup G} [Finite ↥(autOn (K ⊔ T) V)]
    (h : Nat.card ↥(autOn (K ⊔ T) V) = Nat.card ↥(autOn K V)) :
    autOn K V = autOn (K ⊔ T) V :=
  Subgroup.eq_of_le_of_card_ge (A4.autOn_mono le_sup_left) h.le

theorem mul_two_pow_ne_2520 (k : ℕ) : 20160 * 2 ^ k ≠ 2520 := by
  have := Nat.one_le_two_pow (n := k)
  omega

theorem mul_two_pow_ne_9999360 (k : ℕ) : 20160 * 2 ^ k ≠ 9999360 := by
  intro h
  have h1 : 2 ^ k = 496 := by omega
  have hk : k < 9 := by
    by_contra hk
    have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

theorem two_pow_eq_one_of_mul (k : ℕ) (h : 20160 * 2 ^ k = 20160) : 2 ^ k = 1 := by
  omega

theorem not_dvd_mul_two_pow {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h20 : ¬ p ∣ 20160) (k : ℕ) :
    ¬ p ∣ 20160 * 2 ^ k := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact h20 h1
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

omit [Group G] [Finite G] in
theorem card_G2_derived_ne_20160 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ ≠ 20160 := by
  rcases n with _ | _ | n
  · exfalso
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  · have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := 1) one_ne_zero hF
    have hG : Nat.card ↥(quasithinG2 F) = 12096 := by
      rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
        Vol2.KGNat.card_cayleyGroup, hF]
      norm_num
    have : Finite ↥(quasithinG2 F) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
    have hle := Subgroup.card_le_of_le (Subgroup.commutator_le_self (quasithinG2 F))
    omega
  · rw [Vol2.KGNat.factG2DerivedOrder_holds F (n + 2) (by omega) hF]
    have hq : 4 ≤ 2 ^ (n + 2) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (n + 2) = q at hq ⊢
    have h6 : 4096 ≤ q ^ 6 :=
      calc 4096 = 4 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 4096 * (4095 * 15) ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
      Nat.mul_le_mul h6 (Nat.mul_le_mul (by omega) (by omega))
    omega

@[expose] def m12A : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def m12B : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def m22A : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] *
    List.formPerm [10, 13]

@[expose] def m22B : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

@[expose] def m23A : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def m23B : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

@[expose] def m24A : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]

@[expose] def m24B : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem m12A_mem : m12A ∈ NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m12B_mem : m12B ∈ NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem m22A_mem : m22A ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m22B_mem : m22B ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem m23A_mem : m23A ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m23B_mem : m23B ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem m24A_mem : m24A ∈ NativeSporadic.M24 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m24B_mem : m24B ∈ NativeSporadic.M24 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem m12AB_pow : (m12A * m12B) ^ 11 = 1 := by decide +kernel

theorem m12AB_not_comm : m12A * m12B * m12A * (m12A * m12B)⁻¹ ≠ m12A := by decide +kernel

theorem m22AB_pow : (m22A * m22B) ^ 11 = 1 := by decide +kernel

theorem m22AB_ne_one : m22A * m22B ≠ 1 := by decide +kernel

theorem m23AB_pow : (m23A * m23B) ^ 23 = 1 := by decide +kernel

theorem m23AB_ne_one : m23A * m23B ≠ 1 := by decide +kernel

theorem m24AB_pow : (m24A * m24B) ^ 23 = 1 := by decide +kernel

theorem m24AB_ne_one : m24A * m24B ≠ 1 := by decide +kernel

theorem prime_dvd_card_of_mem {Ω : Type*} {H : Subgroup (Equiv.Perm Ω)} {p : ℕ} (hp : p.Prime)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ H) (hpow : σ ^ p = 1) (hne : σ ≠ 1) : p ∣ Nat.card ↥H := by
  have : Fact p.Prime := ⟨hp⟩
  have h : orderOf (⟨σ, hσ⟩ : ↥H) = p := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hne (congrArg Subtype.val h1)
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hpow
  rw [← h]
  exact orderOf_dvd_natCard _

theorem eleven_dvd_card_M22 : 11 ∣ Nat.card ↥NativeSporadic.M22 :=
  prime_dvd_card_of_mem (by norm_num) (Subgroup.mul_mem _ m22A_mem m22B_mem) m22AB_pow
    m22AB_ne_one

theorem twentyThree_dvd_card_M23 : 23 ∣ Nat.card ↥NativeSporadic.M23 :=
  prime_dvd_card_of_mem (by norm_num) (Subgroup.mul_mem _ m23A_mem m23B_mem) m23AB_pow
    m23AB_ne_one

theorem twentyThree_dvd_card_M24 : 23 ∣ Nat.card ↥NativeSporadic.M24 :=
  prime_dvd_card_of_mem (by norm_num) (Subgroup.mul_mem _ m24A_mem m24B_mem) m24AB_pow
    m24AB_ne_one

theorem eleven_dvd_card_mulAut_M12 : 11 ∣ Nat.card (MulAut ↥NativeSporadic.M12) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set y : ↥NativeSporadic.M12 := ⟨m12A * m12B, Subgroup.mul_mem _ m12A_mem m12B_mem⟩ with hy
  have hy11 : y ^ 11 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact m12AB_pow)
  have hc : MulAut.conj y ≠ 1 := by
    intro h1
    have h2 := congrArg (fun φ : MulAut ↥NativeSporadic.M12 => ((φ ⟨m12A, m12A_mem⟩ :
      ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))) h1
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv, hy] at h2
    exact m12AB_not_comm h2
  have hord : orderOf (MulAut.conj y) = 11 :=
    orderOf_eq_prime (by rw [← map_pow, hy11, map_one]) hc
  rw [← hord]
  exact orderOf_dvd_natCard _

end CFSG.Quasithin.H13.L34Orders
