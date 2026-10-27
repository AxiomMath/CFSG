module

public import CFSG.Quasithin.H13.A6S13816m
public import CFSG.Quasithin.H13.U3L139H

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

@[expose] def A6L2N.C3At (σ : Perm (Fin 6)) : Prop :=
  σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 → σ * σ * σ = 1 → σ ∈ S14.C3

instance (σ : Perm (Fin 6)) : Decidable (A6L2N.C3At σ) := by
  unfold A6L2N.C3At
  infer_instance

theorem A6L2N.mem_C3_of_cube : ∀ σ : Perm (Fin 6), A6L2N.C3At σ := by
  decide +kernel

namespace L2Borel

open CFSG.Quasithin.SBc5SL2 Matrix

variable {F : Type} [Field F]

@[expose] def dmHom : Fˣ →* SL2 F where
  toFun := dm
  map_one' := by
    ext i j
    rw [coe_dm']
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := fun c c' => by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_dm', coe_dm', coe_dm']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dmHom_injective : Function.Injective (dmHom : Fˣ →* SL2 F) := by
  intro c c' h
  have h1 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [dmHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_dm'] at h1
  exact Units.ext (by simpa using h1)

theorem exists_torus {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X) {Q : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) :
    ∃ x ∈ Subgroup.normalizer (Q : Set X), orderOf x = 2 ^ n - 1 := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := SBc6.exists_sl2_equiv_of_psl hX
  classical
  have := Fintype.ofFinite F
  have hQ' := isSylowTwoOf_top_comap φ hQ
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_Uplus hn hFcard) hQ'
  have hQg : ∀ y : SL2 F, y ∈ Q.comap (φ : SL2 F →* X) ↔ g⁻¹ * y * g ∈ Uplus F := fun y => by
    rw [hg, B6.mem_conjSub]
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcord : orderOf c = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hFcard]
  refine ⟨φ (g * dm c * g⁻¹), ?_, ?_⟩
  · have h1 : g⁻¹ * (g * dm c * g⁻¹) * g ∈ Subgroup.normalizer ((Uplus F : Subgroup (SL2 F)) :
        Set (SL2 F)) := by
      rw [normalizer_Uplus, show g⁻¹ * (g * dm c * g⁻¹) * g = xm 0 * dm c by
        rw [show xm (0 : F) = 1 from Subtype.ext (by ext i j; rw [coe_xm']; fin_cases i <;>
          fin_cases j <;> simp)]
        group]
      exact (mem_Tplus_iff).mpr ⟨0, c, rfl⟩
    have h2 := (mem_normalizer_iff_of_conj hQg _).mpr h1
    rw [← Subgroup.comap_normalizer_eq_of_surjective Q φ.surjective] at h2
    simpa using h2
  · have e1 : φ (g * dm c * g⁻¹) = φ.toMonoidHom ((MulAut.conj g).toMonoidHom (dmHom c)) := rfl
    rw [e1, orderOf_injective φ.toMonoidHom φ.injective,
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      orderOf_injective dmHom dmHom_injective, hcord]

end L2Borel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_two_three_dec (hhat : IsHatA6 L) {x : G}
    (hx : x ∈ S.L1) : ∃ z ∈ pCoreOf 2 S.L1, ∃ k : ℕ, x = z * x ^ 4 ^ k ∧ (x ^ 4 ^ k) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3 := S.cube_mem_pCoreOf_L1_hat hhat hx
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, hx3⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : ∃ m, 4 ^ k = 3 * m + 1 := by
    have : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    exact ⟨4 ^ k / 3, by omega⟩
  refine ⟨((x ^ 3) ^ m)⁻¹, (pCoreOf 2 S.L1).inv_mem ((pCoreOf 2 S.L1).pow_mem hx3 m), k, ?_, ?_⟩
  · rw [hm, pow_succ x (3 * m), pow_mul x 3 m, inv_mul_cancel_left]
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]

theorem L1_le_hat (h1337 : Stmt13_3_7) (hhat : IsHatA6 L) :
    S.L1 ≤ (l0 L ⊔ l1plus T L V) ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := S14.plusData_l1plus S (S.hatL1Plus hhat)
  have hL0 : l0 L = orderThreeSubgroup (Subgroup.centralizer (V : Set G)) := by
    rcases h1337 G T L V S.h13 S.irr S.a6 with h | ⟨-, -, h⟩
    · exfalso
      obtain ⟨c, hc, hc3, hcO, -⟩ := l0_decomp hhat
      apply h
      have hc1 : c ≠ 1 := fun h1 => hcO (h1 ▸ Subgroup.one_mem _)
      have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
      have hcC : c ∈ Subgroup.centralizer (V : Set G) := S.o2Z_le_centralizer (oTwoRes_le _ hc)
      have := orderOf_dvd_natCard (⟨c, hcC⟩ : ↥(Subgroup.centralizer (V : Set G)))
      rwa [Subgroup.orderOf_mk, hord] at this
    · exact h
  have hcen : ∀ y ∈ Subgroup.centralizer (V : Set G), y ^ 3 = 1 → y ∈ l0 L := by
    intro y hy hy3
    rw [hL0]
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem _
    · exact U3.mem_orderThreeSubgroup hy (orderOf_eq_prime hy3 hy1)
  have hO₂T : pCoreOf 2 S.L1 ≤ T :=
    (pCoreOf_le_pCoreOf_sup S.T_le_normalizer_L1).trans
      (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  set R := (l0 L ⊔ l1plus T L V) ⊔ T with hR
  have hTR : T ≤ R := le_sup_right
  have hL0R : l0 L ≤ R := le_sup_left.trans le_sup_left
  have hLpR : l1plus T L V ≤ R := le_sup_right.trans le_sup_left
  have hy : ∀ y ∈ S.L1, y ^ 3 = 1 → y ∈ R := by
    intro y hyL hy3
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hyL)
    by_cases hρ : S.frame.ρ ⟨y, hyN⟩ = 1
    · exact hL0R (hcen y ((S.rho_eq_one_iff _).1 hρ) hy3)
    · obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨y, hyN⟩) hyL
      have hρ3 : S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ ⟨y, hyN⟩ = 1 := by
        rw [← map_mul, ← map_mul]
        have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) *
            ⟨y, hyN⟩ * ⟨y, hyN⟩ = 1 := Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one, ← pow_three']
          exact hy3)
        rw [this, map_one]
      obtain ⟨w, hwL, hρw⟩ := hP.three _ (A6L2N.mem_C3_of_cube _ h4 h5 hs hρ3)
      have hwL1 : (w : G) ∈ S.L1 := hP.le_L1 hwL
      set v := y * (w : G)⁻¹ with hv
      have hvL : v ∈ S.L1 := S.L1.mul_mem hyL (S.L1.inv_mem hwL1)
      obtain ⟨z, hz, k, hvz, hv3⟩ := S.exists_two_three_dec hhat hvL
      have hvN : v ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hvL)
      have hρv : S.frame.ρ ⟨v, hvN⟩ = 1 := by
        have e : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨y, hyN⟩ * w⁻¹ := rfl
        rw [e, map_mul, map_inv, hρw, mul_inv_cancel]
      have hpowN : v ^ 4 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hvN _
      have hρp : S.frame.ρ ⟨v ^ 4 ^ k, hpowN⟩ = 1 := by
        have e : (⟨v ^ 4 ^ k, hpowN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨v, hvN⟩ ^ 4 ^ k := rfl
        rw [e, map_pow, hρv, one_pow]
      have h1 : v ^ 4 ^ k ∈ l0 L := hcen _ ((S.rho_eq_one_iff _).1 hρp) hv3
      have e : y = z * v ^ 4 ^ k * (w : G) := by
        rw [← hvz, hv, inv_mul_cancel_right]
      rw [e]
      exact R.mul_mem (R.mul_mem (hTR (hO₂T hz)) (hL0R h1)) (hLpR hwL)
  intro x hx
  obtain ⟨z, hz, k, hxz, hx3⟩ := S.exists_two_three_dec hhat hx
  rw [hxz]
  exact R.mul_mem (hTR (hO₂T hz)) (hy _ (S.L1.pow_mem hx _) hx3)

end Setting4


namespace L2Hat

open scoped Pointwise

variable {Q : Type} [Group Q]

theorem mem_of_mul_mem_sup {K₁ K₂ U₁ U₂ : Subgroup Q}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥) (hU₁ : U₁ ≤ K₁)
    (hU₂ : U₂ ≤ K₂) {x₁ x₂ : Q} (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (h : x₁ * x₂ ∈ U₁ ⊔ U₂) :
    x₁ ∈ U₁ := by
  have hN : U₁ ≤ Subgroup.normalizer (U₂ : Set Q) := fun u hu =>
    L2Comm.mem_normalizer_of_comm (fun x hx y hy => (hcomm y hy x hx).symm) hU₂ (hU₁ hu)
  have hmul : ((U₁ ⊔ U₂ : Subgroup Q) : Set Q) = (U₁ : Set Q) * (U₂ : Set Q) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U₁ U₂ hN
  have h' : x₁ * x₂ ∈ (U₁ : Set Q) * (U₂ : Set Q) := by
    rw [← hmul]
    exact h
  obtain ⟨u₁, hu₁, u₂, hu₂, he⟩ := Set.mem_mul.mp h'
  have hk : u₁⁻¹ * x₁ ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.mul_mem (K₁.inv_mem (hU₁ hu₁)) hx₁, ?_⟩
    have e : u₁⁻¹ * x₁ = u₂ * x₂⁻¹ :=
      calc u₁⁻¹ * x₁ = u₁⁻¹ * (x₁ * x₂) * x₂⁻¹ := by group
        _ = u₁⁻¹ * (u₁ * u₂) * x₂⁻¹ := by rw [he]
        _ = u₂ * x₂⁻¹ := by group
    rw [e]
    exact K₂.mul_mem (hU₂ hu₂) (K₂.inv_mem hx₂)
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hk
  rw [← hk]
  exact hu₁

theorem orderOf_dvd_of_mul {K₁ K₂ : Subgroup Q} (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hinf : K₁ ⊓ K₂ = ⊥) {x y : Q} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    orderOf x ∣ orderOf (x * y) := by
  apply orderOf_dvd_of_pow_eq_one
  have hc : Commute x y := hcomm x hx y hy
  have h1 := pow_orderOf_eq_one (x * y)
  rw [hc.mul_pow] at h1
  have hm : x ^ orderOf (x * y) ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.pow_mem hx _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact K₂.inv_mem (K₂.pow_mem hy _)
  rw [hinf] at hm
  exact Subgroup.mem_bot.mp hm

theorem exists_torus_in {K U : Subgroup Q} {n : ℕ} (hK : IsPSL 2 2 n ↥K)
    (hU : IsSylowTwoOf U K) :
    ∃ x ∈ K, x ∈ Subgroup.normalizer (U : Set Q) ∧ orderOf x = 2 ^ n - 1 := by
  obtain ⟨x, hxN, hx⟩ := L2Borel.exists_torus hK (isSylowTwoOf_top_subgroupOf hU)
  refine ⟨x, x.2, ?_, by rw [Subgroup.orderOf_coe, hx]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := (Subgroup.mem_normalizer_iff.mp hxN ⟨h, hU.1 hh⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have hhK : h ∈ K := by
      have h1 : (x : Q) * h * (x : Q)⁻¹ ∈ K := hU.1 hh
      have e : h = (x : Q)⁻¹ * ((x : Q) * h * (x : Q)⁻¹) * x := by group
      rw [e]
      exact K.mul_mem (K.mul_mem (K.inv_mem x.2) h1) x.2
    have := (Subgroup.mem_normalizer_iff.mp hxN ⟨h, hhK⟩).mpr (by
      rw [Subgroup.mem_subgroupOf]
      simpa using hh)
    exact Subgroup.mem_subgroupOf.mp this

theorem false_of_inv {K₁ K₂ U₁ U₂ Tq : Subgroup Q} {n : ℕ} (hK : IsPSL 2 2 n ↥K₁)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hU₁ : IsSylowTwoOf U₁ K₁) (hU₂ : U₂ ≤ K₂) (hT : Tq ⊓ (K₁ ⊔ K₂) ≤ U₁ ⊔ U₂)
    {a a' b b' s : Q} (haK : a ∈ K₁) (ha'K : a' ∈ K₁) (hbK : b ∈ K₂) (hb'K : b' ∈ K₂)
    (haN : a ∈ Subgroup.normalizer (U₁ : Set Q)) (ha'N : a' ∈ Subgroup.normalizer (U₁ : Set Q))
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (ha'3 : a' ^ 3 = 1) (ha'1 : a' ≠ 1)
    (hs₁ : s ∈ Subgroup.normalizer (K₁ : Set Q)) (hs₂ : s ∈ Subgroup.normalizer (K₂ : Set Q))
    (hsU : s ∈ Subgroup.normalizer (U₁ : Set Q))
    (h₀ : s * (a * b) * s⁻¹ * (a * b)⁻¹ ∈ Tq) (h₁ : s * (a' * b') * s⁻¹ * (a' * b') ∈ Tq) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsa : s * a * s⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hs₁ a).mp haK
  have hsa' : s * a' * s⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hs₁ a').mp ha'K
  have hsb : s * b * s⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hs₂ b).mp hbK
  have hsb' : s * b' * s⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hs₂ b').mp hb'K
  have hx₁ : s * a * s⁻¹ * a⁻¹ ∈ U₁ := by
    have hm₁ := K₁.mul_mem hsa (K₁.inv_mem haK)
    have hm₂ := K₂.mul_mem hsb (K₂.inv_mem hbK)
    refine mem_of_mul_mem_sup hcomm hinf hU₁.1 hU₂ hm₁ hm₂ (hT ⟨?_, ?_⟩)
    · have hc := hcomm a⁻¹ (K₁.inv_mem haK) _ hm₂
      have e : s * a * s⁻¹ * a⁻¹ * (s * b * s⁻¹ * b⁻¹) = s * (a * b) * s⁻¹ * (a * b)⁻¹ :=
        calc s * a * s⁻¹ * a⁻¹ * (s * b * s⁻¹ * b⁻¹) =
              s * a * s⁻¹ * (a⁻¹ * (s * b * s⁻¹ * b⁻¹)) := by group
          _ = s * a * s⁻¹ * ((s * b * s⁻¹ * b⁻¹) * a⁻¹) := by rw [hc]
          _ = s * (a * b) * s⁻¹ * (a * b)⁻¹ := by group
      rw [e]
      exact h₀
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm₁) (Subgroup.mem_sup_right hm₂)
  have hy₁ : s * a' * s⁻¹ * a' ∈ U₁ := by
    have hm₁ := K₁.mul_mem hsa' ha'K
    have hm₂ := K₂.mul_mem hsb' hb'K
    refine mem_of_mul_mem_sup hcomm hinf hU₁.1 hU₂ hm₁ hm₂ (hT ⟨?_, ?_⟩)
    · have hc := hcomm a' ha'K _ hsb'
      have e : s * a' * s⁻¹ * a' * (s * b' * s⁻¹ * b') = s * (a' * b') * s⁻¹ * (a' * b') :=
        calc s * a' * s⁻¹ * a' * (s * b' * s⁻¹ * b') =
              s * a' * s⁻¹ * (a' * (s * b' * s⁻¹)) * b' := by group
          _ = s * a' * s⁻¹ * ((s * b' * s⁻¹) * a') * b' := by rw [hc]
          _ = s * (a' * b') * s⁻¹ * (a' * b') := by group
      rw [e]
      exact h₁
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm₁) (Subgroup.mem_sup_right hm₂)
  have haU : a ∈ U₁ := by
    rcases mul_mem_or_in hK hU₁ haK ha'K haN ha'N ha3 ha1 ha'3 ha'1 with h | h
    ·
      have hsv : s * (a' * a⁻¹) * s⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp hsU _).mp h
      have hav : a * (a' * a⁻¹) * a⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp haN _).mp h
      have e : a ^ 2 = ((s * (a' * a⁻¹) * s⁻¹) * (s * a * s⁻¹ * a⁻¹) * (a * (a' * a⁻¹) * a⁻¹))⁻¹ *
          (s * a' * s⁻¹ * a') := by group
      have h2 : a ^ 2 ∈ U₁ := by
        rw [e]
        exact U₁.mul_mem (U₁.inv_mem (U₁.mul_mem (U₁.mul_mem hsv hx₁) hav)) hy₁
      have e' : a = (a ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact ha3
      rw [e']
      exact U₁.inv_mem h2
    ·
      have hsv : s * (a' * a) * s⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp hsU _).mp h
      have hw : (s * a * s⁻¹ * a⁻¹)⁻¹ * (a' * a) ∈ U₁ := U₁.mul_mem (U₁.inv_mem hx₁) h
      have hav : a⁻¹ * ((s * a * s⁻¹ * a⁻¹)⁻¹ * (a' * a)) * a⁻¹⁻¹ ∈ U₁ :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp hw
      have e : a⁻¹ ^ 2 = (a⁻¹ * ((s * a * s⁻¹ * a⁻¹)⁻¹ * (a' * a)) * a⁻¹⁻¹)⁻¹ *
          (s * (a' * a) * s⁻¹)⁻¹ * (s * a' * s⁻¹ * a') := by group
      have h2 : a⁻¹ ^ 2 ∈ U₁ := by
        rw [e]
        exact U₁.mul_mem (U₁.mul_mem (U₁.inv_mem hav) (U₁.inv_mem hsv)) hy₁
      have e' : a = a⁻¹ ^ 2 := by
        rw [inv_pow, eq_inv_iff_mul_eq_one, ← pow_succ']
        exact ha3
      rw [e']
      exact h2
  obtain ⟨k, hk⟩ := hU₁.2.1 ⟨a, haU⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ha1 (L32Comm.eq_one_of_pow_of_cube hk' ha3)

end L2Hat

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem n_eq_two_of_hat (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h1334 : Stmt13_3_4) (h1337 : Stmt13_3_7)
    (h13 : Lem13813) (hS : S.Hyp138) (hhat : IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) {n : ℕ}
    (hn : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) : n = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card (Or.inl ⟨n, hn⟩))
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ2 : ∀ x : ↥H, π x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hmem := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hmem⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2'⟩ := h38 _ hQ Kb hKbc
  rcases hL2' Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm', hinf, hTN, -⟩
  · exact (hne (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm))).elim
  set K₂ := Kb.map (MulAut.conj t).toMonoidHom with hK₂
  set X := (S.L1.subgroupOf H).map π with hX
  have hXle : X ≤ Kb ⊔ K₂ := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤ (Kb ⊔ K₂).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjClosure K T := hℓK (Subgroup.mem_subgroupOf.mp hy)
    rw [← hcc] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hcl hz
  have hcomm : ∀ x ∈ Kb, ∀ y ∈ K₂, x * y = y * x :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₂, ∀ y ∈ Kb, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hK₂c : K₂ ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := A38.cComp_conj hKbc
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hU₂ : IsSylowTwoOf (Tb ⊓ K₂) K₂ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂c) hTbs
  have hK0N1 : Kb ⊔ K₂ ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer fun x hx => L2Comm.mem_normalizer_of_comm hcomm le_rfl hx
  have hK0N2 : Kb ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun x hx => L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hx) Subgroup.le_normalizer
  have hP := S14.plusData_l1plus S (S.hatL1Plus hhat)
  obtain ⟨c₀, hc₀, hc₀3, hc₀O, hdec₀⟩ := l0_decomp hhat
  obtain ⟨c₁, hc₁, hρc₁, hc₁3⟩ := hP.exists_c012_cube
  have hL0H : l0 L ≤ H := S.l0_le_L1.trans hℓH
  have hLpH : l1plus T L V ≤ H := hP.le_L1.trans hℓH
  have hTl0 : T ≤ Subgroup.normalizer (l0 L : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans normalizer_L_le_o2Z)
  set X₀ := ((l0 L).subgroupOf H).map π with hX₀
  set X₁ := ((l1plus T L V).subgroupOf H).map π with hX₁
  have hX₀le : X₀ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l0 L).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => S.l0_le_L1 hx)).trans hXle
  have hX₁le : X₁ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l1plus T L V).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => hP.le_L1 hx)).trans
      hXle
  have hTX₀ : Tb ≤ Subgroup.normalizer (X₀ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hTl0 π
  have hTX₁ : Tb ≤ Subgroup.normalizer (X₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hP.T_le π
  obtain ⟨hcb₀3, hcb₀1, hNp₀, hdecb₀⟩ := L2Hat.bar_data π hπ2 hL0H hc₀ hc₀3 hc₀O hdec₀
  obtain ⟨hcb₁3, hcb₁1, hNp₁, hdecb₁⟩ := L2Hat.bar_data π hπ2 hLpH hc₁ hc₁3
    (S14.PlusData.not_mem hρc₁ hc₁3) (fun x hx => hP.decomp hc₁ hρc₁ hx)
  obtain ⟨a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1, haN, hbN⟩ := L2Hat.split_of hcomm' hinf
    hX₀le (hTX₀ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 (l0 L)) π) hNp₀
    ⟨⟨c₀, hL0H hc₀⟩, Subgroup.mem_subgroupOf.mpr hc₀, rfl⟩ hcb₀3 hcb₀1 hdecb₀ hU₁ hU₂
    (inf_le_left.trans hTX₀) (inf_le_left.trans hTX₀)
  obtain ⟨a', ha'K, b', hb'K, hcab', ha'3, ha'1, hb'3, hb'1, ha'N, hb'N⟩ := L2Hat.split_of hcomm'
    hinf hX₁le (hTX₁ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 _) π) hNp₁
    ⟨⟨c₁, hLpH hc₁⟩, Subgroup.mem_subgroupOf.mpr hc₁, rfl⟩ hcb₁3 hcb₁1 hdecb₁ hU₁ hU₂
    (inf_le_left.trans hTX₁) (inf_le_left.trans hTX₁)
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  have hKbP : IsPSL 2 2 n ↥Kb := isPSL_congr e₁ hn
  have hK₂P : IsPSL 2 2 n ↥K₂ := isPSL_congr (A38.conjEquiv t Kb) hKbP
  set B := (Kb ⊔ K₂) ⊓ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ Subgroup.normalizer ((Tb ⊓ K₂ :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hB
  have hBsol : Group.IsSolvable B := L2Comm.isSolvable_borel hcomm hinf hU₁ hU₂
  have hmemB : ∀ x ∈ Kb, x ∈ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) → x ∈ B := fun x hx hxN =>
    ⟨⟨Subgroup.mem_sup_left hx, hxN⟩, L2Comm.mem_normalizer_of_comm hcomm2 hU₂.1 hx⟩
  have hmemB₂ : ∀ x ∈ K₂, x ∈ Subgroup.normalizer ((Tb ⊓ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) → x ∈ B := fun x hx hxN =>
    ⟨⟨Subgroup.mem_sup_right hx, L2Comm.mem_normalizer_of_comm hcomm hU₁.1 hx⟩, hxN⟩
  have hc₀B : π ⟨c₀, hL0H hc₀⟩ ∈ B := hcab ▸ B.mul_mem (hmemB a haK haN) (hmemB₂ b hbK hbN)
  have hc₁B : π ⟨c₁, hLpH hc₁⟩ ∈ B :=
    hcab' ▸ B.mul_mem (hmemB a' ha'K ha'N) (hmemB₂ b' hb'K hb'N)
  have hW : (Tb ⊓ Kb) ⊔ (Tb ⊓ K₂) = Tb ⊓ (Kb ⊔ K₂) := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    · intro u hu
      obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hTbs.2.1 hu.1
      refine L2Comm.mem_sup_of_two_elt hcomm hinf hU₁ hU₂ hu.2 ?_ ?_ hk
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N1 hu.2)
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N2 hu.2)
  have hTB : Tb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun s hs g hg => ?_
    have hgW : g ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hW, ← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hg.1.2,
        A38.map_conj_eq_iff.mpr hg.2]
    have hsW : s ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.mem_normalizer_inf (Subgroup.le_normalizer hs) (hTN hs)
    have hsg : s * g * s⁻¹ ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsW hgW) (Subgroup.inv_mem _ hsW)
    have hsgK : s * g * s⁻¹ ∈ Kb ⊔ K₂ := (Subgroup.mem_normalizer_iff.mp (hTN hs) g).mp hg.1.1
    refine ⟨⟨hsgK, ?_⟩, ?_⟩
    · have h1 := F7.mem_normalizer_inf hsg (hK0N1 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ Kb = Tb ⊓ Kb := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Kb ≤ Kb ⊔ K₂)]
      rwa [e] at h1
    · have h1 := F7.mem_normalizer_inf hsg (hK0N2 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ K₂ = Tb ⊓ K₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : K₂ ≤ Kb ⊔ K₂)]
      rwa [e] at h1
  have hYbsol : Group.IsSolvable ↥(B ⊔ Tb) :=
    C126.isSolvable_sup_of_le_normalizer' hTB hBsol (F1.isSolvable_of_isPGroup_two hTbs.2.1)
  set Y := ((B ⊔ Tb).comap π).map H.subtype with hY
  have hkerπ : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact isSolvable_pCore_two_group ↥H
  have hYsol : Group.IsSolvable Y := by
    have h1 := L2Case.isSolvable_comap π hkerπ hYbsol
    exact Group.isSolvable_of_surjective
      (f := (((B ⊔ Tb).comap π).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hmemY : ∀ x (hx : x ∈ H), π ⟨x, hx⟩ ∈ B ⊔ Tb → x ∈ Y := fun x hx h => ⟨⟨x, hx⟩, h, rfl⟩
  have hTY : T ≤ Y := fun x hx => hmemY x (hTH hx)
    (Subgroup.mem_sup_right ⟨⟨x, hTH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hc₀Y : c₀ ∈ Y := hmemY c₀ (hL0H hc₀) (Subgroup.mem_sup_left hc₀B)
  have hc₁Y : (c₁ : G) ∈ Y := hmemY c₁ (hLpH hc₁) (Subgroup.mem_sup_left hc₁B)
  have hO₂L0 : pCoreOf 2 (l0 L) ≤ T :=
    (pCoreOf_le_pCoreOf_sup hTl0).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have hL0Y : l0 L ≤ Y := by
    intro x hx
    rcases hdec₀ x hx with h | h | h
    · exact hTY (hO₂L0 h)
    · have e : x = (c₀ * c₀)⁻¹ * (c₀ * c₀ * x) := by group
      rw [e]
      exact Y.mul_mem (Y.inv_mem (Y.mul_mem hc₀Y hc₀Y)) (hTY (hO₂L0 h))
    · have e : x = c₀⁻¹ * (c₀ * x) := by group
      rw [e]
      exact Y.mul_mem (Y.inv_mem hc₀Y) (hTY (hO₂L0 h))
  have hLpY : l1plus T L V ≤ Y := by
    intro x hx
    rcases hP.decomp hc₁ hρc₁ hx with h | h | h
    · exact hTY (hP.pCoreOf_le_T h)
    · have e : x = ((c₁ : G) * c₁)⁻¹ * ((c₁ : G) * c₁ * x) := by group
      rw [e]
      exact Y.mul_mem (Y.inv_mem (Y.mul_mem hc₁Y hc₁Y)) (hTY (hP.pCoreOf_le_T h))
    · have e : x = (c₁ : G)⁻¹ * ((c₁ : G) * x) := by group
      rw [e]
      exact Y.mul_mem (Y.inv_mem hc₁Y) (hTY (hP.pCoreOf_le_T h))
  have hL1TY : S.L1 ⊔ T ≤ Y :=
    sup_le ((S.L1_le_hat h1337 hhat).trans (sup_le (sup_le hL0Y hLpY) hTY)) hTY
  have hYG1 : Y ≤ S.G1 := (Subgroup.map_subtype_le _).trans hH.2.1
  have hYM : Y ≤ Subgroup.normalizer (L : Set G) := h13 G T L V S hS Y hL1TY hYG1 hYsol
  obtain ⟨s, hsTL, hρs⟩ := S14.exists_TL_rho S S14.t0_facts.1 S14.t0_facts.2.1
  have hsH : (s : G) ∈ H := hTH hsTL.1
  have hO₂L : pCoreOf 2 L ≤ T :=
    (pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have he₀ : (s : G) * c₀ * (s : G)⁻¹ * c₀⁻¹ ∈ T := by
    obtain ⟨-, hc⟩ := mem_o2Z_iff.mp (oTwoRes_le _ hc₀)
    have e : (s : G) * c₀ * (s : G)⁻¹ * c₀⁻¹ = (c₀ * s * c₀⁻¹ * (s : G)⁻¹)⁻¹ := by group
    rw [e]
    exact T.inv_mem (hO₂L (hc s hsTL.2))
  have he₁ : (s : G) * c₁ * (s : G)⁻¹ * c₁ ∈ T := by
    have hm : ((s * c₁ * s⁻¹ * c₁ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ l1plus T L V := by
      have h1 : (s : G) * c₁ * (s : G)⁻¹ ∈ l1plus T L V :=
        (Subgroup.mem_normalizer_iff.mp (hP.T_le hsTL.1) c₁).mp hc₁
      simpa using (l1plus T L V).mul_mem h1 hc₁
    have hK4 : S.frame.ρ (s * c₁ * s⁻¹ * c₁) ∈ K4L := by
      rw [map_mul, map_mul, map_mul, map_inv, hρs, hρc₁]
      decide +kernel
    simpa using hP.pCoreOf_le_T (hP.mem_pCoreOf_of_K4 hm hK4)
  set sb := π ⟨s, hsH⟩ with hsb
  have hsbT : sb ∈ Tb := ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsTL.1, rfl⟩
  have hē₀ : sb * π ⟨c₀, hL0H hc₀⟩ * sb⁻¹ * (π ⟨c₀, hL0H hc₀⟩)⁻¹ ∈ Tb := by
    refine ⟨⟨s, hsH⟩ * ⟨c₀, hL0H hc₀⟩ * ⟨s, hsH⟩⁻¹ * ⟨c₀, hL0H hc₀⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using he₀), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hē₁ : sb * π ⟨c₁, hLpH hc₁⟩ * sb⁻¹ * π ⟨c₁, hLpH hc₁⟩ ∈ Tb := by
    refine ⟨⟨s, hsH⟩ * ⟨c₁, hLpH hc₁⟩ * ⟨s, hsH⟩⁻¹ * ⟨c₁, hLpH hc₁⟩,
      Subgroup.mem_subgroupOf.mpr (by simpa using he₁), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv]
  have hKbne : Kb ≠ K₂ := fun h => ha1 (by
    have : a ∈ Kb ⊓ K₂ := ⟨haK, h ▸ haK⟩
    rw [hinf] at this
    exact this)
  have hTstab : ∀ s ∈ Tb, s ∈ L2Hat.pairStab Kb K₂ := by
    intro s hs
    have hA : Kb.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb := ⟨s, hs, rfl⟩
    have hB : K₂.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
      ⟨s * t, Tb.mul_mem hs htT, L2Hat.map_conj_map_conj Kb t s⟩
    rw [hconj] at hA hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    have hinj : Kb.map (MulAut.conj s).toMonoidHom ≠ K₂.map (MulAut.conj s).toMonoidHom := by
      intro h
      apply hKbne
      calc Kb = (Kb.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
            (L2Hat.map_conj_inv_map_conj Kb s).symm
        _ = (K₂.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by rw [h]
        _ = K₂ := L2Hat.map_conj_inv_map_conj K₂ s
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (hA.trans hB.symm) hinj
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (hA.trans hB.symm) hinj
  have hswap : Kb.map (MulAut.conj sb).toMonoidHom = K₂ := by
    rcases hTstab sb hsbT with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exfalso
      have hsK : sb ∈ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
        A38.map_conj_eq_iff.mp h1
      refine L2Hat.false_of_inv hKbP hcomm hinf hU₁ inf_le_right hW.ge haK ha'K hbK hb'K haN
        ha'N ha3 ha1 ha'3 ha'1 hsK (A38.map_conj_eq_iff.mp h2)
        (F7.mem_normalizer_inf (Subgroup.le_normalizer hsbT) hsK) ?_ ?_
      · rw [← hcab]
        exact hē₀
      · rw [← hcab']
        exact hē₁
    · exact h1
  obtain ⟨xb, hxbK, hxbN, hxbo⟩ := L2Hat.exists_torus_in hKbP hU₁
  obtain ⟨x₀, hx₀⟩ := hπs xb
  have hx₀M : (x₀ : G) ∈ Subgroup.normalizer (L : Set G) :=
    hYM ⟨x₀, show π x₀ ∈ B ⊔ Tb by rw [hx₀]; exact Subgroup.mem_sup_left (hmemB xb hxbK hxbN),
      rfl⟩
  set g := (x₀ : G) * s * (x₀ : G)⁻¹ * (s : G)⁻¹ with hg
  have hgL : g ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hx₀M s).mp hsTL.2) (L.inv_mem hsTL.2)
  have hgH : g ∈ H := H.mul_mem (H.mul_mem (H.mul_mem x₀.2 hsH) (H.inv_mem x₀.2)) (H.inv_mem hsH)
  set X₂ := (L ⊓ S.G1) ⊔ T with hX₂
  have hTG1 : T ≤ S.G1 := hTH.trans hH.2.1
  have hX₂lt : X₂ < L ⊔ T := by
    refine lt_of_le_of_ne (sup_le (inf_le_left.trans le_sup_left) le_sup_right) fun h => ?_
    have hLG1 : L ≤ S.G1 := le_sup_left.trans (h.symm.le.trans (sup_le inf_le_right hTG1))
    have hz : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨S.z_mem_V, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have h1 := hLG1 hl
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      exact h1
    rw [S.zv] at hz
    exact S.z_ne_one hz
  have h23 := (h1334 G T L V S.h13 S.irr).2.2 X₂ le_sup_right hX₂lt
  have hgX : g ∈ X₂ := Subgroup.mem_sup_left ⟨hgL, hH.2.1 hgH⟩
  have hdvd : 2 ^ n - 1 ∣ Nat.card X₂ := by
    have h1 : sb * xb⁻¹ * sb⁻¹ ∈ K₂ := by
      rw [← hswap]
      exact ⟨xb⁻¹, Kb.inv_mem hxbK, by simp [MulAut.conj_apply]⟩
    have h2 : orderOf xb ∣ orderOf (xb * (sb * xb⁻¹ * sb⁻¹)) :=
      L2Hat.orderOf_dvd_of_mul hcomm hinf hxbK h1
    have e : π (x₀ * ⟨s, hsH⟩ * x₀⁻¹ * ⟨s, hsH⟩⁻¹) = xb * (sb * xb⁻¹ * sb⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx₀, ← hsb]
      group
    have h3 : orderOf (π (x₀ * ⟨s, hsH⟩ * x₀⁻¹ * ⟨s, hsH⟩⁻¹)) ∣
        orderOf (x₀ * ⟨s, hsH⟩ * x₀⁻¹ * ⟨s, hsH⟩⁻¹) := orderOf_map_dvd π _
    have h4 : orderOf (x₀ * ⟨s, hsH⟩ * x₀⁻¹ * ⟨s, hsH⟩⁻¹ : ↥H) = orderOf g := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [e, h4] at h3
    rw [← hxbo]
    exact h2.trans (h3.trans (X₂.orderOf_dvd_natCard hgX))
  have hn1 : 1 ≤ n := hn.1.2.1
  have hn2 : 2 ≤ n := by
    by_contra h0
    have hn : n = 1 := by omega
    subst hn
    exact hKbP.1.2.2.2.1 rfl
  have hpow : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hp3 : ∀ {p : ℕ}, p.Prime → p ∣ 2 ^ n - 1 → p = 3 := by
    intro p hp hpd
    rcases h23 p hp (hpd.trans hdvd) with rfl | rfl
    · exfalso
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    · rfl
  have h3 : 2 ^ n - 1 = 3 ^ (2 ^ n - 1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hp3
  have h38' : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> omega
  by_contra hne2
  have hn3 : 3 ≤ n := by omega
  have e8 : 2 ^ n = 2 ^ (n - 3) * 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.sub_add_cancel hn3]
  have hq : 1 ≤ 2 ^ (n - 3) := Nat.one_le_two_pow
  generalize (2 ^ n - 1).primeFactorsList.length = k at h3
  rcases h38' k with h | h <;> omega

end Setting4

end CFSG.Quasithin.H13.A6
