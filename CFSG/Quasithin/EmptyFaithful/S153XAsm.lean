module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Asm

section Comm

variable {K₁ K₂ : Subgroup G} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
include hc

theorem conj_mul_left {a b x : G} (hb : b ∈ K₂) (hx : x ∈ K₁) :
    a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
  have h : b * x = x * b := (hc x hx b hb).symm
  calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [h]; group

theorem conj_mul_right {a b y : G} (ha : a ∈ K₁) (hb : b ∈ K₂) (hy : y ∈ K₂) :
    a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := by
  have h : a * (b * y * b⁻¹) = b * y * b⁻¹ * a :=
    hc a ha _ (K₂.mul_mem (K₂.mul_mem hb hy) (K₂.inv_mem hb))
  calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    _ = b * y * b⁻¹ := by rw [h]; group

end Comm

theorem comm_mem_of_mem {U : Subgroup G} {x k : G} (hx : x ∈ U)
    (hk : k ∈ Subgroup.normalizer (U : Set G)) : x * k * x⁻¹ * k⁻¹ ∈ U := by
  have h : k * x⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hk x⁻¹).mp (inv_mem hx)
  rw [show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
  exact mul_mem hx h

theorem comm_mem_of_mem' {U : Subgroup G} {k x : G} (hk : k ∈ Subgroup.normalizer (U : Set G))
    (hx : x ∈ U) : k * x * k⁻¹ * x⁻¹ ∈ U :=
  mul_mem ((Subgroup.mem_normalizer_iff.mp hk x).mp hx) (inv_mem hx)

theorem comm_mem_self {K : Subgroup G} {b c : G} (hb : b ∈ K) (hc : c ∈ K) :
    b * c * b⁻¹ * c⁻¹ ∈ K :=
  K.mul_mem (K.mul_mem (K.mul_mem hb hc) (K.inv_mem hb)) (K.inv_mem hc)

theorem esub_le_blockU {K Iz : Subgroup G}
    (hN : K ≤ Subgroup.normalizer ((blockU K : Subgroup G) : Set G)) : Esub K Iz ≤ blockU K :=
  Subgroup.commutator_le.mpr fun _ hu _ hk => comm_mem_of_mem hu (hN (Subgroup.mem_inf.mp hk).1)

def commSub (Q E : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (E : Set G) ∧ ∀ q ∈ Q, q * k * q⁻¹ * k⁻¹ ∈ E}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, fun q hq => ?_⟩
    have h : a * (q * b * q⁻¹ * b⁻¹) * a⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp ha.1 _).mp (hb.2 q hq)
    rw [show q * (a * b) * q⁻¹ * (a * b)⁻¹ =
      q * a * q⁻¹ * a⁻¹ * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) by group]
    exact mul_mem (ha.2 q hq) h
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun q hq => ?_⟩
    rw [show q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem ha.1) _).mp (inv_mem (ha.2 q hq))

theorem mem_commSub {Q E : Subgroup G} {k : G} :
    k ∈ commSub Q E ↔ k ∈ Subgroup.normalizer (E : Set G) ∧ ∀ q ∈ Q, q * k * q⁻¹ * k⁻¹ ∈ E :=
  Iff.rfl

theorem z0_le_centerOf (Iz : Subgroup G) : z0 Iz ≤ centerOf (rz Iz) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem esub₁_le_Pp {K₁ K₂ Iz : Subgroup G} {c₁ c₂ : G} : Esub K₁ Iz ≤ Pp K₁ K₂ Iz c₁ c₂ :=
  (le_sup_left : Esub K₁ Iz ≤ E0 K₁ K₂ Iz).trans le_sup_right

theorem esub₂_le_Pp {K₁ K₂ Iz : Subgroup G} {c₁ c₂ : G} : Esub K₂ Iz ≤ Pp K₁ K₂ Iz c₁ c₂ :=
  (le_sup_right : Esub K₂ Iz ≤ E0 K₁ K₂ Iz).trans le_sup_right

variable {I S Iz K₁ K₂ : Subgroup G} {t z c₁ c₂ : G}

theorem esub₁_le (PG : PairGen I S Iz K₁ K₂ t z) : Esub K₁ Iz ≤ K₁ :=
  (esub_le_blockU PG.K₁_N_U).trans (PG.U₁_le_B.trans inf_le_right)

theorem esub₂_le (PG : PairGen I S Iz K₁ K₂ t z) : Esub K₂ Iz ≤ K₂ :=
  (esub_le_blockU PG.K₂_N_U).trans (PG.U₂_le_B.trans inf_le_right)

theorem comm₁_mem_Pp (PG : PairGen I S Iz K₁ K₂ t z) {b : G} (hb : b ∈ S ⊓ K₁) :
    b * c₁ * b⁻¹ * c₁⁻¹ ∈ Pp K₁ K₂ Iz c₁ c₂ :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (PG.B₁_le_R hb)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁)))

theorem comm₂_mem_Pp (PG : PairGen I S Iz K₁ K₂ t z) {b : G} (hb : b ∈ S ⊓ K₂) :
    b * c₂ * b⁻¹ * c₂⁻¹ ∈ Pp K₁ K₂ Iz c₁ c₂ :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (PG.B₂_le_R hb)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂)))

theorem Kp_le_Iz (BF₁ : BlockFacts S Iz K₁ c₁) (BF₂ : BlockFacts S Iz K₂ c₂) : Kp c₁ c₂ ≤ Iz :=
  sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp BF₁.mem).2)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp BF₂.mem).2)

theorem Pp_le_rz (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : Pp K₁ K₂ Iz c₁ c₂ ≤ rz Iz := by
  refine sup_le (Subgroup.commutator_le.mpr fun g hg k hk => ?_) (sup_le ?_ ?_)
  · exact comm_mem_of_mem hg (PG.Iz_N_R (Kp_le_Iz BF₁ BF₂ hk))
  · exact (esub_le_blockU PG.K₁_N_U).trans (PG.U₁_le_Q.trans PG.Q_le_R)
  · exact (esub_le_blockU PG.K₂_N_U).trans (PG.U₂_le_Q.trans PG.Q_le_R)

theorem rz_le_sup (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : rz Iz ≤ Pp K₁ K₂ Iz c₁ c₂ ⊔ pCoreOf 2 I := by
  intro g hg
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := PG.R_decomp g hg
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := BF₁.gen_B s₁ hs₁
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := BF₂.gen_B s₂ hs₂
  exact mul_mem
    (mul_mem (Subgroup.mem_sup_left (comm₁_mem_Pp PG hb₁)) (Subgroup.mem_sup_right (PG.U₁_le_Q hu₁)))
    (mul_mem (Subgroup.mem_sup_left (comm₂_mem_Pp PG hb₂)) (Subgroup.mem_sup_right (PG.U₂_le_Q hu₂)))

theorem commutator_le_E0 (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : ⁅pCoreOf 2 I, Kp c₁ c₂⁆ ≤ E0 K₁ K₂ Iz := by
  have hc₁ := Subgroup.mem_inf.mp BF₁.mem
  have hc₂ := Subgroup.mem_inf.mp BF₂.mem
  have hle : Kp c₁ c₂ ≤ commSub (pCoreOf 2 I) (E0 K₁ K₂ Iz) := by
    refine sup_le
      (Subgroup.zpowers_le.mpr (mem_commSub.mpr ⟨PG.Iz_normalizes_E hc₁.2, fun q hq => ?_⟩))
      (Subgroup.zpowers_le.mpr (mem_commSub.mpr ⟨PG.Iz_normalizes_E hc₂.2, fun q hq => ?_⟩))
    · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := PG.Q_decomp q hq
      rw [conj_mul_left PG.comm (Subgroup.mem_inf.mp (PG.U₂_le_B hu₂)).2 hc₁.1]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu₁ BF₁.mem)
    · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := PG.Q_decomp q hq
      rw [conj_mul_right PG.comm (Subgroup.mem_inf.mp (PG.U₁_le_B hu₁)).2
        (Subgroup.mem_inf.mp (PG.U₂_le_B hu₂)).2 hc₂.1]
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hu₂ BF₂.mem)
  exact Subgroup.commutator_le.mpr fun q hq k hk => (mem_commSub.mp (hle hk)).2 q hq

theorem cent_decomp (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) {g : G} (hg : g ∈ rz Iz)
    (hc : ∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, g * p * g⁻¹ * p⁻¹ = 1) :
    ∃ a₁ ∈ Zsub S K₁, ∃ a₂ ∈ Zsub S K₂, g = a₁ * a₂ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := PG.R_decomp g hg
  have hs₁K := (Subgroup.mem_inf.mp hs₁).2
  have hs₂K := (Subgroup.mem_inf.mp hs₂).2
  have hconj : ∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, s₁ * s₂ * p * (s₁ * s₂)⁻¹ = p := fun p hp =>
    mul_inv_eq_one.mp (hc p hp)
  have hu₁ : s₁ ∈ blockU K₁ := BF₁.faith_E s₁ hs₁ fun e he =>
    (conj_mul_left PG.comm hs₂K (esub₁_le PG he)).symm.trans (hconj e (esub₁_le_Pp he))
  have hu₂ : s₂ ∈ blockU K₂ := BF₂.faith_E s₂ hs₂ fun e he =>
    (conj_mul_right PG.comm hs₁K hs₂K (esub₂_le PG he)).symm.trans (hconj e (esub₂_le_Pp he))
  refine ⟨s₁, BF₁.cent_B s₁ hu₁ fun b hb => ?_, s₂, BF₂.cent_B s₂ hu₂ fun b hb => ?_, rfl⟩
  · have h := hconj _ (comm₁_mem_Pp PG hb)
    rw [conj_mul_left PG.comm hs₂K
      (comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₁.mem).1)] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · have h := hconj _ (comm₂_mem_Pp PG hb)
    rw [conj_mul_right PG.comm hs₁K hs₂K
      (comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₂.mem).1)] at h
    exact mul_inv_eq_iff_eq_mul.mp h

theorem cent_P (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) :
    ∀ g ∈ rz Iz, (∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, g * p * g⁻¹ * p⁻¹ = 1) → g ∈ z0 Iz := by
  intro g hg hc
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := cent_decomp PG BF₁ BF₂ hg hc
  exact mul_mem (PG.Z₁_le_z0 h₁) (PG.Z₂_le_z0 h₂)

theorem z0_decomp (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) {x : G} (hx : x ∈ z0 Iz) :
    ∃ a₁ ∈ Zsub S K₁, ∃ a₂ ∈ Zsub S K₂, x = a₁ * a₂ := by
  obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp (z0_le_centerOf Iz hx)
  refine cent_decomp PG BF₁ BF₂ hxR fun p hp => ?_
  rw [← Subgroup.mem_centralizer_iff.mp hxC p (Pp_le_rz PG BF₁ BF₂ hp), mul_inv_cancel_right,
    mul_inv_cancel]

theorem z0_eq_sup (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : z0 Iz = Zsub S K₁ ⊔ Zsub S K₂ := by
  refine le_antisymm (fun x hx => ?_) (sup_le PG.Z₁_le_z0 PG.Z₂_le_z0)
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := z0_decomp PG BF₁ BF₂ hx
  exact mul_mem (Subgroup.mem_sup_left h₁) (Subgroup.mem_sup_right h₂)

theorem card_z0 (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : Nat.card (z0 Iz) = 4 := by
  have hcomm : ∀ a ∈ Zsub S K₁, ∀ b ∈ Zsub S K₂, a * b = b * a := fun a ha b hb =>
    PG.comm a (Subgroup.mem_inf.mp (PG.U₁_le_B (Subgroup.mem_inf.mp ha).1)).2 b
      (Subgroup.mem_inf.mp (PG.U₂_le_B (Subgroup.mem_inf.mp hb).1)).2
  have hinf : Zsub S K₁ ⊓ Zsub S K₂ = ⊥ := by
    rw [eq_bot_iff, ← PG.U_inf]
    exact inf_le_inf inf_le_left inf_le_left
  have h := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, BF₁.card_Z, BF₂.card_Z, ← z0_eq_sup PG BF₁ BF₂] at h
  omega

theorem mem_Zsub₁_of_mem_z0 (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) {x : G} (hxU : x ∈ blockU K₁) (hx : x ∈ z0 Iz) :
    x ∈ Zsub S K₁ := by
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := z0_decomp PG BF₁ BF₂ hx
  have ha₂ : a₂ ∈ blockU K₁ ⊓ blockU K₂ := Subgroup.mem_inf.mpr
    ⟨by simpa using mul_mem (inv_mem (Subgroup.mem_inf.mp h₁).1) hxU, (Subgroup.mem_inf.mp h₂).1⟩
  rw [PG.U_inf, Subgroup.mem_bot] at ha₂
  rwa [ha₂, mul_one]

theorem mem_Zsub₂_of_mem_z0 (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) {x : G} (hxU : x ∈ blockU K₂) (hx : x ∈ z0 Iz) :
    x ∈ Zsub S K₂ := by
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := z0_decomp PG BF₁ BF₂ hx
  have ha₁ : a₁ ∈ blockU K₁ ⊓ blockU K₂ := Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_inf.mp h₁).1, by simpa using mul_mem hxU (inv_mem (Subgroup.mem_inf.mp h₂).1)⟩
  rw [PG.U_inf, Subgroup.mem_bot] at ha₁
  rwa [ha₁, one_mul]

theorem z_mem_z0 (PG : PairGen I S Iz K₁ K₂ t z) (hzc : ∀ s ∈ S, s * z = z * s) : z ∈ z0 Iz := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hz⟩ := PG.Q_decomp z PG.z_mem_Q
  have hu₁K := (Subgroup.mem_inf.mp (PG.U₁_le_B hu₁)).2
  have hu₂K := (Subgroup.mem_inf.mp (PG.U₂_le_B hu₂)).2
  have hconj : ∀ b ∈ S, u₁ * u₂ * b * (u₁ * u₂)⁻¹ = b := fun b hb => by
    rw [← hz]
    exact mul_inv_eq_iff_eq_mul.mpr (hzc b hb).symm
  have h₁ : u₁ ∈ Zsub S K₁ := Subgroup.mem_inf.mpr ⟨hu₁, Subgroup.mem_centralizer_iff.mpr fun b hb => by
    have hb' := Subgroup.mem_inf.mp hb
    have h := hconj b hb'.1
    rw [conj_mul_left PG.comm hu₂K hb'.2] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  have h₂ : u₂ ∈ Zsub S K₂ := Subgroup.mem_inf.mpr ⟨hu₂, Subgroup.mem_centralizer_iff.mpr fun b hb => by
    have hb' := Subgroup.mem_inf.mp hb
    have h := hconj b hb'.1
    rw [conj_mul_right PG.comm hu₁K hu₂K hb'.2] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  rw [hz]
  exact mul_mem (PG.Z₁_le_z0 h₁) (PG.Z₂_le_z0 h₂)

theorem z_not_mem_U₁ (PG : PairGen I S Iz K₁ K₂ t z) (hz1 : z ≠ 1)
    (hzc : ∀ s ∈ S, s * z = z * s) : z ∉ blockU K₁ := fun hz => by
  have h := PG.swap_U z hz
  rw [hzc t PG.t_mem, mul_inv_cancel_right] at h
  have h' : z ∈ blockU K₁ ⊓ blockU K₂ := Subgroup.mem_inf.mpr ⟨hz, h⟩
  rw [PG.U_inf, Subgroup.mem_bot] at h'
  exact hz1 h'

theorem z_not_mem_U₂ (PG : PairGen I S Iz K₁ K₂ t z) (hz1 : z ≠ 1)
    (hzc : ∀ s ∈ S, s * z = z * s) : z ∉ blockU K₂ := fun hz => by
  have h := PG.swap_U' z hz
  rw [mul_assoc, ← hzc t PG.t_mem, inv_mul_cancel_left] at h
  have h' : z ∈ blockU K₁ ⊓ blockU K₂ := Subgroup.mem_inf.mpr ⟨h, hz⟩
  rw [PG.U_inf, Subgroup.mem_bot] at h'
  exact hz1 h'

theorem z_sq (PG : PairGen I S Iz K₁ K₂ t z) : z ^ 2 = 1 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hz⟩ := PG.Q_decomp z PG.z_mem_Q
  have hc : Commute u₁ u₂ := PG.comm u₁ (Subgroup.mem_inf.mp (PG.U₁_le_B hu₁)).2 u₂
    (Subgroup.mem_inf.mp (PG.U₂_le_B hu₂)).2
  rw [hz, hc.mul_pow, PG.U₁_elem.2 u₁ hu₁, PG.U₂_elem.2 u₂ hu₂, one_mul]

theorem eq_one_of_mem_zpowers (PG : PairGen I S Iz K₁ K₂ t z) {U : Subgroup G} (hzU : z ∉ U)
    {x : G} (hx : x ∈ U) (hxz : x ∈ Subgroup.zpowers z) : x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have h2 : z ^ (2 : ℤ) = 1 := by exact_mod_cast z_sq PG
  rw [zpow_eq_zpow_emod k h2] at hx ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hx
    exact absurd hx hzU

theorem cent_U_mod (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) :
    ∀ u ∈ pCoreOf 2 I, (∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, u * p * u⁻¹ * p⁻¹ ∈ z0 Iz) →
      u ∈ Pp K₁ K₂ Iz c₁ c₂ := by
  intro u hu hc
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := PG.Q_decomp u hu
  have hu₁K := (Subgroup.mem_inf.mp (PG.U₁_le_B hu₁)).2
  have hu₂K := (Subgroup.mem_inf.mp (PG.U₂_le_B hu₂)).2
  have h₁ : u₁ ∈ Esub K₁ Iz := BF₁.centmod_B u₁ hu₁ fun b hb => by
    have hpK := comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₁.mem).1
    have h := hc _ (comm₁_mem_Pp PG hb)
    rw [conj_mul_left PG.comm hu₂K hpK] at h
    exact mem_Zsub₁_of_mem_z0 PG BF₁ BF₂ (comm_mem_of_mem hu₁ (PG.K₁_N_U hpK)) h
  have h₂ : u₂ ∈ Esub K₂ Iz := BF₂.centmod_B u₂ hu₂ fun b hb => by
    have hpK := comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₂.mem).1
    have h := hc _ (comm₂_mem_Pp PG hb)
    rw [conj_mul_right PG.comm hu₁K hu₂K hpK] at h
    exact mem_Zsub₂_of_mem_z0 PG BF₁ BF₂ (comm_mem_of_mem hu₂ (PG.K₂_N_U hpK)) h
  exact Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left h₁) (Subgroup.mem_sup_right h₂))

theorem center_P_mod (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s) :
    ∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, (∀ p' ∈ Pp K₁ K₂ Iz c₁ c₂,
      p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers z) → p ∈ z0 Iz := by
  intro p hp hc
  have hz₁ := z_not_mem_U₁ PG hz1 hzc
  have hz₂ := z_not_mem_U₂ PG hz1 hzc
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := PG.R_decomp p (Pp_le_rz PG BF₁ BF₂ hp)
  have hs₁K := (Subgroup.mem_inf.mp hs₁).2
  have hs₂K := (Subgroup.mem_inf.mp hs₂).2
  have hu₁ : s₁ ∈ blockU K₁ := BF₁.faith_E s₁ hs₁ fun e he => by
    have h := hc e (esub₁_le_Pp he)
    rw [conj_mul_left PG.comm hs₂K (esub₁_le PG he)] at h
    exact mul_inv_eq_one.mp (eq_one_of_mem_zpowers PG hz₁
      (comm_mem_of_mem' (PG.K₁_N_U hs₁K) (esub_le_blockU PG.K₁_N_U he)) h)
  have hu₂ : s₂ ∈ blockU K₂ := BF₂.faith_E s₂ hs₂ fun e he => by
    have h := hc e (esub₂_le_Pp he)
    rw [conj_mul_right PG.comm hs₁K hs₂K (esub₂_le PG he)] at h
    exact mul_inv_eq_one.mp (eq_one_of_mem_zpowers PG hz₂
      (comm_mem_of_mem' (PG.K₂_N_U hs₂K) (esub_le_blockU PG.K₂_N_U he)) h)
  refine mul_mem (PG.Z₁_le_z0 (BF₁.cent_B s₁ hu₁ fun b hb => ?_))
    (PG.Z₂_le_z0 (BF₂.cent_B s₂ hu₂ fun b hb => ?_))
  · have hpK := comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₁.mem).1
    have h := hc _ (comm₁_mem_Pp PG hb)
    rw [conj_mul_left PG.comm hs₂K hpK] at h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp
      (eq_one_of_mem_zpowers PG hz₁ (comm_mem_of_mem hu₁ (PG.K₁_N_U hpK)) h))
  · have hpK := comm_mem_self (Subgroup.mem_inf.mp hb).2 (Subgroup.mem_inf.mp BF₂.mem).1
    have h := hc _ (comm₂_mem_Pp PG hb)
    rw [conj_mul_right PG.comm hs₁K hs₂K hpK] at h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp
      (eq_one_of_mem_zpowers PG hz₂ (comm_mem_of_mem hu₂ (PG.K₂_N_U hpK)) h))

theorem not_E0_le_z0 [Finite G] (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁)
    (BF₂ : BlockFacts S Iz K₂ c₂) : ¬ E0 K₁ K₂ Iz ≤ z0 Iz := by
  intro h
  have hle : Esub K₁ Iz ≤ Zsub S K₁ := fun e he =>
    mem_Zsub₁_of_mem_z0 PG BF₁ BF₂ (esub_le_blockU PG.K₁_N_U he) (h (Subgroup.mem_sup_left he))
  have hcard := Subgroup.card_le_of_le hle
  rw [BF₁.card_E, BF₁.card_Z] at hcard
  omega

end Asm

variable [Finite G]

theorem exists_sub_facts {I S Iz K₁ K₂ : Subgroup G} {t z c₁ c₂ : G}
    (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁) (BF₂ : BlockFacts S Iz K₂ c₂)
    (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s) :
    Nat.card (z0 Iz) = 4 ∧ z ∈ z0 Iz ∧ Kp c₁ c₂ ≤ Iz ∧ Pp K₁ K₂ Iz c₁ c₂ ≤ rz Iz ∧
      E0 K₁ K₂ Iz ≤ Pp K₁ K₂ Iz c₁ c₂ ∧ ⁅pCoreOf 2 I, Kp c₁ c₂⁆ ≤ E0 K₁ K₂ Iz ∧
      rz Iz ≤ Pp K₁ K₂ Iz c₁ c₂ ⊔ pCoreOf 2 I ∧
      (∀ g ∈ rz Iz, (∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, g * p * g⁻¹ * p⁻¹ = 1) → g ∈ z0 Iz) ∧
      (∀ u ∈ pCoreOf 2 I, (∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, u * p * u⁻¹ * p⁻¹ ∈ z0 Iz) →
        u ∈ Pp K₁ K₂ Iz c₁ c₂) ∧
      (∀ p ∈ Pp K₁ K₂ Iz c₁ c₂, (∀ p' ∈ Pp K₁ K₂ Iz c₁ c₂,
        p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers z) → p ∈ z0 Iz) ∧
      ¬ E0 K₁ K₂ Iz ≤ z0 Iz :=
  ⟨Asm.card_z0 PG BF₁ BF₂, Asm.z_mem_z0 PG hzc, Asm.Kp_le_Iz BF₁ BF₂, Asm.Pp_le_rz PG BF₁ BF₂,
    le_sup_right, Asm.commutator_le_E0 PG BF₁ BF₂, Asm.rz_le_sup PG BF₁ BF₂, Asm.cent_P PG BF₁ BF₂,
    Asm.cent_U_mod PG BF₁ BF₂, Asm.center_P_mod PG BF₁ BF₂ hz1 hzc, Asm.not_E0_le_z0 PG BF₁ BF₂⟩

end CFSG.Quasithin.X1469
