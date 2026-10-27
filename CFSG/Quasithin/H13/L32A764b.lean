module

public import CFSG.Quasithin.H13.L32A764a
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32A770g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

omit C in
theorem pCoreOf_kz_le : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (hz T V) := fun _ hk =>
  A4.pCoreOf_le_of_subnormal 2 (A4.subnormal_of_normal (oTwoUpper_le _)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
      (le_normalizer_oTwoUpper _))) hk

theorem exists_kq {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    ∃ k ∈ kz T V, k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧ ∃ q ∈ pCoreOf 2 (hz T V),
      s = k * q := by
  have S0 : Setting147 G T L V (hz T V) := ⟨C.hyp, C.hyp.isHzOne_hz C.h63⟩
  obtain ⟨hR1KQ, -⟩ := R1_le_kz_sup S0 C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hKQ : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hs' := hR1KQ hs
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKQ] at hs'
  obtain ⟨k, hk, q, hq, rfl⟩ := hs'
  have hQR := pCoreOf_hz_le_R1 C.hyp C.hF
  refine ⟨k, hk, ?_, q, hq, rfl⟩
  rw [show k = k * q * q⁻¹ by group]
  exact mul_mem hs (inv_mem (hQR hq))

theorem sq_mem_Q {r : G} (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    r * r ∈ pCoreOf 2 (hz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, π, -, -, hπk, -, -, -⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  obtain ⟨k, hk, hkR, q, hq, rfl⟩ := C.exists_kq hr
  have hπ2 : π ⟨k, hk⟩ ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⟨k, hkR⟩
    have hk2 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine sl24_sq_of_two_pow _ n ?_
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk2)
    rw [this, map_one]
  have hk2 : k * k ∈ pCoreOf 2 (hz T V) := by
    have h1 : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hπ2]
    rw [hπk, Subgroup.mem_subgroupOf] at h1
    have := pCoreOf_kz_le (T := T) (V := V) h1
    simpa [sq] using this
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (hz T V) := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (hz T V) (inv_mem hkH))
      q).mp hq
    simpa using this
  rw [show k * q * (k * q) = (k * k) * (k⁻¹ * q * k) * q by group]
  exact mul_mem (mul_mem hk2 hq') hq

theorem comm_mem_v1_of_mem_u0 {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) {u : G} (hu : u ∈ fsuU T V)
    (h0 : u * s * u⁻¹ * s⁻¹ ∈ u0 T V) : u * s * u⁻¹ * s⁻¹ ∈ fsuV1 T V := by
  have hsu : s * u * s⁻¹ * u⁻¹ ∈ u0 T V := by
    have := inv_mem h0
    rwa [show (u * s * u⁻¹ * s⁻¹)⁻¹ = s * u * s⁻¹ * u⁻¹ by group] at this
  obtain ⟨w, hw, hw0⟩ := C.exists_comm_of_mem_u0 hs hsQ hu hsu
  have hwc : w * s * w⁻¹ * s⁻¹ ∈ V ⊔ u0 T V :=
    commutator_le_sup_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
      (Subgroup.commutator_mem_commutator hw hs)
  have huVU : u ∈ V ⊔ u0 T V := by
    rw [show u = (u * (w * s * w⁻¹ * s⁻¹)⁻¹) * (w * s * w⁻¹ * s⁻¹) by group]
    exact mul_mem (Subgroup.mem_sup_right hw0) hwc
  have h1 := comm_mem_of_R1_sup C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 hs huVU
  have := inv_mem h1
  rwa [show (s * u * s⁻¹ * u⁻¹)⁻¹ = u * s * u⁻¹ * s⁻¹ by group] at this

theorem R1_le_normalizer_U :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  C.R1_le_H.trans C.H_le_normalizer_U

theorem dS_le {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    dS T V s ≤ V ⊔ u0 T V := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_)
    ((inf_le_left : fsuV1 T V ≤ V).trans le_sup_left)
  rintro _ ⟨u, hu, rfl⟩
  exact commutator_le_sup_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
    (Subgroup.commutator_mem_commutator hu hs)

theorem dS_le_U {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    dS T V s ≤ fsuU T V :=
  (C.dS_le hs).trans (sup_le (le_conjClosure V _) (centralizerMod_le_left _ _ _))

theorem dS_inf_u0 {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) : dS T V s ⊓ u0 T V = fsuV1 T V := by
  refine le_antisymm ?_ (le_inf le_sup_right (fsuV1_le_u0 C.hyp C.hMod))
  intro x hxm
  obtain ⟨hx, hx0⟩ := Subgroup.mem_inf.mp hxm
  obtain ⟨u, hu, c, hc, rfl⟩ := (mem_dS_iff C.hUc (C.R1_le_normalizer_U hs)).mp hx
  have hc0 : c ∈ u0 T V := fsuV1_le_u0 C.hyp C.hMod hc
  have h1 : u * s * u⁻¹ * s⁻¹ ∈ u0 T V := by
    have := mul_mem hx0 (inv_mem hc0)
    simpa using this
  exact mul_mem (C.comm_mem_v1_of_mem_u0 hs hsQ hu h1) hc

theorem dS_sup_u0 {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) : dS T V s ⊔ u0 T V = V ⊔ u0 T V := by
  refine le_antisymm (sup_le (C.dS_le hs) le_sup_right) ?_
  intro w hw
  have hwU : w ∈ fsuU T V :=
    (sup_le (le_conjClosure V _) (centralizerMod_le_left _ _ _) : V ⊔ u0 T V ≤ fsuU T V) hw
  have h1 := comm_mem_of_R1_sup C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 hs hw
  obtain ⟨w', hw', hw'0⟩ :=
    C.exists_comm_of_mem_u0 hs hsQ hwU (fsuV1_le_u0 C.hyp C.hMod h1)
  have hd : w' * s * w'⁻¹ * s⁻¹ ∈ dS T V s :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨w', hw', rfl⟩)
  have hU0d : w * (w' * s * w'⁻¹ * s⁻¹)⁻¹ ∈ dS T V s ⊔ u0 T V := Subgroup.mem_sup_right hw'0
  rw [show w = (w * (w' * s * w'⁻¹ * s⁻¹)⁻¹) * (w' * s * w'⁻¹ * s⁻¹) by group]
  exact mul_mem hU0d (Subgroup.mem_sup_left hd)

theorem card_dS {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) : Nat.card ↥(dS T V s) = 8 := by
  have hN : dS T V s ≤ Subgroup.normalizer (u0 T V : Set G) :=
    ((C.dS_le_U hs).trans C.U_le_H).trans (hz_le_normalizer_u0 C.hyp C.hMod)
  have h1 := L32NSet14.card_sup_mul_card_inf hN
  rw [C.dS_sup_u0 hs hsQ, C.dS_inf_u0 hs hsQ, C.hF.card_V₁] at h1
  have h4 := (relIndex_sup_u0 C.hyp C.hMod C.h63 C.hF).1
  have h2 := Subgroup.relIndex_mul_card (u0 T V) (V ⊔ u0 T V)
  rw [inf_eq_left.mpr le_sup_right, h4] at h2
  have hpos : 0 < Nat.card ↥(u0 T V) := Nat.card_pos
  rw [← h2] at h1
  have : Nat.card ↥(dS T V s) * Nat.card ↥(u0 T V) = 8 * Nat.card ↥(u0 T V) := by
    rw [← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem dS_mul_le {s q : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hq : q ∈ pCoreOf 2 (hz T V)) : dS T V (s * q) ≤ dS T V s := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_) le_sup_right
  rintro _ ⟨u, hu, rfl⟩
  have hsH : s ∈ hz T V := C.R1_le_H hs
  have h1 : u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V := by
    have := inv_mem (C.comm_Q hq hu)
    rwa [show (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ by group] at this
  have h2 : s * (u * q * u⁻¹ * q⁻¹) * s⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (C.hF.H_normalizes_V₁ hsH) _).mp h1
  have e : u * (s * q) * u⁻¹ * (s * q)⁻¹ =
      (u * s * u⁻¹ * s⁻¹) * (s * (u * q * u⁻¹ * q⁻¹) * s⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩))
    (Subgroup.mem_sup_right h2)

theorem conj_mem_dS {s x : G} (hx : x ∈ hz T V) {d : G} (hd : d ∈ dS T V s) :
    x * d * x⁻¹ ∈ dS T V (x * s * x⁻¹) := by
  have hxU := C.H_le_normalizer_U hx
  have hxV1 := C.hF.H_normalizes_V₁ hx
  revert d
  refine (sup_le ((Subgroup.closure_le _).mpr ?_) ?_ : dS T V s ≤ (dS T V (x * s * x⁻¹)).comap
    (MulAut.conj x).toMonoidHom)
  · rintro _ ⟨u, hu, rfl⟩
    show x * (u * s * u⁻¹ * s⁻¹) * x⁻¹ ∈ dS T V (x * s * x⁻¹)
    have hxu : x * u * x⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp hxU u).mp hu
    rw [show x * (u * s * u⁻¹ * s⁻¹) * x⁻¹ = (x * u * x⁻¹) * (x * s * x⁻¹) * (x * u * x⁻¹)⁻¹ *
      (x * s * x⁻¹)⁻¹ by group]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, hxu, rfl⟩)
  · intro c hc
    show x * c * x⁻¹ ∈ dS T V (x * s * x⁻¹)
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxV1 c).mp hc)

end Ctx764

end CFSG.Quasithin.H13.L32A
