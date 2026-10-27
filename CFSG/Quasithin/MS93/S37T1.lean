module

public import CFSG.Quasithin.MS93.S37LQ

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

@[expose] def T1 (M T L : Subgroup G) : Subgroup G := T ⊓ (L ⊔ pCoreOf 2 M)

omit [Finite G] in
theorem T1_le_sup {M T L : Subgroup G} : T1 M T L ≤ L ⊔ pCoreOf 2 M := inf_le_right

omit [Finite G] in
theorem T1_le_T {M T L : Subgroup G} : T1 M T L ≤ T := inf_le_left

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem act_pow {x : G} (hx : x ∈ M) (n : ℕ) (v : V4 F) :
    C.act (pow_mem hx n) v = (C.act hx)^[n] v := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, id]
    have e := C.N.act_congr C.hMU C.hMA (pow_zero x) (pow_mem hx 0) M.one_mem
    rw [show C.act (pow_mem hx 0) = C.N.act C.hMU C.hMA (pow_mem hx 0) from rfl, e,
      C.N.act_one]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have h1 := congrArg (fun f => f v) (C.N.act_mul C.hMU C.hMA hx (pow_mem hx n))
    simp only [AddMonoidHom.comp_apply] at h1
    rw [← h1]
    exact congrArg (fun f => f v) (C.N.act_congr C.hMU C.hMA (pow_succ' x n) _ _)

theorem mem_sup_of_linear {t : G} (ht : t ∈ T)
    (hlin : ∀ (c : F) (v : V4 F), C.act (C.h.le ht) (c • v) = c • C.act (C.h.le ht) v) :
    t ∈ L ⊔ pCoreOf 2 M := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have htM := C.h.le ht
  obtain ⟨m, hm⟩ := C.h.isPGroup ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hiter : ∀ v : V4 F, (C.act htM)^[2 ^ m] v = v := by
    intro v
    rw [← C.act_pow htM]
    have e : C.act (pow_mem htM (2 ^ m)) = C.N.act C.hMU C.hMA M.one_mem :=
      C.N.act_congr C.hMU C.hMA htm _ _
    rw [e, C.N.act_one]
    rfl
  obtain ⟨g, hg⟩ := exists_eq_mat_of_two_power (C.N.act_bijective C.hMU C.hMA htM)
    (C.N.act_normalizes C.hMU C.hMA C.h.L_le C.h.le_normalizer htM) hlin hiter
  obtain ⟨l, hl⟩ := C.hα g
  have hlM : (l : G) ∈ M := C.h.L_le l.2
  have hxM : t * (l : G)⁻¹ ∈ M := M.mul_mem htM (M.inv_mem hlM)
  have hxact : ∀ v, C.act hxM v = v := by
    intro v
    have h1 := congrArg (fun f => f v) (C.N.act_mul C.hMU C.hMA htM (M.inv_mem hlM))
    simp only [AddMonoidHom.comp_apply] at h1
    rw [show C.act hxM = C.N.act C.hMU C.hMA (M.mul_mem htM (M.inv_mem hlM)) from rfl, h1, hg]
    have h2 : C.N.act C.hMU C.hMA (M.inv_mem hlM) v = mat g⁻¹ *ᵥ v := by
      rw [C.N.act_of_mem C.hMU C.hMA _ (inv_mem l.2), C.N_α]
      have e : (⟨(l : G)⁻¹, inv_mem l.2⟩ : ↥L) = l⁻¹ := rfl
      rw [e, map_inv, hl]
    rw [h2, mat_mulVec_inv]
  obtain ⟨e, he⟩ := C.h.exists_pow_mem_L hxM
  have hxe1 : ∀ v, C.act (pow_mem hxM (2 ^ e)) v = v := by
    intro v
    rw [C.act_pow hxM]
    exact Function.iterate_fixed (hxact v) _
  have hxeQ : (t * (l : G)⁻¹) ^ 2 ^ e ∈ pCoreOf 2 M := by
    refine mem_pCoreOf_of_alpha_eq_one C.N C.h C.hVU he ?_
    refine ext_mulVec fun v => ?_
    rw [← C.N.act_of_mem C.hMU C.hMA (C.h.L_le he) he, mat_one, Matrix.one_mulVec]
    exact hxe1 v
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨_, hxeQ⟩
  have hx2 : (t * (l : G)⁻¹) ^ 2 ^ (e + e') = 1 := by
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val he'
  have hxQ : t * (l : G)⁻¹ ∈ pCoreOf 2 M := by
    refine C.h.mem_pCoreOf_of_comm_Uq_two hxM ⟨_, hx2⟩ fun u hu => ?_
    have hu' : u⁻¹ ∈ Uq M T L := inv_mem hu
    have hxu := C.N.act_co C.hMU C.hMA hxM (u := ⟨u⁻¹, hu'⟩)
      (v := ⟨(t * (l : G)⁻¹) * u⁻¹ * (t * (l : G)⁻¹)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (C.hMU hxM) _).1 hu'⟩) rfl
    rw [hxact] at hxu
    have hA := (C.N.co_eq_co_iff _ _).1 hxu
    have e2 : ⁅u, t * (l : G)⁻¹⁆ =
        (u⁻¹)⁻¹ * ((t * (l : G)⁻¹) * u⁻¹ * (t * (l : G)⁻¹)⁻¹) := by
      rw [commutatorElement_def, inv_inv]
      group
    rw [e2]
    exact hA.2
  have e3 : t = (t * (l : G)⁻¹) * l := by group
  rw [e3]
  exact mul_mem (Subgroup.mem_sup_right hxQ) (Subgroup.mem_sup_left l.2)

theorem pCore_le_T1 : pCoreOf 2 M ≤ T1 M T L := le_inf C.h.pCore_le le_sup_right

theorem Uq_le_T : Uq M T L ≤ T :=
  (C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans C.h.pCore_le

theorem Uq_le_T1 : Uq M T L ≤ T1 M T L :=
  (C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans C.pCore_le_T1

theorem exists_mul_of_mem_T1 {t : G} (ht : t ∈ T1 M T L) :
    ∃ l ∈ T ⊓ L, ∃ q ∈ pCoreOf 2 M, l * q = t := by
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_sup ht.2
  refine ⟨l, ⟨?_, hl⟩, q, hq, e⟩
  have : l = t * q⁻¹ := by rw [← e]; group
  rw [this]
  exact T.mul_mem ht.1 (T.inv_mem (C.h.pCore_le hq))

theorem T_inf_L_inf_pCore : T ⊓ L ⊓ pCoreOf 2 M = Uq M T L := by
  rw [inf_assoc, C.inf_pCore_eq_Uq]
  exact inf_eq_right.2 C.Uq_le_T

@[expose] noncomputable def rho1 : ↥(T1 M T L) →* Sp4 F :=
  C.rho.comp (Subgroup.inclusion T1_le_sup)

theorem rho1_apply (t : ↥(T1 M T L)) :
    C.rho1 t = C.rho ⟨(t : G), T1_le_sup t.2⟩ := rfl

theorem rho1_eq_one_iff (t : ↥(T1 M T L)) : C.rho1 t = 1 ↔ (t : G) ∈ pCoreOf 2 M :=
  C.rho_eq_one_iff _

noncomputable abbrev T0bar : Subgroup (Sp4 F) := C.rho1.range

theorem mem_T1_of_rho_mem {x : ↥(L ⊔ pCoreOf 2 M)} (hx : C.rho x ∈ C.T0bar) :
    (x : G) ∈ T1 M T L := by
  obtain ⟨t, ht⟩ := hx
  have h1 : C.rho (⟨(t : G), T1_le_sup t.2⟩⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, ← C.rho1_apply, ht, inv_mul_cancel]
  rw [C.rho_eq_one_iff] at h1
  have e : (x : G) = t * (((⟨(t : G), T1_le_sup t.2⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ * x :
      ↥(L ⊔ pCoreOf 2 M)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem t.2 (C.pCore_le_T1 h1)

end Cfg

end CFSG.Quasithin.MS93.S37
