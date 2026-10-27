module

public import CFSG.Quasithin.MS93.S37QD
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.Quasithin.MS93.S37Rho

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem eq_one_of_mem_scalars {g : Sp4 F}
    (hg : g ∈ (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf
      (StatedSp 2 F)) : g = 1 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  rw [Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
    at hg
  obtain ⟨c, hc⟩ := hg
  have hmul : ∀ v : V4 F, mat g *ᵥ v = (c : F) • v := by
    intro v
    rw [mat, ← hc]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hc1 := eq_one_of_smul_mem hmul
  refine ext_mulVec fun v => ?_
  rw [hmul, hc1, one_smul, mat_one, Matrix.one_mulVec]

theorem alpha_eq_one_of_centralizes {y : ↥L}
    (hy : ∀ v ∈ Uq M T L, (y : G) * v * (y : G)⁻¹ = v) : C.α y = 1 :=
  eq_one_of_isSumOfNaturalModulesVia C.hnat hy

theorem inf_pCore_eq_Uq : L ⊓ pCoreOf 2 M = Uq M T L := by
  refine le_antisymm ?_ (le_inf (Uq_le_L C.h) (C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)))
  have hcomm : ∀ y ∈ pCoreOf 2 M, ∀ v ∈ Uq M T L, y * v * y⁻¹ = v := fun y hy v hv => by
    rw [comm_of_mem_Uq C.h hv hy, mul_inv_cancel_right]
  set N₀ : Subgroup ↥L := (Uq M T L).subgroupOf L with hN₀
  have hN₀n : N₀.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le_L C.h)).2 C.hnat.1
  let Z₀ : Subgroup (Sp4 F) :=
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)
  let f : ↥L →* (Sp4 F ⧸ Z₀) := (QuotientGroup.mk' Z₀).comp C.α
  have hf1 : ∀ y : ↥L, f y = 1 ↔ C.α y = 1 := by
    intro y
    constructor
    · intro hy
      exact C.eq_one_of_mem_scalars ((QuotientGroup.eq_one_iff _).1 hy)
    · intro hy
      show (QuotientGroup.mk' Z₀) (C.α y) = 1
      rw [hy, map_one]
  have hNf : N₀ ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hf1]
    have hyU : (y : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.1 hy
    exact C.alpha_eq_one_of_centralizes fun v hv => by
      rw [Sp4L.uq_comm C.h hyU hv, mul_inv_cancel_right]
  let P := ↥L ⧸ N₀
  let η : P →* (Sp4 F ⧸ Z₀) := QuotientGroup.lift N₀ f hNf
  have hη : Function.Surjective η := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z₀ z
    obtain ⟨y, rfl⟩ := C.hα g
    exact ⟨QuotientGroup.mk y, rfl⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 C.h.perfect
  have hkerQ : ∀ y : ↥L, η (QuotientGroup.mk y) = 1 → (y : G) ∈ pCoreOf 2 M := by
    intro y hy
    have : f y = 1 := hy
    rw [hf1] at this
    exact mem_pCoreOf_of_alpha_eq_one C.N C.h C.hVU y.2 (by rw [C.N_α]; exact this)
  have hC : η.ker ≤ Subgroup.center P := by
    intro p hp
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
    have hyQ := hkerQ y hp
    rw [Subgroup.mem_center_iff]
    intro p'
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective p'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have e : (((l * y)⁻¹ * (y * l) : ↥L) : G) = ⁅(y : G)⁻¹, (l : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact comm_mem_Uq C.hVU (inv_mem hyQ) (inv_mem l.2)
  have h2 : IsPGroup 2 η.ker := by
    intro p
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (p : P)
    have hyQ := hkerQ y (by rw [hy]; exact p.2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨y, hyQ⟩
    refine ⟨e, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hy, ← QuotientGroup.mk_pow]
    have : y ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
    rw [this, QuotientGroup.mk_one]
    rfl
  have hk1 : 1 ≤ C.k := by have := C.hk; omega
  have hFn : Nat.card F = 2 ^ C.k := by rw [Nat.card_eq_fintype_card, C.hF]
  have hker := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_two_cover_trivial hFn hk1 le_rfl
    (fun _ => C.hk) P η hη hC h2
  intro y ⟨hyL, hyQ⟩
  have hy1 : η (QuotientGroup.mk ⟨y, hyL⟩) = 1 := by
    show f ⟨y, hyL⟩ = 1
    rw [hf1]
    exact C.alpha_eq_one_of_centralizes (hcomm y hyQ)
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hy1
  exact hy1

end Cfg

end CFSG.Quasithin.MS93.S37
