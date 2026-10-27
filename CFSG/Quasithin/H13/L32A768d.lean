module

public import CFSG.Quasithin.H13.L32A768c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

omit C in
theorem comm_kz_QH_mem {k q : G} (hk : k ∈ kz T V) (hq : q ∈ pCoreOf 2 (hz T V)) :
    k * q * k⁻¹ * q⁻¹ ∈ pCoreOf 2 (kz T V) := by
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  have hle : kz T V ⊓ pCoreOf 2 (hz T V) ≤ pCoreOf 2 (kz T V) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx)
        (le_normalizer_pCoreOf 2 _ (hKH hx)))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  refine hle (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have : q * k⁻¹ * q⁻¹ ∈ kz T V :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hqH) _).mp (inv_mem hk)
    rw [show k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) by group]
    exact mul_mem hk this
  · have : k * q * k⁻¹ ∈ pCoreOf 2 (hz T V) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (hKH hk)) q).mp hq
    exact mul_mem this (inv_mem hq)

theorem mem_u0_of_centralizer_kz (h13314 : A6.Stmt13_3_14) {w : G} (hw : w ∈ fsuU T V)
    (hc : ∀ x ∈ pCoreOf 2 (kz T V), x * w = w * x) : w ∈ u0 T V := by
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have h1 : ⁅⁅kz T V, pCoreOf 2 (hz T V)⁆, Subgroup.zpowers w⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro k hk q hq
    rw [commutatorElement_def, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute (k * q * k⁻¹ * q⁻¹) w from
      hc _ (comm_kz_QH_mem hk hq)).zpow_right n).eq.symm
  have h2 : ⁅⁅pCoreOf 2 (hz T V), Subgroup.zpowers w⁆, kz T V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro q hq y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [commutatorElement_def, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKH hk) _ (C.comm_Q hq (zpow_mem hw n))).symm
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  have hwk : ∀ k ∈ kz T V, w * k * w⁻¹ * k⁻¹ ∈ u0 T V := by
    intro k hk
    have hcen := h3 (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers w) hk)
    rw [commutatorElement_def] at hcen
    have hU : w * k * w⁻¹ * k⁻¹ ∈ fsuU T V := by
      rw [show w * k * w⁻¹ * k⁻¹ = w * (k * w⁻¹ * k⁻¹) by group]
      exact mul_mem hw ((Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (hKH hk)) _).mp
        (inv_mem hw))
    exact centralizer_le_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 h13314 hU
      fun q hq => Subgroup.mem_centralizer_iff.mp hcen q hq
  obtain ⟨-, π, β, hπs, -, -, hβk, hβe⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  have hfix : ∀ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β ⟨w, hw⟩)) = Multiplicative.toAdd (β ⟨w, hw⟩) := by
    intro A
    obtain ⟨k, rfl⟩ := hπs A
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ fsuU T V :=
      (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (hKH k.2)) w).mp hw
    have e1 := hβe k ⟨w, hw⟩ ⟨_, hkw⟩ rfl
    have h0 : β (⟨w, hw⟩ * (⟨_, hkw⟩ : ↥(fsuU T V))⁻¹) = 1 := by
      refine (l24_ker_iff hβk _).mpr ?_
      show w * ((k : G) * w * (k : G)⁻¹)⁻¹ ∈ u0 T V
      rw [show w * ((k : G) * w * (k : G)⁻¹)⁻¹ = w * k * w⁻¹ * (k : G)⁻¹ by group]
      exact hwk k k.2
    rw [map_mul, map_inv, mul_inv_eq_one] at h0
    have h2 := congrArg Multiplicative.toAdd (h0.trans e1)
    rw [toAdd_ofAdd] at h2
    exact h2.symm
  have h0 : Multiplicative.toAdd (β ⟨w, hw⟩) = 0 := sl24_fix_all _ hfix
  have hβ1 : β ⟨w, hw⟩ = 1 := by
    rw [← ofAdd_toAdd (β ⟨w, hw⟩), h0]
    rfl
  exact (l24_ker_iff hβk _).mp hβ1

theorem not_isShort2_kz (h13314 : A6.Stmt13_3_14) : ¬ IsShort2 (kz T V) := by
  rintro ⟨-, -, ⟨hUQ, -⟩, -, -⟩
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  obtain ⟨-, π, β, hπs, -, hβs, hβk, hβe⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  obtain ⟨A, hA⟩ := sl24_exists_fpf
  obtain ⟨k, rfl⟩ := hπs A
  obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd ![1, 0])
  have hx0 : Multiplicative.toAdd (β x) ≠ 0 := by
    rw [hx, toAdd_ofAdd]
    exact f4_e1_ne
  have hkU : ∀ y : ↥(fsuU T V), (k : G) * y * (k : G)⁻¹ ∈ fsuU T V := fun y =>
    (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (hKH k.2)) y).mp y.2
  set kx : ↥(fsuU T V) := ⟨_, hkU x⟩ with hkx
  set y : ↥(fsuU T V) := kx * x⁻¹ with hy
  set ky : ↥(fsuU T V) := ⟨_, hkU y⟩ with hky
  set w : ↥(fsuU T V) := y * ky⁻¹ with hw
  have hUp : IsPGroup 2 ↥(fsuU T V) := fun u => ⟨1, Subtype.ext (by
    simpa using C.hUe u u.2)⟩
  have hyK : (y : G) ∈ kz T V := by
    show (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ kz T V
    have : (x : G) * (k : G)⁻¹ * (x : G)⁻¹ ∈ kz T V :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ (C.U_le_H x.2)) _).mp
        (inv_mem k.2)
    rw [show (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ = k * ((x : G) * (k : G)⁻¹ * (x : G)⁻¹) by
      group]
    exact mul_mem k.2 this
  have hyO : (y : G) ∈ pCoreOf 2 (kz T V) := by
    have hle : kz T V ⊓ fsuU T V ≤ pCoreOf 2 (kz T V) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hg)
          (C.H_le_normalizer_U (hKH hg)))
        (hUp.to_le inf_le_right)
    exact hle (Subgroup.mem_inf.mpr ⟨hyK, y.2⟩)
  have hwB : (w : G) ∈ blockU (kz T V) := by
    have := Subgroup.commutator_mem_commutator hyO k.2
    rw [commutatorElement_def] at this
    show (y : G) * ((k : G) * y * (k : G)⁻¹)⁻¹ ∈ blockU (kz T V)
    rw [show (y : G) * ((k : G) * y * (k : G)⁻¹)⁻¹ = y * k * (y : G)⁻¹ * (k : G)⁻¹ by group]
    exact this
  have hwc := (hUQ hwB).2
  have hw0 : (w : G) ∈ u0 T V :=
    C.mem_u0_of_centralizer_kz h13314 w.2 fun z hz => Subgroup.mem_centralizer_iff.mp hwc z hz
  have hβw : β w = 1 := (l24_ker_iff hβk w).mpr hw0
  rw [hw, map_mul, map_inv, mul_inv_eq_one, hβe k y ky rfl] at hβw
  have hy0 : Multiplicative.toAdd (β y) = 0 := by
    have h2 := congrArg Multiplicative.toAdd hβw
    rw [toAdd_ofAdd] at h2
    exact hA _ h2.symm
  have hβy : β y = 1 := by
    rw [← ofAdd_toAdd (β y), hy0]
    rfl
  rw [hy, map_mul, map_inv, mul_inv_eq_one, hβe k x kx rfl] at hβy
  have h2 := congrArg Multiplicative.toAdd hβy
  rw [toAdd_ofAdd] at h2
  exact hx0 (hA _ h2)

theorem false_of_blocks (h13314 : A6.Stmt13_3_14) {u : G} {r : ℕ} {Kb : Fin r → Subgroup G}
    (hr : 1 ≤ r) (hb : ∀ i, IsChi0Block (yU T V u) (Kb i))
    (hcomm : ∀ i j, i ≠ j → ⁅Kb i, Kb j⁆ = ⊥) (hsup : twoResidual (yU T V u) = ⨆ i, Kb i) :
    False := by
  have := isSimpleGroup_sl24
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  have hK : kz T V = ⨆ i, Kb i := (twoResidual_yU C.hyp C.h63).symm.trans hsup
  have hle : ∀ i, Kb i ≤ kz T V := fun i => hK ▸ le_iSup Kb i
  have hcen : ∀ i j, i ≠ j → ∀ a ∈ Kb i, ∀ b ∈ Kb j, b * a = a * b := fun i j hij a ha b hb' =>
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hij) ha) b hb'
  have hnorm : ∀ i, kz T V ≤ Subgroup.normalizer (Kb i : Set G) := by
    intro i
    rw [hK]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · rw [hji]
      exact Subgroup.le_normalizer
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hcen j i hji x hx y hy, mul_inv_cancel_right]
        exact hy
      · intro hy
        have e := hcen j i hji x hx _ hy
        rw [show x * y * x⁻¹ * x = x * y by group] at e
        rwa [mul_left_cancel e]
  have htop : ∀ i, ((Kb i).subgroupOf (kz T V)).map π = ⊤ := by
    intro i
    have hn : ((Kb i).subgroupOf (kz T V)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hle i)).mpr (hnorm i)
    have hmn : (((Kb i).subgroupOf (kz T V)).map π).Normal := hn.map π hπs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Kb i).subgroupOf (kz T V)).map π) with
      hbot | htop
    · exfalso
      rw [Subgroup.map_eq_bot_iff, hπk] at hbot
      have hKO : Kb i ≤ pCoreOf 2 (kz T V) := fun x hx => by
        have := hbot (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hle i hx⟩ : ↥(kz T V)) ∈ _)
        exact Subgroup.mem_subgroupOf.mp this
      obtain ⟨⟨⟨h1, -, -, -, ⟨hZU, -⟩⟩, -, -⟩, -⟩ := hb i
      have hp : IsPGroup 2 ↥(Kb i) := (pCoreOf_isPGroup 2 _).to_le hKO
      have hbt := h1 ⊥ (hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
      have hKb : Kb i = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
        have : (⟨x, hx⟩ : ↥(Kb i)) ∈ (⊥ : Subgroup ↥(Kb i)) := hbt ▸ Subgroup.mem_top _
        exact congrArg Subtype.val ((Subgroup.mem_bot).mp this)
      have hU : blockU (Kb i) = ⊥ := by
        rw [blockU, hKb, Subgroup.commutator_bot_right]
      rw [hU] at hZU
      exact not_lt_bot hZU
    · exact htop
  have huniq : ∀ i j : Fin r, i = j := by
    intro i j
    by_contra hij
    obtain ⟨a, ha, ea⟩ := Subgroup.mem_map.mp ((htop i).symm ▸ Subgroup.mem_top (upper24 1))
    obtain ⟨b, hb', eb⟩ := Subgroup.mem_map.mp ((htop j).symm ▸ Subgroup.mem_top (lower24 1))
    have hab : b * a = a * b := Subtype.ext (hcen i j hij a (Subgroup.mem_subgroupOf.mp ha) b
      (Subgroup.mem_subgroupOf.mp hb'))
    apply upper24_lower24_ne
    rw [← ea, ← eb, ← map_mul, ← map_mul, hab]
  set i₀ : Fin r := ⟨0, hr⟩
  have hK0 : kz T V = Kb i₀ := by
    rw [hK]
    exact le_antisymm (iSup_le fun i => by rw [huniq i i₀]) (le_iSup Kb i₀)
  exact C.not_isShort2_kz h13314 (hK0 ▸ (hb i₀).1.1)

end Ctx764

end CFSG.Quasithin.H13.L32A
