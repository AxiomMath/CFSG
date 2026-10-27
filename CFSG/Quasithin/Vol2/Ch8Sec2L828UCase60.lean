module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UDickson
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UGlue3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

set_option maxHeartbeats 400000 in
theorem ob5_case60 {G : Type} [Group G] [Finite G]
    {T U LU K : Subgroup G}
    (hLUperf : ⁅LU, LU⁆ = LU) (hfam : LU ∈ lFamily T)
    (hK : quasithinIsCComponent K (Subgroup.normalizer (U : Set G)))
    (hLUK : LU ≤ K)
    (hKle : K ≤ Subgroup.normalizer (U : Set G))
    (hKn : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (θ : K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (hψne : (θ.comp (Subgroup.inclusion hLUK)).range ≠ ⊥)
    (h60 : Nat.card θ.range = 60) :
    K = LU := by
  classical
  haveI : Group.IsPerfect ↥LU := Subgroup.isPerfect_iff.mpr hLUperf
  haveI : Group.IsPerfect (θ.comp (Subgroup.inclusion hLUK)).range :=
    Group.IsPerfect.range (θ.comp (Subgroup.inclusion hLUK))
  have hD' := ob5_perfect_SL_card (θ.comp (Subgroup.inclusion hLUK)).range hψne
  have hle : (θ.comp (Subgroup.inclusion hLUK)).range ≤ θ.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hLUK x, rfl⟩
  have hψ60 : (θ.comp (Subgroup.inclusion hLUK)).range = θ.range := by
    apply Subgroup.eq_of_le_of_card_ge hle
    have hcle : Nat.card (θ.comp (Subgroup.inclusion hLUK)).range ≤ Nat.card θ.range :=
      Subgroup.card_le_of_le hle
    rcases hD' with h1 | h1
    · exact le_of_eq (by rw [h1, h60])
    · exfalso
      have h3 := hcle
      rw [h1, h60] at h3
      norm_num at h3
  have hκ : ∀ κ : ↥K, ∃ x : ↥LU, θ (Subgroup.inclusion hLUK x) = θ κ := by
    intro κ
    have hm : θ κ ∈ (θ.comp (Subgroup.inclusion hLUK)).range := by
      rw [hψ60]
      exact MonoidHom.mem_range.mpr ⟨κ, rfl⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hm
    exact ⟨x, hx⟩
  let C : Subgroup G := (θ.ker).map K.subtype
  have hCK : C ≤ K := by
    intro x hx
    obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact z.2
  have hCsub : C.subgroupOf K = θ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      have hzx' : z = x := Subtype.ext hzx
      exact hzx' ▸ hz
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hCn : (C.subgroupOf K).Normal := by
    rw [hCsub]
    infer_instance
  have hCne : C ≠ K := by
    intro hEq
    have hker : θ.ker = ⊤ := by
      rw [← hCsub, hEq, Subgroup.subgroupOf_self]
    apply hψne
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have hx1 : θ (Subgroup.inclusion hLUK x) = 1 := by
      have hmem : Subgroup.inclusion hLUK x ∈ θ.ker := by
        rw [hker]
        exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp hmem
    rw [MonoidHom.comp_apply, hx1]
    exact Subgroup.one_mem _
  have hKBC : ∀ k ∈ K, ∃ b ∈ LU, b⁻¹ * k ∈ C := by
    intro k hk
    obtain ⟨x, hx⟩ := hκ ⟨k, hk⟩
    refine ⟨(x : G), x.2, ?_⟩
    refine ⟨(Subgroup.inclusion hLUK x)⁻¹ * ⟨k, hk⟩, ?_, ?_⟩
    · exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hx, inv_mul_cancel])
    · rfl
  have hsup := le_sup_pCoreOf_828 hq hK.2.1 hLUK hCK hCn hCne hKBC
  have hO2T := ob5_O2K_le_T hKle hKn hS
  have hKBT : K ≤ LU ⊔ T := hsup.trans (sup_le_sup_left hO2T _)
  have hB : LU ∈ cComp (LU ⊔ T) := hfam
  have hKc : K ∈ cComp (Subgroup.normalizer (U : Set G)) := mem_cComp_iff.mpr hK
  exact eq_of_le_sup_828 hB hKc hLUK hKBT

end CFSG.Quasithin.H13
