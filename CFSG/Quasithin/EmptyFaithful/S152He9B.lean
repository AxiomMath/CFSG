module

public import CFSG.Quasithin.EmptyFaithful.S152He9Lc
public import CFSG.Quasithin.EmptyFaithful.S152He9V

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoUpper_sup_le {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) : oTwoUpper (K ⊔ P) ≤ K := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hPK).1 hx
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hPK hp) (2 ^ k)
  exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem Y_le_of_not_sylow {Lc : Subgroup G} (hLcG : Lc ≤ g0Of T Mc M K₁)
    (hn : (Lc.subgroupOf (g0Of T Mc M K₁)).Normal) (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁))
    (hnot : ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc)) : yOf152 T Mc M ≤ Lc := by
  by_contra hY
  apply hnot
  have hLN : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLcG).1 hn
  set Y := yOf152 T Mc M with hYdef
  set P := pCoreOf 2 Y with hPdef
  have hYL : Y ⊓ Lc ≤ P := by
    set Z := (Y ⊓ Lc) ⊔ P with hZ
    have hZY : Z ≤ Y := sup_le inf_le_left (pCoreOf_le 2 Y)
    have hPZ : P ≤ Z := le_sup_right
    have hmul : P.relIndex Z * Z.relIndex Y = P.relIndex Y :=
      Subgroup.relIndex_mul_relIndex P Z Y hPZ hZY
    rw [c.y.relIndex_five] at hmul
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (Dvd.intro_left _ hmul) with h1 | h5
    · exfalso
      apply hY
      have hYZ : Y ≤ Z := Subgroup.relIndex_eq_one.mp h1
      have hPN : P ≤ Subgroup.normalizer ((Y ⊓ Lc : Subgroup G) : Set G) := fun p hp =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (pCoreOf_le 2 Y hp),
          hLN (Y_le_G₀ (pCoreOf_le 2 Y hp))⟩
      have hle : oTwoUpper Y ≤ Y ⊓ Lc := by
        refine oTwoUpper_le_of_pow_mem fun x hx => ?_
        obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hPN).1 (hYZ hx)
        obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨p, hp⟩
        have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hPN hp) (2 ^ k)
        exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩
      rw [← yOf152_eq_oTwoUpper T Mc M] at hle
      exact fun x hx => (hle hx).2
    · have h1 : P.relIndex Z = 1 := by
        rw [h5] at hmul
        omega
      exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)
  have hSN : sOf T K₁ ≤ Subgroup.normalizer (Y : Set G) := c.S_le_normalizer_Y
  have hW2 : IsPGroup 2 ((Y ⊔ sOf T K₁) ⊓ Lc : Subgroup G) := by
    rintro ⟨w, hw⟩
    obtain ⟨hwYS, hwL⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨y, hy, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSN).1 hwYS
    obtain ⟨k, hk⟩ := c.S_pgroup ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨y', hy', hxe⟩ := A4.exists_pow_mul_eq hy (hSN hs) (2 ^ k)
    rw [hk', mul_one] at hxe
    have hy'L : y' ∈ Lc := by rw [← hxe]; exact Lc.pow_mem hwL _
    have hy'P : y' ∈ P := hYL ⟨hy', hy'L⟩
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 Y) ⟨y', hy'P⟩
    have hm' : y' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    change (y * s) ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul, hxe, hm']
  have hYSG : Y ⊔ sOf T K₁ ≤ g0Of T Mc M K₁ := sup_le Y_le_G₀ S_le_G₀
  have hWR : (Y ⊔ sOf T K₁) ⊓ Lc ≤ rOf T Mc M K₁ := by
    refine le_pCoreOf_of_le_normalizer inf_le_left ?_ hW2
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hLN (hYSG hg)⟩
  have hRN : rOf T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (c.R_le_S.trans S_le_G₀).trans hLN
  have hLR : Lc ⊓ rOf T Mc M K₁ = sOf T K₁ ⊓ Lc := by
    apply le_antisymm
    · exact fun x hx => ⟨c.R_le_S hx.2, hx.1⟩
    · exact fun x hx => ⟨hx.2, hWR ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩
  have hsyl : IsSylowTwoOf (sOf T K₁ ⊓ Lc) Lc := A4.isSylowTwoOf_inf_normal hS hLcG hLN
  refine ⟨le_sup_left, R_isPGroup, ?_⟩
  have h1 : (rOf T Mc M K₁).relIndex (Lc ⊔ rOf T Mc M K₁) = (Lc ⊓ rOf T Mc M K₁).relIndex Lc :=
    relIndex_sup_right hRN
  rw [sup_comm] at h1
  show ¬ 2 ∣ (rOf T Mc M K₁).relIndex (rOf T Mc M K₁ ⊔ Lc)
  rw [h1, hLR]
  exact hsyl.2.2

theorem false_of_commutator_le {Lc : Subgroup G} (hK : K₁ ≤ Lc) (hLcG : Lc ≤ g0Of T Mc M K₁)
    (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁))
    (hcomm : ⁅yOf152 T Mc M, Lc⁆ ≤ pCoreOf 2 (g0Of T Mc M K₁)) : False := by
  set O := pCoreOf 2 (g0Of T Mc M K₁) with hO
  set Y := yOf152 T Mc M with hYdef
  have hOG : O ≤ g0Of T Mc M K₁ := pCoreOf_le 2 _
  have hON : g0Of T Mc M K₁ ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 _
  have hOS : O ≤ sOf T K₁ :=
    A4.le_of_normal_of_isSylowTwoOf hS hOG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOG).2 hON) (pCoreOf_isPGroup 2 _)
  have hOY : O ≤ Subgroup.normalizer (Y : Set G) := hOS.trans c.S_le_normalizer_Y
  have hLN : Lc ≤ Subgroup.normalizer ((Y ⊔ O : Subgroup G) : Set G) := by
    intro l hl
    apply A4.mem_normalizer_of_conj_mem
    intro x hx
    refine S153D.conj_mem_sup_of_conj_mem (fun a ha => ?_) (fun b hb => ?_) x hx
    · have h1 : ⁅a, l⁆ ∈ O := hcomm (Subgroup.commutator_mem_commutator ha hl)
      have h2 : l * a * l⁻¹ = (⁅a, l⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact (Y ⊔ O).mul_mem (Subgroup.mem_sup_right (O.inv_mem h1)) (Subgroup.mem_sup_left ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hON (hLcG hl)) b).mp hb)
  have hYO : oTwoUpper (Y ⊔ O) = Y := by
    apply le_antisymm (oTwoUpper_sup_le (pCoreOf_isPGroup 2 _) hOY)
    have hYo : Y = oTwoUpper Y := yOf152_eq_oTwoUpper T Mc M
    calc Y = oTwoUpper Y := hYo
      _ ≤ oTwoUpper (Y ⊔ O) :=
        Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hLY : Lc ≤ Subgroup.normalizer (Y : Set G) := by
    have := hLN.trans (normalizer_le_normalizer_oTwoUpper (Y ⊔ O))
    rwa [hYO] at this
  exact c.not_K₁_le_M (hK.trans (hLY.trans c.y.normalizer_Y_le))

end Ctx15204

end CFSG.Quasithin.He9
