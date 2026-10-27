module

public import CFSG.Quasithin.H13.L32NLem14332b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem l32nH_le_normalizer_zU : l32nH T V ≤ Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
  (l32nH_le_normalizer_fsuU T V).trans (normalizer_le_normalizer_centerOf _)

theorem Ctx14332.conj_zU_mem (C : Ctx14332 G T L V V₂ g a D)
    (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4) :
    ∀ h ∈ l32nH T V, ∀ c ∈ centerOf (fsuU T V), h * c * h⁻¹ * c⁻¹ ∈ fsuV1 T V := by
  intro h hh c hc
  by_cases hc1 : c ∈ fsuV1 T V
  · rw [C.H_V1 h hh c hc1, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  have h2 : ((fsuV1 T V).subgroupOf (centerOf (fsuU T V))).index = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := centerOf (fsuU T V))
    rw [inf_eq_left.mpr C.lt.le, C.card_V1, h4] at this
    change (fsuV1 T V).relIndex (centerOf (fsuU T V)) = 2
    omega
  have hhc : h * c * h⁻¹ ∈ centerOf (fsuU T V) :=
    (Subgroup.mem_normalizer_iff.mp (l32nH_le_normalizer_zU hh) c).mp hc
  have hhc1 : h * c * h⁻¹ ∉ fsuV1 T V := fun hm => hc1 (by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) _).mp hm
    rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this)
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨h * c * h⁻¹, hhc⟩)
    (b := ⟨c⁻¹, (centerOf (fsuU T V)).inv_mem hc⟩)).mpr (iff_of_false
      (fun hm => hhc1 (Subgroup.mem_subgroupOf.mp hm))
      (fun hm => hc1 (by
        have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        rwa [inv_inv] at this)))
  exact Subgroup.mem_subgroupOf.mp this

theorem Ctx14332.sq_mem_q (C : Ctx14332 G T L V V₂ g a D)
    (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4) {x : G} (hx : x ∈ l32nCHat T V) :
    x * x ∈ pCoreOf 2 (l32nH T V) := by
  obtain ⟨hxH, hxN, hxc⟩ := hx
  rw [← C.q_tilde]
  refine ⟨(l32nH T V).mul_mem hxH hxH, (l32nH T V).mul_mem hxH hxH, fun u hu => ?_⟩
  have hcZ : x * u * x⁻¹ * u⁻¹ ∈ centerOf (fsuU T V) := hxc u hu
  have e : x * x * u * (x * x)⁻¹ * u⁻¹ =
      (x * (x * u * x⁻¹ * u⁻¹) * x⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹) *
        ((x * u * x⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)) := by group
  rw [e]
  exact (fsuV1 T V).mul_mem (C.conj_zU_mem h4 x hxH _ hcZ)
    (C.sq _ (Subgroup.mem_inf.mp hcZ).1)

theorem Ctx14332.q_eq (C : Ctx14332 G T L V V₂ g a D)
    (h4 : Nat.card ↥(centerOf (fsuU T V)) = 4) : pCoreOf 2 (l32nH T V) = l32nCHat T V := by
  apply le_antisymm
  · rw [← C.q_tilde]
    rintro x ⟨hxH, -, hxc⟩
    exact ⟨hxH, l32nH_le_normalizer_zU hxH, fun u hu => C.lt.le (hxc u hu)⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun x hx => hx.1)
      (le_normalizer_centralizerMod (l32nH_le_normalizer_fsuU T V) l32nH_le_normalizer_zU) ?_
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V))
      ⟨x * x, C.sq_mem_q h4 hx⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_succ', pow_mul, pow_two]
    exact this

omit [Finite G] in
theorem rho_eq_one_iff_mem {h : G} (hh : h ∈ l32nH T V)
    (hN : h ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨h, hN⟩ = 1 ↔ h ∈ l32nCHat T V := by
  rw [L128A.HatU.rho_eq_one_iff D]
  exact ⟨fun h1 => ⟨hh, l32nH_le_normalizer_zU hh, h1⟩, fun h1 => h1.2.2⟩

end L14332

end CFSG.Quasithin.H13
