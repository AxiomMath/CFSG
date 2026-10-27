module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4UMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Mod

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

omit [Finite G] in
theorem mem_centralizerMod_zpowers_of_comm {X Z : Subgroup G} {x u : G} (hxX : x ∈ X)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hu : ∀ z ∈ Z, u * z = z * u)
    (hc : x * u * x⁻¹ * u⁻¹ ∈ Z) : x ∈ centralizerMod Z X (Subgroup.zpowers u) := by
  refine ⟨hxX, hxZ, fun w hw => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  set c := x * u * x⁻¹ * u⁻¹ with hcdef
  have hcomm : Commute c u := (hu c hc).symm
  have e1 : x * u * x⁻¹ = c * u := by rw [hcdef]; group
  have e2 : x * u ^ n * x⁻¹ * (u ^ n)⁻¹ = c ^ n := by
    calc x * u ^ n * x⁻¹ * (u ^ n)⁻¹ = (x * u * x⁻¹) ^ n * (u ^ n)⁻¹ := by rw [conj_zpow]
      _ = (c * u) ^ n * (u ^ n)⁻¹ := by rw [e1]
      _ = c ^ n := by rw [hcomm.mul_zpow]; group
  rw [e2]
  exact Subgroup.zpow_mem _ hc n

theorem exists_nonsingular_of_mem_uHi
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Qa Qb) {u : G}
    (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Qa)) (huZ : u ∉ quasithinOmegaOneCenter T) :
    ∃ k : ↥(kOf (rhoH h)), (k : UMod h) = clsU h (uHi_le_conjClosure (HLb_le _) hu) ∧
      k ∈ Nonsingular P := by
  have hr : Qa ≤ (resBeta (rhoH h)).range := hp.1.trans hstr.P_le_X
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  obtain ⟨k, hk, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit hr hUu hu
  have hk1 : k ≠ 1 := fun e => huZ ((clsU_eq_one_iff h hUu).mp (by rw [← hkc, e]; rfl))
  refine ⟨k, hkc, ?_⟩
  rw [hstr.nonsingular_eq hp]
  exact ⟨hk1, Or.inl hk⟩

theorem e9_exists_conj_of_mem_uHi (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Q₁ Q₂ : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Q₁ Q₂) {u u' : G}
    (hu : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₁) ∨ u ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₂))
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (hu' : u' ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₁) ∨
      u' ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₂))
    (hu'Z : u' ∉ quasithinOmegaOneCenter T) :
    ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hns : ∀ {v : G}, (v ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₁) ∨
      v ∈ uHi T M H (HLb (resBeta (rhoH h)) Q₂)) → v ∉ quasithinOmegaOneCenter T →
      ∃ hvU : v ∈ conjClosure (VZ T M) H, ∃ k : ↥(kOf (rhoH h)),
        (k : UMod h) = clsU h hvU ∧ k ∈ Nonsingular P := by
    intro v hv hvZ
    rcases hv with hv | hv
    · obtain ⟨k, hk, hkn⟩ := exists_nonsingular_of_mem_uHi h hsplit hstr hp hv hvZ
      exact ⟨uHi_le_conjClosure (HLb_le _) hv, k, hk, hkn⟩
    · obtain ⟨k, hk, hkn⟩ := exists_nonsingular_of_mem_uHi h hsplit hstr hp.symm hv hvZ
      exact ⟨uHi_le_conjClosure (HLb_le _) hv, k, hk, hkn⟩
  obtain ⟨huU, k, hk, hkn⟩ := hns hu huZ
  obtain ⟨hu'U, k', hk', hkn'⟩ := hns hu' hu'Z
  obtain ⟨x, hx, hxk⟩ := hstr.nonsingular_transitive hkn hkn'
  obtain ⟨c, rfl⟩ := hx
  have hcH : (c : G) ∈ H := c.2
  have hcls : clsU h (conj_mem_UH hcH huU) = clsU h hu'U := by
    rw [← rhoH_clsU h c huU, ← hk, ← hk', ← resBeta_apply, hxk]
  have hz := (clsU_eq_iff h (conj_mem_UH hcH huU) hu'U).mp hcls
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hcomm : (c : G) * u * (c : G)⁻¹ * u'⁻¹ = u'⁻¹ * ((c : G) * u * (c : G)⁻¹) := by
    have := isElemAbelian_comm hUab (conj_mem_UH hcH huU) ((conjClosure (VZ T M) H).inv_mem hu'U)
    exact this
  refine ⟨c, hcH, ?_⟩
  rw [hcomm]
  have := (quasithinOmegaOneCenter T).inv_mem hz
  simpa using this

end Mod

end CFSG.Quasithin
