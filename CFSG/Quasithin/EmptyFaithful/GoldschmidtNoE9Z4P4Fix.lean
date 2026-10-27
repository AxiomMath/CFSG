module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Fix

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

omit [Finite G] in
theorem mem_tZero_of_comm_mem_Z {x u : G} (hxT : x ∈ T)
    (hxZ : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hu : ∀ z ∈ quasithinOmegaOneCenter T, u * z = z * u)
    (hc : x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T) : x ∈ tZero T u := by
  refine ⟨hxT, hxZ, fun w hw => ?_⟩
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

theorem e9z4_exists_fixed (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    ∃ u ∈ uHi T M H R₁, u ∉ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ tZero T u := by
  classical
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, -⟩ := hdat.setup h35 S hred hshape
  subst hR₁
  have hTH : T ≤ H := hred.isHTM.1.1
  obtain ⟨t, htT, ht2, -⟩ := hstr.inv
  have hQ₁P : Q₁ ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) := hpp.1
  have hQ₁3 : Nat.card Q₁ = 3 := hpp.2.2.1
  have hr₁ : Q₁ ≤ (resBeta (rhoH h98.toHypF91)).range := hQ₁P.trans hstr.P_le_X
  have hrk₁ := hstr.rk_inf_fixV_of_plane htT ht2 hQ₁P hQ₁3 (hstr.rk_commV_plane hpp).1
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ commV Q₁ ⊓ fixV (Subgroup.zpowers t), k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall _).2 hcon, rk_bot] at hrk₁
    omega
  obtain ⟨u, hUu, hu, hcls⟩ := exists_mem_uHi_of_mem_commV h98.toHypF91 hsplit hr₁ hk.1
  have huZ : u ∉ quasithinOmegaOneCenter T := fun hZ => by
    have : (k : UMod h98.toHypF91) = 1 := by
      rw [← hcls]
      exact (clsU_eq_one_iff h98.toHypF91 hUu).mpr hZ
    exact hk1 (Subtype.ext this)
  refine ⟨u, hu, huZ, fun x ⟨hxT, hxN⟩ => ?_⟩
  have hxH : x ∈ H := hTH hxT
  have hy := resBeta_mem_zpowers_of_mem_normalizer h98.toHypF91 rfl hstr hQ₁P hQ₁3 htT ht2 hxH
    hxT hxN
  have hfix : resBeta (rhoH h98.toHypF91) ⟨x, hxH⟩ k = k := hk.2 _ hy
  have hρ : rhoH h98.toHypF91 ⟨x, hxH⟩ (clsU h98.toHypF91 hUu) = clsU h98.toHypF91 hUu := by
    rw [hcls]
    exact (resBeta_apply _ _ _).symm.trans (congrArg Subtype.val hfix)
  have hc := (rhoH_clsU_eq_iff h98.toHypF91 ⟨x, hxH⟩ hUu).mp hρ
  have huH : u ∈ H := pCoreOf_le 2 H (h98.toHypF91.conjClosure_Vp_le_pCoreOf hUu)
  exact mem_tZero_of_comm_mem_Z hxT (h98.toHypF91.H_normalizes_V₁ hxH)
    (fun z hz => (Subgroup.mem_centralizer_iff.mp (h98.toHypF91.H_le_centralizer huH) z hz).symm) hc

end Fix

end CFSG.Quasithin
