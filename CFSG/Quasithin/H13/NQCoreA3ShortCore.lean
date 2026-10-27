module

public import CFSG.Quasithin.H13.NQCoreA3Endpoint
public import CFSG.Quasithin.SteinbergCDOddPlaneTools
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCD (glFixedSpace mem_glFixedSpace)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {X T K A U V : Subgroup G}

theorem actual_A3_Sylow_normalizer_preserves_short_core (hX : CharTwo X)
    (hT : IsSylowTwoOf T X) (hKX : K ≤ X) (hK : IsShort2 K)
    (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hTK : T ≤ normalizer (K : Set G))
    (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hU : U = blockQ K) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE2 : Nat.card ↥(A ⊓ centralizer (U : Set G)) = 2)
    (h3 : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9)
    (hV : V = conjJoin X U) :
    ((normalizer (T : Set G) ⊓ X : Subgroup G) : Set G) =
        (T : Set G) * ((normalizer (T : Set G) ⊓ (X ⊓ centralizer (V : Set G)) : Subgroup G) :
          Set G) ∧
      normalizer (T : Set G) ⊓ X ≤ normalizer (U : Set G) := by
  classical
  obtain ⟨-, ⟨M, _, _, ι, ρ, hρ⟩, hall⟩ := actual_A3_reduced_actor_S3_or_S7_normalizer_endpoint
    hX hT hKX hK hK3 hTK hAT hAn hU hAU hE2 h3 hV
  obtain ⟨τ, -, -, -, -, -, hrest⟩ := hall M ι ρ hρ
  set N := closure {x | ∃ h ∈ ρ.range,
    x = h * (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * h⁻¹} with hN
  obtain ⟨-, -, -, -, -, -, hnorm, -⟩ := hrest N (glFixedSpace N) rfl fun v => mem_glFixedSpace N
  have hXV : X ≤ normalizer (V : Set G) := by
    intro x hx
    rw [LieType.Steinberg.mem_normalizer_iff_map_conj, hV, conjJoin, Subgroup.map_iSup]
    have h1 : ∀ s : ↥X, (U.map (MulAut.conj (s : G)).toMonoidHom).map
        (MulAut.conj x).toMonoidHom =
          U.map (MulAut.conj (((⟨x, hx⟩ : ↥X) * s : ↥X) : G)).toMonoidHom := fun s => by
      rw [Subgroup.coe_mul, LieType.Steinberg.map_conj_mul]
    simp_rw [h1]
    exact (Equiv.mulLeft (⟨x, hx⟩ : ↥X)).iSup_comp
      (g := fun s : ↥X => U.map (MulAut.conj (s : G)).toMonoidHom)
  have hker : ∀ z : ↥X, z ∈ ρ.ker → (z : G) ∈ centralizer (V : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro v hv
    have hw : (z : G) * v * (z : G)⁻¹ ∈ V := (mem_normalizer_iff.mp (hXV z.2) v).mp hv
    have h1 := hρ z ⟨v, hv⟩ ⟨_, hw⟩ rfl
    rw [MonoidHom.mem_ker.mp hz, Units.val_one, Module.End.one_apply] at h1
    have h2 := congrArg Subtype.val (ι.injective (Multiplicative.toAdd.injective h1))
    change v = (z : G) * v * (z : G)⁻¹ at h2
    calc v * z = ((z : G) * v * (z : G)⁻¹) * z := by rw [← h2]
      _ = z * v := by group
  set Ts := (T.subgroupOf X).map ρ with hTs
  have hTU : T ≤ normalizer (U : Set G) := by
    rw [hU]
    exact hTK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hUV : U ≤ V := by
    rw [hV]
    refine le_iSup_of_le (1 : ↥X) ?_
    rw [OneMemClass.coe_one, LieType.Steinberg.map_conj_one]
  have hsub : ((normalizer (T : Set G) ⊓ X : Subgroup G) : Set G) ⊆
      (T : Set G) * ((normalizer (T : Set G) ⊓ (X ⊓ centralizer (V : Set G)) : Subgroup G) :
        Set G) := by
    intro x hx
    obtain ⟨hxN, hxX⟩ := mem_inf.mp hx
    set x' : ↥X := ⟨x, hxX⟩ with hx'
    have hconj : ∀ z : ↥X, (z : G) ∈ normalizer (T : Set G) → ∀ y ∈ Ts,
        ρ z * y * (ρ z)⁻¹ ∈ Ts := by
      rintro z hz _ ⟨t, ht, rfl⟩
      refine ⟨z * t * z⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (mem_normalizer_iff.mp hz t).mp ht
    have hρx : ρ x' ∈ normalizer (Ts : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) ⊓
        ρ.range := by
      refine mem_inf.mpr ⟨mem_normalizer_iff.mpr fun y => ⟨hconj x' hxN y, fun hy => ?_⟩,
        ⟨x', rfl⟩⟩
      have h1 := hconj x'⁻¹ (inv_mem hxN) _ hy
      rwa [map_inv, inv_inv, show (ρ x')⁻¹ * (ρ x' * y * (ρ x')⁻¹) * ρ x' = y by group] at h1
    rw [hnorm] at hρx
    obtain ⟨t, ht, hte⟩ := hρx
    have hd : t⁻¹ * x' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
    refine ⟨t, ht, ((t⁻¹ * x' : ↥X) : G), mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem (inv_mem (le_normalizer (mem_subgroupOf.mp ht))) hxN
    · exact mem_inf.mpr ⟨(t⁻¹ * x').2, hker _ hd⟩
    · change (t : G) * ((t : G)⁻¹ * x) = x
      group
  refine ⟨Set.Subset.antisymm hsub ?_, fun x hx => ?_⟩
  · rintro _ ⟨t, ht, d, hd, rfl⟩
    have hdN : d ∈ normalizer (T : Set G) := (mem_inf.mp hd).1
    have hdX : d ∈ X := (mem_inf.mp (mem_inf.mp hd).2).1
    exact mem_inf.mpr ⟨mul_mem (le_normalizer ht) hdN, mul_mem (hT.1 ht) hdX⟩
  · obtain ⟨t, ht, d, hd, rfl⟩ := hsub hx
    obtain ⟨-, hdD⟩ := mem_inf.mp hd
    have hdC : d ∈ centralizer (V : Set G) := (mem_inf.mp hdD).2
    refine mul_mem (hTU ht) ?_
    rw [mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← mem_centralizer_iff.mp hdC u (hUV hu), mul_inv_cancel_right]
      exact hu
    · intro hu
      have h1 := mem_centralizer_iff.mp hdC _ (hUV hu)
      have h2 : u = d * u * d⁻¹ := by
        calc u = d⁻¹ * (d * u * d⁻¹) * d := by group
          _ = d⁻¹ * (d * (d * u * d⁻¹)) := by rw [mul_assoc, h1]
          _ = d * u * d⁻¹ := by group
      rw [h2]
      exact hu

end CFSG.Quasithin.H13.NQCore
