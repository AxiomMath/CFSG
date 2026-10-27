module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
public import CFSG.Quasithin.EmptyFaithful.S152FinShape

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sign_eq_one_of_pow_eq_one {α : Type*} [DecidableEq α] [Fintype α] {σ : Perm α} {m : ℕ}
    (hm : Odd m) (h : σ ^ m = 1) : Perm.sign σ = 1 := by
  have h1 : Perm.sign σ ^ m = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_toPerm {H : Subgroup G} (hq : Nonempty (OTwoQuot H ≃* Perm (Fin 5))) :
    ∃ φ : ↥H →* Perm (Fin 5), Function.Surjective φ ∧
      ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  obtain ⟨ι⟩ := hq
  refine ⟨ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)),
    ι.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  have h1 : (x ∈ CFSG.Open.pCore 2 ↥H) ↔ (x : G) ∈ pCoreOf 2 H := by
    rw [← S152Fin.pCoreOf_subgroupOf H, Subgroup.mem_subgroupOf]
  show ι (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, h1]

variable [Finite G]

theorem cSecIn_eq_pCoreOf_of_noncentral {H : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5)))
    {U L N : Subgroup G} (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) (hs : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) : cSecIn H L N = pCoreOf 2 H := by
  obtain ⟨φ, hφs, hφk⟩ := exists_toPerm hq
  have hHL := normalizer_left hs
  have hHN := normalizer_right hs
  have hQC := pCoreOf_le_cSecIn_of_chiefStep hUH hUQ hs
  have hCH : cSecIn H L N ≤ H := (Subgroup.closure_le H).mpr fun _ hx => hx.1
  by_contra hne
  obtain ⟨c, hcC, hcQ⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hQC (Ne.symm hne))
  have hCn : ((cSecIn H L N).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCH]
    intro y g hy hg
    rw [mem_cSecIn_iff hHL] at hy ⊢
    refine ⟨H.mul_mem (H.mul_mem hg hy.1) (H.inv_mem hg), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ N := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) x).mp hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHL hg) _).mp (hy.2 _ hx')
    have e : g * (y * (g⁻¹ * x * g) * y⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ =
        (g * y * g⁻¹) * x * (g * y * g⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h1
  set K : Subgroup (Perm (Fin 5)) := Subgroup.map φ ((cSecIn H L N).subgroupOf H)
  have : K.Normal := Subgroup.Normal.map hCn φ hφs
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hcH : c ∈ H := hCH hcC
    have hmem : φ ⟨c, hcH⟩ ∈ K := Subgroup.mem_map_of_mem φ
      (show (⟨c, hcH⟩ : ↥H) ∈ (cSecIn H L N).subgroupOf H from hcC)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hcQ ((hφk ⟨c, hcH⟩).mp hmem)
  have hAK := F53.normal_ge_alt5 K hKne
  have hO : oTwoUpper H ≤ cSecIn H L N := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    have hsign : Perm.sign (φ ⟨x, hxH⟩) = 1 := by
      refine sign_eq_one_of_pow_eq_one hxo ?_
      rw [← map_pow]
      have : (⟨x, hxH⟩ : ↥H) ^ orderOf x = 1 := Subtype.ext (by simp)
      rw [this, map_one]
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hAK (Perm.mem_alternatingGroup.mpr hsign))
    have hyC : (y : G) ∈ cSecIn H L N := hy
    have h1 : φ (y⁻¹ * ⟨x, hxH⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h3 := (cSecIn H L N).mul_mem hyC (hQC ((hφk _).mp h1))
    simpa using h3
  have hP : ⁅N, oTwoUpper H⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro n hn p hp
    have h := ((mem_cSecIn_iff hHL).mp (hO hp)).2 n hn
    have e : ⁅n, p⁆ = (p * n * p⁻¹ * n⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact L.inv_mem h
  obtain ⟨T, hT, hQT⟩ := F1.exists_isSylowTwoOf_ge (pCoreOf_le 2 H) (pCoreOf_isPGroup 2 H)
  exact hnc (D15Proof.isCentralStep_of_commutator_le hT hUH (hs.1.1.trans (hUQ.trans hQT)) hs hP)

end CFSG.Quasithin.F53Mod
