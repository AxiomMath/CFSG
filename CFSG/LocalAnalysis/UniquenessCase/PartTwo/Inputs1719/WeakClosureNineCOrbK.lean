module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbFam
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace OrbData

variable {Lb Tb A C F H₁ X₁ : Subgroup X} {p : ℕ} (d : OrbData Lb Tb A C F H₁ X₁ p)
include d

omit [Finite X] in
theorem S_le_normalizer_H : orbS Tb A C F H₁ ≤ normalizer (orb C H₁ : Set X) :=
  orbS_le_orbK.trans (d.K_le_normalizer le_rfl)

omit [Finite X] in
theorem K_le_normalizer_R :
    orbK Tb A C F H₁ ≤ normalizer (orb C (pCoreOf 2 H₁) : Set X) :=
  d.K_le_normalizer (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H₁)

theorem K_le_normalizer_Z :
    orbK Tb A C F H₁ ≤ normalizer (orb C (pCoreOf 2 H₁ ⊔ X₁) : Set X) :=
  d.K_le_normalizer d.normalizer_le_Z

theorem K_eq : orbK Tb A C F H₁ = orb C (pCoreOf 2 H₁ ⊔ X₁) ⊔ orbS Tb A C F H₁ := by
  apply le_antisymm
  · refine sup_le (orb_le fun c hc h hh => ?_) le_sup_right
    have hh' : h ∈ (conjSub c (H₁ ⊓ Tb) : Set X) * (conjSub c X₁ : Set X) := by
      rw [← TwoPTwo.mul_eq (d.irr_conjSub c).toTwoPTwo]
      exact hh
    obtain ⟨s, hs, x, hx, rfl⟩ := Set.mem_mul.1 hh'
    exact mul_mem (mem_sup_right (mem_sup_left (mem_sup_left (conjSub_le_orb hc hs))))
      (mem_sup_left (conjSub_le_orb hc (conjSub_mono _ le_sup_right hx)))
  · exact sup_le ((orb_mono (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H₁) d.X_le_H)).trans
      orb_le_orbK) orbS_le_orbK

theorem oTwoPTwo_K : E1.oTwoPTwo ↥(orbK Tb A C F H₁) p = ⊤ := by
  have : Fact p.Prime := ⟨d.irr.prime⟩
  have hKR := d.K_le_normalizer_R
  have hKZ := d.K_le_normalizer_Z
  have : ((orb C (pCoreOf 2 H₁)).subgroupOf (orbK Tb A C F H₁)).Normal :=
    normal_subgroupOf_of_le_normalizer hKR
  have : ((orb C (pCoreOf 2 H₁ ⊔ X₁)).subgroupOf (orbK Tb A C F H₁)).Normal :=
    normal_subgroupOf_of_le_normalizer hKZ
  refine E1.oTwoPTwo_eq_top_of_series
    (N₂ := (orb C (pCoreOf 2 H₁)).subgroupOf (orbK Tb A C F H₁))
    (N₂p := (orb C (pCoreOf 2 H₁ ⊔ X₁)).subgroupOf (orbK Tb A C F H₁)) ?_ ?_ ?_
  · exact (d.T2.to_le d.R_le_T).comap_of_injective _ (orbK Tb A C F H₁).subtype_injective
  · intro x hx
    have hZ : (orb C (pCoreOf 2 H₁ ⊔ X₁) : Set X) =
        (orb C X₁ : Set X) * (orb C (pCoreOf 2 H₁) : Set X) := by
      rw [orb_sup, sup_comm]
      exact coe_mul_of_left_le_normalizer_right _ _ (d.XB_le_K.trans hKR)
    have hx' : (x : X) ∈ (orb C (pCoreOf 2 H₁ ⊔ X₁) : Set X) := hx
    rw [hZ] at hx'
    obtain ⟨y, hy, r, hr, hyr⟩ := Set.mem_mul.1 hx'
    obtain ⟨o, ho, he⟩ := E1.mul_pow_eq_of_mem_normalizer (hKR (d.XB_le_K hy)) hr p
    refine ⟨1, ?_⟩
    rw [mem_subgroupOf, coe_pow, pow_one, ← hyr, he, d.XB_elem.2 y hy, one_mul]
    exact ho
  · intro q
    have hK : (orbK Tb A C F H₁ : Set X) =
        (orbS Tb A C F H₁ : Set X) * (orb C (pCoreOf 2 H₁ ⊔ X₁) : Set X) := by
      rw [d.K_eq, sup_comm]
      exact coe_mul_of_left_le_normalizer_right _ _ (orbS_le_orbK.trans hKZ)
    have hq : (q : X) ∈ (orbK Tb A C F H₁ : Set X) := q.2
    rw [hK] at hq
    obtain ⟨s, hs, z, hz, hsz⟩ := Set.mem_mul.1 hq
    obtain ⟨k, hk⟩ := d.S_isPGroup ⟨s, hs⟩
    obtain ⟨o, ho, he⟩ := E1.mul_pow_eq_of_mem_normalizer (hKZ (orbS_le_orbK hs)) hz (2 ^ k)
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [mem_subgroupOf, coe_pow, ← hsz, he, hk', one_mul]
    exact ho

theorem sylowTwo_K : IsSylowIn 2 (orbK Tb A C F H₁ ⊓ Tb) (orbK Tb A C F H₁) := by
  refine ⟨inf_le_left, d.T2.to_le inf_le_right, fun h2 => ?_⟩
  have h1 := relIndex_dvd_of_le_left (orbK Tb A C F H₁) (le_inf orbS_le_orbK d.S_le_T)
  have h3 : (orbS Tb A C F H₁).relIndex (orbK Tb A C F H₁) =
      (orbS Tb A C F H₁ ⊓ orb C H₁).relIndex (orb C H₁) := by
    rw [orbK, sup_comm]
    exact (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer d.S_le_normalizer_H).1
  have h4 := relIndex_dvd_of_le_left (orb C H₁)
    (le_inf (le_sup_left.trans le_sup_left : orb C (H₁ ⊓ Tb) ≤ orbS Tb A C F H₁)
      (orb_mono inf_le_left))
  have : Fintype C := Fintype.ofFinite C
  classical
  refine not_dvd_relIndex_iSup (d.pairwise d.H_le) Nat.prime_two
    (P := fun i : C => conjSub (i : X) (H₁ ⊓ Tb)) (fun _ => conjSub_mono _ inf_le_left)
    (fun i => (d.irr_conjSub i).sylowTwo.not_dvd_relIndex) ?_
  exact h2.trans (h1.trans (h3 ▸ h4))

theorem sylowP_K : IsSylowIn p (orb C X₁) (orbK Tb A C F H₁) := by
  refine ⟨d.XB_le_K, d.XB_elem.isPGroup, fun hp => ?_⟩
  rw [← relIndex_mul_relIndex _ _ _ (orb_mono d.X_le_H) orb_le_orbK] at hp
  rcases (Nat.Prime.dvd_mul d.irr.prime).1 hp with h | h
  · have : Fintype C := Fintype.ofFinite C
    classical
    exact not_dvd_relIndex_iSup (d.pairwise d.H_le) d.irr.prime
      (P := fun i : C => conjSub (i : X) X₁) (fun _ => conjSub_mono _ d.X_le_H)
      (fun i => (d.irr_conjSub i).sylowP.not_dvd_relIndex) h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h3 : (orb C H₁).relIndex (orbK Tb A C F H₁) =
        (orbS Tb A C F H₁ ⊓ orb C H₁).relIndex (orbS Tb A C F H₁) := by
      rw [orbK, sup_comm]
      exact (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer d.S_le_normalizer_H).2
    rw [h3] at h
    have h4 := h.trans (relIndex_dvd_card _ _)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 d.S_isPGroup
    rw [hn] at h4
    exact d.irr.odd ((Nat.prime_dvd_prime_iff_eq d.irr.prime Nat.prime_two).1
      (d.irr.prime.dvd_of_dvd_pow h4))

end OrbData

end CFSG.LocalAnalysis.WeakClosure81.TC914
