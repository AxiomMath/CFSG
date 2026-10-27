module

public import CFSG.RankThree.GF2n.Stroth80.Sec717CorBHypProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem conjSubgroup_eq_of_sylow {X : Type*} [Group X] [Finite X] {L V : Subgroup X} {h : X}
    (hLV : ∀ k ∈ normalizer (conjSubgroup h V : Set X),
      conjSubgroup k (conjSubgroup h L) = conjSubgroup h L)
    (S : Sylow 2 X) (hSL : (S : Subgroup X) ≤ normalizer (L : Set X))
    (hSLh : (S : Subgroup X) ≤ normalizer (conjSubgroup h L : Set X))
    (hN : normalizer ((S : Subgroup X) : Set X) ≤ normalizer (conjSubgroup h V : Set X)) :
    conjSubgroup h L = L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsmul : ∀ (g : X) (P : Sylow 2 X),
      ((g • P : Sylow 2 X) : Subgroup X) = conjSubgroup g (P : Subgroup X) := fun g P => rfl
  have hS'N : ((h⁻¹ • S : Sylow 2 X) : Subgroup X) ≤ normalizer (L : Set X) := by
    rw [hsmul]
    intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    have h1 : conjSubgroup (h * x * h⁻¹) (conjSubgroup h L) = conjSubgroup h L :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hSLh hx)
    rw [conjSubgroup_conjSubgroup] at h1
    have h2 := congrArg (conjSubgroup h⁻¹) h1
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h2
    rw [mem_normalizer_iff_conjSubgroup_eq]
    convert h2 using 2
    group
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (normalizer (L : Set X))
    ((h⁻¹ • S : Sylow 2 X).subtype hS'N) (S.subtype hSL)
  rw [Sylow.smul_subtype] at hc
  have hc' : (c : X) • (h⁻¹ • S : Sylow 2 X) = S := Sylow.subtype_injective hc
  rw [← mul_smul, Sylow.smul_eq_iff_mem_normalizer] at hc'
  have hn := hLV _ (hN hc')
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right] at hn
  have hcL : conjSubgroup (c : X) L = L := mem_normalizer_iff_conjSubgroup_eq.mp c.2
  rw [← hn, hcL]

section Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.conjSubgroup_conj_L (F : MoveFrame B φ V L Nb Rb Tt q) (h : X) :
    ∀ k ∈ normalizer (conjSubgroup h V : Set X),
      conjSubgroup k (conjSubgroup h L) = conjSubgroup h L := by
  intro k hk
  have h1 : conjSubgroup k (conjSubgroup h V) = conjSubgroup h V :=
    mem_normalizer_iff_conjSubgroup_eq.mp hk
  have h2 : conjSubgroup (h⁻¹ * k * h) V = V := by
    have := congrArg (conjSubgroup h⁻¹) h1
    rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      inv_mul_cancel, conjSubgroup_one] at this
  have hkN : h⁻¹ * k * h ∈ normalizer (V : Set X) := mem_normalizer_iff_conjSubgroup_eq.mpr h2
  have hkN' : (h⁻¹ * k * h)⁻¹ ∈ normalizer (V : Set X) := inv_mem hkN
  have h3 : conjSubgroup (h⁻¹ * k * h) L = L := by
    ext x
    rw [mem_conjSubgroup]
    constructor
    · intro hx
      have := F.L_norm _ hkN _ hx
      simpa [mul_assoc] using this
    · intro hx
      simpa [mul_assoc] using F.L_norm _ hkN' x hx
  calc conjSubgroup k (conjSubgroup h L) = conjSubgroup h (conjSubgroup (h⁻¹ * k * h) L) := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup h L := by rw [h3]

end Frame


@[expose] def Sec717NormSylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    ∀ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), z ≠ 1 →
      ∀ h : ↥(bar M Q (H0 M Z)),
        h * z * h⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) →
        h * z * h⁻¹ ∉ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) →
          ∃ S : Sylow 2 ↥(bar M Q (H0 M Z)),
            (S : Subgroup ↥(bar M Q (H0 M Z))) ≤ Subgroup.normalizer
                ((bar M Q L).subgroupOf (bar M Q (H0 M Z)) : Set ↥(bar M Q (H0 M Z))) ∧
              (S : Subgroup ↥(bar M Q (H0 M Z))) ≤ Subgroup.normalizer
                (conjSubgroup h ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) :
                  Set ↥(bar M Q (H0 M Z))) ∧
              Subgroup.normalizer ((S : Subgroup ↥(bar M Q (H0 M Z))) :
                  Set ↥(bar M Q (H0 M Z))) ≤ Subgroup.normalizer
                (conjSubgroup h ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) :
                  Set ↥(bar M Q (H0 M Z)))

theorem sec717Normalize_of_sylow (hF : Sec717MoveFrameStatement)
    (hSyl : Sec717NormSylowStatement) : Sec717NormalizeStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 h hhz hhzV
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  obtain ⟨S, hSL, hSLh, hN⟩ :=
    hSyl G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 h hhz hhzV
  exact conjSubgroup_eq_of_sylow (F.conjSubgroup_conj_L h) S hSL hSLh hN

end CFSG.RankThree.GF2n.Stroth80
