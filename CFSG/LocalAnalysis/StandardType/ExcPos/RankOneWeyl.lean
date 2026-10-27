module

public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootMono

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem canonicalRep_mem_centralizer_rootSpan_pair_of_smul_eq
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {v : WeylGroup τ} (hv : v • γ = γ) :
    canonicalRep (coxeterSystem τ) L v ∈
      Subgroup.centralizer (rootSpan τ L {γ, -γ} : Set (ModGL τ L)) := by
  have hconj : ∀ (u : WeylGroup τ) {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ c : L,
      canonicalRep (coxeterSystem τ) L u * pinnedX τ L β c *
        (canonicalRep (coxeterSystem τ) L u)⁻¹ = pinnedX τ L (u • β) c := by
    intro u β hβ c
    obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L u hβ
    have hε1 : ε = 1 := by
      have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
      have h : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
    rw [hεc, hε1, one_mul]
  have hγ' : v • (-γ) = -γ := by rw [smul_neg, hv]
  have hcommγ : ∀ c : L, Commute (canonicalRep (coxeterSystem τ) L v) (pinnedX τ L γ c) := by
    intro c
    have h := hconj v hγ c
    rw [hv] at h
    refine (commute_iff_eq _ _).2 ?_
    calc
      canonicalRep (coxeterSystem τ) L v * pinnedX τ L γ c =
          (canonicalRep (coxeterSystem τ) L v * pinnedX τ L γ c *
            (canonicalRep (coxeterSystem τ) L v)⁻¹) * canonicalRep (coxeterSystem τ) L v := by
        group
      _ = pinnedX τ L γ c * canonicalRep (coxeterSystem τ) L v := by rw [h]
  have hcommγ' : ∀ c : L, Commute (canonicalRep (coxeterSystem τ) L v) (pinnedX τ L (-γ) c) := by
    intro c
    have h := hconj v (IsRoot.neg hγ) c
    rw [hγ'] at h
    refine (commute_iff_eq _ _).2 ?_
    calc
      canonicalRep (coxeterSystem τ) L v * pinnedX τ L (-γ) c =
          (canonicalRep (coxeterSystem τ) L v * pinnedX τ L (-γ) c *
            (canonicalRep (coxeterSystem τ) L v)⁻¹) * canonicalRep (coxeterSystem τ) L v := by
        group
      _ = pinnedX τ L (-γ) c * canonicalRep (coxeterSystem τ) L v := by rw [h]
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact (commute_of_mem_rootSpan_pair hcommγ hcommγ' y hy).eq.symm

theorem exists_mem_rootSpan_mul_centralizer_of_smul_eq
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {w : WeylGroup τ}
    (hw : w • γ = γ ∨ w • γ = -γ) :
    ∃ h ∈ rootSpan τ L {γ, -γ},
      ∃ c ∈ Subgroup.centralizer (rootSpan τ L {γ, -γ} : Set (ModGL τ L)),
        canonicalRep (coxeterSystem τ) L w = h * c := by
  rcases hw with hw | hw
  · refine ⟨1, one_mem _, canonicalRep (coxeterSystem τ) L w,
      canonicalRep_mem_centralizer_rootSpan_pair_of_smul_eq (τ := τ) (L := L) hγ hw, ?_⟩
    rw [one_mul]
  · set r := rootReflection γ with hr
    set u := r * w with hu
    have hrm : r * r = 1 := rootReflection_mul_self hγ
    have hdecomp : w = r * u := by
      rw [show u = r * w from rfl, ← mul_assoc, hrm, one_mul]
    have hrn : r • (-γ) = γ := by
      rw [← rootReflection_smul_self hγ, ← mul_smul, hrm, one_smul]
    have huγ : u • γ = γ := by
      rw [hu, mul_smul, hw, hrn]
    have hh : canonicalRep (coxeterSystem τ) L r ∈ rootSpan τ L {γ, -γ} := by
      rw [hr, canonicalRep_rootReflection_eq_charTwo hγ]
      exact mul_mem (mul_mem (pinnedX_mem_rootSpan (by simp) 1)
        (pinnedX_mem_rootSpan (by simp) 1)) (pinnedX_mem_rootSpan (by simp) 1)
    have hc : canonicalRep (coxeterSystem τ) L u ∈
        Subgroup.centralizer (rootSpan τ L {γ, -γ} : Set (ModGL τ L)) :=
      canonicalRep_mem_centralizer_rootSpan_pair_of_smul_eq (τ := τ) (L := L) hγ huγ
    refine ⟨canonicalRep (coxeterSystem τ) L r, hh,
      canonicalRep (coxeterSystem τ) L u, hc, ?_⟩
    rw [hdecomp, CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]

theorem canonicalRep_mem_sup_centralizer_rootSpan_pair_of_smul_eq
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {w : WeylGroup τ}
    (hw : w • γ = γ ∨ w • γ = -γ) :
    canonicalRep (coxeterSystem τ) L w ∈
      rootSpan τ L {γ, -γ} ⊔
        Subgroup.centralizer (rootSpan τ L {γ, -γ} : Set (ModGL τ L)) := by
  obtain ⟨h, hh, c, hc, hw_eq⟩ := exists_mem_rootSpan_mul_centralizer_of_smul_eq (τ := τ) (L := L) hγ hw
  rw [hw_eq]
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hc)

end CFSG.StandardType.LieKnownR2.ExcPos
