module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Aux
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

@[expose] def K9For (J : Type) [Group J] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], SectionFourHyp S → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 →
      ∀ C P : Subgroup S, (∀ x, x ∈ C ↔ σ x = x) → P ≤ C → (P.subgroupOf C).IsSubnormal →
        Group.IsPerfect P → ∀ (N : Subgroup P) [N.Normal], IsEmpty (P ⧸ N ≃* J)

@[expose] def fixedSubgroup {X : Type*} [Group X] (σ : MulAut X) : Subgroup X where
  carrier := {x | σ x = x}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, map_inv] at *
    rw [ha]

theorem mem_fixedSubgroup {X : Type*} [Group X] {σ : MulAut X} {x : X} :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

theorem exists_lift_of_surjective {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (f : G₁ →* G₂) (hf : Function.Surjective f) (g : G₁ →* G₃) (hg : f.ker ≤ g.ker) :
    ∃ h : G₂ →* G₃, ∀ x, h (f x) = g x :=
  ⟨f.liftOfSurjective hf ⟨g, hg⟩, fun x =>
    f.liftOfRightInverse_comp_apply (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨g, hg⟩ x⟩

theorem false_of_perfect_fixed {J : Type} [Group J] (hJ : J2Facts J) (hK9 : K9For J)
    {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hS : SectionFourHyp (X ⧸ Subgroup.center X)) (σ : MulAut X) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) (P : Subgroup X) (hPfix : ∀ x ∈ P, σ x = x) (hPperf : Group.IsPerfect P)
    (hPsub : SubnormalIn P (fixedSubgroup σ)) (ψ : P →* J) (hψ : Function.Surjective ψ) :
    False := by
  haveI : Group.IsPerfect X := hX.1
  haveI := hPperf
  set Z := Subgroup.center X with hZ
  let σb : MulAut (X ⧸ Z) := mulAutQuotientHom Z σ
  have hσb : ∀ x : X, σb (x : X ⧸ Z) = ((σ x : X) : X ⧸ Z) := fun x => rfl
  have hσb3 : σb ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hσb1 : σb ≠ 1 := by
    intro h1
    apply hσ1
    refine KFacts.eq_one_of_forall_mul_inv_mem_center fun x => ?_
    have h := congrArg (fun τ : MulAut (X ⧸ Z) => τ (x : X ⧸ Z)) h1
    simp only [hσb, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  have hPC : P ≤ fixedSubgroup σ := fun x hx => hPfix x hx
  have hC0 : (fixedSubgroup σ).map (QuotientGroup.mk' Z) ≤ fixedSubgroup σb := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hσb c).trans (by rw [mem_fixedSubgroup.mp hc]; rfl)
  have hnorm : SubnormalIn ((fixedSubgroup σ).map (QuotientGroup.mk' Z)) (fixedSubgroup σb) := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := hn
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g : X ⧸ Z)
    have h1 : ((σ x : X) : X ⧸ Z) = (x : X ⧸ Z) := by
      have h2 := mem_fixedSubgroup.mp g.2
      rw [← hx] at h2
      exact h2
    have hz : x⁻¹ * σ x ∈ Z := QuotientGroup.eq.mp h1.symm
    have hzc := Subgroup.mem_center_iff.mp hz
    have hσx : σ x = x * (x⁻¹ * σ x) := by group
    have hCx : x * c * x⁻¹ ∈ fixedSubgroup σ := by
      rw [mem_fixedSubgroup, map_mul, map_mul, map_inv, mem_fixedSubgroup.mp hc]
      calc σ x * c * (σ x)⁻¹ = (x * (x⁻¹ * σ x)) * c * (x * (x⁻¹ * σ x))⁻¹ := by rw [← hσx]
        _ = x * ((x⁻¹ * σ x) * c) * (x⁻¹ * σ x)⁻¹ * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * σ x)) * (x⁻¹ * σ x)⁻¹ * x⁻¹ := by rw [hzc c]
        _ = x * c * x⁻¹ := by group
    refine ⟨x * c * x⁻¹, hCx, ?_⟩
    change (QuotientGroup.mk' Z) (x * c * x⁻¹) = (g : X ⧸ Z) * (n : X ⧸ Z) * (g : X ⧸ Z)⁻¹
    rw [map_mul, map_mul, map_inv, hcn, ← hx]
    rfl
  have hPb_le : P.map (QuotientGroup.mk' Z) ≤ (fixedSubgroup σ).map (QuotientGroup.mk' Z) :=
    Subgroup.map_mono hPC
  have hsub : SubnormalIn (P.map (QuotientGroup.mk' Z)) (fixedSubgroup σb) :=
    SubnormalIn.trans hPb_le hC0 (SubnormalIn.map hPC (QuotientGroup.mk' Z) hPsub) hnorm
  haveI hPbperf : Group.IsPerfect (P.map (QuotientGroup.mk' Z)) :=
    Group.IsPerfect.map (QuotientGroup.mk' Z)
  have hker : ((QuotientGroup.mk' Z).subgroupMap P).ker ≤ ψ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have hpZ : (p : X) ∈ Z := by
      have h1 : (QuotientGroup.mk' Z) (p : X) = 1 := congrArg Subtype.val hp
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcen : ψ p ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      obtain ⟨q, rfl⟩ := hψ j
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hpZ q)
    rw [hJ.center] at hcen
    exact hcen
  obtain ⟨ψb, hψb⟩ := exists_lift_of_surjective _ (MonoidHom.subgroupMap_surjective _ P) ψ hker
  have hψbs : Function.Surjective ψb := by
    intro j
    obtain ⟨p, rfl⟩ := hψ j
    exact ⟨_, hψb p⟩
  have hempty := hK9 (X ⧸ Z) hS hX.2.1 hX.2.2 σb hσb3 hσb1 (fixedSubgroup σb)
    (P.map (QuotientGroup.mk' Z)) (fun x => Iff.rfl) (hPb_le.trans hC0) hsub hPbperf ψb.ker
  exact hempty.false (QuotientGroup.quotientKerEquivOfSurjective ψb hψbs)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
