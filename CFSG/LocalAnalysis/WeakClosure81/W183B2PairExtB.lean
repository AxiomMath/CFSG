module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem w183b2_card_image_mk {L : Type} [Group L] [Finite L] (N S : Subgroup L) [N.Normal] :
    Nat.card (S.map (QuotientGroup.mk' N)) = (N ⊓ S).relIndex S := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.inf_relIndex_right]

variable {G : Type} [Group G] [Finite G]

theorem w183b2_pq_ne {P Q M₁ M₂ K : Subgroup G} [(K.subgroupOf (P ⊔ Q)).Normal]
    (hPM : P ≤ M₁) (hnot : ¬ Q ≤ M₁)
    (hK : (K : Set G) = ((Q ⊓ M₁ : Subgroup G) : Set G) * ((P ⊓ M₂ : Subgroup G) : Set G)) :
    (P.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))) ≠
      (Q.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))) := by
  intro heq
  apply hnot
  intro q hq
  have hqL : q ∈ P ⊔ Q := Subgroup.mem_sup_right hq
  have hmem : QuotientGroup.mk' (K.subgroupOf (P ⊔ Q)) (⟨q, hqL⟩ : ↥(P ⊔ Q)) ∈
      (Q.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)
  rw [← heq] at hmem
  obtain ⟨p', hp', hpq⟩ := Subgroup.mem_map.1 hmem
  have hp : (p' : G) ∈ P := Subgroup.mem_subgroupOf.1 hp'
  have hk : p'⁻¹ * (⟨q, hqL⟩ : ↥(P ⊔ Q)) ∈ K.subgroupOf (P ⊔ Q) := QuotientGroup.eq.1 hpq
  have hconj := (inferInstance : (K.subgroupOf (P ⊔ Q)).Normal).conj_mem _ hk p'
  have hqp : q * (p' : G)⁻¹ ∈ K := by
    have h1 := Subgroup.mem_subgroupOf.1 hconj
    have h2 : ((p' * (p'⁻¹ * (⟨q, hqL⟩ : ↥(P ⊔ Q))) * p'⁻¹ : ↥(P ⊔ Q)) : G) =
        q * (p' : G)⁻¹ := by
      simp [mul_assoc]
    rwa [h2] at h1
  have hqp' : q * (p' : G)⁻¹ ∈ (K : Set G) := hqp
  rw [hK] at hqp'
  obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.1 hqp'
  have hu' : u ∈ Q ⊓ M₁ := hu
  have hw' : w ∈ P ⊓ M₂ := hw
  have hq_eq : q = u * (w * (p' : G)) := by
    have h1 : u * w = q * (p' : G)⁻¹ := huw
    calc q = q * (p' : G)⁻¹ * (p' : G) := by group
      _ = u * w * (p' : G) := by rw [← h1]
      _ = u * (w * (p' : G)) := by group
  have hwpQ : w * (p' : G) ∈ Q := by
    have h1 : w * (p' : G) = u⁻¹ * q := by
      rw [hq_eq]; group
    rw [h1]
    exact Q.mul_mem (Q.inv_mem (Subgroup.mem_inf.1 hu').1) hq
  have hwpP : w * (p' : G) ∈ P := P.mul_mem (Subgroup.mem_inf.1 hw').1 hp
  rw [hq_eq]
  exact M₁.mul_mem (Subgroup.mem_inf.1 hu').2 (hPM hwpP)

theorem w183b2_pq_card_conj {P Q K : Subgroup G} [(K.subgroupOf (P ⊔ Q)).Normal]
    (hconj : ∃ l ∈ P ⊔ Q, Q = conjSubgroup P l) :
    Nat.card ((Q.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q)))) =
      Nat.card ((P.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q)))) := by
  obtain ⟨l, hl, hQ⟩ := hconj
  let l' : ↥(P ⊔ Q) := ⟨l, hl⟩
  let π₀ : ↥(P ⊔ Q) →* ↥(P ⊔ Q) ⧸ K.subgroupOf (P ⊔ Q) :=
    QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))
  have hQmem : ∀ y : G, y ∈ Q ↔ l * y * l⁻¹ ∈ P := by
    intro y
    rw [hQ]
    exact mem_conjSubgroup_iff
  have hmem : ∀ x : ↥(P ⊔ Q), x ∈ Q.subgroupOf (P ⊔ Q) ↔
      l' * x * l'⁻¹ ∈ P.subgroupOf (P ⊔ Q) := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hQmem]
    rfl
  have hEq : (Q.subgroupOf (P ⊔ Q)).map π₀ =
      ((P.subgroupOf (P ⊔ Q)).map π₀).map (MulAut.conj (π₀ l')⁻¹).toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨π₀ (l' * x * l'⁻¹),
        Subgroup.mem_map.2 ⟨_, (hmem x).1 hx, rfl⟩, ?_⟩
      simp [map_mul, map_inv, mul_assoc]
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hz
      refine Subgroup.mem_map.2 ⟨l'⁻¹ * p * l', ?_, ?_⟩
      · rw [hmem]
        have h1 : l' * (l'⁻¹ * p * l') * l'⁻¹ = p := by group
        rw [h1]
        exact hp
      · simp [map_mul, map_inv, mul_assoc]
  rw [hEq]
  exact Subgroup.card_map_of_injective (MulAut.conj (π₀ l')⁻¹).injective

end CFSG.LocalAnalysis.WeakClosure81

end
