module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43l
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43k

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem V_cen_B (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {V : Subgroup G} (hV : IsSylowOf 2 V (Opp 3 (Cen b))) :
    ∀ β ∈ B, ∀ y ∈ V, β * y * β⁻¹ = y := by
  intro β hβ y hy
  rw [Subgroup.mem_centralizer_iff.1 (X_le_cenS_B hA h (hV.1 hy)) β hβ]
  group

theorem Tstar_B_inv (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {V : Subgroup G} (hV : IsSylowOf 2 V (Opp 3 (Cen b))) :
    ∀ z ∈ Op 2 (Nor V), ∀ β ∈ B, β * z * β⁻¹ ∈ Op 2 (Nor V) := by
  intro z hz β hβ
  have hβN : β ∈ Nor V :=
    FF79.L41.mem_nor_of_forall (fun y hy => by rw [V_cen_B hA h hV β hβ y hy]; exact hy)
  exact FF79.L41.Op_conj_mem hβN hz

theorem tstar_cen_bb₁ (h23 : FF84_2_3) (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (hC : CommTheta b b₁ b₂) {V : Subgroup G}
    (hV : IsSylowOf 2 V (Opp 3 (Cen b))) : Op 2 (Nor V) ⊓ Cen (b * b₁) ≤ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro w ⟨hwT, hwD⟩
  have hb : w * b = b * w :=
    W_comm_E h23 hA h hC (FF79.L41.Op_isPGroup _) (fun t ht β hβ => Tstar_B_inv hA h hV t ht β hβ)
      hwT hwD b (Subgroup.subset_closure (by simp))
  exact tstar_cen_b hA h hV ⟨hwT, Subgroup.mem_centralizer_singleton_iff.2 hb⟩

theorem tstar_cen_bb₁sq (h23 : FF84_2_3) (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (hC : CommTheta b b₁ b₂) {V : Subgroup G}
    (hV : IsSylowOf 2 V (Opp 3 (Cen b))) : Op 2 (Nor V) ⊓ Cen (b * b₁ ^ 2) ≤ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  obtain ⟨x, hxL, hx⟩ := exists_inv_b₁ hA h hθ
  have hXL : Opp 3 (Cen b) ≤ CenS L := X_le_cenS_L h.hyp hA
  have hVL : ∀ l ∈ L, ∀ y ∈ V, l * y * l⁻¹ = y := by
    intro l hl y hy
    rw [Subgroup.mem_centralizer_iff.1 (hXL (hV.1 hy)) l hl]
    group
  have hLN : ∀ l ∈ L, l ∈ Nor V := fun l hl =>
    FF79.L41.mem_nor_of_forall (fun y hy => by rw [hVL l hl y hy]; exact hy)
  rintro z ⟨hzT, hzc⟩
  have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hxL)
  have hxb' : x * b * x⁻¹ = b := by
    calc x * b * x⁻¹ = b * x * x⁻¹ := by rw [hxb]
      _ = b := by group
  have hb₁inv : (b₁⁻¹) ^ 2 = b₁ := by
    have h3 := pow3_of_mem h (mem_b₁ h)
    calc (b₁⁻¹) ^ 2 = b₁ * (b₁ ^ 3)⁻¹ := by group
      _ = b₁ := by rw [h3]; group
  have hxc : x * (b * b₁ ^ 2) * x⁻¹ = b * b₁ := by
    calc x * (b * b₁ ^ 2) * x⁻¹ = (x * b * x⁻¹) * (x * b₁ ^ 2 * x⁻¹) := by group
      _ = (x * b * x⁻¹) * (x * b₁ * x⁻¹) ^ 2 := by rw [conj_pow]
      _ = b * b₁ := by rw [hxb', hx, hb₁inv]
  have hz : z * (b * b₁ ^ 2) = (b * b₁ ^ 2) * z := Subgroup.mem_centralizer_singleton_iff.1 hzc
  have hz'T : x * z * x⁻¹ ∈ Op 2 (Nor V) := FF79.L41.Op_conj_mem (hLN x hxL) hzT
  have hz'D : x * z * x⁻¹ ∈ Cen (b * b₁) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * z * x⁻¹ * (b * b₁) = x * z * x⁻¹ * (x * (b * b₁ ^ 2) * x⁻¹) := by rw [hxc]
      _ = x * (z * (b * b₁ ^ 2)) * x⁻¹ := by group
      _ = x * ((b * b₁ ^ 2) * z) * x⁻¹ := by rw [hz]
      _ = (x * (b * b₁ ^ 2) * x⁻¹) * (x * z * x⁻¹) := by group
      _ = (b * b₁) * (x * z * x⁻¹) := by rw [hxc]
  have hz'V : x * z * x⁻¹ ∈ V := tstar_cen_bb₁ h23 hA h hC hV ⟨hz'T, hz'D⟩
  have := hVL x⁻¹ (inv_mem hxL) _ hz'V
  have hzz : z = x * z * x⁻¹ := by
    calc z = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by group
      _ = x * z * x⁻¹ := this
  rw [hzz]; exact hz'V

@[expose] def S43_TstarCen₁ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ V : Subgroup G, IsSylowOf 2 V (Opp 3 (Cen b)) → V ≠ ⊥ →
      Op 2 (Nor V) ⊓ Cen b₁ ≤ V

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
