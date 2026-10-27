module

public import CFSG.RankThree.GF2n.Parrott.CaseIIDouble
public import CFSG.RankThree.GF2n.Parrott.Section4HPrimeIndex

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}


private theorem centerIn_le_commutator_A (h : Tim79a.ParrottHypA z) :
    centerIn (J z) ≤ ⁅H z, H z⁆ := by
  have hzJ : z ∈ ⁅J z, J z⁆ := by
    rw [h.commutator]
    exact Subgroup.mem_zpowers z
  have hzH : z ∈ ⁅H z, H z⁆ :=
    Subgroup.commutator_mono (J_le_H (z := z)) (J_le_H (z := z)) hzJ
  rw [centerIn_J_eq_zpowers_A h]
  exact Subgroup.zpowers_le_of_mem hzH

theorem J_le_commutator_of_not_equalityBranch_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    J z ≤ ⁅H z, H z⁆ := by
  let h2 : Tim79a.ParrottHyp (CaseIIDouble.zz z) := CaseIIDouble.parrottHyp_zz h
  let D2 : QuotientData (z := CaseIIDouble.zz z) (J_subgroupOf_normal (CaseIIDouble.zz z)) :=
    CaseIIDouble.quotientDataZZ D
  have hIII2 : ¬ ParrottEqualityBranch (z := CaseIIDouble.zz z) (D := D2) h2 :=
    fun hb => hIII ((CaseIIDouble.parrottEqualityBranch_zz_iff h2 D).mp hb)
  have hmain := J_le_commutator_sup_centerIn_of_not_equalityBranch
    (z := CaseIIDouble.zz z) h2 D2 hIII2
  rw [CaseIIDouble.centerIn_J_zz, CaseIIDouble.J_zz, CaseIIDouble.H_zz,
    Subgroup.commutator_prod_prod] at hmain
  have htop : ⁅(⊤ : Subgroup (Multiplicative (ZMod 2))),
      (⊤ : Subgroup (Multiplicative (ZMod 2)))⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr (by infer_instance)
  rw [htop] at hmain
  have hZle : centerIn (J z) ≤ ⁅H z, H z⁆ := centerIn_le_commutator_A h
  have hsup_le : (⁅H z, H z⁆.prod (⊥ : Subgroup (Multiplicative (ZMod 2)))) ⊔
      ((centerIn (J z)).prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) ≤
      (⁅H z, H z⁆).prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :=
    sup_le (Subgroup.prod_mono le_rfl bot_le) (Subgroup.prod_mono hZle le_rfl)
  intro j hj
  have hmem : ((j, 1) : CaseIIDouble.D2 G) ∈
      (⁅H z, H z⁆.prod (⊥ : Subgroup (Multiplicative (ZMod 2)))) ⊔
        ((centerIn (J z)).prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) :=
    hmain (Subgroup.mem_prod.mpr ⟨hj, Subgroup.mem_top 1⟩)
  exact (Subgroup.mem_prod.mp (hsup_le hmem)).1

theorem relIndex_commutator_of_not_equalityBranch_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ⁅H z, H z⁆.relIndex (H z) = 2 := by
  let h2 : Tim79a.ParrottHyp (CaseIIDouble.zz z) := CaseIIDouble.parrottHyp_zz h
  let D2 : QuotientData (z := CaseIIDouble.zz z) (J_subgroupOf_normal (CaseIIDouble.zz z)) :=
    CaseIIDouble.quotientDataZZ D
  have hIII2 : ¬ ParrottEqualityBranch (z := CaseIIDouble.zz z) (D := D2) h2 :=
    fun hb => hIII ((CaseIIDouble.parrottEqualityBranch_zz_iff h2 D).mp hb)
  have hmain := relIndex_commutator_sup_centerIn_of_not_equalityBranch
    (z := CaseIIDouble.zz z) h2 D2 hIII2
  rw [CaseIIDouble.centerIn_J_zz, CaseIIDouble.H_zz,
    Subgroup.commutator_prod_prod] at hmain
  have htop : ⁅(⊤ : Subgroup (Multiplicative (ZMod 2))),
      (⊤ : Subgroup (Multiplicative (ZMod 2)))⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr (by infer_instance)
  rw [htop] at hmain
  have hZle : centerIn (J z) ≤ ⁅H z, H z⁆ := centerIn_le_commutator_A h
  set A : Subgroup G := H z with hA
  set B : Subgroup G := ⁅H z, H z⁆ with hB
  have hZleB : centerIn (J z) ≤ B := hB ▸ hZle
  have hsup : (B.prod (⊥ : Subgroup (Multiplicative (ZMod 2)))) ⊔
      ((centerIn (J z)).prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) = B.prod ⊤ := by
    apply le_antisymm
    · exact sup_le (Subgroup.prod_mono le_rfl bot_le) (Subgroup.prod_mono hZleB le_rfl)
    · rintro ⟨b, c⟩ hbc
      obtain ⟨hb, hc⟩ := Subgroup.mem_prod.mp hbc
      have h1 : ((b, 1) : CaseIIDouble.D2 G) ∈
          B.prod (⊥ : Subgroup (Multiplicative (ZMod 2))) :=
        Subgroup.mem_prod.mpr ⟨hb, Subgroup.mem_bot.mpr rfl⟩
      have h2 : ((1, c) : CaseIIDouble.D2 G) ∈
          (centerIn (J z)).prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :=
        Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩
      have heq : ((b, c) : CaseIIDouble.D2 G) = (b, 1) * (1, c) := by
        ext <;> simp
      rw [heq]
      exact Subgroup.mul_mem_sup h1 h2
  rw [hsup] at hmain
  let f : ↥(A.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) →* ↥A :=
    ((MonoidHom.fst G (Multiplicative (ZMod 2))).comp
      (A.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).subtype).codRestrict A
      (fun x => (Subgroup.mem_prod.mp x.2).1)
  have hfsurj : Function.Surjective f := by
    intro a
    refine ⟨⟨((a : G), 1), Subgroup.mem_prod.mpr ⟨a.2, Subgroup.mem_top 1⟩⟩, ?_⟩
    exact Subtype.ext rfl
  have hker : (B.subgroupOf A).comap f =
      (B.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).subgroupOf
        (A.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_prod]
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hx
      exact ⟨hx, Subgroup.mem_top _⟩
    · intro hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_prod] at hx
      exact hx.1
  have hrel : (B.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).relIndex
      (A.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) = B.relIndex A := by
    change ((B.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).subgroupOf
      (A.prod (⊤ : Subgroup (Multiplicative (ZMod 2))))).index = (B.subgroupOf A).index
    rw [← hker]
    exact Subgroup.index_comap_of_surjective (B.subgroupOf A) hfsurj
  rw [hrel] at hmain
  exact hmain

end CFSG.RankThree.GF2n.Parrott
