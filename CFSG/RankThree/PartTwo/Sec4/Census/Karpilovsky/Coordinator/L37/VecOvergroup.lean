module

public import CFSG.Sporadic.ON.Chain

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.Sporadic.ON
open CFSG.Sporadic.ON.Native (nPts)
open scoped Pointwise

section General

variable {G X : Type*} [Group G] [MulAction G X]

theorem smul_pair_cases {a b : X} {x : G} (hx : x • ({a, b} : Set X) = {a, b}) :
    (x • a = a ∧ x • b = b) ∨ (x • a = b ∧ x • b = a) := by
  have ha : x • a ∈ ({a, b} : Set X) := by
    rw [← hx]; exact Set.smul_mem_smul_set (Set.mem_insert a {b})
  have hb : x • b ∈ ({a, b} : Set X) := by
    rw [← hx]; exact Set.smul_mem_smul_set (Set.mem_insert_of_mem a rfl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : a = b := (smul_left_cancel_iff x).1 (ha.trans hb.symm)
    exact Or.inl ⟨ha, by rw [hb, hab]⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · have hab : a = b := (smul_left_cancel_iff x).1 (ha.trans hb.symm)
    exact Or.inl ⟨by rw [ha, hab], hb⟩

theorem card_stabilizer_eq [MulAction.IsPretransitive G X] (x y : X) :
    Nat.card (MulAction.stabilizer G y) = Nat.card (MulAction.stabilizer G x) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem stabilizer_le_cases_of_base [MulAction.IsPretransitive G X] {x x' : X}
    (hcases : ∀ K : Subgroup G, MulAction.stabilizer G x ≤ K →
      K = MulAction.stabilizer G x ∨ K = MulAction.stabilizer G ({x, x'} : Set X) ∨ K = ⊤)
    (y : X) {K : Subgroup G} (hK : MulAction.stabilizer G y ≤ K) :
    ∃ y' : X, K = MulAction.stabilizer G y ∨
      K = MulAction.stabilizer G ({y, y'} : Set X) ∨ K = ⊤ := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  set K₀ := K.map (MulAut.conj g⁻¹).toMonoidHom with hK₀
  have hback : K = K₀.map (MulAut.conj g).toMonoidHom := by
    rw [hK₀, Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id K]
    congr 1
    ext z
    simp only [MonoidHom.id_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hK₀le : MulAction.stabilizer G x ≤ K₀ := by
    intro z hz
    refine ⟨g * z * g⁻¹, hK ?_, by simp [mul_assoc]⟩
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact ⟨z, hz, rfl⟩
  refine ⟨g • x', ?_⟩
  rcases hcases K₀ hK₀le with h | h | h
  · left
    rw [hback, h, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  · right; left
    rw [hback, h, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, Set.smul_set_insert,
      Set.smul_set_singleton]
  · right; right
    rw [hback, h, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

end General

theorem card_stabilizer_vec (w : Fin nPts) :
    Nat.card (MulAction.stabilizer J w) = 1876896 := by
  rw [card_stabilizer_eq root w, stabilizer_root, card_lvl_one]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
