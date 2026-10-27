module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivTransl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivFrob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivCard

public section

namespace CFSG.Quasithin.Fan86.Univ

open CFSG.Quasithin

variable {A C B : Type} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem ofA_smul_inr_eq_self_iff (X : GoldAmalgam A C B) (y a : A) :
    X.ofA y • (Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) : Vtx X) =
        Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) ↔
      a⁻¹ * y * a ∈ X.edgeA := by
  rw [ofA_smul_inr, inr_ofA_eq_iff]
  have e : (y * a)⁻¹ * a = (a⁻¹ * y * a)⁻¹ := by group
  rw [e, Subgroup.inv_mem_iff]

theorem ofB_smul_inl_eq_self_iff (X : GoldAmalgam A C B) (y b : B) :
    X.ofB y • (Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) : Vtx X) =
        Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) ↔
      b⁻¹ * y * b ∈ X.edgeB := by
  rw [ofB_smul_inl, inl_ofB_eq_iff]
  have e : (y * b)⁻¹ * b = (b⁻¹ * y * b)⁻¹ := by group
  rw [e, Subgroup.inv_mem_iff]

theorem locTrans_baseA (X : GoldAmalgam A C B) : LocTrans X.treeGraph X.Universal (baseA X) := by
  intro a' b' ha hb
  obtain ⟨a, rfl⟩ := (adj_baseA_iff X a').1 ha
  obtain ⟨b, rfl⟩ := (adj_baseA_iff X b').1 hb
  refine ⟨X.ofA (b * a⁻¹), ?_, ?_⟩
  · rw [stabilizer_baseA]
    exact ⟨_, rfl⟩
  · rw [ofA_smul_inr, inv_mul_cancel_right]

theorem locTrans_baseB (X : GoldAmalgam A C B) : LocTrans X.treeGraph X.Universal (baseB X) := by
  intro a' b' ha hb
  obtain ⟨a, rfl⟩ := (adj_baseB_iff X a').1 ha
  obtain ⟨b, rfl⟩ := (adj_baseB_iff X b').1 hb
  refine ⟨X.ofB (b * a⁻¹), ?_, ?_⟩
  · rw [stabilizer_baseB]
    exact ⟨_, rfl⟩
  · rw [ofB_smul_inl, inv_mul_cancel_right]

theorem frobTwo_baseA (h : Hyp53 X) : FrobTwo X.treeGraph X.Universal (baseA X) := by
  have := h.finite_left
  have hE := X.isPGroup_edgeA h.pgroup
  have hodd : ¬ 2 ∣ X.edgeA.index := by rw [h.index_left]; decide
  intro a' b' ha hb hab k hk hka hkb c' hc
  obtain ⟨a, rfl⟩ := (adj_baseA_iff X a').1 ha
  obtain ⟨b, rfl⟩ := (adj_baseA_iff X b').1 hb
  obtain ⟨c, rfl⟩ := (adj_baseA_iff X c').1 hc
  rw [stabilizer_baseA] at hk
  obtain ⟨y, rfl⟩ := hk
  rw [ofA_smul_inr_eq_self_iff] at hka hkb ⊢
  have hy := frob_two_left hE h.index_left (card_oTwoQuot_left h) (a := a) (b := b)
    (fun hmem => hab ((inr_ofA_eq_iff X a b).2 hmem)) hka hkb
  exact conj_mem_of_mem_pCore hE hodd hy c

theorem frobTwo_baseB (h : Hyp53 X) : FrobTwo X.treeGraph X.Universal (baseB X) := by
  refine frobTwo_of_card_three (adj_smul X) ?_
  have : (X.treeGraph.neighborSet (baseB X)).ncard = 3 := by
    have h1 := ncard_neighborSet_inr X 1
    rw [h.index_right] at h1
    exact h1
  rwa [Nat.card_coe_set_eq]

theorem frobNonreg_baseA (h : Hyp53 X) : FrobNonreg X.treeGraph X.Universal (baseA X) := by
  have := h.finite_left
  have hE := X.isPGroup_edgeA h.pgroup
  have hodd : ¬ 2 ∣ X.edgeA.index := by rw [h.index_left]; decide
  have hne : ∃ e ∈ X.edgeA, e ∉ Open.pCore 2 A :=
    exists_mem_not_mem_pCore hE hodd (by
      rw [h.index_left]
      rcases card_oTwoQuot_left h with h1 | h1 <;> omega)
  intro a' ha
  obtain ⟨a, rfl⟩ := (adj_baseA_iff X a').1 ha
  obtain ⟨y, hy1, hy2⟩ := exists_mem_not_forall hE hodd hne a
  refine ⟨X.ofA y, by rw [stabilizer_baseA]; exact ⟨y, rfl⟩,
    (ofA_smul_inr_eq_self_iff X y a).2 hy1, ?_⟩
  by_contra hcon
  apply hy2
  intro c
  have h1 : X.ofA y • (Sum.inr ((X.ofA c : X.Universal) : X.Universal ⧸ X.ofB.range) : Vtx X) =
      Sum.inr ((X.ofA c : X.Universal) : X.Universal ⧸ X.ofB.range) := by
    by_contra hne'
    exact hcon ⟨_, (adj_baseA_iff X _).2 ⟨c, rfl⟩, hne'⟩
  exact (ofA_smul_inr_eq_self_iff X y c).1 h1

theorem frobNonreg_baseB (h : Hyp53 X) : FrobNonreg X.treeGraph X.Universal (baseB X) := by
  have := h.finite_right
  have hE := X.isPGroup_edgeB h.pgroup
  have hodd : ¬ 2 ∣ X.edgeB.index := by rw [h.index_right]; decide
  have hne : ∃ e ∈ X.edgeB, e ∉ Open.pCore 2 B :=
    exists_mem_not_mem_pCore hE hodd (by rw [h.index_right, card_oTwoQuot_right h]; decide)
  intro a' ha
  obtain ⟨a, rfl⟩ := (adj_baseB_iff X a').1 ha
  obtain ⟨y, hy1, hy2⟩ := exists_mem_not_forall hE hodd hne a
  refine ⟨X.ofB y, by rw [stabilizer_baseB]; exact ⟨y, rfl⟩,
    (ofB_smul_inl_eq_self_iff X y a).2 hy1, ?_⟩
  by_contra hcon
  apply hy2
  intro c
  have h1 : X.ofB y • (Sum.inl ((X.ofB c : X.Universal) : X.Universal ⧸ X.ofA.range) : Vtx X) =
      Sum.inl ((X.ofB c : X.Universal) : X.Universal ⧸ X.ofA.range) := by
    by_contra hne'
    exact hcon ⟨_, (adj_baseB_iff X _).2 ⟨c, rfl⟩, hne'⟩
  exact (ofB_smul_inl_eq_self_iff X y c).1 h1

end CFSG.Quasithin.Fan86.Univ
