module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3AY
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Ex
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

@[expose] def genSet (δ' : V) : Set G :=
  Set.range (D.y δ') ∪ (D.calpha : Set G) ∪ (L.zGroup 2 α : Set G)

theorem mem_genSet {δ' : V} {s : G} :
    s ∈ genSet D δ' ↔ (∃ i, D.y δ' i = s) ∨ s ∈ D.calpha ∨ s ∈ L.zGroup 2 α := by
  simp only [genSet, Set.mem_union, Set.mem_range, SetLike.mem_coe, or_assoc]

theorem closure_genSet_le (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L) {δ' : V}
    (hY : D.IsYPair δ') : Subgroup.closure (genSet D δ') ≤ MulAction.stabilizer G α := by
  rw [Subgroup.closure_le]
  intro s hs
  rcases (mem_genSet D).1 hs with ⟨i, rfl⟩ | hs | hs
  · exact F.nbrStab_le_stabilizer α (y_mem_nbrStab D h83a hY i)
  · exact F.nbrStab_le_stabilizer α (Subgroup.mem_inf.1 hs).1
  · exact zGroup_le_stabilizer h71c hs

theorem nbrStab_le_closure_genSet (h83a : Fan83a F L) {δ' : V} (hY : D.IsYPair δ') :
    nbrStab Γ G α ≤ Subgroup.closure (genSet D δ') := by
  rw [h83a α D δ' hY]
  refine sup_le (Subgroup.closure_mono fun s hs => Or.inl (Or.inl hs)) (sup_le ?_ ?_)
  · exact fun v hv => Subgroup.subset_closure (Or.inr hv)
  · exact fun c hc => Subgroup.subset_closure (Or.inl (Or.inr hc))

theorem fcomm_genSet_mem (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83c : Fan83c F L) (h83d : Fan83d F L) (hcyc : IsCyclic ↥D.calpha) {δ' : V}
    (hY : D.IsYPair δ') {s t : G} (hs : s ∈ genSet D δ') (ht : t ∈ genSet D δ') :
    fcomm s t ∈ L.zGroup 2 α := by
  have hst := closure_genSet_le D F h71c h83a hY
  have hyst : ∀ i, D.y δ' i ∈ MulAction.stabilizer G α := fun i =>
    hst (Subgroup.subset_closure ((mem_genSet D).2 (Or.inl ⟨i, rfl⟩)))
  have hCst : ∀ c ∈ D.calpha, c ∈ MulAction.stabilizer G α := fun c hc =>
    hst (Subgroup.subset_closure ((mem_genSet D).2 (Or.inr (Or.inl hc))))
  have := hcyc
  rcases (mem_genSet D).1 hs with ⟨i, rfl⟩ | hs | hs
  · rcases (mem_genSet D).1 ht with ⟨j, rfl⟩ | ht | ht
    · exact fcomm_y_y_mem D F h83d hY i j
    · exact fcomm_y_calpha_mem D F h71c h83c hY i (hyst i) ht
    · exact fcomm_mem_of_right_mem F (hyst i) ht
  · rcases (mem_genSet D).1 ht with ⟨j, rfl⟩ | ht | ht
    · have e : fcomm s (D.y δ' j) = (fcomm (D.y δ' j) s)⁻¹ := by
        unfold fcomm
        group
      rw [e]
      exact inv_mem (fcomm_y_calpha_mem D F h71c h83c hY j (hyst j) hs)
    · have hcom : (⟨s, hs⟩ : ↥D.calpha) * ⟨t, ht⟩ = ⟨t, ht⟩ * ⟨s, hs⟩ :=
        (IsCyclic.isMulCommutative (α := ↥D.calpha)).is_comm.comm _ _
      have h' : s * t = t * s := congrArg Subtype.val hcom
      have e : fcomm s t = (t * s)⁻¹ * (s * t) := by
        unfold fcomm
        group
      rw [e, ← h', inv_mul_cancel]
      exact one_mem _
    · exact fcomm_mem_of_right_mem F (hCst s hs) ht
  · rcases (mem_genSet D).1 ht with ⟨j, rfl⟩ | ht | ht
    · exact fcomm_mem_of_left_mem F (hyst j) hs
    · exact fcomm_mem_of_left_mem F (hCst t ht) hs
    · rw [zGroup_fcomm h71c s hs t ht]
      exact one_mem _

theorem mul_self_genSet_mem (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (hcyc : IsCyclic ↥D.calpha) (hle : Nat.card ↥D.calpha ≤ 4) {δ' : V} (hY : D.IsYPair δ')
    {s : G} (hs : s ∈ genSet D δ') : s * s ∈ L.zGroup 2 α := by
  rcases (mem_genSet D).1 hs with ⟨i, rfl⟩ | hs | hs
  · rw [y_mul_self D F h71c hY i]
    exact one_mem _
  · rcases calpha_sq_mem D F h71c h75 hcyc hle hs with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact z_mem_zGroup D.val
  · exact mul_mem hs hs

theorem nbrStab_mul_self_mem (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (h83a : Fan83a F L) (h83c : Fan83c F L) (h83d : Fan83d F L) (hcyc : IsCyclic ↥D.calpha)
    (hle : Nat.card ↥D.calpha ≤ 4) {δ' : V} (hY : D.IsYPair δ') {g : G}
    (hg : g ∈ nbrStab Γ G α) : g * g ∈ L.zGroup 2 α := by
  have hnorm : ∀ a ∈ Subgroup.closure (genSet D δ'), ∀ n ∈ L.zGroup 2 α,
      a * n * a⁻¹ ∈ L.zGroup 2 α := fun a ha n hn =>
    zGroup_normal F (closure_genSet_le D F h71c h83a hY ha) n hn
  have hcomm := fcomm_mem_of_gens (L.zGroup 2 α) (genSet D δ') hnorm
    fun s hs t ht => fcomm_genSet_mem D F h71c h83a h83c h83d hcyc hY hs ht
  exact mul_self_mem_of_gens (L.zGroup 2 α) (genSet D δ') hnorm hcomm
    (fun s hs => mul_self_genSet_mem D F h71c h75 hcyc hle hY hs) g
    (nbrStab_le_closure_genSet D h83a hY hg)

end Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_6a (F : FanTree Γ G) (L : ZLab Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (h83a : Fan83a F L) (h83c : Fan83c F L) (h83d : Fan83d F L) (h84a : Fan84a F L)
    (hD : D10YPairExists F L) : Fan86a F := by
  intro α hα g hg hg1
  obtain ⟨D, δ', hY⟩ := hD α hα
  obtain ⟨hcyc, hle⟩ := h84a α D
  have hg2 := Sec8P3.nbrStab_mul_self_mem D F h71c h75 h83a h83c h83d hcyc hle hY hg
  have h4 : g ^ 4 = 1 := by
    calc g ^ 4 = (g * g) * (g * g) := by simp [pow_succ, mul_assoc]
      _ = 1 := Sec8P3.zGroup_mul_self h71c _ hg2
  have hdvd : orderOf g ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h4
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases m
  · exact absurd (orderOf_eq_one_iff.1 (by simpa using hm')) hg1
  · left
    simpa using hm'
  · right
    simpa using hm'

end CFSG.Quasithin.Fan86
