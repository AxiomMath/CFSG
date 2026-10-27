module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2
public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace S153E56a

open CFSG.Quasithin.S153E

section Ortho

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem eq_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨y₀, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp hK
  have h1 : (⟨x, hx⟩ : ↥K) = y₀ := hu _ (fun e => hx1 (congrArg Subtype.val e))
  have h2 : (⟨y, hy⟩ : ↥K) = y₀ := hu _ (fun e => hy1 (congrArg Subtype.val e))
  exact congrArg Subtype.val (h1.trans h2.symm)

omit [Finite G] in
theorem sq_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x : G} (hx : x ∈ K) : x * x = 1 := by
  have h := pow_card_eq_one' (G := ↥K) (x := ⟨x, hx⟩)
  rw [hK] at h
  have := congrArg Subtype.val h
  simpa [pow_two] using this

open scoped Classical in
omit [Finite G] in
theorem ite_mul_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) :
    (if x * y = 1 then (0 : ZMod 2) else 1) =
      (if x = 1 then 0 else 1) + (if y = 1 then 0 else 1) := by
  by_cases hx1 : x = 1
  · simp [hx1]
  by_cases hy1 : y = 1
  · simp [hy1]
  have hxy : x = y := eq_of_card_two hK hx hy hx1 hy1
  subst hxy
  have h1 : x * x = 1 := sq_of_card_two hK hx
  simp only [h1, hx1, ite_true, ite_false]
  decide

theorem Z_comm_U (cx : Ctx15350 T Mc M V₁ V₂ t) {z u : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hu : u ∈ UH153 T M V₁ Mc) : z * u = u * z := by
  have hu' : u ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    cx.hF.H_le_centralizer ((U_le_T cx).trans (T_le_Mc cx) hu)
  exact Subgroup.mem_centralizer_iff.mp hu' z hz

theorem Z_le_U (cx : Ctx15350 T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
  (Z_le_ZS cx).trans (ZS_le_U cx)

theorem sq_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    z * z = 1 :=
  sq_of_card_two cx.c.hyp.lemma_15_3_2_two.2 hz

theorem pwr_mul_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {u z : G} (hu : u ∈ UH153 T M V₁ Mc)
    (hz : z ∈ quasithinOmegaOneCenter T) : pwr153 (u * z) = pwr153 u := by
  have hc : Commute u z := (Z_comm_U cx hz hu).symm
  have e : (u * z) ^ 2 = u ^ 2 := by
    rw [hc.mul_pow, pow_two z, sq_Z cx hz, mul_one]
  unfold pwr153
  rw [e]

theorem zmod_aux (x y z : ZMod 2) : z + x + y + x + y = z := by
  revert x y z
  decide

theorem pwr_polar (cx : Ctx15350 T Mc M V₁ V₂ t) {u v : G} (hu : u ∈ UH153 T M V₁ Mc)
    (hv : v ∈ UH153 T M V₁ Mc) : pwr153 (u * v) + pwr153 u + pwr153 v = comm153 u v := by
  classical
  have hZ2 := cx.c.hyp.lemma_15_3_2_two.2
  have ha := sq_U_mem cx hu
  have hb := sq_U_mem cx hv
  have hc := commutator_U_mem cx hu hv
  have hav : (u * u) * v = v * (u * u) := Z_comm_U cx ha hv
  have hav' : v⁻¹ * (u * u) = (u * u) * v⁻¹ := by
    have h1 : v⁻¹ * ((u * u) * v) * v⁻¹ = v⁻¹ * (v * (u * u)) * v⁻¹ := by rw [hav]
    calc v⁻¹ * (u * u) = v⁻¹ * ((u * u) * v) * v⁻¹ := by group
      _ = v⁻¹ * (v * (u * u)) * v⁻¹ := h1
      _ = (u * u) * v⁻¹ := by group
  have key : (u * v) ^ 2 = (u * v * u⁻¹ * v⁻¹) * (u * u) * (v * v) := by
    calc (u * v) ^ 2 = (u * v) * (u * v) := pow_two _
      _ = (u * v * u⁻¹) * ((u * u) * v⁻¹) * (v * v) := by group
      _ = (u * v * u⁻¹) * (v⁻¹ * (u * u)) * (v * v) := by rw [hav']
      _ = (u * v * u⁻¹ * v⁻¹) * (u * u) * (v * v) := by group
  have hca : (u * v * u⁻¹ * v⁻¹) * (u * u) ∈ quasithinOmegaOneCenter T :=
    Subgroup.mul_mem _ hc ha
  have e1 := ite_mul_of_card_two hZ2 hca hb
  have e2 := ite_mul_of_card_two hZ2 hc ha
  have hpu : pwr153 u = if u * u = 1 then 0 else 1 := by
    unfold pwr153
    rw [pow_two]
  have hpv : pwr153 v = if v * v = 1 then 0 else 1 := by
    unfold pwr153
    rw [pow_two]
  have hpuv : pwr153 (u * v) = if (u * v * u⁻¹ * v⁻¹) * (u * u) * (v * v) = 1 then 0 else 1 := by
    unfold pwr153
    rw [key]
  have hcm : comm153 u v = if u * v * u⁻¹ * v⁻¹ = 1 then 0 else 1 := by
    unfold comm153
    rw [commutatorElement_def]
  rw [hpuv, hpu, hpv, hcm, e1, e2]
  exact zmod_aux _ _ _

theorem center_eq (cx : Ctx15350 T Mc M V₁ V₂ t) (hU : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc)) :
    Subgroup.center ↥(UH153 T M V₁ Mc) =
      (quasithinOmegaOneCenter T).subgroupOf (UH153 T M V₁ Mc) := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Z_comm_U cx hx g.2).symm
  · rw [@CFSG.IsExtraspecial.center_order_p 2 ↥(UH153 T M V₁ Mc) _ hU,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_U cx)).toEquiv]
    exact cx.c.hyp.lemma_15_3_2_two.2.ge

theorem orth_nondeg (cx : Ctx15350 T Mc M V₁ V₂ t) (hU : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc))
    {u : G} (hu : u ∈ UH153 T M V₁ Mc) (h : ∀ v ∈ UH153 T M V₁ Mc, ⁅u, v⁆ = 1) :
    u ∈ quasithinOmegaOneCenter T := by
  have hmem : (⟨u, hu⟩ : ↥(UH153 T M V₁ Mc)) ∈ Subgroup.center ↥(UH153 T M V₁ Mc) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : u * g = g * u := commutatorElement_eq_one_iff_mul_comm.mp (h g g.2)
    exact Subtype.ext h1.symm
  rw [center_eq cx hU, Subgroup.mem_subgroupOf] at hmem
  exact hmem

omit [Finite G] in
theorem pwr_conj (h u : G) : pwr153 (h * u * h⁻¹) = pwr153 u := by
  unfold pwr153
  rw [conj_pow, conj_eq_one_iff]

end Ortho

end S153E56a

namespace S153E

open CFSG.Quasithin.S153E56a

section Lemma

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_56_orth (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hU : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc)) :
    (∀ u ∈ UH153 T M V₁ Mc, ∀ z ∈ quasithinOmegaOneCenter T, pwr153 (u * z) = pwr153 u) ∧
    (∀ u ∈ UH153 T M V₁ Mc, ∀ v ∈ UH153 T M V₁ Mc,
      pwr153 (u * v) + pwr153 u + pwr153 v = comm153 u v) ∧
    (∀ u ∈ UH153 T M V₁ Mc, (∀ v ∈ UH153 T M V₁ Mc, ⁅u, v⁆ = 1) →
      u ∈ quasithinOmegaOneCenter T) ∧
    (∀ h ∈ Mc, ∀ u ∈ UH153 T M V₁ Mc, pwr153 (h * u * h⁻¹) = pwr153 u) :=
  ⟨fun _ hu _ hz => pwr_mul_Z cx hu hz, fun _ hu _ hv => pwr_polar cx hu hv,
    fun _ hu h => orth_nondeg cx hU hu h, fun h _ _ _ => pwr_conj h _⟩

end Lemma

end S153E

end CFSG.Quasithin
