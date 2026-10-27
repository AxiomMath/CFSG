module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchDir
public import CFSG.LocalAnalysis.StandardType.PhanEFlagIntr

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

@[expose] noncomputable def jShift21 (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (u : Fin 2 → K) : Fin 3 → K :=
  ![0, sg K f (u 0), sg K f (u 1)]

@[expose] noncomputable def jShift21Inv (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (v : Fin 3 → K) : Fin 2 → K :=
  ![sg K f (v 1), sg K f (v 2)]

theorem q2cFA2_isCut_013 : IsCut 3 [0, 1, 3] where
  head := by decide
  last := by decide
  strict := by
    intro i hi
    have hlen : i + 1 < 3 := by simpa using hi
    have h2 : i < 2 := by omega
    interval_cases i <;> decide

private theorem q2cFA2_farSet_le : ∀ i, i < [0, 1, 3].length → [0, 1, 3].getD i 0 ≤ 3 := by
  intro i hi
  have hi' : i < 3 := by simpa using hi
  interval_cases i <;> decide

theorem q2cFA2_blockU_013 (E : FlagK K 3) :
    blockU K 3 [0, 1, 3] E.E 1 1 = E.E 1 ⊔ Vsub 3 1 := by
  simp only [blockU, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_self, Nat.zero_add,
    Vsub_self, inf_top_eq]

theorem q2cFA2_R₀_eq :
    {c : FlagK K 3 × FlagK K 2 | c.1 ∈ refSet K 3 [0, 1, 3]} =
      refSet K 3 [0, 1, 3] ×ˢ (Set.univ : Set (FlagK K 2)) := by
  ext c
  simp [Set.mem_prod]

private theorem q2cFA2_farSet_inf_Vsub_one {E : FlagK K 3} (hfar : E ∈ farSet 3 [0, 1, 3]) :
    E.E 1 ⊓ Vsub 3 1 = ⊥ := by
  have h := (mem_farSet_iff (K := K) (n := 3) (d := [0, 1, 3]) q2cFA2_farSet_le).mp hfar
    1 (by decide) 1 (by norm_num)
  simpa using h.1 (by decide)

theorem q2cFA2_farSet_inf_Vsub_two {E : FlagK K 3} (hfar : E ∈ farSet 3 [0, 1, 3]) :
    E.E 2 ⊓ Vsub 3 1 = ⊥ := by
  have h := (mem_farSet_iff (K := K) (n := 3) (d := [0, 1, 3]) q2cFA2_farSet_le).mp hfar
    1 (by decide) 2 (by norm_num)
  simpa using h.1 (by decide)

private theorem q2cFA2_jShift21_smul (a : K) (u : Fin 2 → K) :
    jShift21 K f (a • u) = sg K f a • jShift21 K f u := by
  funext i
  fin_cases i <;> simp [jShift21, Pi.smul_apply, smul_eq_mul, map_mul]

private theorem q2cFA2_jShift21Inv_add (a b : Fin 3 → K) :
    jShift21Inv K f (a + b) = jShift21Inv K f a + jShift21Inv K f b := by
  funext i
  fin_cases i <;> simp [jShift21Inv, map_add]

private theorem q2cFA2_jShift21Inv_smul (a : K) (v : Fin 3 → K) :
    jShift21Inv K f (a • v) = sg K f a • jShift21Inv K f v := by
  funext i
  fin_cases i <;> simp [jShift21Inv, Pi.smul_apply, smul_eq_mul, map_mul]

private theorem q2cFA2_jShift21Inv_eq_zero_of_mem_Vsub {v : Fin 3 → K}
    (hv : v ∈ Vsub 3 1) : jShift21Inv K f v = 0 := by
  funext i
  fin_cases i
  · show sg K f (v 1) = 0
    rw [hv 1 (by norm_num), map_zero]
  · show sg K f (v 2) = 0
    rw [hv 2 (by norm_num), map_zero]

private theorem q2cFA2_jShift21Inv_eq_zero_iff (v : Fin 3 → K) :
    jShift21Inv K f v = 0 ↔ v ∈ Vsub 3 1 := by
  constructor
  · intro h j hj
    have hj' : j = 1 ∨ j = 2 := by
      fin_cases j <;> simp_all
    rcases hj' with rfl | rfl
    · have h0 : sg K f (v 1) = 0 := by
        have := congrFun h 0
        simpa [jShift21Inv] using this
      exact (sg K f).injective (by rw [h0, map_zero])
    · have h1 : sg K f (v 2) = 0 := by
        have := congrFun h 1
        simpa [jShift21Inv] using this
      exact (sg K f).injective (by rw [h1, map_zero])
  · exact q2cFA2_jShift21Inv_eq_zero_of_mem_Vsub

private theorem q2cFA2_jShift21_ne_zero {u : Fin 2 → K} (hu : u ≠ 0) :
    jShift21 K f u ≠ 0 := by
  intro h
  apply hu
  have ha : u 0 = 0 := by
    have h1 := congrFun h 1
    have hsg : sg K f (u 0) = 0 := by simpa [jShift21] using h1
    exact (sg K f).injective (by simpa using hsg)
  have hb : u 1 = 0 := by
    have h2 := congrFun h 2
    have hsg : sg K f (u 1) = 0 := by simpa [jShift21] using h2
    exact (sg K f).injective (by simpa using hsg)
  funext i
  fin_cases i
  · exact ha
  · exact hb

private theorem q2cFA2_jShift21_notMem_Vsub {u : Fin 2 → K} (hu : u ≠ 0) :
    jShift21 K f u ∉ Vsub 3 1 := by
  intro h
  apply q2cFA2_jShift21_ne_zero hu
  funext i
  fin_cases i
  · simp [jShift21]
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)

private def q2cFA2_vEmb (v : Fin 3 → K) : Fin 3 → K := ![v 0, 0, 0]

private def q2cFA2_wEmb (v : Fin 3 → K) : Fin 3 → K := ![0, v 1, v 2]

private theorem q2cFA2_vEmb_mem (v : Fin 3 → K) : q2cFA2_vEmb v ∈ Vsub 3 1 := by
  intro j hj
  fin_cases j <;> simp_all [q2cFA2_vEmb]

private theorem q2cFA2_vEmb_add_wEmb (v : Fin 3 → K) :
    q2cFA2_vEmb v + q2cFA2_wEmb v = v := by
  funext i
  fin_cases i <;> simp [q2cFA2_vEmb, q2cFA2_wEmb]

private theorem q2cFA2_wEmb_eq_sub (v : Fin 3 → K) :
    q2cFA2_wEmb v = v - q2cFA2_vEmb v := by
  funext i
  fin_cases i <;> simp [q2cFA2_vEmb, q2cFA2_wEmb]

private theorem q2cFA2_jShift21_jShift21Inv (hK : Nat.card K = (2 ^ f) ^ 2)
    (v : Fin 3 → K) : jShift21 K f (jShift21Inv K f v) = q2cFA2_wEmb v := by
  funext i
  fin_cases i
  · rfl
  · show sg K f (sg K f (v 1)) = v 1
    rw [sg_sg hK]
  · show sg K f (sg K f (v 2)) = v 2
    rw [sg_sg hK]

private theorem q2cFA2_span_jShift21_singleton (v : Fin 2 → K) :
    Submodule.span K (jShift21 K f '' (K ∙ v : Set (Fin 2 → K))) = K ∙ jShift21 K f v := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨u, hu, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
    rw [← ha, q2cFA2_jShift21_smul]
    exact Submodule.mem_span_singleton.mpr ⟨sg K f a, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨v, Submodule.mem_span_singleton_self v, rfl⟩

private theorem q2cFA2_span_jShift21Inv_Vsub_sup_singleton (u : Fin 3 → K) :
    Submodule.span K (jShift21Inv K f ''
      ((Vsub 3 1 ⊔ K ∙ u : Submodule K (Fin 3 → K)) : Set (Fin 3 → K))) =
      K ∙ jShift21Inv K f u := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨a, ha, rfl⟩
    change a ∈ Vsub 3 1 ⊔ K ∙ u at ha
    rw [Submodule.mem_sup] at ha
    obtain ⟨p, hp, q, hq, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    rw [q2cFA2_jShift21Inv_add, q2cFA2_jShift21Inv_smul,
      q2cFA2_jShift21Inv_eq_zero_of_mem_Vsub hp, zero_add]
    exact Submodule.mem_span_singleton.mpr ⟨sg K f c, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span
      ⟨u, Submodule.mem_sup_right (Submodule.mem_span_singleton_self u), rfl⟩

private theorem q2cFA2_finrank_jShift21_span {L : Submodule K (Fin 2 → K)}
    (hL : finrank K L = 1) :
    finrank K (Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K)))) = 1 := by
  obtain ⟨v, hv0, hLv⟩ := exists_eq_span_of_finrank_eq_one hL
  rw [hLv, q2cFA2_span_jShift21_singleton]
  exact finrank_span_singleton (q2cFA2_jShift21_ne_zero hv0)

private theorem q2cFA2_inf_Vsub_jShift21_span {L : Submodule K (Fin 2 → K)}
    (hL : finrank K L = 1) :
    Vsub 3 1 ⊓ Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K))) = ⊥ := by
  obtain ⟨v, hv0, hLv⟩ := exists_eq_span_of_finrank_eq_one hL
  rw [hLv, q2cFA2_span_jShift21_singleton]
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxV, hxspan⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
  rw [← hc]
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul]
  · exfalso
    apply q2cFA2_jShift21_notMem_Vsub hv0
    have : jShift21 K f v = c⁻¹ • (c • jShift21 K f v) := by
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this, hc]
    exact Submodule.smul_mem _ _ hxV

theorem q2cFA2_finrank_sup_jShift21_span {L : Submodule K (Fin 2 → K)}
    (hL : finrank K L = 1) :
    finrank K ↥(Vsub (K := K) 3 1 ⊔
      Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K)))) = 2 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) 3 1)
    (Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K))))
  rw [q2cFA2_inf_Vsub_jShift21_span hL, finrank_bot, add_zero,
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num),
    q2cFA2_finrank_jShift21_span hL] at hsum
  exact hsum

theorem q2cFA2_finrank_jShift21Inv_span (hK : Nat.card K = (2 ^ f) ^ 2)
    {M : Submodule K (Fin 3 → K)} (hV : Vsub 3 1 ≤ M) (hfin : finrank K M = 2) :
    finrank K (Submodule.span K (jShift21Inv K f '' (M : Set (Fin 3 → K)))) = 1 := by
  have hne : M ≠ Vsub 3 1 := by
    intro h
    rw [h, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hfin
    omega
  have hnot : ¬ (M : Set (Fin 3 → K)) ⊆ (Vsub (K := K) 3 1 : Set (Fin 3 → K)) := by
    intro hle
    exact hne (Submodule.ext fun x => ⟨fun hx => hle hx, fun hx => hV hx⟩)
  obtain ⟨u, huM, huV⟩ := Set.not_subset.mp hnot
  have hu0 : u ≠ 0 := fun h => huV (by rw [h]; exact Submodule.zero_mem (Vsub 3 1))
  have hle : Vsub 3 1 ⊔ K ∙ u ≤ M :=
    sup_le hV ((Submodule.span_singleton_le_iff_mem u M).mpr huM)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) 3 1) (K ∙ u)
  have hinf : Vsub 3 1 ⊓ K ∙ u = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxV, hxspan⟩ := hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
    rw [← hc]
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul]
    · exfalso
      apply huV
      have : u = c⁻¹ • (c • u) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, hc]
      exact Submodule.smul_mem _ _ hxV
  rw [hinf, finrank_bot, add_zero,
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num),
    finrank_span_singleton hu0] at hsum
  have hM : M = Vsub 3 1 ⊔ K ∙ u := (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  rw [hM, q2cFA2_span_jShift21Inv_Vsub_sup_singleton]
  exact finrank_span_singleton
    (fun h => huV ((q2cFA2_jShift21Inv_eq_zero_iff u).mp h))

private theorem q2cFA2_dirZ_eq (z : Submodule K (Fin 2 → K)) :
    Exch.dirZ K f z = Vsub 3 1 ⊔ Submodule.span K (jShift21 K f '' (z : Set (Fin 2 → K))) :=
  rfl

private theorem q2cFA2_dirZ_span_jShift21Inv_line (hK : Nat.card K = (2 ^ f) ^ 2)
    {u : Fin 3 → K} (hu : u ∉ Vsub 3 1) :
    Exch.dirZ K f (Submodule.span K (jShift21Inv K f ''
      ((Vsub 3 1 ⊔ K ∙ u : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)))) =
      Vsub 3 1 ⊔ K ∙ u := by
  have hβ : Submodule.span K (jShift21Inv K f ''
      ((Vsub 3 1 ⊔ K ∙ u : Submodule K (Fin 3 → K)) : Set (Fin 3 → K))) =
      K ∙ jShift21Inv K f u := q2cFA2_span_jShift21Inv_Vsub_sup_singleton u
  have hspan : Vsub 3 1 ⊔ K ∙ q2cFA2_wEmb u = Vsub 3 1 ⊔ K ∙ u := by
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [Submodule.span_singleton_le_iff_mem]
      change q2cFA2_wEmb u ∈ Vsub 3 1 ⊔ K ∙ u
      rw [Submodule.mem_sup]
      refine ⟨-q2cFA2_vEmb u, neg_mem (q2cFA2_vEmb_mem u), u,
        Submodule.mem_span_singleton_self u, ?_⟩
      rw [q2cFA2_wEmb_eq_sub, sub_eq_add_neg, add_comm]
    · apply sup_le le_sup_left
      rw [Submodule.span_singleton_le_iff_mem]
      change u ∈ Vsub 3 1 ⊔ K ∙ q2cFA2_wEmb u
      rw [Submodule.mem_sup]
      exact ⟨q2cFA2_vEmb u, q2cFA2_vEmb_mem u, q2cFA2_wEmb u,
        Submodule.mem_span_singleton_self _, q2cFA2_vEmb_add_wEmb u⟩
  rw [q2cFA2_dirZ_eq, hβ, q2cFA2_span_jShift21_singleton,
    q2cFA2_jShift21_jShift21Inv hK u, hspan]

theorem q2cFA2_dirZ_span_jShift21Inv_sup (hK : Nat.card K = (2 ^ f) ^ 2)
    {E : FlagK K 3} (hfar : E ∈ farSet 3 [0, 1, 3]) :
    Exch.dirZ K f (Submodule.span K (jShift21Inv K f ''
      ((E.E 1 ⊔ Vsub 3 1 : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)))) =
      E.E 1 ⊔ Vsub 3 1 := by
  have hline : finrank K (E.E 1) = 1 := E.dim 1 (by norm_num)
  obtain ⟨u, hu0, hEu⟩ := exists_eq_span_of_finrank_eq_one hline
  have huV : u ∉ Vsub 3 1 := by
    intro huV
    have hmem : u ∈ E.E 1 ⊓ Vsub 3 1 :=
      ⟨by rw [hEu]; exact Submodule.mem_span_singleton_self u, huV⟩
    rw [q2cFA2_farSet_inf_Vsub_one hfar] at hmem
    have hz : u ∈ (⊥ : Submodule K (Fin 3 → K)) := hmem
    exact hu0 (by simpa using hz)
  have hsup : E.E 1 ⊔ Vsub 3 1 = Vsub 3 1 ⊔ K ∙ u := by rw [hEu, sup_comm]
  rw [hsup]
  exact q2cFA2_dirZ_span_jShift21Inv_line hK huV

theorem q2cFA2_inf_dirZ_eq_bot (hK : Nat.card K = (2 ^ f) ^ 2) {E : FlagK K 3}
    (hfar : E ∈ farSet 3 [0, 1, 3]) {z : FlagK K 2}
    (hbu : E.E 1 ⊔ Vsub 3 1 ≠ Exch.dirZ K f (z.E 1)) :
    E.E 1 ⊓ Exch.dirZ K f (z.E 1) = ⊥ := by
  have hline : finrank K (E.E 1) = 1 := E.dim 1 (by norm_num)
  have hdir : finrank K (Exch.dirZ K f (z.E 1)) = 2 :=
    Exch.finrank_dirZ hK (z.dim 1 (by norm_num))
  have hVfin : finrank K (Vsub 3 1) = 1 :=
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)
  have hinfV : E.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ := q2cFA2_farSet_inf_Vsub_one hfar
  rcases Nat.eq_zero_or_pos (finrank K ↥(E.E 1 ⊓ Exch.dirZ K f (z.E 1))) with h0 | hpos
  · exact (Submodule.finrank_eq_zero).mp h0
  · exfalso
    have hle1 : finrank K ↥(E.E 1 ⊓ Exch.dirZ K f (z.E 1)) ≤ 1 := by
      simpa [hline] using
        Submodule.finrank_mono (inf_le_left : E.E 1 ⊓ Exch.dirZ K f (z.E 1) ≤ E.E 1)
    have h1 : finrank K ↥(E.E 1 ⊓ Exch.dirZ K f (z.E 1)) = 1 := by omega
    have heq : E.E 1 ⊓ Exch.dirZ K f (z.E 1) = E.E 1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hline])
    have hle : E.E 1 ≤ Exch.dirZ K f (z.E 1) := by rw [← heq]; exact inf_le_right
    apply hbu
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (E.E 1) (Vsub (K := K) 3 1)
    rw [hinfV, finrank_bot, add_zero, hline, hVfin] at hsum
    exact Submodule.eq_of_le_of_finrank_eq
      (sup_le hle (Exch.Vsub_le_dirZ (z.E 1))) (by rw [hsum]; omega)

theorem q2cFA2_isGateAt_prod {I J : Type} {C₁ C₂ : Type}
    {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂} (hX : X.Connected) (hY : Y.Connected)
    {R₁ : Set C₁} {R₂ : Set C₂} {y₁ g₁ : C₁} {y₂ g₂ : C₂} :
    IsGateAt (X.prod Y) (R₁ ×ˢ R₂) (y₁, y₂) (g₁, g₂) ↔
      IsGateAt X R₁ y₁ g₁ ∧ IsGateAt Y R₂ y₂ g₂ := by
  constructor
  · rintro ⟨⟨hg₁, hg₂⟩, h⟩
    refine ⟨⟨hg₁, fun z hz => ?_⟩, ⟨hg₂, fun z hz => ?_⟩⟩
    · have h' := h (z, g₂) (Set.mem_prod.mpr ⟨hz, hg₂⟩)
      rw [cdist_prod hX hY, cdist_prod hX hY, cdist_prod hX hY] at h'
      dsimp only at h'
      rw [cdist_self] at h'
      omega
    · have h' := h (g₁, z) (Set.mem_prod.mpr ⟨hg₁, hz⟩)
      rw [cdist_prod hX hY, cdist_prod hX hY, cdist_prod hX hY] at h'
      dsimp only at h'
      rw [cdist_self] at h'
      omega
  · rintro ⟨⟨hg₁, h₁⟩, ⟨hg₂, h₂⟩⟩
    refine ⟨⟨hg₁, hg₂⟩, fun z hz => ?_⟩
    rw [Set.mem_prod] at hz
    rw [cdist_prod hX hY, cdist_prod hX hY, cdist_prod hX hY]
    dsimp only
    rw [h₁ z.1 hz.1, h₂ z.2 hz.2]
    omega

theorem q2cFA2_isGateAt_gateFlag {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {E : FlagK K (m + 1)} (hE : E ∈ farSet (m + 1) d) {x₀ : FlagK K (m + 1)}
    (hx₀ : x₀ ∈ refSet K (m + 1) d) :
    IsGateAt (flagSys K m) (refSet K (m + 1) d) E (gateFlag hd hE) := by
  have hB : IsWeylDistanceBuilding (symCox m) (flagδ (K := K) m) :=
    isWeylDistanceBuilding_flag (K := K) (m := m)
  have hproj := resProj_eq_gateFlag (K := K) hd hE hx₀
  have hIso := isProjection_resProj hB (cutTypes m d) x₀ E
  rw [hproj] at hIso
  refine ⟨gateFlag_mem_refSet hd hE, fun z hz => ?_⟩
  have hzres : z ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ := by
    rw [residue_cutTypes_eq hd hx₀]
    exact hz
  have hgate := (IsProjection.gate hB hIso hzres).2
  rw [← length_flagδ_eq_cdist (K := K) m E z,
    ← length_flagδ_eq_cdist (K := K) m E (gateFlag hd hE),
    ← length_flagδ_eq_cdist (K := K) m (gateFlag hd hE) z]
  exact hgate

theorem q2cFA2_cdist_prod_eq_four {E F : FlagK K 3} {z z' : FlagK K 2}
    (h : cdist ((flagSys K 2).prod (flagSys K 1)) (E, z) (F, z') = 4) :
    cdist (flagSys K 2) E F = 3 ∧ cdist (flagSys K 1) z z' = 1 := by
  rw [cdist_prod (flagSys_connected K 2) (flagSys_connected K 1)] at h
  dsimp only at h
  have h2 : cdist (flagSys K 2) E F ≤ 3 := by
    rw [← length_flagδ_eq_cdist (K := K) 2 E F]
    simpa using length_flagδ_le (K := K) (m := 2) E F
  have h1 : cdist (flagSys K 1) z z' ≤ 1 := by
    rw [← length_flagδ_eq_cdist (K := K) 1 z z']
    simpa using length_flagδ_le (K := K) (m := 1) z z'
  omega

theorem q2cFA2_cdist_flagSys_two_eq_three_of_opp {E F : FlagK K 3} (h : Opp E F) :
    cdist (flagSys K 2) E F = 3 := by
  have h' := (opp_iff_length_flagδ E F).mp h
  rw [← length_flagδ_eq_cdist (K := K) 2 E F]
  simpa using h'

theorem q2cFA2_opp_of_cdist_flagSys_two_eq_three {E F : FlagK K 3}
    (h : cdist (flagSys K 2) E F = 3) : Opp E F := by
  have h' : (symCox 2).length (flagδ (K := K) 2 E F) = 3 := by
    rw [length_flagδ_eq_cdist (K := K) 2 E F]
    exact h
  rw [opp_iff_length_flagδ E F]
  simpa using h'

theorem q2cFA2_cdist_flagSys_one_eq_one {z z' : FlagK K 2} (h : z ≠ z') :
    cdist (flagSys K 1) z z' = 1 := by
  have hle : cdist (flagSys K 1) z z' ≤ 1 := by
    rw [← length_flagδ_eq_cdist (K := K) 1 z z']
    simpa using length_flagδ_le (K := K) (m := 1) z z'
  have hne : cdist (flagSys K 1) z z' ≠ 0 := by
    intro h0
    exact h ((cdist_eq_zero_iff (flagSys K 1) (flagSys_connected K 1)).mp h0)
  omega

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
