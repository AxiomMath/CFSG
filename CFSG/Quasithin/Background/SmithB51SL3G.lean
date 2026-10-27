module

public import CFSG.Quasithin.Background.SmithB51SL3F

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def elT {i j : Fin 3} (hij : i ≠ j) (c : K) : ↥(StatedSL 3 K) :=
  transv (c • Pi.single i 1) (Pi.single j 1) (by
    rw [dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one, Pi.single_apply]
    simp [hij])

theorem slAct_elT {i j : Fin 3} (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    slAct (elT hij c) v = v + Pi.single i (c * v j) := by
  rw [elT, slAct_transv]
  congr 1
  ext k
  simp only [Pi.smul_apply, smul_eq_mul, single_dotProduct, one_mul, Pi.single_apply]
  split_ifs <;> ring

@[expose] noncomputable def xW (w : Fin 3 → K) (hw : w 2 = 0) : ↥(StatedSL 3 K) :=
  transv w (Pi.single 2 1) (by rw [single_dotProduct, one_mul, hw])

theorem slAct_xW (w : Fin 3 → K) (hw : w 2 = 0) (v : Fin 3 → K) :
    slAct (xW w hw) v = v + v 2 • w := by
  rw [xW, slAct_transv, single_dotProduct, one_mul]

theorem xW_mem (w : Fin 3 → K) (hw : w 2 = 0) : xW w hw ∈ axisSub (stdAxis K) := by
  refine ⟨fun x hx => ?_, fun v => ?_⟩
  · rw [slAct_xW, mem_coordHyp.1 hx, zero_smul, add_zero]
  · rw [slAct_xW, add_sub_cancel_left, mem_coordHyp, Pi.smul_apply, hw, smul_zero]

@[expose] def stabH (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) where
  carrier := {g | ∀ v, slAct g v 2 = v 2}
  one_mem' := fun v => by rw [slAct_one]
  mul_mem' := fun {g h} hg hh v => by rw [slAct_mul, hg, hh]
  inv_mem' := fun {g} hg v => by
    have := hg (slAct g⁻¹ v)
    rw [slAct_slAct_inv] at this
    exact this.symm

@[expose] def levi (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) where
  carrier := {g | g ∈ stabH K ∧ slAct g (Pi.single 2 1) = Pi.single 2 1}
  one_mem' := ⟨(stabH K).one_mem, slAct_one _⟩
  mul_mem' := fun {g h} hg hh => ⟨(stabH K).mul_mem hg.1 hh.1, by rw [slAct_mul, hh.2, hg.2]⟩
  inv_mem' := fun {g} hg => ⟨(stabH K).inv_mem hg.1, by
    have := slAct_inv_slAct g (Pi.single 2 1)
    rwa [hg.2] at this⟩

theorem levi_le_stabH : levi K ≤ stabH K := fun _ hg => hg.1

theorem axisSub_le_stabH : axisSub (stdAxis K) ≤ stabH K := by
  intro g hg v
  have := mem_coordHyp.1 (hg.2 v)
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

theorem elT_mem_levi {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2) (c : K) :
    elT hij c ∈ levi K := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [slAct_elT, Pi.add_apply, Pi.single_apply]
    simp [Ne.symm hi]
  · rw [slAct_elT]
    have : (Pi.single 2 (1 : K) : Fin 3 → K) j = 0 := by simp [hj]
    rw [this, mul_zero, Pi.single_zero, add_zero]

@[expose] def rootP (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) where
  carrier := {g | ∃ c : K, g = elT (show (0 : Fin 3) ≠ 1 by decide) c}
  one_mem' := ⟨0, ext_slAct fun v => by simp [slAct_elT, slAct_one]⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ext_slAct fun v => ?_⟩
    rw [slAct_mul, slAct_elT, slAct_elT, slAct_elT]
    ext k
    fin_cases k
    · simp; ring
    · simp
    · simp
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, ext_slAct fun v => ?_⟩
    have h1 : ∀ v, slAct (elT (show (0 : Fin 3) ≠ 1 by decide) (-c))
        (slAct (elT (show (0 : Fin 3) ≠ 1 by decide) c) v) = v := by
      intro v
      rw [slAct_elT, slAct_elT]
      ext k
      fin_cases k <;> simp
    have := h1 (slAct (elT (show (0 : Fin 3) ≠ 1 by decide) c)⁻¹ v)
    rw [slAct_slAct_inv] at this
    exact this.symm

theorem conj_xW {g : ↥(StatedSL 3 K)} (hg : g ∈ levi K) (w : Fin 3 → K) (hw : w 2 = 0) :
    g * xW w hw * g⁻¹ = xW (slAct g w) (by rw [hg.1 w]; exact hw) := by
  apply ext_slAct
  intro v
  rw [slAct_mul, slAct_mul, slAct_xW, slAct_xW, slAct_add, slAct_smul, slAct_slAct_inv,
    ((levi K).inv_mem hg).1 v]

theorem exists_xW_mul_levi {h : ↥(StatedSL 3 K)} (hh : h ∈ stabH K) :
    ∃ (w : Fin 3 → K) (hw : w 2 = 0) (k : ↥(StatedSL 3 K)), k ∈ levi K ∧ h = xW w hw * k := by
  have hw : (slAct h (Pi.single 2 1) - Pi.single 2 1 : Fin 3 → K) 2 = 0 := by
    rw [Pi.sub_apply, hh, sub_self]
  refine ⟨_, hw, (xW _ hw)⁻¹ * h, ⟨(stabH K).mul_mem ((stabH K).inv_mem
    (axisSub_le_stabH (xW_mem _ hw))) hh, ?_⟩, by group⟩
  have h1 : slAct (xW _ hw) (Pi.single 2 1) = slAct h (Pi.single 2 1) := by
    rw [slAct_xW, Pi.single_eq_same, one_smul]
    abel
  rw [slAct_mul]
  exact (congrArg (slAct (xW _ hw)⁻¹) h1).symm.trans (slAct_inv_slAct _ _)

theorem eq_single_of_levi_fix {v : Fin 3 → K} (hv : ∀ g ∈ levi K, slAct g v = v) :
    v = Pi.single 2 (v 2) := by
  have h1 := hv _ (elT_mem_levi (show (0 : Fin 3) ≠ 1 by decide) (by decide) (by decide) 1)
  have h2 := hv _ (elT_mem_levi (show (1 : Fin 3) ≠ 0 by decide) (by decide) (by decide) 1)
  rw [slAct_elT, add_eq_left, one_mul, Pi.single_eq_zero_iff] at h1 h2
  ext k
  fin_cases k <;> simp [h1, h2]

theorem coe_apply_eq (g : ↥(StatedSL 3 K)) (i j : Fin 3) :
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = slAct g (Pi.single j 1) i := by
  show _ = (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1) i
  rw [Matrix.mulVec_single_one]
  rfl

theorem stabilizer_levi :
    MulAction.stabilizer (levi K) (Pi.single 0 1 : Fin 3 → K) = (rootP K).subgroupOf (levi K) := by
  ext ⟨g, hg⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h0
    have h0' : slAct g (Pi.single 0 1) = Pi.single 0 1 := h0
    have h2 : slAct g (Pi.single 2 1) = Pi.single 2 1 := hg.2
    have h12 : slAct g (Pi.single 1 1) 2 = 0 := by rw [hg.1]; simp
    have hdet := H.SL3Pair.mem_statedSL_iff.1 g.2
    rw [Matrix.det_fin_three] at hdet
    simp only [coe_apply_eq, h0', h2, h12] at hdet
    simp at hdet
    refine ⟨slAct g (Pi.single 1 1) 0, ext_slAct fun v => ?_⟩
    have hv : v = (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1) + v 2 • Pi.single 2 1 := by
      ext k; fin_cases k <;> simp
    have he1 : slAct g (Pi.single 1 1) =
        Pi.single 0 (slAct g (Pi.single 1 1) 0) + Pi.single 1 1 := by
      ext k; fin_cases k <;> simp [hdet, h12]
    rw [slAct_elT]
    conv_lhs => rw [hv]
    rw [slAct_add, slAct_add, slAct_smul, slAct_smul, slAct_smul, h0', h2, he1]
    conv_rhs => rw [hv]
    ext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp
      ring
    · simp
    · simp
  · rintro ⟨c, rfl⟩
    show slAct (elT (show (0 : Fin 3) ≠ 1 by decide) c) (Pi.single 0 1) = Pi.single 0 1
    rw [slAct_elT]
    simp

theorem orbit_levi :
    MulAction.orbit (levi K) (Pi.single 0 1 : Fin 3 → K) = {v | v 2 = 0 ∧ v ≠ 0} := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨by
      show slAct g (Pi.single 0 1) 2 = 0
      rw [hg.1]; simp, fun h0 => ?_⟩
    have h0' : slAct g (Pi.single 0 1) = slAct g 0 := by
      rw [slAct_zero]; exact h0
    exact one_ne_zero (congrFun (slAct_injective g h0') 0 |>.trans (by simp))
  · rintro ⟨hv2, hv0⟩
    have t01 := fun c => elT_mem_levi (K := K) (show (0 : Fin 3) ≠ 1 by decide) (by decide)
      (by decide) c
    have t10 := fun c => elT_mem_levi (K := K) (show (1 : Fin 3) ≠ 0 by decide) (by decide)
      (by decide) c
    by_cases hv1 : v 1 = 0
    · have hv00 : v 0 ≠ 0 := by
        intro h
        apply hv0
        ext k; fin_cases k <;> simp [h, hv1, hv2]
      refine ⟨⟨_, (levi K).mul_mem ((levi K).mul_mem (t10 (-(v 0)⁻¹)) (t01 (v 0 - 1)))
        (t10 1)⟩, ?_⟩
      show slAct (_ * _ * _) _ = v
      rw [slAct_mul, slAct_mul, slAct_elT, slAct_elT, slAct_elT]
      ext k
      fin_cases k
      · simp
      · simp [hv1, inv_mul_cancel₀ hv00]
      · simp [hv2]
    · refine ⟨⟨_, (levi K).mul_mem (t01 ((v 0 - 1) / v 1)) (t10 (v 1))⟩, ?_⟩
      show slAct (_ * _) _ = v
      rw [slAct_mul, slAct_elT, slAct_elT]
      ext k
      fin_cases k
      · simp
        field_simp
        ring
      · simp
      · simp [hv2]

theorem ncard_axis_ne_zero [Finite K] :
    {v : Fin 3 → K | v 2 = 0 ∧ v ≠ 0}.ncard = Nat.card K ^ 2 - 1 := by
  have h1 : {v : Fin 3 → K | v 2 = 0 ∧ v ≠ 0} =
      ((stdAxis K : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)) \ {0} := by
    ext v
    simp [mem_coordHyp]
  have h2 : ((stdAxis K : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)).ncard =
      Nat.card K ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    show Nat.card ↥(stdAxis K) = _
    rw [Module.natCard_eq_pow_finrank (K := K), finrank_coordHyp]
  rw [h1, Set.ncard_sdiff_singleton_of_mem (Submodule.zero_mem _), h2]

theorem index_rootP [Finite K] :
    ((rootP K).subgroupOf (levi K)).index = Nat.card K ^ 2 - 1 := by
  rw [← stabilizer_levi, MulAction.index_stabilizer, orbit_levi, ncard_axis_ne_zero]

theorem rootP_le_levi : rootP K ≤ levi K := by
  rintro _ ⟨c, rfl⟩
  exact elT_mem_levi _ (by decide) (by decide) c

theorem card_rootP [Finite K] : Nat.card (rootP K) = Nat.card K := by
  set e : K → ↥(rootP K) := fun c => ⟨elT (show (0 : Fin 3) ≠ 1 by decide) c, c, rfl⟩ with he
  have hinj : Function.Injective e := by
    intro c c' h
    have := congrArg (fun g : ↥(rootP K) => slAct (g : ↥(StatedSL 3 K)) (Pi.single 1 1) 0) h
    simpa [he, slAct_elT] using this
  have hsurj : Function.Surjective e := by
    rintro ⟨g, c, rfl⟩
    exact ⟨c, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩)).symm

theorem stabilizer_stabH :
    MulAction.stabilizer (stabH K) (Pi.single 2 1 : Fin 3 → K) =
      (levi K).subgroupOf (stabH K) := by
  ext ⟨g, hg⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩

theorem orbit_stabH :
    MulAction.orbit (stabH K) (Pi.single 2 1 : Fin 3 → K) =
      (fun w => w + Pi.single 2 1) ''
        ((stdAxis K : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)) := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨slAct g (Pi.single 2 1) - Pi.single 2 1, ?_, by
      show slAct g (Pi.single 2 1) - Pi.single 2 1 + Pi.single 2 1 = slAct g (Pi.single 2 1)
      exact sub_add_cancel _ _⟩
    show (slAct g _ - _) 2 = 0
    rw [Pi.sub_apply, hg, sub_self]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨xW w (mem_coordHyp.1 hw), axisSub_le_stabH (xW_mem w _)⟩, ?_⟩
    show slAct (xW w (mem_coordHyp.1 hw)) (Pi.single 2 1) = w + Pi.single 2 1
    rw [slAct_xW, Pi.single_eq_same, one_smul, add_comm]

theorem index_levi_stabH [Finite K] :
    ((levi K).subgroupOf (stabH K)).index = Nat.card K ^ 2 := by
  rw [← stabilizer_stabH, MulAction.index_stabilizer, orbit_stabH,
    Set.ncard_image_of_injective _ (add_left_injective _), ← Nat.card_coe_set_eq]
  show Nat.card ↥(stdAxis K) = _
  rw [Module.natCard_eq_pow_finrank (K := K), finrank_coordHyp]

theorem index_stabH [Finite K] : (stabH K).index = Nat.card K ^ 3 - 1 := by
  have := Fintype.ofFinite K
  have h1 := Subgroup.index_mul_card (stabH K)
  have h2 := Subgroup.relIndex_mul_card (levi K) (stabH K)
  have h3 := Subgroup.relIndex_mul_card (rootP K) (levi K)
  rw [inf_eq_left.2 levi_le_stabH] at h2
  rw [inf_eq_left.2 rootP_le_levi, card_rootP] at h3
  have e2 : (levi K).relIndex (stabH K) = Nat.card K ^ 2 := index_levi_stabH
  have e3 : (rootP K).relIndex (levi K) = Nat.card K ^ 2 - 1 := index_rootP
  rw [e2] at h2
  rw [e3] at h3
  rw [card_statedSL_three_eq, ← Nat.card_eq_fintype_card, ← h2, ← h3] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  set q := Nat.card K with hqdef
  have hq2 : 0 < q ^ 2 - 1 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hpos : 0 < q ^ 2 * ((q ^ 2 - 1) * q) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

theorem odd_index_rootP [Finite K] (hq : 2 ∣ Nat.card K) :
    ¬ 2 ∣ ((rootP K).subgroupOf (levi K)).index := by
  rw [index_rootP]
  have h1 : 2 ∣ Nat.card K ^ 2 := dvd_pow hq (by norm_num)
  have h2 : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  omega

theorem odd_index_stabH [Finite K] (hq : 2 ∣ Nat.card K) : ¬ 2 ∣ (stabH K).index := by
  rw [index_stabH]
  have h1 : 2 ∣ Nat.card K ^ 3 := dvd_pow hq (by norm_num)
  have h2 : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
  omega

theorem exists_smul_of_levi {ψ : (Fin 3 → K) → (Fin 3 → K)}
    (hadd : ∀ w w', w 2 = 0 → w' 2 = 0 → ψ (w + w') = ψ w + ψ w')
    (hcomm : ∀ g ∈ levi K, ∀ w, w 2 = 0 → ψ (slAct g w) = slAct g (ψ w)) :
    ∃ a : K, ∀ w, w 2 = 0 → ψ w = a • w := by
  set a := ψ (Pi.single 0 1) 0 with ha
  set d := ψ (Pi.single 1 1) 1 with hd
  have t01 := fun c => elT_mem_levi (K := K) (show (0 : Fin 3) ≠ 1 by decide) (by decide)
    (by decide) c
  have t10 := fun c => elT_mem_levi (K := K) (show (1 : Fin 3) ≠ 0 by decide) (by decide)
    (by decide) c
  have h0 : ∀ c, ψ (Pi.single 0 c) = Pi.single 0 (c * d) := by
    intro c
    have h := hcomm _ (t01 c) (Pi.single 1 1) (by simp)
    rw [slAct_elT, slAct_elT, Pi.single_eq_same, mul_one, hadd _ _ (by simp) (by simp)] at h
    exact add_left_cancel h
  have h1 : ∀ c, ψ (Pi.single 1 c) = Pi.single 1 (c * a) := by
    intro c
    have h := hcomm _ (t10 c) (Pi.single 0 1) (by simp)
    rw [slAct_elT, slAct_elT, Pi.single_eq_same, mul_one, hadd _ _ (by simp) (by simp)] at h
    exact add_left_cancel h
  have had : a = d := by
    have := h0 1
    rw [one_mul] at this
    rw [ha, this, Pi.single_eq_same]
  refine ⟨a, fun w hw => ?_⟩
  have hw' : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) := by
    ext k
    fin_cases k <;> simp [hw]
  rw [hw', hadd _ _ (by simp) (by simp), h0, h1, ← had]
  ext k
  fin_cases k <;> simp [mul_comm]

theorem eq_top_of_slAct_mem {S : AddSubgroup (Fin 3 → K)}
    (hS : ∀ g : ↥(StatedSL 3 K), ∀ v ∈ S, slAct g v ∈ S) {v : Fin 3 → K} (hv : v ∈ S)
    (hne : v ≠ 0) : S = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hne' : ∀ j, j ≠ i → ∀ t : K, Pi.single j t ∈ S := by
    intro j hji t
    have h := S.sub_mem (hS (elT hji (t / v i)) v hv) hv
    rwa [slAct_elT, add_sub_cancel_left, div_mul_cancel₀ _ hi] at h
  have hall : ∀ k (t : K), Pi.single k t ∈ S := by
    intro k t
    by_cases hk : k = i
    · subst hk
      obtain ⟨j, hj⟩ : ∃ j, j ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
      have h1 := hne' j hj 1
      have h := S.sub_mem (hS (elT (Ne.symm hj) t) _ h1) h1
      rwa [slAct_elT, add_sub_cancel_left, Pi.single_eq_same, mul_one] at h
    · exact hne' k hk t
  rw [eq_top_iff]
  intro w _
  have hw : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) + Pi.single 2 (w 2) := by
    ext k
    fin_cases k <;> simp
  rw [hw]
  exact S.add_mem (S.add_mem (hall 0 _) (hall 1 _)) (hall 2 _)

end B5

end CFSG.Quasithin
