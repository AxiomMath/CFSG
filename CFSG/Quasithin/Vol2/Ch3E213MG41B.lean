module

public import CFSG.Quasithin.Vol2.Ch3E213MG41A
public import CFSG.Quasithin.Vol2.Ch3E213MG41W

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open LinearMap.BilinForm (orthogonal mem_orthogonal_iff)

variable {k : Type} [Field k] [CharP k 2]

@[expose] def centres (G₀ : Subgroup (antiSp k)) : Set (Fin 4 → k) :=
  {v | v ≠ 0 ∧ ∃ c : k, c ≠ 0 ∧ c ∈ Lam G₀ v}

variable {G₀ : Subgroup (antiSp k)}

theorem act_mem_centres {v : Fin 4 → k} (hv : v ∈ centres G₀) {g : antiSp k} (hg : g ∈ G₀) :
    natAct g v ∈ centres G₀ := by
  obtain ⟨hv0, c, hc, hcL⟩ := hv
  refine ⟨fun h => hv0 (act_injective g (by rw [h, act_zero])), c, hc, ?_⟩
  exact (mem_Lam_act hg).mpr hcL

theorem exists_mem_centres (hD : (transvSet G₀).Nonempty) : ∃ v, v ∈ centres G₀ := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨v, c, hv, hc, hcL, -⟩ := exists_of_mem_transvSet hd
  exact ⟨v, hv, c, hc, hcL⟩

theorem span_centres_eq_top (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty) :
    Submodule.span k (centres G₀) = ⊤ := by
  have hinv : ∀ g ∈ G₀, ∀ w ∈ Submodule.span k (centres G₀),
      natAct g w ∈ Submodule.span k (centres G₀) := by
    intro g hg w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (act_mem_centres hx hg)
    | zero => rw [act_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [act_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [act_smul]; exact Submodule.smul_mem _ r hx
  rcases hirr _ hinv with h | h
  · obtain ⟨v, hv⟩ := exists_mem_centres hD
    have hmem : v ∈ Submodule.span k (centres G₀) := Submodule.subset_span hv
    rw [h, Submodule.mem_bot] at hmem
    exact absurd hmem hv.1
  · exact h

theorem eq_zero_of_orth_centres (hspan : Submodule.span k (centres G₀) = ⊤) {x : Fin 4 → k}
    (h : ∀ v ∈ centres G₀, spBil x v = 0) : x = 0 := by
  have hle : Submodule.span k (centres G₀) ≤ LinearMap.ker (spBil x) := by
    rw [Submodule.span_le]
    intro v hv
    exact LinearMap.mem_ker.mpr (h v hv)
  rw [hspan] at hle
  apply eq_zero_of_bil_eq_zero
  intro y
  rw [bil_symm]
  exact LinearMap.mem_ker.mp (hle (Submodule.mem_top (x := y)))

theorem mem_or_orth_of_mapsTo {v : Fin 4 → k} {c : k} (hc : c ≠ 0)
    {W : Submodule k (Fin 4 → k)} (hW : ∀ w ∈ W, natAct (trv v c) w ∈ W) :
    v ∈ W ∨ ∀ w ∈ W, spBil w v = 0 := by
  by_cases h : ∀ w ∈ W, spBil w v = 0
  · exact Or.inr h
  · left
    simp only [not_forall] at h
    obtain ⟨w, hw, hwv⟩ := h
    have h1 : (c * spBil w v) • v ∈ W := by
      have := W.sub_mem (hW w hw) hw
      rwa [act_trv, add_sub_cancel_left] at this
    have h2 := W.smul_mem (c * spBil w v)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hwv), one_smul] at h2

@[expose] def DInv (G₀ : Subgroup (antiSp k)) (W : Submodule k (Fin 4 → k)) : Prop :=
  ∀ d ∈ transvSet G₀, ∀ w ∈ W, natAct d w ∈ W

theorem mem_or_mem_orth {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W) {v : Fin 4 → k}
    (hv : v ∈ centres G₀) : v ∈ W ∨ v ∈ orthogonal spBil W := by
  obtain ⟨hv0, c, hc, hcL⟩ := hv
  rcases mem_or_orth_of_mapsTo hc (hW _ (trv_mem_transvSet hv0 hc hcL)) with h | h
  · exact Or.inl h
  · exact Or.inr (mem_orthogonal_iff.mpr h)

omit [CharP k 2] in
theorem bil_isRefl : (spBil : LinearMap.BilinForm k (Fin 4 → k)).IsRefl := fun x y h => by
  rw [bil_symm]
  exact h

omit [CharP k 2] in
theorem bil_nondegenerate : (spBil : LinearMap.BilinForm k (Fin 4 → k)).Nondegenerate :=
  minorForm_nondegenerate

omit [CharP k 2] in
theorem orth_orth (W : Submodule k (Fin 4 → k)) : orthogonal spBil (orthogonal spBil W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal bil_nondegenerate bil_isRefl W

omit [CharP k 2] in
theorem finrank_orth (W : Submodule k (Fin 4 → k)) :
    Module.finrank k (orthogonal spBil W) = 4 - Module.finrank k W := by
  rw [LinearMap.BilinForm.finrank_orthogonal bil_nondegenerate, Module.finrank_fin_fun]

theorem le_orth_of_finrank_eq_one {X : Submodule k (Fin 4 → k)} (hX : Module.finrank k X = 1) :
    X ≤ orthogonal spBil X := by
  obtain ⟨⟨u, hu⟩, -, hspan⟩ := finrank_eq_one_iff'.mp hX
  have hmem : ∀ x ∈ X, ∃ a : k, x = a • u := by
    intro x hx
    obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  intro x hx
  rw [mem_orthogonal_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := hmem x hx
  obtain ⟨b, rfl⟩ := hmem y hy
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, bil_self, mul_zero, mul_zero]

section Reducible

variable (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
  {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W)
include hirr hD hW

theorem inf_orth_eq_bot : W ⊓ orthogonal spBil W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxW, hxO⟩
  apply eq_zero_of_orth_centres (span_centres_eq_top hirr hD)
  intro v hv
  rcases mem_or_mem_orth hW hv with h | h
  · rw [bil_symm]
    exact (mem_orthogonal_iff.mp hxO) v h
  · exact (mem_orthogonal_iff.mp h) x hxW

theorem finrank_eq_two (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) : Module.finrank k W = 2 := by
  have hinf := inf_orth_eq_bot hirr hD hW
  have hle : Module.finrank k W ≤ 4 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at this
  have h0 : Module.finrank k W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have h4 : Module.finrank k W ≠ 4 := fun h =>
    hWt (Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun]))
  have h1 : Module.finrank k W ≠ 1 := by
    intro h
    have hle' := le_orth_of_finrank_eq_one h
    have : W = ⊥ := by
      rw [← hinf]
      exact le_antisymm (le_inf le_rfl hle') inf_le_left
    exact hW0 this
  have h3 : Module.finrank k W ≠ 3 := by
    intro h
    have hO : Module.finrank k (orthogonal spBil W) = 1 := by rw [finrank_orth, h]
    have hle' := le_orth_of_finrank_eq_one hO
    rw [orth_orth] at hle'
    have : orthogonal spBil W = ⊥ := by
      rw [← hinf]
      exact le_antisymm (le_inf hle' le_rfl) inf_le_right
    rw [this, finrank_bot] at hO
    exact zero_ne_one hO
  omega

end Reducible

omit [CharP k 2] in
theorem map_orth (g : antiSp k) (W : Submodule k (Fin 4 → k)) :
    (orthogonal spBil W).map (natLin g) = orthogonal spBil (W.map (natLin g)) := by
  ext y
  simp only [Submodule.mem_map, mem_orthogonal_iff, natLin_apply']
  constructor
  · rintro ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩
    rw [bil_act]
    exact hx w hw
  · intro hy
    refine ⟨natAct g⁻¹ y, fun w hw => ?_, act_act_inv g y⟩
    rw [← bil_act g, act_act_inv]
    exact hy _ ⟨w, hw, rfl⟩

theorem dInv_map {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W) {g : antiSp k} (hg : g ∈ G₀) :
    DInv G₀ (W.map (natLin g)) := by
  intro d hd y hy
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
  have hd' := conj_mem_transvSet hd (G₀.inv_mem hg)
  rw [inv_inv] at hd'
  refine Submodule.mem_map.mpr ⟨natAct (g⁻¹ * d * g) w, hW _ hd' w hw, ?_⟩
  rw [natLin_apply', natLin_apply', ← natAct_mul, ← natAct_mul]
  congr 1
  group

omit [CharP k 2] in
theorem finrank_map (g : antiSp k) (W : Submodule k (Fin 4 → k)) :
    Module.finrank k (W.map (natLin g)) = Module.finrank k W := by
  have hinj : Function.Injective (natLin g) := fun x y h => by
    rw [natLin_apply', natLin_apply'] at h
    exact act_injective g h
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

theorem span_centres_inf (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
    {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W) :
    Submodule.span k (centres G₀ ∩ W) = W := by
  set a := Submodule.span k (centres G₀ ∩ W)
  set b := Submodule.span k (centres G₀ ∩ orthogonal spBil W)
  have haW : a ≤ W := by
    rw [Submodule.span_le]
    exact Set.inter_subset_right
  have hbO : b ≤ orthogonal spBil W := by
    rw [Submodule.span_le]
    exact Set.inter_subset_right
  have hab : a ⊔ b = ⊤ := by
    rw [eq_top_iff, ← span_centres_eq_top hirr hD, Submodule.span_le]
    intro v hv
    rcases mem_or_mem_orth hW hv with h | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨hv, h⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨hv, h⟩)
  have hmod := sup_inf_assoc_of_le b haW
  rw [hab, top_inf_eq] at hmod
  have hbW : b ⊓ W = ⊥ := by
    rw [eq_bot_iff, ← inf_orth_eq_bot hirr hD hW]
    exact fun x hx => ⟨hx.2, hbO hx.1⟩
  rw [hbW, sup_bot_eq] at hmod
  exact hmod.symm

theorem map_eq_or_map_eq (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
    {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    {g : antiSp k} (hg : g ∈ G₀) :
    W.map (natLin g) = W ∨ W.map (natLin g) = orthogonal spBil W := by
  set W' := W.map (natLin g) with hW'def
  have hW' : DInv G₀ W' := dInv_map hW hg
  have h2 := finrank_eq_two hirr hD hW hW0 hWt
  have h2' : Module.finrank k W' = 2 := by rw [finrank_map, h2]
  have h2'' : Module.finrank k (orthogonal spBil W') = 2 := by rw [finrank_orth, h2']
  have hspan := span_centres_inf hirr hD hW
  by_cases hA : centres G₀ ∩ W ⊆ W'
  · left
    have hle : W ≤ W' := by
      rw [← hspan, Submodule.span_le]
      exact hA
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, h2'])).symm
  by_cases hB : centres G₀ ∩ W ⊆ orthogonal spBil W'
  · right
    have hle : W ≤ orthogonal spBil W' := by
      rw [← hspan, Submodule.span_le]
      exact hB
    have hWO : W = orthogonal spBil W' :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, h2''])
    rw [hWO, orth_orth]
  exfalso
  obtain ⟨a, ⟨haC, haW⟩, haW'⟩ := Set.not_subset.mp hA
  obtain ⟨b, ⟨hbC, hbW⟩, hbO⟩ := Set.not_subset.mp hB
  have haO : a ∈ orthogonal spBil W' := (mem_or_mem_orth hW' haC).resolve_left haW'
  have hbW' : b ∈ W' := (mem_or_mem_orth hW' hbC).resolve_right hbO
  have hab : spBil a b = 0 := by
    rw [bil_symm]
    exact (mem_orthogonal_iff.mp haO) b hbW'
  have hli : LinearIndependent k ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : s = 0 := by
      by_contra hs
      apply haW'
      have ha : a = (-(s⁻¹ * t)) • b := by
        have := congrArg (fun x => s⁻¹ • x) hst
        simp only [smul_add, smul_smul, inv_mul_cancel₀ hs, one_smul, smul_zero] at this
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left this
      rw [ha]
      exact W'.smul_mem _ hbW'
    subst hs
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hbC.1⟩
  have hspan2 : Submodule.span k (Set.range ![a, b]) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact haW
      · exact hbW
    · rw [h2, finrank_span_eq_card hli, Fintype.card_fin]
  have hiso : W ≤ orthogonal spBil W := by
    rw [← hspan2]
    intro x hx
    rw [mem_orthogonal_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy
    obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
    simp [Fin.sum_univ_two, LinearMap.BilinForm.add_right, bil_self, hab, bil_symm b a]
  have : W = ⊥ := by
    rw [← inf_orth_eq_bot hirr hD hW]
    exact le_antisymm (le_inf le_rfl hiso) inf_le_left
  exact hW0 this

theorem decW_of_reducible (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
    {W : Submodule k (Fin 4 → k)} (hW : DInv G₀ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    G41DecW G₀ := by
  refine ⟨W, orthogonal spBil W, finrank_eq_two hirr hD hW hW0 hWt, rfl,
    inf_orth_eq_bot hirr hD hW, fun g hg => ?_⟩
  rcases map_eq_or_map_eq hirr hD hW hW0 hWt hg with h | h
  · left
    exact ⟨h, by rw [map_orth, h]⟩
  · right
    exact ⟨h, by rw [map_orth, h, orth_orth]⟩

end CFSG.Quasithin.Ch3E213M.G41
