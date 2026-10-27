module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenAct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {M L : Subgroup (MulAut W)} {Z : Subgroup W}

theorem SevenCfg.exists_conj_ne (h : SevenCfg M L Z) :
    ∃ Y ∈ conjSubs M Z, ∃ l ∈ L, ∃ y ∈ Y, l y ≠ y := by
  by_contra hcon
  have hL1 : ∀ l ∈ L, l = 1 := fun l hl =>
    h.eq_one_of_fix_all fun Y hY y hy => by
      by_contra hne
      exact hcon ⟨Y, hY, l, hl, y, hy, hne⟩
  have hbot : L = ⊥ := (Subgroup.eq_bot_iff_forall L).2 hL1
  have hcard := h.card_L
  rw [hbot, Subgroup.card_bot] at hcard
  omega

private theorem s16c167_ne_map_of_normalizer {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) {Y : Subgroup W}
    (hY : ∃ l ∈ L, ∃ y ∈ Y, l y ≠ y) : ∃ l ∈ L, ∃ y ∈ Y.map g.toMonoidHom, l y ≠ y := by
  obtain ⟨l, hl, y, hy, hly⟩ := hY
  refine ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg l).1 hl, g y,
    Subgroup.mem_map.2 ⟨y, hy, rfl⟩, fun h => hly ?_⟩
  have h1 : g (l y) = g y := by simpa [MulAut.mul_apply] using h
  exact g.injective h1

private theorem s16c167_conj_fix_of_not_normalizer (h : SevenCfg M L Z) {g : MulAut W}
    (hgM : g ∈ M) (hgn : g ∉ normalizer (L : Set (MulAut W))) {Y : Subgroup W}
    (hY : Y ∈ conjSubs M Z) (hI : ∃ l ∈ L, ∃ y ∈ Y, l y ≠ y) :
    ∀ l ∈ L, ∀ y ∈ Y, (g * l * g⁻¹) y = y := by
  obtain ⟨l₀, hl₀, y₀, hy₀, hne⟩ := hI
  have hYle : Y ≤ commSub ⊤ L := h.le_commSub_of_ne hY hl₀ hy₀ hne
  have hfix : commSub ⊤ L ≤ fixV (L.map (MulAut.conj g).toMonoidHom) :=
    commSub_eq_bot_iff.1 (h.commute g hgM hgn)
  intro l hl y hy
  exact (mem_fixV.1 (hfix (hYle hy))) (g * l * g⁻¹) (Subgroup.mem_map.2 ⟨l, hl, rfl⟩)

private theorem s16c167_block (h : SevenCfg M L Z) (π : Equiv.Perm ↥(conjSubs M Z)) :
    π '' {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} =
        {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} ∨
      Disjoint (π '' {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y})
        {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} := by
  classical
  obtain ⟨g, hgM, hgπ⟩ := h.perm π
  by_cases hgn : g ∈ normalizer (L : Set (MulAut W))
  · left
    have hcard : Nat.card ↥(conjSubs M Z) = 4 := by
      rw [Nat.card_coe_set_eq]
      exact h.ncard
    haveI : Finite ↥(conjSubs M Z) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hsub : π '' {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} ⊆
        {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} := by
      rintro _ ⟨Y, hY, rfl⟩
      have h1 := s16c167_ne_map_of_normalizer hgn hY
      rw [hgπ Y] at h1
      exact h1
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [Set.ncard_image_of_injective _ π.injective]
  · right
    rw [Set.disjoint_left]
    rintro _ ⟨Y, hY, rfl⟩ hπY
    have h1 := s16c167_conj_fix_of_not_normalizer h hgM hgn (π Y).2 hπY
    obtain ⟨l, hl, y, hy, hly⟩ := hY
    apply hly
    have h2 : (g * l * g⁻¹) (g y) = g y :=
      h1 l hl (g y) (by rw [← hgπ Y]; exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    have h3 : g (l y) = g y := by simpa [MulAut.mul_apply] using h2
    exact g.injective h3

theorem SevenCfg.exists_ne_of_mem (h : SevenCfg M L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs M Z) :
    ∃ l ∈ L, ∃ y ∈ Y, l y ≠ y := by
  classical
  obtain ⟨Y₀, hY₀, l₀, hl₀, y₀, hy₀, hne₀⟩ := h.exists_conj_ne
  have hI : ({Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y}).Nonempty :=
    ⟨⟨Y₀, hY₀⟩, l₀, hl₀, y₀, hy₀, hne₀⟩
  rcases s16c167_block_trivial hI (s16c167_block h) with huniv | hone
  · have hmem : (⟨Y, hY⟩ : ↥(conjSubs M Z)) ∈
        {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} := by
      rw [huniv]
      exact Set.mem_univ _
    exact hmem
  · exfalso
    obtain ⟨Y₁, hY₁⟩ := Set.ncard_eq_one.1 hone
    have hY₁mem : (Y₁ : Subgroup W) ∈ conjSubs M Z := Y₁.2
    have hmoved : ∀ k ∈ L, k ≠ 1 → ∃ y' ∈ (Y₁ : Subgroup W), k y' ≠ y' := by
      intro k hk hk1
      by_contra hcon
      apply hk1
      refine h.eq_one_of_fix_all fun Y' hY' y' hy' => ?_
      by_contra hne
      have hmem : (⟨Y', hY'⟩ : ↥(conjSubs M Z)) ∈
          {Y : ↥(conjSubs M Z) | ∃ l ∈ L, ∃ y ∈ (Y : Subgroup W), l y ≠ y} :=
        ⟨k, hk, y', hy', hne⟩
      rw [hY₁] at hmem
      have hYY : (⟨Y', hY'⟩ : ↥(conjSubs M Z)) = Y₁ := hmem
      exact hcon ⟨y', by rw [← hYY]; exact hy', hne⟩
    have hcard8 : Nat.card ↥(Y₁ : Subgroup W) = 8 := h.card_of_mem hY₁mem
    haveI : Nontrivial ↥(Y₁ : Subgroup W) :=
      (Finite.one_lt_card_iff_nontrivial (α := ↥(Y₁ : Subgroup W))).1 (by omega)
    obtain ⟨y₁, hy₁⟩ : ∃ y : ↥(Y₁ : Subgroup W), y ≠ 1 := exists_ne 1
    let f : ↥L → ↥(Y₁ : Subgroup W) := fun l =>
      ⟨(l : MulAut W) (y₁ : W), by
        have hm := h.map_eq_of_mem l.2 hY₁mem
        have hmem : (l : MulAut W) (y₁ : W) ∈ (Y₁ : Subgroup W).map (l : MulAut W).toMonoidHom :=
          Subgroup.mem_map.2 ⟨y₁, y₁.2, rfl⟩
        rwa [hm] at hmem⟩
    haveI : Finite ↥(Y₁ : Subgroup W) := Nat.finite_of_card_ne_zero (by rw [hcard8]; norm_num)
    haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [h.card_L]; norm_num)
    have hnotinj : ¬ Function.Injective f := fun hinj => by
      have hle := Nat.card_le_card_of_injective f hinj
      rw [hcard8, h.card_L] at hle
      omega
    obtain ⟨a, b, hfab, hab⟩ := Function.not_injective_iff.1 hnotinj
    have hfab' : (a : MulAut W) (y₁ : W) = (b : MulAut W) (y₁ : W) := congrArg Subtype.val hfab
    have hk : (b : MulAut W)⁻¹ * (a : MulAut W) ∈ L :=
      L.mul_mem (L.inv_mem b.2) a.2
    have hk1 : (b : MulAut W)⁻¹ * (a : MulAut W) ≠ 1 := by
      intro h1
      apply hab
      apply Subtype.ext
      exact (inv_mul_eq_one.1 h1).symm
    have hky : ((b : MulAut W)⁻¹ * (a : MulAut W)) (y₁ : W) = (y₁ : W) := by
      rw [MulAut.mul_apply, hfab']
      exact MulAut.inv_apply_self _ _ _
    obtain ⟨y', hy', hky'⟩ := hmoved _ hk hk1
    have h1 := h.eq_one_of_fixed hY₁mem hk hy' hky' y₁.2 hky
    exact hy₁ (Subtype.ext h1)

theorem SevenCfg.le_normalizer (h : SevenCfg M L Z) :
    M ≤ normalizer (L : Set (MulAut W)) := by
  intro g hgM
  by_contra hgn
  have hZ : Z ∈ conjSubs M Z := ⟨1, M.one_mem, (s16c167_map_one_aut Z).symm⟩
  have hgZ : Z.map g.toMonoidHom ∈ conjSubs M Z := SevenCfg.map_mem hgM hZ
  have h1 := s16c167_conj_fix_of_not_normalizer h hgM hgn hgZ (h.exists_ne_of_mem hgZ)
  obtain ⟨l, hl, z, hz, hlz⟩ := h.exists_ne_of_mem hZ
  apply hlz
  have h2 : (g * l * g⁻¹) (g z) = g z := h1 l hl (g z) (Subgroup.mem_map.2 ⟨z, hz, rfl⟩)
  have h3 : g (l z) = g z := by simpa [MulAut.mul_apply] using h2
  exact g.injective h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
