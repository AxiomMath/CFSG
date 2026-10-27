module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovX
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Cov

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.AGLEmbedding.KFactProofs.J3Sylow

private theorem card_comap_mk' {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (U : Subgroup (X ⧸ N)) :
    Nat.card (U.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card U := by
  have h1 := Subgroup.card_mul_index (U.comap (QuotientGroup.mk' N))
  rw [Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective N)] at h1
  have h2 := Subgroup.card_mul_index U
  have h3 := Subgroup.card_mul_index N
  have hU0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hU0)
  rw [h1, ← h3, Subgroup.index_eq_card, ← h2]
  ring

private theorem pow_three_eq_one_of_mem {X : Type*} [Group X] {Z : Subgroup X}
    (hZ3 : Nat.card Z = 3) {z : X} (hz : z ∈ Z) : z ^ 3 = 1 := by
  have h0 := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
  rw [hZ3] at h0
  simpa using congrArg Subtype.val h0

private theorem coverX_of_lift {X : Type} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {Tb Rb : Subgroup (X ⧸ Z)} {sb : X ⧸ Z} (hF : J3CoverFacts Tb Rb sb)
    (hcent : ∀ x ∈ Rb.comap (QuotientGroup.mk' Z), ∀ t ∈ Tb.comap (QuotientGroup.mk' Z),
      x * t = t * x)
    {s : X} (hs : QuotientGroup.mk' Z s = sb) (hs8 : s ^ 8 = 1) :
    CoverX X Z (Rb.comap (QuotientGroup.mk' Z)) (Tb.comap (QuotientGroup.mk' Z)) s := by
  have hker : ∀ x : X, QuotientGroup.mk' Z x = 1 ↔ x ∈ Z := fun x => QuotientGroup.eq_one_iff x
  have hsR : ∀ g : X ⧸ Z, g ∈ Subgroup.normalizer (Tb : Set (X ⧸ Z)) →
      ∀ x ∈ Rb, g * x * g⁻¹ ∈ Rb := by
    intro g hg x hx
    have hgT := Subgroup.mem_normalizer_iff.mp hg
    obtain ⟨hxT, hxc⟩ := (hF.mem_R x).1 hx
    rw [hF.mem_R]
    refine ⟨(hgT x).mp hxT, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Tb := by
      rw [hgT (g⁻¹ * y * g), show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      exact hy
    have h1 := hxc _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  have hsnR : s ∈ Subgroup.normalizer ((Rb.comap (QuotientGroup.mk' Z) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_comap, map_mul, map_inv, hs]
    constructor
    · exact hsR sb hF.s_norm _
    · intro hh
      have h2 := hsR sb⁻¹ (inv_mem hF.s_norm) _ hh
      rwa [inv_inv, show sb⁻¹ * (sb * QuotientGroup.mk' Z h * sb⁻¹) * sb =
        QuotientGroup.mk' Z h by group] at h2
  have hsnT : s ∈ Subgroup.normalizer ((Tb.comap (QuotientGroup.mk' Z) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_comap, map_mul, map_inv, hs]
    exact Subgroup.mem_normalizer_iff.mp hF.s_norm _
  have hRfix : ∀ x ∈ Rb.comap (QuotientGroup.mk' Z), s * x * s⁻¹ * x⁻¹ ∈ Z → x ∈ Z := by
    intro x hx hz
    have h1 : QuotientGroup.mk' Z (s * x * s⁻¹ * x⁻¹) = 1 := (hker _).mpr hz
    simp only [map_mul, map_inv, hs] at h1
    exact (hker x).mp (hF.R_fix _ (Subgroup.mem_comap.mp hx) (mul_inv_eq_one.mp h1))
  have hRinv : ∀ x ∈ Rb.comap (QuotientGroup.mk' Z), s ^ 4 * x * (s ^ 4)⁻¹ * x ∈ Z := by
    intro x hx
    have h1 : QuotientGroup.mk' Z (s ^ 4 * x * (s ^ 4)⁻¹ * x) = 1 := by
      simp only [map_mul, map_inv, map_pow, hs]
      rw [hF.R_inv _ (Subgroup.mem_comap.mp hx)]
      simp
    exact (hker _).mp h1
  have hcube : ∀ x ∈ Rb.comap (QuotientGroup.mk' Z), x ^ 3 ∈ Z := by
    intro x hx
    have h1 : QuotientGroup.mk' Z (x ^ 3) = 1 := by
      rw [map_pow]
      exact hF.R_elem.2 _ (Subgroup.mem_comap.mp hx)
    exact (hker _).mp h1
  have hcardT : Nat.card (Tb.comap (QuotientGroup.mk' Z)) = 729 := by
    rw [card_comap_mk' Z Tb, hF.card_T, hZ3]
  have hcardR : Nat.card (Rb.comap (QuotientGroup.mk' Z)) = 27 := by
    rw [card_comap_mk' Z Rb, hF.R_card, hZ3]
  have hnonab : ∃ x ∈ Tb.comap (QuotientGroup.mk' Z), ∃ y ∈ Tb.comap (QuotientGroup.mk' Z),
      x * y * x⁻¹ * y⁻¹ ∉ Rb.comap (QuotientGroup.mk' Z) := by
    obtain ⟨x, hx, y, hy, hn⟩ := hF.nonab
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective Z x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective Z y
    refine ⟨x', Subgroup.mem_comap.mpr hx, y', Subgroup.mem_comap.mpr hy, ?_⟩
    rw [Subgroup.mem_comap]
    simpa only [map_mul, map_inv] using hn
  have hsinger : ∀ W : Subgroup X, W ≤ Tb.comap (QuotientGroup.mk' Z) → Z ≤ W →
      W.relIndex (Tb.comap (QuotientGroup.mk' Z)) = 3 →
      s ^ 2 ∉ Subgroup.normalizer (W : Set X) := by
    intro W hWT hZW hW3 hn
    have hWc : (W.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = W := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZW]
    have hmem : ∀ x : X, x ∈ W ↔ QuotientGroup.mk' Z x ∈ W.map (QuotientGroup.mk' Z) := by
      intro x
      conv_lhs => rw [← hWc]
      exact Subgroup.mem_comap
    have hWbT : W.map (QuotientGroup.mk' Z) ≤ Tb :=
      Subgroup.map_le_iff_le_comap.mpr hWT
    have hrel : (W.map (QuotientGroup.mk' Z)).relIndex Tb = 3 := by
      have h := Subgroup.relIndex_comap (H := W.map (QuotientGroup.mk' Z))
        (f := QuotientGroup.mk' Z) (K := Tb.comap (QuotientGroup.mk' Z))
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Tb, hWc] at h
      rw [← h]
      exact hW3
    have hsq : sb ^ 2 ∈
        Subgroup.normalizer ((W.map (QuotientGroup.mk' Z) : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z k
      have e : sb ^ 2 * QuotientGroup.mk' Z h * (sb ^ 2)⁻¹ =
          QuotientGroup.mk' Z (s ^ 2 * h * (s ^ 2)⁻¹) := by
        rw [← hs]
        simp only [map_mul, map_inv, map_pow]
      rw [e, ← hmem h, ← hmem (s ^ 2 * h * (s ^ 2)⁻¹)]
      exact Subgroup.mem_normalizer_iff.mp hn h
    exact hF.singer (W.map (QuotientGroup.mk' Z)) hWbT hrel hsq
  exact
    { Z_central := hZc
      card_Z := hZ3
      Z_le_R := fun z hz => Subgroup.mem_comap.mpr (by
        rw [(hker z).mpr hz]
        exact Rb.one_mem)
      R_le_T := fun x hx => Subgroup.mem_comap.mpr
        ((hF.mem_R _).1 (Subgroup.mem_comap.mp hx)).1
      T_pgroup := IsPGroup.of_card (n := 6) (hcardT.trans (by norm_num))
      card_T := hcardT
      R_central := hcent
      card_R := hcardR
      R_cube := hcube
      s_normT := hsnT
      s_normR := hsnR
      s_pow := hs8
      R_fix := hRfix
      R_inv := hRinv
      nonab := hnonab
      singer := hsinger }

theorem coverX_of_facts {X : Type} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {Tb Rb : Subgroup (X ⧸ Z)} {sb : X ⧸ Z} (hF : J3CoverFacts Tb Rb sb)
    (hcent : ∀ x ∈ Rb.comap (QuotientGroup.mk' Z), ∀ t ∈ Tb.comap (QuotientGroup.mk' Z),
      x * t = t * x) :
    ∃ s : X, QuotientGroup.mk' Z s = sb ∧
      CoverX X Z (Rb.comap (QuotientGroup.mk' Z)) (Tb.comap (QuotientGroup.mk' Z)) s := by
  obtain ⟨s₀, hs₀⟩ := QuotientGroup.mk'_surjective Z sb
  have h8 : QuotientGroup.mk' Z (s₀ ^ 8) = 1 := by
    rw [map_pow, hs₀, hF.s_pow]
  have hz8 : s₀ ^ 8 ∈ Z := (QuotientGroup.eq_one_iff (s₀ ^ 8)).mp h8
  have hs9 : QuotientGroup.mk' Z (s₀ ^ 9) = sb := by
    rw [map_pow, hs₀]
    calc sb ^ 9 = sb ^ 8 * sb := pow_succ sb 8
      _ = sb := by rw [hF.s_pow, one_mul]
  have hcube8 : (s₀ ^ 8) ^ 3 = 1 := pow_three_eq_one_of_mem hZ3 hz8
  have hs8 : (s₀ ^ 9) ^ 8 = 1 := by
    calc (s₀ ^ 9) ^ 8 = ((s₀ ^ 8) ^ 3) ^ 3 := by group
      _ = 1 := by rw [hcube8, one_pow]
  exact ⟨s₀ ^ 9, hs9, coverX_of_lift hZc hZ3 hF hcent hs9 hs8⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
