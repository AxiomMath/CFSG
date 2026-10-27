module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Radical

public section

namespace CFSG.QuadraticMap

open Module _root_.QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def hullDim (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V) : ℕ :=
  finrank (ZMod 2) U + finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U)

theorem orthogonal_sup (Q : QuadraticForm (ZMod 2) V) (U W : Submodule (ZMod 2) V) :
    LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W) =
      LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
  rw [LinearMap.BilinForm.orthogonal, LinearMap.BilinForm.orthogonal,
    LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_sup]

variable [Module.Finite (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

omit [Module.Finite (ZMod 2) V] in
private lemma polar_self_eq_zero (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, CharTwo.two_nsmul]

private lemma finrank_rad_sup_le (U W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) ↥((U ⊔ W) ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W)) ≤
      finrank (ZMod 2) W +
        finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by
  set R : Submodule (ZMod 2) V :=
    (U ⊔ W) ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W) with hR
  have hRU : R ≤ U ⊔ W := inf_le_left
  have hRorth : R ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    inf_le_right.trans (LinearMap.BilinForm.orthogonal_le le_sup_left)
  have hinf : R ⊓ U ≤ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    le_inf inf_le_right (inf_le_left.trans hRorth)
  have h1 : finrank (ZMod 2) ↥(R ⊔ U) + finrank (ZMod 2) ↥(R ⊓ U) =
      finrank (ZMod 2) R + finrank (ZMod 2) U :=
    Submodule.finrank_sup_add_finrank_inf_eq R U
  have h2 : finrank (ZMod 2) ↥(R ⊔ U) ≤ finrank (ZMod 2) ↥(U ⊔ W) :=
    Submodule.finrank_mono (sup_le hRU le_sup_left)
  have h3 : finrank (ZMod 2) ↥(R ⊓ U) ≤
      finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :=
    Submodule.finrank_mono hinf
  have h4 : finrank (ZMod 2) ↥(U ⊔ W) + finrank (ZMod 2) ↥(U ⊓ W) =
      finrank (ZMod 2) U + finrank (ZMod 2) W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

theorem hullDim_sup_le (U W : Submodule (ZMod 2) V) :
    hullDim Q (U ⊔ W) ≤ hullDim Q U + 2 * finrank (ZMod 2) W := by
  rw [hullDim, hullDim]
  have h := finrank_rad_sup_le (Q := Q) U W
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

omit [Module.Finite (ZMod 2) V] in
private lemma rad_sup_le_sup_rad {U W : Submodule (ZMod 2) V}
    (hW : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    (U ⊔ W) ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W) ≤
      (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) ⊔
        (W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W) := by
  intro x hx
  obtain ⟨hxU, hxO⟩ := Submodule.mem_inf.mp hx
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hxU
  have hx0 : ∀ y ∈ U ⊔ W, polar Q y x = 0 := fun y hy =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) y hy
  have hu_rad : u ∈ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    refine Submodule.mem_inf.mpr ⟨hu, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u' hu'
    have h1 : polar Q u' x = 0 := hx0 u' (Submodule.mem_sup_left hu')
    have h2 : polar Q u' w = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using hW hw u' hu'
    have hux : u = x - w := by rw [← huw]; abel
    rw [hux, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right, h1, h2,
      sub_zero]
  have hw_rad : w ∈ W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    refine Submodule.mem_inf.mpr ⟨hw, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    have h1 : polar Q w' x = 0 := hx0 w' (Submodule.mem_sup_right hw')
    have h2 : polar Q w' u = 0 := by
      rw [polar_comm Q w' u]
      simpa only [QuadraticMap.polarBilin_apply_apply] using hW hw' u hu
    have hwx : w = x - u := by rw [← huw]; abel
    rw [hwx, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right, h1, h2,
      sub_zero]
  exact Submodule.mem_sup.mpr ⟨u, hu_rad, w, hw_rad, huw⟩

theorem hullDim_sup_le_of_le_orthogonal {U W : Submodule (ZMod 2) V}
    (h : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    hullDim Q (U ⊔ W) ≤ hullDim Q U + hullDim Q W := by
  rw [hullDim, hullDim, hullDim]
  have hrad := Submodule.finrank_mono (rad_sup_le_sup_rad (Q := Q) h)
  have hsup : finrank (ZMod 2) ↥((U ⊔ W) ⊓
      LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W)) ≤
        finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) +
          finrank (ZMod 2) ↥(W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
      (W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W)
    omega
  have h2 : finrank (ZMod 2) ↥(U ⊔ W) ≤ finrank (ZMod 2) U + finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
    omega
  omega

omit [Module.Finite (ZMod 2) V] in
theorem hullDim_span_pair {u w : V} (h : polar Q u w = 1) :
    hullDim Q (Submodule.span (ZMod 2) {u, w}) = 2 := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.polar_zero_left] at h
    exact zero_ne_one h
  have hlin : LinearIndependent (ZMod 2) ![u, w] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro a ha
    have h1 : polar Q u (a • u) = polar Q u w := by rw [ha]
    rw [QuadraticMap.polar_smul_right, polar_self_eq_zero, smul_zero, h] at h1
    exact zero_ne_one h1
  have hspan : finrank (ZMod 2) (Submodule.span (ZMod 2) {u, w}) = 2 := by
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hlin, Fintype.card_fin]
  have hrad : Submodule.span (ZMod 2) {u, w} ⊓
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {u, w}) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxo⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hxs
    obtain ⟨h1, h2⟩ := (LinearMap.BilinForm.mem_orthogonal_span_pair_iff (polarBilin Q)).mp hxo
    have ht : t = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, polar_self_eq_zero, h,
        smul_zero, smul_eq_mul, mul_one, zero_add] at h1
      exact h1
    have hs : s = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, polar_self_eq_zero,
        polar_comm Q w u, h, smul_zero, smul_eq_mul, mul_one, add_zero] at h2
      exact h2
    rw [hs, ht, zero_smul, zero_smul, add_zero]
    simp
  rw [hullDim, hspan, hrad, finrank_bot, add_zero]

omit [Module.Finite (ZMod 2) V] in
private lemma polar_add_polar_smul_self_eq_zero {z₁ z₂ p : V}
    (h : polar Q z₁ p = 0) :
    polar Q z₁ (p + (polar Q p z₂) • z₁) = 0 := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, polar_self_eq_zero, h,
    smul_zero, add_zero]

omit [Module.Finite (ZMod 2) V] in
private lemma polar_add_polar_smul_eq_zero_of_polar_eq_one {z₁ z₂ p : V}
    (hz : polar Q z₁ z₂ = 1) :
    polar Q z₂ (p + (polar Q p z₂) • z₁) = 0 := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    polar_comm Q z₂ p, polar_comm Q z₂ z₁, hz, smul_eq_mul, mul_one]
  exact CharTwo.add_self_eq_zero _

omit [Module.Finite (ZMod 2) V] in
private lemma polar_add_polar_smul_add_polar_smul_eq_one {z₁ z₂ p₁ p₂ : V}
    (hp : polar Q p₁ p₂ = 1) (h₁ : polar Q z₁ p₁ = 0) (h₂ : polar Q z₁ p₂ = 0) :
    polar Q (p₁ + (polar Q p₁ z₂) • z₁) (p₂ + (polar Q p₂ z₂) • z₁) = 1 := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  rw [polar_comm Q p₁ z₁, h₁, h₂, hp, polar_self_eq_zero]
  simp

omit [Module.Finite (ZMod 2) V] in
private lemma span_pair_sup_span_pair_add_polar_smul_eq {z₁ z₂ p₁ p₂ : V} :
    Submodule.span (ZMod 2) {z₁, z₂} ⊔ Submodule.span (ZMod 2) {p₁, p₂} =
      Submodule.span (ZMod 2) {z₁, z₂} ⊔
        Submodule.span (ZMod 2)
          {p₁ + (polar Q p₁ z₂) • z₁, p₂ + (polar Q p₂ z₂) • z₁} := by
  let A : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {z₁, z₂}
  let B : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {p₁, p₂}
  let B' : Submodule (ZMod 2) V := Submodule.span (ZMod 2)
    {p₁ + (polar Q p₁ z₂) • z₁, p₂ + (polar Q p₂ z₂) • z₁}
  change A ⊔ B = A ⊔ B'
  have hz₁ : z₁ ∈ A := by
    dsimp only [A]
    exact Submodule.subset_span (by simp)
  have hp₁ : p₁ ∈ B := by
    dsimp only [B]
    exact Submodule.subset_span (by simp)
  have hp₂ : p₂ ∈ B := by
    dsimp only [B]
    exact Submodule.subset_span (by simp)
  have hp₁' : p₁ + (polar Q p₁ z₂) • z₁ ∈ B' := by
    dsimp only [B']
    exact Submodule.subset_span (by simp)
  have hp₂' : p₂ + (polar Q p₂ z₂) • z₁ ∈ B' := by
    dsimp only [B']
    exact Submodule.subset_span (by simp)
  refine le_antisymm ?_ ?_
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      change p₁ ∈ A ⊔ B'
      have h : p₁ + (polar Q p₁ z₂) • z₁ - (polar Q p₁ z₂) • z₁ ∈ A ⊔ B' :=
        Submodule.sub_mem (A ⊔ B')
          (Submodule.mem_sup_right hp₁')
          (Submodule.smul_mem (A ⊔ B') (polar Q p₁ z₂) (Submodule.mem_sup_left hz₁))
      simpa only [add_sub_cancel_right] using h
    · rw [hx]
      change p₂ ∈ A ⊔ B'
      have h : p₂ + (polar Q p₂ z₂) • z₁ - (polar Q p₂ z₂) • z₁ ∈ A ⊔ B' :=
        Submodule.sub_mem (A ⊔ B')
          (Submodule.mem_sup_right hp₂')
          (Submodule.smul_mem (A ⊔ B') (polar Q p₂ z₂) (Submodule.mem_sup_left hz₁))
      simpa only [add_sub_cancel_right] using h
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.add_mem (A ⊔ B) (Submodule.mem_sup_right hp₁)
        (Submodule.smul_mem (A ⊔ B) (polar Q p₁ z₂) (Submodule.mem_sup_left hz₁))
    · rw [hx]
      exact Submodule.add_mem (A ⊔ B) (Submodule.mem_sup_right hp₂)
        (Submodule.smul_mem (A ⊔ B) (polar Q p₂ z₂) (Submodule.mem_sup_left hz₁))

theorem hullDim_span_pair_sup_le_four {z₁ z₂ p₁ p₂ : V} (hz : polar Q z₁ z₂ = 1)
    (hp : polar Q p₁ p₂ = 1) (h₁ : polar Q z₁ p₁ = 0) (h₂ : polar Q z₁ p₂ = 0) :
    hullDim Q (Submodule.span (ZMod 2) {z₁, z₂} ⊔ Submodule.span (ZMod 2) {p₁, p₂}) ≤ 4 := by
  have horth : Submodule.span (ZMod 2)
      {p₁ + (polar Q p₁ z₂) • z₁, p₂ + (polar Q p₂ z₂) • z₁} ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span (ZMod 2) {z₁, z₂}) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
      intro y hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
        polar_add_polar_smul_self_eq_zero h₁,
        polar_add_polar_smul_eq_zero_of_polar_eq_one hz]
      simp
    · refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
      intro y hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
        polar_add_polar_smul_self_eq_zero h₂,
        polar_add_polar_smul_eq_zero_of_polar_eq_one hz]
      simp
  have hp' : polar Q (p₁ + (polar Q p₁ z₂) • z₁)
      (p₂ + (polar Q p₂ z₂) • z₁) = 1 :=
    polar_add_polar_smul_add_polar_smul_eq_one hp h₁ h₂
  rw [span_pair_sup_span_pair_add_polar_smul_eq (Q := Q)]
  calc
    hullDim Q (Submodule.span (ZMod 2) {z₁, z₂} ⊔
        Submodule.span (ZMod 2)
          {p₁ + (polar Q p₁ z₂) • z₁, p₂ + (polar Q p₂ z₂) • z₁})
        ≤ hullDim Q (Submodule.span (ZMod 2) {z₁, z₂}) +
            hullDim Q (Submodule.span (ZMod 2)
              {p₁ + (polar Q p₁ z₂) • z₁, p₂ + (polar Q p₂ z₂) • z₁}) :=
          hullDim_sup_le_of_le_orthogonal horth
    _ = 2 + 2 := by rw [hullDim_span_pair hz, hullDim_span_pair hp']
    _ = 4 := by norm_num

private lemma finrank_orthogonal_top_restrict_le (L : Submodule (ZMod 2) V) :
    finrank (ZMod 2) ↥((LinearMap.BilinForm.restrict (polarBilin Q) L).orthogonal ⊤) ≤
      finrank (ZMod 2) ↥(L ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) L) := by
  let B_L : LinearMap.BilinForm (ZMod 2) L :=
    LinearMap.BilinForm.restrict (polarBilin Q) L
  have hB : ∀ x y : L, B_L x y = polar Q x y := by
    intro x y
    simp only [B_L, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      QuadraticMap.polarBilin_apply_apply]
  have hmap_le : (B_L.orthogonal ⊤).map L.subtype ≤
      L ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) L := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := Submodule.mem_map.mp hx
    rw [← hrx]
    refine Submodule.mem_inf.mpr ⟨r.2, ?_⟩
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
    intro y hy
    have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) ⟨y, hy⟩ (Submodule.mem_top)
    rw [hB ⟨y, hy⟩ r] at h0
    simpa only [QuadraticMap.polarBilin_apply_apply, Submodule.subtype_apply] using h0
  have hle := Submodule.finrank_mono hmap_le
  have hmapfin := Submodule.finrank_map_subtype_eq L (B_L.orthogonal ⊤)
  simpa only [B_L] using hmapfin.symm.trans_le hle

theorem two_mul_finrank_le_hullDim {T L : Submodule (ZMod 2) V} (hTL : T ≤ L)
    (hT : ∀ x ∈ T, ∀ y ∈ T, polar Q x y = 0) : 2 * finrank (ZMod 2) T ≤ hullDim Q L := by
  let B_L : LinearMap.BilinForm (ZMod 2) L :=
    LinearMap.BilinForm.restrict (polarBilin Q) L
  let T' : Submodule (ZMod 2) L := T.comap L.subtype
  have hB : ∀ x y : L, B_L x y = polar Q x y := by
    intro x y
    simp only [B_L, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      QuadraticMap.polarBilin_apply_apply]
  have hB_refl : B_L.IsRefl := by
    simpa only [B_L] using
      (LinearMap.BilinForm.IsSymm.restrict (QuadraticMap.isSymm_polarBilin (Q := Q)) L).isRefl
  have hfinT : finrank (ZMod 2) T' = finrank (ZMod 2) T := by
    have hmap : T'.map L.subtype = T := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        rw [← hyx]
        exact hy
      · intro hx
        refine ⟨⟨x, hTL hx⟩, ?_, rfl⟩
        show L.subtype ⟨x, hTL hx⟩ ∈ T
        simpa only [Submodule.subtype_apply] using hx
    have h := Submodule.finrank_map_subtype_eq L T'
    rw [hmap] at h
    exact h.symm
  have hT'orth : T' ≤ B_L.orthogonal T' := by
    intro x hx
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
    intro y hy
    have hxT : (x : V) ∈ T := hx
    have hyT : (y : V) ∈ T := hy
    rw [hB y x]
    exact hT y hyT x hxT
  have hRorth : B_L.orthogonal ⊤ ≤ B_L.orthogonal T' := by
    intro r hr
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
    intro y hy
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) y (Submodule.mem_top)
  have hrank := LinearMap.BilinForm.finrank_add_finrank_orthogonal hB_refl T'
  have hsup := Submodule.finrank_mono (sup_le hT'orth hRorth)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T' (B_L.orthogonal ⊤)
  have h2 := Submodule.finrank_mono
    (inf_le_right : T' ⊓ B_L.orthogonal ⊤ ≤ B_L.orthogonal ⊤)
  have hmain : 2 * finrank (ZMod 2) T' ≤
      finrank (ZMod 2) L + finrank (ZMod 2) ↥(B_L.orthogonal ⊤) := by
    omega
  have hrad : finrank (ZMod 2) ↥(B_L.orthogonal ⊤) ≤
      finrank (ZMod 2) ↥(L ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) L) :=
    finrank_orthogonal_top_restrict_le (Q := Q) L
  rw [hullDim]
  omega

private lemma zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private lemma eq_one_of_add_add_eq_one {a b c : ZMod 2} (h : a + b + c = 1) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  revert h
  revert a b c
  decide

omit [Module.Finite (ZMod 2) V] in
private lemma add_add_add_Q_add_polar_eq_polar (l k₁ k₂ : V) :
    (Q k₁ + polar Q l k₁) + (Q k₂ + polar Q l k₂) +
      (Q (k₁ + k₂) + polar Q l (k₁ + k₂)) = polar Q k₁ k₂ := by
  rw [QuadraticMap.map_add Q, QuadraticMap.polar_add_right]
  rw [show (Q k₁ + polar Q l k₁) + (Q k₂ + polar Q l k₂) +
      (Q k₁ + Q k₂ + polar Q k₁ k₂ + (polar Q l k₁ + polar Q l k₂)) =
      (Q k₁ + Q k₁) + (Q k₂ + Q k₂) + (polar Q l k₁ + polar Q l k₁) +
        (polar Q l k₂ + polar Q l k₂) + polar Q k₁ k₂ by abel,
    CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
  simp [CharTwo.add_self_eq_zero]

omit [Module.Finite (ZMod 2) V] in
private lemma exists_polar_eq_one_Q_eq_one_add {U : Submodule (ZMod 2) V} {z l k : V}
    (hl : l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (hk : k ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (hzl : polar Q z l = 1) (hzk : polar Q z k = 0) (hQl : Q l = 0)
    (hf : Q k + polar Q l k = 1) :
    ∃ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z y = 1 ∧ Q y = 1 := by
  refine ⟨l + k, Submodule.add_mem _ hl hk, ?_, ?_⟩
  · rw [QuadraticMap.polar_add_right, hzk, hzl, add_zero]
  · rw [QuadraticMap.map_add Q]
    simpa only [hQl, zero_add] using hf

theorem exists_Q_eq_one_polar_eq_one (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : hullDim Q U < finrank (ZMod 2) V) :
    ∃ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, Q z = 1 ∧
      ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z l = 1 := by
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin (Q := Q)).isRefl
  have hdimL : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin Q) U) =
      finrank (ZMod 2) V - finrank (ZMod 2) U :=
    LinearMap.BilinForm.finrank_orthogonal hQ U
  have hUle : finrank (ZMod 2) U ≤ finrank (ZMod 2) V := Submodule.finrank_le U
  have hnotle : ¬ LinearMap.BilinForm.orthogonal (polarBilin Q) U ≤ U := by
    intro hle
    have hEq : U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U =
        LinearMap.BilinForm.orthogonal (polarBilin Q) U := inf_eq_right.mpr hle
    have hlt := hU
    rw [hullDim, hEq, hdimL] at hlt
    omega
  obtain ⟨x, hxL, hxU⟩ := SetLike.not_le_iff_exists.mp hnotle
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl U
  have hxorth : x ∉ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by
    rwa [horth]
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxorth
  push Not at hxorth
  obtain ⟨y, hyL, hBxy⟩ := hxorth
  have hpol : polar Q x y = 1 := by
    rw [polar_comm Q x y, ← QuadraticMap.polarBilin_apply_apply]
    rcases zmod2_eq_zero_or_eq_one ((polarBilin Q) y x) with h0 | h1
    · exact absurd h0 hBxy
    · exact h1
  have hquad : Q x + Q y + Q (x + y) = 1 := by
    rw [QuadraticMap.map_add Q, hpol]
    rw [show Q x + Q y + (Q x + Q y + 1) = (Q x + Q y) + (Q x + Q y) + 1 by abel,
      CharTwo.add_self_eq_zero, zero_add]
  rcases zmod2_eq_zero_or_eq_one (Q x) with hx | hx
  · rcases zmod2_eq_zero_or_eq_one (Q y) with hy | hy
    · have hxy : Q (x + y) = 1 := by
        simpa only [hx, hy, zero_add] using hquad
      refine ⟨x + y, Submodule.add_mem _ hxL hyL, hxy, y, hyL, ?_⟩
      rw [QuadraticMap.polar_add_left, polar_self_eq_zero, hpol, add_zero]
    · exact ⟨y, hyL, hy, x, hxL, by rw [polar_comm Q y x, hpol]⟩
  · exact ⟨x, hxL, hx, y, hyL, hpol⟩

private lemma exists_polar_eq_one_of_hullDim_add_three (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : hullDim Q U + 3 ≤ finrank (ZMod 2) V) {z : V}
    (hz0 : z ≠ 0) :
    ∃ k₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z}),
      ∃ k₂ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z}),
        polar Q k₁ k₂ = 1 := by
  have hzdim : finrank (ZMod 2) (Submodule.span (ZMod 2) {z}) = 1 := by
    simpa using finrank_span_singleton (K := ZMod 2) hz0
  have hLdim : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin Q) U) =
      finrank (ZMod 2) V - finrank (ZMod 2) U :=
    LinearMap.BilinForm.finrank_orthogonal hQ U
  have hPdim : finrank (ZMod 2)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z})) =
      finrank (ZMod 2) V - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hzdim]
  set K := LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊓
    LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z}) with hK
  have hKdim : finrank (ZMod 2)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) - 1 ≤ finrank (ZMod 2) K := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z}))
    rw [← hK] at h1
    have hsup : finrank (ZMod 2)
        ↥(LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊔
          LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z})) ≤
        finrank (ZMod 2) V := Submodule.finrank_le _
    rw [hPdim, hLdim] at h1
    omega
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ
      (QuadraticMap.isSymm_polarBilin (Q := Q)).isRefl U
  have hhull : hullDim Q (LinearMap.BilinForm.orthogonal (polarBilin Q) U) =
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin Q) U) +
        finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by
    rw [hullDim, horth, inf_comm]
  have hU' : finrank (ZMod 2) U +
      finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) + 3 ≤
      finrank (ZMod 2) V := by
    simpa only [hullDim] using hU
  have hnoiso : ¬ ∀ x ∈ K, ∀ y ∈ K, polar Q x y = 0 := by
    intro hiso
    have h2 := two_mul_finrank_le_hullDim (Q := Q) (T := K)
      (L := LinearMap.BilinForm.orthogonal (polarBilin Q) U) inf_le_left hiso
    rw [hhull] at h2
    omega
  push Not at hnoiso
  obtain ⟨k₁, hk₁, k₂, hk₂, hk₁₂⟩ := hnoiso
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rcases zmod2_eq_zero_or_eq_one (polar Q k₁ k₂) with h0 | h1
  · exact absurd h0 hk₁₂
  · exact h1

theorem exists_polar_eq_one_Q_eq_one (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : hullDim Q U + 3 ≤ finrank (ZMod 2) V) {z l : V}
    (hl : l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hzl : polar Q z l = 1) :
    ∃ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z y = 1 ∧ Q y = 1 := by
  rcases zmod2_eq_zero_or_eq_one (Q l) with hQl | hQl
  · have hz0 : z ≠ 0 := by
      rintro rfl
      rw [QuadraticMap.polar_zero_left] at hzl
      exact zero_ne_one hzl
    obtain ⟨k₁, hk₁, k₂, hk₂, hk₁₂'⟩ :=
      exists_polar_eq_one_of_hullDim_add_three hQ hU hz0
    have hfs : (Q k₁ + polar Q l k₁) + (Q k₂ + polar Q l k₂) +
        (Q (k₁ + k₂) + polar Q l (k₁ + k₂)) = 1 := by
      rw [add_add_add_Q_add_polar_eq_polar, hk₁₂']
    have hzk : ∀ k ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {z}),
        polar Q z k = 0 := by
      intro k hk
      have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp hk.2) z
        (Submodule.mem_span_singleton_self z)
      simpa only [QuadraticMap.polarBilin_apply_apply] using hmem
    rcases eq_one_of_add_add_eq_one hfs with hf | hf | hf
    · exact exists_polar_eq_one_Q_eq_one_add hl hk₁.1 hzl (hzk k₁ hk₁) hQl hf
    · exact exists_polar_eq_one_Q_eq_one_add hl hk₂.1 hzl (hzk k₂ hk₂) hQl hf
    · exact exists_polar_eq_one_Q_eq_one_add hl (Submodule.add_mem _ hk₁ hk₂).1 hzl
        (hzk (k₁ + k₂) (Submodule.add_mem _ hk₁ hk₂)) hQl hf
  · exact ⟨l, hl, hzl, hQl⟩

theorem exists_framedPair_orthogonal (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : hullDim Q U + 3 ≤ finrank (ZMod 2) V) :
    ∃ u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U,
      ∃ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U,
        Q u = 1 ∧ Q w = 1 ∧ polar Q u w = 1 := by
  obtain ⟨u, hu, hQu, l, hl, hul⟩ :=
    exists_Q_eq_one_polar_eq_one (U := U) hQ (by omega)
  obtain ⟨w, hw, huw, hQw⟩ := exists_polar_eq_one_Q_eq_one hQ hU hl hul
  exact ⟨u, hu, w, hw, hQu, hQw, huw⟩

end CFSG.QuadraticMap
