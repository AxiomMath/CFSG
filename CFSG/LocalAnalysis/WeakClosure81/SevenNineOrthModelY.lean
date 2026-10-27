module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OrthFrame

variable {p m : ℕ} [Fact p.Prime] {f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)}
  (F : OrthFrame p m f)

theorem refl_mem_closure : F.refl ∈ Subgroup.closure (orthReflSet p m f) :=
  Subgroup.subset_closure (orthRefl_mem f F.norm_a)

private theorem a_ne_zero : F.a ≠ 0 := by
  intro h
  have h' : (0 : ZMod p) = -2 := by
    calc (0 : ZMod p) = f (0 : Fin m → ZMod p) 0 := by simp
      _ = f F.a F.a := by rw [h]
      _ = -2 := F.norm_a
  exact F.two_ne (neg_eq_zero.mp h'.symm)

private theorem orthRefl_mulVec_mem_U {v w : Fin m → ZMod p} (hv : v ∈ F.U) (hw : w ∈ F.U) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w ∈ F.U := by
  by_cases hvv : f v v = -2
  · rw [orthRefl_mulVec f hvv]
    exact F.U.add_mem hw (F.U.smul_mem (f w v) hv)
  · have hr : orthRefl f v = 1 := by simp [orthRefl, hvv]
    rw [hr]
    simpa [Matrix.one_mulVec] using hw

theorem orthRefl_mulVec_s {v : Fin m → ZMod p} (hv : f v F.s = 0) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.s = F.s := by
  by_cases hvv : f v v = -2
  · rw [orthRefl_mulVec f hvv]
    have hv' : f F.s v = 0 := by rw [F.symm F.s v]; exact hv
    rw [hv']
    simp
  · simp [orthRefl, hvv]

theorem siegel_mem_Y {w : Fin m → ZMod p} (hw : w ∈ F.U) : F.siegel w ∈ F.Y :=
  F.mem_Y.2 ⟨w, hw, rfl⟩

private theorem siegel_eq_siegel_iff {u v : Fin m → ZMod p} (hu : u ∈ F.U) (hv : v ∈ F.U) :
    F.siegel u = F.siegel v ↔ u = v := by
  constructor
  · intro h
    have hneg : -v ∈ F.U := F.U.neg_mem hv
    have h1 : F.siegel (u + -v) = 1 := by
      rw [F.siegel_add (F.mem_U.1 hu).1 (F.mem_U.1 hneg).1, F.siegel_neg (F.mem_U.1 hv).1, h]
      group
    have h2 : u + -v = 0 := (F.siegel_eq_one_iff (F.U.add_mem hu hneg)).1 h1
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact h2
  · rintro rfl
    rfl

private theorem orthRefl_mulVec_eq_self_iff (w : Fin m → ZMod p) :
    (orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w = w ↔ f w F.a = 0 := by
  constructor
  · intro h
    have h0 : w + f w F.a • F.a = w + 0 := by
      rw [← orthRefl_mulVec f F.norm_a, h]
      simp
    have hc : f w F.a • F.a = 0 := add_left_cancel h0
    exact (smul_eq_zero.1 hc).resolve_right (a_ne_zero F)
  · intro hfwa
    rw [orthRefl_mulVec f F.norm_a, hfwa]
    simp

private theorem refl_mul_siegel_eq_iff {w : Fin m → ZMod p} (hw : w ∈ F.U) :
    F.refl * F.siegel w = F.siegel w * F.refl ↔ f w F.a = 0 := by
  have hconj : F.refl * F.siegel w * F.refl⁻¹ =
      F.siegel ((orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) := by
    change orthRefl f F.a * F.siegel w * (orthRefl f F.a)⁻¹ = _
    exact F.siegel_conj (isOrthIsometry_orthRefl f F.symm F.a)
      (orthRefl_mulVec_s F F.a_orth_s) w
  have hU : (orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w ∈ F.U :=
    orthRefl_mulVec_mem_U F F.a_mem_U hw
  constructor
  · intro h
    have h2 : F.siegel ((orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) =
        F.siegel w := by
      rw [← hconj, h, mul_assoc, mul_inv_cancel, mul_one]
    exact (orthRefl_mulVec_eq_self_iff F w).1 ((siegel_eq_siegel_iff F hU hw).1 h2)
  · intro hfwa
    have hwr : (orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w = w :=
      (orthRefl_mulVec_eq_self_iff F w).2 hfwa
    have h1 : F.refl * F.siegel w * F.refl⁻¹ = F.siegel w := by rw [hconj, hwr]
    calc F.refl * F.siegel w = F.refl * F.siegel w * F.refl⁻¹ * F.refl := by group
      _ = F.siegel w * F.refl := by rw [h1]

theorem orthRefl_mem_normalizer_Y {v : Fin m → ZMod p} (hv : v ∈ F.U) :
    orthRefl f v ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) := by
  by_cases hvv : f v v = -2
  · rw [Subgroup.mem_normalizer_iff]
    have hgis : IsOrthIsometry f (orthRefl f v) := isOrthIsometry_orthRefl f F.symm v
    have hvs : (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.s = F.s :=
      orthRefl_mulVec_s F (F.mem_U.1 hv).1
    have hfwd : ∀ x : GL (Fin m) (ZMod p),
        x ∈ F.Y → orthRefl f v * x * (orthRefl f v)⁻¹ ∈ F.Y := by
      intro x hx
      obtain ⟨w, hw, hwT⟩ := F.mem_Y.1 hx
      rw [← hwT, F.siegel_conj hgis hvs w]
      exact F.siegel_mem_Y (orthRefl_mulVec_mem_U F hv hw)
    intro x
    constructor
    · exact hfwd x
    · intro hx
      have hy := hfwd (orthRefl f v * x * (orthRefl f v)⁻¹) hx
      have hx' : orthRefl f v * (orthRefl f v * x * (orthRefl f v)⁻¹) *
          (orthRefl f v)⁻¹ = x := by
        rw [orthRefl_inv f v]
        calc orthRefl f v * (orthRefl f v * x * orthRefl f v) * orthRefl f v
            = (orthRefl f v * orthRefl f v) * x * (orthRefl f v * orthRefl f v) := by
              group
          _ = x := by rw [orthRefl_mul_self f hvv]; simp
      rwa [hx'] at hy
  · rw [show orthRefl f v = 1 by simp [orthRefl, hvv]]
    exact Subgroup.one_mem _

theorem zpowers_refl_le_normalizer :
    Subgroup.zpowers F.refl ≤ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p))) := by
  rw [Subgroup.zpowers_le]
  change orthRefl f F.a ∈ Subgroup.normalizer (F.Y : Set (GL (Fin m) (ZMod p)))
  exact orthRefl_mem_normalizer_Y F F.a_mem_U

theorem siegel_mem_Z_iff {w : Fin m → ZMod p} (hw : w ∈ F.U) :
    F.siegel w ∈ F.Z ↔ f w F.a = 0 := by
  rw [OrthFrame.Z, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [F.siegel_mem_Y hw, true_and]
  constructor
  · intro hc
    exact (refl_mul_siegel_eq_iff F hw).1
      (hc F.refl (Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one F.refl⟩))
  · intro hfwa h hs
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hs
    rw [← hn]
    exact Commute.zpow_left ((refl_mul_siegel_eq_iff F hw).2 hfwa) n

theorem mem_Z {g : GL (Fin m) (ZMod p)} :
    g ∈ F.Z ↔ ∃ w ∈ F.U, f w F.a = 0 ∧ F.siegel w = g := by
  constructor
  · intro hg
    obtain ⟨hgY, _⟩ := Subgroup.mem_inf.1 (show g ∈ F.Y ⊓ Subgroup.centralizer
      ((Subgroup.zpowers F.refl : Subgroup (GL (Fin m) (ZMod p))) :
        Set (GL (Fin m) (ZMod p))) from hg)
    obtain ⟨w, hw, hwT⟩ := F.mem_Y.1 hgY
    refine ⟨w, hw, ?_, hwT⟩
    have hZ : F.siegel w ∈ F.Z := by rw [hwT]; exact hg
    exact (F.siegel_mem_Z_iff hw).1 hZ
  · rintro ⟨w, hw, hwa, rfl⟩
    exact (F.siegel_mem_Z_iff hw).2 hwa

theorem card_zpowers_refl : Nat.card (Subgroup.zpowers F.refl) = 2 := by
  have h2 : F.refl ^ 2 = 1 := by
    rw [pow_two]
    change orthRefl f F.a * orthRefl f F.a = 1
    exact orthRefl_mul_self f F.norm_a
  have hne : F.refl ≠ 1 := by
    change orthRefl f F.a ≠ 1
    exact orthRefl_ne_one f F.two_ne F.norm_a
  rw [Nat.card_zpowers, orderOf_eq_prime h2 hne]

theorem isElemAbelian_Y : IsElemAbelian p F.Y := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨w, hw, hwT⟩ := F.mem_Y.1 a.2
    obtain ⟨u, hu, huT⟩ := F.mem_Y.1 b.2
    apply Subtype.ext
    show (a : GL (Fin m) (ZMod p)) * b = b * (a : GL (Fin m) (ZMod p))
    rw [← hwT, ← huT, ← F.siegel_add (F.mem_U.1 hw).1 (F.mem_U.1 hu).1,
      ← F.siegel_add (F.mem_U.1 hu).1 (F.mem_U.1 hw).1, add_comm w u]
  · intro x hx
    obtain ⟨w, hw, hwT⟩ := F.mem_Y.1 hx
    rw [← hwT, ← F.siegel_nsmul (F.mem_U.1 hw).1 p]
    have hpw : p • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p w, ZMod.natCast_self, zero_smul]
    rw [hpw, F.siegel_zero]

theorem card_Z_mul : Nat.card F.Z * p = Nat.card F.Y := by
  let φ : F.U →+ ZMod p :=
    { toFun := fun w => f (w : Fin m → ZMod p) F.a
      map_zero' := by simp
      map_add' := by intro x y; simp [map_add] }
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨⟨-(c * (2 : ZMod p)⁻¹) • F.a, F.U.smul_mem _ F.a_mem_U⟩, ?_⟩
    show f (-(c * (2 : ZMod p)⁻¹) • F.a) F.a = c
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, F.norm_a]
    calc (-(c * (2 : ZMod p)⁻¹)) * (-2)
        = c * ((2 : ZMod p)⁻¹ * 2) := by ring
      _ = c * 1 := by rw [inv_mul_cancel₀ F.two_ne]
      _ = c := by ring
  have hU : Nat.card φ.ker * p = Nat.card F.U := by
    have hrange : φ.range = ⊤ := AddMonoidHom.range_eq_top.2 hsurj
    have := AddSubgroup.card_ker_mul_card_range φ
    rwa [hrange, AddSubgroup.card_top, Nat.card_zmod] at this
  have hYU : Nat.card F.U = Nat.card F.Y := by
    apply Nat.card_eq_of_bijective
      (fun w : F.U => (⟨F.siegel (w : Fin m → ZMod p), F.siegel_mem_Y w.2⟩ : F.Y))
    constructor
    · intro x y h
      apply Subtype.ext
      exact (siegel_eq_siegel_iff F x.2 y.2).1 (congrArg Subtype.val h)
    · intro y
      obtain ⟨w, hw, hwT⟩ := F.mem_Y.1 y.2
      exact ⟨⟨w, hw⟩, Subtype.ext hwT⟩
  have hZ : Nat.card F.Z = Nat.card φ.ker := by
    symm
    apply Nat.card_eq_of_bijective
      (fun w : φ.ker =>
        (⟨F.siegel ((w.1 : F.U) : Fin m → ZMod p),
          F.mem_Z.2 ⟨(w.1 : F.U), w.1.2, w.2, rfl⟩⟩ : F.Z))
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact (siegel_eq_siegel_iff F x.1.2 y.1.2).1 (congrArg Subtype.val h)
    · intro z
      obtain ⟨w, hw, hwa, hwz⟩ := F.mem_Z.1 z.2
      refine ⟨⟨⟨w, hw⟩, ?_⟩, ?_⟩
      · show f w F.a = 0
        exact hwa
      · apply Subtype.ext
        exact hwz
  calc Nat.card F.Z * p = Nat.card φ.ker * p := by rw [hZ]
    _ = Nat.card F.U := hU
    _ = Nat.card F.Y := hYU

theorem siegel_a_mem_commutator :
    F.siegel F.a ∈ ⁅F.Y, Subgroup.zpowers F.refl⁆ := by
  let w : Fin m → ZMod p := (2 : ZMod p)⁻¹ • F.a
  have hwU : w ∈ F.U := F.U.smul_mem _ F.a_mem_U
  have hwS : f w F.s = 0 := (F.mem_U.1 hwU).1
  have hfwa : f w F.a = -1 := by
    change f ((2 : ZMod p)⁻¹ • F.a) F.a = -1
    rw [LinearMap.map_smul, LinearMap.smul_apply, F.norm_a, smul_eq_mul, mul_neg,
      inv_mul_cancel₀ F.two_ne]
  have hrw : (orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w = -w := by
    rw [orthRefl_mulVec f F.norm_a, hfwa]
    change (2 : ZMod p)⁻¹ • F.a + (-1 : ZMod p) • F.a = -((2 : ZMod p)⁻¹ • F.a)
    have h : (2 : ZMod p)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ F.two_ne]
    have hc : (2 : ZMod p)⁻¹ - 1 = -((2 : ZMod p)⁻¹) := by linear_combination h
    calc (2 : ZMod p)⁻¹ • F.a + (-1 : ZMod p) • F.a
        = (2 : ZMod p)⁻¹ • F.a + -F.a := by rw [neg_one_smul (ZMod p)]
      _ = (2 : ZMod p)⁻¹ • F.a - F.a := by rw [sub_eq_add_neg]
      _ = (2 : ZMod p)⁻¹ • F.a - (1 : ZMod p) • F.a := by rw [one_smul]
      _ = ((2 : ZMod p)⁻¹ - 1) • F.a := by rw [sub_smul]
      _ = (-((2 : ZMod p)⁻¹)) • F.a := by rw [hc]
      _ = -((2 : ZMod p)⁻¹ • F.a) := by rw [neg_smul]
  have hconj : F.refl * F.siegel w * F.refl⁻¹ = (F.siegel w)⁻¹ := by
    have h1 : F.refl * F.siegel w * F.refl⁻¹ =
        F.siegel ((orthRefl f F.a : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) := by
      change orthRefl f F.a * F.siegel w * (orthRefl f F.a)⁻¹ = _
      exact F.siegel_conj (isOrthIsometry_orthRefl f F.symm F.a)
        (orthRefl_mulVec_s F F.a_orth_s) w
    rw [h1, hrw, F.siegel_neg hwS]
  have hcomm : ⁅F.siegel w, F.refl⁆ = F.siegel F.a := by
    calc ⁅F.siegel w, F.refl⁆
        = F.siegel w * F.refl * (F.siegel w)⁻¹ * F.refl⁻¹ := commutatorElement_def _ _
      _ = F.siegel w * (F.refl * F.siegel w * F.refl⁻¹)⁻¹ := by group
      _ = F.siegel w * ((F.siegel w)⁻¹)⁻¹ := by rw [hconj]
      _ = F.siegel w * F.siegel w := by rw [inv_inv]
      _ = F.siegel (w + w) := (F.siegel_add hwS hwS).symm
      _ = F.siegel F.a := by
          have hww : w + w = F.a := by
            change (2 : ZMod p)⁻¹ • F.a + (2 : ZMod p)⁻¹ • F.a = F.a
            have h : (2 : ZMod p)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ F.two_ne]
            rw [← add_smul, h, one_smul]
          rw [hww]
  have hmem := Subgroup.commutator_mem_commutator (H₁ := F.Y)
    (H₂ := Subgroup.zpowers F.refl) (F.siegel_mem_Y hwU)
    (Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one F.refl⟩)
  rwa [hcomm] at hmem

theorem siegel_mem_closure_of_span
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0})
    {w : Fin m → ZMod p} (hw : w ∈ F.U) :
    F.siegel w ∈ Subgroup.closure (F.siegel '' {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0}) := by
  let W : Set (Fin m → ZMod p) := {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0}
  have hmain : ∀ x ∈ Submodule.span (ZMod p) W,
      x ∈ F.U ∧ F.siegel x ∈ Subgroup.closure (F.siegel '' W) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨hy.1, Subgroup.subset_closure ⟨y, hy, rfl⟩⟩
    | zero => exact ⟨F.U.zero_mem, by rw [F.siegel_zero]; exact Subgroup.one_mem _⟩
    | add y z _ _ ihy ihz =>
        exact ⟨F.U.add_mem ihy.1 ihz.1, by
          rw [F.siegel_add (F.mem_U.1 ihy.1).1 (F.mem_U.1 ihz.1).1]
          exact Subgroup.mul_mem _ ihy.2 ihz.2⟩
    | smul c y _ ihy =>
        have hcy : c • y ∈ F.U := F.U.smul_mem c ihy.1
        have hval : c • y = c.val • y := by
          conv_lhs => rw [show c = (c.val : ZMod p) from (ZMod.natCast_zmod_val c).symm]
          exact Nat.cast_smul_eq_nsmul (ZMod p) c.val y
        exact ⟨hcy, by
          rw [hval, F.siegel_nsmul (F.mem_U.1 ihy.1).1 c.val]
          exact Subgroup.pow_mem _ ihy.2 c.val⟩
  exact (hmain w (hspan hw)).2

theorem Y_le_closure
    (hspan : F.U ≤ Submodule.span (ZMod p) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0}) :
    F.Y ≤ Subgroup.closure (orthReflSet p m f) := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := F.mem_Y.1 hg
  have hsub : F.siegel '' {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} ⊆
      (Subgroup.closure (orthReflSet p m f) : Set (GL (Fin m) (ZMod p))) := by
    rintro _ ⟨v, ⟨hvU, hvv, _hva⟩, rfl⟩
    have hvs : f v F.s = 0 := (F.mem_U.1 hvU).1
    have hnorm : f (v - F.s) (v - F.s) = -2 := by
      rw [show v - F.s = v + (-1 : ZMod p) • F.s by
        rw [neg_one_smul (ZMod p), sub_eq_add_neg]]
      simp [map_add, LinearMap.add_apply, F.symm, hvs, F.isotropic_s, hvv]
    have hT : F.siegel v = orthRefl f v * orthRefl f (v + (-1 : ZMod p) • F.s) := by
      simpa using OrthFrame.siegel_neg_smul F hvv hvs (-1)
    have h1 : orthRefl f v ∈ Subgroup.closure (orthReflSet p m f) :=
      Subgroup.subset_closure (orthRefl_mem f hvv)
    have h2 : orthRefl f (v + (-1 : ZMod p) • F.s) ∈
        Subgroup.closure (orthReflSet p m f) := by
      refine Subgroup.subset_closure (orthRefl_mem f ?_)
      simpa [neg_one_smul (ZMod p), sub_eq_add_neg] using hnorm
    rw [hT]
    exact Subgroup.mul_mem _ h1 h2
  exact (Subgroup.closure_le (Subgroup.closure (orthReflSet p m f))).2 hsub
    (F.siegel_mem_closure_of_span hspan hw)

theorem Z_le_orthConjSup (hz : ∀ w ∈ F.U, f w F.a = 0 → F.siegel w ∈ orthConjSup f F.a) :
    F.Z ≤ orthConjSup f F.a := by
  intro g hg
  obtain ⟨w, hw, hwa, hwT⟩ := F.mem_Z.1 hg
  rw [← hwT]
  exact hz w hw hwa

end OrthFrame

end CFSG.LocalAnalysis.WeakClosure81
