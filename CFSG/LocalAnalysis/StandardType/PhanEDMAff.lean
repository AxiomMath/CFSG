module

public import CFSG.LocalAnalysis.StandardType.PhanEDMPanel
public import CFSG.LocalAnalysis.StandardType.PhanEDMFilt
public import CFSG.LocalAnalysis.StandardType.PhanEDMBuilding
public import CFSG.LocalAnalysis.StandardType.PhanEDMCoxeter

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C}

structure IsRankFn (cs : CoxeterSystem M W) (rk : W → ℕ) : Prop where
  injective : Function.Injective rk
  map_one : rk 1 = 0
  lt_of_length_lt : ∀ u v, cs.length u < cs.length v → rk u < rk v

@[expose] def flipLev (rk : W → ℕ) (δ : C → C → W) (w₀ : W) (t : C → C) (x : C) : ℕ :=
  rk (dstar δ w₀ t x)

private theorem q2cDMa_left_ascent {w : W} (hw : w * w = 1) {J : Set ι}
    (hasc : ∀ j ∈ J, cs.length (w * cs.simple j) = cs.length w + 1) :
    ∀ j ∈ J, cs.length (cs.simple j * w) = cs.length w + 1 := by
  intro j hj
  rw [CoxeterSystem.length_simple_mul_eq_length_mul_simple_of_mul_self cs hw j]
  exact hasc j hj

private theorem q2cDMa_mem_doubleCoset (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {J : Set ι} {c x y : C}
    (hx : x ∈ residue cs δ J c) (hy : y ∈ residue cs δ J c) :
    dstar δ w₀ t y ∈
      DoubleCoset.doubleCoset (dstar δ w₀ t x) (cs.parabolic J) (cs.parabolic J) := by
  have hwx := dstar_mem_doubleCoset hB hw ht hx
  have hwy := dstar_mem_doubleCoset hB hw ht hy
  rw [DoubleCoset.doubleCoset_eq_of_mem hwx]
  exact hwy

theorem forall_ascent_of_minimal (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {J : Set ι} {c x : C} (hx : x ∈ residue cs δ J c)
    (hmin : ∀ z ∈ residue cs δ J c,
      cs.length (dstar δ w₀ t x) ≤ cs.length (dstar δ w₀ t z)) :
    ∀ j ∈ J, cs.length (dstar δ w₀ t x * cs.simple j) = cs.length (dstar δ w₀ t x) + 1 := by
  intro j hj
  rcases cs.length_mul_simple (dstar δ w₀ t x) j with h | h
  · exact h
  · exfalso
    have hdesc : cs.length (dstar δ w₀ t x * cs.simple j) < cs.length (dstar δ w₀ t x) := by
      omega
    obtain ⟨z', hz'panel, hz'lt⟩ := exists_panel_dstar_lt hB hw ht (z := x) hdesc
    have hz'J : z' ∈ residue cs δ J x :=
      residue_mono (J := {j}) (K := J) (Set.singleton_subset_iff.mpr hj) x hz'panel
    have hz'R : z' ∈ residue cs δ J c := mem_residue_trans hx hz'J
    exact absurd (hmin z' hz'R) (not_le.mpr hz'lt)

theorem length_le_of_forall_ascent_dstar (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {J : Set ι} {c x : C} (hx : x ∈ residue cs δ J c)
    (hasc : ∀ j ∈ J,
      cs.length (dstar δ w₀ t x * cs.simple j) = cs.length (dstar δ w₀ t x) + 1) :
    ∀ z ∈ residue cs δ J c, cs.length (dstar δ w₀ t x) ≤ cs.length (dstar δ w₀ t z) := by
  intro z hz
  have hxl := q2cDMa_left_ascent (dstar_mul_self hB hw ht x) hasc
  have hmem := q2cDMa_mem_doubleCoset hB hw ht (J := J) (c := c) hx hz
  exact CoxeterSystem.length_le_of_forall_ascent cs hxl hasc hmem

theorem dstar_eq_of_minimal (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {J : Set ι} {c x y : C} (hx : x ∈ residue cs δ J c)
    (hy : y ∈ residue cs δ J c)
    (hxm : ∀ z ∈ residue cs δ J c, cs.length (dstar δ w₀ t x) ≤ cs.length (dstar δ w₀ t z))
    (hym : ∀ z ∈ residue cs δ J c, cs.length (dstar δ w₀ t y) ≤ cs.length (dstar δ w₀ t z)) :
    dstar δ w₀ t x = dstar δ w₀ t y := by
  have hxr := forall_ascent_of_minimal hB hw ht hx hxm
  have hyr := forall_ascent_of_minimal hB hw ht hy hym
  have hxl := q2cDMa_left_ascent (dstar_mul_self hB hw ht x) hxr
  have hyl := q2cDMa_left_ascent (dstar_mul_self hB hw ht y) hyr
  have hmem := q2cDMa_mem_doubleCoset hB hw ht (J := J) (c := c) hx hy
  exact CoxeterSystem.eq_of_forall_ascent cs hxl hxr hyl hyr hmem

theorem flipLev_min_iff (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {rk : W → ℕ} (hrk : IsRankFn cs rk) {J : Set ι} {c x : C}
    (hx : x ∈ residue cs δ J c) :
    (∀ y ∈ residue cs δ J c, flipLev rk δ w₀ t x ≤ flipLev rk δ w₀ t y) ↔
      ∀ z ∈ residue cs δ J c, cs.length (dstar δ w₀ t x) ≤ cs.length (dstar δ w₀ t z) := by
  classical
  constructor
  · intro hminrk
    have hex : ∃ n : ℕ, ∃ z ∈ residue cs δ J c, cs.length (dstar δ w₀ t z) = n :=
      ⟨_, x, hx, rfl⟩
    obtain ⟨xstar, hxstarR, hxstar_eq⟩ := Nat.find_spec hex
    have hxstar_min : ∀ z ∈ residue cs δ J c,
        cs.length (dstar δ w₀ t xstar) ≤ cs.length (dstar δ w₀ t z) := by
      intro z hz
      have h := Nat.find_min' hex ⟨z, hz, rfl⟩
      omega
    have hxstar_ascent := forall_ascent_of_minimal hB hw ht hxstarR hxstar_min
    have hxstar_minL := length_le_of_forall_ascent_dstar hB hw ht hxstarR hxstar_ascent
    intro z hz
    have hxle : cs.length (dstar δ w₀ t x) ≤ cs.length (dstar δ w₀ t xstar) := by
      by_contra hlt
      have hlt' : cs.length (dstar δ w₀ t xstar) < cs.length (dstar δ w₀ t x) :=
        not_le.mp hlt
      have h1 : rk (dstar δ w₀ t xstar) < rk (dstar δ w₀ t x) :=
        hrk.lt_of_length_lt _ _ hlt'
      have h2 : rk (dstar δ w₀ t x) ≤ rk (dstar δ w₀ t xstar) := by
        simpa only [flipLev] using hminrk xstar hxstarR
      omega
    exact le_trans hxle (hxstar_minL z hz)
  · intro hminL y hy
    rcases lt_or_eq_of_le (hminL y hy) with hlt | heq
    · exact le_of_lt (hrk.lt_of_length_lt _ _ hlt)
    · have hymin : ∀ z ∈ residue cs δ J c,
          cs.length (dstar δ w₀ t y) ≤ cs.length (dstar δ w₀ t z) := by
        intro z hz
        rw [← heq]
        exact hminL z hz
      have heq' := dstar_eq_of_minimal hB hw ht hx hy hminL hymin
      exact le_of_eq (congrArg rk heq')

theorem aff_flipLev_eq_flipMaxSet (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {rk : W → ℕ} (hrk : IsRankFn cs rk) (J : Set ι) (c : C) :
    aff (flipLev rk δ w₀ t) (residue cs δ J c) = flipMaxSet cs δ t J c := by
  ext z
  constructor
  · rintro ⟨hzR, hzmin⟩
    refine ⟨hzR, fun y hy => ?_⟩
    have h := (flipLev_min_iff hB hw ht hrk hzR).mp hzmin y hy
    have h1 := length_dstar_add (cs := cs) (δ := δ) (t := t) hw y
    have h2 := length_dstar_add (cs := cs) (δ := δ) (t := t) hw z
    omega
  · rintro ⟨hzR, hzmax⟩
    refine ⟨hzR, ?_⟩
    rw [flipLev_min_iff hB hw ht hrk hzR]
    intro y hy
    have h := hzmax y hy
    have h1 := length_dstar_add (cs := cs) (δ := δ) (t := t) hw y
    have h2 := length_dstar_add (cs := cs) (δ := δ) (t := t) hw z
    omega

theorem flipLev_isResidual (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {rk : W → ℕ} (hrk : IsRankFn cs rk) :
    IsResidual (buildingSystem cs δ) (flipLev rk δ w₀ t) := by
  intro J c hJ
  rw [buildingSystem_residue hB J c]
  intro m hm
  obtain ⟨x₀, hx₀R, hx₀m⟩ := hm
  by_cases hcase : ∃ y ∈ residue cs δ J c, flipLev rk δ w₀ t y = m + 1
  · obtain ⟨y, hyR, hyEq⟩ := hcase
    have hyEq' : rk (dstar δ w₀ t y) = m + 1 := by simpa only [flipLev] using hyEq
    have hex : ∃ j ∈ J,
        cs.length (dstar δ w₀ t y * cs.simple j) < cs.length (dstar δ w₀ t y) := by
      by_contra hno
      push Not at hno
      have hasc : ∀ j ∈ J, cs.length (dstar δ w₀ t y * cs.simple j) =
          cs.length (dstar δ w₀ t y) + 1 := by
        intro j hj
        rcases cs.length_mul_simple (dstar δ w₀ t y) j with h | h
        · exact h
        · have hlt : cs.length (dstar δ w₀ t y * cs.simple j) <
              cs.length (dstar δ w₀ t y) := by omega
          exact absurd (hno j hj) (not_le.mpr hlt)
      have hminL := length_le_of_forall_ascent_dstar hB hw ht hyR hasc
      have hymin : ∀ z ∈ residue cs δ J c,
          flipLev rk δ w₀ t y ≤ flipLev rk δ w₀ t z :=
        (flipLev_min_iff hB hw ht hrk hyR).mpr hminL
      have hle : rk (dstar δ w₀ t y) ≤ rk (dstar δ w₀ t x₀) := by
        simpa only [flipLev] using hymin x₀ hx₀R
      have hx₀m' : rk (dstar δ w₀ t x₀) ≤ m := by simpa only [flipLev] using hx₀m
      omega
    obtain ⟨j, hjJ, hjdesc⟩ := hex
    refine ⟨j, hjJ, fun x hxR hxlev => ?_⟩
    by_cases hxl : flipLev rk δ w₀ t x ≤ m
    · exact ⟨x, hxR, hxl, ((buildingSystem cs δ).equivalence j).refl x⟩
    · simp only [flipLev] at hxlev hxl
      have hxEq : rk (dstar δ w₀ t x) = m + 1 := by omega
      have hwx : dstar δ w₀ t x = dstar δ w₀ t y := by
        apply hrk.injective
        rw [hxEq, hyEq']
      have hjdesc' : cs.length (dstar δ w₀ t x * cs.simple j) <
          cs.length (dstar δ w₀ t x) := by
        rw [hwx]
        exact hjdesc
      obtain ⟨z', hz'panel, hz'lt⟩ := exists_panel_dstar_lt hB hw ht (z := x) hjdesc'
      have hz'J : z' ∈ residue cs δ J x :=
        residue_mono (J := {j}) (K := J) (Set.singleton_subset_iff.mpr hjJ) x hz'panel
      have hz'R : z' ∈ residue cs δ J c := mem_residue_trans hxR hz'J
      have hz'lev : flipLev rk δ w₀ t z' ≤ m := by
        show rk (dstar δ w₀ t z') ≤ m
        have hlt : rk (dstar δ w₀ t z') < rk (dstar δ w₀ t x) :=
          hrk.lt_of_length_lt _ _ hz'lt
        omega
      have hadj : (buildingSystem cs δ).adj j x z' := by
        apply ChamberSystem.mem_residue_singleton.mp
        rw [buildingSystem_residue hB {j} x]
        exact hz'panel
      exact ⟨z', hz'R, hz'lev, hadj⟩
  · push Not at hcase
    obtain ⟨j, hjJ⟩ := hJ
    refine ⟨j, hjJ, fun x hxR hxlev => ?_⟩
    have hne : flipLev rk δ w₀ t x ≠ m + 1 := hcase x hxR
    exact ⟨x, hxR, by omega, ((buildingSystem cs δ).equivalence j).refl x⟩

theorem flipLev_eq_zero_iff (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    {rk : W → ℕ} (hrk : IsRankFn cs rk) (x : C) :
    flipLev rk δ w₀ t x = 0 ↔ x ∈ flipOpSet δ w₀ t := by
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  rw [flipOpSet]
  constructor
  · intro h
    have hd : dstar δ w₀ t x = 1 := by
      apply hrk.injective
      have h' : rk (dstar δ w₀ t x) = 0 := by simpa only [flipLev] using h
      rw [h', hrk.map_one]
    have hd' : δ x (t x) * w₀ = 1 := hd
    calc δ x (t x) = δ x (t x) * w₀ * w₀ := by rw [mul_assoc, hw0, mul_one]
      _ = 1 * w₀ := by rw [hd']
      _ = w₀ := one_mul _
  · intro h
    have hd : dstar δ w₀ t x = 1 := by rw [dstar, h, hw0]
    rw [flipLev, hd, hrk.map_one]

end CFSG.ClassicalInvolution.Phan.PhanE.DM
