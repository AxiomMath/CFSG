module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.MS93.S32Nat
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

open Matrix in
private theorem s16h_sl28_mulVec_e0_eq_of_ne_zero {K : Type} [Field K] {u : Fin 2 → K}
    (hu : u ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K).mulVec ![1, 0] = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      exact hu (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open Matrix in
private theorem s16h_sl28_mulVec_eq_of_ne_zero {K : Type} [Field K] {u v : Fin 2 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K).mulVec u = v := by
  obtain ⟨a, ha⟩ := s16h_sl28_mulVec_e0_eq_of_ne_zero hu
  obtain ⟨b, hb⟩ := s16h_sl28_mulVec_e0_eq_of_ne_zero hv
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec u = ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hb]

private theorem s16h_sl28_isTransNZ_statedSL_two (K : Type) [Field K] :
    CFSG.Quasithin.MS93.S32.IsTransNZ (CFSG.Open.StatedSL 2 K) := by
  intro x y hx hy
  obtain ⟨g, hg⟩ := s16h_sl28_mulVec_eq_of_ne_zero (K := K) hx hy
  refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g, ?_⟩
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  exact hg

theorem s16h_sl28_quotient_fixV_aux {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hgen : commSub (commSub ⊤ L) L = commSub ⊤ L)
    {d : MulAut W} (hdcent : ∀ a ∈ L, d * a = a * d)
    (hdnt : d ∉ centSub (commSub ⊤ L)) :
    ∀ v ∈ commSub ⊤ L,
      d v * v⁻¹ ∈ commSub ⊤ L ⊓ fixV L → v ∈ commSub ⊤ L ⊓ fixV L := by
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hUinv : ∀ x ∈ L, ∀ w ∈ U, x w ∈ U :=
    s16jp_commSub_stable (L := L) (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))
  have hmapL : L.map (MulAut.conj d).toMonoidHom = L := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change d * b * d⁻¹ ∈ L
      rw [hdcent b hb, mul_assoc, mul_inv_cancel, mul_one]
      exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      change d * a * d⁻¹ = a
      rw [hdcent a ha, mul_assoc, mul_inv_cancel, mul_one]
  have hdU : ∀ w ∈ U, d w ∈ U := by
    intro w hw
    have hcomm := CFSG.Quasithin.Asc81c.commSub_map_conj (X := L) d
    have h1 : d w ∈ (commSub ⊤ L).map d.toMonoidHom := ⟨w, hw, rfl⟩
    rw [← hcomm, hmapL] at h1
    exact h1
  let φ : W →* W :=
    { toFun := fun w => d w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hφ_apply : ∀ w : W, φ w = d w * w⁻¹ := fun _ => rfl
  have hφequiv : ∀ (l : MulAut W) (hl : l ∈ L) (w : W), φ (l w) = l (φ w) := by
    intro l hl w
    have hdl : d (l w) = l (d w) := by
      calc d (l w) = (d * l) w := rfl
        _ = (l * d) w := by rw [hdcent l hl]
        _ = l (d w) := rfl
    change d (l w) * (l w)⁻¹ = l (d w * w⁻¹)
    rw [hdl, map_mul, map_inv]
  obtain ⟨K, hKf, hKfin, hKcard, π, hπ⟩ := hrow.2
  letI : Field K := hKf
  letI : Finite K := hKfin
  have htrans : CFSG.Quasithin.MS93.S32.IsTransNZ (CFSG.Open.StatedSL 2 K) :=
    s16h_sl28_isTransNZ_statedSL_two K
  have hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → Z ≤ J → J ≤ U →
      J = Z ∨ J = U :=
    fun J hJ hZJ hJU => CFSG.Quasithin.MS93.S32.natReal_inv_eq htrans hπ hJ hZJ hJU
  set J : Subgroup W := U ⊓ Subgroup.comap φ Z with hJ
  have hJI : J ≤ U := inf_le_left
  have hJinv : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    have hφwZ : φ w ∈ Z := hw.2
    refine ⟨hUinv x hx w hw.1, ?_⟩
    change φ (x w) ∈ Z
    rw [hφequiv x hx w]
    have hxfix : x (φ w) = φ w := mem_fixV.mp hφwZ.2 x hx
    rw [hxfix]
    exact hφwZ
  have hZJ : Z ≤ J := by
    intro z hz
    have hdz_fix : d z ∈ fixV L := by
      rw [mem_fixV]
      intro l hl
      have h1 : l (d z) = d (l z) := by
        calc l (d z) = (l * d) z := rfl
          _ = (d * l) z := by rw [← hdcent l hl]
          _ = d (l z) := rfl
      rw [h1, mem_fixV.mp hz.2 l hl]
    have hdzZ : d z ∈ Z := ⟨hdU z hz.1, hdz_fix⟩
    refine ⟨hz.1, ?_⟩
    change φ z ∈ Z
    rw [hφ_apply]
    exact Z.mul_mem hdzZ (Z.inv_mem hz)
  rcases hirr J hJinv hZJ hJI with hJZ | hJU
  · intro v hv hφv
    have hvJ : v ∈ J := ⟨hv, by change φ v ∈ Z; rw [hφ_apply]; exact hφv⟩
    rwa [hJZ] at hvJ
  · exfalso
    have hUJ : U ≤ J := le_of_eq hJU.symm
    have hφ1 : ∀ w ∈ U, φ w = 1 := by
      have hker : commSub U L ≤ φ.ker := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, u, hu, rfl⟩
        change φ (l u * u⁻¹) = 1
        rw [map_mul, map_inv, hφequiv l hl u]
        have hZu : φ u ∈ Z := (hUJ hu).2
        rw [mem_fixV.mp hZu.2 l hl, mul_inv_cancel]
      have hUker : U ≤ φ.ker := by rwa [hgen] at hker
      intro w hw
      exact MonoidHom.mem_ker.mp (hUker hw)
    apply hdnt
    rw [mem_centSub]
    intro w hw
    exact mul_inv_eq_one.mp (hφ1 w hw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
