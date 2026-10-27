module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.FixedPointFreeOutsideCentral
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoExtraspecial
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix

variable {K : Type} [Field K]

@[expose] def threeAMatrix (ω : K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal ![ω, ω ^ 2, 1, 1, 1, 1]

@[expose] noncomputable def threeASU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (threeAMatrix ω) (by
      have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
      have hdet : (threeAMatrix ω).det = 1 := by
        simp [threeAMatrix, Matrix.det_diagonal, Fin.prod_univ_six]
        rw [show ω * ω ^ 2 = ω ^ 3 by ring, h3]
      rw [hdet]; exact one_ne_zero), by
      have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · have hdet : (threeAMatrix ω).det = 1 := by
          simp [threeAMatrix, Matrix.det_diagonal, Fin.prod_univ_six]
          rw [show ω * ω ^ 2 = ω ^ 3 by ring, h3]
        exact hdet
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [threeAMatrix, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind⟩

theorem coe_threeASU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (((threeASU hω : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = threeAMatrix ω :=
  rfl

@[expose] noncomputable def threeA {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _ (threeASU hω)

theorem threeA_eq_extraspecial {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    threeA hω = Extraspecial.threeAAux (K := K) hω := by
  unfold threeA Extraspecial.threeAAux
  apply congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
  apply Subtype.ext
  apply Units.ext
  rfl

theorem exists_extraspecial_conj_threeA [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ (P : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
      (z : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      Nat.card P = 27 ∧ (∀ g ∈ P, g ^ 3 = 1) ∧ z ∈ P ∧ (∀ g ∈ P, g * z = z * g) ∧
      ∀ g ∈ P, g ∉ Subgroup.zpowers z →
        ∃ u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
          u * threeA hω * u⁻¹ = g ∨ u * (threeA hω)⁻¹ * u⁻¹ = g := by
  obtain ⟨P, z, hP, hexp, hz, hcomm, hconj⟩ :=
    Extraspecial.exists_extraspecial_conj_threeAAux (K := K) hK hω
  refine ⟨P, z, hP, hexp, hz, hcomm, ?_⟩
  intro g hg hgz
  obtain ⟨u, hu⟩ := hconj g hg hgz
  refine ⟨u, ?_⟩
  rw [threeA_eq_extraspecial hω]
  exact hu

theorem le_of_centralizer_le_of_threeA {G : Type*} [Group G] [Finite G] [Finite K]
    (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {L X Y : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) {e : G} (heL : e ∈ L)
    (he : ∃ u, u * φ ⟨e, heL⟩ * u⁻¹ = threeA hω)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hY : ¬ 3 ∣ Nat.card Y)
    (hfix : Y ⊓ Subgroup.centralizer {e} ≤ X) : Y ≤ X := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨P₀, z₀, hP₀card, hP₀exp, hz₀P, hP₀cent, hP₀conj⟩ :=
    exists_extraspecial_conj_threeA (K := K) hK hω
  let P_L : Subgroup L := P₀.comap φ.toMonoidHom
  let zL : P_L := ⟨φ.symm z₀, by
    change φ (φ.symm z₀) ∈ P₀
    simpa using hz₀P⟩
  let P_G : Subgroup G := P_L.map L.subtype
  let zG : G := L.subtype zL
  have hzGP : zG ∈ P_G := Subgroup.mem_map.mpr ⟨zL, zL.2, rfl⟩
  let eP : P_L ≃ P₀ :=
    { toFun := fun l => ⟨φ (l : L), l.2⟩
      invFun := fun h => ⟨φ.symm h, by
        change φ (φ.symm h) ∈ P₀
        simpa using h.2⟩
      left_inv := by intro l; apply Subtype.ext; simp
      right_inv := by intro h; apply Subtype.ext; simp }
  have hP_Gcard : Nat.card P_G = 27 := by
    change Nat.card ↥(P_L.map L.subtype) = 27
    let ePG : ↥(P_L.map L.subtype) ≃ P₀ :=
      (Subgroup.equivMapOfInjective P_L L.subtype
        (Subgroup.subtype_injective L)).symm.toEquiv.trans eP
    rw [Nat.card_congr ePG, hP₀card]
  have hexp : ∀ g ∈ P_G, g ^ 3 = 1 := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨l, hl, rfl⟩
    have hL : l ^ 3 = 1 := by
      apply φ.injective
      have h := hP₀exp (φ l) hl
      simpa only [map_pow, map_one] using h
    simpa only [map_pow, map_one] using congrArg (L.subtype) hL
  have hzL : zL ∈ Subgroup.center P_L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    apply φ.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    have hzLimg : φ (zL : L) = z₀ := by
      change φ (φ.symm z₀) = z₀
      exact MulEquiv.apply_symm_apply φ z₀
    rw [hzLimg]
    exact hP₀cent (φ (l : L)) l.2
  have hzcent : ∀ g ∈ P_G, g * zG = zG * g := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨l, hl, rfl⟩
    have h := Subgroup.mem_center_iff.mp hzL ⟨l, hl⟩
    have h' : (l : L) * (zL : L) = (zL : L) * (l : L) := congrArg Subtype.val h
    simpa [zG] using congrArg (L.subtype) h'
  have hP_L : P_G ≤ L := by
    rintro g ⟨l, -, rfl⟩
    exact l.2
  have hPX : P_G ≤ Subgroup.normalizer (X : Set G) := hP_L.trans hLX
  have hPY : P_G ≤ Subgroup.normalizer (Y : Set G) := hP_L.trans hLY
  have hfix' : ∀ g ∈ P_G, g ∉ Subgroup.zpowers zG →
      Y ⊓ Subgroup.centralizer {g} ≤ X := by
    intro g hg hgz y hy
    rw [Subgroup.mem_inf] at hy
    rcases hy with ⟨hyY, hyC⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC
    rcases Subgroup.mem_map.mp hg with ⟨l, hl, rfl⟩
    have hg0 : φ l ∉ Subgroup.zpowers z₀ := by
      intro hmem
      apply hgz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      change L.subtype ((zL : L) ^ k) = L.subtype l
      congr 1
      change (φ.symm z₀) ^ k = (l : L)
      calc (φ.symm z₀) ^ k = φ.symm (z₀ ^ k) := (map_zpow φ.symm z₀ k).symm
        _ = φ.symm (φ l) := by rw [hk]
        _ = (l : L) := φ.symm_apply_apply _
    obtain ⟨u₀, hu₀⟩ := he
    let eL : L := ⟨e, heL⟩
    rcases hP₀conj (φ l) hl hg0 with ⟨u, hu | hu⟩
    · let wL : L := φ.symm (u * u₀)
      let wG : G := L.subtype wL
      have hwL : wL * eL * wL⁻¹ = l := by
        apply φ.injective
        change φ (φ.symm (u * u₀) * eL * (φ.symm (u * u₀))⁻¹) = φ l
        rw [map_mul, map_mul, map_inv]
        simp only [MulEquiv.apply_symm_apply]
        calc (u * u₀) * φ eL * (u * u₀)⁻¹ = u * (u₀ * φ eL * u₀⁻¹) * u⁻¹ := by group
          _ = u * threeA hω * u⁻¹ := by rw [hu₀]
          _ = φ l := hu
      have hwG : wG * e * wG⁻¹ = L.subtype l := by
        simpa [wG, eL] using congrArg (L.subtype) hwL
      let y' : G := wG⁻¹ * y * wG
      have hy'Y : y' ∈ Y := by
        have hwGinv : wG⁻¹ ∈ L := L.inv_mem wL.2
        have h := (Subgroup.mem_normalizer_iff.mp (hLY hwGinv) y).mp hyY
        simpa [y', wG] using h
      have hy'C : y' ∈ Subgroup.centralizer ({e} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hwe : wG * e = L.subtype l * wG := by
          calc wG * e = (wG * e * wG⁻¹) * wG := by group
            _ = L.subtype l * wG := by rw [hwG]
        calc y' * e = wG⁻¹ * y * (wG * e) := by simp only [y']; group
          _ = wG⁻¹ * y * (L.subtype l * wG) := by rw [hwe]
          _ = wG⁻¹ * (y * L.subtype l) * wG := by group
          _ = wG⁻¹ * (L.subtype l * y) * wG := by rw [hyC]
          _ = e * y' := by
            rw [← hwG]
            simp only [y']; group
      have hy'X : y' ∈ X := hfix (Subgroup.mem_inf.mpr ⟨hy'Y, hy'C⟩)
      have hyX : y ∈ X := by
        have h := (Subgroup.mem_normalizer_iff.mp (hLX wL.2) y').mp hy'X
        change wG * y' * wG⁻¹ ∈ X at h
        have hy_eq : wG * y' * wG⁻¹ = y := by
          simp only [y', wG]; group
        rwa [hy_eq] at h
      exact hyX
    · let wL : L := φ.symm (u * u₀)
      let wG : G := L.subtype wL
      have hwL : wL * eL⁻¹ * wL⁻¹ = l := by
        apply φ.injective
        change φ (φ.symm (u * u₀) * eL⁻¹ * (φ.symm (u * u₀))⁻¹) = φ l
        rw [map_mul, map_mul, map_inv, map_inv]
        simp only [MulEquiv.apply_symm_apply]
        calc (u * u₀) * (φ eL)⁻¹ * (u * u₀)⁻¹ =
            u * (u₀ * φ eL * u₀⁻¹)⁻¹ * u⁻¹ := by group
          _ = u * (threeA hω)⁻¹ * u⁻¹ := by rw [hu₀]
          _ = φ l := hu
      have hwG : wG * e⁻¹ * wG⁻¹ = L.subtype l := by
        simpa [wG, eL] using congrArg (L.subtype) hwL
      let y' : G := wG⁻¹ * y * wG
      have hy'Y : y' ∈ Y := by
        have hwGinv : wG⁻¹ ∈ L := L.inv_mem wL.2
        have h := (Subgroup.mem_normalizer_iff.mp (hLY hwGinv) y).mp hyY
        simpa [y', wG] using h
      have hy'C : y' ∈ Subgroup.centralizer ({e} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hwe : wG * e⁻¹ = L.subtype l * wG := by
          calc wG * e⁻¹ = (wG * e⁻¹ * wG⁻¹) * wG := by group
            _ = L.subtype l * wG := by rw [hwG]
        have hce_inv : y' * e⁻¹ = e⁻¹ * y' := by
          calc y' * e⁻¹ = wG⁻¹ * y * (wG * e⁻¹) := by simp only [y']; group
            _ = wG⁻¹ * y * (L.subtype l * wG) := by rw [hwe]
            _ = wG⁻¹ * (y * L.subtype l) * wG := by group
            _ = wG⁻¹ * (L.subtype l * y) * wG := by rw [hyC]
            _ = e⁻¹ * y' := by
              rw [← hwG]
              simp only [y']; group
        have h'' : e * y' = y' * e := by
          calc e * y' = e * (y' * e⁻¹) * e := by group
            _ = e * (e⁻¹ * y') * e := by rw [hce_inv]
            _ = y' * e := by group
        exact h''.symm
      have hy'X : y' ∈ X := hfix (Subgroup.mem_inf.mpr ⟨hy'Y, hy'C⟩)
      have hyX : y ∈ X := by
        have h := (Subgroup.mem_normalizer_iff.mp (hLX wL.2) y').mp hy'X
        change wG * y' * wG⁻¹ ∈ X at h
        have hy_eq : wG * y' * wG⁻¹ = y := by
          simp only [y', wG]; group
        rwa [hy_eq] at h
      exact hyX
  exact CFSG.le_of_centralizer_le_outside_zpowers
    (p := 3) hYX hPX hPY hY hexp (by rw [hP_Gcard]; norm_num) hzGP hzcent hfix'

end CFSG.StandardType.USixTwo

end
