module

public import CFSG.RankThree.PartOne.KF4.Kernel4
public import CFSG.RankThree.PartOne.KF4.B2Native
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix)
open scoped Matrix MatrixGroups


@[expose] def f4B2N1 (L : Type) [Field L] : ModGL Tag.F4 L :=
  weylElt Tag.F4 L (f4Index 1) 1 * weylElt Tag.F4 L (f4Index 2) 1

@[expose] def f4B2N2 (L : Type) [Field L] : ModGL Tag.F4 L :=
  weylElt Tag.F4 L (f4Index 2) 1 * weylElt Tag.F4 L (f4Index 1) 1

theorem f4B2_rot1 :
    (simple Tag.F4 (f4Index 1) * simple Tag.F4 (f4Index 2)) •
        (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
      (simple Tag.F4 (f4Index 1) * simple Tag.F4 (f4Index 2)) •
        (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma := by
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem f4B2_rot2 :
    (simple Tag.F4 (f4Index 2) * simple Tag.F4 (f4Index 1)) •
        (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
      (simple Tag.F4 (f4Index 2) * simple Tag.F4 (f4Index 1)) •
        (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma := by
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem exists_torus2_rootDiag {L : Type} [Field L] [IsAlgClosed L] (u2 u3 : Lˣ) :
    ∃ (s t : Lˣ) (a : Fin Tag.F4.rank → Lˣ),
      torus2Elt (f4Index 1) (f4Index 2) s t = rootDiagUnit Tag.F4 a ∧
        a (f4Index 1) = u2 ∧ a (f4Index 2) = u3 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (u2 : L) (n := 2) (by norm_num)
  have hx0 : x ≠ 0 := fun h => u2.ne_zero (by rw [← hx, h]; simp)
  set r : Lˣ := Units.mk0 x hx0 with hr
  have hrr : (r : L) ^ 2 = (u2 : L) := hx
  refine ⟨u2 * u3, u3 * r,
    fun j => (u2 * u3) ^ Tag.F4.cartan (f4Index 1) j * (u3 * r) ^ Tag.F4.cartan (f4Index 2) j,
    ?_, ?_, ?_⟩
  · rw [torus2Elt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    rfl
  · have h1 : Tag.F4.cartan (f4Index 1) (f4Index 1) = 2 := by decide +kernel
    have h2 : Tag.F4.cartan (f4Index 2) (f4Index 1) = -2 := by decide +kernel
    apply Units.ext
    simp only [h1, h2, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mul]
    have hu2 : (u2 : L) ≠ 0 := u2.ne_zero
    have hu3 : (u3 : L) ≠ 0 := u3.ne_zero
    have hr0 : (r : L) ≠ 0 := r.ne_zero
    rw [zpow_neg, zpow_ofNat, zpow_ofNat]
    field_simp
    exact hrr.symm
  · have h1 : Tag.F4.cartan (f4Index 1) (f4Index 2) = -1 := by decide +kernel
    have h2 : Tag.F4.cartan (f4Index 2) (f4Index 2) = 2 := by decide +kernel
    apply Units.ext
    simp only [h1, h2, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mul]
    have hu2 : (u2 : L) ≠ 0 := u2.ne_zero
    have hu3 : (u3 : L) ≠ 0 := u3.ne_zero
    have hr0 : (r : L) ≠ 0 := r.ne_zero
    rw [zpow_neg, zpow_one, zpow_ofNat]
    field_simp
    rw [hrr]

theorem rootSL2_single_eq_simple {L : Type} [Field L] (τ : Tag) (i : Fin τ.rank) (A : SL2 L) :
    rootSL2 τ L (Pi.single i 1) A = simpleRootSL2 τ L i A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem f4B2_twist {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) (n : ModGL Tag.F4 L)
    (hnm : n ∈ monomialSubgroup Tag.F4 L) (w₀ : WeylGroup Tag.F4) (hw₀ : MapsRootLines n w₀)
    (hrot : (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Gamma) ∨
        (w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4B2Beta ∧
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Gamma)) :
    ∃ A ∈ subsystemGroup Tag.F4 L f4B2Support, ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹ := by
  classical
  have hi1 : f4Index 1 ∈ f4B2Support := (mem_f4B2Support _).2 (Or.inl rfl)
  have hi2 : f4Index 2 ∈ f4B2Support := (mem_f4B2Support _).2 (Or.inr rfl)
  obtain ⟨N, hNG, hNm, ρ, hNρ, hρ1, hρ2⟩ : ∃ N ∈ subsystemGroup Tag.F4 L f4B2Support,
      ∃ hNm : N ∈ monomialSubgroup Tag.F4 L, ∃ ρ : WeylGroup Tag.F4, MapsRootLines N ρ ∧
        ρ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) =
          w₀ • (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) ∧
        ρ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) =
          w₀ • (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) := by
    have hw1 := weylElt_mem_subsystemGroup (K := L) hi1 (1 : Lˣ)
    have hw2 := weylElt_mem_subsystemGroup (K := L) hi2 (1 : Lˣ)
    have hm1 := weylElt_mem_monomialSubgroup (τ := Tag.F4) (R := L) (f4Index 1)
    have hm2 := weylElt_mem_monomialSubgroup (τ := Tag.F4) (R := L) (f4Index 2)
    rcases hrot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨f4B2N1 L, mul_mem hw1 hw2, mul_mem hm1 hm2,
        simple Tag.F4 (f4Index 1) * simple Tag.F4 (f4Index 2),
        (mapsRootLines_weylElt _).mul (mapsRootLines_weylElt _), ?_, ?_⟩
      · rw [h1]
        exact f4B2_rot1.1
      · rw [h2]
        exact f4B2_rot1.2
    · refine ⟨f4B2N2 L, mul_mem hw2 hw1, mul_mem hm2 hm1,
        simple Tag.F4 (f4Index 2) * simple Tag.F4 (f4Index 1),
        (mapsRootLines_weylElt _).mul (mapsRootLines_weylElt _), ?_, ?_⟩
      · rw [h1]
        exact f4B2_rot2.1
      · rw [h2]
        exact f4B2_rot2.2
  obtain ⟨s1, hs1⟩ := exists_conj_rootSL2_eq hnm hw₀ (IsRoot.basis (f4Index 1)) rfl
  obtain ⟨s2, hs2⟩ := exists_conj_rootSL2_eq hnm hw₀ (IsRoot.basis (f4Index 2)) rfl
  obtain ⟨s1', hs1'⟩ := exists_conj_rootSL2_eq hNm hNρ (IsRoot.basis (f4Index 1)) hρ1
  obtain ⟨s2', hs2'⟩ := exists_conj_rootSL2_eq hNm hNρ (IsRoot.basis (f4Index 2)) hρ2
  obtain ⟨s, t, a, hda, ha1, ha2⟩ := exists_torus2_rootDiag (L := L) (s1'⁻¹ * s1) (s2'⁻¹ * s2)
  refine ⟨N * torus2Elt (f4Index 1) (f4Index 2) s t, mul_mem hNG (torus2Elt_mem_f4B2 s t), ?_⟩
  have hgen : ∀ i : Fin Tag.F4.rank, i ∈ f4B2Support → ∀ B : SL2 L,
      n * Units.map (entrywiseHom Fr) (rootSL2 Tag.F4 L (Pi.single i 1) B) * n⁻¹ =
        (N * torus2Elt (f4Index 1) (f4Index 2) s t) *
          Units.map (entrywiseHom Fr) (rootSL2 Tag.F4 L (Pi.single i 1) B) *
            (N * torus2Elt (f4Index 1) (f4Index 2) s t)⁻¹ := by
    intro i hi B
    rw [entrywise_rootSL2_of_field]
    have key : ∀ (si si' : Lˣ), (∀ B' : SL2 L, n * rootSL2 Tag.F4 L (Pi.single i 1) B' * n⁻¹ =
          rootSL2 Tag.F4 L (w₀ • Pi.single i 1) (conjSL (diagUnitOne si) B')) →
        (∀ B' : SL2 L, N * rootSL2 Tag.F4 L (Pi.single i 1) B' * N⁻¹ =
          rootSL2 Tag.F4 L (w₀ • Pi.single i 1) (conjSL (diagUnitOne si') B')) →
        a i = si'⁻¹ * si →
        n * rootSL2 Tag.F4 L (Pi.single i 1) (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹ =
          (N * torus2Elt (f4Index 1) (f4Index 2) s t) *
            rootSL2 Tag.F4 L (Pi.single i 1) (Matrix.SpecialLinearGroup.map Fr B) *
              (N * torus2Elt (f4Index 1) (f4Index 2) s t)⁻¹ := by
      intro si si' hsi hsi' hai
      have e1 : (N * torus2Elt (f4Index 1) (f4Index 2) s t) *
            rootSL2 Tag.F4 L (Pi.single i 1) (Matrix.SpecialLinearGroup.map Fr B) *
              (N * torus2Elt (f4Index 1) (f4Index 2) s t)⁻¹ =
          N * (rootDiagUnit Tag.F4 a * rootSL2 Tag.F4 L (Pi.single i 1)
            (Matrix.SpecialLinearGroup.map Fr B) * (rootDiagUnit Tag.F4 a)⁻¹) * N⁻¹ := by
        rw [hda]
        group
      rw [e1, rootDiagUnit_conj_rootSL2 a (IsRoot.basis i), hsi', hsi,
        CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single,
        conjSL_diagUnitOne_mul, hai, mul_inv_cancel_left]
    rcases (mem_f4B2Support i).1 hi with rfl | rfl
    · exact key s1 s1' hs1 hs1' ha1
    · exact key s2 s2' hs2 hs2' ha2
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · have := hgen i hi (uSL c)
      rwa [rootSL2_single_eq_simple, simpleRootSL2_uSL] at this
    · have := hgen i hi (vSL c)
      rwa [rootSL2_single_eq_simple, simpleRootSL2_vSL] at this
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    calc n * (Units.map (entrywiseHom Fr) x * Units.map (entrywiseHom Fr) y) * n⁻¹
        = (n * Units.map (entrywiseHom Fr) x * n⁻¹) *
            (n * Units.map (entrywiseHom Fr) y * n⁻¹) := by
          group
      _ = _ := by rw [hx, hy]; group
  | inv x _ hx =>
    rw [map_inv]
    calc n * (Units.map (entrywiseHom Fr) x)⁻¹ * n⁻¹
        = (n * Units.map (entrywiseHom Fr) x * n⁻¹)⁻¹ := by group
      _ = _ := by rw [hx]; group

end CFSG.RankThree.PartOne.KF4
