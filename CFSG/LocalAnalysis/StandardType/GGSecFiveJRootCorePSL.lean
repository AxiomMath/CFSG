module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTags
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.SeitzReduction.LinearPilot

private theorem jcore_pair {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m) {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    (hb : ∀ γ ∈ (SpecialLinear.rootDatum m F).roots, ∃ h ∈ ggTorus (SpecialLinear.rootDatum m F),
      ∀ z ∈ (SpecialLinear.rootDatum m F).rootGroup γ, b * ψ z * b⁻¹ = ψ (h * z * h⁻¹)) :
    ∃ d : Fin (m + 1) → Fˣ, (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
  have key : ∀ (i j : Fin (m + 1)) (hij : i ≠ j), ∃ χ : F, ∀ t : F,
      b * ψ (Matrix.SpecialLinearGroup.transvection hij t) * b⁻¹ =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ * t)) := by
    intro i j hij
    obtain ⟨h, hh, hz⟩ := hb _ (InnerDiagA.typeARoot_mem_roots F hij)
    have hN : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      have h1 : h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) :
          Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :=
        hh _ (InnerDiagA.typeARoot_mem_roots F hij)
      rwa [InnerDiagA.rootGroup_typeARoot] at h1
    obtain ⟨χ, hχ⟩ := InnerDiagA.exists_conj_transvection_eq hij hN
    have hmem : ∀ t : F, Matrix.SpecialLinearGroup.transvection hij t ∈
        SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) := fun t => by
      rw [InnerDiagA.rootGroup_typeARoot]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t
    exact ⟨χ, fun t => by rw [hz _ (hmem t), hχ]⟩
  choose! χ hχ using key
  have hne : ∀ i j : Fin (m + 1), i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (Matrix.SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = b⁻¹ * (b * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij (hker h2))
  let β : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G := (MulAut.conj b).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = b * ψ u * b⁻¹ := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  obtain ⟨d, hd⟩ := InnerDiagA.exists_diag_of_cocycle (χ := χ) hm
    (fun _ _ _ hij hjk hik => InnerDiagA.chi_cocycle ψ β hker hχ' hij hjk hik) hne
  have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
      InnerDiagA.conjSL_diagGL_transvection, hd i j hij, Units.val_inv_eq_inv_val,
      mul_right_comm (χ i j), mul_assoc _ _ ((d j : F))⁻¹, mul_inv_cancel₀ (d j).ne_zero,
      mul_one]
  exact ⟨d, LinFusion.mem_ggInducedPairs.mpr fun u => by rw [← hβ, hβψ, MonoidHom.comp_apply]⟩

private theorem jcore_levi_le {m : ℕ} {F : Type} [Field F] {I : Finset (Fin (m + 1))}
    {j l : Fin (m + 1)} (hjl : j ≠ l) (hj : j ∈ I) (hl : l ∈ I) :
    ggRootLevi (SpecialLinear.rootDatum m F) (InnerDiagA.typeARoot j l) ≤
      blockSpecialLinear (K := F) I := by
  have hneg : -InnerDiagA.typeARoot j l = InnerDiagA.typeARoot (m := m) l j := by
    funext k
    simp only [InnerDiagA.typeARoot, Pi.neg_apply, neg_sub]
  have hroot : ∀ {a c : Fin (m + 1)}, a ≠ c → a ∈ I → c ∈ I →
      SpecialLinear.rootGroup m F (InnerDiagA.typeARoot a c) ≤ blockSpecialLinear (K := F) I := by
    intro a c hac ha hc g hg
    rw [InnerDiagA.rootGroup_typeARoot hac] at hg
    obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hac g).mp hg
    exact transvection_mem_blockSpecialLinear hac ha hc t
  refine sup_le (hroot hjl hj hl) ?_
  change SpecialLinear.rootGroup m F (-InnerDiagA.typeARoot j l) ≤ _
  rw [hneg]
  exact hroot hjl.symm hl hj

theorem ggJRootCoreAt_PSL :
    GGJRootCoreAt .PSL := by
  intro G _ _ p Bs L J n f ψ y hloc hstd hy hJ
  obtain ⟨⟨-, -, -, h3⟩, ⟨hker, hrange, -, -⟩, -, -, -⟩ := hloc
  change 3 ≤ n - 1 at h3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨d, hd⟩ := jcore_pair (F := GaloisField 2 f) hm hker (hstd y hy)
  have hJ' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (Set.range fun _ : Unit => y)) := by
    rwa [Set.range_const, hrange]
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf
    (F := GaloisField 2 f) hker (d := fun _ : Unit => d) (b := fun _ => y) (fun _ => hd) hJ'
  obtain ⟨h2, -⟩ := LinSemisimple.two_le_card_of_isQuasisimple_le hJ.2.2 hi.le
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp (show 1 < (LinSemisimple.eigClass
    (fun _ : Unit => d) i).card by omega)
  refine ⟨InnerDiagA.typeARoot j l, InnerDiagA.typeARoot_mem_roots (GaloisField 2 f) hjl, ?_⟩
  rw [hi]
  exact Subgroup.map_mono (jcore_levi_le hjl hj hl)

end CFSG.StandardType
