module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem TauCeti
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma ct_tyb_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

theorem ggOrthTy_frame
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
      ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = L ∧
      (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ 3 ∣ 2 ^ f - 1 ∧ GGTableBPos 3 Bs L t n f ψ := by
  obtain ⟨t, n, f, ψ, hloc, -, htab⟩ :=
    s2jn_exists_tableBFrame G 3 B Bs x L D J 𝒦 S.cfg S.split
  exact ⟨t, n, f, ψ, hloc.1.2.2.1, hloc.1.2.2.2, hloc.2.1.1, hloc.2.1.2.1,
    hloc.2.1.2.2.1, hloc.2.1.2.2.2, htab⟩

theorem ggOrthTy_cox_psl
    {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 2 f) :
    ∃ e : Fin (n - 1) ≃ Fin (ggU .PSL n f).D.rank,
      coxeterMatrix (ggU .PSL n f).D.isFiniteType = (CoxeterMatrix.A (n - 1)).reindex e := by
  have hn2 : 2 ≤ n := by
    have h := hadm
    simp only [StatedLieAdmissible] at h
    exact h.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hM : coxeterMatrix (SpecialLinear.isFiniteType_A m) = CoxeterMatrix.A m :=
    coxeterMatrix_eq_of_ggIntCartan (SpecialLinear.isFiniteType_A m) (ggIntCartan_A m)
  refine ⟨Equiv.refl (Fin m), ?_⟩
  change coxeterMatrix (SpecialLinear.isFiniteType_A m) =
    (CoxeterMatrix.A (m + 1 - 1)).reindex (Equiv.refl (Fin m))
  rw [hM]
  exact (ct_tyb_reindex_refl (CoxeterMatrix.A m)).symm

theorem ggOrthTy_cox_D
    {n f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 2 f) :
    ∃ e : Fin n ≃ Fin (ggU .POmegaPlus n f).D.rank,
      coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType = (ggCoxeterMatrixD n).reindex e := by
  have hn4 : 4 ≤ n := by
    have h := hadm
    simp only [StatedLieAdmissible] at h
    exact h.2.2
  have hn3 : 3 ≤ n := by omega
  have hM : coxeterMatrix (Spin.isFiniteType_cartanD n) = ggCoxeterMatrixD n := by
    have hC : GGIntCartan (ggCoxeterMatrixD n) (Spin.cartanD n) := by
      rw [Spin.cartanD_eq n]
      exact ggIntCartan_D n
    exact coxeterMatrix_eq_of_ggIntCartan (Spin.isFiniteType_cartanD n) hC
  have hU : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  rw [hU]
  refine ⟨Equiv.refl (Fin n), ?_⟩
  change coxeterMatrix (Spin.isFiniteType_cartanD n) =
    (ggCoxeterMatrixD n).reindex (Equiv.refl (Fin n))
  rw [hM]
  exact (ct_tyb_reindex_refl (ggCoxeterMatrixD n)).symm

theorem ggOrthTy_cox_E
    {n f : ℕ} :
    ∃ e : Fin 6 ≃ Fin (ggU .E6 n f).D.rank,
      coxeterMatrix (ggU .E6 n f).D.isFiniteType = CoxeterMatrix.E₆.reindex e := by
  have hC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
    rw [show Tag.cartan .E6 = CartanMatrix.E 6 from cartanE_eq 6]
    exact ggIntCartan_E₆
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) =
      CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) hC
  refine ⟨Equiv.refl (Fin 6), ?_⟩
  change coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) =
    CoxeterMatrix.E₆.reindex (Equiv.refl (Fin 6))
  rw [hM]
  exact (ct_tyb_reindex_refl CoxeterMatrix.E₆).symm

theorem ggOrthTy_cox_E7
    {n f : ℕ} :
    ∃ e : Fin 7 ≃ Fin (ggU .E7 n f).D.rank,
      coxeterMatrix (ggU .E7 n f).D.isFiniteType = CoxeterMatrix.E₇.reindex e := by
  have hC : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
    rw [show Tag.cartan .E7 = CartanMatrix.E 7 from cartanE_eq 7]
    exact ggIntCartan_E₇
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) =
      CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) hC
  refine ⟨Equiv.refl (Fin 7), ?_⟩
  change coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) =
    CoxeterMatrix.E₇.reindex (Equiv.refl (Fin 7))
  rw [hM]
  exact (ct_tyb_reindex_refl CoxeterMatrix.E₇).symm

theorem ggOrthTy_cox_E8
    {n f : ℕ} :
    ∃ e : Fin 8 ≃ Fin (ggU .E8 n f).D.rank,
      coxeterMatrix (ggU .E8 n f).D.isFiniteType = CoxeterMatrix.E₈.reindex e := by
  have hC : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
    rw [show Tag.cartan .E8 = CartanMatrix.E 8 from cartanE_eq 8]
    exact ggIntCartan_E₈
  have hM : coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) hC
  refine ⟨Equiv.refl (Fin 8), ?_⟩
  change coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈.reindex (Equiv.refl (Fin 8))
  rw [hM]
  exact (ct_tyb_reindex_refl CoxeterMatrix.E₈).symm

end CFSG.StandardType.OrthF3

end
