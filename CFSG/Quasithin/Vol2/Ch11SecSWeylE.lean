module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShD
public import CFSG.Quasithin.Vol2.Ch11SecSWeylB
public import CFSG.Quasithin.Vol2.Ch11SecSWeylC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {K : Type} [Field K]

@[expose] noncomputable def spW0 : StatedSp 2 K :=
  lam 0 (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * lam 1 sl2W

theorem sl2W_conj_sl2Diag (a : Kˣ) :
    (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2Diag a * sl2W⁻¹ = sl2Diag a⁻¹ := by
  rw [sl2W_mul_sl2Diag, mul_inv_cancel_right]

theorem torusHom_eq_lam (t : Fin 2 → Kˣ) :
    torusHom t = lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)) := by
  rw [lam_sl2Diag, lam_sl2Diag, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

theorem spW0_conj_torusHom (t : Fin 2 → Kˣ) :
    spW0 * torusHom t * spW0⁻¹ = (torusHom t)⁻¹ := by
  rw [spW0, torusHom_eq_lam]
  have c10 : ∀ g g' : Matrix.SpecialLinearGroup (Fin 2) K,
      lam (1 : Fin 2) g * lam (0 : Fin 2) g' = lam 0 g' * lam 1 g :=
    fun g g' => (commute_lam_lam (by decide) g g').eq
  have h0 : lam (0 : Fin 2) sl2W * lam 0 (sl2Diag (t 0)) * (lam 0 sl2W)⁻¹ =
      (lam (0 : Fin 2) (sl2Diag (t 0)))⁻¹ := by
    rw [← map_inv (lam 0) sl2W, ← map_mul, ← map_mul, sl2W_conj_sl2Diag, map_inv, map_inv]
  have h1 : lam (1 : Fin 2) sl2W * lam 1 (sl2Diag (t 1)) * (lam 1 sl2W)⁻¹ =
      (lam (1 : Fin 2) (sl2Diag (t 1)))⁻¹ := by
    rw [← map_inv (lam 1) sl2W, ← map_mul, ← map_mul, sl2W_conj_sl2Diag, map_inv, map_inv]
  have e1 : lam (1 : Fin 2) sl2W * lam 0 (sl2Diag (t 0)) = lam 0 (sl2Diag (t 0)) * lam 1 sl2W :=
    c10 _ _
  have e2 : (lam (1 : Fin 2) (sl2Diag (t 1)))⁻¹ * (lam (0 : Fin 2) sl2W)⁻¹ =
      (lam 0 sl2W)⁻¹ * (lam 1 (sl2Diag (t 1)))⁻¹ := by
    rw [← map_inv (lam 1), ← map_inv (lam 0)]
    exact c10 _ _
  have e3 : (lam (1 : Fin 2) (sl2Diag (t 1)))⁻¹ * (lam (0 : Fin 2) (sl2Diag (t 0)))⁻¹ =
      (lam 0 (sl2Diag (t 0)))⁻¹ * (lam 1 (sl2Diag (t 1)))⁻¹ := by
    rw [← map_inv (lam 1), ← map_inv (lam 0)]
    exact c10 _ _
  calc lam 0 sl2W * lam 1 sl2W * (lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1))) *
        (lam 0 sl2W * lam 1 sl2W)⁻¹
      = lam 0 sl2W * (lam 1 sl2W * lam 0 (sl2Diag (t 0))) * lam 1 (sl2Diag (t 1)) *
          (lam 1 sl2W)⁻¹ * (lam 0 sl2W)⁻¹ := by group
    _ = lam 0 sl2W * lam 0 (sl2Diag (t 0)) * (lam 1 sl2W * lam 1 (sl2Diag (t 1)) *
          (lam 1 sl2W)⁻¹) * (lam 0 sl2W)⁻¹ := by rw [e1]; group
    _ = lam 0 sl2W * lam 0 (sl2Diag (t 0)) * ((lam 1 (sl2Diag (t 1)))⁻¹ * (lam 0 sl2W)⁻¹) := by
          rw [h1]; group
    _ = lam 0 sl2W * lam 0 (sl2Diag (t 0)) * (lam 0 sl2W)⁻¹ * (lam 1 (sl2Diag (t 1)))⁻¹ := by
          rw [e2]; group
    _ = (lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)))⁻¹ := by
          rw [h0, _root_.mul_inv_rev, e3]

theorem spW0_mulVec_inr :
    ((((spW0 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) (Sum.inr 0) = 1 := by
  rw [spW0, coe_mul_statedSp, coe_lam, coe_lam]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, pairMat, Fintype.sum_sum_type,
    Fin.sum_univ_two, Pi.single_apply]

theorem spW0_not_mem_stabilizer {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ 2) :
    spW0 ∉ stabilizer 2 K (flag 2 K i) := by
  intro h
  have hW : flag 2 K i = isoFlag 2 K i := by simp [flag, hi2]
  have he : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K i := by
    rw [hW, mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h => by
      subst h
      simp at hj
      omega
    simp [hj0]
  have hm : ((((spW0 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) ∈ flag 2 K i := by
    have h' : (flag 2 K i).map (mulVecLin ((((spW0 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) = flag 2 K i := h
    rw [← h']
    exact ⟨_, he, rfl⟩
  rw [hW, mem_isoFlag] at hm
  have := hm.1 0
  rw [spW0_mulVec_inr] at this
  exact one_ne_zero this

variable [Finite K] [CharP K 2]

open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher C11P9A CFSG.QuasithinUnique.Setup.X6 in
theorem part2_sp4 {Q : Type} [Group Q] [Finite Q] (hQ : StatedClassicalModel Q .PSp 2 2 2)
    {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {B₁ B₂ : Subgroup Q}
    (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂) {E : Subgroup Q}
    (hE : Nat.card ↥E = 9) (hE₁ : E ≤ Subgroup.normalizer (B₁ : Set Q))
    (hE₂ : E ≤ Subgroup.normalizer (B₂ : Set Q)) (E₂ : Subgroup Q)
    (hle : E₂ ≤ E ⊓ sectionCentralizer B₂ (CFSG.Open.pCoreOf 2 B₂)) (hne₂ : E₂ ≠ ⊥) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B₂ : Set Q) := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q 2 2 2 hQ
  obtain ⟨L, _, _, _, φ, hL, hφ, hres, -⟩ := even_rank_two_residual_symplectic hQ hS
  have hL' : Nat.card L = 4 := by rw [hL]; norm_num
  have hL4 : ∃ s : Finset L, s.card = 4 := exists_finset_card_four (by omega)
  have hB := fun j => dInf_projStabilizer_ne_bot hL4 φ j
  have hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤ := fun X _ _ hX1 =>
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1
  have hpp := parabPair_of_residual hS hres hB
  have hS' : S = (projUnipotent 2 L).map φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hinf : (projStabilizer 2 L (flag 2 L 1)).map φ.symm.toMonoidHom ⊓
      (projStabilizer 2 L (flag 2 L 2)).map φ.symm.toMonoidHom ≤
        Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, projStabilizer_inf_eq, hS',
      ← Subgroup.map_equiv_normalizer_eq]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, card_normalizer_projUnipotent hL']
  refine part2_of_residual hS hres hB hN hpp.top_not ?_ hne h₁ h₂ hE hE₁ hE₂ E₂ hle hne₂
  intro j _ E hEM hE9 E₂ hle _
  have hTP : ∀ i : Fin 2, ((torus 2 L).map (proj 2 L)).map φ.symm.toMonoidHom ≤
      (projStabilizer 2 L (flag 2 L ((i : ℕ) + 1))).map φ.symm.toMonoidHom := by
    intro i
    refine Subgroup.map_mono (Subgroup.map_mono ((torus_le_borelSubgroup).trans ?_))
    rw [← stabilizer_inf_eq_borel]
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  have hTc : Nat.card ↥(((torus 2 L).map (proj 2 L)).map φ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective proj_injective_charTwo, torus,
      ← Nat.card_congr (MonoidHom.ofInjective torusHom_injective).toEquiv, Nat.card_fun,
      Nat.card_units, hL', Nat.card_fin]
    norm_num
  refine part2_of_inverting (not_dvd_of_borel hS.2.1 hinf hcard) (le_inf (hTP 0) (hTP 1)) hTc
    hEM hE9 ?_ (w := φ.symm (proj 2 L spW0)) ?_ ?_ E₂ (hle.trans inf_le_left)
  · fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  · rintro _ ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv (proj 2 L), ← map_mul, ← map_mul,
      spW0_conj_torusHom, map_inv, map_inv]
  · rintro ⟨y, ⟨g, hg, hgy⟩, hy⟩
    have hy' : y = proj 2 L spW0 := by
      have := congrArg φ hy
      simpa using this
    rw [hy'] at hgy
    have hgw : g = spW0 := proj_injective_charTwo hgy
    rw [hgw] at hg
    exact spW0_not_mem_stabilizer (K := L) (by omega) (by have := j.isLt; omega) hg

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
