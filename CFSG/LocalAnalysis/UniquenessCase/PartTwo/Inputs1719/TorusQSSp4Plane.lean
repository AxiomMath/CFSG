module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSL2
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Assembly.LowTwoRank
open scoped Matrix

section PlaneBlocks

open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem sp_entry {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (u v : Fin 2 ⊕ Fin 2) :
    M (Sum.inl 0) u * M (Sum.inr 0) v - M (Sum.inr 0) u * M (Sum.inl 0) v +
      (M (Sum.inl 1) u * M (Sum.inr 1) v - M (Sum.inr 1) u * M (Sum.inl 1) v) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) u v := by
  rw [← hM]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]
  ring

private theorem stab_plane_facts {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hW : ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) → M i j = 0) :
    M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) -
        M (Sum.inl 0) (Sum.inr 0) * M (Sum.inr 0) (Sum.inl 0) = 1 ∧
      ∀ j : Fin 2 ⊕ Fin 2, (j = Sum.inl 1 ∨ j = Sum.inr 1) →
        M (Sum.inl 0) j = 0 ∧ M (Sum.inr 0) j = 0 := by
  have z1 := hW (Sum.inl 1) (Sum.inl 0) (Or.inl rfl) (Or.inl rfl)
  have z2 := hW (Sum.inl 1) (Sum.inr 0) (Or.inl rfl) (Or.inr rfl)
  have z3 := hW (Sum.inr 1) (Sum.inl 0) (Or.inr rfl) (Or.inl rfl)
  have z4 := hW (Sum.inr 1) (Sum.inr 0) (Or.inr rfl) (Or.inr rfl)
  have e1 := sp_entry hM (Sum.inl 0) (Sum.inr 0)
  have hJ1 : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inr 0) = 1 := by simp
  rw [z1, z2, z3, z4, hJ1] at e1
  refine ⟨by linear_combination e1, fun j hj => ?_⟩
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) j
      (Sum.inl 0) = 0 ∧ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      j (Sum.inr 0) = 0 := by
    rcases hj with rfl | rfl <;> simp
  have e2 := sp_entry hM j (Sum.inl 0)
  have e3 := sp_entry hM j (Sum.inr 0)
  rw [z1, z3, hJ.1] at e2
  rw [z2, z4, hJ.2] at e3
  constructor
  · linear_combination (-M (Sum.inl 0) j) * e1 - M (Sum.inl 0) (Sum.inr 0) * e2 +
      M (Sum.inl 0) (Sum.inl 0) * e3
  · linear_combination (-M (Sum.inr 0) j) * e1 - M (Sum.inr 0) (Sum.inr 0) * e2 +
      M (Sum.inr 0) (Sum.inl 0) * e3

private theorem stab_plane_det1 {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hz : ∀ j : Fin 2 ⊕ Fin 2, (j = Sum.inl 1 ∨ j = Sum.inr 1) →
        M (Sum.inl 0) j = 0 ∧ M (Sum.inr 0) j = 0) :
    M (Sum.inl 1) (Sum.inl 1) * M (Sum.inr 1) (Sum.inr 1) -
        M (Sum.inl 1) (Sum.inr 1) * M (Sum.inr 1) (Sum.inl 1) = 1 := by
  have e := sp_entry hM (Sum.inl 1) (Sum.inr 1)
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 1) (Sum.inr 1) = 1 := by simp
  rw [(hz _ (Or.inl rfl)).1, (hz _ (Or.inl rfl)).2, (hz _ (Or.inr rfl)).1,
    (hz _ (Or.inr rfl)).2, hJ] at e
  linear_combination e

private def blk (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (a b : Fin 2 ⊕ Fin 2) :
    Matrix (Fin 2) (Fin 2) K :=
  !![M a a, M a b; M b a, M b b]

private theorem pairMat_mul_pairMat_blk {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hW : ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) → M i j = 0)
    (hz : ∀ j : Fin 2 ⊕ Fin 2, (j = Sum.inl 1 ∨ j = Sum.inr 1) →
        M (Sum.inl 0) j = 0 ∧ M (Sum.inr 0) j = 0) :
    pairMat (Sum.inl 0) (Sum.inr 0) (blk M (Sum.inl 0) (Sum.inr 0)) *
      pairMat (Sum.inl 1) (Sum.inr 1) (blk M (Sum.inl 1) (Sum.inr 1)) = M := by
  have w1 := hW (Sum.inl 1) (Sum.inl 0) (Or.inl rfl) (Or.inl rfl)
  have w2 := hW (Sum.inl 1) (Sum.inr 0) (Or.inl rfl) (Or.inr rfl)
  have w3 := hW (Sum.inr 1) (Sum.inl 0) (Or.inr rfl) (Or.inl rfl)
  have w4 := hW (Sum.inr 1) (Sum.inr 0) (Or.inr rfl) (Or.inr rfl)
  obtain ⟨z1, z2⟩ := hz _ (Or.inl rfl)
  obtain ⟨z3, z4⟩ := hz _ (Or.inr rfl)
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [blk, pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply, w1, w2, w3, w4, z1, z2, z3, z4]

private theorem exists_pairMat_mul_pairMat {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hW : ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) → M i j = 0) :
    ∃ A B : SL(2, K), pairMat (Sum.inl 0) (Sum.inr 0) (A : Matrix (Fin 2) (Fin 2) K) *
      pairMat (Sum.inl 1) (Sum.inr 1) (B : Matrix (Fin 2) (Fin 2) K) = M := by
  obtain ⟨hd0, hz⟩ := stab_plane_facts hM hW
  exact ⟨⟨blk M (Sum.inl 0) (Sum.inr 0), by rw [blk, Matrix.det_fin_two_of]; exact hd0⟩,
    ⟨blk M (Sum.inl 1) (Sum.inr 1), by
      rw [blk, Matrix.det_fin_two_of]; exact stab_plane_det1 hM hz⟩,
    pairMat_mul_pairMat_blk hW hz⟩

private noncomputable def phi : SL(2, K) × SL(2, K) →* StatedSp 2 K :=
  (lam 0).noncommCoprod (lam 1) (commute_lam_lam (by decide))

private theorem phi_apply (x : SL(2, K) × SL(2, K)) : phi x = lam 0 x.1 * lam 1 x.2 := rfl

private theorem phi_mk (A B : SL(2, K)) : phi (A, B) = lam 0 A * lam 1 B := rfl

private theorem phi_apply_blk (A B : SL(2, K)) (i j : Fin 2) :
    ((phi (A, B) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        (![Sum.inl 0, Sum.inr 0] i) (![Sum.inl 0, Sum.inr 0] j) = A i j ∧
      ((phi (A, B) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        (![Sum.inl 1, Sum.inr 1] i) (![Sum.inl 1, Sum.inr 1] j) = B i j := by
  rw [phi_mk, coe_mul_statedSp, coe_lam, coe_lam]
  fin_cases i <;> fin_cases j <;>
    simp [pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]

private theorem phi_injective : Function.Injective (phi (K := K)) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ h
  have hM : ((phi (A, B) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((phi (A', B') : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by rw [h]
  rw [Prod.mk.injEq]
  exact ⟨Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [← (phi_apply_blk A B i j).1, hM, (phi_apply_blk A' B' i j).1],
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [← (phi_apply_blk A B i j).2, hM, (phi_apply_blk A' B' i j).2]⟩

private theorem mem_range_phi {g : StatedSp 2 K}
    (hW : ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) → ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j = 0) :
    g ∈ (phi (K := K)).range := by
  obtain ⟨A, B, hAB⟩ := exists_pairMat_mul_pairMat (mem_statedSp_iff.1 g.2) hW
  exact ⟨(A, B), statedSp_ext (by rw [phi_mk, coe_mul_statedSp, coe_lam, coe_lam]; exact hAB)⟩

private theorem mem_normalizer_comap_phi {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) (a : Kˣ) :
    ((sl2Diag a, 1) : SL(2, K) × SL(2, K)) ∈
        Subgroup.normalizer ((H.comap phi : Subgroup _) : Set (SL(2, K) × SL(2, K))) ∧
      ((1, sl2Diag a) : SL(2, K) × SL(2, K)) ∈
        Subgroup.normalizer ((H.comap phi : Subgroup _) : Set (SL(2, K) × SL(2, K))) := by
  refine ⟨Subgroup.le_normalizer_comap _ ?_, Subgroup.le_normalizer_comap _ ?_⟩
  · rw [Subgroup.mem_comap, phi_mk, map_one, mul_one, lam_sl2Diag]
    exact hT (torusHom_mem_torus _)
  · rw [Subgroup.mem_comap, phi_mk, map_one, one_mul, lam_sl2Diag]
    exact hT (torusHom_mem_torus _)

private theorem torusElt_eq_sl2Diag (a : Kˣ) :
    CFSG.CGT.Timmesfeld75.torusElt a = sl2Diag a := by
  refine CFSG.CGT.Timmesfeld75.sl2_ext ?_ ?_ ?_ ?_ <;> simp [CFSG.CGT.Timmesfeld75.torusElt]

private theorem torus_le_normalizer_map {R : Subgroup (SL(2, K) × SL(2, K))}
    {f : SL(2, K) × SL(2, K) →* SL(2, K)}
    (hR : ∀ a : Kˣ, ∃ x ∈ Subgroup.normalizer (R : Set (SL(2, K) × SL(2, K))),
      f x = sl2Diag a) :
    CFSG.CGT.Timmesfeld75.torus K ≤
      Subgroup.normalizer ((R.map f : Subgroup SL(2, K)) : Set SL(2, K)) := by
  intro g hg
  obtain ⟨a, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_torus_iff.1 hg
  obtain ⟨x, hx, hfx⟩ := hR a
  rw [torusElt_eq_sl2Diag, ← hfx]
  exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hx)

private theorem fst_eq_one {P₁ P₂ : Type*} [Group P₁] [Group P₂] {R : Subgroup (P₁ × P₂)}
    (h : R.map (MonoidHom.fst P₁ P₂) = ⊥) {r : P₁ × P₂} (hr : r ∈ R) : r.1 = 1 := by
  have : r.1 ∈ R.map (MonoidHom.fst P₁ P₂) := ⟨r, hr, rfl⟩
  rwa [h, Subgroup.mem_bot] at this

private theorem snd_eq_one {P₁ P₂ : Type*} [Group P₁] [Group P₂] {R : Subgroup (P₁ × P₂)}
    (h : R.map (MonoidHom.snd P₁ P₂) = ⊥) {r : P₁ × P₂} (hr : r ∈ R) : r.2 = 1 := by
  have : r.2 ∈ R.map (MonoidHom.snd P₁ P₂) := ⟨r, hr, rfl⟩
  rwa [h, Subgroup.mem_bot] at this

private theorem map_phi_eq_lam_zero {R : Subgroup (SL(2, K) × SL(2, K))}
    (h1 : R.map (MonoidHom.fst _ _) = ⊤) (h2 : R.map (MonoidHom.snd _ _) = ⊥) :
    R.map phi = (lam 0 : SL(2, K) →* StatedSp 2 K).range := by
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨r.1, by rw [phi_apply, snd_eq_one h2 hr, map_one, mul_one]⟩
  · rintro _ ⟨A, rfl⟩
    have hA : A ∈ R.map (MonoidHom.fst _ _) := h1 ▸ Subgroup.mem_top A
    obtain ⟨r, hr, hrA⟩ := Subgroup.mem_map.1 hA
    refine ⟨r, hr, ?_⟩
    rw [phi_apply, snd_eq_one h2 hr, map_one, mul_one]
    exact congrArg (lam 0) hrA

private theorem map_phi_eq_lam_one {R : Subgroup (SL(2, K) × SL(2, K))}
    (h1 : R.map (MonoidHom.fst _ _) = ⊥) (h2 : R.map (MonoidHom.snd _ _) = ⊤) :
    R.map phi = (lam 1 : SL(2, K) →* StatedSp 2 K).range := by
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨r.2, by rw [phi_apply, fst_eq_one h1 hr, map_one, one_mul]⟩
  · rintro _ ⟨B, rfl⟩
    have hB : B ∈ R.map (MonoidHom.snd _ _) := h2 ▸ Subgroup.mem_top B
    obtain ⟨r, hr, hrB⟩ := Subgroup.mem_map.1 hB
    refine ⟨r, hr, ?_⟩
    rw [phi_apply, fst_eq_one h1 hr, map_one, one_mul]
    exact congrArg (lam 1) hrB

private theorem map_top_phi :
    (⊤ : Subgroup (SL(2, K) × SL(2, K))).map phi =
      (lam 0 : SL(2, K) →* StatedSp 2 K).range ⊔ (lam 1 : SL(2, K) →* StatedSp 2 K).range := by
  rw [← MonoidHom.range_eq_map, phi, MonoidHom.noncommCoprod_range]

theorem nonempty_lam_sup_equiv_prod :
    Nonempty (↥((lam 0 : SL(2, K) →* StatedSp 2 K).range ⊔
      (lam 1 : SL(2, K) →* StatedSp 2 K).range) ≃* SL(2, K) × SL(2, K)) :=
  ⟨((Subgroup.equivMapOfInjective ⊤ phi phi_injective).trans
    (MulEquiv.subgroupCongr map_top_phi)).symm.trans Subgroup.topEquiv⟩

end PlaneBlocks

section Torus

open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem map_eq_bot_or_top {R : Subgroup (SL(2, K) × SL(2, K))} (h4 : 4 ≤ Nat.card K)
    (hR : ⁅R, R⁆ = R) {f : SL(2, K) × SL(2, K) →* SL(2, K)}
    (hN : ∀ a : Kˣ, ∃ x ∈ Subgroup.normalizer (R : Set (SL(2, K) × SL(2, K))),
      f x = sl2Diag a) :
    R.map f = ⊥ ∨ R.map f = ⊤ :=
  perfect_eq_bot_or_top_of_torus h4 (by rw [← Subgroup.map_commutator, hR])
    (torus_le_normalizer_map hN)

omit [Finite K] in
private theorem sl2Diag_notMem_center {a : Kˣ} (ha : a ≠ 1) :
    sl2Diag a ∉ Subgroup.center SL(2, K) := by
  rw [CFSG.CGT.Timmesfeld75.center_sl2_eq_bot, Subgroup.mem_bot]
  intro h
  apply ha
  ext
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa using this

end Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_of_stab_plane (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H, ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j = 0) :
    H = ⊥ ∨ H = (lam (0 : Fin 2) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ∨
      H = (lam (1 : Fin 2) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ∨
      H = (lam (0 : Fin 2) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ⊔
        (lam (1 : Fin 2) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range := by
  have h4 : 4 ≤ Nat.card K := by omega
  have hHR : (H.comap phi).map phi = H := Subgroup.map_comap_eq_self fun g hg =>
    mem_range_phi (hW g hg)
  set R := H.comap (phi (K := K)) with hRdef
  have hR : ⁅R, R⁆ = R := Subgroup.map_injective phi_injective
    (by rw [Subgroup.map_commutator, hHR, hHH])
  have hN := mem_normalizer_comap_phi hT
  rw [← hRdef] at hN
  rcases map_eq_bot_or_top h4 hR (f := MonoidHom.fst _ _) (fun a => ⟨_, (hN a).1, rfl⟩) with
    h1 | h1 <;>
  rcases map_eq_bot_or_top h4 hR (f := MonoidHom.snd _ _) (fun a => ⟨_, (hN a).2, rfl⟩) with
    h2 | h2
  · have hR0 : R = ⊥ := eq_bot_iff.2 fun r hr =>
      Subgroup.mem_bot.2 (Prod.ext (fst_eq_one h1 hr) (snd_eq_one h2 hr))
    exact Or.inl (by rw [← hHR, hR0, Subgroup.map_bot])
  · exact Or.inr (Or.inr (Or.inl (hHR ▸ map_phi_eq_lam_one h1 h2)))
  · exact Or.inr (Or.inl (hHR ▸ map_phi_eq_lam_zero h1 h2))
  · right; right; right
    have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := K) h4
    have : Nontrivial Kˣ := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
      omega
    obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
    rw [← hHR, eq_top_of_fst_snd_eq_top h1 h2 (sl2Diag_notMem_center ha) (hN a).1, map_top_phi]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
