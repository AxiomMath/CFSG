module

public import CFSG.RankThree.PartOne.KE.E6FourGraph

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index charVal dualMatrix chain134 support134
  IsNegativeTransition e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (apply_eq_zero_of_conj_inv_transpose_elementary)
open CFSG.RankThree.Classical2 (invTransposeHom coe_invTransposeHom)
open scoped Matrix MatrixGroups Pointwise

theorem not_exists_conj_inv_transpose_of_elementary {M : Type*} [Field M] {n : ℕ} (hn : 3 ≤ n)
    (U : Set (GL (Fin n) M))
    (hU : ∀ i j : Fin n, i ≠ j →
      ∃ X ∈ U, (X : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j 1) :
    ¬ ∃ A : GL (Fin n) M, ∀ X ∈ U,
      (A : Matrix (Fin n) (Fin n) M) * (↑X⁻¹ : Matrix (Fin n) (Fin n) M)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = X := by
  rintro ⟨A, hA⟩
  have hcol : ∀ i j : Fin n, i ≠ j → ∀ l, l ≠ i → (A : Matrix (Fin n) (Fin n) M) l j = 0 := by
    intro i j hij l hl
    obtain ⟨X, hX, hXe⟩ := hU i j hij
    have hXinv : (↑X⁻¹ : Matrix (Fin n) (Fin n) M) = 1 - Matrix.single i j 1 := by
      rw [Matrix.coe_units_inv, hXe]
      apply Matrix.inv_eq_left_inv
      rw [sub_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne (h := hij.symm)]
      abel
    have h := hA X hX
    rw [hXinv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_single, hXe] at h
    exact apply_eq_zero_of_conj_inv_transpose_elementary A h hl
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h2 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hzero : ∀ l, (A : Matrix (Fin n) (Fin n) M) l ⟨0, by omega⟩ = 0 := by
    intro l
    by_cases hl : l = ⟨1, by omega⟩
    · subst hl
      exact hcol _ _ h1.symm _ h2
    · exact hcol _ _ h0.symm _ hl
  exact Matrix.GeneralLinearGroup.det_ne_zero A (Matrix.det_eq_zero_of_column_eq_zero _ hzero)

theorem e6_tw_graph_contra {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} [Fact p.Prime]
    (hp5 : p = 5 ∨ 7 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0)
    {b : Fin Tag.E6.rank → Lˣ} {z : Fin Tag.E6.rank → ZMod p} (hz0 : z ≠ 0)
    (hzr : (dualMatrix (ZMod p) e6F4U).mulVec z = r • z)
    (hcol : ∀ l l' : Fin Tag.E6.rank → ℤ, rootChar b l = rootChar b l' ↔ charVal z l = charVal z l')
    {v : WeylGroup Tag.E6} (hSeq : rootCharKernel b = sigmaSetE6A3 v)
    (hCent : ∀ y ∈ adjointGroup Tag.E6 L, y * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * y →
      y ∈ (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) *
        (rootSpan Tag.E6 L (sigmaSetE6A3 v) : Set (ModGL Tag.E6 L)))
    {G₃ : ModGL Tag.E6 L} (hG₃ : G₃ ∈ adjointGroup Tag.E6 L)
    (hfix : (G₃ * diagE6 L) * rootDiagUnit Tag.E6 b * (G₃ * diagE6 L)⁻¹ = rootDiagUnit Tag.E6 b)
    {k : Type} [Field k] [Algebra k L] {H : SL(4, L)}
    (hP : ∀ Y : SL(4, k), (G₃ * diagE6 L) *
      rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) *
        (G₃ * diagE6 L)⁻¹ =
      rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹)) :
    False := by
  classical
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  obtain ⟨w, hwd, hwz⟩ := e6_graph_transporter hcol hG₃ hfix
  have hkerz : rootKernel z = rootCharKernel b := by
    ext α
    have h0 := hcol α 0
    rw [rootChar_zero] at h0
    have h00 : charVal z (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [charVal]
    rw [h00] at h0
    exact and_congr_right fun _ => h0.symm
  have hv : ((v⁻¹ • ·) : (Fin Tag.E6.rank → ℤ) → _) '' rootKernel z =
      parabolicRoots Tag.E6 support134 := by
    rw [hkerz, hSeq, sigmaSetE6A3, Set.image_image]
    ext x
    simp
  have hneg := e6_graph_orientation hp5 hr hz0 hzr hv hwz
  obtain ⟨π', hπ'⟩ := hneg
  have hπ'' : ∀ i j : Fin 4, v⁻¹ • (w • permLattice e6Rho (v • chainRoot chain134 i j)) =
      chainRoot chain134 (π' j) (π' i) := by
    intro i j
    have := hπ' i j
    simpa using this
  have hroot : ∀ i j : Fin 4, w • permLattice e6Rho (sigmaRootE6A3 v i j) =
      sigmaRootE6A3 v (π' j) (π' i) := by
    intro i j
    rw [sigmaRootE6A3_eq_smul, sigmaRootE6A3_eq_smul]
    have := congrArg (fun x => v • x) (hπ'' i j)
    simpa using this
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hnwA : nw ∈ adjointGroup Tag.E6 L :=
    ((exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 L b b).2.2.2) w
  set bσ : Fin Tag.E6.rank → Lˣ := fun i => b (TwistTag.E6.perm.symm i) with hbσ
  have hQb : Q * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 bσ * Q :=
    E6_diagramMap_mul_rootDiagUnit b
  have h1 : G₃ * rootDiagUnit Tag.E6 bσ * G₃⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : rootDiagUnit Tag.E6 bσ = Q * rootDiagUnit Tag.E6 b * Q⁻¹ := by
      rw [hQb, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    simpa [mul_assoc] using hfix
  have hu : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by
    have e : nw⁻¹ * rootDiagUnit Tag.E6 b * nw = rootDiagUnit Tag.E6 bσ := by
      rw [hwd]
      group
    have : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹ = rootDiagUnit Tag.E6 b := by
      calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹
          = G₃ * (nw⁻¹ * rootDiagUnit Tag.E6 b * nw) * G₃⁻¹ := by group
        _ = rootDiagUnit Tag.E6 b := by rw [e, h1]
    calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b
        = ((G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹) * (G₃ * nw⁻¹) := by group
      _ = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by rw [this]
  obtain ⟨t₀, ht₀, q₀, hq₀, huq⟩ := hCent (G₃ * nw⁻¹) (mul_mem hG₃ (inv_mem hnwA)) hu
  set q'' : ModGL Tag.E6 L := t₀ * q₀ * t₀⁻¹ with hq''
  have hq''mem : q'' ∈ rootSpan Tag.E6 L (sigmaSetE6A3 v) := by
    have hnorm := torusGroup_le_normalizer_rootSpan (τ := Tag.E6) (L := L)
      (S := sigmaSetE6A3 v) (sigmaSetE6A3_isRoot v) ht₀
    exact (Subgroup.mem_normalizer_iff.1 hnorm q₀).1 hq₀
  have hm' : G₃ * Q = q'' * (t₀ * nw * Q) := by
    have huq' : t₀ * q₀ = G₃ * nw⁻¹ := huq
    have : G₃ = t₀ * q₀ * nw := by
      rw [huq']
      group
    rw [this, hq'']
    group
  obtain ⟨Φ'', A, hΦ'', hA⟩ := e6_graph_conj_shape (L := L) v w π'
    (fun i j => hroot i j) ht₀
  obtain ⟨Qt, hQt⟩ : ∃ Qt : SL(4, L), rhoSigmaE6A3 L v Qt = q'' := by
    have : q'' ∈ (rhoSigmaE6A3 L v).range := by
      rw [rhoSigmaE6A3_range]
      exact hq''mem
    exact this
  have hfixZ : ∀ Y : SL(4, k),
      Qt * Φ'' (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) * Qt⁻¹ =
        H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹ := by
    intro Y
    have h := hP Y
    rw [hm'] at h
    set Z : SL(4, L) := H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹ with hZ
    have e : (q'' * (t₀ * nw * Q)) * rhoSigmaE6A3 L v Z * (q'' * (t₀ * nw * Q))⁻¹ =
        q'' * ((t₀ * nw * Q) * rhoSigmaE6A3 L v Z * (t₀ * nw * Q)⁻¹) * q''⁻¹ := by group
    rw [e, hΦ'', ← hQt, ← map_inv, ← map_mul, ← map_mul] at h
    exact (rhoSigmaE6A3_injective v h)
  set Hg : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL H with hHg
  set Qg : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL Qt with hQg
  set A₁ : GL (Fin 4) L := Qg * A with hA₁def
  have hcoeinv : ∀ g : GL (Fin 4) L, ((g⁻¹ : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) =
      (g : Matrix (Fin 4) (Fin 4) L)⁻¹ := fun g => Matrix.coe_units_inv g
  have hHA : ∀ Y : SL(4, k),
      (Hg⁻¹ * A₁ * invTransposeHom Hg) *
        invTransposeHom (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y)) *
        (Hg⁻¹ * A₁ * invTransposeHom Hg)⁻¹ =
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) := by
    intro Y
    set Z : SL(4, L) := H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹ with hZ
    set Yg : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) with hYg
    have hZg : Matrix.SpecialLinearGroup.toGL Z = Hg * Yg * Hg⁻¹ := by
      rw [hZ, map_mul, map_mul, map_inv]
    have h1 := hfixZ Y
    have h2 : Matrix.SpecialLinearGroup.toGL (Φ'' Z) =
        A * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_invTransposeHom, hcoeinv]
      exact hA Z
    have e : Matrix.SpecialLinearGroup.toGL Z =
        A₁ * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A₁⁻¹ := by
      calc Matrix.SpecialLinearGroup.toGL Z
          = Matrix.SpecialLinearGroup.toGL (Qt * Φ'' Z * Qt⁻¹) := by rw [h1]
        _ = Qg * Matrix.SpecialLinearGroup.toGL (Φ'' Z) * Qg⁻¹ := by
            simp [map_mul, map_inv, hQg]
        _ = A₁ * invTransposeHom (Matrix.SpecialLinearGroup.toGL Z) * A₁⁻¹ := by
            rw [h2, hA₁def]
            group
    rw [hZg, map_mul, map_mul, map_inv] at e
    calc (Hg⁻¹ * A₁ * invTransposeHom Hg) * invTransposeHom Yg *
          (Hg⁻¹ * A₁ * invTransposeHom Hg)⁻¹
        = Hg⁻¹ * (A₁ * (invTransposeHom Hg * invTransposeHom Yg * (invTransposeHom Hg)⁻¹) *
            A₁⁻¹) * Hg := by group
      _ = Hg⁻¹ * (Hg * Yg * Hg⁻¹) * Hg := by rw [← e]
      _ = Yg := by group
  refine not_exists_conj_inv_transpose_of_elementary (M := L) (n := 4) (by norm_num)
    {X | ∃ Y : SL(4, k), X = Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y)} (fun i j hij => ?_)
    ⟨Hg⁻¹ * A₁ * invTransposeHom Hg, ?_⟩
  · refine ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (algebraMap k L)
      (Matrix.SpecialLinearGroup.transvection hij (1 : k))), ⟨_, rfl⟩, ?_⟩
    change ((Matrix.transvection i j (1 : k)).map (algebraMap k L) : Matrix (Fin 4) (Fin 4) L) =
      1 + Matrix.single i j 1
    ext a b'
    simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  · rintro X ⟨Y, rfl⟩
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) (hHA Y)
    simpa [Units.val_mul, coe_invTransposeHom, hcoeinv] using this

end CFSG.RankThree.PartOne.KE
