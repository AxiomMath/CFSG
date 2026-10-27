module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSL2
import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open Matrix CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree ModNine qSubPi diagE blockHom
  coe_blockHom blockMat)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_mem_rootsOfUnity_two (hK : PiField π p f K) {B : GL (Fin 2) K}
    (hB : B ∈ glPi π 2 (p ^ f) K) :
    GeneralLinearGroup.det B ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  cases π
  · have h := hK.unitary
    have hu := (Sec4.mem_glPi_false h).mp hB
    have := congrArg Matrix.det hu
    rw [det_mul, det_transpose, show ((B : Matrix (Fin 2) (Fin 2) K).map h.bar).det =
      h.bar (B : Matrix (Fin 2) (Fin 2) K).det from (RingHom.map_det h.bar _).symm,
      det_one, h.bar_apply, ← pow_succ] at this
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact this
  · have := hK.finite
    exact Sec4.mem_rootsOfUnity_of_card (by simpa [Sec4.piCard] using hK.card) _

theorem scalar_two_mem_glPi (hK : PiField π p f K) {δ : Kˣ}
    (hδ : δ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) :
    GeneralLinearGroup.scalar (Fin 2) δ ∈ glPi π 2 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [Sec4.mem_glPi_false h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h1 := congrArg Units.val ((mem_rootsOfUnity _ _).mp hδ)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
    rw [h.bar_apply, ← pow_succ]
    exact h1
  · exact Sec4.mem_glPi_true _ _

theorem pow_three_eq_one_of_pow_nine {q : ℕ} (hq : ModThree π q) (h9 : ¬ ModNine π q)
    {δ : Kˣ} (hδ : δ ∈ rootsOfUnity (qSubPi π q) K) (hδ9 : δ ^ 9 = 1) : δ ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := Sec4.three_dvd_qSubPi hq
  have hk3 : ¬ 3 ∣ k := by
    rintro ⟨j, rfl⟩
    apply h9
    cases π
    · change q % 3 = 2 at hq
      change q + 1 = 3 * (3 * j) at hk
      change q % 9 = 8
      omega
    · change q % 3 = 1 at hq
      change q - 1 = 3 * (3 * j) at hk
      change q % 9 = 1
      omega
  have h1 : (δ ^ 3) ^ k = 1 := by
    rw [← pow_mul, ← hk]
    exact (mem_rootsOfUnity _ _).mp hδ
  have h2 : (δ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hδ9
  have hcop : Nat.gcd 3 k = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk3
  have : (δ ^ 3) ^ Nat.gcd 3 k = 1 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rwa [hcop, pow_one] at this

theorem mem_centralizer_of_mk_conj_pi (hK : PiField π p f K) {e₀ : Kˣ}
    (he3 : (e₀ : K) ^ 3 = 1) (h3 : (3 : K) ≠ 0) {g N : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hN : N ∈ slPi π 3 (p ^ f) K)
    (h : ProjGenLinGroup.mk (g * diagE e₀ * g⁻¹) * ProjGenLinGroup.mk N *
      (ProjGenLinGroup.mk (g * diagE e₀ * g⁻¹))⁻¹ = ProjGenLinGroup.mk N) :
    N * (g * diagE e₀ * g⁻¹) = (g * diagE e₀ * g⁻¹) * N := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set D := diagE e₀ with hD
  set Y := g * D * g⁻¹ with hY
  rw [← map_inv, ← map_mul, ← map_mul] at h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  set s := GeneralLinearGroup.scalar (Fin 3) u with hs
  have hsc : ∀ X : GL (Fin 3) K, X * s = s * X := fun X =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u X).eq
  have e1 : Y * N * Y⁻¹ = N * s⁻¹ := by
    calc Y * N * Y⁻¹ = Y * N * Y⁻¹ * s * s⁻¹ := by group
      _ = N * s⁻¹ := by rw [hu]
  have e2 : N⁻¹ * Y * N = s⁻¹ * Y := by
    calc N⁻¹ * Y * N = N⁻¹ * (Y * N * Y⁻¹) * Y := by group
      _ = N⁻¹ * (N * s⁻¹) * Y := by rw [e1]
      _ = s⁻¹ * Y := by group
  have e3 : N * (s⁻¹ * Y) * N⁻¹ = Y := by rw [← e2]; group
  have hNY : N * Y * N⁻¹ = s * Y := by
    calc N * Y * N⁻¹ = N * s * (s⁻¹ * Y) * N⁻¹ := by group
      _ = s * N * (s⁻¹ * Y) * N⁻¹ := by rw [hsc N]
      _ = s * (N * (s⁻¹ * Y) * N⁻¹) := by group
      _ = s * Y := by rw [e3]
  set N' := g⁻¹ * N * g with hN'
  have hN'SL : N' ∈ slPi π 3 (p ^ f) K := by
    have := Sec4.conj_mem_slPi hπ (inv_mem hg) hN
    rwa [inv_inv] at this
  have h2 : N' * D * N'⁻¹ = s * D := by
    calc N' * D * N'⁻¹ = g⁻¹ * (N * Y * N⁻¹) * g := by rw [hN', hY]; group
      _ = g⁻¹ * (s * Y) * g := by rw [hNY]
      _ = s * (g⁻¹ * Y * g) := by rw [← mul_assoc g⁻¹ s Y, hsc g⁻¹]; group
      _ = s * D := by rw [hY]; group
  have hmem : N' ∈ Sec4.centMod (slPi π 3 (p ^ f) K) D :=
    Sec4.mem_centMod_iff_scalar.mpr ⟨hN'SL, s, ⟨u, rfl⟩, h2⟩
  rw [Sec4.centMod_diagE_eq (p := p) (f := f) π he3 h3] at hmem
  have hc : N' * D = D * N' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
  calc N * Y = g * (N' * D) * g⁻¹ := by rw [hN', hY]; group
    _ = g * (D * N') * g⁻¹ := by rw [hc]
    _ = Y * N := by rw [hN', hY]; group

theorem inf_centralizer_conj_pi (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (z : GL (Fin 3) K) :
    slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * z * g⁻¹} =
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {z}).map (MulAut.conj g).toMonoidHom := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  ext M
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hM, hMc⟩
    refine ⟨g⁻¹ * M * g, ⟨?_, ?_⟩, by group⟩
    · have := Sec4.conj_mem_slPi hπ (inv_mem hg) hM
      rwa [inv_inv] at this
    · calc g⁻¹ * M * g * z = g⁻¹ * (M * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * M) * g := by rw [hMc]
        _ = z * (g⁻¹ * M * g) := by group
  · rintro ⟨M', ⟨hM', hM'c⟩, rfl⟩
    refine ⟨Sec4.conj_mem_slPi hπ hg hM', ?_⟩
    calc g * M' * g⁻¹ * (g * z * g⁻¹) = g * (M' * z) * g⁻¹ := by group
      _ = g * (z * M') * g⁻¹ := by rw [hM'c]
      _ = g * z * g⁻¹ * (g * M' * g⁻¹) := by group

theorem perfectResidual_centralizer_diagE_pi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {e₀ : Kˣ} (he₀ : e₀ ≠ 1) :
    inSubgroup perfectResidual (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e₀}) =
      (slPi π 2 (p ^ f) K).map blockHom := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [Sec4.centralizer_diagE_eq hK he₀]
  have hSp : Group.IsPerfect (slPi π 2 (p ^ f) K) :=
    (Sec11.KS11LieProof.isQuasisimple_slPi_two hK hq hq2).1
  set S := slPi π 2 (p ^ f) K with hS
  have h1 : (⊤ : Subgroup S).map S.subtype = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSc : ⁅S, S⁆ = S := by
    calc ⁅S, S⁆ = (commutator S).map S.subtype := by
          rw [commutator_def, Subgroup.map_commutator, h1]
      _ = S := by rw [hSp.commutator_eq_top, h1]
  refine Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator
    (Subgroup.map_mono (Sec4.slPi_le_glPi hπ)) ?_ ?_
  · rw [← Subgroup.map_commutator, hSc]
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    refine ⟨A * B * A⁻¹ * B⁻¹, (Sec4.mem_slPi_iff hπ).mpr ⟨?_, ?_⟩, by
      simp only [map_mul, map_inv]⟩
    · exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
    · have hdet : GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [mul_comm (GeneralLinearGroup.det A) (GeneralLinearGroup.det B)]
        group
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]

theorem perfectResidual_centralizer_conj_pi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {e₀ : Kˣ} (he₀ : e₀ ≠ 1) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    inSubgroup perfectResidual
        (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * diagE e₀ * g⁻¹}) =
      ((slPi π 2 (p ^ f) K).map blockHom).map (MulAut.conj g).toMonoidHom := by
  rw [inf_centralizer_conj_pi hK hg,
    ← CFSG.RankThree.PartTwo.map_inSubgroup_perfectResidual (MulAut.conj g),
    perfectResidual_centralizer_diagE_pi hK hq hq2 he₀]

theorem eq_one_of_mem_block_of_mk_eq_one (hK : PiField π p f K) {g N : GL (Fin 3) K}
    (hN : N ∈ ((slPi π 2 (p ^ f) K).map blockHom).map (MulAut.conj g).toMonoidHom)
    (h1 : ProjGenLinGroup.mk N = 1) : N = 1 := by
  obtain ⟨M, ⟨B, hB, rfl⟩, rfl⟩ := hN
  have hsc : g * blockHom B * g⁻¹ ∈ StatedScalars (Fin 3) K :=
    Sec4.mk_eq_one_iff_mem_statedScalars.mp h1
  have hB1 := Sec11.KS11LieProof.eq_one_of_blockHom_mem_statedScalars
    (Sec11.KS11LieProof.det_eq_one_of_mem_slPi hK hB)
    (Sec11.KS11LieProof.conj_mem_statedScalars_iff.mp hsc)
  rw [hB1, map_one, map_one]

theorem det_blockHom (B : GL (Fin 2) K) : GeneralLinearGroup.det (blockHom B) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_blockHom, Sec4.det_blockMat,
    Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, Units.val_one]
  exact inv_mul_cancel₀ (by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _)

theorem exists_mem_block_of_mk_pow_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ ModNine π (p ^ f)) {e₀ : Kˣ} (he₀ : e₀ ≠ 1) {g N : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hN : N ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * diagE e₀ * g⁻¹})
    (hN3 : ProjGenLinGroup.mk N ^ 3 = 1) :
    ∃ N'' ∈ ((slPi π 2 (p ^ f) K).map blockHom).map (MulAut.conj g).toMonoidHom,
      ProjGenLinGroup.mk N'' = ProjGenLinGroup.mk N := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [inf_centralizer_conj_pi hK hg, Sec4.centralizer_diagE_eq hK he₀] at hN
  obtain ⟨M, ⟨B, hB, rfl⟩, rfl⟩ := hN
  have hsc : blockHom (B ^ 3) ∈ StatedScalars (Fin 3) K := by
    have h1 : ProjGenLinGroup.mk ((MulAut.conj g).toMonoidHom (blockHom (B ^ 3))) = 1 := by
      rw [map_pow, map_pow, map_pow, hN3]
    exact Sec11.KS11LieProof.conj_mem_statedScalars_iff.mp
      (Sec4.mk_eq_one_iff_mem_statedScalars.mp h1)
  obtain ⟨l, hl⟩ := hsc
  have hl3 : l ^ 3 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hl
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, det_blockHom] at h1
    exact h1
  have hl00 : l = (GeneralLinearGroup.det B ^ 3)⁻¹ := by
    have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hl
    simp only [GeneralLinearGroup.coe_scalar, coe_blockHom] at h00
    apply Units.ext
    simpa [blockMat, Matrix.scalar_apply, map_pow] using h00
  have hB9 : GeneralLinearGroup.det B ^ 9 = 1 := by
    rw [hl00, inv_pow, inv_eq_one, ← pow_mul] at hl3
    exact hl3
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, GeneralLinearGroup.det B = δ := ⟨_, rfl⟩
  rw [hδ] at hB9
  have hδμ : δ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := hδ ▸ det_mem_rootsOfUnity_two hK hB
  have hδ3 := pow_three_eq_one_of_pow_nine hq h9 hδμ hB9
  obtain ⟨B'', hB''⟩ : ∃ B'' : GL (Fin 2) K, B'' = GeneralLinearGroup.scalar (Fin 2) δ * B :=
    ⟨_, rfl⟩
  have hdet'' : GeneralLinearGroup.det B'' = 1 := by
    rw [hB'', map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hδ, ← pow_succ]
    exact hδ3
  have hB''S : B'' ∈ slPi π 2 (p ^ f) K := (Sec4.mem_slPi_iff hπ).mpr
    ⟨hB'' ▸ mul_mem (scalar_two_mem_glPi hK hδμ) hB, by
      rw [← GeneralLinearGroup.val_det_apply, hdet'', Units.val_one]⟩
  have hB''m : ((B'' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (δ : K) • (B : Matrix (Fin 2) (Fin 2) K) := by
    rw [hB'', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hblock : blockHom B'' = GeneralLinearGroup.scalar (Fin 3) δ * blockHom B := by
    apply Units.ext
    rw [coe_blockHom, hdet'', inv_one, Units.val_one, hB''m]
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_blockHom, hδ]
    have hδ0 : (δ : K) ≠ 0 := δ.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, Matrix.scalar_apply, Matrix.diagonal, Matrix.mul_apply, hδ0]
  refine ⟨(MulAut.conj g).toMonoidHom (blockHom B''),
    Subgroup.mem_map_of_mem _ ⟨B'', hB''S, rfl⟩, ?_⟩
  have hconj : (MulAut.conj g).toMonoidHom (GeneralLinearGroup.scalar (Fin 3) δ) =
      GeneralLinearGroup.scalar (Fin 3) δ := by
    change g * _ * g⁻¹ = _
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar δ g).eq, mul_inv_cancel_right]
  rw [hblock, map_mul (MulAut.conj g).toMonoidHom, hconj, map_mul, ProjGenLinGroup.mk_scalar,
    one_mul]

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
