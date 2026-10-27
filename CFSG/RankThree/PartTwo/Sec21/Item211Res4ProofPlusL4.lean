module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusProj
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofL4
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projImage)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem fromBlocks_diag_mul (a b a' b' : Matrix (Fin 2) (Fin 2) K) :
    fromBlocks a 0 0 b * fromBlocks a' 0 0 b' = fromBlocks (a * a') 0 0 (b * b') := by
  rw [fromBlocks_multiply]
  simp

theorem cubeMat_cube : cubeMat K * cubeMat K * cubeMat K = 1 := by
  have h := cubeMat_sq_add (K := K)
  calc cubeMat K * cubeMat K * cubeMat K =
      (cubeMat K * cubeMat K + cubeMat K + 1) * (cubeMat K - 1) + 1 := by noncomm_ring
    _ = 1 := by rw [h, Matrix.zero_mul, zero_add]

theorem fromBlocks_diag_pow (a b : Matrix (Fin 2) (Fin 2) K) (j : ℕ) :
    (fromBlocks a 0 0 b) ^ j = fromBlocks (a ^ j) 0 0 (b ^ j) := by
  induction j with
  | zero => simp [fromBlocks_one]
  | succ j ih => rw [pow_succ, ih, fromBlocks_diag_mul, pow_succ, pow_succ]

theorem dec_plane (hK : ∀ s : K, s * s + s + 1 ≠ 0) (h3 : (3 : K) ≠ 0) {D0 B : GL V₄ K}
    (hD0 : (D0 : Matrix V₄ V₄ K) = fromBlocks (cubeMat K) 0 0 1)
    (hB : B ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker) (hB3 : B ^ 3 = 1)
    (hBD : B * D0 = D0 * B) : ∃ (j : ℕ) (S : SL(2, K)), B = D0 ^ j * iotaPlane S := by
  have hX : (B : Matrix V₄ V₄ K) * fromBlocks (cubeMat K) 0 0 1 =
      fromBlocks (cubeMat K) 0 0 1 * (B : Matrix V₄ V₄ K) := by
    rw [← hD0, ← Units.val_mul, ← Units.val_mul, hBD]
  obtain ⟨h12, h21, h11⟩ := blocks_of_commute_diagM h3 cubeMat_sq_add hX
  set b11 := (B : Matrix V₄ V₄ K).toBlocks₁₁ with hb11
  set b22 := (B : Matrix V₄ V₄ K).toBlocks₂₂ with hb22
  have hBm : (B : Matrix V₄ V₄ K) = fromBlocks b11 0 0 b22 := by
    conv_lhs => rw [← fromBlocks_toBlocks (B : Matrix V₄ V₄ K), h12, h21]
  have hB3m : fromBlocks (b11 ^ 3) 0 0 (b22 ^ 3) = (1 : Matrix V₄ V₄ K) := by
    rw [← fromBlocks_diag_pow, ← hBm, ← Units.val_pow_eq_pow_val, hB3, Units.val_one]
  rw [← fromBlocks_one] at hB3m
  obtain ⟨e11, -, -, -⟩ := Matrix.fromBlocks_inj.mp hB3m
  set u : cubeAlg K := ⟨b11, mem_cubeAlg.mpr h11⟩ with hu
  have hu3 : u ^ 3 = 1 := Subtype.ext (by
    change b11 ^ 3 = 1
    exact e11)
  have hdetB : b11.det * b22.det = 1 := by
    have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hB)
    rw [GeneralLinearGroup.val_det_apply, hBm, det_fromBlocks_zero₂₁, Units.val_one] at h1
    exact h1
  have hpow : ∀ j : ℕ, ((D0 ^ j : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (cubeMat K ^ j) 0 0 1 := fun j => by
    rw [Units.val_pow_eq_pow_val, hD0, fromBlocks_diag_pow, one_pow]
  have key : ∀ j : ℕ, b11 = cubeMat K ^ j → ∃ (j : ℕ) (S : SL(2, K)), B = D0 ^ j * iotaPlane S := by
    intro j hj
    have hdet1 : (cubeMat K ^ j).det = 1 := by rw [Matrix.det_pow, det_cubeMat, one_pow]
    have hb22det : b22.det = 1 := by rw [hj, hdet1, one_mul] at hdetB; exact hdetB
    let S : SL(2, K) := ⟨b22, hb22det⟩
    refine ⟨j, S, Units.ext ?_⟩
    rw [Units.val_mul, hpow, coe_iotaPlane S, fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul,
      hBm, hj]
  rcases eq_of_pow_three_eq_one hK hu3 with h | h | h
  · exact key 0 (by rw [pow_zero]; exact congrArg Subtype.val h)
  · exact key 1 (by rw [pow_one]; exact congrArg Subtype.val h)
  · exact key 2 (by rw [sq]; exact congrArg Subtype.val h)

theorem fromBlocks_smulC (w a b c d : Matrix (Fin 2) (Fin 2) K) :
    fromBlocks w 0 0 w * fromBlocks a b c d = fromBlocks (w * a) (w * b) (w * c) (w * d) := by
  rw [fromBlocks_multiply]
  simp

theorem dec_cube (hK : ∀ s : K, s * s + s + 1 ≠ 0) {D0 B : GL V₄ K}
    (hD0 : (D0 : Matrix V₄ V₄ K) = fromBlocks (cubeMat K) 0 0 (cubeMat K)) (hB3 : B ^ 3 = 1)
    (hBD : B * D0 = D0 * B) : ∃ (j : ℕ) (S : SL(2, cubeAlg K)), B = D0 ^ j * iotaCube S := by
  have hX : (B : Matrix V₄ V₄ K) * fromBlocks (cubeMat K) 0 0 (cubeMat K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K) * (B : Matrix V₄ V₄ K) := by
    rw [← hD0, ← Units.val_mul, ← Units.val_mul, hBD]
  have hblk := blocks_mem_cubeAlg hX
  obtain ⟨a1, a2, a3, a4⟩ := hblk
  set Bm := (B : Matrix V₄ V₄ K) with hBm
  have hblk2 : (Bm * Bm).toBlocks₁₁ ∈ cubeAlg K ∧ (Bm * Bm).toBlocks₁₂ ∈ cubeAlg K ∧
      (Bm * Bm).toBlocks₂₁ ∈ cubeAlg K ∧ (Bm * Bm).toBlocks₂₂ ∈ cubeAlg K := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul] <;>
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (by assumption) (by assumption))
        (Subalgebra.mul_mem _ (by assumption) (by assumption))
  have hδ3 : detC Bm * detC Bm * detC Bm = 1 := by
    have h1 : detC (Bm * Bm * Bm) = detC Bm * detC Bm * detC Bm := by
      rw [detC_mul hblk2 ⟨a1, a2, a3, a4⟩, detC_mul ⟨a1, a2, a3, a4⟩ ⟨a1, a2, a3, a4⟩]
    have h2 : Bm * Bm * Bm = 1 := by
      rw [hBm, ← Units.val_mul, ← Units.val_mul, ← pow_three', hB3, Units.val_one]
    rw [← h1, h2]
    obtain ⟨o1, o2, o3, o4⟩ := toBlocks_one (K := K) (n := Fin 2)
    rw [detC, o1, o2, o3, o4, Matrix.mul_one, Matrix.zero_mul, sub_zero]
  have hδmem : detC Bm ∈ cubeAlg K :=
    Subalgebra.sub_mem _ (Subalgebra.mul_mem _ a1 a4) (Subalgebra.mul_mem _ a2 a3)
  set δ : cubeAlg K := ⟨detC Bm, hδmem⟩ with hδ
  have hδ3' : δ ^ 3 = 1 := Subtype.ext (by
    change detC Bm ^ 3 = 1
    rw [pow_three']
    exact hδ3)
  have hC3 := cubeMat_cube (K := K)
  have hpow : ∀ j : ℕ, ((D0 ^ j : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (cubeMat K ^ j) 0 0 (cubeMat K ^ j) := fun j => by
    rw [Units.val_pow_eq_pow_val, hD0, fromBlocks_diag_pow]
  have key : ∀ (j : ℕ) (w : Matrix (Fin 2) (Fin 2) K), w ∈ cubeAlg K → cubeMat K ^ j * w = 1 →
      w * w * detC Bm = 1 → ∃ (j : ℕ) (S : SL(2, cubeAlg K)), B = D0 ^ j * iotaCube S := by
    intro j w hw hjw hdet
    set S0 : Matrix (Fin 2) (Fin 2) (cubeAlg K) :=
      !![⟨w * Bm.toBlocks₁₁, Subalgebra.mul_mem _ hw a1⟩,
        ⟨w * Bm.toBlocks₁₂, Subalgebra.mul_mem _ hw a2⟩;
        ⟨w * Bm.toBlocks₂₁, Subalgebra.mul_mem _ hw a3⟩,
        ⟨w * Bm.toBlocks₂₂, Subalgebra.mul_mem _ hw a4⟩] with hS0
    have hS0det : S0.det = 1 := by
      rw [Matrix.det_fin_two]
      let wv : cubeAlg K := ⟨w, hw⟩
      let x1 : cubeAlg K := ⟨_, a1⟩
      let x2 : cubeAlg K := ⟨_, a2⟩
      let x3 : cubeAlg K := ⟨_, a3⟩
      let x4 : cubeAlg K := ⟨_, a4⟩
      have hdet' : wv * wv * (x1 * x4 - x2 * x3) = 1 := by
        apply Subtype.ext
        change w * w * (Bm.toBlocks₁₁ * Bm.toBlocks₂₂ - Bm.toBlocks₁₂ * Bm.toBlocks₂₁) = 1
        exact hdet
      calc S0 0 0 * S0 1 1 - S0 0 1 * S0 1 0 = (wv * x1) * (wv * x4) - (wv * x2) * (wv * x3) :=
            rfl
        _ = wv * wv * (x1 * x4 - x2 * x3) := by ring
        _ = 1 := hdet'
    let S : SL(2, cubeAlg K) := ⟨S0, hS0det⟩
    refine ⟨j, S, Units.ext ?_⟩
    rw [Units.val_mul, hpow, coe_iotaCube S]
    change Bm = fromBlocks (cubeMat K ^ j) 0 0 (cubeMat K ^ j) *
      fromBlocks (w * Bm.toBlocks₁₁) (w * Bm.toBlocks₁₂) (w * Bm.toBlocks₂₁) (w * Bm.toBlocks₂₂)
    rw [fromBlocks_smulC]
    simp only [← Matrix.mul_assoc, hjw, Matrix.one_mul]
    exact (fromBlocks_toBlocks Bm).symm
  have hC1 : cubeMat K * cubeMat K * cubeMat K = 1 := hC3
  rcases eq_of_pow_three_eq_one hK hδ3' with h | h | h
  ·
    have hd : detC Bm = 1 := congrArg Subtype.val h
    exact key 0 1 (Subalgebra.one_mem _) (by rw [pow_zero, Matrix.mul_one])
      (by rw [hd, Matrix.mul_one, Matrix.mul_one])
  ·
    have hd : detC Bm = cubeMat K := congrArg Subtype.val h
    exact key 2 (cubeMat K) (mem_cubeAlg.mpr rfl) (by rw [sq]; exact hC1) (by rw [hd]; exact hC1)
  ·
    have hd : detC Bm = cubeMat K * cubeMat K := congrArg Subtype.val h
    refine key 1 (cubeMat K * cubeMat K) (Subalgebra.mul_mem _ (mem_cubeAlg.mpr rfl)
      (mem_cubeAlg.mpr rfl)) (by rw [pow_one, ← Matrix.mul_assoc]; exact hC1) ?_
    rw [hd]
    calc cubeMat K * cubeMat K * (cubeMat K * cubeMat K) * (cubeMat K * cubeMat K) =
        (cubeMat K * cubeMat K * cubeMat K) * (cubeMat K * cubeMat K * cubeMat K) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hC1, Matrix.one_mul]

theorem IsCentData.comp_surjective {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {G : Subgroup (GL ι' K)}
    {A : GL ι' K} {X Y : Type*} [Group X] [Group Y] {φ : X →* GL ι' K} (h : IsCentData G A φ)
    (f : Y →* X) (hf : Function.Surjective f) : IsCentData G A (φ.comp f) := by
  obtain ⟨hmem, hcomm, hcom⟩ := h
  refine ⟨fun y => hmem (f y), fun y => hcomm (f y), fun g hg k hk hgA hkA => ?_⟩
  obtain ⟨x, hx⟩ := hcom g hg k hk hgA hkA
  obtain ⟨y, rfl⟩ := hf x
  exact ⟨y, hx⟩

theorem mem_center_iff_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    e x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center X := by
  rw [← map_center_equiv e]
  constructor
  · rintro ⟨x', hx', h⟩
    rwa [e.injective h] at hx'
  · intro h
    exact ⟨x, h, rfl⟩

theorem exists_three_mul_sq_eq_one {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) :
    ∃ c : GaloisField p 2, 3 * c ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  set F := GaloisField p 2
  have : Fintype F := Fintype.ofFinite F
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff F p 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    omega
  have hcard : Fintype.card F = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 (by norm_num)]
  have h3p : (3 : F) ^ p = 3 := by
    have e := congrArg (algebraMap (ZMod p) F) (ZMod.pow_card (3 : ZMod p))
    rwa [map_pow, map_ofNat] at e
  have h3p1 : (3 : F)⁻¹ ^ (p - 1) = 1 := by
    have e : (3 : F) ^ (p - 1) * 3 = 1 * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, h3p, one_mul]
    rw [inv_pow, mul_right_cancel₀ h3 e, inv_one]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨r, hr⟩ := hodd
  have hdiv : Fintype.card F / 2 = (p - 1) * (r + 1) := by
    rw [hcard, hr]
    have e1 : (2 * r + 1) ^ 2 = 2 * (2 * r * (r + 1)) + 1 := by ring
    rw [e1, Nat.mul_add_div (by norm_num : 0 < 2), show (1 : ℕ) / 2 = 0 from rfl, add_zero,
      show 2 * r + 1 - 1 = 2 * r by omega]
  have hsq : IsSquare (3 : F)⁻¹ := by
    rw [FiniteField.isSquare_iff hchar (inv_ne_zero h3), hdiv, pow_mul, h3p1, one_pow]
  obtain ⟨c, hc⟩ := hsq
  refine ⟨c, ?_⟩
  rw [sq, ← hc, mul_inv_cancel₀ h3]

theorem center_projSL_four_eq_bot : Subgroup.center (projSL 4 K) = ⊥ := by
  have h34 : 3 ≤ 4 ∨ ∃ s : Finset K, s.card = 4 := Or.inl (by norm_num)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 4)
    (by norm_num) h34
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 4) (by norm_num) h34
  exact Item211Lie2Proof.center_eq_bot_of_mulEquiv (Sec4.projSLEquivPSLn 4 K)
    (CFSG.RankThree.PartOne.KCUnitaryRegular.center_eq_bot_of_isSimpleGroup_of_isPerfect hperf)

@[expose] noncomputable def phiPlane (P : GL V₄ K) : SL(2, K) →* GL (Fin 4) K :=
  (reindexV₄ K : GL V₄ K →* GL (Fin 4) K).comp ((MulAut.conj P⁻¹).toMonoidHom.comp iotaPlane)

@[expose] noncomputable def phiCube (P : GL V₄ K) : SL(2, cubeAlg K) →* GL (Fin 4) K :=
  (reindexV₄ K : GL V₄ K →* GL (Fin 4) K).comp ((MulAut.conj P⁻¹).toMonoidHom.comp iotaCube)

theorem move_L4 {A B : GL (Fin 4) K} (hB : B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker)
    (hB3 : B ^ 3 = 1) (hBA : B * A = A * B) (P : GL V₄ K) :
    (P * (reindexV₄ K).symm B * P⁻¹) ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker ∧
      (P * (reindexV₄ K).symm B * P⁻¹) ^ 3 = 1 ∧
      (P * (reindexV₄ K).symm B * P⁻¹) * (P * (reindexV₄ K).symm A * P⁻¹) =
        (P * (reindexV₄ K).symm A * P⁻¹) * (P * (reindexV₄ K).symm B * P⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← mem_ker_det_conj_iff, MonoidHom.mem_ker, ← det_reindexV₄, MulEquiv.apply_symm_apply]
    exact hB
  · rw [conj_pow, ← map_pow, hB3, map_one, mul_one, mul_inv_cancel]
  · have e : (reindexV₄ K).symm B * (reindexV₄ K).symm A =
        (reindexV₄ K).symm A * (reindexV₄ K).symm B := by
      rw [← map_mul, ← map_mul, hBA]
    calc P * (reindexV₄ K).symm B * P⁻¹ * (P * (reindexV₄ K).symm A * P⁻¹) =
        P * ((reindexV₄ K).symm B * (reindexV₄ K).symm A) * P⁻¹ := by group
      _ = P * ((reindexV₄ K).symm A * (reindexV₄ K).symm B) * P⁻¹ := by rw [e]
      _ = _ := by group

theorem back_L4 {A B : GL (Fin 4) K} (P X : GL V₄ K) (j : ℕ)
    (h : P * (reindexV₄ K).symm B * P⁻¹ = (P * (reindexV₄ K).symm A * P⁻¹) ^ j * X) :
    B = A ^ j * reindexV₄ K (P⁻¹ * X * P) := by
  have e1 : (reindexV₄ K).symm B = ((reindexV₄ K).symm A) ^ j * (P⁻¹ * X * P) := by
    have e2 : (reindexV₄ K).symm B = P⁻¹ * (P * (reindexV₄ K).symm B * P⁻¹) * P := by group
    rw [e2, h, conj_pow]
    group
  have e3 := congrArg (reindexV₄ K) e1
  rw [MulEquiv.apply_symm_apply, map_mul, map_pow, MulEquiv.apply_symm_apply] at e3
  exact e3

theorem mem_ker_det_reindex_iff (g : GL V₄ K) :
    g ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker ↔
      reindexV₄ K g ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, det_reindexV₄]

theorem plane_data_L4 (hK : ∀ s : K, s * s + s + 1 ≠ 0) (h3 : (3 : K) ≠ 0)
    {A : GL (Fin 4) K} {P : GL V₄ K}
    (hD : ((P * (reindexV₄ K).symm A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (cubeMat K) 0 0 1) :
    IsCentData (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker A (phiPlane P) ∧
      (ProjGenLinGroup.mk.comp (phiPlane P)).ker = ⊥ ∧
      ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker, B ^ 3 = 1 → B * A = A * B →
        ∃ (j : ℕ) (S : SL(2, K)), B = A ^ j * phiPlane P S := by
  have hφ := isCentData_map_equiv (reindexV₄ K) mem_ker_det_reindex_iff
    ((isCentData_det_plane h3 det_cubeMat cubeMat_sq_add hD).conj (mem_ker_det_conj_iff P) rfl)
  rw [MulEquiv.apply_symm_apply] at hφ
  refine ⟨hφ, ?_, fun B hB hB3 hBA => ?_⟩
  · rw [phiPlane, ker_mk_reindexV₄, ker_mk_conj, ker_mk_iotaPlane]
  · obtain ⟨hk, h3', hc⟩ := move_L4 hB hB3 hBA P
    obtain ⟨j, S, hjS⟩ := dec_plane hK h3 hD hk h3' hc
    exact ⟨j, S, back_L4 P _ j hjS⟩

theorem cube_data_L4 (hK : ∀ s : K, s * s + s + 1 ≠ 0)
    [Group.IsPerfect (SpecialLinearGroup (Fin 2) (cubeAlg K))] {A : GL (Fin 4) K}
    {P : GL V₄ K}
    (hD : ((P * (reindexV₄ K).symm A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K)) :
    IsCentData (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker A (phiCube P) ∧
      (ProjGenLinGroup.mk.comp (phiCube P)).ker = Subgroup.center SL(2, cubeAlg K) ∧
      ∀ B ∈ (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker, B ^ 3 = 1 → B * A = A * B →
        ∃ (j : ℕ) (S : SL(2, cubeAlg K)), B = A ^ j * phiCube P S := by
  have hφ := isCentData_map_equiv (reindexV₄ K) mem_ker_det_reindex_iff
    ((isCentData_det_cube hD).conj (mem_ker_det_conj_iff P) rfl)
  rw [MulEquiv.apply_symm_apply] at hφ
  refine ⟨hφ, ?_, fun B hB hB3 hBA => ?_⟩
  · rw [phiCube, ker_mk_reindexV₄, ker_mk_conj, ker_mk_iotaCube hK]
  · obtain ⟨-, h3', hc⟩ := move_L4 hB hB3 hBA P
    obtain ⟨j, S, hjS⟩ := dec_cube hK hD h3' hc
    exact ⟨j, S, back_L4 P _ j hjS⟩

theorem data_L4 [Finite K] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hp2 : p % 3 = 2)
    (hKc : Nat.card K = p) (A : (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker)
    (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    SL2Datum (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker (A : GL (Fin 4) K) ∨
      PSL2Datum (GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker (A : GL (Fin 4) K) := by
  have hp' : p.Prime := Fact.out
  have hq : Nat.card K % 3 = 2 := by rw [hKc]; exact hp2
  have hK : ∀ s : K, s * s + s + 1 ≠ 0 := no_root_of_card_mod_three hq
  have h3 : (3 : K) ≠ 0 := by
    have h := hK 1
    norm_num at h
    exact h
  have hA'3 : (reindexV₄ K).symm (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hA3, Subgroup.coe_one, map_one]
  have hA'1 : (reindexV₄ K).symm (A : GL (Fin 4) K) ≠ 1 := fun h => hA1 (Subtype.ext (by
    have e := congrArg (reindexV₄ K) h
    rwa [MulEquiv.apply_symm_apply, map_one] at e))
  obtain ⟨P, hD | hD⟩ := exists_normal_form_GL4 hK hq hA'3 hA'1
  · left
    obtain ⟨hφ, hker, hdec⟩ := plane_data_L4 hK h3 hD
    exact ⟨K, inferInstance, inferInstance, p, hp', by omega, hKc, _, hφ, hker, hdec⟩
  · right
    have hcard2 : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
    obtain ⟨ψ⟩ := nonempty_ringEquiv_cubeAlg hK (GaloisField p 2) (by rw [hcard2, hKc])
    let e2 := CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2) ψ
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (GaloisField p 2)) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by
        rw [hcard2]
        have := Nat.pow_le_pow_left (show 2 ≤ p by omega) 2
        omega)
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (cubeAlg K)) :=
      Group.IsPerfect.ofSurjective (f := e2.symm.toMonoidHom) e2.symm.surjective
    have hF4 : 4 ≤ Nat.card (GaloisField p 2) := by
      rw [hcard2]
      have := Nat.pow_le_pow_left (show 2 ≤ p by omega) 2
      omega
    have h2F : (2 : GaloisField p 2) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff (GaloisField p 2) p 2).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h3F : (3 : GaloisField p 2) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff (GaloisField p 2) p 3).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    refine ⟨GaloisField p 2, inferInstance, inferInstance, hF4, h2F, h3F,
      exists_three_mul_sq_eq_one hp3, ?_⟩
    obtain ⟨hφ0, hker0, hdec0⟩ := cube_data_L4 hK hD
    have hφ := IsCentData.comp_surjective hφ0 e2.symm.toMonoidHom e2.symm.surjective
    refine ⟨_, hφ, ?_, fun B hB hB3 hBA => ?_⟩
    · ext s
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, ← MonoidHom.comp_apply,
        ← MonoidHom.mem_ker, hker0]
      exact mem_center_iff_of_mulEquiv e2.symm s
    · obtain ⟨j, S, hjS⟩ := hdec0 B hB hB3 hBA
      refine ⟨j, e2 S, ?_⟩
      rw [hjS]
      change _ = _ * phiCube P (e2.symm (e2 S))
      rw [MulEquiv.symm_apply_apply]

end Item211Res4Proof

open Item211Res4Proof Item228Census5Proof

theorem ks211ExcPlusL4_holds : KS211ExcPlusL4 := by
  intro p _ hp3 hp2
  have hKc : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  exact excPlusFor_projImage _ center_projSL_four_eq_bot
    (fun u hu => pow_four_eq_one_of_scalar_mem_ker hu)
    (fun A hA3 hA1 => data_L4 hp3 hp2 hKc A hA3 hA1)

end CFSG.RankThree.PartTwo.Sec21
