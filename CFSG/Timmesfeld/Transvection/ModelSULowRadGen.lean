module

public import CFSG.Timmesfeld.Transvection.ModelSULowBlock
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LinearAlgebra CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.BorelTits

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

variable (F m) in
private def lowVec (u : Fin (m / 2) → F) : Fin m → F :=
  ∑ a, u a • (Pi.single (lowIdx a) 1 : Fin m → F)

private theorem lowVec_mem (u : Fin (m / 2) → F) : lowVec F m u ∈ lowSpan F m :=
  (lowSpan F m).sum_mem fun a _ =>
    (lowSpan F m).smul_mem _ (single_lowIdx_mem_lowSpan a)

private theorem lowVec_apply_lowIdx (u : Fin (m / 2) → F) (a : Fin (m / 2)) :
    lowVec F m u (lowIdx a) = u a := by
  simp only [lowVec, Fintype.sum_apply]
  refine (Finset.sum_eq_single a ?_ ?_).trans ?_
  · intro b _ hba
    rw [Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    exact hba (Fin.ext (by
      have := congrArg Fin.val h
      simpa [val_lowIdx] using this.symm))
  · intro ha
    exact absurd (Finset.mem_univ a) ha
  · rw [Pi.smul_apply, Pi.single_apply, if_pos rfl, smul_eq_mul, mul_one]

private theorem lowVec_ne_zero {u : Fin (m / 2) → F} (hu : u ≠ 0) : lowVec F m u ≠ 0 := by
  intro h
  apply hu
  funext a
  have h0 := lowVec_apply_lowIdx (F := F) (m := m) u a
  rw [h] at h0
  exact h0.symm

private theorem exists_mem_lowRad_lowBlock_eq_of_forall_le [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)}
    (hL : ∀ (v : Fin m → F) (T : Subgroup (SU σ m)), v ∈ lowSpan F m → v ≠ 0 →
      IsUTransGroup σ v T → T ≤ L)
    {M : Matrix (Fin (m / 2)) (Fin (m / 2)) F} (hM : M + conjTr σ M = 0) :
    ∃ w : SU σ m, w ∈ lowRad σ m ∧ w ∈ L ∧ lowBlock σ m w = M := by
  classical
  let S : AddSubmonoid (Matrix (Fin (m / 2)) (Fin (m / 2)) F) :=
    { carrier := {N | ∃ w : SU σ m, w ∈ lowRad σ m ∧ w ∈ L ∧ lowBlock σ m w = N}
      zero_mem' := ⟨1, one_mem _, one_mem _, lowBlock_one⟩
      add_mem' := by
        rintro N N' ⟨w, hw, hwL, rfl⟩ ⟨w', hw', hw'L, rfl⟩
        exact ⟨w * w', mul_mem hw hw', L.mul_mem hwL hw'L,
          by rw [lowBlock_mul hw hw']⟩ }
  let Gen : Set (Matrix (Fin (m / 2)) (Fin (m / 2)) F) :=
    {N | ∃ (c : F) (u : Fin (m / 2) → F), σ c = c ∧
      N = c • vecMulVec u (fun i => σ (u i))}
  have hgen : Gen ⊆ S := by
    rintro M ⟨c, u, hc, rfl⟩
    by_cases hu : u = 0
    · subst u
      simpa using S.zero_mem
    · let v : Fin m → F := lowVec F m u
      have hv : v ∈ lowSpan F m := lowVec_mem u
      have hv0 : v ≠ 0 := lowVec_ne_zero hu
      have hvv : uForm σ v v = 0 := uForm_eq_zero_of_mem_lowSpan hv hv
      obtain ⟨T, hT⟩ := exists_isUTransGroup hσ hvv
      have htc : c + σ c = 0 := by rw [hc, CharTwo.add_self_eq_zero]
      obtain ⟨t, ht⟩ := hT.2 c htc
      have htT : t ∈ T := (hT.1 t).2 ⟨c, htc, ht⟩
      refine ⟨t, le_lowRad_of_isUTransGroup hv hT htT, hL v T hv hv0 hT htT, ?_⟩
      have h1 : (fun a : Fin (m / 2) => v (lowIdx a)) = u :=
        funext (lowVec_apply_lowIdx u)
      have h2 : (fun a : Fin (m / 2) => σ (v (lowIdx a))) = (fun i => σ (u i)) := by
        funext a
        exact congrArg σ (lowVec_apply_lowIdx u a)
      rw [lowBlock_of_suMat_eq_uTrans ht, h1, h2]
  have hclosure : AddSubmonoid.closure Gen ≤ S := by
    rw [AddSubmonoid.closure_le]
    exact hgen
  exact hclosure (by simpa only [Gen] using mem_closure_smul_vecMulVec (σ := σ) hσ hM)

theorem exists_mem_lowRad_lowBlock_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {M : Matrix (Fin (m / 2)) (Fin (m / 2)) F} (hM : M + conjTr σ M = 0) :
    ∃ w ∈ lowRad σ m, lowBlock σ m w = M := by
  obtain ⟨w, hw, -, hB⟩ :=
    exists_mem_lowRad_lowBlock_eq_of_forall_le (F := F) (m := m) hσ (L := ⊤)
      (fun _ _ _ _ _ => le_top) hM
  exact ⟨w, hw, hB⟩

theorem lowRad_le_of_forall [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)}
    (hL : ∀ (v : Fin m → F) (T : Subgroup (SU σ m)), v ∈ lowSpan F m → v ≠ 0 →
      IsUTransGroup σ v T → T ≤ L) : lowRad σ m ≤ L := by
  intro u hu
  obtain ⟨w, hw, hwL, hB⟩ :=
    exists_mem_lowRad_lowBlock_eq_of_forall_le (F := F) (m := m) hσ hL
      (M := lowBlock σ m u) (lowBlock_add_conjTr hu)
  rw [eq_of_lowBlock_eq hw hu hB] at hwL
  exact hwL

private theorem lowBlock_bijective_lowRad [CharP F 2] (hσ : ∀ c, σ (σ c) = c) :
    Function.Bijective (fun w : ↥(lowRad σ m) =>
      (⟨lowBlock σ m (w : SU σ m), lowBlock_add_conjTr w.2⟩ :
        {C : Matrix (Fin (m / 2)) (Fin (m / 2)) F // C + conjTr σ C = 0})) := by
  constructor
  · rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    exact Subtype.ext (eq_of_lowBlock_eq hw hw' (congrArg Subtype.val h))
  · rintro ⟨M, hM⟩
    obtain ⟨w, hw, hB⟩ := exists_mem_lowRad_lowBlock_eq (σ := σ) hσ hM
    exact ⟨⟨w, hw⟩, Subtype.ext hB⟩

theorem natCard_lowRad {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (m : ℕ) :
    Nat.card ↥(lowRad (unitaryInvolution F 2 f) m) = (2 ^ f) ^ ((m / 2) ^ 2) := by
  have hcard : Nat.card F = 2 ^ (2 * f) := by
    rw [hF, ← pow_mul, Nat.mul_comm f 2]
  let h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, hcard⟩
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have hbij := lowBlock_bijective_lowRad (σ := unitaryInvolution F 2 f) (m := m) hσ
  have hbar : h.bar = (unitaryInvolution F 2 f : F →+* F) := by
    ext c
    change h.bar c = unitaryInvolution F 2 f c
    rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hcount := card_add_conjTranspose_eq (p := 2) (f := f) h (r := m / 2) (M := 0) (by simp)
  rw [hbar] at hcount
  rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
  simpa [conjTr, pow_two] using hcount

end ModelRank

end CFSG.Timmesfeld.Transvection
