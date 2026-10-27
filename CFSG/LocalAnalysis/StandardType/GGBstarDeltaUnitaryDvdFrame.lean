module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInn
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame

public section

namespace CFSG.StandardType

namespace TableBUD

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem diagHom_mem_primeFormUnitary {σ : Fin d → Kˣ}
    (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) :
    diagHom d σ ∈ primeFormUnitary h (idGram K d) := by
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  exact CFSG.RankThree.Classical2.diagHom_unitary h hσ

@[expose] def FrameAct (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d))
    (e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) (σ : Fin d → Kˣ) : Prop :=
  IsSemilin (frameMk h Q hQ) e (diagHom d σ) 1

variable {h} {Q : GL (Fin d) K} {hQ : Q ∈ primeFormUnitary h (idGram K d)}
  {e e' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} {σ σ' : Fin d → Kˣ}

theorem FrameAct.apply (he : FrameAct h Q hQ e σ) (u v : ↥(unitarySU 2 n K d))
    (huv : (v : GL (Fin d) K) = diagHom d σ * u * (diagHom d σ)⁻¹) :
    e (frameMk h Q hQ u) = frameMk h Q hQ v :=
  he u v (by rw [huv, map_one, MulAut.one_apply])

theorem frameAct_of (H : ∀ u v : ↥(unitarySU 2 n K d),
    (v : GL (Fin d) K) = diagHom d σ * u * (diagHom d σ)⁻¹ →
      e (frameMk h Q hQ u) = frameMk h Q hQ v) : FrameAct h Q hQ e σ :=
  fun u v huv => H u v (by rw [huv, map_one, MulAut.one_apply])

theorem FrameAct.unique (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (he : FrameAct h Q hQ e σ) (he' : FrameAct h Q hQ e' σ) : e = e' := by
  ext r
  obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ r
  set v : ↥(unitarySU 2 n K d) := ⟨diagHom d σ * u * (diagHom d σ)⁻¹, by
    have := semilin_mem h (diagHom_mem_primeFormUnitary h hσ) 1 u
    rwa [map_one, MulAut.one_apply] at this⟩
  rw [he.apply u v rfl, he'.apply u v rfl]

theorem FrameAct.smul (he : FrameAct h Q hQ e σ) (c : Kˣ) :
    FrameAct h Q hQ e (fun k => c * σ k) := by
  refine frameAct_of fun u v huv => he.apply u v ?_
  have hc : diagHom d (fun k => c * σ k) =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ := by
    apply Units.ext
    rw [Units.val_mul, coe_diagHom, coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    rfl
  have hcc := Subgroup.mem_center_iff.mp (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨c, rfl⟩)
  rw [huv, hc, _root_.mul_inv_rev]
  calc Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * u *
        ((diagHom d σ)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹)
      = Matrix.GeneralLinearGroup.scalar (Fin d) c * (diagHom d σ * u * (diagHom d σ)⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
    _ = diagHom d σ * u * (diagHom d σ)⁻¹ := by
        rw [← hcc, mul_inv_cancel_right]

theorem FrameAct.mul (he : FrameAct h Q hQ e σ) (he' : FrameAct h Q hQ e' σ')
    (hσ' : ∀ k, ((σ' k : Kˣ) : K) ^ (2 ^ n + 1) = 1) :
    FrameAct h Q hQ (e * e') (σ * σ') := by
  have h1 := IsSemilin.mul h he he' (diagHom_mem_primeFormUnitary h hσ')
  rw [map_one, MulAut.one_apply, one_mul, ← map_mul] at h1
  exact h1

theorem frameAct_one : FrameAct h Q hQ 1 1 := by
  refine frameAct_of fun u v huv => ?_
  rw [map_one, inv_one, mul_one, one_mul] at huv
  rw [MulAut.one_apply, Subtype.ext huv.symm]

theorem FrameAct.inv (he : FrameAct h Q hQ e σ) : FrameAct h Q hQ e⁻¹ σ⁻¹ := by
  refine frameAct_of fun u v huv => ?_
  have h1 := he.apply v u (by rw [huv, map_inv]; group)
  rw [← h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem FrameAct.eq_smul [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (hσ' : ∀ k, ((σ' k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (he : FrameAct h Q hQ e σ) (he' : FrameAct h Q hQ e σ') :
    ∃ c : Kˣ, ∀ k, σ' k = c * σ k := by
  have hinv := he.inv
  have hN : IsSemilin (frameMk h Q hQ) 1 (diagHom d (σ⁻¹ * σ')) 1 := by
    have h1 := hinv.mul he' hσ'
    rw [inv_mul_cancel] at h1
    exact h1
  have hNu : diagHom d (σ⁻¹ * σ') ∈ primeFormUnitary h (idGram K d) :=
    diagHom_mem_primeFormUnitary h fun k => by
      rw [Pi.mul_apply, Pi.inv_apply, Units.val_mul, mul_pow, Units.val_inv_eq_inv_val, inv_pow,
        hσ k, hσ' k, inv_one, one_mul]
  obtain ⟨c, hc⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq Q hQ hNu hN
  refine ⟨c, fun k => ?_⟩
  have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
    (g : Matrix (Fin d) (Fin d) K)) hc) k) k
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, coe_diagHom, Pi.mul_apply, Pi.inv_apply] at h1
  apply Units.ext
  rw [Units.val_mul, h1, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

section Frame

variable [Finite K] {p : ℕ}

@[expose] noncomputable def innU (n d : ℕ) (K : Type) [Field K] :
    ↥(unitarySU 2 n K d) →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
  MulAut.conj.comp (projU n d K)

theorem ker_innU_le_center (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) : (innU n d K).ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro u hu
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  have h1 : projU n d K u = 1 := hcinj (by rw [map_one]; exact hu)
  obtain ⟨c, hc⟩ := mem_scalars_of_projU_eq_one h1
  have hcc := Subgroup.mem_center_iff.mp (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨c, rfl⟩)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : GL (Fin d) K) * u = u * g
  rw [← hc, hcc]

omit [Finite K] in
theorem mem_suPairs_innU {B : GL (Fin d) K} (hB : B ∈ primeFormUnitary h (idGram K d))
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hsl : IsSemilin (projU n d K) e B 1) : (e, B) ∈ SUTorus.suPairs (innU n d K) := by
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
    fun u v huv => ?_⟩
  · have := semilin_mem h hB 1 ⟨g, hg⟩
    rwa [map_one, MulAut.one_apply] at this
  · have := semilin_mem h (Subgroup.inv_mem _ hB) 1 ⟨_, hg⟩
    simp only [map_one, MulAut.one_apply, inv_inv] at this
    rwa [show B⁻¹ * (B * g * B⁻¹) * B = g by group] at this
  · have h1 := hsl u v (by rw [huv, map_one, MulAut.one_apply])
    change e * MulAut.conj (projU n d K u) * e⁻¹ = MulAut.conj (projU n d K v)
    rw [← h1]
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]

theorem exists_frame_inndiag (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1)
    {E₀ : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hE₀ : IsElemAbelian p E₀) (hE₀D : E₀ ≤ inndiagU h (by omega))
    (hbig : p ^ (d / p + 1) < Nat.card E₀) :
    ∃ (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d)), ∀ e ∈ E₀,
      ∃ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ p = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧ FrameAct h Q hQ e σ := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  have hkerψ := ker_innU_le_center hK hd hdq
  have hlin : ∀ e ∈ E₀, ∃ B ∈ primeFormUnitary h (idGram K d), IsSemilin (projU n d K) e B 1 := by
    intro e he
    obtain ⟨B, hB, hsl⟩ := exists_isSemilin h hd hq e
    have hF : fieldFactorU h hd hq e = 1 := by
      have := hE₀D he
      rw [← ker_fieldFactorU h hd hq] at this
      exact this
    rw [hF] at hsl
    exact ⟨B, hB, hsl⟩
  have hEA : ∀ e ∈ E₀, ∃ A, (e, A) ∈ SUTorus.suPairs (innU n d K) := by
    intro e he
    obtain ⟨B, hB, hsl⟩ := hlin e he
    exact ⟨B, mem_suPairs_innU hB hsl⟩
  have hEC : E₀ ⊓ Subgroup.centralizer ((innU n d K).range : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨-, hec⟩
    rw [Subgroup.mem_bot]
    ext r
    obtain ⟨u, rfl⟩ := projU_surjective r
    apply hcinj
    have h1 := Subgroup.mem_centralizer_iff.mp hec (innU n d K u) ⟨u, rfl⟩
    have h2 : MulAut.conj (e (projU n d K u)) = e * MulAut.conj (projU n d K u) * e⁻¹ := by
      ext y
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
        MulEquiv.apply_symm_apply]
    rw [MulAut.one_apply, h2]
    change e * innU n d K u * e⁻¹ = innU n d K u
    rw [← h1, mul_inv_cancel_right]
  have hT := SUTorus.isToral_inducedMatrices h hd hdq hp hp2 hpq hkerψ hE₀ hbig hEA hEC
  have hĜ := SUTorus.isProjElem_inducedMatrices h hd hdq hp hpq hkerψ hE₀
  obtain ⟨Q, hQ, hQd⟩ := SUTorus.exists_unitary_frame h hp hp2 hpq hĜ hT
  refine ⟨Q, hQ, fun e he => ?_⟩
  obtain ⟨B, hB, hsl⟩ := hlin e he
  obtain ⟨τ, hτ⟩ := hQd B (SUTorus.mem_inducedMatrices.mpr ⟨e, he, mem_suPairs_innU hB hsl⟩) hB
  have hfr : FrameAct h Q hQ e τ := by
    have h1 := hsl.frame h Q hQ
    rw [map_one, MulAut.one_apply, hτ] at h1
    exact h1
  have hτu : diagHom d τ ∈ primeFormUnitary h (idGram K d) := by
    rw [← hτ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQ) hB) hQ
  have hτn := norm_eq_one_of_diagHom_mem h hτu
  have hpow : ∀ k, τ k ^ p = τ ⟨0, by omega⟩ ^ p := by
    have h1 := hfr.pow h hτu p
    rw [hE₀.2 e he, one_pow, semilinNorm_diagHom] at h1
    have hNu : diagHom d (fun k => ∏ l ∈ Finset.range p,
        Units.map (((1 : K ≃+* K) ^ l : K ≃+* K) : K →* K) (τ k)) ∈
        primeFormUnitary h (idGram K d) := by
      rw [← semilinNorm_diagHom]
      exact semilinNorm_mem h hτu 1 p
    obtain ⟨c, hc⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq Q hQ hNu h1
    have hent : ∀ k, τ k ^ p = c := by
      intro k
      have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
        (g : Matrix (Fin d) (Fin d) K)) hc) k) k
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, coe_diagHom, one_pow] at h2
      have hid : ∀ x : Kˣ, Units.map ((1 : K ≃+* K) : K →* K) x = x := fun x => Units.ext rfl
      simp only [hid, Finset.prod_const, Finset.card_range] at h2
      exact (Units.ext h2).symm
    intro k
    rw [hent k, hent ⟨0, by omega⟩]
  set c := (τ ⟨0, by omega⟩)⁻¹ with hc
  refine ⟨fun k => c * τ k, ?_, fun k => ?_, fun k => ?_, hfr.smul c⟩
  · show c * τ ⟨0, by omega⟩ = 1
    rw [hc]
    exact inv_mul_cancel _
  · show (c * τ k) ^ p = 1
    rw [mul_pow, hpow k, hc, inv_pow, inv_mul_cancel]
  · show ((c * τ k : Kˣ) : K) ^ (2 ^ n + 1) = 1
    rw [Units.val_mul, mul_pow, hτn k, mul_one, hc, Units.val_inv_eq_inv_val, inv_pow,
      hτn ⟨0, by omega⟩, inv_one]

end Frame

section Weights

@[expose] def frameWeights (h : UnitaryFieldData 2 n K) (Q : GL (Fin d) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K d)) (hd : 1 ≤ d) (p : ℕ)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) :
    Subgroup (Fin d → Kˣ) where
  carrier := {σ | σ ⟨0, hd⟩ = 1 ∧ (∀ k, σ k ^ p = 1) ∧
    (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧ ∃ e ∈ E, FrameAct h Q hQ e σ}
  one_mem' := ⟨rfl, fun _ => one_pow _, fun _ => by simp, 1, E.one_mem, frameAct_one⟩
  mul_mem' := by
    rintro σ σ' ⟨h0, hp, hn, e, he, hfr⟩ ⟨h0', hp', hn', e', he', hfr'⟩
    refine ⟨by rw [Pi.mul_apply, h0, h0', one_mul], fun k => ?_, fun k => ?_, e * e',
      E.mul_mem he he', hfr.mul hfr' hn'⟩
    · rw [Pi.mul_apply, mul_pow, hp, hp', one_mul]
    · rw [Pi.mul_apply, Units.val_mul, mul_pow, hn, hn', one_mul]
  inv_mem' := by
    rintro σ ⟨h0, hp, hn, e, he, hfr⟩
    refine ⟨by rw [Pi.inv_apply, h0, inv_one], fun k => ?_, fun k => ?_, e⁻¹, E.inv_mem he,
      hfr.inv⟩
    · rw [Pi.inv_apply, inv_pow, hp, inv_one]
    · rw [Pi.inv_apply, Units.val_inv_eq_inv_val, inv_pow, hn, inv_one]

variable [Finite K] {p : ℕ}

theorem card_frameWeights (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hcov : ∀ e ∈ E, ∃ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ p = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧ FrameAct h Q hQ e σ) :
    Nat.card (frameWeights h Q hQ (by omega) p E) = Nat.card E := by
  classical
  set W := frameWeights h Q hQ (by omega) p E with hW
  have hex : ∀ σ : W, ∃ e ∈ E, FrameAct h Q hQ e σ := fun σ => σ.2.2.2.2
  let F : W → E := fun σ => ⟨Classical.choose (hex σ), (Classical.choose_spec (hex σ)).1⟩
  have hF : ∀ σ : W, FrameAct h Q hQ (F σ) σ := fun σ => (Classical.choose_spec (hex σ)).2
  refine Nat.card_eq_of_bijective F ⟨fun σ σ' hσσ' => ?_, fun e => ?_⟩
  · have h1 := hF σ
    have h2 := hF σ'
    rw [hσσ'] at h1
    obtain ⟨c, hc⟩ := FrameAct.eq_smul hK hd hdq hp hpq σ'.2.2.2.1 σ.2.2.2.1 h2 h1
    have hc1 : c = 1 := by
      have := hc ⟨0, by omega⟩
      rw [σ.2.1, σ'.2.1, mul_one] at this
      exact this.symm
    apply Subtype.ext
    funext k
    rw [hc k, hc1, one_mul]
  · obtain ⟨σ, h0, hp', hn, hfr⟩ := hcov e e.2
    refine ⟨⟨σ, h0, hp', hn, e, e.2, hfr⟩, Subtype.ext ?_⟩
    exact FrameAct.unique hn (hF _) hfr

end Weights

section Fix

theorem frameMk_monoSwap_ne_one {i j : Fin d} (hij : i ≠ j) {c : Kˣ}
    (hc : c ^ (2 ^ n + 1) = 1) [Finite K] :
    frameMk h Q hQ ⟨TableBUM.monoSwap i j c, TableBUM.monoSwap_mem h hij hc⟩ ≠ 1 := by
  intro h1
  have h2 : frameMk h Q hQ 1 =
      frameMk h Q hQ ⟨TableBUM.monoSwap i j c, TableBUM.monoSwap_mem h hij hc⟩ := by
    rw [map_one, h1]
  obtain ⟨a, ha⟩ := exists_scalar_of_frameMk_eq h Q hQ h2
  apply TableBUM.monoSwap_not_mem_scalars hij c
  refine ⟨a, ?_⟩
  have ha' : TableBUM.monoSwap i j c = Matrix.GeneralLinearGroup.scalar (Fin d) a * 1 := ha
  rw [ha', mul_one]

theorem frameMk_monoSwap_sq {i j : Fin d} (hij : i ≠ j) {c : Kˣ}
    (hc : c ^ (2 ^ n + 1) = 1) [Finite K] :
    (frameMk h Q hQ ⟨TableBUM.monoSwap i j c, TableBUM.monoSwap_mem h hij hc⟩) ^ 2 = 1 := by
  have hM2 : (⟨TableBUM.monoSwap i j c, TableBUM.monoSwap_mem h hij hc⟩ :
      ↥(unitarySU 2 n K d)) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact TableBUM.monoSwap_mul_self hij c)
  rw [← map_pow, hM2, map_one]

theorem exists_two_subgroup_of_fix {R : Type} [Group R] {E : Subgroup (MulAut R)} {m : R}
    (hm1 : m ≠ 1) (hm2 : m ^ 2 = 1) (hfix : ∀ α ∈ E, α m = m) :
    ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V := by
  refine ⟨Subgroup.zpowers m, fun h1 => hm1 ?_,
    isPGroup_zpowers_of_pow Nat.prime_two (k := 1) (by rw [pow_one]; exact hm2), ?_⟩
  · have h2 := Subgroup.mem_zpowers m
    rw [h1, Subgroup.mem_bot] at h2
    exact h2
  · intro α hα v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow, hfix α hα]
    exact Subgroup.zpow_mem_zpowers m k

theorem exists_two_subgroup_of_pair [Finite K] {E : Subgroup (MulAut
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))} {k l : Fin d} (hkl : k ≠ l)
    (hact : ∀ e ∈ E, ∃ σ : Fin d → Kˣ, σ k = σ l ∧ FrameAct h Q hQ e σ) :
    ∃ V : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), V ≠ ⊥ ∧
      IsPGroup 2 V ∧ ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V := by
  have hc : (1 : Kˣ) ^ (2 ^ n + 1) = 1 := one_pow _
  refine exists_two_subgroup_of_fix (frameMk_monoSwap_ne_one (h := h) (Q := Q) (hQ := hQ) hkl hc)
    (frameMk_monoSwap_sq (h := h) (Q := Q) (hQ := hQ) hkl hc) fun e he => ?_
  obtain ⟨σ, hσ, hfr⟩ := hact e he
  refine hfr.apply _ _ ?_
  change TableBUM.monoSwap k l 1 = diagHom d σ * TableBUM.monoSwap k l 1 * (diagHom d σ)⁻¹
  rw [TableBUM.commute_monoSwap hσ, mul_inv_cancel_right]

end Fix

end TableBUD

end CFSG.StandardType
