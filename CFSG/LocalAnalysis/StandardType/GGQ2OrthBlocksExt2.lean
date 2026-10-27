module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksQuasi
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksMark
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFrameDimensions
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)
open CFSG.ClassicalGroups.Symplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)

theorem extSupport_liftV (e : PlaneRaw.V t) :
    PlaneRaw.Code.extSupport (liftV t δ e) =
      (PlaneRaw.Code.extSupport e).map (Fin.castAddEmb δ.val) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [PlaneRaw.mem_extSupport, Finset.mem_map]
    have hlift : liftV t δ e (Fin.castAdd δ.val j) = e j := by
      simp [liftV, Fin.append_left]
    rw [hlift]
    rw [show (∃ k, k ∈ PlaneRaw.Code.extSupport e ∧
        Fin.castAddEmb δ.val k = Fin.castAdd δ.val j) ↔
        (∃ k, e k ≠ 0 ∧ Fin.castAddEmb δ.val k = Fin.castAdd δ.val j) by
      simp [PlaneRaw.mem_extSupport]]
    constructor
    · intro h
      exact ⟨j, h, rfl⟩
    · rintro ⟨k, hk, hkj⟩
      have hjk : k = j := Fin.castAdd_inj.mp hkj
      simpa [hjk] using hk
  · rw [PlaneRaw.mem_extSupport, Finset.mem_map]
    have hlift : liftV t δ e (Fin.natAdd t j) = 0 := by
      simp [liftV, Fin.append_right]
    rw [hlift]
    simp only [ne_eq, not_true_eq_false, false_iff]
    rintro ⟨k, -, hkj⟩
    have hkk : (Fin.castAddEmb δ.val k).val = k.val := rfl
    have hval := congrArg Fin.val hkj
    rw [hkk, Fin.val_natAdd] at hval
    omega

theorem card_extSupport_liftV (e : PlaneRaw.V t) :
    (PlaneRaw.Code.extSupport (liftV t δ e)).card = (PlaneRaw.Code.extSupport e).card := by
  rw [extSupport_liftV, Finset.card_map]

theorem lt_of_mem_extSupport_liftV {e : PlaneRaw.V t} {i : Fin (t + δ.val)}
    (hi : i ∈ PlaneRaw.Code.extSupport (liftV t δ e)) : (i : ℕ) < t := by
  rw [extSupport_liftV] at hi
  obtain ⟨j, -, hji⟩ := Finset.mem_map.mp hi
  subst i
  simp [Fin.val_castAdd]

omit [Finite K] [CharP K 2] in
theorem planeIdem_mulVec_self {m : ℕ} {S : Finset (Fin m)} {w : Fin m ⊕ Fin m → K}
    (h : SpBlocks.planeIdem m S *ᵥ w = w) {i : Fin m} (hi : i ∉ S) :
    w (Sum.inl i) = 0 ∧ w (Sum.inr i) = 0 := by
  have hdiag : (SpBlocks.planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.diagonal (fun x => if (Sum.elim id id x) ∈ S then (1 : K) else 0) := rfl
  constructor
  · have h' := congrFun h (Sum.inl i)
    rw [hdiag, Matrix.mulVec_diagonal] at h'
    simp [hi] at h'
    exact h'.symm
  · have h' := congrFun h (Sum.inr i)
    rw [hdiag, Matrix.mulVec_diagonal] at h'
    simp [hi] at h'
    exact h'.symm

noncomputable def zetaMat (k : ZMod 3) : Matrix (Fin 2) (Fin 2) K :=
  ((ζ (Multiplicative.ofAdd k) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

theorem entries_of_sq_add_self (hK : Nat.card K = 2)
    {M : Matrix (Fin 2) (Fin 2) K} (h : M * M + M = 1) :
    M 0 1 = 1 ∧ M 1 0 = 1 ∧ M 0 0 + M 1 1 = 1 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 0 = 1 := by
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 + M 0 1 = 0 := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 + M 1 0 = 0 := by
    have := congrFun (congrFun h 1) 0
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 1 = 1 := by
    have := congrFun (congrFun h 1) 1
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have hb : M 0 1 = 1 := by
    rcases SpBlocks.eq_zero_or_eq_one hK (M 0 1) with hb | hb
    · exfalso
      rw [hb, zero_mul, add_zero] at h00
      rcases SpBlocks.eq_zero_or_eq_one hK (M 0 0) with ha | ha
      · rw [ha, mul_zero, zero_add] at h00
        exact zero_ne_one h00
      · rw [ha, mul_one] at h00
        simp [CharTwo.add_self_eq_zero] at h00
    · exact hb
  have hc : M 1 0 = 1 := by
    rcases SpBlocks.eq_zero_or_eq_one hK (M 1 0) with hc | hc
    · exfalso
      rw [hc, zero_mul, zero_add] at h11
      rcases SpBlocks.eq_zero_or_eq_one hK (M 1 1) with hd | hd
      · rw [hd, mul_zero, zero_add] at h11
        exact zero_ne_one h11
      · rw [hd, mul_one] at h11
        simp [CharTwo.add_self_eq_zero] at h11
    · exact hc
  refine ⟨hb, hc, ?_⟩
  have h01' : M 0 0 + M 1 1 + 1 = 0 := by
    simpa [hb, mul_one, one_mul] using h01
  have hsum := congrArg (fun z : K => z + 1) h01'
  simpa [add_assoc, CharTwo.add_self_eq_zero] using hsum

theorem plane_tau_form (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {k : ZMod 3} (hk : k ≠ 0) (x y : K) :
    x * (zetaMat ζ k 1 0 * x + zetaMat ζ k 1 1 * y) -
        y * (zetaMat ζ k 0 0 * x + zetaMat ζ k 0 1 * y) =
      x * y + (x ^ 2 + y ^ 2) := by
  have h : zetaMat ζ k * zetaMat ζ k + zetaMat ζ k = 1 := by
    rw [zetaMat]
    have := SpBlocks.zeta_mul_self_add hK hζ k
    rwa [if_neg hk] at this
  obtain ⟨h01, h10, hsum⟩ := entries_of_sq_add_self hK h
  have h00 : zetaMat ζ k 0 0 = 1 + zetaMat ζ k 1 1 := by
    calc zetaMat ζ k 0 0
        = zetaMat ζ k 0 0 + (zetaMat ζ k 1 1 + zetaMat ζ k 1 1) := by
            rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (zetaMat ζ k 0 0 + zetaMat ζ k 1 1) + zetaMat ζ k 1 1 := by abel
      _ = 1 + zetaMat ζ k 1 1 := by rw [hsum]
  rw [h01, h10, h00]
  rcases SpBlocks.eq_zero_or_eq_one hK (zetaMat ζ k 1 1) with hd | hd
  · rw [hd, add_zero]
    simp only [one_mul, sub_eq_add_neg, CharTwo.neg_eq]
    ring
  · rw [hd]
    have h0 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [h0, zero_mul, zero_add, sub_eq_add_neg, CharTwo.neg_eq]
    ring

omit [Finite K] [CharP K 2] in
theorem planeMat_mulVec_inl (M : Fin (t + δ.val) → Matrix (Fin 2) (Fin 2) K)
    (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (j : Fin (t + δ.val)) :
    (WitSpNs.planeMat M *ᵥ w) (Sum.inl j) =
      M j 0 0 * w (Sum.inl j) + M j 0 1 * w (Sum.inr j) := by
  have h := CFSG.StandardType.QTwoSymplecticCav.planeMat_mulVec_coord
    (P := M) (v := w) (i := j) (a := 0)
  simpa [WitSpNs.coord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

omit [Finite K] [CharP K 2] in
theorem planeMat_mulVec_inr (M : Fin (t + δ.val) → Matrix (Fin 2) (Fin 2) K)
    (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (j : Fin (t + δ.val)) :
    (WitSpNs.planeMat M *ᵥ w) (Sum.inr j) =
      M j 1 0 * w (Sum.inl j) + M j 1 1 * w (Sum.inr j) := by
  have h := CFSG.StandardType.QTwoSymplecticCav.planeMat_mulVec_coord
    (P := M) (v := w) (i := j) (a := 1)
  simpa [WitSpNs.coord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

omit [Finite K] [CharP K 2] in
theorem tau_mulVec_inl (e : PlaneRaw.V (t + δ.val))
    (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (j : Fin (t + δ.val)) :
    ((((SpBlocks.tau ζ (t + δ.val) e : ↥(StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) (Sum.inl j) =
      zetaMat ζ (e j) 0 0 * w (Sum.inl j) + zetaMat ζ (e j) 0 1 * w (Sum.inr j) := by
  rw [SpBlocks.coe_tau]
  exact planeMat_mulVec_inl (t := t) (δ := δ)
    (fun i => zetaMat ζ (e i)) w j

omit [Finite K] [CharP K 2] in
theorem tau_mulVec_inr (e : PlaneRaw.V (t + δ.val))
    (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) (j : Fin (t + δ.val)) :
    ((((SpBlocks.tau ζ (t + δ.val) e : ↥(StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) (Sum.inr j) =
      zetaMat ζ (e j) 1 0 * w (Sum.inl j) + zetaMat ζ (e j) 1 1 * w (Sum.inr j) := by
  rw [SpBlocks.coe_tau]
  exact planeMat_mulVec_inr (t := t) (δ := δ)
    (fun i => zetaMat ζ (e i)) w j

omit [Finite K] [CharP K 2] in
theorem spForm_eq_sum_plane (w z : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    spForm (t + δ.val) K w z =
      ∑ j, (w (Sum.inl j) * z (Sum.inr j) - w (Sum.inr j) * z (Sum.inl j)) := by
  rw [spForm_apply]
  trans ∑ j, (w (Sum.inl j) * (spJ (t + δ.val) K *ᵥ z) (Sum.inl j) +
      w (Sum.inr j) * (spJ (t + δ.val) K *ᵥ z) (Sum.inr j))
  · rw [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [spJ_mulVec_inl, spJ_mulVec_inr]
    ring

theorem planeQ_eq_spForm_tau_of_support (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (e : PlaneRaw.V t)
    {w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K}
    (hw : ∀ i, i ∉ PlaneRaw.Code.extSupport (liftV t δ e) →
      w (Sum.inl i) = 0 ∧ w (Sum.inr i) = 0) :
    planeQ t δ w =
      spForm (t + δ.val) K w
        ((((SpBlocks.tau ζ (t + δ.val) (liftV t δ e) : ↥(StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) := by
  rw [planeQ, spForm_eq_sum_plane]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm : w (Sum.inl j) * w (Sum.inr j) +
        (if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) =
      w (Sum.inl j) *
          ((((SpBlocks.tau ζ (t + δ.val) (liftV t δ e) :
            ↥(StatedSp (t + δ.val) K)) :
            GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) (Sum.inr j) -
        w (Sum.inr j) *
          ((((SpBlocks.tau ζ (t + δ.val) (liftV t δ e) :
            ↥(StatedSp (t + δ.val) K)) :
            GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) (Sum.inl j) := by
    by_cases hj : j ∈ PlaneRaw.Code.extSupport (liftV t δ e)
    · have hjt : (j : ℕ) < t := lt_of_mem_extSupport_liftV t δ hj
      have hej : liftV t δ e j ≠ 0 := (PlaneRaw.mem_extSupport _ _).mp hj
      rw [if_pos hjt, tau_mulVec_inl, tau_mulVec_inr]
      exact (plane_tau_form (ζ := ζ) hK hζ hej _ _).symm
    · have h0 := hw j hj
      rw [h0.1, h0.2]
      simp
  exact hterm

theorem blockGroup_extension_map_le_orth (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (e : PlaneRaw.V t) :
    (SpBlocks.blockGroup ζ (t + δ.val) (.extension (liftV t δ e))).map
        (StatedSp (t + δ.val) K).subtype ≤
      LargeEvenOrthGroup (planeQ (K := K) t δ) := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
  have hblevi : b ∈ SpBlocks.levi (K := K) (t + δ.val)
      (PlaneRaw.Code.extSupport (liftV t δ e)) := hb.1
  have hbcent : b ∈ Subgroup.centralizer
      ({SpBlocks.tau ζ (t + δ.val) (liftV t δ e)} : Set ↥(StatedSp (t + δ.val) K)) := hb.2
  have hbcomm : b * SpBlocks.tau ζ (t + δ.val) (liftV t δ e) =
      SpBlocks.tau ζ (t + δ.val) (liftV t δ e) * b :=
    Subgroup.mem_centralizer_singleton_iff.mp hbcent
  change ((b : ↥(StatedSp (t + δ.val) K)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
    CFSG.PGLModel.orthogonalGroup (planeQ (K := K) t δ)
  rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
  intro v
  let S : Finset (Fin (t + δ.val)) := PlaneRaw.Code.extSupport (liftV t δ e)
  let P : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K := SpBlocks.planeIdem (t + δ.val) S
  let A : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
    ((b : ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
  let T : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
    ((SpBlocks.tau ζ (t + δ.val) (liftV t δ e) : ↥(StatedSp (t + δ.val) K)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
  let av : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K := P *ᵥ v
  let bv : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K := (1 - P) *ᵥ v
  have hPP : P * P = P := SpBlocks.isIdempotentElem_planeIdem (t + δ.val) S
  have hfixA : A * (1 - P) = 1 - P := hblevi
  have hPcomm : A * P = P * A := SpBlocks.commute_planeIdem_of_mem_levi hblevi
  have hcommAT : A * T = T * A := SpBlocks.coe_mul_comm_of_mul_comm hbcomm
  have hsumP : P + (1 - P) = 1 := by abel
  have havbv : av + bv = v := by
    change P *ᵥ v + (1 - P) *ᵥ v = v
    rw [← Matrix.add_mulVec, hsumP, Matrix.one_mulVec]
  have havP : P *ᵥ av = av := by
    change P *ᵥ (P *ᵥ v) = P *ᵥ v
    rw [Matrix.mulVec_mulVec, hPP]
  have hgbv : A *ᵥ bv = bv := by
    change A *ᵥ ((1 - P) *ᵥ v) = (1 - P) *ᵥ v
    rw [Matrix.mulVec_mulVec, hfixA]
  have hPgav : P *ᵥ (A *ᵥ av) = A *ᵥ av := by
    calc P *ᵥ (A *ᵥ av)
        = (P * A) *ᵥ av := by rw [Matrix.mulVec_mulVec]
      _ = (A * P) *ᵥ av := by rw [← hPcomm]
      _ = A *ᵥ (P *ᵥ av) := by rw [← Matrix.mulVec_mulVec]
      _ = A *ᵥ av := by rw [havP]
  have hav_supp : ∀ i, i ∉ S → av (Sum.inl i) = 0 ∧ av (Sum.inr i) = 0 :=
    fun i hi => planeIdem_mulVec_self havP hi
  have hgav_supp : ∀ i, i ∉ S → (A *ᵥ av) (Sum.inl i) = 0 ∧
      (A *ᵥ av) (Sum.inr i) = 0 := fun i hi => planeIdem_mulVec_self hPgav hi
  have hspAv : spForm (t + δ.val) K (A *ᵥ av) (A *ᵥ (T *ᵥ av)) =
      spForm (t + δ.val) K av (T *ᵥ av) :=
    (mem_statedSp_iff_forall (A := ((b : ↥(StatedSp (t + δ.val) K)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K))).mp b.2 av (T *ᵥ av)
  have hTA : T *ᵥ (A *ᵥ av) = A *ᵥ (T *ᵥ av) := by
    calc T *ᵥ (A *ᵥ av)
        = (T * A) *ᵥ av := by rw [Matrix.mulVec_mulVec]
      _ = (A * T) *ᵥ av := by rw [← hcommAT]
      _ = A *ᵥ (T *ᵥ av) := by rw [← Matrix.mulVec_mulVec]
  have hQga : planeQ t δ (A *ᵥ av) = planeQ t δ av := by
    calc planeQ t δ (A *ᵥ av)
        = spForm (t + δ.val) K (A *ᵥ av) (T *ᵥ (A *ᵥ av)) :=
            planeQ_eq_spForm_tau_of_support ζ t δ hK hζ e hgav_supp
      _ = spForm (t + δ.val) K (A *ᵥ av) (A *ᵥ (T *ᵥ av)) := by rw [hTA]
      _ = spForm (t + δ.val) K av (T *ᵥ av) := hspAv
      _ = planeQ t δ av :=
            (planeQ_eq_spForm_tau_of_support ζ t δ hK hζ e hav_supp).symm
  have hbeta : (A *ᵥ av) ⬝ᵥ
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ bv) =
      av ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ bv) := by
    have hsp : spForm (t + δ.val) K (A *ᵥ av) (A *ᵥ bv) =
        spForm (t + δ.val) K av bv :=
      (mem_statedSp_iff_forall (A := ((b : ↥(StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K))).mp b.2 av bv
    have h3 : spForm (t + δ.val) K av (A *ᵥ bv) = spForm (t + δ.val) K av bv := by
      rw [hgbv]
    rw [← hgbv]
    change (A *ᵥ av) ⬝ᵥ (spJ (t + δ.val) K *ᵥ (A *ᵥ bv)) =
      av ⬝ᵥ (spJ (t + δ.val) K *ᵥ (A *ᵥ bv))
    rw [← spForm_apply, ← spForm_apply]
    exact hsp.trans h3.symm
  change planeQ t δ (A *ᵥ v) = planeQ t δ v
  calc planeQ t δ (A *ᵥ v)
      = planeQ t δ (A *ᵥ (av + bv)) := by rw [havbv]
    _ = planeQ t δ (A *ᵥ av + A *ᵥ bv) := by rw [Matrix.mulVec_add]
    _ = planeQ t δ (A *ᵥ av + bv) := by rw [hgbv]
    _ = planeQ t δ (A *ᵥ av) + planeQ t δ bv +
          (A *ᵥ av) ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ bv) :=
          planeQ_add t δ (A *ᵥ av) bv
    _ = planeQ t δ av + planeQ t δ bv +
          av ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ bv) := by rw [hQga, hbeta]
    _ = planeQ t δ (av + bv) := (planeQ_add t δ av bv).symm
    _ = planeQ t δ v := by rw [havbv]

theorem mem_inside_liftV_iff (k k' : PlaneRaw.PlaneKind) (e u : PlaneRaw.V t) :
    liftV t δ u ∈ PlaneRaw.inside k
        (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) ↔
      u ∈ PlaneRaw.inside k' (.extension e : PlaneRaw.Code t) := by
  rw [PlaneRaw.mem_inside_extension, PlaneRaw.mem_inside_extension]
  have h1 : (∀ i : Fin (t + δ.val), liftV t δ e i = 0 → liftV t δ u i = 0) ↔
      (∀ i : Fin t, e i = 0 → u i = 0) := by
    constructor
    · intro h i hi
      have := h (Fin.castAdd δ.val i) (by simpa [liftV, Fin.append_left] using hi)
      simpa [liftV, Fin.append_left] using this
    · intro h i hi
      revert hi
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · intro hi
        have h_e : e j = 0 := by simpa [liftV, Fin.append_left] using hi
        simpa [liftV, Fin.append_left] using h j h_e
      · intro hi
        simp [liftV, Fin.append_right]
  have h2 : (∑ i : Fin (t + δ.val), liftV t δ e i * liftV t δ u i) =
      ∑ i : Fin t, e i * u i := by
    rw [Fin.sum_univ_add]
    simp [liftV, Fin.append_left, Fin.append_right]
  rw [h1, h2]

theorem mem_cent_liftV_iff (k k' : PlaneRaw.PlaneKind) (e u : PlaneRaw.V t) :
    liftV t δ u ∈ PlaneRaw.cent k
        (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) ↔
      u ∈ PlaneRaw.cent k' (.extension e : PlaneRaw.Code t) := by
  rw [PlaneRaw.mem_cent_extension, PlaneRaw.mem_cent_extension]
  constructor
  · intro h i hi j hj
    have hi' : Fin.castAdd δ.val i ∈
        PlaneRaw.Code.extSupport (liftV t δ e) := by
      rw [extSupport_liftV]
      exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hj' : Fin.castAdd δ.val j ∈
        PlaneRaw.Code.extSupport (liftV t δ e) := by
      rw [extSupport_liftV]
      exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have := h _ hi' _ hj'
    simpa [liftV, Fin.append_left] using this
  · intro h i hi j hj
    rw [extSupport_liftV] at hi hj
    obtain ⟨i', hi', hii⟩ := Finset.mem_map.mp hi
    obtain ⟨j', hj', hjj⟩ := Finset.mem_map.mp hj
    subst i
    subst j
    simpa [liftV, Fin.append_left] using h i' hi' j' hj'

theorem admissible_symplectic_lift {e : PlaneRaw.V t}
    (he : PlaneRaw.admissible (.orthogonal δ) (.extension e : PlaneRaw.Code t)) :
    PlaneRaw.admissible .symplectic
      (.extension (liftV t δ e) : PlaneRaw.Code (t + δ.val)) := by
  obtain ⟨hne, h4⟩ := he
  have hcard := card_extSupport_liftV t δ e
  constructor
  · intro h0
    have hzero : (PlaneRaw.Code.extSupport (liftV t δ e)).card = 0 := by
      rw [h0]
      simp [PlaneRaw.Code.extSupport]
    omega
  · rwa [hcard]

omit [Finite K] [CharP K 2] in
theorem mem_map_subtype_iff {m : ℕ}
    (Y : Subgroup ↥(StatedSp m K)) (x : ↥(StatedSp m K)) :
    ((x : GL (Fin m ⊕ Fin m) K) ∈ Y.map (StatedSp m K).subtype) ↔ x ∈ Y := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite K] [CharP K 2] in
theorem oBlockGroup_map_eq (c : PlaneRaw.Code t) :
    (oBlockGroup ζ t δ c).map (omegaQ (K := K) t δ).subtype =
      ((SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c)).map
        (StatedSp (t + δ.val) K).subtype) ⊓ omegaQ (K := K) t δ := by
  rw [oBlockGroup, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]

