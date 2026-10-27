module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpPhi
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

namespace Item211Lie3Proof

open Item211Lie2Proof
open CFSG.RankThree.SubgroupLists (plusBlock minusBlock tStdMat plusBlock_mul)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut)

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem mem_normalizer_conjClosure {M : Type*} [Group M] {D H : Subgroup M} {k : M}
    (hk : k ∈ H) : k ∈ Subgroup.normalizer (conjClosure D H : Set M) := by
  have hconj : ∀ {k : M}, k ∈ H → ∀ y ∈ conjClosure D H, k * y * k⁻¹ ∈ conjClosure D H := by
    intro k hk y hy
    have hle : conjClosure D H ≤ (conjClosure D H).comap (MulAut.conj k).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, x, hx, rfl⟩
      refine Subgroup.subset_closure ⟨k * g, H.mul_mem hk hg, x, hx, ?_⟩
      change k * (g * x * g⁻¹) * k⁻¹ = k * g * x * (k * g)⁻¹
      group
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj hk y, fun hy => ?_⟩
  have e := hconj (H.inv_mem hk) _ hy
  rwa [inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at e

variable {K : Type} [Field K]

theorem mul_commute_tStd {M N : Matrix V₄ V₄ K} (hM : M * tStdMat = tStdMat * M)
    (hN : N * tStdMat = tStdMat * N) : M * N * tStdMat = tStdMat * (M * N) := by
  rw [Matrix.mul_assoc, hN, ← Matrix.mul_assoc, hM, Matrix.mul_assoc]

theorem det_minusBlock_frConj (h2 : (2 : K) ≠ 0) (hS y : StatedSp 2 K)
    (hy : frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K)) :
    (minusBlock (frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K))).det = 1 := by
  rw [← coe_conj_eq_frConj] at hy ⊢
  exact det_minusBlock h2 (hS⁻¹ * y * hS).2 hy

theorem eq_smul_one_of_isScalar2 {M : Matrix (Fin 2) (Fin 2) K} (hM : IsScalar2 M) :
    M = M 1 1 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨h01, h10, h00⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

theorem commute_of_conjAut_commute (h2 : (2 : K) ≠ 0)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    {d₀ : StatedSp 2 K} (hd3 : (d₀ : GL V₄ K) ^ 3 = 1) (A : gsp 2 K)
    (hA : conjAut 2 K A * MulAut.conj (d₀ : StatedProj (StatedSp 2 K)) =
      MulAut.conj (d₀ : StatedProj (StatedSp 2 K)) * conjAut 2 K A) :
    ((A : GL V₄ K) : Matrix V₄ V₄ K) * (d₀ : GL V₄ K) =
      ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) * (A : GL V₄ K) := by
  have hs := conjAut_sign A d₀ (fix_of_commute_conj hinj hA)
  have hs' : (d₀ : GL V₄ K) * A = A * d₀ ∨ (d₀ : GL V₄ K) * A = -(A * d₀) := by
    rcases hs with h | h
    · exact Or.inl h.symm
    · right
      rw [h, neg_neg]
  have e := commute_of_pow_three_of_signs (ne_neg_gl h2 _) hd3 hs'
  have e' := congrArg Units.val e
  rw [Units.val_mul, Units.val_mul] at e'
  exact e'.symm

theorem excPlus_statedSp_of_fixed [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hK4 : 4 ≤ Nat.card K)
    (hAut : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ A : gsp 2 K, α = conjAut 2 K A)
    {D : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hDi : D ≤ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range)
    (hDe : IsElemAbelian 3 D) {d₀ : StatedSp 2 K} (hd3 : (d₀ : GL V₄ K) ^ 3 = 1)
    (hd1 : (d₀ : GL V₄ K) ≠ 1)
    (hP : ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) * ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) +
      ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) + 1 ≠ 0)
    (hdD : MulAut.conj (d₀ : StatedProj (StatedSp 2 K)) ∈ D)
    {T : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (StatedProj (StatedSp 2 K))))) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D ((MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range ⊓
        Subgroup.centralizer ({MulAut.conj (d₀ : StatedProj (StatedSp 2 K))} :
          Set (MulAut (StatedProj (StatedSp 2 K))))) ⊓
        Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K))))) :
          Subgroup (MulAut (StatedProj (StatedSp 2 K)))) :
            Set (MulAut (StatedProj (StatedSp 2 K)))) := by
  classical
  have hZ := center_statedProj_statedSp_eq_bot hK4
  have hinj := Item211Lie2Proof.conj_injective' hZ
  set Cd := (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range ⊓
    Subgroup.centralizer ({MulAut.conj (d₀ : StatedProj (StatedSp 2 K))} :
      Set (MulAut (StatedProj (StatedSp 2 K)))) with hCd
  set C := conjClosure D Cd with hC
  set H := C ⊓ Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDCd : D ≤ Cd := fun x hx => Subgroup.mem_inf.mpr ⟨hDi hx,
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm _ hx _ hdD)⟩
  have hDC : D ≤ C := fun x hx => Subgroup.subset_closure ⟨1, Cd.one_mem, x, hx, by group⟩
  have hCCd : C ≤ Cd := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, x, hx, rfl⟩
    exact Cd.mul_mem (Cd.mul_mem hg (hDCd hx)) (Cd.inv_mem hg))
  have hd3' : ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) * ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) *
      ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    have e := congrArg Units.val hd3
    rwa [Units.val_pow_eq_pow_val, pow_three', Units.val_one] at e
  obtain ⟨h, hh, hfr, hB1, hm⟩ := exists_frame h2 h3 d₀.2 hd3' hd1 hP
  obtain ⟨hS, rfl⟩ : ∃ hS : StatedSp 2 K, (hS : GL V₄ K) = h := ⟨⟨h, hh⟩, rfl⟩
  set G := ((d₀ : GL V₄ K) : Matrix V₄ V₄ K) with hG
  have hGt : frConj (hS : GL V₄ K) G * tStdMat = tStdMat * frConj (hS : GL V₄ K) G := hfr G rfl
  set m := minusBlock (frConj (hS : GL V₄ K) G) with hmdef
  have hmns : ¬ IsScalar2 m := not_isScalar2_of_root h3 (det_minusBlock_frConj h2 hS d₀ hGt) hm
  have hblk : ∀ N : Matrix V₄ V₄ K, N * G = G * N →
      frConj (hS : GL V₄ K) N * tStdMat = tStdMat * frConj (hS : GL V₄ K) N ∧
        minusBlock (frConj (hS : GL V₄ K) N) * m = m * minusBlock (frConj (hS : GL V₄ K) N) := by
    intro N hN
    refine ⟨hfr N hN, ?_⟩
    have e := congrArg (fun X => minusBlock (frConj (hS : GL V₄ K) X)) hN
    simp only [frConj_mul] at e
    rwa [minusBlock_mul h2 (hfr N hN), minusBlock_mul h2 hGt] at e
  have hblkGL : ∀ N : GL V₄ K, (d₀ : GL V₄ K) * N = N * d₀ →
      frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) * tStdMat =
        tStdMat * frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) ∧
        minusBlock (frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K)) * m =
          m * minusBlock (frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K)) := by
    intro N hN
    refine hblk _ ?_
    have e := congrArg Units.val hN
    rw [Units.val_mul, Units.val_mul] at e
    exact e.symm
  obtain ⟨a₀, b₀, ha₀, -, hdΦ⟩ := exists_framePhi_eq h2 hS d₀ hGt
  have ha₀1 : a₀ = 1 := Subtype.ext (by rw [ha₀, hB1, Matrix.SpecialLinearGroup.coe_one])
  have hΨCd : ∀ a : SL(2, K), framePhi hS (a, 1) ∈ Cd := by
    intro a
    refine Subgroup.mem_inf.mpr ⟨⟨_, (framePhi_apply hS (a, 1)).symm⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hdΦ, ha₀1, ← map_mul, ← map_mul]
    congr 1
    ext1 <;> simp
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨x', rfl⟩ := hDi hx
  have hx'3 : x' ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hx, map_one])
  obtain ⟨x₀, rfl, hx₀3⟩ := exists_lift_pow_three hx'3
  have hx₀d : (d₀ : GL V₄ K) * x₀ = x₀ * d₀ := by
    have hc : (x₀ : StatedProj (StatedSp 2 K)) * d₀ = d₀ * x₀ :=
      hinj (by rw [map_mul, map_mul]; exact hDcomm _ hx _ hdD)
    exact (commute_of_pow_three_of_signs (ne_neg_gl h2 _) hx₀3 (comm_or_anticomm_of_mk hc)).symm
  have hqH := hQH hq
  obtain ⟨q₀, rfl, hq₀d⟩ := exists_lift_commute h2 hinj hd3 (hCCd (Subgroup.mem_inf.mp hqH).1)
  obtain ⟨hXt, hXm⟩ := hblkGL _ hx₀d
  obtain ⟨hQt, hQm⟩ := hblkGL _ hq₀d
  set Xm := frConj (hS : GL V₄ K) ((x₀ : GL V₄ K) : Matrix V₄ V₄ K) with hXmdef
  set Qm := frConj (hS : GL V₄ K) ((q₀ : GL V₄ K) : Matrix V₄ V₄ K) with hQmdef
  suffices hqx : (q₀ : GL V₄ K) * x₀ = x₀ * q₀ by
    have e : q₀ * x₀ = x₀ * q₀ := Subtype.ext hqx
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e]
  suffices hblocks : plusBlock Qm * plusBlock Xm = plusBlock Xm * plusBlock Qm by
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul]
    refine eq_of_plusBlock_minusBlock h2 (mul_commute_tStd hQt hXt) (mul_commute_tStd hXt hQt)
      ?_ ?_
    · rw [plusBlock_mul h2 hQt hXt, plusBlock_mul h2 hXt hQt, hblocks]
    · rw [minusBlock_mul h2 hQt, minusBlock_mul h2 hXt]
      exact commute_of_commute_nonscalar hmns hQm.symm hXm.symm
  have hTA : ∀ t ∈ T, ∀ A : gsp 2 K, t = conjAut 2 K A →
      ((A : GL V₄ K) : Matrix V₄ V₄ K) * G = G * (A : GL V₄ K) := by
    intro t ht A hA
    subst hA
    exact commute_of_conjAut_commute h2 hinj hd3 A
      (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hdD).symm
  by_cases hcase : ∃ t ∈ T, ∃ A : gsp 2 K, t = conjAut 2 K A ∧
      ¬ IsScalar2 (plusBlock (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)))
  ·
    obtain ⟨t, ht, A, rfl, hAns⟩ := hcase
    obtain ⟨hAt, hAm⟩ := hblk _ (hTA _ ht A rfl)
    have hAx : (A : GL V₄ K) * x₀ = x₀ * A :=
      commute_of_sign h2 (hS : GL V₄ K) hmns hAt hAm hXt hXm (det_minusBlock_frConj h2 hS x₀ hXt)
        (conjAut_sign A x₀ (fix_of_commute_conj hinj
          (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hx).symm))
    have hAq : (A : GL V₄ K) * q₀ = q₀ * A :=
      commute_of_sign h2 (hS : GL V₄ K) hmns hAt hAm hQt hQm (det_minusBlock_frConj h2 hS q₀ hQt)
        (conjAut_sign A q₀ (fix_of_commute_conj hinj
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqH).2 _ ht)))
    have hplus : ∀ N : GL V₄ K, (A : GL V₄ K) * N = N * A →
        frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) * tStdMat =
          tStdMat * frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K) →
        plusBlock (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)) *
            plusBlock (frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K)) =
          plusBlock (frConj (hS : GL V₄ K) (N : Matrix V₄ V₄ K)) *
            plusBlock (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)) := by
      intro N hN hNt
      have e := congrArg (fun g : GL V₄ K => plusBlock (frConj (hS : GL V₄ K) (g : Matrix V₄ V₄ K)))
        hN
      simp only [Units.val_mul, frConj_mul] at e
      rwa [plusBlock_mul h2 hAt hNt, plusBlock_mul h2 hNt hAt] at e
    exact commute_of_commute_nonscalar hAns (hplus _ hAq hQt) (hplus _ hAx hXt)
  ·
    push Not at hcase
    by_cases hXs : IsScalar2 (plusBlock Xm)
    · rw [eq_smul_one_of_isScalar2 hXs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
    obtain ⟨X₁, X₂, hX₁, -, hxΦ⟩ := exists_framePhi_eq h2 hS x₀ hXt
    obtain ⟨Q₁, Q₂, hQ₁, -, hqΦ⟩ := exists_framePhi_eq h2 hS q₀ hQt
    have hX13 : X₁ ^ 3 = 1 := by
      apply Subtype.ext
      have e : plusBlock (Xm * Xm * Xm) = 1 := by
        have e0 := congrArg
          (fun g : GL V₄ K => plusBlock (frConj (hS : GL V₄ K) (g : Matrix V₄ V₄ K))) hx₀3
        simpa only [pow_three', Units.val_mul, frConj_mul, Units.val_one, frConj_one,
          CFSG.RankThree.SubgroupLists.plusBlock_one] using e0
      have hXt2 : Xm * Xm * tStdMat = tStdMat * (Xm * Xm) := mul_commute_tStd hXt hXt
      rw [plusBlock_mul h2 hXt2 hXt, plusBlock_mul h2 hXt hXt] at e
      rw [Matrix.SpecialLinearGroup.coe_pow, pow_three', hX₁, Matrix.SpecialLinearGroup.coe_one]
      exact e
    have hΨC : ∀ a : SL(2, K), framePhi hS (a, 1) ∈ C := by
      intro a
      refine mem_of_normalizer hK4 h2 ((framePhi hS).comp (MonoidHom.inl _ _))
        (fun a => mem_normalizer_conjClosure (hΨCd a)) (X := X₁) (by rwa [hX₁]) hX13
        (z := framePhi hS (1, X₂)) (fun a => ?_) ?_ a
      · rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, ← map_mul]
        congr 1
        ext1 <;> simp
      · rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul]
        have e : ((X₁, 1) * (1, X₂) : SL(2, K) × SL(2, K)) = (X₁, X₂) := by
          ext1 <;> simp
        rw [e, ← hxΦ]
        exact hDC hx
    have hΨT : ∀ a : SL(2, K), framePhi hS (a, 1) ∈
        Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
      intro a
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨A, rfl⟩ := hAut t
      obtain ⟨hAt, -⟩ := hblk _ (hTA _ ht A rfl)
      exact conjAut_commute_framePhi h2 hS A hAt (eq_smul_one_of_isScalar2 (hcase _ ht A rfl)) a
    have hΨQ : ∀ a : SL(2, K), framePhi hS (a, 1) ∈ Subgroup.normalizer (Q : Set (MulAut _)) :=
      fun a => CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
        (Subgroup.mem_inf.mpr ⟨hΨC a, hΨT a⟩)
    have hQ1 : Q₁ ∈ Subgroup.center SL(2, K) :=
      mem_center_of_pairHom hK4 (framePhi hS) hQ2 hΨQ (fun _ _ h => framePhi_eq_one hinj hS h)
        (by rw [← hqΦ]; exact hq)
    have e := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
      (Subgroup.mem_center_iff.mp hQ1 X₁)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e
    rw [← hX₁, ← hQ₁]
    exact e.symm

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
