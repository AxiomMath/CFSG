module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

variable {d : ℕ} {K : Type} [Field K]

theorem coe_slConjugation' (A : GL (Fin d) K) (g : SpecialLinearGroup (Fin d) K) :
    ((CatalogueBHigherLinearAction.slConjugation d K A g : SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (A : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  CatalogueBHigherLinearAction.slConjugation_matrix d K A g

theorem exists_scalar_of_conjAut_eq_one [Finite K] {A : GL (Fin d) K}
    (h : conjAut d K A = 1) : ∃ c : K, (A : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hcomm : ∀ i j : Fin d, i ≠ j →
      Commute (single i j (1 : K)) (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set t : SpecialLinearGroup (Fin d) K := SpecialLinearGroup.transvection hij 1 with ht
    set s := CatalogueBHigherLinearAction.slConjugation d K A t with hs
    have h1 : proj d K s = proj d K t := by
      rw [hs, ← conjAut_proj, h]
      rfl
    rw [proj_eq_proj_iff] at h1
    obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
    have hzc : s⁻¹ * t ∈ Subgroup.center _ := scalars_le_center d K h1
    have hts : t = s * (s⁻¹ * t) := by group
    have htℓ : t ^ ℓ = 1 := by
      have := CFSG.RankThree.CALinearPlane.transvection_pow_char (k := K) (ℓ := ℓ) hij (1 : K)
      rwa [pow_one] at this
    have hsℓ : s ^ ℓ = 1 := by
      rw [hs, ← map_pow, htℓ, map_one]
    have hzℓ : (s⁻¹ * t) ^ ℓ = 1 := by
      have h2 : t ^ ℓ = s ^ ℓ * (s⁻¹ * t) ^ ℓ := by
        conv_lhs => rw [hts]
        exact Commute.mul_pow (Subgroup.mem_center_iff.mp hzc s) ℓ
      rw [htℓ, hsℓ, one_mul] at h2
      exact h2.symm
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        exact i.elim0
      · exact hd
    have hcℓ : (c : K) ^ ℓ = 1 := by
      have h3 := Matrix.SpecialLinearGroup.coe_pow (s⁻¹ * t) ℓ
      rw [hzℓ, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at h3
      have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, hd0⟩ ⟨0, hd0⟩) h3
      simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
      exact h4.symm
    have hc1 : (c : K) = 1 := by
      apply frobenius_inj K ℓ
      rw [frobenius_def, frobenius_def, hcℓ, one_pow]
    have hz1 : s⁻¹ * t = 1 := by
      ext a b
      rw [hc, hc1, map_one]
      rfl
    have hst : s = t := by
      rw [hts, hz1, mul_one]
    have hmat := congrArg (fun g : SpecialLinearGroup (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K)) hst
    simp only [hs, coe_slConjugation', ht, CFSG.LinearGroups.coe_transvection] at hmat
    have hA1 : ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (A : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h4 : (A : Matrix (Fin d) (Fin d) K) * (1 + single i j 1) =
        (1 + single i j 1) * (A : Matrix (Fin d) (Fin d) K) := by
      calc (A : Matrix (Fin d) (Fin d) K) * (1 + single i j 1)
          = (A : Matrix (Fin d) (Fin d) K) * (1 + single i j 1) *
              (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
                (A : Matrix (Fin d) (Fin d) K)) := by rw [hA1, Matrix.mul_one]
        _ = (1 + single i j 1) * (A : Matrix (Fin d) (Fin d) K) := by
          rw [← Matrix.mul_assoc, hmat]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h4
    exact (add_left_cancel h4).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := (A : Matrix (Fin d) (Fin d) K))
    fun i j hij => hcomm i j hij
  exact ⟨c, hc.symm⟩

theorem exists_unit_of_scalar {A : GL (Fin d) K} (hd : 0 < d) {c : K}
    (hA : (A : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c) :
    ∃ u : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin d) u := by
  have hc0 : c ≠ 0 := by
    intro hc
    have h1 : (A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hA, hc, map_zero, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h2
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_scalar, hA, Units.val_mk0]

variable {p : ℕ}

theorem mem_scalars_of_coe_eq_scalar (hd : 0 < d) {z : SpecialLinearGroup (Fin d) K} {c : K}
    (hz : (z : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c) : c ^ d = 1 ∧ z ∈ scalars d K := by
  have hdet : c ^ d = 1 := by
    have h1 := z.2
    rw [hz, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      at h1
    exact h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hdet
    exact zero_ne_one hdet
  refine ⟨hdet, Units.mk0 c hc0, Units.ext ?_, hz⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]

theorem eq_one_of_scalar_of_pow (hpd : Nat.Coprime p d) {z : SpecialLinearGroup (Fin d) K}
    (hz : z ∈ scalars d K) (hzp : z ^ p = 1) : z = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · ext i
    exact i.elim0
  obtain ⟨c, hcd, hc⟩ := mem_scalars.mp hz
  have hcp : c ^ p = 1 := by
    have h3 := Matrix.SpecialLinearGroup.coe_pow z p
    rw [hzp, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at h3
    have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, hd⟩ ⟨0, hd⟩) h3
    simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h4, Units.val_one])
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hpd).mp ⟨hcp, hcd⟩
  ext i j
  rw [hc, hc1, Units.val_one, map_one]
  rfl

theorem slLift_exponents {G : Type*} [CommGroup G] {a l : G} {u v : ℤ}
    (huv : u * d + v * p = 1) (hal : a ^ p = l ^ d) :
    (a ^ (-u) * l ^ (-v)) ^ p * l = 1 ∧ (a ^ (-u) * l ^ (-v)) ^ d * a = 1 := by
  have hal' : a ^ (p : ℤ) = l ^ (d : ℤ) := by rw [zpow_natCast, zpow_natCast, hal]
  have e1 : ∀ n : ℕ, (a ^ (-u) * l ^ (-v)) ^ n = a ^ (-u * n) * l ^ (-v * n) := by
    intro n
    rw [← zpow_natCast, mul_zpow, ← _root_.zpow_mul a, ← _root_.zpow_mul l]
  have e2 : a ^ (-u * (p : ℤ)) = l ^ (-u * (d : ℤ)) := by
    rw [mul_comm (-u) (p : ℤ), _root_.zpow_mul, hal', ← _root_.zpow_mul, mul_comm (d : ℤ) (-u)]
  have e3 : l ^ (-v * (d : ℤ)) = a ^ (-v * (p : ℤ)) := by
    rw [mul_comm (-v) (d : ℤ), _root_.zpow_mul, ← hal', ← _root_.zpow_mul, mul_comm (p : ℤ) (-v)]
  constructor
  · calc (a ^ (-u) * l ^ (-v)) ^ p * l = l ^ (-u * d) * l ^ (-v * p) * l := by rw [e1, e2]
      _ = l ^ (-u * d + -v * p + 1) := by rw [_root_.zpow_add, _root_.zpow_add, zpow_one]
      _ = 1 := by rw [show -u * (d : ℤ) + -v * p + 1 = 0 by linarith, zpow_zero]
  · calc (a ^ (-u) * l ^ (-v)) ^ d * a = a ^ (-u * d) * a ^ (-v * p) * a := by rw [e1, e3]
      _ = a ^ (-u * d + -v * p + 1) := by rw [_root_.zpow_add, _root_.zpow_add, zpow_one]
      _ = 1 := by rw [show -u * (d : ℤ) + -v * p + 1 = 0 by linarith, zpow_zero]

theorem det_scalar_GL (s : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) s) = s ^ d := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
    det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]

theorem commute_scalar_GL (s : Kˣ) (A : GL (Fin d) K) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin d) s) A :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute (s : K) (fun _ => Commute.all _ _) _)

theorem exists_slLift [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d) {A : GL (Fin d) K}
    (hA : conjAut d K A ^ p = 1) :
    ∃ g : SpecialLinearGroup (Fin d) K, g ^ p = 1 ∧
      conjAut d K (SpecialLinearGroup.toGL g) = conjAut d K A := by
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one (A := A ^ p) (by rw [map_pow, hA])
  obtain ⟨l, hl⟩ := exists_unit_of_scalar hd hc
  set a : Kˣ := Matrix.GeneralLinearGroup.det A with ha
  have hal : a ^ p = l ^ d := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hl
    rw [map_pow] at h1
    rw [ha, h1, det_scalar_GL]
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * d + v * p = 1 := Nat.isCoprime_iff_coprime.mpr hpd.symm
  obtain ⟨hsp, hsd⟩ := slLift_exponents huv hal
  set s : Kˣ := a ^ (-u) * l ^ (-v) with hs
  set C : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) s * A with hC
  have hCdet : (C : Matrix (Fin d) (Fin d) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det C = 1 := by
      rw [hC, map_mul, ← ha, det_scalar_GL, hsd]
    have h2 := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  have hCp : C ^ p = 1 := by
    rw [hC, (commute_scalar_GL s A).mul_pow, ← map_pow, hl, ← map_mul, hsp, map_one]
  set g : SpecialLinearGroup (Fin d) K := ⟨(C : Matrix (Fin d) (Fin d) K), hCdet⟩
  have hgC : (g : Matrix (Fin d) (Fin d) K) = C := rfl
  refine ⟨g, ?_, ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hgC, ← Units.val_pow_eq_pow_val, hCp, Units.val_one]
    rfl
  · have h1 : SpecialLinearGroup.toGL g = C := Units.ext rfl
    rw [h1, hC, map_mul, conjAut_scalar, one_mul]

theorem eq_of_slLift [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
    {g h : SpecialLinearGroup (Fin d) K} (hg : g ^ p = 1) (hh : h ^ p = 1)
    (he : conjAut d K (SpecialLinearGroup.toGL g) = conjAut d K (SpecialLinearGroup.toGL h)) :
    g = h := by
  have h1 : conjAut d K (SpecialLinearGroup.toGL (g⁻¹ * h)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, he, inv_mul_cancel]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h1
  have hz := (mem_scalars_of_coe_eq_scalar hd (z := g⁻¹ * h) hc).2
  have hzc := scalars_le_center d K hz
  have hzp : (g⁻¹ * h) ^ p = 1 := by
    have h2 : h ^ p = g ^ p * (g⁻¹ * h) ^ p := by
      conv_lhs => rw [show h = g * (g⁻¹ * h) by group]
      exact Commute.mul_pow (Subgroup.mem_center_iff.mp hzc g) p
    rw [hh, hg, one_mul] at h2
    exact h2.symm
  exact inv_mul_eq_one.mp (eq_one_of_scalar_of_pow hpd hz hzp)

theorem commute_of_slLift [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
    {g h : SpecialLinearGroup (Fin d) K} (hh : h ^ p = 1)
    (hc : conjAut d K (SpecialLinearGroup.toGL g) * conjAut d K (SpecialLinearGroup.toGL h) =
      conjAut d K (SpecialLinearGroup.toGL h) * conjAut d K (SpecialLinearGroup.toGL g)) :
    g * h = h * g := by
  set z := g * h * g⁻¹ * h⁻¹ with hzdef
  have h1 : conjAut d K (SpecialLinearGroup.toGL z) = 1 := by
    rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, hc]
    group
  obtain ⟨c, hcz⟩ := exists_scalar_of_conjAut_eq_one h1
  have hz := (mem_scalars_of_coe_eq_scalar hd (z := z) hcz).2
  have hzc := scalars_le_center d K hz
  have h2 : g * h * g⁻¹ = z * h := by rw [hzdef]; group
  have h3 : (g * h * g⁻¹) ^ p = 1 := by rw [conj_pow, hh, mul_one, mul_inv_cancel]
  have h4 : (z * h) ^ p = z ^ p * h ^ p :=
    Commute.mul_pow (Subgroup.mem_center_iff.mp hzc h).symm p
  rw [← h2, h3, hh, mul_one] at h4
  have h5 : z = 1 := eq_one_of_scalar_of_pow hpd hz h4.symm
  calc g * h = z * (h * g) := by rw [hzdef]; group
    _ = h * g := by rw [h5, one_mul]

section LiftGroup

variable [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
  (X : Subgroup (MulAut (projectiveSL d K))) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)

@[expose] def slLift : Subgroup (SpecialLinearGroup (Fin d) K) where
  carrier := {g | g ^ p = 1 ∧ conjAut d K (SpecialLinearGroup.toGL g) ∈ X}
  mul_mem' := by
    rintro g h ⟨hg, hgX⟩ ⟨hh, hhX⟩
    have hgh : g * h = h * g := commute_of_slLift hd hpd hh (hXc _ hgX _ hhX)
    refine ⟨?_, ?_⟩
    · rw [Commute.mul_pow hgh, hg, hh, one_mul]
    · rw [map_mul, map_mul]
      exact X.mul_mem hgX hhX
  one_mem' := ⟨one_pow p, by rw [map_one, map_one]; exact X.one_mem⟩
  inv_mem' := by
    rintro g ⟨hg, hgX⟩
    exact ⟨by rw [inv_pow, hg, inv_one], by rw [map_inv, map_inv]; exact X.inv_mem hgX⟩

theorem mem_slLift {g : SpecialLinearGroup (Fin d) K} :
    g ∈ slLift hd hpd X hXc ↔ g ^ p = 1 ∧ conjAut d K (SpecialLinearGroup.toGL g) ∈ X :=
  Iff.rfl

theorem slLift_comm {g h : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc)
    (hh : h ∈ slLift hd hpd X hXc) : g * h = h * g :=
  commute_of_slLift hd hpd hh.1 (hXc _ hg.2 _ hh.2)

theorem card_slLift (hXp : ∀ x ∈ X, x ^ p = 1)
    (hXI : ∀ x ∈ X, ∃ A : GL (Fin d) K, conjAut d K A = x) :
    Nat.card (slLift hd hpd X hXc) = Nat.card X := by
  let f : slLift hd hpd X hXc → X := fun g => ⟨conjAut d K (SpecialLinearGroup.toGL g), g.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ he
    exact Subtype.ext (eq_of_slLift hd hpd hg.1 hh.1 (congrArg Subtype.val he))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨A, rfl⟩ := hXI x hx
    obtain ⟨g, hgp, hgA⟩ := exists_slLift hd hpd (hXp _ hx)
    exact ⟨⟨g, hgp, hgA ▸ hx⟩, Subtype.ext hgA⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end LiftGroup

theorem exists_isPrimitiveRoot [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpK)
  exact ⟨u, IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)⟩

section Diagonal

variable (A : GL (Fin d) K)

@[expose] def conjMat (g : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  (A : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
    ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)

variable {A}

theorem inv_mul_GL : ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
    (A : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem mul_inv_GL : (A : Matrix (Fin d) (Fin d) K) *
    ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjMat_mul (g h : SpecialLinearGroup (Fin d) K) :
    conjMat A (g * h) = conjMat A g * conjMat A h := by
  simp only [conjMat, Matrix.SpecialLinearGroup.coe_mul]
  calc (A : Matrix (Fin d) (Fin d) K) * ((g : Matrix (Fin d) (Fin d) K) *
        (h : Matrix (Fin d) (Fin d) K)) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      = (A : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
          (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K)) *
          (h : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [inv_mul_GL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conjMat_one : conjMat A (1 : SpecialLinearGroup (Fin d) K) = 1 := by
  rw [conjMat, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, mul_inv_GL]

theorem conjMat_pow (g : SpecialLinearGroup (Fin d) K) (n : ℕ) :
    conjMat A (g ^ n) = conjMat A g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, conjMat_one]
  | succ n ih => rw [pow_succ, conjMat_mul, ih, pow_succ]

theorem det_conjMat (g : SpecialLinearGroup (Fin d) K) : (conjMat A g).det = 1 := by
  rw [conjMat, det_mul, det_mul, g.2, mul_one, ← det_mul, mul_inv_GL, det_one]

theorem conjMat_injective : Function.Injective (conjMat (d := d) (K := K) A) := by
  intro g h hgh
  ext i j
  have h1 : (g : Matrix (Fin d) (Fin d) K) = ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      conjMat A g * (A : Matrix (Fin d) (Fin d) K) := by
    simp only [conjMat, ← Matrix.mul_assoc, inv_mul_GL, Matrix.one_mul]
    rw [Matrix.mul_assoc, inv_mul_GL, Matrix.mul_one]
  have h2 : (h : Matrix (Fin d) (Fin d) K) = ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      conjMat A h * (A : Matrix (Fin d) (Fin d) K) := by
    simp only [conjMat, ← Matrix.mul_assoc, inv_mul_GL, Matrix.one_mul]
    rw [Matrix.mul_assoc, inv_mul_GL, Matrix.mul_one]
  rw [h1, h2, hgh]

theorem conjMat_diag {p : ℕ} {g : SpecialLinearGroup (Fin d) K} (hg : g ^ p = 1)
    (hdiag : ∀ i j, i ≠ j → conjMat A g i j = 0) :
    conjMat A g = diagonal (fun i => conjMat A g i i) ∧ (∀ i, conjMat A g i i ^ p = 1) ∧
      ∏ i, conjMat A g i i = 1 := by
  have hD := CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag hdiag
  refine ⟨hD, fun i => ?_, ?_⟩
  · have h1 : conjMat A g ^ p = 1 := by rw [← conjMat_pow, hg, conjMat_one]
    rw [hD, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  · have h1 := det_conjMat (A := A) g
    rw [hD, det_diagonal] at h1
    exact h1

end Diagonal

theorem exists_diagonalizing_slLift [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hpd : Nat.Coprime p d) (X : Subgroup (MulAut (projectiveSL d K)))
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXp : ∀ x ∈ X, x ^ p = 1)
    (hXI : ∀ x ∈ X, ∃ A : GL (Fin d) K, conjAut d K A = x) :
    ∃ A₀ : GL (Fin d) K,
      (∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0) ∧
      Nat.card X ≤ p ^ (d - 1) ∧
      (Nat.card X = p ^ (d - 1) → ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
        ∃ g ∈ slLift hd hpd X hXc, conjMat A₀ g = diagonal t) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have : NeZero p := ⟨hp.ne_zero⟩
  set Y := slLift hd hpd X hXc with hY
  obtain ⟨A₀, hA₀⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ Y
    (fun x hx y hy => slLift_comm hd hpd X hXc hx hy) (fun x hx => hx.1)
  have hdiag : ∀ g ∈ Y, ∀ i j, i ≠ j → conjMat A₀ g i j = 0 :=
    fun g hg i j hij => hA₀ g hg i j hij
  have hcard := card_slLift hd hpd X hXc hXp hXI
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  set S : Finset (Fin d) := {i₀}ᶜ with hSdef
  set R := Polynomial.nthRootsFinset p (1 : K) with hRdef
  have hmemR : ∀ c : K, c ∈ R ↔ c ^ p = 1 := fun c => Polynomial.mem_nthRootsFinset hp.pos 1
  let f : Y → (S → R) := fun g i =>
    ⟨conjMat A₀ g i i, (hmemR _).mpr ((conjMat_diag g.2.1 (hdiag g g.2)).2.1 i)⟩
  have hprod : ∀ g ∈ Y, conjMat A₀ g i₀ i₀ * ∏ i ∈ S, conjMat A₀ g i i = 1 := by
    intro g hg
    have e := Fintype.prod_eq_mul_prod_compl i₀ (fun i => conjMat A₀ g i i)
    rw [hSdef, ← e]
    exact (conjMat_diag hg.1 (hdiag g hg)).2.2
  have hmemS : ∀ i, i ≠ i₀ → i ∈ S := fun i hi => by simp [hSdef, hi]
  have hinj : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ hfgh
    have h1 : ∀ i ∈ S, conjMat A₀ g i i = conjMat A₀ h i i := fun i hi =>
      congrArg Subtype.val (congrFun hfgh ⟨i, hi⟩)
    have h3 : conjMat A₀ g i₀ i₀ = conjMat A₀ h i₀ i₀ := by
      have e1 := hprod g hg
      have e2 := hprod h hh
      rw [Finset.prod_congr rfl h1] at e1
      have hne : ∏ i ∈ S, conjMat A₀ h i i ≠ 0 := right_ne_zero_of_mul_eq_one e2
      exact mul_right_cancel₀ hne (e1.trans e2.symm)
    apply Subtype.ext
    apply conjMat_injective (A := A₀)
    rw [(conjMat_diag hg.1 (hdiag g hg)).1, (conjMat_diag hh.1 (hdiag h hh)).1]
    congr 1
    funext i
    by_cases hi : i = i₀
    · rw [hi]
      exact h3
    · exact h1 i (hmemS i hi)
  have hS : Nat.card S = d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hSdef, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hR : Nat.card R = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hζ.card_nthRootsFinset
  have htarget : Nat.card (S → R) = p ^ (d - 1) := by rw [Nat.card_fun, hS, hR]
  have hle : Nat.card Y ≤ p ^ (d - 1) := htarget ▸ Nat.card_le_card_of_injective f hinj
  refine ⟨A₀, hdiag, hcard ▸ hle, fun heq t ht htp => ?_⟩
  have hbij := hinj.bijective_of_nat_card_le (by rw [htarget, hcard, heq])
  obtain ⟨⟨g, hg⟩, hfg⟩ := hbij.2 (fun i => ⟨t i, (hmemR _).mpr (ht i)⟩)
  have h1 : ∀ i ∈ S, conjMat A₀ g i i = t i := fun i hi =>
    congrArg Subtype.val (congrFun hfg ⟨i, hi⟩)
  have h3 : conjMat A₀ g i₀ i₀ = t i₀ := by
    have e1 := hprod g hg
    have e2 : t i₀ * ∏ i ∈ S, t i = 1 := by
      rw [hSdef, ← Fintype.prod_eq_mul_prod_compl i₀ t]
      exact htp
    rw [Finset.prod_congr rfl h1] at e1
    have hne : ∏ i ∈ S, t i ≠ 0 := right_ne_zero_of_mul_eq_one e2
    exact mul_right_cancel₀ hne (e1.trans e2.symm)
  refine ⟨g, hg, ?_⟩
  rw [(conjMat_diag hg.1 (hdiag g hg)).1]
  congr 1
  funext i
  by_cases hi : i = i₀
  · rw [hi]
    exact h3
  · exact h1 i (hmemS i hi)

end CFSG.StandardType.TypeA
