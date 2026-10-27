module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Matrix

private theorem pdw_three_ne_zero {K : Type} [Field K] (hK : ringChar K ≠ 3) :
    (3 : K) ≠ 0 := by
  intro h
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).mp h
  have hp : Nat.Prime 3 := by norm_num
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · have h10 : (1 : K) = 0 := by
      simpa using (ringChar.spec K (1 : ℕ)).mpr (by rw [h1])
    exact one_ne_zero h10
  · exact hK h3

private theorem pdw_ofAdd_nsmul {α : Type*} [AddCommMonoid α] (e : α) (m : ℕ) :
    Multiplicative.ofAdd (m • e) = Multiplicative.ofAdd e ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [succ_nsmul]
    change Multiplicative.ofAdd (m • e) * Multiplicative.ofAdd e =
      Multiplicative.ofAdd e ^ (m + 1)
    rw [ih, pow_succ]

private theorem pdw_char_add {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (x y : ZMod 3) : ggPDChar ζ (x + y) = ggPDChar ζ x * ggPDChar ζ y := by
  simp only [ggPDChar]
  rw [ZMod.val_add]
  rw [← pow_eq_pow_mod (x.val + y.val) hζ.pow_eq_one]
  exact pow_add ζ x.val y.val

private theorem pdw_domain_pow_three (v : Multiplicative (Fin 4 → ZMod 3)) : v ^ 3 = 1 := by
  change (3 : ℕ) • (Multiplicative.toAdd v) = 0
  ext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

private theorem pdw_decomp (v : Multiplicative (Fin 4 → ZMod 3)) :
    v = ∏ k : Fin 4, (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) ^
      (Multiplicative.toAdd v k).val := by
  have h1 : Multiplicative.toAdd v =
      ∑ k : Fin 4, Pi.single k (Multiplicative.toAdd v k) :=
    (Finset.univ_sum_single (Multiplicative.toAdd v)).symm
  change Multiplicative.ofAdd (Multiplicative.toAdd v) = _
  conv_lhs => rw [h1]
  rw [show Multiplicative.ofAdd (∑ k : Fin 4,
        Pi.single k (Multiplicative.toAdd v k)) =
      ∏ k : Fin 4,
        Multiplicative.ofAdd (Pi.single k (Multiplicative.toAdd v k))
      from rfl]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h2 : Pi.single k (Multiplicative.toAdd v k) =
      (Multiplicative.toAdd v k) • (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3) := by
    simpa only [smul_eq_mul, mul_one] using
      (Pi.single_smul (f := fun _ : Fin 4 => ZMod 3) k
        (Multiplicative.toAdd v k) (1 : ZMod 3))
  rw [h2]
  conv_lhs => rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd v k)]
  rw [Nat.cast_smul_eq_nsmul (ZMod 3) (Multiplicative.toAdd v k).val
      (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3)]
  exact pdw_ofAdd_nsmul (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3)
    (Multiplicative.toAdd v k).val

private theorem pdw_char_exists {K : Type} [Field K] {d : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3)
    (ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K)
    (b : Module.Basis (Fin d) K (Fin d → K))
    (dd : Matrix.GeneralLinearGroup (Fin d) K → Fin d → K)
    (hb : ∀ x ∈ ρ.range, ∀ a, (x : Matrix (Fin d) (Fin d) K) *ᵥ b a = dd x a • b a)
    (hexp : ∀ x ∈ ρ.range, x ^ 3 = 1) (j : Fin d) :
    ∃ u : Fin 4 → ZMod 3, ∀ v, dd (ρ v) j =
      ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd v) := by
  classical
  have hcube : ∀ k : Fin 4,
      dd (ρ (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))) j ^ 3 = 1 := by
    intro k
    exact CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩) (hexp _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)) j
  have hgen : ∀ k : Fin 4, ∃ r : ZMod 3,
      ggPDChar ζ r = dd (ρ (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))) j := by
    intro k
    obtain ⟨i, hi_lt, hi_eq⟩ := hζ.eq_pow_of_pow_eq_one (hcube k)
    exact ⟨(i : ZMod 3), by rw [ggPDChar, ZMod.val_cast_of_lt hi_lt]; exact hi_eq⟩
  let u : Fin 4 → ZMod 3 := fun k => Classical.choose (hgen k)
  have hu : ∀ k : Fin 4, ggPDChar ζ (u k) =
      dd (ρ (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))) j := fun k =>
    Classical.choose_spec (hgen k)
  refine ⟨u, ?_⟩
  intro v
  have hne_dd : ∀ v, dd (ρ v) j ≠ 0 := by
    intro v h0
    have h1 := CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb
      (MonoidHom.mem_range.mpr ⟨v, rfl⟩)
      (hexp (ρ v) (MonoidHom.mem_range.mpr ⟨v, rfl⟩)) j
    rw [h0] at h1
    norm_num at h1
  have hχmul : ∀ v w, dd (ρ (v * w)) j = dd (ρ v) j * dd (ρ w) j := by
    intro v w
    have h := CFSG.RankThree.PartTwo.Sec4.eigen_mul hb (x := ρ v) (y := ρ w)
      (MonoidHom.mem_range.mpr ⟨v, rfl⟩) (MonoidHom.mem_range.mpr ⟨w, rfl⟩) j
    simpa only [map_mul] using h
  have hχone : dd (ρ 1) j = 1 := by
    rw [map_one]
    exact CFSG.RankThree.PartTwo.Sec4.eigen_one hb j
  let χ : Multiplicative (Fin 4 → ZMod 3) →* Kˣ :=
    { toFun := fun v => Units.mk0 (dd (ρ v) j) (hne_dd v)
      map_one' := Units.ext hχone
      map_mul' := fun v w => Units.ext (hχmul v w) }
  have hne_eta : ∀ v, ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd v) ≠ 0 := by
    intro v
    rw [ggPDChar]
    exact pow_ne_zero _ (hζ.ne_zero (by norm_num))
  let η : Multiplicative (Fin 4 → ZMod 3) →* Kˣ :=
    { toFun := fun v => Units.mk0 (ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd v)) (hne_eta v)
      map_one' := by
        apply Units.ext
        show ggPDChar ζ (u ⬝ᵥ (0 : Fin 4 → ZMod 3)) = 1
        simp [ggPDChar]
      map_mul' := by
        intro v w
        apply Units.ext
        change ggPDChar ζ (u ⬝ᵥ (Multiplicative.toAdd v + Multiplicative.toAdd w)) =
          ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd v) *
            ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd w)
        rw [dotProduct_add, pdw_char_add hζ] }
  have hpoint : ∀ v, χ v = η v := by
    intro v
    rw [pdw_decomp v]
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_pow]
    congr 1
    apply Units.ext
    change dd (ρ (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))) j =
      ggPDChar ζ (u ⬝ᵥ (Pi.single k (1 : ZMod 3) : Fin 4 → ZMod 3))
    rw [dotProduct_single, mul_one]
    exact (hu k).symm
  have hχη : χ = η := MonoidHom.ext hpoint
  have h1 : χ v = η v :=
    congrArg (fun f : Multiplicative (Fin 4 → ZMod 3) →* Kˣ => f v) hχη
  have h2 : (χ v : K) = (η v : K) := congrArg (fun z : Kˣ => (z : K)) h1
  exact h2

theorem ggPD_weights {K : Type} [Field K] [IsAlgClosed K] (hK : ringChar K ≠ 3) {d : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3)
    (ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K) :
    ∃ (b : Module.Basis (Fin d) K (Fin d → K)) (u : Fin d → (Fin 4 → ZMod 3)),
      ∀ (v : Multiplicative (Fin 4 → ZMod 3)) (j : Fin d),
        (ρ v : Matrix (Fin d) (Fin d) K).mulVec (b j) =
          ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd v) • b j := by
  classical
  have h3 : (3 : K) ≠ 0 := pdw_three_ne_zero hK
  have hcomm : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hexp : ∀ x ∈ ρ.range, x ^ 3 = 1 := by
    rintro x ⟨v, rfl⟩
    rw [← map_pow, pdw_domain_pow_three v, map_one]
  obtain ⟨b, dd, hb⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_common_eigenbasis_pow_three h3 ρ.range hcomm hexp
  have hchar : ∀ j : Fin d, ∃ u : Fin 4 → ZMod 3, ∀ v, dd (ρ v) j =
      ggPDChar ζ (u ⬝ᵥ Multiplicative.toAdd v) := fun j =>
    pdw_char_exists hζ ρ b dd hb hexp j
  choose u hu using hchar
  refine ⟨b, u, ?_⟩
  intro v j
  rw [hb (ρ v) ⟨v, rfl⟩ j, hu j v]

end CFSG.StandardType

end
