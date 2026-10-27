module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34Unitary
public import CFSG.Quasithin.Background.HSU3Beta
public import CFSG.LieType.SeitzGeneration.UnitaryTwoPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open CFSG.LieType.BorelTits
open scoped Matrix

theorem k_U34Hermitian_holds : K_U34Hermitian := by
  intro K _ _ _ hK U hU
  classical
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  have : Fintype K := Fintype.ofFinite K
  let S := {x : K // bar 2 x = x}
  have hS4 : Nat.card S ≤ 4 := by
    have hcard : Nat.card S = (Finset.univ.filter (fun x : K => bar 2 x = x)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard]
    simpa using card_filter_bar_le (K := K) (n := 2) (by norm_num)
  by_cases hU0 : ∃ u : U, u ≠ 0
  · obtain ⟨u, hu0⟩ := hU0
    set uK : Fin 3 → K := (u : Fin 3 → K) with huK
    have hu0' : uK ≠ 0 := by simpa [huK] using hu0
    have huu : herm 2 uK uK = 0 := hU uK u.2
    have hfix : ∀ w : U, bar 2 (herm 2 uK (w : Fin 3 → K)) =
        herm 2 uK (w : Fin 3 → K) := by
      intro w
      have hsum : (uK + (w : Fin 3 → K)) ∈ U := U.add_mem u.2 w.2
      have h0 := hU _ hsum
      rw [herm_add_left, herm_add_right, herm_add_right, hU uK u.2, hU _ w.2,
        zero_add, add_zero] at h0
      have hwu : herm 2 uK (w : Fin 3 → K) = herm 2 (w : Fin 3 → K) uK :=
        CharTwo.add_eq_zero.mp h0
      rw [← herm_comm hK' uK (w : Fin 3 → K)]
      exact hwu.symm
    let f : U →+ K :=
      { toFun := fun w => herm 2 uK (w : Fin 3 → K)
        map_zero' := by simp [herm]
        map_add' := fun a b => by
          change herm 2 uK ((a : Fin 3 → K) + (b : Fin 3 → K)) =
            herm 2 uK (a : Fin 3 → K) + herm 2 uK (b : Fin 3 → K)
          rw [herm_add_right] }
    by_cases hf0 : ∀ w : U, f w = 0
    · have hf0' : ∀ w : U, herm 2 uK (w : Fin 3 → K) = 0 := fun w => hf0 w
      let g : U → K := fun w =>
        Classical.choose (eq_smul_of_isotropic (n := 2) hK' hu0' huu (hU _ w.2) (hf0' w))
      have hg : ∀ w : U, (w : Fin 3 → K) = g w • uK := fun w =>
        Classical.choose_spec
          (eq_smul_of_isotropic (n := 2) hK' hu0' huu (hU _ w.2) (hf0' w))
      have hinj : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        rw [hg a, hg b, hab]
      calc Nat.card U ≤ Nat.card K := Nat.card_le_card_of_injective g hinj
        _ = 16 := hK
    · push Not at hf0
      obtain ⟨w0, hw0⟩ := hf0
      have hkw0 : herm 2 uK (w0 : Fin 3 → K) ≠ 0 := by simpa [f] using hw0
      have hker_exists : ∀ w : f.ker, ∃ c : K,
          ((w : U) : Fin 3 → K) = c • uK ∧ bar 2 c = c := by
        intro w
        have hwmem : ((w : U) : Fin 3 → K) ∈ U := (w : U).2
        have hwker : herm 2 uK ((w : U) : Fin 3 → K) = 0 := by
          have := AddMonoidHom.mem_ker.mp w.2
          simpa [f] using this
        obtain ⟨c, hc⟩ :=
          eq_smul_of_isotropic (n := 2) hK' hu0' huu (hU _ hwmem) hwker
        refine ⟨c, hc, ?_⟩
        have hcU : c • uK ∈ U := by rw [← hc]; exact (w : U).2
        have hsum : (c • uK + (w0 : Fin 3 → K)) ∈ U := U.add_mem hcU w0.2
        have h0 := hU _ hsum
        have hexp : herm 2 (c • uK + (w0 : Fin 3 → K))
            (c • uK + (w0 : Fin 3 → K)) =
            (bar 2 c + c) * herm 2 uK (w0 : Fin 3 → K) := by
          rw [herm_add_left, herm_add_right, herm_add_right,
            herm_smul_left, herm_smul_right, herm_smul_left, herm_smul_right,
            herm_comm hK' uK (w0 : Fin 3 → K), hfix w0, huu, hU _ w0.2]
          ring
        rw [hexp] at h0
        have hz : bar 2 c + c = 0 := (mul_eq_zero.mp h0).resolve_right hkw0
        exact CharTwo.add_eq_zero.mp hz
      let gker : f.ker → S := fun w =>
        ⟨Classical.choose (hker_exists w), (Classical.choose_spec (hker_exists w)).2⟩
      have hker_le : Nat.card f.ker ≤ 4 := by
        have hinj : Function.Injective gker := by
          intro a b hab
          have ha := (Classical.choose_spec (hker_exists a)).1
          have hb := (Classical.choose_spec (hker_exists b)).1
          have hab' : Classical.choose (hker_exists a) =
              Classical.choose (hker_exists b) := congrArg Subtype.val hab
          apply Subtype.ext
          apply Subtype.ext
          rw [ha, hb, hab']
        calc Nat.card f.ker ≤ Nat.card S := Nat.card_le_card_of_injective gker hinj
          _ ≤ 4 := hS4
      let grange : f.range → S := fun y =>
        ⟨y.val, by
          obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp y.2
          rw [← hw]
          exact hfix w⟩
      have hrange_le : Nat.card f.range ≤ 4 := by
        have hinj : Function.Injective grange := by
          intro a b hab
          apply Subtype.ext
          exact congrArg (fun z : S => z.val) hab
        calc Nat.card f.range ≤ Nat.card S := Nat.card_le_card_of_injective grange hinj
          _ ≤ 4 := hS4
      have hcard : Nat.card U = Nat.card f.ker * Nat.card f.range :=
        (AddSubgroup.card_ker_mul_card_range f).symm
      rw [hcard]
      calc Nat.card f.ker * Nat.card f.range ≤ 4 * 4 := Nat.mul_le_mul hker_le hrange_le
        _ = 16 := by norm_num
  · push Not at hU0
    have hsub : Subsingleton U := ⟨fun a b => by rw [hU0 a, hU0 b]⟩
    calc Nat.card U ≤ Nat.card K :=
          Nat.card_le_card_of_injective (fun _ : U => (0 : K))
            (fun a b _ => hsub.elim a b)
      _ = 16 := hK

theorem k_U34NonsingularStab_holds : K_U34NonsingularStab := by
  intro K _ _ _ hK v hv hvns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  obtain ⟨ζ, hζord⟩ := exists_orderOf_eq_succ (K := K) (q := 4) hK' (by norm_num)
  have hζ5 : (ζ : K) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζord] at h
    exact congrArg (fun u : Kˣ => (u : K)) h
  have hζne : (ζ : K) ≠ 1 := by
    intro h
    have h1 : ζ = 1 := Units.ext h
    rw [h1] at hζord
    norm_num at hζord
  let σ : K ≃+* K := unitaryInvolution K 2 2
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 2) hK'
  have hζbar : σ (ζ : K) * (ζ : K) = 1 := by
    change bar 2 (ζ : K) * (ζ : K) = 1
    rw [bar_apply, show (2 : ℕ) ^ 2 = 4 by norm_num, ← pow_succ]
    simpa using hζ5
  obtain ⟨t, ht⟩ := exists_smul_herm_eq_one (K := K) (n := 2) (by norm_num) hK' hvns
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht
    simp [herm] at ht
  set b₀ : Fin 3 → K := t • v with hb₀
  have hb₀norm : CFSG.ClassicalGroups.Unitary.herm σ b₀ b₀ = 1 := by
    rw [hb₀]
    exact ht
  let d : Fin 3 → K := ![1, (ζ : K), (ζ : K) ^ 4]
  have hd : ∀ i, σ (d i) * d i = 1 := by
    intro i
    have h4 : σ ((ζ : K) ^ 4) * (ζ : K) ^ 4 = 1 := by
      rw [map_pow, ← mul_pow, hζbar, one_pow]
    fin_cases i
    · simp [d]
    · simpa [d] using hζbar
    · simpa [d] using h4
  have hprod : (ζ : K) * (ζ : K) ^ 4 = 1 := by
    rw [← pow_succ']
    simpa using hζ5
  have hdet : ∏ i, d i = 1 := by
    simp [d, Fin.prod_univ_three, hprod]
  let x₀ : CFSG.LieType.Universal.Unitary.SUid σ 3 :=
    CFSG.LieType.SeitzGeneration.UnitaryTwo.diagSU σ d hd hdet
  let e0 : Fin 3 → K := Pi.single 0 1
  let e1 : Fin 3 → K := Pi.single 1 1
  have hx0_e0 : x₀ • e0 = e0 := by
    funext i
    rw [CFSG.LieType.SeitzGeneration.UnitaryTwo.diagSU_smul]
    fin_cases i <;> simp [d, e0, Pi.single_apply]
  have hpow : ∀ (k : ℕ) (w : Fin 3 → K) (i : Fin 3),
      ((x₀ ^ k) • w) i = (d i) ^ k * w i := by
    intro k
    induction k with
    | zero =>
      intro w i
      simp
    | succ k ih =>
      intro w i
      rw [pow_succ', mul_smul, CFSG.LieType.SeitzGeneration.UnitaryTwo.diagSU_smul, ih]
      ring
  have hx0_pow : x₀ ^ 5 = 1 := by
    apply CFSG.ClassicalGroups.Unitary.ext_smul σ
    intro w
    funext i
    rw [hpow]
    have h4 : ((ζ : K) ^ 4) ^ 5 = 1 := by
      rw [← pow_mul, show 4 * 5 = 5 * 4 by norm_num, pow_mul, hζ5, one_pow]
    fin_cases i <;> simp [d, hζ5, h4]
  have hx0_ne : x₀ ≠ 1 := by
    intro h
    have h1 : ((x₀ • e1) 1) =
        (((1 : CFSG.LieType.Universal.Unitary.SUid σ 3) • e1) 1) := by rw [h]
    rw [CFSG.LieType.SeitzGeneration.UnitaryTwo.diagSU_smul] at h1
    simp [d, e1, Pi.single_apply] at h1
    exact hζne (congrArg Units.val h1)
  have hx0_ord : orderOf x₀ = 5 := orderOf_eq_prime hx0_pow hx0_ne
  have hex : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1 :=
    CFSG.ClassicalGroups.Unitary.exists_norm_ne_one (p := 2) (f := 2) hK' (by norm_num)
  have he0 : CFSG.ClassicalGroups.Unitary.herm σ e0 e0 = 1 := by
    simp [CFSG.ClassicalGroups.Unitary.herm, e0, Pi.single_apply]
  obtain ⟨g, _hgT, hg⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_norm_one (K := K) (σ := σ) (n := 3) hσ
    (Or.inr ⟨by norm_num, hex⟩)
    (x := e0) (y := b₀) he0 hb₀norm
  let x : CFSG.LieType.Universal.Unitary.SUid σ 3 := g * x₀ * g⁻¹
  have hsem : SemiconjBy g x₀ x := by
    unfold SemiconjBy
    rw [show x = g * x₀ * g⁻¹ from rfl]
    group
  have hx_ord : orderOf x = 5 := by
    rw [← SemiconjBy.orderOf_eq g hsem]
    exact hx0_ord
  have hg_inv : g⁻¹ • b₀ = e0 := by
    rw [← hg]
    simp
  have hx_b0 : x • b₀ = b₀ := by
    rw [show x = g * x₀ * g⁻¹ from rfl, mul_smul, mul_smul, hg_inv, hx0_e0, hg]
  have h1 : x • (t • v) = t • v := by rw [← hb₀, hx_b0]
  have h2 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (t • v) = t • v := by
    have h1' : (x : GL (Fin 3) K) • (t • v) = t • v := by
      simpa only [Subgroup.smul_def] using h1
    exact h1'
  rw [Matrix.mulVec_smul] at h2
  have hxv : (x : GL (Fin 3) K) *ᵥ v = v :=
    smul_right_injective (Fin 3 → K) ht0 h2
  have hEq : CFSG.LieType.Universal.Unitary.SUid σ 3 = StatedSU 3 4 K :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 2) hK' 3
  let xS : StatedSU 3 4 K := ⟨(x : GL (Fin 3) K), by rw [← hEq]; exact x.2⟩
  refine ⟨xS, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe xS]
    change orderOf (x : GL (Fin 3) K) = 5
    rw [Subgroup.orderOf_coe x]
    exact hx_ord
  · simpa using hxv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
