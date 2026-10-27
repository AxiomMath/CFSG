module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreModel
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_SU3EightTorusE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 3 → 3 ∣ Nat.card (Subgroup.center X) →
    ∃ (x : X) (E : Subgroup X), orderOf x = 9 ∧ x ^ 3 ∈ Subgroup.center X ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, e * x = x * e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem exists_mulEquiv_unitarySU_three_of_isSU3
    {X : Type} [Group X] [Finite X]
    (hX : IsSU3 X 3) (hZ : 3 ∣ Nat.card (Subgroup.center X)) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 3 F),
      Nat.card F = 64 ∧ Nat.card (Subgroup.center X) = 3 ∧
        Nonempty (unitarySU 2 3 F 3 ≃* X) := by
  have hz : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ
    omega
  obtain ⟨-, F, hField, hFinite, hFcard, ⟨e₀⟩⟩ :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hX.2
  letI := hField
  have : Finite F := hFinite
  have hFc : Nat.card F = (2 ^ 3) ^ 2 := hFcard
  let hd : UnitaryFieldData 2 3 F := unitaryFieldDataOfCard hFc
  have e : X ⧸ Subgroup.center X ≃* unitaryPSU hd 3 :=
    e₀.trans (unitaryPSUEquivStated hFc).symm
  obtain ⟨ψ, -⟩ :=
    KSU3Core.exists_mulEquiv_unitarySU_three_compat hd (by norm_num) hX.1.1 e hz
  refine ⟨F, hField, hd, ?_, ?_, ⟨ψ⟩⟩
  · rw [hFcard]
    norm_num
  · have h1 : Nat.card (Subgroup.center X) =
        Nat.card (Subgroup.center (unitarySU 2 3 F 3)) := by
      rw [← Subgroup.map_center_eq ψ]
      exact Subgroup.card_map_of_injective ψ.injective
    rw [h1, CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := hd) (by norm_num),
      card_unitaryScalars hd (n := 3) (by norm_num)]
    norm_num

private lemma inv_mul_self_pow_three {M : Type} [CommGroup M] {ζ : M} (hζ : ζ ^ 9 = 1) :
    (ζ⁻¹ * ζ⁻¹) ^ 3 = ζ ^ 3 := by
  have h : ζ ^ 3 * (ζ ^ 3 * ζ ^ 3) = 1 := by
    rw [← pow_add, ← pow_add, show 3 + (3 + 3) = 9 by norm_num]
    exact hζ
  calc (ζ⁻¹ * ζ⁻¹) ^ 3 = ((ζ * ζ) ^ 3)⁻¹ := by
        rw [show ζ⁻¹ * ζ⁻¹ = (ζ * ζ)⁻¹ by group, inv_pow]
    _ = (ζ ^ 3 * ζ ^ 3)⁻¹ := by rw [mul_pow]
    _ = ζ ^ 3 := inv_eq_of_mul_eq_one_left h

theorem exists_unitarySU_three_orderOf_nine_elemAbelian {F : Type} [Field F]
    (h : UnitaryFieldData 2 3 F) :
    ∃ (x : unitarySU 2 3 F 3) (E : Subgroup (unitarySU 2 3 F 3)),
      orderOf x = 9 ∧ x ^ 3 ∈ Subgroup.center (unitarySU 2 3 F 3) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, e * x = x * e := by
  classical
  obtain ⟨ζ, hζ⟩ := KSFourU.exists_orderOf_nine h
  have hζ9 : ζ ^ 9 = 1 := KSFourU.pow_nine_eq_one hζ
  let a : Fˣ := ζ ^ 3
  have ha3 : a ^ 3 = 1 := by
    change (ζ ^ 3) ^ 3 = 1
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, hζ9]
  have ha9 : a ^ 9 = 1 := by
    change (ζ ^ 3) ^ 9 = 1
    rw [← pow_mul, show 3 * 9 = 9 * 3 by norm_num, pow_mul, hζ9, one_pow]
  have haord : orderOf a = 3 := by
    have h := orderOf_pow_of_dvd (x := ζ) (n := 3) (by norm_num) (by rw [hζ]; norm_num)
    rw [hζ] at h
    simpa using h
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1] at haord
    simp at haord
  let u : Fin 3 → Fˣ := ![ζ, ζ, ζ⁻¹ * ζ⁻¹]
  have hu9 : ∀ k, u k ^ 9 = 1 := by
    intro k
    fin_cases k
    · simpa [u] using hζ9
    · simpa [u] using hζ9
    · change u 2 ^ 9 = 1
      rw [show u 2 = ζ⁻¹ * ζ⁻¹ from rfl,
        show ζ⁻¹ * ζ⁻¹ = (ζ * ζ)⁻¹ by group, inv_pow, mul_pow, hζ9]
      simp
  have hudet : u 0 * u 1 * u 2 = 1 := by
    show ζ * ζ * (ζ⁻¹ * ζ⁻¹) = 1
    group
  let x : unitarySU 2 3 F 3 := ⟨KSFourU.diagGL u, KSFourU.diagGL_mem_SU h hu9 hudet⟩
  have hxmat : (x : GL (Fin 3) F) = KSFourU.diagGL u := rfl
  have hx9 : x ^ 9 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, Subgroup.coe_one, hxmat, ← map_pow]
    have hu : u ^ 9 = 1 := by
      funext k
      exact hu9 k
    rw [hu, map_one]
  have hx3ne : x ^ 3 ≠ 1 := by
    intro h3
    have h00 : (((x ^ 3 : unitarySU 2 3 F 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
      rw [h3]
      rfl
    rw [SubgroupClass.coe_pow, hxmat, ← map_pow] at h00
    rw [KSFourU.coe_diagGL, Matrix.diagonal_apply_eq] at h00
    have hq : ((u ^ 3 : Fin 3 → Fˣ) 0 : F) = (ζ : F) ^ 3 := by
      rw [Pi.pow_apply, show u 0 = ζ from rfl, Units.val_pow_eq_pow_val]
    rw [hq] at h00
    have hζ3u : ζ ^ 3 = 1 := by
      apply Units.ext
      simpa using h00
    have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hζ3u
    rw [hζ] at hdvd
    norm_num at hdvd
  have hxord : orderOf x = 9 := by
    have hdvd : orderOf x ∣ 9 := orderOf_dvd_iff_pow_eq_one.mpr hx9
    have hne1 : orderOf x ≠ 1 := by
      intro h1
      exact hx3ne (by rw [orderOf_eq_one_iff.mp h1, one_pow])
    have hne3 : orderOf x ≠ 3 := by
      intro h3
      apply hx3ne
      have h := pow_orderOf_eq_one x
      rwa [h3] at h
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (m := 2) Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      exact hne1 (by rw [hk]; norm_num)
    · exfalso
      exact hne3 (by rw [hk]; norm_num)
    · rw [hk]
      norm_num
  have hu3 : u ^ 3 = ![a, a, a] := by
    funext k
    fin_cases k
    · simp [u, a]
    · simp [u, a]
    · simp only [Pi.pow_apply, u, a, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact inv_mul_self_pow_three hζ9
  have hnorma : h.norm (a : F) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    calc (a : F) * (a : F) ^ 2 ^ 3 = (a : F) ^ 9 := by
          norm_num
          ring
      _ = 1 := by rw [← Units.val_pow_eq_pow_val, ha9, Units.val_one]
  have hx3mat : ((x ^ 3 : unitarySU 2 3 F 3) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) a := by
    rw [SubgroupClass.coe_pow, hxmat, ← map_pow, hu3]
    apply Units.ext
    rw [KSFourU.coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.scalar_apply]
  have hx3cen : x ^ 3 ∈ Subgroup.center (unitarySU 2 3 F 3) :=
    unitaryScalars_le_center h 3
      ((mem_unitaryScalars).mpr ⟨a, hnorma, ha3, hx3mat⟩)
  let v₁ : Fin 3 → Fˣ := ![a, a⁻¹, 1]
  let v₂ : Fin 3 → Fˣ := ![1, a, a⁻¹]
  have hv1det : v₁ 0 * v₁ 1 * v₁ 2 = 1 := by
    show a * a⁻¹ * 1 = 1
    group
  have hv2det : v₂ 0 * v₂ 1 * v₂ 2 = 1 := by
    show 1 * a * a⁻¹ = 1
    group
  have hv1pow : ∀ k, v₁ k ^ 9 = 1 := by
    intro k
    fin_cases k <;> simp [v₁, ha9]
  have hv2pow : ∀ k, v₂ k ^ 9 = 1 := by
    intro k
    fin_cases k <;> simp [v₂, ha9]
  let e₁ : unitarySU 2 3 F 3 :=
    ⟨KSFourU.diagGL v₁, KSFourU.diagGL_mem_SU h hv1pow hv1det⟩
  let e₂ : unitarySU 2 3 F 3 :=
    ⟨KSFourU.diagGL v₂, KSFourU.diagGL_mem_SU h hv2pow hv2det⟩
  have he1mat : (e₁ : GL (Fin 3) F) = KSFourU.diagGL v₁ := rfl
  have he2mat : (e₂ : GL (Fin 3) F) = KSFourU.diagGL v₂ := rfl
  have he₁3 : e₁ ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, Subgroup.coe_one, he1mat, ← map_pow]
    have hv : v₁ ^ 3 = 1 := by
      funext k
      fin_cases k <;> simp [v₁, ha3]
    rw [hv, map_one]
  have he₂3 : e₂ ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, Subgroup.coe_one, he2mat, ← map_pow]
    have hv : v₂ ^ 3 = 1 := by
      funext k
      fin_cases k <;> simp [v₂, ha3]
    rw [hv, map_one]
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he1mat, he2mat, ← map_mul, ← map_mul]
    congr 1
    funext k
    fin_cases k <;> simp [v₁, v₂] <;> group
  have he1ne : e₁ ≠ 1 := by
    intro h1
    have h00 : (((e₁ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
      rw [h1]
      rfl
    rw [he1mat, KSFourU.coe_diagGL, Matrix.diagonal_apply_eq] at h00
    have : (a : F) = 1 := by simpa [v₁] using h00
    exact ha1 (Units.ext this)
  have he2ne : e₂ ≠ 1 := by
    intro h1
    have h00 : (((e₂ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by
      rw [h1]
      rfl
    rw [he2mat, KSFourU.coe_diagGL, Matrix.diagonal_apply_eq] at h00
    have : (a : F) = 1 := by simpa [v₂] using h00
    exact ha1 (Units.ext this)
  have he1ord : orderOf e₁ = 3 := by
    have hdvd : orderOf e₁ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr he₁3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) he1ne
    · exact h
  have he2ord : orderOf e₂ = 3 := by
    have hdvd : orderOf e₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr he₂3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) he2ne
    · exact h
  have hentry₁ : ∀ i : ℤ, (((e₁ ^ i : unitarySU 2 3 F 3) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = (a : F) ^ i := by
    intro i
    rw [SubgroupClass.coe_zpow, he1mat, ← map_zpow, KSFourU.coe_diagGL,
      Matrix.diagonal_apply_eq]
    simp [v₁]
  have hentry₂ : ∀ j : ℤ, (((e₂ ^ j : unitarySU 2 3 F 3) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    intro j
    rw [SubgroupClass.coe_zpow, he2mat, ← map_zpow, KSFourU.coe_diagGL,
      Matrix.diagonal_apply_eq]
    simp [v₂]
  have hdisj : Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
    rw [Subgroup.mem_bot]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw2
    have h00 : (a : F) ^ i = 1 := by
      calc (a : F) ^ i = (((e₁ ^ i : unitarySU 2 3 F 3) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) 0 0 := (hentry₁ i).symm
        _ = (((w : unitarySU 2 3 F 3) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) 0 0 := by rw [hi]
        _ = (((e₂ ^ j : unitarySU 2 3 F 3) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) 0 0 := by rw [hj]
        _ = 1 := hentry₂ j
    have h00u : a ^ i = 1 := by
      apply Units.ext
      simpa using h00
    have h3i : (3 : ℤ) ∣ i := by
      have h9 : (orderOf a : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.mpr h00u
      simpa [haord] using h9
    obtain ⟨k, hk⟩ := h3i
    rw [← hi, hk, zpow_mul]
    have h3 : e₁ ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, he₁3]
    rw [h3, one_zpow]
  have hcommute : ∀ y ∈ Subgroup.zpowers e₁, ∀ z ∈ Subgroup.zpowers e₂, Commute y z := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_zpow hcomm m n
  have hEel : IsElemAbelian 3 (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) :=
    (isElemAbelian_zpowers he₁3).sup_of_commute (isElemAbelian_zpowers he₂3)
      (fun y hy z hz => hcommute y hy z hz)
  have hEcard : Nat.card ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) = 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers e₁) (Subgroup.zpowers e₂)
      hcommute hdisj, Nat.card_zpowers, Nat.card_zpowers, he1ord, he2ord]
  have hEx : ∀ e ∈ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂, e * x = x * e := by
    intro e he
    rw [CFSG.mem_sup_of_commute (A := Subgroup.zpowers e₁) (B := Subgroup.zpowers e₂)
      hcommute] at he
    obtain ⟨y, hy, z, hz, rfl⟩ := he
    have hyx : y * x = x * y := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, SubgroupClass.coe_zpow, hxmat, he1mat,
        ← map_zpow, ← map_mul, ← map_mul]
      congr 1
      funext k
      fin_cases k <;> simp [u, v₁] <;> ac_rfl
    have hzx : z * x = x * z := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, SubgroupClass.coe_zpow, hxmat, he2mat,
        ← map_zpow, ← map_mul, ← map_mul]
      congr 1
      funext k
      fin_cases k <;> simp [u, v₂] <;> ac_rfl
    calc (y * z) * x = y * (z * x) := by group
      _ = y * (x * z) := by rw [hzx]
      _ = (y * x) * z := by group
      _ = (x * y) * z := by rw [hyx]
      _ = x * (y * z) := by group
  refine ⟨x, Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂, hxord, hx3cen, hEel,
    hEcard, hEx⟩

theorem k_SU3EightTorusE9_holds :
    S17.K_SU3EightTorusE9 := by
  intro X _ _ hX hZ
  obtain ⟨F, hF, hd, -, -, ⟨ψ⟩⟩ := exists_mulEquiv_unitarySU_three_of_isSU3 hX hZ
  letI := hF
  obtain ⟨x, E, hxord, hx3, hEel, hEcard, hEx⟩ :=
    exists_unitarySU_three_orderOf_nine_elemAbelian hd
  refine ⟨ψ x, E.map ψ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ψ.orderOf_eq x).trans hxord
  · have hmem : ψ (x ^ 3) ∈ Subgroup.center X := by
      rw [← Subgroup.map_center_eq ψ]
      exact Subgroup.mem_map_of_mem _ hx3
    simpa using hmem
  · exact hEel.map _
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact hEcard
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    simpa using congrArg ψ (hEx e₀ he₀)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
