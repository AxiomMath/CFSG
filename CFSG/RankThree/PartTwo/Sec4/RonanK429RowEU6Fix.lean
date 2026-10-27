module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6Lift
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEKrylov

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace U6

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Matrix
open scoped Matrix

theorem matC_scalar (c : F4ˣ) :
    matC (GeneralLinearGroup.scalar (Fin 6) c) = Matrix.scalar (Fin 6) (eK.symm c) := by
  rw [matC_apply, GeneralLinearGroup.coe_scalar, Φ_scalar]

theorem mem_GU6_of_mem_S6 {g : GL (Fin 6) F4} (hg : g ∈ S6) : g ∈ GU6 :=
  ((mem_gramSU_iff_unitary uData).mp hg).1

theorem uni_matC {g : GL (Fin 6) F4} (hg : g ∈ GU6) : Uni (matC g) := by
  rw [matC_apply]
  exact uni_of_mem_GU6 hg

theorem conj6_eq_one_of_matC {B : GU6} {d : F4c}
    (h : matC (B : GL (Fin 6) F4) = Matrix.scalar (Fin 6) d) : conj6 B = 1 := by
  have hB : ((B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.scalar (Fin 6) (eK d) := by
    apply Φ.injective
    rw [← matC_apply, h, Φ_scalar, RingEquiv.symm_apply_apply]
  have hd : eK d ≠ 0 := by
    intro h0
    have h1 := (B : GL (Fin 6) F4).mul_inv
    rw [hB, h0, map_zero, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hBu : B = scalarGU6 (Units.mk0 (eK d) hd) := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_scalarGU6, GeneralLinearGroup.coe_scalar, Units.val_mk0, hB]
  rw [hBu, conj6_scalarGU6]

theorem exists_pow_three_eq_scalar {A : GU6} (h3 : conj6 A ^ 3 = 1) :
    ∃ c : F4ˣ, (A : GL (Fin 6) F4) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c := by
  have hk : A ^ 3 ∈ conj6.ker := by rw [MonoidHom.mem_ker, map_pow, h3]
  rw [ker_conj6] at hk
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hk
  exact ⟨c, by rw [← Subgroup.coe_pow, ← hc, coe_scalarGU6]⟩

theorem eq_scalar_of_commute_y7 {B : GL (Fin 6) F4} (hB : B ∈ GU6) (hc : B * y7G = y7G * B)
    (h3 : B ^ 3 = 1) : ∃ d : F4c, matC B = Matrix.scalar (Fin 6) d := by
  have hX : matC B * y7C = y7C * matC B := by
    have h := congrArg matC hc
    rwa [map_mul, map_mul, matC_y7G] at h
  have heq := eq_sum_of_commute (kr := kr7) (kr' := kr7i) (v := e0) pw7_eq (fun _ _ => rfl)
    kr7i_mul_kr7 hX
  have key := check7 (matC B *ᵥ e0)
  unfold Check7 at key
  rw [← heq] at key
  exact key (uni_matC hB) (by rw [← map_pow, h3, map_one])

theorem trace_ne_zero_of_commute_y11 {B : GL (Fin 6) F4} (hB : B ∈ GU6)
    (hc : B * y11G = y11G * B) (h3 : ∃ c : F4ˣ, B ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    (hns : ∀ d : F4c, matC B ≠ Matrix.scalar (Fin 6) d) : (matC B).trace ≠ 0 := by
  have hX : matC B * y11C = y11C * matC B := by
    have h := congrArg matC hc
    rwa [map_mul, map_mul, matC_y11G] at h
  have heq := eq_sum_of_commute (kr := kr11) (kr' := kr11i) (v := e0) pw11_eq (fun _ _ => rfl)
    kr11i_mul_kr11 hX
  have key := check11 (matC B *ᵥ e0)
  unfold Check11 at key
  rw [← heq] at key
  obtain ⟨c, hc3⟩ := h3
  exact key (uni_matC hB) ⟨eK.symm c, by rw [← map_pow, hc3, matC_scalar]⟩ hns

theorem exists_ext6_of_commute_y5 {X : Matrix (Fin 6) (Fin 6) F4c} (hX : X * y5C = y5C * X) :
    ∃ P M, X = ext6 P M ∧ P = ∑ j, (kr4i *ᵥ (P *ᵥ e40)) j • pw4 j := by
  have hd : X * Matrix.diagonal d6 = Matrix.diagonal d6 * X := by
    rw [diagonal_d6_eq]
    exact commute_sum_pow hX 5
  obtain ⟨P, M, hb⟩ : ∃ P M, X = ext6 P M := ⟨_, _, eq_ext6_of_commute hd⟩
  subst hb
  refine ⟨P, M, rfl, ?_⟩
  rw [y5C_eq, ext6_mul, ext6_mul] at hX
  exact eq_sum_of_commute (kr := kr4) (kr' := kr4i) (v := e40) pw4_eq (fun _ _ => rfl)
    kr4i_mul_kr4 (ext6_injective hX).1

theorem cube_eq_one_of_ext6 {P : Matrix (Fin 4) (Fin 4) F4c} {M : Matrix (Fin 2) (Fin 2) F4c}
    (hP : P = ∑ j, (kr4i *ᵥ (P *ᵥ e40)) j • pw4 j) (hU : Uni P) {c : F4c}
    (h3 : ext6 P M ^ 3 = Matrix.scalar (Fin 6) c) : c = 1 ∧ P ^ 3 = 1 ∧ M ^ 3 = 1 := by
  rw [ext6_pow, scalar_ext6] at h3
  have h5a := check5a (P *ᵥ e40)
  rw [← hP] at h5a
  have hP1 := h5a hU ⟨_, (ext6_injective h3).1⟩
  have hc1 : c = 1 := by
    have h := congrFun (congrFun ((ext6_injective h3).1.symm.trans hP1) 0) 0
    rwa [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  refine ⟨hc1, hP1, ?_⟩
  rw [(ext6_injective h3).2, hc1, map_one]

theorem pow_three_eq_one_of_commute_y5 {B : GL (Fin 6) F4} (hB : B ∈ GU6)
    (hc : B * y5G = y5G * B) (h3 : ∃ c : F4ˣ, B ^ 3 = GeneralLinearGroup.scalar (Fin 6) c) :
    B ^ 3 = 1 := by
  have hX : matC B * y5C = y5C * matC B := by
    have h := congrArg matC hc
    rwa [map_mul, map_mul, matC_y5G] at h
  obtain ⟨P, M, hb, hP⟩ := exists_ext6_of_commute_y5 hX
  have hU : Uni P ∧ Uni M := uni_ext6 (by rw [← hb]; exact uni_matC hB)
  obtain ⟨c, hc3⟩ := h3
  have hX3 : ext6 P M ^ 3 = Matrix.scalar (Fin 6) (eK.symm c) := by
    rw [← hb, ← map_pow, hc3, matC_scalar]
  have hc1 := (cube_eq_one_of_ext6 hP hU.1 hX3).1
  apply matC_injective
  rw [hc3, matC_scalar, hc1, map_one, map_one]

theorem trace_eq_zero_of_commute_y5 {B H : GL (Fin 6) F4} (hB : B ∈ GU6) (hH : H ∈ GU6)
    (hc : B * y5G = y5G * B) (hcH : H * y5G = y5G * H) (hH2 : H ^ 2 = 1) (hH1 : H ≠ 1)
    (hBH : B * H = H * B) (h3 : ∃ c : F4ˣ, B ^ 3 = GeneralLinearGroup.scalar (Fin 6) c) :
    (matC B).trace = 0 := by
  have hX : matC B * y5C = y5C * matC B := by
    have h := congrArg matC hc
    rwa [map_mul, map_mul, matC_y5G] at h
  have hXH : matC H * y5C = y5C * matC H := by
    have h := congrArg matC hcH
    rwa [map_mul, map_mul, matC_y5G] at h
  obtain ⟨P, M, hb, hP⟩ := exists_ext6_of_commute_y5 hX
  obtain ⟨P', M', hb', hP'⟩ := exists_ext6_of_commute_y5 hXH
  have hU : Uni P ∧ Uni M := uni_ext6 (by rw [← hb]; exact uni_matC hB)
  have hU' : Uni P' ∧ Uni M' := uni_ext6 (by rw [← hb']; exact uni_matC hH)
  obtain ⟨c, hc3⟩ := h3
  have hX3 : ext6 P M ^ 3 = Matrix.scalar (Fin 6) (eK.symm c) := by
    rw [← hb, ← map_pow, hc3, matC_scalar]
  obtain ⟨-, hP1, hM3⟩ := cube_eq_one_of_ext6 hP hU.1 hX3
  have h5b := check5b (P *ᵥ e40)
  rw [← hP] at h5b
  obtain ⟨a, ha⟩ := h5b hU.1 hP1
  have hH2' : ext6 (P' ^ 2) (M' ^ 2) = ext6 1 1 := by
    rw [← ext6_pow, ← hb', ← map_pow, hH2, map_one, ext6_one]
  have h5c := check5c (P' *ᵥ e40)
  rw [← hP'] at h5c
  have hP'1 := h5c hU'.1 (ext6_injective hH2').1
  have hM'1 : M' ≠ 1 := by
    rintro rfl
    apply hH1
    apply matC_injective
    rw [hb', hP'1, ext6_one, map_one]
  have hcomm : M * M' = M' * M := by
    have h := congrArg matC hBH
    rw [map_mul, map_mul, hb, hb', ext6_mul, ext6_mul] at h
    exact (ext6_injective h).2
  obtain ⟨b, hb2⟩ := check2 M M' hU.2 hU'.2 hM3 (ext6_injective hH2').2 hM'1 hcomm
  rw [hb, ha, hb2]
  exact trace_ext6_scalar a b

theorem conj_mem_GU6 {s : GL (Fin 6) F4} (hs : s ∈ S6) {A : GL (Fin 6) F4} (hA : A ∈ GU6) :
    MulAut.conj s A ∈ GU6 := by
  have hs' := mem_GU6_of_mem_S6 hs
  rw [MulAut.conj_apply]
  exact mul_mem (mul_mem hs' hA) (inv_mem hs')

theorem conj_pow_three_scalar (s : GL (Fin 6) F4) {A : GL (Fin 6) F4}
    (h3 : ∃ c : F4ˣ, A ^ 3 = GeneralLinearGroup.scalar (Fin 6) c) :
    ∃ c : F4ˣ, (MulAut.conj s A) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c := by
  obtain ⟨c, hc⟩ := h3
  refine ⟨c, ?_⟩
  rw [← map_pow, hc, MulAut.conj_apply, ← scalar_comm, mul_inv_cancel_right]

theorem conj_pow_three_eq_one_iff (s A : GL (Fin 6) F4) :
    (MulAut.conj s A) ^ 3 = 1 ↔ A ^ 3 = 1 := by
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem matC_conj (s A : GL (Fin 6) F4) :
    matC (MulAut.conj s A) = matC s * matC A * matC s⁻¹ := by
  rw [MulAut.conj_apply, map_mul, map_mul]

theorem trace_conj (s A : GL (Fin 6) F4) :
    (matC (MulAut.conj s A)).trace = (matC A).trace := by
  rw [matC_conj, Matrix.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

theorem not_scalar_conj (s : GL (Fin 6) F4) {A : GL (Fin 6) F4}
    (hns : ∀ d : F4c, matC A ≠ Matrix.scalar (Fin 6) d) (d : F4c) :
    matC (MulAut.conj s A) ≠ Matrix.scalar (Fin 6) d := by
  intro h
  apply hns d
  have h1 : matC A = matC s⁻¹ * matC (MulAut.conj s A) * matC s := by
    rw [← map_mul, ← map_mul, MulAut.conj_apply]
    congr 1
    group
  rw [h1, h, ← (Matrix.scalar_commute d (fun _ => Commute.all _ _) (matC s⁻¹)).eq,
    Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem exists_conj_commute {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hr2 : ¬ r ^ 2 ∣ Nat.card S6)
    {y : GL (Fin 6) F4} (hy : y ∈ S6) (hyo : orderOf y = r) (A : GU6) {g : P6}
    (hg : conj6 A g = g) (hgo : orderOf g = r) :
    ∃ s ∈ S6, MulAut.conj s (A : GL (Fin 6) F4) * y = y * MulAut.conj s (A : GL (Fin 6) F4) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨h, hh, hhr, hAh⟩ :=
    exists_lift_commute A hg (m := r) (by rw [← hgo]; exact pow_orderOf_eq_one g)
  have hho : orderOf h = r := by
    refine orderOf_eq_prime hhr ?_
    rintro rfl
    have h3 : g ^ 3 = 1 := by rw [← hh, QuotientGroup.mk_one]
    have h3' := orderOf_dvd_of_pow_eq_one h3
    rw [hgo] at h3'
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3')
  obtain ⟨t, ht, m, hm⟩ :=
    exists_conj_pow_eq hr hr2 hy h.2 hyo (by rw [Subgroup.orderOf_coe]; exact hho)
  refine ⟨t⁻¹, inv_mem ht, ?_⟩
  have hc : Commute (MulAut.conj t⁻¹ (A : GL (Fin 6) F4)) (MulAut.conj t⁻¹ (h : GL (Fin 6) F4)) :=
    Commute.map (show Commute (A : GL (Fin 6) F4) h from hAh) (MulAut.conj t⁻¹)
  have hm' : (MulAut.conj t⁻¹ (h : GL (Fin 6) F4)) ^ m = y := by
    rw [MulAut.conj_apply, inv_inv]
    exact hm
  rw [← hm']
  exact (hc.zpow_right m).eq

variable {A : GU6}

theorem pow_three_ne_one_of_seven
    (hns : ∀ d : F4c, matC (A : GL (Fin 6) F4) ≠ Matrix.scalar (Fin 6) d)
    {g : P6} (hg : conj6 A g = g) (hgo : orderOf g = 7) : (A : GL (Fin 6) F4) ^ 3 ≠ 1 := by
  intro h3
  obtain ⟨s, hs, hc⟩ := exists_conj_commute (by norm_num) (by norm_num)
    (by rw [card_S6]; norm_num) y7G_mem orderOf_y7G A hg hgo
  obtain ⟨d, hd⟩ := eq_scalar_of_commute_y7 (conj_mem_GU6 hs A.2) hc
    ((conj_pow_three_eq_one_iff s _).mpr h3)
  exact not_scalar_conj s hns d hd

theorem pow_three_eq_one_of_five
    (hA3 : ∃ c : F4ˣ, (A : GL (Fin 6) F4) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    {g : P6} (hg : conj6 A g = g) (hgo : orderOf g = 5) : (A : GL (Fin 6) F4) ^ 3 = 1 := by
  obtain ⟨s, hs, hc⟩ := exists_conj_commute (by norm_num) (by norm_num)
    (by rw [card_S6]; norm_num) y5G_mem orderOf_y5G A hg hgo
  exact (conj_pow_three_eq_one_iff s _).mp
    (pow_three_eq_one_of_commute_y5 (conj_mem_GU6 hs A.2) hc (conj_pow_three_scalar s hA3))

theorem trace_ne_zero_of_eleven
    (hA3 : ∃ c : F4ˣ, (A : GL (Fin 6) F4) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    (hns : ∀ d : F4c, matC (A : GL (Fin 6) F4) ≠ Matrix.scalar (Fin 6) d)
    {g : P6} (hg : conj6 A g = g) (hgo : orderOf g = 11) :
    (matC (A : GL (Fin 6) F4)).trace ≠ 0 := by
  obtain ⟨s, hs, hc⟩ := exists_conj_commute (by norm_num) (by norm_num)
    (by rw [card_S6]; norm_num) y11G_mem orderOf_y11G A hg hgo
  rw [← trace_conj s]
  exact trace_ne_zero_of_commute_y11 (conj_mem_GU6 hs A.2) hc (conj_pow_three_scalar s hA3)
    (not_scalar_conj s hns)

theorem trace_eq_zero_of_ten
    (hA3 : ∃ c : F4ˣ, (A : GL (Fin 6) F4) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    {g : P6} (hg : conj6 A g = g) (hgo : orderOf g = 10) :
    (matC (A : GL (Fin 6) F4)).trace = 0 := by
  obtain ⟨h, hh, hh10, hAh⟩ :=
    exists_lift_commute A hg (m := 10) (by rw [← hgo]; exact pow_orderOf_eq_one g)
  have hho : orderOf h = 10 := by
    have h1 : orderOf (g ^ 3) = 10 := by
      rw [Nat.Coprime.orderOf_pow (by rw [hgo]; decide), hgo]
    have h2 := orderOf_map_dvd (QuotientGroup.mk' (normOneScalars uData (gramSU uData M6) 6)) h
    rw [QuotientGroup.mk'_apply, hh, h1] at h2
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hh10) h2
  have ho2 : orderOf (h ^ 2) = 5 := by
    have h1 := orderOf_pow_orderOf_div (x := h) (n := 5) (by rw [hho]; norm_num)
      (by rw [hho]; norm_num)
    rwa [hho] at h1
  have ho5 : orderOf (h ^ 5) = 2 := by
    have h1 := orderOf_pow_orderOf_div (x := h) (n := 2) (by rw [hho]; norm_num)
      (by rw [hho]; norm_num)
    rwa [hho] at h1
  obtain ⟨t, ht, m, hm⟩ := exists_conj_pow_eq (r := 5) (by norm_num) (by rw [card_S6]; norm_num)
    y5G_mem (h ^ 2).2 orderOf_y5G (by rw [Subgroup.orderOf_coe]; exact ho2)
  have hm' : (MulAut.conj t⁻¹ ((h ^ 2 : gramSU uData M6) : GL (Fin 6) F4)) ^ m = y5G := by
    rw [MulAut.conj_apply, inv_inv]
    exact hm
  have hAh' : Commute (A : GL (Fin 6) F4) (h : GL (Fin 6) F4) := hAh
  have hA2 : Commute (MulAut.conj t⁻¹ (A : GL (Fin 6) F4))
      (MulAut.conj t⁻¹ ((h ^ 2 : gramSU uData M6) : GL (Fin 6) F4)) := by
    rw [Subgroup.coe_pow]
    exact (hAh'.pow_right 2).map (MulAut.conj t⁻¹)
  have hA5 : Commute (MulAut.conj t⁻¹ (A : GL (Fin 6) F4))
      (MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4)) := by
    rw [Subgroup.coe_pow]
    exact (hAh'.pow_right 5).map (MulAut.conj t⁻¹)
  have h52 : Commute (MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4))
      (MulAut.conj t⁻¹ ((h ^ 2 : gramSU uData M6) : GL (Fin 6) F4)) := by
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
    exact ((Commute.refl (h : GL (Fin 6) F4)).pow_pow 5 2).map (MulAut.conj t⁻¹)
  have hcB : MulAut.conj t⁻¹ (A : GL (Fin 6) F4) * y5G = y5G * MulAut.conj t⁻¹ (A : GL (Fin 6) F4) := by
    rw [← hm']
    exact (hA2.zpow_right m).eq
  have hcH : MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4) * y5G =
      y5G * MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4) := by
    rw [← hm']
    exact (h52.zpow_right m).eq
  have hH2 : (MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4)) ^ 2 = 1 := by
    have h10 : (h ^ 5) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hh10
    rw [← map_pow, ← Subgroup.coe_pow, h10, Subgroup.coe_one, map_one]
  have hH1 : MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4) ≠ 1 := by
    intro h1
    have h2 : (h ^ 5 : gramSU uData M6) = 1 := by
      apply Subtype.ext
      apply (MulAut.conj t⁻¹).injective
      rw [h1, Subgroup.coe_one, map_one]
    rw [h2, orderOf_one] at ho5
    norm_num at ho5
  have hHmem : MulAut.conj t⁻¹ ((h ^ 5 : gramSU uData M6) : GL (Fin 6) F4) ∈ GU6 :=
    conj_mem_GU6 (inv_mem ht) (mem_GU6_of_mem_S6 (h ^ 5).2)
  rw [← trace_conj t⁻¹]
  exact trace_eq_zero_of_commute_y5 (conj_mem_GU6 (inv_mem ht) A.2) hHmem hcB hcH hH2 hH1 hA5.eq
    (conj_pow_three_scalar t⁻¹ hA3)

end U6

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
