module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDihedral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_hasL32Quot_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {E : Subgroup Q}
    (hE : HasL32Quot E) : HasL32Quot (E.map e.toMonoidHom) := by
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  let ε := E.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨Qm, hQm, π.comp ε.symm.toMonoidHom, hπ.comp ε.symm.surjective, hm⟩

theorem r95_not_isSolvable_of_hasL32Quot {Q : Type} [Group Q] {E : Subgroup Q}
    (hE : HasL32Quot E) {W : Subgroup Q} (hEW : E ≤ W) : ¬ Group.IsSolvable ↥W := by
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  obtain ⟨hsimple, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  intro hW
  haveI : Group.IsSolvable ↥W := hW
  haveI : IsSimpleGroup Qm := hsimple
  have hsolvE : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hEW)
  have hsolvQ : Group.IsSolvable Qm := by
    haveI : Group.IsSolvable ↥E := hsolvE
    exact Group.isSolvable_of_surjective hπ
  have hcomm : ∀ a b : Qm, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hsolvQ
  haveI : IsMulCommutative Qm := IsMulCommutative.of_comm hcomm
  have hprime : (Nat.card Qm).Prime := Group.is_simple_iff_prime_card.mp hsimple
  rw [hcard] at hprime
  exact (by norm_num : ¬ Nat.Prime 168) hprime

theorem r95_exists_order_three_of_hasL32Quot {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE : HasL32Quot E) : ∃ A : Subgroup Q, A ≤ E ∧ Nat.card A = 3 := by
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  obtain ⟨-, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  have hdvd : Nat.card Qm ∣ Nat.card ↥E := Subgroup.card_dvd_of_surjective hπ
  have h3 : 3 ∣ Nat.card ↥E := by
    have : 3 ∣ Nat.card Qm := by rw [hcard]; norm_num
    exact dvd_trans this hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 3 h3
  refine ⟨(Subgroup.zpowers c).map E.subtype, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hc]

theorem r95_exists_noncomm_two_subgroup {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE : HasL32Quot E) :
    ∃ R : Subgroup Q, R ≤ E ∧ IsPGroup 2 R ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  haveI : Finite Qm := Finite.of_surjective π hπ
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  letI : Field K := hK
  letI : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hKcard
  obtain ⟨m, hm3, S, r, hrS, s, hsS, -, hro, -, -, hconj⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSL_three_dihedral_sylow hK2
  have hrs : r * s ≠ s * r := by
    intro hrs
    have hr_eq : r = r⁻¹ := by
      have h1 : s⁻¹ * r * s = r := by
        calc s⁻¹ * r * s = s⁻¹ * (r * s) := by rw [mul_assoc]
          _ = s⁻¹ * (s * r) := by rw [hrs]
          _ = (s⁻¹ * s) * r := by rw [mul_assoc]
          _ = 1 * r := by rw [inv_mul_cancel]
          _ = r := by rw [one_mul]
      exact h1.symm.trans hconj
    have hr2 : r ^ 2 = 1 := by
      calc r ^ 2 = r * r := pow_two r
        _ = r * r⁻¹ := congrArg (fun x => r * x) hr_eq
        _ = 1 := mul_inv_cancel r
    have hdvd : orderOf r ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hr2
    rw [hro] at hdvd
    have hle : 2 ^ (m - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hmle : m - 1 ≤ 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hle
    omega
  let S' : Sylow 2 Qm := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let a : Qm := e.symm r
  let b : Qm := e.symm s
  have haS : a ∈ (S' : Subgroup Qm) := by
    simp only [S', Sylow.coe_mapSurjective, a]
    exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hrS
  have hbS : b ∈ (S' : Subgroup Qm) := by
    simp only [S', Sylow.coe_mapSurjective, b]
    exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hsS
  have hab : a * b ≠ b * a := by
    intro h
    exact hrs (by simpa [a, b, map_mul] using congrArg (fun x => e x) h)
  obtain ⟨P, hP⟩ := (Sylow.mapSurjective_surjective hπ 2) S'
  have hPS : (P : Subgroup ↥E).map π = (S' : Subgroup Qm) := by
    rw [← hP, Sylow.coe_mapSurjective]
  obtain ⟨x, hxP, hxπ⟩ := Subgroup.mem_map.mp (hPS.symm ▸ haS)
  obtain ⟨y, hyP, hyπ⟩ := Subgroup.mem_map.mp (hPS.symm ▸ hbS)
  have hxy : (x : Q) * (y : Q) ≠ (y : Q) * (x : Q) := by
    intro h
    apply hab
    have h' : (x : ↥E) * y = y * x := Subtype.ext h
    calc a * b = π x * π y := by rw [← hxπ, ← hyπ]
      _ = π (x * y) := (map_mul π x y).symm
      _ = π (y * x) := by rw [h']
      _ = π y * π x := map_mul π y x
      _ = b * a := by rw [hxπ, hyπ]
  refine ⟨(P : Subgroup ↥E).map E.subtype, Subgroup.map_subtype_le _,
    (P.isPGroup').map E.subtype, (x : Q), Subgroup.mem_map_of_mem E.subtype hxP,
    (y : Q), Subgroup.mem_map_of_mem E.subtype hyP, hxy⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
