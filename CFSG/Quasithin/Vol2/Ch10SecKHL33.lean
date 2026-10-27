module

public import CFSG.Quasithin.Vol2.Ch10SecKHL33B
public import CFSG.Quasithin.Vol2.Ch10SecBFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11
public import CFSG.Quasithin.Background.F420L33
public import CFSG.Quasithin.Background.F420M11

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace C10KH

theorem exists_mem_sylow_pow {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) {r : Q} (hr8 : r ^ 8 = 1) (hr4 : r ^ 4 ≠ 1) :
    ∃ s ∈ S, s ^ 8 = 1 ∧ s ^ 4 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S0 : Sylow 2 Q :=
    hS.2.1.toSylow (by rw [← Subgroup.relIndex_top_right]; exact hS.2.2) with hS0
  have hr : IsPGroup 2 (Subgroup.zpowers r) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf r ∣ 2 ^ 3 from orderOf_dvd_of_pow_eq_one hr8)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨P, hP⟩ := hr.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P S0
  have hmem : g * r * g⁻¹ ∈ (S0 : Subgroup Q) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hP (Subgroup.mem_zpowers r))
  refine ⟨g * r * g⁻¹, hmem, ?_, ?_⟩
  · rw [conj_pow, hr8, mul_one, mul_inv_cancel]
  · rw [conj_pow]
    intro h
    apply hr4
    have h' : r ^ 4 = g⁻¹ * (g * r ^ 4 * g⁻¹) * g := by group
    rw [h', h]
    group

theorem data_of_l33 {Q : Type}
    [Group Q] [Finite Q] (h : CFSG.Open.StatedClassicalModel Q .PSL 3 3 1) :
    Fin253.RadData Q ∧ ∃ r : Q, r ^ 8 = 1 ∧ r ^ 4 ≠ 1 := by
  refine ⟨Fin253.radData_of_stated_l33 h, ?_⟩
  obtain ⟨e₀⟩ := Unc25K1.psl33_equiv h
  set e := e₀.trans Unc25K1.psl33EquivS3
  refine ⟨e.symm F420.l33r, ?_, ?_⟩
  · rw [← map_pow, F420.l33r_pow_eight, map_one]
  · rw [← map_pow, F420.l33r_pow_four]
    intro hz
    have hz' : (F420.l33z : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 1 :=
      e.symm.injective (hz.trans (map_one _).symm)
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) =>
      (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0) hz'
    simp [F420.l33z, F420.l33zM] at h1
    exact absurd h1 (by decide)

theorem openModel_of_equiv {Q : Type} [Group Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
    CFSG.Open.StatedClassicalModel Q .PSL 3 3 1 :=
  ⟨⟨Nat.prime_three, le_rfl, by decide⟩, ZMod 3, inferInstance, inferInstance, by simp,
    ⟨(e.trans Unc25K1.psl33EquivS3.symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 3))⟩⟩

theorem data_of_m11
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) :
    Fin253.RadData Q ∧ ∃ r : Q, r ^ 8 = 1 ∧ r ^ 4 ≠ 1 := by
  refine ⟨Fin253.radData_of_equiv_m11 e, ?_⟩
  set e' : Q ≃* F420.M11G := e.trans (MulEquiv.refl F420.M11G)
  have h8 : (F420.m11r : F420.M11G) ^ 8 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, F420.m11r_coe, F420.m11rP_pow_eight]; rfl)
  have h4 : (F420.m11r : F420.M11G) ^ 4 ≠ 1 := by
    intro h
    have h1 := congrArg (fun x : F420.M11G => (x : Equiv.Perm (Fin 11)) 0) h
    simp only [Subgroup.coe_pow, F420.m11r_coe, Subgroup.coe_one, Equiv.Perm.one_apply] at h1
    rw [F420.m11_base.2.2.1] at h1
    exact absurd h1 (by decide)
  refine ⟨e'.symm F420.m11r, by rw [← map_pow, h8, map_one], fun h => h4 ?_⟩
  apply e'.symm.injective
  rw [map_pow, h, map_one]

end C10KH

open C10KH in
theorem factL33M11 : FactL33M11 := by
  intro Q _ _ hQ S Y hS _ hSY h3 h9
  obtain ⟨hD, r, hr8, hr4⟩ : Fin253.RadData Q ∧ ∃ r : Q, r ^ 8 = 1 ∧ r ^ 4 ≠ 1 := by
    rcases hQ with ⟨-, F, hF1, hF2, hF, ⟨e₀⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact data_of_l33 ⟨⟨Nat.prime_three, le_rfl, by decide⟩, F, hF1, hF2, hF, ⟨e₀⟩⟩
    · exact data_of_l33 (openModel_of_equiv
        (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 3)).symm))
    · exact data_of_m11 e
  obtain ⟨s, hsS, hs8, hs4⟩ := exists_mem_sylow_pow hS hr8 hr4
  have hzz : s ^ 4 * s ^ 4 = 1 := by rw [← pow_add]; exact hs8
  obtain ⟨y, hy, hne⟩ :=
    exists_not_mem_of_radData hD hs4 hzz (Subgroup.pow_mem _ (hSY hsS) 4) h3 h9
  exact ⟨s, hsS, y, hy, hne⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
