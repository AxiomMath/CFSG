module

public import CFSG.Quasithin.Vol2.KGFactAutSylowU35
public import CFSG.RankThree.PartOne.HNB.F25
public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.HNB
open scoped Matrix

namespace U35Syl

@[expose] def t : F25 := ((0 : ZMod 5), (1 : ZMod 5))

@[expose] def Rm : Matrix (Fin 3) (Fin 3) F25 := !![t, t, 0; -t, t, 0; 0, 0, -1]

@[expose] def Sm : Matrix (Fin 3) (Fin 3) F25 := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem Rm_det : Rm.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem Sm_det : Sm.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem Rm_unitary : (Rm.map (· ^ (5 ^ 1)))ᵀ * Rm = 1 := by decide +kernel

theorem Sm_unitary : (Sm.map (· ^ (5 ^ 1)))ᵀ * Sm = 1 := by decide +kernel

theorem Rm_pow : Rm ^ 8 = 1 := by decide +kernel

theorem Sm_sq : Sm ^ 2 = 1 := by decide +kernel

theorem Sm_Rm : Sm * Rm * Sm = Rm ^ 3 := by decide +kernel

theorem not_scalar : ∀ i : Fin 8, ∀ e : Fin 2,
    ((Rm ^ (i : ℕ) * Sm ^ (e : ℕ)) 0 1 = 0 ∧
      (Rm ^ (i : ℕ) * Sm ^ (e : ℕ)) 0 0 = (Rm ^ (i : ℕ) * Sm ^ (e : ℕ)) 2 2 ∧
      (Rm ^ (i : ℕ) * Sm ^ (e : ℕ)) 1 1 = (Rm ^ (i : ℕ) * Sm ^ (e : ℕ)) 2 2) →
    i = 0 ∧ e = 0 := by
  decide +kernel

abbrev SU35 : Subgroup (GL (Fin 3) F25) := StatedSU 3 (5 ^ 1) F25

@[expose] noncomputable def RR : SU35 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Rm (by rw [Rm_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using Rm_det, by simpa using Rm_unitary⟩⟩

@[expose] noncomputable def SS : SU35 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Sm (by rw [Sm_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using Sm_det, by simpa using Sm_unitary⟩⟩

theorem coe_RR : (((RR : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = Rm := rfl

theorem coe_SS : (((SS : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = Sm := rfl

theorem coe_pow (x : SU35) (k : ℕ) :
    (((x ^ k : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      (((x : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) ^ k := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem coe_mul (x y : SU35) :
    (((x * y : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      (((x : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) *
        (((y : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := rfl

theorem ext_iff' {x y : SU35} :
    x = y ↔ (((x : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      (((y : SU35) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext (Units.ext h)⟩

theorem RR_pow : RR ^ 8 = 1 := by
  rw [ext_iff', coe_pow, coe_RR, Rm_pow]
  rfl

theorem SS_sq : SS ^ 2 = 1 := by
  rw [ext_iff', coe_pow, coe_SS, Sm_sq]
  rfl

theorem SS_inv : SS⁻¹ = SS := by
  rw [inv_eq_iff_mul_eq_one, ← sq, SS_sq]

theorem SS_RR : SS * RR * SS⁻¹ = RR ^ 3 := by
  rw [SS_inv, ext_iff', coe_mul, coe_mul, coe_pow, coe_RR, coe_SS, Sm_Rm]

abbrev PSU35 : Type := StatedProj SU35

noncomputable abbrev proj : SU35 →* PSU35 :=
  QuotientGroup.mk' ((StatedScalars (Fin 3) F25).subgroupOf SU35)

theorem r_pow : proj RR ^ 8 = 1 := by rw [← map_pow, RR_pow, map_one]

theorem s_sq : proj SS ^ 2 = 1 := by rw [← map_pow, SS_sq, map_one]

theorem s_r : proj SS * proj RR * (proj SS)⁻¹ = proj RR ^ 3 := by
  rw [← map_inv, ← map_mul, ← map_mul, SS_RR, map_pow]

theorem r_s_ne : ∀ i : Fin 8, ∀ e : Fin 2,
    proj RR ^ (i : ℕ) * proj SS ^ (e : ℕ) = 1 → i = 0 ∧ e = 0 := by
  intro i e h
  rw [← map_pow, ← map_pow, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hM := congrArg (fun g : GL (Fin 3) F25 => (g : Matrix (Fin 3) (Fin 3) F25)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at hM
  have hM' : Rm ^ (i : ℕ) * Sm ^ (e : ℕ) = Matrix.scalar (Fin 3) (c : F25) := by
    rw [← coe_RR, ← coe_SS, ← coe_pow, ← coe_pow, ← coe_mul]
    exact hM.symm
  refine not_scalar i e ⟨?_, ?_, ?_⟩ <;> rw [hM'] <;> simp [Matrix.scalar_apply]

theorem card_PSU35 : Nat.card PSU35 = 126000 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F25) (p := 5) (f := 1)
    (n := 3) (by norm_num) le_rfl (by rw [F25.card]; norm_num) (by norm_num)
  rw [h]
  decide

theorem factorization_card_PSU35 : (Nat.card PSU35).factorization 2 = 4 := by
  rw [card_PSU35, show (126000 : ℕ) = 2 ^ 4 * 7875 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 7875)]
  simp

theorem exists_sylow_semidihedral :
    ∃ T : Sylow 2 PSU35, Nonempty (↥(T : Subgroup PSU35) ≃* CFSG.Open.SemidihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := CFSG.RankThree.Asc83Table.sdHom (proj RR) (proj SS) r_pow s_sq s_r
  have hH : Nat.card φ.range ∣ 16 := by
    have := Subgroup.card_range_dvd φ
    rwa [CFSG.Semidihedral.card 4 (by norm_num)] at this
  have hR : proj RR ∈ φ.range :=
    ⟨CFSG.Semidihedral.r 4, CFSG.RankThree.Asc83Table.sdHom_r _ _ r_pow s_sq s_r⟩
  have hS : proj SS ∈ φ.range :=
    ⟨CFSG.Semidihedral.s 4, CFSG.RankThree.Asc83Table.sdHom_s _ _ r_pow s_sq s_r⟩
  obtain ⟨eH⟩ := CFSG.RankThree.Asc83Table.nonempty_mulEquiv_semidihedral hH hR hS r_pow s_sq
    s_r r_s_ne
  have hcard : Nat.card φ.range = 2 ^ (Nat.card PSU35).factorization 2 := by
    rw [Nat.card_congr eH.toEquiv, CFSG.Semidihedral.card 4 (by norm_num),
      factorization_card_PSU35]
  exact ⟨Sylow.ofCard φ.range hcard, ⟨(MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _)).trans eH⟩⟩

end U35Syl

theorem u35SylowSemidihedral_holds : U35SylowSemidihedral := by
  intro K _ _ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card F25 = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, F25.card, hK]
    norm_num
  let φ : F25 ≃+* K := FiniteField.ringEquivOfCardEq hc
  let E : StatedProj (StatedSU 3 (5 ^ 1) F25) ≃* StatedProj (StatedSU 3 (5 ^ 1) K) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (5 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  obtain ⟨T, ⟨eT⟩⟩ := U35Syl.exists_sylow_semidihedral
  obtain ⟨T₂, hT₂⟩ := Sylow.exists_comap_eq_of_injective T (f := E.toMonoidHom) E.injective
  have hmap : (T : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F25))).map E.toMonoidHom = T₂ := by
    rw [← hT₂]
    exact Subgroup.map_comap_eq_self_of_surjective E.surjective _
  exact ⟨T₂, ⟨(MulEquiv.subgroupCongr hmap.symm).trans ((E.subgroupMap _).symm.trans eT)⟩⟩

end CFSG.Quasithin.H13.KGAutSyl
