module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEKrylov
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU52
public import CFSG.RankThree.PartOne.U5K.Model
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.GH74.Uniqueness.SU.SU5.F4c (z0 z1 w w2)
open Matrix
open scoped Matrix

namespace SU5

abbrev KK : Type := GaloisField 2 (2 * 1)

instance : NeZero (2 * 1) := ⟨by norm_num⟩

abbrev U : Type := ↥(CFSG.Open.StatedSU 5 (2 ^ 1) KK)

noncomputable def eK : F4c ≃+* KK := F4c.equivGF

@[expose] def yC : Matrix (Fin 5) (Fin 5) F4c :=
  !![w2, w, w, w, z1; w2, z0, z1, z0, w; w, w, w, w, w; z1, w, z0, z0, w2; w2, z0, z0, z1, w]

@[expose] def yCi : Matrix (Fin 5) (Fin 5) F4c :=
  !![w, w, w2, z1, w; w2, z0, w2, w2, z0; w2, z1, w2, z0, z0; w2, z0, w2, z0, z1;
    z1, w2, w2, w, w2]

@[expose] def p2 : Matrix (Fin 5) (Fin 5) F4c :=
  !![z1, z1, z0, w2, z0; z1, w2, w2, z1, w; z0, w2, w, w, z0; z0, w, z0, z1, w2;
    w, w2, z1, w2, w2]

@[expose] def p3 : Matrix (Fin 5) (Fin 5) F4c :=
  !![w2, w2, w2, w, z1; z0, z1, z0, z1, z1; w2, z0, z0, w2, w2; w, w, w, w2, z1;
    z0, z0, w, w, w]

@[expose] def p4 : Matrix (Fin 5) (Fin 5) F4c :=
  !![z0, w2, w2, z1, z0; z1, w, z1, z1, w2; w2, z0, z1, w, z0; w2, z1, w, z1, w;
    z0, z0, w2, z1, z1]

@[expose] def pw : Fin 5 → Matrix (Fin 5) (Fin 5) F4c := ![1, yC, p2, p3, p4]

theorem pw_eq : ∀ j : Fin 5, pw j = yC ^ (j : ℕ) := by decide +kernel

@[expose] def v5 : Fin 5 → F4c := ![z1, z0, z0, z0, z0]

@[expose] def kr5 : Matrix (Fin 5) (Fin 5) F4c := Matrix.of fun i j => (pw j *ᵥ v5) i

@[expose] def kr5i : Matrix (Fin 5) (Fin 5) F4c :=
  !![z1, w2, z1, z0, z1; z0, z1, w2, z1, w2; z0, w, z1, w, w; z0, w2, w2, w, w;
    z0, z0, w2, z1, z0]

theorem kr5i_mul_kr5 : kr5i * kr5 = 1 := by decide +kernel

theorem commute_check : ∀ v : Fin 5 → F4c, (∑ j, (kr5i *ᵥ v) j • pw j) ^ 3 = 1 →
    ∃ c : F4c, ∑ j, (kr5i *ᵥ v) j • pw j = Matrix.scalar (Fin 5) c := by
  decide +kernel

theorem yC_mul_yCi : yC * yCi = 1 := by decide +kernel

theorem yCi_mul_yC : yCi * yC = 1 := by decide +kernel

theorem yC_pow_eleven : yC ^ 11 = 1 := by decide +kernel

theorem yC_ne_one : yC ≠ 1 := by decide +kernel

theorem yC_unitary : (yC.map (· ^ (2 ^ 1)))ᵀ * yC = 1 := by decide +kernel

theorem f4c_eq_one_of_pow_eleven : ∀ c : F4c, c ^ 11 = 1 → c = 1 := by decide

theorem f4c_eq_one_of_pow_five : ∀ c : F4c, c ^ 5 = 1 → c = 1 := by decide

theorem det_yC : yC.det = 1 :=
  f4c_eq_one_of_pow_eleven _ (by rw [← Matrix.det_pow, yC_pow_eleven, Matrix.det_one])

@[expose] def y0C : GL (Fin 5) F4c := ⟨yC, yCi, yC_mul_yCi, yCi_mul_yC⟩

theorem y0C_mem : y0C ∈ CFSG.Open.StatedSU 5 (2 ^ 1) F4c := by
  unfold CFSG.Open.StatedSU
  exact Subgroup.subset_closure ⟨det_yC, yC_unitary⟩

noncomputable def y0 : U :=
  ⟨CFSG.Adapters.RankTwoModelTransports.glCongr eK y0C, by
    rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU eK 5 (2 ^ 1)]
    exact ⟨y0C, y0C_mem, rfl⟩⟩

noncomputable def Φ : Matrix (Fin 5) (Fin 5) KK ≃+* Matrix (Fin 5) (Fin 5) F4c :=
  eK.symm.mapMatrix

noncomputable def matU : U →* Matrix (Fin 5) (Fin 5) KK :=
  (Units.coeHom (Matrix (Fin 5) (Fin 5) KK)).comp (CFSG.Open.StatedSU 5 (2 ^ 1) KK).subtype

theorem matU_injective : Function.Injective matU := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem Φ_matU_y0 : Φ (matU y0) = yC := by
  show (yC.map eK).map eK.symm = yC
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id yC]
  congr 1
  funext c
  exact eK.symm_apply_apply c

theorem orderOf_y0 : orderOf y0 = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime (matU_injective (Φ.injective ?_)) fun h => yC_ne_one ?_
  · rw [map_pow, map_pow, Φ_matU_y0, yC_pow_eleven, map_one, map_one]
  · rw [← Φ_matU_y0, h, map_one, map_one]

theorem eq_one_of_commute_y0 (s : U) (hs : s * y0 = y0 * s) (h3 : s ^ 3 = 1) : s = 1 := by
  have hm : Φ (matU s) * yC = yC * Φ (matU s) := by
    rw [← Φ_matU_y0, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hs]
  have heq := eq_sum_of_commute (kr := kr5) (kr' := kr5i) (v := v5) pw_eq (fun _ _ => rfl)
    kr5i_mul_kr5 hm
  have h3' : (∑ j, (kr5i *ᵥ (Φ (matU s) *ᵥ v5)) j • pw j) ^ 3 = 1 := by
    rw [← heq, ← map_pow, ← map_pow, h3, map_one, map_one]
  obtain ⟨c, hc⟩ := commute_check _ h3'
  rw [← heq] at hc
  have hdet : (Φ (matU s)).det = 1 := by
    have h1 : (matU s).det = 1 := det_eq_one_of_mem_statedSU s.2
    have h2 := RingHom.map_det (eK.symm : KK →+* F4c) (matU s)
    rw [h1, map_one] at h2
    exact h2.symm
  rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hc1 := f4c_eq_one_of_pow_five c hdet
  rw [hc1, map_one] at hc
  apply matU_injective
  apply Φ.injective
  rw [hc, map_one, map_one]

theorem card_U : Nat.card U = 13685760 := by
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int
    (CFSG.RankThree.PartOne.U5K.u5FieldData 1 le_rfl) (n := 5) (by norm_num)
  have hp : ∏ i ∈ Finset.Icc 2 5, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 13365 := by decide
  rw [hp] at hc
  norm_num at hc
  exact_mod_cast hc

theorem not_sq_eleven_dvd : ¬ 11 ^ 2 ∣ Nat.card U := by
  rw [card_U]
  norm_num

theorem scalars_eq_bot :
    (CFSG.Open.StatedScalars (Fin 5) KK).subgroupOf (CFSG.Open.StatedSU 5 (2 ^ 1) KK) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hs
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨l, hl⟩ := hs
  have hl' : Matrix.GeneralLinearGroup.scalar (Fin 5) l = g := hl
  have hdet := det_eq_one_of_mem_statedSU hg
  rw [← hl', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hl1 : (l : KK) = 1 := by
    obtain ⟨c, hc⟩ : ∃ c : F4c, eK c = l := ⟨eK.symm l, eK.apply_symm_apply _⟩
    rw [← hc, ← map_pow] at hdet
    rw [← hc, f4c_eq_one_of_pow_five c (eK.injective (by rw [hdet, map_one])), map_one]
  have : g = 1 := by
    rw [← hl']
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, hl1, Units.val_one,
      Matrix.scalar_apply, Matrix.diagonal_one])
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

noncomputable def projEquiv : projSU 5 2 1 ≃* U :=
  (CFSG.PGLModel.projSUEquivStatedProj 5 2 1).trans
    ((QuotientGroup.quotientMulEquivOfEq scalars_eq_bot).trans QuotientGroup.quotientBot)

theorem good429_U (x : U) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set U)) := by
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have h11 := not_dvd_card_centralizer_of_sylow (by norm_num) orderOf_y0 not_sq_eleven_dvd
    eq_one_of_commute_y0 hx3 hx1
  refine good429_of_not_dvd (N := 13685760) (B := 240)
    (card_U ▸ Subgroup.card_subgroup_dvd_card _) (by norm_num) (by norm_num) [11]
    (by simpa using h11) (by decide +kernel)

end SU5

theorem noCfgS429_su52 {S : Type} [Group S] [Finite S] (hna : ∃ a b : S, a * b ≠ b * a)
    [IsSimpleGroup S] (e : S ≃* projSU 5 2 1) : NoCfgS429 S := by
  let φ : S ≃* SU5.U := e.trans SU5.projEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (projSU 5 2 1)) := by
    rw [Item434SmallTwoIV.card_outer_projSU_five_two]
    norm_num
  exact noCfgS429_of_model φ (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) SU5.good429_U

theorem eight_SU5 : RowSOf429 (projSU 5 2 1) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_su52 hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
