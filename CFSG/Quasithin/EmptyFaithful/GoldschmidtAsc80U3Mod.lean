module

public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Ord

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.Quasithin.A312U3

abbrev SU3F (p : ℕ) (F : Type) [Field F] : Type := ↥(StatedSU 3 (p ^ 1) F)

abbrev PSU3F (p : ℕ) (F : Type) [Field F] : Type := StatedProj (StatedSU 3 (p ^ 1) F)

abbrev piU (p : ℕ) (F : Type) [Field F] : SU3F p F →* PSU3F p F :=
  statedProjMk (StatedSU 3 (p ^ 1) F)

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

@[expose] def matU (g : SU3F p F) : Matrix (Fin 3) (Fin 3) F :=
  ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

omit [Fact (Nat.Prime p)] in
theorem matU_mul (g g' : SU3F p F) : matU (g * g') = matU g * matU g' := rfl

omit [Fact (Nat.Prime p)] in
theorem matU_one : matU (1 : SU3F p F) = 1 := rfl

omit [Fact (Nat.Prime p)] in
theorem ext_matU {g g' : SU3F p F} (h : matU g = matU g') : g = g' :=
  Subtype.ext (Units.ext h)

omit [Fact (Nat.Prime p)] in
theorem exists_equiv_psu3 {H : Type} [Group H] {K : Subgroup H} (h : IsPSU 3 p 1 ↥K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ 2 ∧ Nonempty (↥K ≃* PSU3F p F) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨eK⟩⟩ := h
  exact ⟨F, hF, hFin, by simpa using hcard, ⟨eK⟩⟩

@[expose] noncomputable def leviU (hF : Nat.card F = p ^ 2) : Subgroup (SU3F p F) :=
  (Lemma41aU3.blkU (uniData hF)).range

theorem matU_blkU (hF : Nat.card F = p ^ 2) (A : ↥(GU2Stated (p ^ 1) F)) :
    matU (Lemma41aU3.blkU (uniData hF) A) =
      Lemma41aL3.blkMat ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det⁻¹ := rfl

theorem mem_leviU_iff (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {g : SU3F p F} :
    g ∈ leviU hF ↔ matU g 0 2 = 0 ∧ matU g 1 2 = 0 ∧ matU g 2 0 = 0 ∧ matU g 2 1 = 0 := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (show (Lemma41aL3.blkMat _ _ : Matrix (Fin 3) (Fin 3) F) _ _ = 0
       simp [Lemma41aL3.blkMat])
  · rintro ⟨h02, h12, h20, h21⟩
    apply Lemma41aU3.mem_range_blkU_of_commute (uniData hF) hp2
    apply ext_matU
    rw [matU_mul, matU_mul]
    show matU g * negNegOneDiag F = negNegOneDiag F * matU g
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [negNegOneDiag, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21]

theorem ker_piU_le_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    (piU p F).ker ≤ leviU hF := by
  intro g hg
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hm : matU g = Matrix.scalar (Fin 3) (c : F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar, matU] using this.symm
  rw [mem_leviU_iff hp2 hF, hm]
  simp [Matrix.scalar_apply]

@[expose] noncomputable def leviCU (hF : Nat.card F = p ^ 2) : Subgroup (PSU3F p F) :=
  (leviU hF).map (piU p F)

omit [Fact (Nat.Prime p)] in
theorem piU_surjective : Function.Surjective (piU p F) := statedProjMk_surjective _

section Index

variable [Finite F]

theorem card_gu2 (hF : Nat.card F = p ^ 2) :
    Nat.card (GU2Stated (p ^ 1) F) = p * ((p + 1) * (p ^ 2 - 1)) := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = (p ^ 1) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hF]
    simp
  have hGU : GU2Stated (p ^ 1) F = CFSG.Quasithin.StatedGU 2 (p ^ 1) F := rfl
  have h := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hq (n := 2) (by norm_num)
  rw [hGU]
  have hp2' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have : ((Nat.card (CFSG.Quasithin.StatedGU 2 (p ^ 1) F) : ℕ) : ℤ) =
      ((p * ((p + 1) * (p ^ 2 - 1)) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hp2']
    simp [show Finset.Icc 1 2 = {1, 2} from by decide]
    ring
  exact_mod_cast this

theorem card_leviU (hF : Nat.card F = p ^ 2) :
    Nat.card (leviU hF) = p * ((p + 1) * (p ^ 2 - 1)) := by
  have h1 : Nat.card (leviU hF) = Nat.card (GU2Stated (p ^ 1) F) :=
    (Nat.card_congr (Equiv.ofInjective _ (Lemma41aU3.blkU_injective (uniData hF)))).symm
  rw [h1, card_gu2 hF]

theorem card_su3F (hF : Nat.card F = p ^ 2) :
    Nat.card (SU3F p F) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) :=
  card_su3_eq hF

theorem index_leviU (hF : Nat.card F = p ^ 2) : (leviU hF).index = p ^ 2 * (p ^ 2 - p + 1) := by
  have hp3 : 3 ≤ p ∨ p = 2 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h := (leviU hF).index_mul_card
  rw [card_leviU hF, card_su3F hF] at h
  have hp1 : 1 ≤ p := by omega
  have hp2' : p ≤ p ^ 2 := by nlinarith
  have hp1' : 1 ≤ p ^ 2 := by nlinarith
  have hp3' : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hne : p * ((p + 1) * (p ^ 2 - 1)) ≠ 0 := by
    apply Nat.mul_ne_zero (by omega)
    apply Nat.mul_ne_zero (by omega)
    have : 1 < p ^ 2 := by nlinarith
    omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne)
  rw [h]
  zify [hp1, hp1', hp3', hp2']
  ring

theorem odd_main_index_u3 (hp2 : p ≠ 2) : Odd (p ^ 2 * (p ^ 2 - p + 1)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine (hodd.pow).mul ?_
  have hp : p ^ 2 - p = p * (p - 1) := by
    rw [sq, Nat.mul_sub_one]
  rw [hp]
  exact (Nat.even_mul_pred_self p).add_one

theorem odd_index_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : Odd (leviU hF).index := by
  rw [index_leviU hF]
  exact odd_main_index_u3 hp2

omit [Finite F] in
theorem index_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    (leviCU hF).index = (leviU hF).index := by
  rw [leviCU, Subgroup.index_map_eq _ piU_surjective (ker_piU_le_leviU hp2 hF)]

theorem odd_index_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : Odd (leviCU hF).index := by
  rw [index_leviCU hp2 hF]
  exact odd_index_leviU hp2 hF

end Index

end CFSG.Quasithin.E2P.Asc80
