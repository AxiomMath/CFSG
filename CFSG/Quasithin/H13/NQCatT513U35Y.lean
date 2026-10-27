module

public import CFSG.Quasithin.H13.NQCatT513U35MC

public section

namespace CFSG.Quasithin.H13.NQCat.T513.U35

open HNUnitaryBridge CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (f25Data suMat suMat_apply suMat_injective mem_SU pow_three_of_mem)
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (Rm RR coe_RR RR_pow)
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

@[expose] def IsBlk (M : Matrix (Fin 3) (Fin 3) F25) : Prop :=
  M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsBlk.mul {M N : Matrix (Fin 3) (Fin 3) F25} (hM : IsBlk M) (hN : IsBlk N) :
    IsBlk (M * N) ∧ (M * N) 2 2 = M 2 2 * N 2 2 := by
  obtain ⟨a, b, c, d⟩ := hM
  obtain ⟨a', b', c', d'⟩ := hN
  simp [IsBlk, Matrix.mul_apply, Fin.sum_univ_three, a, b, c, d, a', b', c', d']

theorem suMat_inv (g : ↥SU) : suMat g⁻¹ = (suMat g).adjugate := by
  have hdet : (suMat g).det = 1 := (mem_SU.mp g.2).1
  rw [suMat_apply, Subgroup.coe_inv, Matrix.coe_units_inv, ← suMat_apply, Matrix.inv_def, hdet,
    Ring.inverse_one, one_smul]

theorem isBlk_inv {g : ↥SU} (hg : IsBlk (suMat g)) :
    IsBlk (suMat g⁻¹) ∧ suMat g⁻¹ 2 2 * suMat g 2 2 = 1 := by
  have hdet : (suMat g).det = 1 := (mem_SU.mp g.2).1
  obtain ⟨a, b, c, d⟩ := hg
  rw [Matrix.det_fin_three, a, b, c, d] at hdet
  rw [suMat_inv]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Matrix.adjugate_fin_three, a, b, c, d]
  linear_combination hdet

theorem suMat_RR4 : suMat (RR ^ 4) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [map_pow, suMat_apply, coe_RR]
  decide +kernel

theorem isBlk_of_comm {g : ↥SU} (h : g * RR ^ 4 = RR ^ 4 * g) : IsBlk (suMat g) := by
  have h1 := congrArg suMat h
  rw [map_mul, map_mul, suMat_RR4] at h1
  have k1 : ∀ m : F25, -m = m → m = 0 := by decide +kernel
  refine ⟨k1 _ ?_, k1 _ ?_, k1 _ ?_, k1 _ ?_⟩
  · have := congrFun (congrFun h1 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    exact this.symm
  · have := congrFun (congrFun h1 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    exact this.symm
  · have := congrFun (congrFun h1 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    exact this
  · have := congrFun (congrFun h1 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    exact this

theorem comm_of_mem_centralizer {g : ↥SU} (h : proj g * z0 = z0 * proj g) :
    g * RR ^ 4 = RR ^ 4 * g := by
  set t := RR ^ 4 with ht
  set w := g * t * g⁻¹ * t⁻¹ with hw
  have hwS : w ∈ unitaryScalars f25Data 3 := by
    rw [← ker_unitaryProj f25Data 3, MonoidHom.mem_ker, hw, map_mul, map_mul, map_mul, map_inv,
      map_inv]
    rw [z0] at h
    calc proj g * proj t * (proj g)⁻¹ * (proj t)⁻¹ =
        (proj g * proj t) * (proj t * proj g)⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have hwc : ∀ y, y * w = w * y := fun y =>
    Subgroup.mem_center_iff.mp (unitaryScalars_le_center f25Data 3 hwS) y
  have hw3 : w ^ 3 = 1 := pow_three_of_mem hwS
  have ht2 : t ^ 2 = 1 := by rw [ht, ← pow_mul, show 4 * 2 = 8 by norm_num, RR_pow]
  have hw2 : w ^ 2 = 1 := by
    have e1 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ht2, mul_one, mul_inv_cancel]
    have e2 : g * t * g⁻¹ = w * t := by rw [hw]; group
    rw [e2, Commute.mul_pow (hwc t).symm 2, ht2, mul_one] at e1
    exact e1
  have hw1 : w = 1 := by
    have : w = w ^ 3 * (w ^ 2)⁻¹ := by group
    rw [this, hw3, hw2, inv_one, mul_one]
  calc g * t = w * (t * g) := by rw [hw]; group
    _ = t * g := by rw [hw1, one_mul]

@[expose] def Yhat : Subgroup ↥SU where
  carrier := {g | IsBlk (suMat g) ∧ suMat g 2 2 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := IsBlk.mul ha.1 hb.1
    refine ⟨by rw [map_mul]; exact h1, by rw [map_mul, h2, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨by simp [IsBlk], by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨h1, h2⟩ := isBlk_inv ha.1
    exact ⟨h1, by rwa [ha.2, mul_one] at h2⟩

theorem pow_five_five (c : F25) : (c ^ 5) ^ 5 = c := by
  have h := CFSG.Quasithin.H13.KGU35.f25Data.bar_bar c
  rwa [f25_bar, f25_bar] at h

theorem pow_thirty (c : F25) : c ^ 30 = c ^ 6 := by
  calc c ^ 30 = (c ^ 5) ^ 5 * c ^ 5 := by ring
    _ = c ^ 6 := by rw [pow_five_five]; ring

theorem Yhat_row {g : ↥SU} (hg : g ∈ Yhat) :
    suMat g 1 1 = suMat g 0 0 ^ 5 ∧ suMat g 1 0 = -suMat g 0 1 ^ 5 ∧
      suMat g 0 0 ^ 6 + suMat g 0 1 ^ 6 = 1 := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := hg
  have hu : ((suMat g).map (· ^ 5))ᵀ * suMat g = 1 := by
    have := (mem_SU.mp g.2).2
    rwa [← suMat_apply] at this
  have hinv : (suMat g)⁻¹ = ((suMat g).map (· ^ 5))ᵀ := Matrix.inv_eq_left_inv hu
  have hdet : (suMat g).det = 1 := (mem_SU.mp g.2).1
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul] at hinv
  have h00 := congrFun (congrFun hinv 0) 0
  have h01 := congrFun (congrFun hinv 0) 1
  simp [Matrix.adjugate_fin_three, a, b, c, d, e] at h00 h01
  have h10 : suMat g 1 0 = -suMat g 0 1 ^ 5 := by
    rw [← pow_five_five (suMat g 1 0), ← h01, neg_pow, show (-1 : F25) ^ 5 = -1 by norm_num,
      neg_one_mul]
  refine ⟨h00, h10, ?_⟩
  have hn := congrFun (congrFun hu 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, c, h10] at hn
  rw [← hn]
  ring_nf
  rw [pow_thirty]

theorem card_normPairs : Nat.card {p : F25 × F25 // p.1 ^ 6 + p.2 ^ 6 = 1} = 120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Yhat : Nat.card Yhat ≤ 120 := by
  let f : Yhat → {p : F25 × F25 // p.1 ^ 6 + p.2 ^ 6 = 1} := fun g =>
    ⟨(suMat (g : ↥SU) 0 0, suMat (g : ↥SU) 0 1), (Yhat_row g.2).2.2⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h1 : suMat (g : ↥SU) 0 0 = suMat (g' : ↥SU) 0 0 := congrArg (fun p => p.1.1) h
    have h2 : suMat (g : ↥SU) 0 1 = suMat (g' : ↥SU) 0 1 := congrArg (fun p => p.1.2) h
    obtain ⟨r1, r2, -⟩ := Yhat_row g.2
    obtain ⟨r1', r2', -⟩ := Yhat_row g'.2
    obtain ⟨⟨a, b, c, d⟩, e⟩ := g.2
    obtain ⟨⟨a', b', c', d'⟩, e'⟩ := g'.2
    apply Subtype.ext
    apply suMat_injective
    ext r s
    fin_cases r <;> fin_cases s
    · exact h1
    · exact h2
    · exact a.trans a'.symm
    · exact r2.trans (h2 ▸ r2'.symm)
    · exact r1.trans (h1 ▸ r1'.symm)
    · exact b.trans b'.symm
    · exact c.trans c'.symm
    · exact d.trans d'.symm
    · exact e.trans e'.symm
  calc Nat.card Yhat ≤ Nat.card {p : F25 × F25 // p.1 ^ 6 + p.2 ^ 6 = 1} :=
        Nat.card_le_card_of_injective f hf
    _ = 120 := card_normPairs

theorem card_commutator_centralizer_z0 :
    Nat.card ↥⁅Subgroup.centralizer {z0}, Subgroup.centralizer {z0}⁆ ≤ 120 := by
  have hle : ⁅Subgroup.centralizer {z0}, Subgroup.centralizer {z0}⁆ ≤ Yhat.map proj := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨g, rfl⟩ := unitaryProj_surjective f25Data 3 x
    obtain ⟨h, rfl⟩ := unitaryProj_surjective f25Data 3 y
    have hx' : proj g * z0 = z0 * proj g := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hy' : proj h * z0 = z0 * proj h := Subgroup.mem_centralizer_singleton_iff.mp hy
    have bg := isBlk_of_comm (comm_of_mem_centralizer hx')
    have bh := isBlk_of_comm (comm_of_mem_centralizer hy')
    obtain ⟨bg', eg⟩ := isBlk_inv bg
    obtain ⟨bh', eh⟩ := isBlk_inv bh
    refine ⟨⁅g, h⁆, ⟨?_, ?_⟩, by rw [map_commutatorElement]⟩
    · rw [commutatorElement_def, map_mul, map_mul, map_mul]
      exact ((bg.mul bh).1.mul bg').1.mul bh' |>.1
    · rw [commutatorElement_def, map_mul, map_mul, map_mul, ((bg.mul bh).1.mul bg').1.mul bh' |>.2,
        ((bg.mul bh).1.mul bg').2, (bg.mul bh).2]
      calc suMat g 2 2 * suMat h 2 2 * suMat g⁻¹ 2 2 * suMat h⁻¹ 2 2 =
          (suMat g⁻¹ 2 2 * suMat g 2 2) * (suMat h⁻¹ 2 2 * suMat h 2 2) := by ring
        _ = 1 := by rw [eg, eh, one_mul]
  calc Nat.card ↥⁅Subgroup.centralizer {z0}, Subgroup.centralizer {z0}⁆
      ≤ Nat.card (Yhat.map proj) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card Yhat :=
        Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective proj Yhat)
    _ ≤ 120 := card_Yhat

end CFSG.Quasithin.H13.NQCat.T513.U35
