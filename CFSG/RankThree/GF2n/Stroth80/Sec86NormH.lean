module

public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec85F2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_CN_normalizes_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {x : G} (hx : x ∈ hc.CN t) :
    x ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have h1 := hc.CN_normalizes_conj_LB h35 hs.mem (Rt M (LB M Q B) t).one_mem hx
  rwa [conjSubgroup_one] at h1

theorem sec86NormH_of (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (h54 : Stroth54Statement) (hge : Stroth6NbarGeStatement)
    (hTI : Sec8TIStatement) (hS : Sec8StrongClosureStatement) : Sec86NormHStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 ν hνM hνL hνZ
  by_contra hno
  push Not at hno
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZLB : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hStrong := hS G M Q Z B hc n t hs Z0 hZ0
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hνi : ν⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) := Subgroup.inv_mem _ hνL
  have hZn : ν ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hνM
  have ha : ∀ z ∈ Z0, ν * z * ν⁻¹ ∈ hc.CN t → ν * z * ν⁻¹ ∈ Q := by
    intro z hz hzN
    have hzL : ν * z * ν⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hνL z).mp (hZLB hz)
    have hy : ν * z * ν⁻¹ ∈ Z0 := hStrong z hz ν hνM ⟨hzL, hzN⟩
    by_contra hyQ
    have hzQ : z ∉ Q := fun hzQ => hyQ (hQn ν hνM z hzQ)
    exact hνZ (hTI G M Q Z B hc n t hs Z0 hZ0 ν hνM z hz hzQ hy)
  have hb : ∀ c ∈ hc.CN t, ∀ z ∈ Z0, c * (ν * z * ν⁻¹) * c⁻¹ ∈ conjSubgroup ν Z0 := by
    intro c hc' z hz
    have hcR : c ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.1 hc').1
    have hcM : c ∈ M := hRM hcR
    have hcH : c ∈ H0 M Z := hc.Rt_le_H0 t hcR
    have hcL : c ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      sec8_CN_normalizes_LB h34 hc hs.toSec5 hc'
    have h1 : ν⁻¹ * c * ν ∈ H0 M Z := by
      refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hνM) hcM) hνM,
        Subgroup.mem_centralizer_iff.mpr fun z' hz' => ?_⟩
      have hz'' : ν * z' * ν⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hZn z').mp hz'
      have h2 : (ν * z' * ν⁻¹) * c = c * (ν * z' * ν⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hcH.2 _ hz''
      calc z' * (ν⁻¹ * c * ν) = ν⁻¹ * ((ν * z' * ν⁻¹) * c) * ν := by group
        _ = ν⁻¹ * (c * (ν * z' * ν⁻¹)) * ν := by rw [h2]
        _ = (ν⁻¹ * c * ν) * z' := by group
    have h3 : ν⁻¹ * c * ν ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hνi hcL) hνL
    have h4 := hno _ h1 h3
    have h5 : (ν⁻¹ * c * ν) * z * (ν⁻¹ * c * ν)⁻¹ ∈ Z0 :=
      (Subgroup.mem_normalizer_iff.mp h4 z).mp hz
    rw [mem_conjSubgroup]
    have e : ν⁻¹ * (c * (ν * z * ν⁻¹) * c⁻¹) * ν = (ν⁻¹ * c * ν) * z * (ν⁻¹ * c * ν)⁻¹ := by
      group
    rw [e]
    exact h5
  have hc'' : ∀ y ∈ conjSubgroup ν Z0, ∀ c ∈ hc.CN t, ⁅y, c⁆ ∈ Q := by
    intro y hy c hc'
    have hyz : ν⁻¹ * y * ν ∈ Z0 := mem_conjSubgroup.mp hy
    have hye : y = ν * (ν⁻¹ * y * ν) * ν⁻¹ := by group
    have hyL : y ∈ LB M Q B := by
      rw [hye]
      exact (Subgroup.mem_normalizer_iff.mp hνL _).mp (hZLB hyz)
    have hyR : y ∈ Rt M (LB M Q B) t := hLR hyL
    have h1 : y * c * y⁻¹ ∈ hc.CN t := hc.CN_conj_mem ht hyR hc'
    have h2 : c * y * c⁻¹ ∈ conjSubgroup ν Z0 := by
      rw [hye]
      exact hb c hc' _ hyz
    have hcomm : ⁅y, c⁆ ∈ conjSubgroup ν Z0 := by
      have e : ⁅y, c⁆ = y * (c * y * c⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup ν Z0).mul_mem hy ((conjSubgroup ν Z0).inv_mem h2)
    have hcN : ⁅y, c⁆ ∈ hc.CN t := by
      have e : ⁅y, c⁆ = (y * c * y⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact (hc.CN t).mul_mem h1 ((hc.CN t).inv_mem hc')
    have hz1 : ν⁻¹ * ⁅y, c⁆ * ν ∈ Z0 := mem_conjSubgroup.mp hcomm
    have e2 : ⁅y, c⁆ = ν * (ν⁻¹ * ⁅y, c⁆ * ν) * ν⁻¹ := by group
    rw [e2] at hcN ⊢
    exact ha _ hz1 hcN
  have hall : ∀ z ∈ Z0, ν * z * ν⁻¹ ∈ Q := by
    intro z hz
    have hyL : ν * z * ν⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hνL z).mp (hZLB hz)
    have hyX : ν * z * ν⁻¹ ∈ conjSubgroup ν Z0 := by
      rw [mem_conjSubgroup]
      have e : ν⁻¹ * (ν * z * ν⁻¹) * ν = z := by group
      rw [e]
      exact hz
    have hyN : ν * z * ν⁻¹ ∈ hc.CN t :=
      sec8_DR h51 hA h54 hge hc hs hZ0 _ (hLR hyL) (hc'' _ hyX)
    exact ha z hz hyN
  have hle : Z0 ≤ Q := by
    intro z hz
    have h1 := hQn ν⁻¹ (M.inv_mem hνM) _ (hall z hz)
    have e : ν⁻¹ * (ν * z * ν⁻¹) * ν⁻¹⁻¹ = z := by group
    rwa [e] at h1
  have hcard := Subgroup.card_le_of_le hle
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z :=
    sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpos : 0 < Nat.card Q := Nat.card_pos
  nlinarith

end CFSG.RankThree.GF2n.Stroth80
