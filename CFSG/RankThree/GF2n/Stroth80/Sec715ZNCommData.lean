module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNParts
public import CFSG.RankThree.GF2n.Stroth80.Sec715SplitData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec715Cm_plus_data (h51 : Stroth51Statement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {m : ℕ} (hm3 : 3 ≤ m) (hPlus : OmegaPlusNat hc t m) {r : G} (hr : Sec7A hc t r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
      Nat.card K = Nat.card Z ∧
      φ.range = StatedOmega (StatedQuadPlus m K) ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      quadPlus m K u = 0 ∧ quadPlus m K u' = 0 ∧ polar (quadPlus m K) u u' ≠ 0 ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.plus hm3).LomGL u ∧
      ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.plus hm3).LomGL u' ∧
      IsOppDecomp (hc.CN t) Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
        (LB M Q B ⊓ hc.CN t) (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
  classical
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  have hPlus' := hPlus
  obtain ⟨K₀, _, _, hK₀, hrep₀⟩ := hPlus
  have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
  have hι₀ : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hι₀] at hcard₀
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    refine ⟨K, hKf, hKfin, hchar, φ, u, u', hKZ, hrange, hker, hu, hu', huu', ?_, ?_, hopp⟩
    · rw [ElemMatrixIso.LomGL_plus hm3]
      exact hLu
    · rw [hLA, ElemMatrixIso.LomGL_plus hm3]
      exact hLu'
  · exfalso
    have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    exact omegaSignStatement_holds G M Q Z B hc t m' (by omega) hPlus'
      ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩

theorem sec715Cm_data (h51 : Stroth51Statement) (hPts : Sec5NatPointsOmegaStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp4 : OmegaPlusNat hc t 4)
    {Z0 Zn : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZn : IsCentrePre Zn (hc.CN t) Q) {r : G} (hr : Sec7A hc t r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 4 ⊕ Fin 4) K) (u u' : Fin 4 ⊕ Fin 4 → K)
      (E : ElemMatrixIso (quadPlus 4 K) (StatedOmega (StatedQuadPlus 4 K))),
      Nat.card K = Nat.card Z ∧ φ.range = StatedOmega (StatedQuadPlus 4 K) ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      quadPlus 4 K u = 0 ∧ quadPlus 4 K u' = 0 ∧ polar (quadPlus 4 K) u u' ≠ 0 ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u ∧
      ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u' ∧
      IsOppDecomp Zn Z0 (LB M Q B) (LB M Q (conjSubgroup r B)) (Zn ⊓ LB M Q B)
        (Zn ⊓ LB M Q (conjSubgroup r B)) := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  obtain ⟨K, hKf, hKfin, hchar, φ, u, u', hKZ, hrange, hker, hu, hu', huu', hLu₁, hLu₂, hopp⟩ :=
    sec715Cm_plus_data h51 hPts hc hs hZ0 hm3 hp4 hr
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hNnorm := sec715Spl_CN_conj hc ht
  have hZ0n := sec715Spl_Z0_conj hc hZ0
  have hZnR' : ∀ x ∈ Rt M (LB M Q B) t, conjSubgroup x Zn = Zn := fun x hx =>
    conjSubgroup_eq_of_le fun y hy => by
      have h1 := hZnn x hx _ (mem_conjSubgroup.mp hy)
      simpa [mul_assoc] using h1
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hι : 4 ≤ Fintype.card (Fin 4 ⊕ Fin 4) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hQnd := nondegenerate_polarBilin_quadPlus 4 K
  have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm3) hQnd hι φ hrange hker hNnorm hZ0n
    hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂ hZ0Zn hZnN hZnR'
  have hdA := isOppDecomp_of_split hopp hZ0Zn hZnN hsplit
  have eA₁ : Zn ⊓ (LB M Q B ⊓ hc.CN t) = Zn ⊓ LB M Q B := by
    rw [inf_comm (LB M Q B) (hc.CN t), ← inf_assoc, inf_of_le_left hZnN]
  have eA₂ : Zn ⊓ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = Zn ⊓ LB M Q (conjSubgroup r B) := by
    rw [inf_comm (LB M Q (conjSubgroup r B)) (hc.CN t), ← inf_assoc, inf_of_le_left hZnN]
  rw [eA₁, eA₂] at hdA
  exact ⟨K, hKf, hKfin, hchar, φ, u, u', ElemMatrixIso.plus hm3, hKZ, hrange, hker, hu, hu',
    huu', hLu₁, hLu₂, hdA⟩

theorem sec715Cm_secHyp (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 Zn : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZn : IsCentrePre Zn (hc.CN t) Q) {r : G} (hr : Sec7A hc t r)
    (hdA : IsOppDecomp Zn Z0 (LB M Q B) (LB M Q (conjSubgroup r B)) (Zn ⊓ LB M Q B)
      (Zn ⊓ LB M Q (conjSubgroup r B))) :
    SecHyp (Rt M (LB M Q B) t) Zn Q := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQM : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    hQM ρ (hRM hρ) y hy
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hQZn : Q ≤ Zn := hZn.Q_le hQN fun ρ hρ => hQn ρ (hCNR hρ)
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hRM hr.mem)
  have hsqA : ∀ a ∈ LB M Q (conjSubgroup r B), a ^ 2 ∈ Q := by
    intro a ha
    rw [hLA, mem_conjSubgroup] at ha
    have h1 := hc.sq_mem_Q_of_mem_LB ha
    have e : a ^ 2 = r * (r⁻¹ * a * r) ^ 2 * r⁻¹ := by
      simp only [pow_two]
      group
    rw [e]
    exact hQM r (hRM hr.mem) _ h1
  have hsq : ∀ z ∈ Zn, z ^ 2 ∈ Q := by
    have key : ∀ z, z ∈ Subgroup.closure
        (((Zn ⊓ LB M Q B : Subgroup G) : Set G) ∪
          ((Zn ⊓ LB M Q (conjSubgroup r B) : Subgroup G) : Set G)) → z ∈ Zn ∧ z ^ 2 ∈ Q := by
      intro z hz'
      induction hz' using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨(Subgroup.mem_inf.mp hx).1, hc.sq_mem_Q_of_mem_LB (Subgroup.mem_inf.mp hx).2⟩
        · exact ⟨(Subgroup.mem_inf.mp hx).1, hsqA x (Subgroup.mem_inf.mp hx).2⟩
      | one => exact ⟨Zn.one_mem, by simpa using Q.one_mem⟩
      | mul x y _ _ ihx ihy =>
        refine ⟨Zn.mul_mem ihx.1 ihy.1, ?_⟩
        have hxM : x ∈ M := hRM (hCNR (hZnN ihx.1))
        have hw : ⁅y, x⁆ ∈ Q := hZn.comm_mem ihy.1 (hZnN ihx.1)
        have e : (x * y) ^ 2 = (x * ⁅y, x⁆ * x⁻¹) * x ^ 2 * y ^ 2 := by
          simp only [pow_two, commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (Q.mul_mem (hQM x hxM _ hw) ihx.2) ihy.2
      | inv x _ ih =>
        exact ⟨Zn.inv_mem ih.1, by rw [inv_pow]; exact Q.inv_mem ih.2⟩
    intro z hz
    refine (key z ?_).2
    rw [← Subgroup.sup_eq_closure, hdA.2.2.2.2.1]
    exact hz
  exact ⟨hQZn, fun x hx y hy => hZn.comm_mem hx (hZnN hy), hsq, hZnn, hQn⟩

theorem sec715Cm_irr (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hNO : Sec7NOrderStatement)
    (h711 : Stroth711StrongStatement) (hc : Ctx M Q Z B) {t : G} (hs : Sec7Hyp hc 16 t)
    (hp4 : OmegaPlusNat hc t 4) {Z0 Zn : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q)
    (hne : Zn ≠ Z0) {U : Subgroup G} (hZU : Z0 ≤ U) (hUZn : U ≤ Zn)
    (hUinv : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ U = U) : U = Z0 ∨ U = Zn := by
  classical
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  have hq1 : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  obtain ⟨k, hk⟩ := sec79_card_eq_omegaPlus h51 hA hPts hc hs hZ0 hZU (hUZn.trans hZnN) hUinv
    (by norm_num) hp4
  obtain ⟨hcardZn, -⟩ := sec715_card_Zn h51 hA hPts hNO h711 hc hs hp4 hZ0 hZn hne
  rw [show (2 : ℕ) ^ (4 - 1) = 8 by norm_num] at hk
  have hle : Nat.card U ≤ Nat.card Zn := Subgroup.card_le_of_le hUZn
  have hq0 : 0 < Nat.card Z0 := Nat.card_pos
  have hk1 : k ≤ 1 := by
    rw [hk, hcardZn] at hle
    have h1 := Nat.le_of_mul_le_mul_left hle hq0
    have h2 := (Nat.pow_le_pow_iff_right hq1).mp h1
    omega
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZU (by rw [hk]; simp)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hUZn (by rw [hk, hcardZn])

end CFSG.RankThree.GF2n.Stroth80
