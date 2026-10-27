module

public import CFSG.RankThree.GF2n.Stroth80.Sec79Split
public import CFSG.RankThree.GF2n.Stroth80.OppDecompSplit
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


@[expose] def Sec7WVSplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ P : Subgroup G, Vt M (LB M Q B) B Z t ≤ P →
    P ≤ Wt Q (Vt M (LB M Q B) B Z t) → (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) →
    ∃ r : G, Sec7A hc t r ∧
      IsOppDecomp P (Vt M (LB M Q B) B Z t) (LB M Q B) (LB M Q (conjSubgroup r B))
        (P ⊓ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t))
        (P ⊓ ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t))

theorem sec7WVSplit_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) : Sec7WVSplitStatement := by
  intro G _ _ M Q Z B hc n t hs P hVP hPW hPR
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  refine ⟨r, hr, ?_⟩
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  obtain ⟨-, hWN⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hWn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx y hy =>
    sec7WVOrd_conj_mem hc ht hx hy
  have hWN' : ∀ s ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, y⁆ ∈ Vt M (LB M Q B) B Z t := hWN
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm')
      (nondegenerate_polarBilin_quadPlus m' K) (by rw [hι]; omega) φ hrange hker hWn hVn hWN'
      hd hLR hL2R hu hu' huu' (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hVP hPW hPR
    exact isOppDecomp_of_split hd hVP hPW hsplit
  · have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := sec79_split_of_hom (ElemMatrixIso.minus hm' hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m' K hirr) (by rw [hι]; omega) φ hrange hker
      hWn hVn hWN' hd hLR hL2R hu hu' huu'
      (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu') hVP hPW hPR
    exact isOppDecomp_of_split hd hVP hPW hsplit

end CFSG.RankThree.GF2n.Stroth80
