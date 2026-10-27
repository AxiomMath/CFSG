module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55R
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.Sporadic.Th.F2Spec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open S36 (hypF hypU hypA dot)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem comm_of_conj_comm (h y v : G)
    (e : (h⁻¹ * y * h) * (h⁻¹ * v * h) = (h⁻¹ * v * h) * (h⁻¹ * y * h)) : y * v = v * y :=
  calc y * v = h * ((h⁻¹ * y * h) * (h⁻¹ * v * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * v * h) * (h⁻¹ * y * h)) * h⁻¹ := by rw [e]
    _ = v * y := by group

theorem two_le_card_of_mem {K : Subgroup G} {s : G} (hs : orderOf s = 2) (hsK : s ∈ K) :
    2 ≤ Nat.card K := by
  have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hsK)
  rwa [Nat.card_zpowers, hs] at this

section Tools

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.b_ne_one : b ≠ 1 := fun hb => by
  have : e 0 = 0 := h5.ε_eq_one (h5.ε_e0.trans hb)
  exact absurd (congrFun this 0) (by decide)

theorem FF81Sec5.mem_S_of_comm {v : G} (hv : v ∈ Cen s₀)
    (hc : ∀ u ∈ Op 2 (Cen s₀), v * u = u * v) : v ∈ Op 2 (Cen s₀) :=
  h5.basis.mem_op_two_of_comm h5.hs₀ hv hc

theorem FF81Sec5.hyp_le_nor_S (i : Fin 13) : S55.hyp h5.εA i ≤ Nor (Op 2 (Cen s₀)) :=
  (S55.hyp_le h5.coordA i).trans h5.A₁_le_nor_S

theorem FF81Sec5.hyp_le_nor_inf {i : Fin 13} {v : G} (hv : v ∈ CenS (S55.hyp h5.εA i)) :
    S55.hyp h5.εA i ≤ Nor (Op 2 (Cen s₀) ⊓ Cen v) := fun a ha =>
  Subgroup.mem_normalizer_fintype fun y hy => by
    have hy' : y ∈ Op 2 (Cen s₀) ⊓ Cen v := hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (h5.hyp_le_nor_S i ha) y).mp
      hy'.1, ?_⟩
    have hav : a * v = v * a := Subgroup.mem_centralizer_iff.mp hv a ha
    have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp hy'.2
    have hav' : a⁻¹ * v * a = v := by rw [mul_assoc, ← hav, inv_mul_cancel_left]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * y * a⁻¹ * v = a * (y * (a⁻¹ * v * a)) * a⁻¹ := by group
      _ = a * (v * y) * a⁻¹ := by rw [hav', hyv]
      _ = (a * v * a⁻¹) * (a * y * a⁻¹) := by group
      _ = v * (a * y * a⁻¹) := by rw [hav, mul_inv_cancel_right]

theorem FF81Sec5.mem_cenS_hyp₂ {y : G} :
    y ∈ CenS (S55.hyp h5.εA 2) ↔ y * b = b * y ∧ y * b₁ = b₁ * y := by
  rw [h5.coordA.cenS_hyp (by decide) (by decide) S55.span_reps.2.1, h5.εA_b, h5.εA_b₁]

theorem FF81Sec5.mem_cenS_hyp₈ {y : G} :
    y ∈ CenS (S55.hyp h5.εA 8) ↔ y * b = b * y ∧ y * (b₁ * (b₂ * b₃)) = b₁ * (b₂ * b₃) * y := by
  rw [h5.coordA.cenS_hyp (by decide) (by decide) S55.span_reps.2.2.2, h5.εA_b, h5.εA_x₂]

theorem FF81Sec5.comm_b_of_mem_L {v : G} (hv : v ∈ L) : v * b = b * v :=
  Subgroup.mem_centralizer_singleton_iff.mp (h5.basis.hyp.hLC hv)

theorem FF81Sec5.comm_of_card_two {x v : G} (hx : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen x) = 2)
    (hs : s₀ ∈ Cen x) (hv : v ∈ Cen s₀) : Op 2 (Cen s₀) ⊓ Cen x ≤ Cen v := fun y hy => by
  rcases eq_one_or_of_card_two h5.hs₀ (Subgroup.mem_inf.mpr ⟨mem_op_two_self h5.hs₀, hs⟩) hx hy with
    rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hv).symm

theorem FF81Sec5.s₀_mem_cen_A₁ {a : G} (ha : a ∈ A₁sub b b₁ b₂ b₃) : s₀ ∈ Cen a :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp h5.hs₀A a ha).symm

end Tools

section Words

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {g : Fin 3 → G}
  (hgH : ∀ i, g i ∈ H₅₂ b b₁ b₂ b₃ s₀) (hg : ∀ i v, g i * h5.ε v * (g i)⁻¹ = h5.ε (S52.gf i v))
include hgH hg

theorem FF81Sec5.S_inf_cen_act (w : List (Fin 3)) (x : Fin 3 → ZMod 3) :
    Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA w x)) =
      conjBy (S55.wel g w) (Op 2 (Cen s₀) ⊓ Cen (h5.εA x)) := by
  rw [conjBy_op_two_inf_cen (S55.wel_cen hgH w), h5.wel_εA hg]

theorem FF81Sec5.conj_mem_cenS_hyp {w : List (Fin 3)} {r : Fin 13} (hw : S55.Carries w r r)
    {v : G} (hv : v ∈ CenS (S55.hyp h5.εA r)) :
    (S55.wel g w)⁻¹ * v * S55.wel g w ∈ CenS (S55.hyp h5.εA r) := by
  rw [← h5.conjBy_hyp hg hw, conjBy_cenS] at hv
  exact mem_conjBy_iff.mp hv

theorem FF81Sec5.le_cen_of_conj {w : List (Fin 3)} {x : Fin 3 → ZMod 3} {v : G}
    (hv : Op 2 (Cen s₀) ⊓ Cen (h5.εA x) ≤ Cen ((S55.wel g w)⁻¹ * v * S55.wel g w)) :
    Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA w x)) ≤ Cen v := fun y hy => by
  rw [h5.S_inf_cen_act hgH hg] at hy
  have h1 := hv (mem_conjBy_iff.mp hy)
  rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
  exact comm_of_conj_comm _ _ _ h1

end Words

section Cases

variable (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF h5

theorem FF81Sec5.card_S_ne_two (hS : Nat.card (Op 2 (Cen s₀)) = 2) : False := by
  have heq : Op 2 (Cen s₀) ⊓ CenS (A₁sub b b₁ b₂ b₃) = Op 2 (Cen s₀) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hS, h5.card_S_cenS_A₁ hKF])
  have hbA : b ∈ A₁sub b b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
  have hbS : b ∈ Op 2 (Cen s₀) := h5.mem_S_of_comm (h5.A₁_le_cen_s₀ hbA) fun u hu => by
    rw [← heq] at hu
    exact Subgroup.mem_centralizer_iff.mp hu.2 b hbA
  exact h5.b_ne_one (h5.eq_one_of_mem_B_S (h5.A₁_le_B hbA) hbS)

theorem FF81Sec5.not_case_eight (hS : Nat.card (Op 2 (Cen s₀)) = 2 ^ 7)
    (hR : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen b) = 8)
    (hW : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen (b₁ * (b₂ * b₃))) = 2)
    (hQ : ∀ v ∈ L ⊓ Cen s₀ ⊓ Cen (b₁ * (b₂ * b₃)), v ^ 4 = 1 → v ∈ CenS (Op 2 (Cen s₀) ⊓ Cen b))
    {v : G} (hv : v ∈ L ⊓ Cen s₀ ⊓ Cen (b₁ * (b₂ * b₃))) (hv4 : v ^ 4 = 1) (hv1 : v ≠ 1)
    (hvs : v ≠ s₀) : False := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (op_two_isPGroup s₀)
  have hB := h5.basis
  have hvΓ : v ∈ CenS (S55.hyp h5.εA 8) := h5.mem_cenS_hyp₈.mpr
    ⟨h5.comm_b_of_mem_L hv.1.1, Subgroup.mem_centralizer_singleton_iff.mp hv.2⟩
  have hW8 : Nat.card (h5.W 8) = 2 := by rw [h5.W₈_eq]; exact hW
  have key : ∀ w : List (Fin 3), S55.Carries w 8 8 →
      Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA w ![1, 0, 0])) ≤ Cen v := fun w hw => by
    refine h5.le_cen_of_conj hgH hg ?_
    set v' := (S55.wel g w)⁻¹ * v * S55.wel g w with hv'
    have hv'Γ := h5.conj_mem_cenS_hyp hgH hg hw hvΓ
    obtain ⟨hv'b, hv'x⟩ := h5.mem_cenS_hyp₈.mp hv'Γ
    have hv'4 : v' ^ (2 ^ 2) = 1 := by
      have hc := conj_pow (a := (S55.wel g w)⁻¹) (b := v) (i := 4)
      rw [inv_inv] at hc
      rw [hv', show (2 : ℕ) ^ 2 = 4 from rfl, hc, hv4]; group
    have hv'L : v' ∈ L := hB.mem_of_pow_two (Subgroup.mem_centralizer_singleton_iff.mpr hv'b) hv'4
    have hv's : v' ∈ Cen s₀ := (Cen s₀).mul_mem ((Cen s₀).mul_mem
      ((Cen s₀).inv_mem (S55.wel_cen hgH w)) hv.1.2) (S55.wel_cen hgH w)
    have := hQ v' ⟨⟨hv'L, hv's⟩, Subgroup.mem_centralizer_singleton_iff.mpr hv'x⟩ hv'4
    intro y hy
    rw [h5.εA_b] at hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp this y hy)
  have hconj : ∀ w : List (Fin 3), Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA w ![1, 0, 0]))) = 8 :=
    fun w => by rw [h5.S_inf_cen_act hgH hg, card_conjBy, h5.εA_b, hR]
  have hl2 : S55.lv 8 2 = S55.actA [0, 2] ![1, 0, 0] := by decide
  have hl3 : S55.lv 8 3 = S55.actA [2] ![1, 0, 0] := by decide
  have hl0 : h5.εA (S55.lv 8 0) = b₁ * (b₂ * b₃) := by
    rw [show S55.lv 8 0 = ![0, 1, 1] by decide, h5.εA_x₂]
  have hl1 : h5.εA (S55.lv 8 1) = b := by rw [show S55.lv 8 1 = ![1, 0, 0] by decide, h5.εA_b]
  have hwiel := S55.card_mul_pow_three h5.coordA 8 (h5.hyp_le_nor_S 8) hc hs
  rw [Fin.prod_univ_four, hl0, hl1, hl2, hl3, hconj, hconj, hR, hS, hW8] at hwiel
  have hx : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (b₁ * (b₂ * b₃))) = 2 := by omega
  have hxA : b₁ * (b₂ * b₃) ∈ A₁sub b b₁ b₂ b₃ := h5.εA_x₂ ▸ h5.coordA.mem _
  have hlines : ∀ j, Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 8 j)) ≤ Op 2 (Cen s₀) ⊓ Cen v := by
    intro j
    fin_cases j
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 8 0)) ≤ _
      rw [hl0]
      exact le_inf inf_le_left (h5.comm_of_card_two hx (h5.s₀_mem_cen_A₁ hxA) hv.1.2)
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 8 1)) ≤ _
      rw [hl1]
      refine le_inf inf_le_left fun y hy => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hQ v hv hv4) y hy)
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 8 2)) ≤ _
      rw [hl2]
      exact le_inf inf_le_left (key [0, 2] (by decide))
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 8 3)) ≤ _
      rw [hl3]
      exact le_inf inf_le_left (key [2] (by decide))
  have hN := S55.eq_of_lines h5.coordA 8 inf_le_left (h5.hyp_le_nor_S 8) (h5.hyp_le_nor_inf hvΓ)
    hc hs hlines
  have hvS : v ∈ Op 2 (Cen s₀) := h5.mem_S_of_comm hv.1.2 fun u hu => by
    rw [← hN] at hu
    exact (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
  rcases eq_one_or_of_card_two h5.hs₀ (h5.s₀_mem_W 8) hW8 ⟨hvS, hvΓ⟩ with h | h
  exacts [hv1 h, hvs h]

theorem FF81Sec5.not_case_thirtytwo (hS : Nat.card (Op 2 (Cen s₀)) = 2 ^ 9)
    (hR : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen b) = 32)
    (hW : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen b₁) = 2)
    (hT : ∀ v ∈ L ⊓ Cen s₀ ⊓ Cen b₁, v * v = 1 →
      (∀ k ∈ L ⊓ Cen s₀ ⊓ Cen b₁, k * v * k⁻¹ * v = v * (k * v * k⁻¹)) →
        v ∈ CenS (Op 2 (Cen s₀) ⊓ Cen b))
    {v : G} (hv : v ∈ L ⊓ Cen s₀ ⊓ Cen b₁) (hv2 : v * v = 1)
    (hvc : ∀ k ∈ L ⊓ Cen s₀ ⊓ Cen b₁, k * v * k⁻¹ * v = v * (k * v * k⁻¹)) (hv1 : v ≠ 1)
    (hvs : v ≠ s₀) : False := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (op_two_isPGroup s₀)
  have hB := h5.basis
  have h0 := h5.opp_eq_bot
  have hvΓ : v ∈ CenS (S55.hyp h5.εA 2) := h5.mem_cenS_hyp₂.mpr
    ⟨h5.comm_b_of_mem_L hv.1.1, Subgroup.mem_centralizer_singleton_iff.mp hv.2⟩
  have hW2 : Nat.card (h5.W 2) = 2 := by rw [h5.W₂_eq]; exact hW
  have hbA : b ∈ A₁sub b b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
  have hb₁A : b₁ ∈ A₁sub b b₁ b₂ b₃ := Subgroup.subset_closure (by simp)
  have hbs : b ∈ Cen s₀ := h5.A₁_le_cen_s₀ hbA
  have hbb₁ : b * b₁ = b₁ * b :=
    hB.B_comm (h5.A₁_le_B hbA) (h5.A₁_le_B hb₁A)
  set f := S55.wel g [1] with hf
  have hfs : f ∈ Cen s₀ := S55.wel_cen hgH [1]
  have hfb : f⁻¹ * b₁ * f = b := by
    have := h5.wel_εA hg [1] ![1, 0, 0]
    rw [show S55.actA [1] ![1, 0, 0] = ![0, 1, 0] by decide, h5.εA_b, h5.εA_b₁, ← hf] at this
    rw [← this]; group
  have hfb₁ : f⁻¹ * b * f = b₁ := by
    have := h5.wel_εA hg [1] ![0, 1, 0]
    rw [show S55.actA [1] ![0, 1, 0] = ![1, 0, 0] by decide, h5.εA_b, h5.εA_b₁, ← hf] at this
    rw [← this]; group
  have hconjc : ∀ x y : G, x * y = y * x → (f⁻¹ * x * f) * (f⁻¹ * y * f) = (f⁻¹ * y * f) * (f⁻¹ * x * f) :=
    fun x y hxy => by
      calc (f⁻¹ * x * f) * (f⁻¹ * y * f) = f⁻¹ * (x * y) * f := by group
        _ = f⁻¹ * (y * x) * f := by rw [hxy]
        _ = (f⁻¹ * y * f) * (f⁻¹ * x * f) := by group
  set v' := f⁻¹ * v * f with hv'
  have hv'b : v' * b = b * v' := by
    have := hconjc v b₁ (Subgroup.mem_centralizer_singleton_iff.mp hv.2); rwa [hfb] at this
  have hv'b₁ : v' * b₁ = b₁ * v' := by
    have := hconjc v b (h5.comm_b_of_mem_L hv.1.1); rwa [hfb₁] at this
  have hv'2 : v' * v' = 1 := by rw [hv']; calc f⁻¹ * v * f * (f⁻¹ * v * f) = f⁻¹ * (v * v) * f := by group
    _ = 1 := by rw [hv2]; group
  have hv'L : v' ∈ L := hB.mem_of_pow_two (Subgroup.mem_centralizer_singleton_iff.mpr hv'b)
    (k := 1) (by rw [pow_one, sq, hv'2])
  have hv's : v' ∈ Cen s₀ :=
    (Cen s₀).mul_mem ((Cen s₀).mul_mem ((Cen s₀).inv_mem hfs) hv.1.2) hfs
  have hv'K : v' ∈ L ⊓ Cen s₀ ⊓ Cen b₁ :=
    ⟨⟨hv'L, hv's⟩, Subgroup.mem_centralizer_singleton_iff.mpr hv'b₁⟩
  have hv'c : ∀ k ∈ L ⊓ Cen s₀ ⊓ Cen b₁, k * v' * k⁻¹ * v' = v' * (k * v' * k⁻¹) := by
    intro k hk
    have hkb₁ : k * b₁ = b₁ * k := Subgroup.mem_centralizer_singleton_iff.mp hk.2
    have hk'b : (f * k * f⁻¹) * b = b * (f * k * f⁻¹) := by
      have := hconjc (f * k * f⁻¹) (f * b₁ * f⁻¹) (by
        calc (f * k * f⁻¹) * (f * b₁ * f⁻¹) = f * (k * b₁) * f⁻¹ := by group
          _ = f * (b₁ * k) * f⁻¹ := by rw [hkb₁]
          _ = (f * b₁ * f⁻¹) * (f * k * f⁻¹) := by group)
      rw [show f⁻¹ * (f * k * f⁻¹) * f = k by group, show f⁻¹ * (f * b₁ * f⁻¹) * f = b₁ by group]
        at this
      calc (f * k * f⁻¹) * b = f * (k * (f⁻¹ * b * f)) * f⁻¹ := by group
        _ = f * (k * b₁) * f⁻¹ := by rw [hfb₁]
        _ = f * (b₁ * k) * f⁻¹ := by rw [hkb₁]
        _ = b * (f * k * f⁻¹) := by rw [← hfb₁]; group
    obtain ⟨i, l, hl, hkl⟩ := hB.cen_dec' h0 (Subgroup.mem_centralizer_singleton_iff.mpr hk'b)
    have hl_eq : l = b ^ (-i) * (f * k * f⁻¹) := by rw [hkl]; group
    have hk's : f * k * f⁻¹ ∈ Cen s₀ :=
      (Cen s₀).mul_mem ((Cen s₀).mul_mem hfs hk.1.2) ((Cen s₀).inv_mem hfs)
    have hk'b₁ : (f * k * f⁻¹) * b₁ = b₁ * (f * k * f⁻¹) := by
      calc (f * k * f⁻¹) * b₁ = f * (k * (f⁻¹ * b₁ * f)) * f⁻¹ := by group
        _ = f * (k * b) * f⁻¹ := by rw [hfb]
        _ = f * (b * k) * f⁻¹ := by rw [h5.comm_b_of_mem_L hk.1.1]
        _ = b₁ * (f * k * f⁻¹) := by rw [← hfb]; group
    have hlK : l ∈ L ⊓ Cen s₀ ⊓ Cen b₁ := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hl, ?_⟩, ?_⟩
      · rw [hl_eq]; exact (Cen s₀).mul_mem ((Cen s₀).zpow_mem hbs _) hk's
      · rw [hl_eq, Subgroup.mem_centralizer_singleton_iff]
        have hbc : Commute (b ^ (-i)) b₁ := (Commute.zpow_left hbb₁ _)
        calc b ^ (-i) * (f * k * f⁻¹) * b₁ = b ^ (-i) * ((f * k * f⁻¹) * b₁) := by group
          _ = b ^ (-i) * (b₁ * (f * k * f⁻¹)) := by rw [hk'b₁]
          _ = b₁ * (b ^ (-i) * (f * k * f⁻¹)) := by rw [← mul_assoc, hbc.eq, mul_assoc]
    have hlv : l * v * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hv.1.1) (L.inv_mem hl)
    have hcb : Commute (b ^ i) (l * v * l⁻¹) :=
      Commute.zpow_left (h5.comm_b_of_mem_L hlv).symm i
    have e1 : k * v' * k⁻¹ = f⁻¹ * (l * v * l⁻¹) * f := by
      have hk : k = f⁻¹ * (b ^ i * l) * f := by rw [← hkl]; group
      rw [hk, hv']
      calc f⁻¹ * (b ^ i * l) * f * (f⁻¹ * v * f) * (f⁻¹ * (b ^ i * l) * f)⁻¹
          = f⁻¹ * (b ^ i * (l * v * l⁻¹) * (b ^ i)⁻¹) * f := by group
        _ = f⁻¹ * (l * v * l⁻¹) * f := by rw [hcb.eq, mul_inv_cancel_right]
    rw [e1, hv']
    calc f⁻¹ * (l * v * l⁻¹) * f * (f⁻¹ * v * f) = f⁻¹ * (l * v * l⁻¹ * v) * f := by group
      _ = f⁻¹ * (v * (l * v * l⁻¹)) * f := by rw [hvc l hlK]
      _ = f⁻¹ * v * f * (f⁻¹ * (l * v * l⁻¹) * f) := by group
  have hv'R := hT v' hv'K hv'2 hv'c
  have key : Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA [1] ![1, 0, 0])) ≤ Cen v := by
    refine h5.le_cen_of_conj hgH hg ?_
    intro y hy
    rw [h5.εA_b] at hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hv'R y hy)
  have hl3 : S55.lv 2 3 = S55.actA [1] ![1, 0, 0] := by decide
  have hl1 : h5.εA (S55.lv 2 1) = b := by rw [show S55.lv 2 1 = ![1, 0, 0] by decide, h5.εA_b]
  have hb₁c : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.actA [1] ![1, 0, 0]))) = 32 := by
    rw [h5.S_inf_cen_act hgH hg, card_conjBy, h5.εA_b, hR]
  have hwiel := S55.card_mul_pow_three h5.coordA 2 (h5.hyp_le_nor_S 2) hc hs
  rw [Fin.prod_univ_four, hl1, hl3, hb₁c, hR, hS, hW2] at hwiel
  have hs0 := two_le_card_of_mem h5.hs₀ (Subgroup.mem_inf.mpr ⟨mem_op_two_self h5.hs₀,
    h5.s₀_mem_cen_A₁ (h5.coordA.mem (S55.lv 2 0))⟩)
  have hs2 := two_le_card_of_mem h5.hs₀ (Subgroup.mem_inf.mpr ⟨mem_op_two_self h5.hs₀,
    h5.s₀_mem_cen_A₁ (h5.coordA.mem (S55.lv 2 2))⟩)
  have hc0 : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 2 0))) = 2 := by nlinarith
  have hc2 : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 2 2))) = 2 := by nlinarith
  have hlines : ∀ j, Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 2 j)) ≤ Op 2 (Cen s₀) ⊓ Cen v := by
    intro j
    fin_cases j
    · exact le_inf inf_le_left (h5.comm_of_card_two hc0
        (h5.s₀_mem_cen_A₁ (h5.coordA.mem _)) hv.1.2)
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 2 1)) ≤ _
      rw [hl1]
      refine le_inf inf_le_left fun y hy => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hT v hv hv2 hvc) y hy)
    · exact le_inf inf_le_left (h5.comm_of_card_two hc2
        (h5.s₀_mem_cen_A₁ (h5.coordA.mem _)) hv.1.2)
    · change Op 2 (Cen s₀) ⊓ Cen (h5.εA (S55.lv 2 3)) ≤ _
      rw [hl3]
      exact le_inf inf_le_left key
  have hN := S55.eq_of_lines h5.coordA 2 inf_le_left (h5.hyp_le_nor_S 2) (h5.hyp_le_nor_inf hvΓ)
    hc hs hlines
  have hvS : v ∈ Op 2 (Cen s₀) := h5.mem_S_of_comm hv.1.2 fun u hu => by
    rw [← hN] at hu
    exact (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
  rcases eq_one_or_of_card_two h5.hs₀ (h5.s₀_mem_W 2) hW2 ⟨hvS, hvΓ⟩ with h | h
  exacts [hv1 h, hvs h]

end Cases

end CFSG.RankThree.PartTwo.Sec21.FF81
