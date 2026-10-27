module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfOmega
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfG
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfFour
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfStar
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfT9

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem false_of_star
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Concl142 A (lB A))
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) (h1411 : Item1411_1 A (lB A))
    (h : Ctx A c L d) {g : G} (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G))
    (hgc : g * c * g⁻¹ = c * d) {T₀ : Subgroup G}
    (hT₀ : T₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hgT₀ : g ∈ Subgroup.normalizer (T₀ : Set G)) : False := by
  classical
  obtain ⟨c', hc'Ω, hT₀c'⟩ :=
    exists_point_centralizer hbal h134 h48 h152 h153 h1411 h T₀ hT₀
  obtain ⟨-, -, hΩform, -⟩ := omega_case2 h134 h48 h
  obtain ⟨b, hb, hc'eq⟩ := hΩform (Subgroup.zpowers c') hc'Ω
  have hT₀cb : T₀ ≤ Subgroup.centralizer ({c * b} : Set G) := by
    have h1 : T₀ ≤ Subgroup.centralizer (Subgroup.zpowers c' : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hT₀c'
    have h2 : T₀ ≤ Subgroup.centralizer (Subgroup.zpowers (c * b) : Set G) := hc'eq ▸ h1
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h2
  have hdX : d ∈ x₀ L d := h.residual_facts.2.2.2.2.1
  have hbX : b ∈ x₀ L d := (Subgroup.zpowers_le.mpr hdX) hb
  have hgb : g * b * g⁻¹ = b := by
    have hcomm : b * g = g * b :=
      Subgroup.mem_centralizer_iff.mp hgX b hbX
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hgcb : g * (c * b) * g⁻¹ = c * d * b := by
    rw [show g * (c * b) * g⁻¹ = (g * c * g⁻¹) * (g * b * g⁻¹) by group, hgc, hgb]
  have hT₀cdb : T₀ ≤ Subgroup.centralizer ({c * d * b} : Set G) := by
    have hmap : T₀.map (MulAut.conj g).toMonoidHom = T₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgT₀
    have h1 : T₀ ≤ (Subgroup.centralizer ({c * b} : Set G)).map
        (MulAut.conj g).toMonoidHom := by
      rw [← hmap]
      exact Subgroup.map_mono hT₀cb
    have h2 : (Subgroup.centralizer ({c * b} : Set G)).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ({c * d * b} : Set G) := by
      have h := Subgroup.map_centralizer_le_centralizer_image ({c * b} : Set G)
        (MulAut.conj g).toMonoidHom
      simpa [MulAut.conj_apply, hgcb] using h
    exact h1.trans h2
  have hT₀d : T₀ ≤ Subgroup.centralizer ({d} : Set G) := by
    intro t ht
    have h1 : Commute t (c * b) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT₀cb ht)
    have h2 : Commute t (c * d * b) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT₀cdb ht)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : Commute t ((c * b)⁻¹ * (c * d * b)) := (h1.inv_right).mul_right h2
    have hbd : Commute b d := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hk]
      exact (Commute.refl d).zpow_left k
    have hbdc : b⁻¹ * d * b = d := by
      calc b⁻¹ * d * b = b⁻¹ * (d * b) := by group
        _ = b⁻¹ * (b * d) := by rw [← hbd]
        _ = d := by group
    have hd_eq : (c * b)⁻¹ * (c * d * b) = d := by
      calc (c * b)⁻¹ * (c * d * b) = b⁻¹ * (c⁻¹ * c) * d * b := by group
        _ = b⁻¹ * d * b := by group
        _ = d := hbdc
    rwa [hd_eq] at h3
  exact (not_le_centralizer h134 h48 h142 h1411 h T₀ hT₀) hT₀d

end Ctx

@[expose] def Case3Fpf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (d : G),
    Ctx A c L d → (∀ F ∈ omegaA A, F ≤ Subgroup.closure {c, d}) →
    ∀ T T₀ : Subgroup G, T ≤ x₀ L d → T ≠ ⊥ → T ≤ T₀ → IsPGroup 2 ↥T₀ →
      A ≤ Subgroup.normalizer (T₀ : Set G) →
      ∀ hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A,
        letI := ker148_normal hY.2
        ¬ Case148Three A (lB A) (Subgroup.normalizer (T₀ : Set G))

section Main


theorem false_of_ctx
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R) (hc142 : Concl142R)
    (h146 : Item146S14) (h148 : Item148R) (h152 : Item152R) (h153 : Item153MainR)
    (h1411 : Item1411_1R) (h3 : Case3Fpf) {A L : Subgroup G} {c d : G}
    (h : Ctx A c L d) : False := by
  classical
  obtain ⟨g, hgA, hgX, hg3, hgc⟩ := Ctx.exists_g h134 h48 h
  have hc142' : Concl142 A (lB A) := hc142 G A c L h.conf.sec15R
  have h146' : Item146 A (lB A) := h146 G A c L h.conf.sec15R.toSec14Std
  have h148' : Item148 A (lB A) := h148 G A c L h.conf.sec15R
  have h152' : Item152 A (lB A) := h152 G A c L h.conf.sec15R
  have h153' : Item153Main A (lB A) := h153 G A c L h.conf.sec15R
  have h1411' : Item1411_1 A (lB A) := h1411 G A c L h.conf.sec15R
  obtain ⟨T, hTX, hT, hT2, -, hTQ⟩ := Ctx.exists_four hc142' h
  have h3T : ∀ T₀ : Subgroup G, T ≤ T₀ → IsPGroup 2 ↥T₀ →
      A ≤ Subgroup.normalizer (T₀ : Set G) →
      ∀ hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A,
        letI := ker148_normal hY.2
        ¬ Case148Three A (lB A) (Subgroup.normalizer (T₀ : Set G)) := by
    intro T₀ hTT₀ hT₀2 hAT₀ hY
    exact h3 G A c L d h (Ctx.omega_le_closure h134 h48 h) T T₀ hTX hT hTT₀ hT₀2 hAT₀ hY
  obtain ⟨T₀, hT₀, hgT₀⟩ :=
    Ctx.exists_star h134 h48 h142 h146' h148' h hgA hgX hg3 hgc hTX hT hT2 hTQ h3T
  exact Ctx.false_of_star hbal h134 h48 hc142' h152' h153' h1411' h hgX hgc hT₀ hgT₀

theorem step1515HJEndFpfRBoundOff_of
    (hbal : Step143Balance) (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R)
    (hc142 : Concl142R) (h146 : Item146S14) (h148 : Item148R) (h152 : Item152R)
    (h153 : Item153MainR) (h1411 : Item1411_1R) (h3 : Case3Fpf) :
    Step1515HJEndFpfRBoundOff :=
  step1515HJEndFpfRBoundOff_of_false fun _ _ _ _ _ _ _ h =>
    false_of_ctx hbal h134 h48 h142 hc142 h146 h148 h152 h153 h1411 h3 h

end Main

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
