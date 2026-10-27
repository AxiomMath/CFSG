module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH4

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)


namespace Hering129KH4b

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem liftSub_trans [Yh.Normal] (hD : HessData Yh Bh xh bh ch) (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (hact : ∀ g ∈ Yh ⊔ Bh, ∃ y, Sec4.IsPGLAtP e g y) {y : GL (Fin 3) K}
    (hy : Sec4.IsPGLAtP e bh y) {F : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hF : PglHess π p f K y
      ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) F) :
    ∀ g ∈ Hering129KH4.liftSub e F, g ≠ 1 →
      ∃ n ∈ Yh ⊓ Subgroup.normalizer (Hering129KH4.liftSub e F : Set P), n * ch * n⁻¹ = g := by
  intro g hgF hg1
  obtain ⟨hgY, hgF'⟩ := (Hering129KH4.mem_liftSub e F).mp hgF
  have hne : ((e ⟨g, hgY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    apply hg1
    have h2 : e ⟨g, hgY⟩ = e 1 := by
      rw [map_one]
      exact Subtype.ext h
    exact congrArg Subtype.val (e.injective h2)
  obtain ⟨-, -, -, -, -, -, -, -, hN9, -⟩ := hF
  obtain ⟨n, hnAB, hnm⟩ := hN9 _ hgF' hne
  obtain ⟨hnP, hnN⟩ := Subgroup.mem_inf.mp hnAB
  obtain ⟨x, hx⟩ : ∃ x : ↥Yh, e x = ⟨n, hnP⟩ :=
    ⟨e.symm ⟨n, hnP⟩, e.apply_symm_apply _⟩
  have hconj : e (x * ⟨ch, hD.cY⟩ * x⁻¹) = e ⟨g, hgY⟩ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, hx, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hnm
  have hcg : (x : P) * ch * (x : P)⁻¹ = g := by
    have h2 := congrArg Subtype.val (e.injective hconj)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hnorm : (x : P) ∈ Subgroup.normalizer (Hering129KH4.liftSub e F : Set P) := by
    apply Subgroup.mem_normalizer_fintype
    intro h hh
    rw [SetLike.mem_coe] at hh ⊢
    obtain ⟨hhY, hhF⟩ := (Hering129KH4.mem_liftSub e F).mp hh
    have hconjY : (x : P) * h * (x : P)⁻¹ ∈ Yh :=
      Subgroup.Normal.conj_mem ‹Yh.Normal› h hhY (x : P)
    refine (Hering129KH4.mem_liftSub e F).mpr ⟨hconjY, ?_⟩
    have hsub : (⟨(x : P) * h * (x : P)⁻¹, hconjY⟩ : ↥Yh) = x * ⟨h, hhY⟩ * x⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((e ⟨(x : P) * h * (x : P)⁻¹, hconjY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        n * ((e ⟨h, hhY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) * n⁻¹ := by
      rw [hsub]
      simp only [map_mul, map_inv, hx, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [key]
    exact (Subgroup.mem_normalizer_iff.mp hnN _).mp hhF
  exact ⟨(x : P), Subgroup.mem_inf.mpr ⟨x.2, hnorm⟩, hcg⟩

end Hering129KH4b

end CFSG.RankThree.PartTwo.Sec12
