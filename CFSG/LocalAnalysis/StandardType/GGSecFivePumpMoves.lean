module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpAbsorb
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPumpup_mem_ggAutomizer_of_moves {G : Type} [Group G] [Finite G]
    {Bs K Y J Kd X : Subgroup G} {r₁ rδ rρ : MulAut ↥Bs} {d b : ↥Bs}
    (hBs : ∀ a c : ↥Bs, a * c = c * a) (hK : IsComponentOf K Y)
    (hY : Subgroup.centralizer (ggHyperplane Bs r₁ : Set G) ≤ Y)
    (hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn K Bs r₁)) (hr₁ : r₁ ∈ ggAutomizer K Bs)
    (hr₁2 : r₁ * r₁ = 1) (hsub : IsSubnormal Kd (Subgroup.centralizer ({(d : G)} : Set G)))
    (hJKd : J ≤ Kd) (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G)) (hδ : rδ ∈ ggAutomizer X Bs)
    (hρ : rρ ∈ ggAutomizer J Bs) (hd : (rδ * r₁ * rδ⁻¹) d = d)
    (hb : (rδ * r₁ * rδ⁻¹) (rρ b) = rρ b) (hb' : (rδ * r₁ * rδ⁻¹) b ≠ b) :
    rδ * r₁ * rδ⁻¹ ∈ ggAutomizer Kd Bs := by
  obtain ⟨n₁, hn₁S, hn₁N, hn₁⟩ := ggExists_weylElt_of_mem_ggAutomizer hr₁ hr₁2
  obtain ⟨nδ, -, hnδN, hnδ⟩ := mem_ggAutomizer_iff.mp hδ
  obtain ⟨nρ, hnρJ, -, hnρ⟩ := mem_ggAutomizer_iff.mp hρ
  have hinv := inv_apply_of_forall hnδ
  have hfix : ∀ y, (rδ * r₁ * rδ⁻¹) y = y → r₁ (rδ⁻¹ y) = rδ⁻¹ y := fun y h => by
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    simpa only [MulAut.inv_apply_self] using congrArg (fun z => rδ⁻¹ z) h
  have hdH : ((rδ⁻¹ d : ↥Bs) : G) ∈ (ggHyperplane Bs r₁ : Set G) :=
    ⟨rδ⁻¹ d, hfix d hd, rfl⟩
  have hN := hsub.map (MulAut.conj nδ⁻¹).toMonoidHom
  have hZ : Subgroup.centralizer (ggHyperplane Bs r₁ : Set G) ≤
      (Subgroup.centralizer ({(d : G)} : Set G)).map (MulAut.conj nδ⁻¹).toMonoidHom := by
    intro z hz
    have hc := Subgroup.mem_centralizer_iff.mp hz _ hdH
    rw [hinv] at hc
    refine ⟨nδ * z * nδ⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · calc nδ * z * nδ⁻¹ * (d : G) = nδ * (z * (nδ⁻¹ * d * nδ)) * nδ⁻¹ := by group
        _ = (d : G) * (nδ * z * nδ⁻¹) := by rw [← hc]; group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hcJ : ((rρ b * b⁻¹ : ↥Bs) : G) ∈ J := by
    have h := (Subgroup.mem_normalizer_iff.mp (hBsJ b.2) nρ⁻¹).mp (J.inv_mem hnρJ)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hnρ]
    simpa only [mul_assoc] using J.mul_mem hnρJ h
  have hu : ((rδ⁻¹ (rρ b * b⁻¹) : ↥Bs) : G) ∈
      Kd.map (MulAut.conj nδ⁻¹).toMonoidHom :=
    ⟨_, hJKd hcJ, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hinv]⟩
  have huC : ((rδ⁻¹ (rρ b * b⁻¹) : ↥Bs) : G) ∈
      Subgroup.centralizer (ggHyperplane Bs r₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, -, rfl⟩
    exact congrArg Subtype.val (hBs c (rδ⁻¹ (rρ b * b⁻¹)))
  have hne : n₁ * ((rδ⁻¹ (rρ b * b⁻¹) : ↥Bs) : G) ≠
      ((rδ⁻¹ (rρ b * b⁻¹) : ↥Bs) : G) * n₁ := fun h => hb' <| by
    have hr : r₁ (rδ⁻¹ (rρ b * b⁻¹)) = rδ⁻¹ (rρ b * b⁻¹) :=
      Subtype.ext (by rw [hn₁, h, mul_inv_cancel_right])
    have h1 : rδ⁻¹ (rρ b) * (r₁ (rδ⁻¹ b))⁻¹ = rδ⁻¹ (rρ b) * (rδ⁻¹ b)⁻¹ := by
      simpa only [map_mul, map_inv, hfix _ hb] using hr
    have h3 : r₁ (rδ⁻¹ b) = rδ⁻¹ b := inv_injective (mul_left_cancel h1)
    rw [MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.apply_inv_self]
  have hn₁N' : n₁ ∈ Kd.map (MulAut.conj nδ⁻¹).toMonoidHom :=
    ggRankOneIn_le_of_isSubnormal hK hY hq hN hZ hn₁S hu huC hne hn₁S
  obtain ⟨c, hc, hcn⟩ := hn₁N'
  refine mem_ggAutomizer_iff.mpr ⟨nδ * n₁ * nδ⁻¹, ?_,
    mul_mem (mul_mem hnδN hn₁N) (inv_mem hnδN), fun b => ?_⟩
  · have h : nδ * n₁ * nδ⁻¹ = c := by
      rw [← hcn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h]
    exact hc
  · rw [MulAut.mul_apply, MulAut.mul_apply, hnδ, hn₁, hinv]
    group

end CFSG.StandardType

end
