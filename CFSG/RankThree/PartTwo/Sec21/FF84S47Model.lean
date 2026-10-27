module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreThetaModel
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

theorem M0_model (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) :
    ∃ e : ↥L ≃* ↥A8s, (∀ x : ↥L, (x : G) = b₁ → ((e x : A8s) : P8) = cc) ∧
      ∀ x : ↥L, (x : G) = b₂ → ((e x : A8s) : P8) = dd := by
  obtain ⟨θ, hker, hmem, hsurj, hθ₁, hθ₂⟩ := theta_model hA h.sec
  have hle : L ≤ Nor L := fun x hx => Subgroup.le_normalizer hx
  let ψ : ↥L →* P8 := θ.comp (Subgroup.inclusion hle)
  have hψx : ∀ x : ↥L, ψ x = θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hψx, hker] at hx
    rw [Subgroup.mem_bot]
    have hxc : x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_centralizer_iff.1 hx (y : G) y.2
      exact Subtype.ext this
    rw [h.z1] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hrange : ∀ x : ↥L, ψ x ∈ A8s := fun x => hmem x
  let ψ' : ↥L →* ↥A8s := ψ.codRestrict A8s hrange
  have hbij : Function.Bijective ψ' := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun a => ?_⟩
    obtain ⟨x, hx⟩ := hsurj a.1 a.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨MulEquiv.ofBijective ψ' hbij, ?_, ?_⟩
  · intro x hx
    subst hx
    exact hθ₁
  · intro x hx
    subst hx
    exact hθ₂

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
