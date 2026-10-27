module

public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
import CFSG.RankThree.GF2n.Stroth80.Sec112Plane
import CFSG.RankThree.GF2n.Stroth80.Sec112Count
import CFSG.RankThree.GF2n.Stroth80.Sec112Class
import CFSG.RankThree.GF2n.Stroth80.Sec112Model
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.mem_class_of_mem_Ebar [(Q.subgroupOf M).Normal] [CharP K 2] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hA : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B) : ∃ x ∈ Xbar M Q Z B, x * t * x⁻¹ = f := by
  by_contra hnot
  obtain ⟨W, hW4, hWnd, hWE, hWst⟩ := hc.exists_four_space_of_not_conj hw hn h hφπ hφker hφiso
    ht hf fun x hx hxe => hnot ⟨x, hx, hxe⟩
  have hQW : Q ≤ M₀.lift W.toAddSubgroup := by
    refine hc.hyp.gen.le.trans (iSup₂_le fun g hg => ?_)
    by_cases hgZ : conjSubgroup g Z = Z
    · intro z hz
      rw [hgZ] at hz
      refine ⟨h.reg.V_le hz, ?_⟩
      rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
      exact W.toAddSubgroup.zero_mem
    · have hc' : Ctx M Q Z (conjSubgroup g Z) := ⟨hc.hyp, ⟨g, rfl⟩, hg, hgZ⟩
      intro u hu
      exact ⟨hg hu, hc.img_le_of_planes_le hw hn hA h hφπ hφker hφiso hWnd hWst hWE hc' _
        (M₀.pi_mem_img hu (hg hu))⟩
  have htop : W = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj v
    exact (hQW hx).2
  have hK : 1 < Nat.card K := by
    have := hc.hyp.q4
    rw [h.card]
    omega
  have hE := h.finrank_E hw hK
  rw [htop, finrank_top] at hW4
  omega

end Model

theorem stroth112_holds : Stroth112Statement := by
  intro G _ _ M Q Z B _ hc n hw hn hA
  obtain ⟨q, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have hD := isRootInvolutionSet_A2Set_inter hc h hφπ hφker hφiso
  have hE := hc.isRootInvolutionSet_Ebar hD
  obtain ⟨a, haL, haA⟩ := hA
  have ha := hc.mk_mem_Ebar haL haA
  refine ⟨⟨_, ha, Set.ext fun e => ⟨fun he => ?_, ?_⟩⟩,
    fun e₁ he₁ e₂ he₂ => ⟨hE.2.1 e₁ he₁ e₂ he₂, hE.2.2 e₁ he₁ e₂ he₂⟩⟩
  · obtain ⟨x, hx, hxe⟩ :=
      hc.mem_class_of_mem_Ebar hw hn ⟨a, haL, haA⟩ h hφπ hφker hφiso ha he
    exact ⟨x, hx, hxe.symm⟩
  · rintro ⟨x, -, rfl⟩
    exact hc.Ebar_conj ha x

theorem Ctx.ebarIsXbarClass {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hA : ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    EbarIsXbarClassStatement M Q Z B := by
  obtain ⟨⟨e₀, he₀, hE⟩, -⟩ := stroth112_holds G M Q Z B hc n hw hn hA
  exact ⟨e₀, he₀, fun e => by rw [hE]; exact Iff.rfl⟩

end CFSG.RankThree.GF2n.Stroth80
