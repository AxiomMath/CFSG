module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
public import CFSG.HardMathSupport.Kantor79.LongRoot
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.cmComm_kantor_instance (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    (∀ x : ↥(cmComm M Q Z B K γ M₀ φ), (∀ y, polar (cmCommQf B φ) x y = 0) → x = 0) ∧
      (∀ s v, cmCommQf B φ (cmCommAct hc φ s v) = cmCommQf B φ v) ∧
      (∀ v : ↥(cmComm M Q Z B K γ M₀ φ), (∀ s, cmCommAct hc φ s v = v) → v = 0) ∧
      commutatorSpace (cmCommAct hc φ).range = ⊤ ∧
      ∀ s : ↥(XbarH M Q Z B), ((s : ↥(H0 M Z)) : G) ∈ LB M Q B →
        IsA2 Q Z ((s : ↥(H0 M Z)) : G) →
        IsLongRootElement (cmCommQf B φ) (cmCommAct hc φ s) := by
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f := by
    intro g e f
    have h1 := M₀.Qf_add (φ g e) (φ g f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφQ g, hφQ g e, hφQ g f] at h1
    linear_combination h2 - h1
  have hnd := hc.cmCommQf_nondegenerate hD φ hφπ
  refine ⟨hnd, fun s v => cmCommQf_cmCommAct hc φ hφQ s v, fun v hv => ?_,
    hc.commutatorSpace_cmCommAct_eq_top hD φ hφπ hφB, fun s hsL hsA => ?_⟩
  · refine Subtype.ext (hc.eq_zero_of_fixed_of_mem_cmComm hD φ hφπ hφB v.2 fun s => ?_)
    exact congrArg Subtype.val (hv s)
  · obtain ⟨h1, h2⟩ := hc.cmCommAct_moved hD hKZ φ hφπ ha2 hsL hsA
    exact (isLongRootElement_iff hnd).mpr ⟨fun v => cmCommQf_cmCommAct hc φ hφQ s v, h1, h2⟩

end CFSG.RankThree.GF2n.Stroth80
