module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SL
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem centralizer_Wt_le_of_quadModel {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ) {V : Subgroup G} (hZV : Z ≤ V)
    (hVQ : V ≤ Q) (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    {x : G} (hx : x ∈ Q) (hxW : ∀ w ∈ Wt Q V, ⁅x, w⁆ = 1) : x ∈ V := by
  obtain ⟨S, hSV⟩ : ∃ S : Submodule K M₀.E, ∀ e, e ∈ S ↔ e ∈ M₀.img V :=
    ⟨imgSub M₀ V hS, fun _ => Iff.rfl⟩
  have hRefl : M₀.B.IsRefl := fun e f h => by
    rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hdouble : M₀.B.orthogonal (M₀.B.orthogonal S) = S :=
    LinearMap.BilinForm.orthogonal_orthogonal (modelB_nondegenerate M₀) hRefl S
  have hperp : M₀.π x ∈ M₀.B.orthogonal (M₀.B.orthogonal S) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
    have hew : e ∈ M₀.img (Wt Q V) := (mem_img_Wt_iff M₀ R hVQ).mpr fun v hv => by
      rw [Tim79.QuadModel.B_comm, he v ((hSV v).mpr hv), neg_zero]
    obtain ⟨w, hwW, hwQ, rfl⟩ := hew
    have hcomm : x * w = w * x := commutatorElement_eq_one_iff_mul_comm.mp (hxW w hwW)
    have h0 : M₀.B (M₀.π x) (M₀.π w) = 0 := (M₀.comm_iff_B R hx hwQ).mp hcomm
    rw [Tim79.QuadModel.B_comm, h0, neg_zero]
  have hπS : M₀.π x ∈ S := by
    rw [← hdouble]
    exact hperp
  exact (M₀.mem_img_iff hZV hx).mp ((hSV _).mp hπS)

theorem Ctx.centralizer_Wt_le_Vt (hc : Ctx M Q Z B) (t : G) {x : G} (hx : x ∈ Q)
    (hxW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ = 1) :
    x ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  exact centralizer_Wt_le_of_quadModel M₀ h.reg sec39_Z_le_Vt (hc.Vt_le_Q t)
    (fun c _ he => hc.smul_mem_img_Vt h t c he) hx hxW

end CFSG.RankThree.GF2n.Stroth80
