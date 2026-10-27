module

public import CFSG.RankThree.GF2n.Stroth80.Sec7ActOp
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}

theorem sec7_conjMod_conj (hc : Ctx M Q Z B) {t f m : G} (hfc : ConjMod M Q t f) (hm : m ∈ M) :
    ConjMod M Q t (m * f * m⁻¹) := by
  obtain ⟨hfM, g₀, hg₀, hq⟩ := hfc
  refine ⟨M.mul_mem (M.mul_mem hm hfM) (M.inv_mem hm), m * g₀, M.mul_mem hm hg₀, ?_⟩
  have e : m * f * m⁻¹ * (m * g₀ * t * (m * g₀)⁻¹)⁻¹ = m * (f * (g₀ * t * g₀⁻¹)⁻¹) * m⁻¹ := by
    group
  rw [e]
  exact (hc.conj_mem_Q_of_mem_M hm).1 _ hq

section SDef

variable (M B M₀) (t : G)

@[expose] noncomputable def sec7Ssub : Submodule K M₀.E :=
  Submodule.span K {e | ∃ f ∈ LB M Q B, ConjMod M Q t f ∧ e ∈ M₀.img (Ut Q Z f)}

end SDef

variable (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}

include hc hS

theorem sec7Ssub_le_perp (hVQ : Vt M (LB M Q B) B Z t ≤ Q)
    (hfW : ∀ f ∈ LB M Q B, ConjMod M Q t f → ∀ a ∈ Ut Q Z f,
      ∀ b ∈ Vt M (LB M Q B) B Z t, b * a = a * b) :
    sec7Ssub M B M₀ t ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := by
  refine Submodule.span_le.mpr ?_
  rintro e ⟨f, hfL, hfc, he⟩
  obtain ⟨a, haU, haQ, rfl⟩ := M₀.mem_img.mp he
  rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨b, hbV, hbQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hn)
  exact (M₀.comm_iff_B hS.model.reg hbQ haQ).mp (hfW f hfL hfc a haU b hbV)

theorem sec7Ssub_iso
    (hpair : ∀ f ∈ LB M Q B, ConjMod M Q t f → ∀ f' ∈ LB M Q B, ConjMod M Q t f' →
      ∀ a ∈ Ut Q Z f, ∀ b ∈ Ut Q Z f', ⁅a, b⁆ = 1) :
    ∀ x ∈ sec7Ssub M B M₀ t, ∀ y ∈ sec7Ssub M B M₀ t, M₀.B x y = 0 := by
  refine sec7_span_iso M₀.B _ ?_
  rintro e ⟨f, hfL, hfc, he⟩ e' ⟨f', hf'L, hf'c, he'⟩
  obtain ⟨a, haU, haQ, rfl⟩ := M₀.mem_img.mp he
  obtain ⟨b, hbU, hbQ, rfl⟩ := M₀.mem_img.mp he'
  exact (M₀.comm_iff_B hS.model.reg haQ hbQ).mp
    (commutatorElement_eq_one_iff_mul_comm.mp (hpair f hfL hfc f' hf'L hf'c a haU b hbU))

theorem sec7Ssub_inv {m : G} (hm : m ∈ H0 M Z) (hmL : conjSubgroup m (LB M Q B) = LB M Q B) :
    ∀ s ∈ sec7Ssub M B M₀ t, sec7Op hc hS hm s ∈ sec7Ssub M B M₀ t := by
  have hmQ : conjSubgroup m Q = Q := hc.conj_Q_eq hm.1
  have hmZ : conjSubgroup m Z = Z := hc.conj_Z_eq hm.1
  have hle : Submodule.map (sec7Op hc hS hm) (sec7Ssub M B M₀ t) ≤ sec7Ssub M B M₀ t := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro e ⟨f, hfL, hfc, he⟩
    obtain ⟨a, haU, haQ, rfl⟩ := M₀.mem_img.mp he
    refine Submodule.subset_span ⟨m * f * m⁻¹, ?_, sec7_conjMod_conj hc hfc hm.1, ?_⟩
    · have h1 : m * f * m⁻¹ ∈ conjSubgroup m (LB M Q B) := by
        rw [mem_conjSubgroup, show m⁻¹ * (m * f * m⁻¹) * m = f by group]
        exact hfL
      rwa [hmL] at h1
    · refine ⟨m * a * m⁻¹, ?_, (hc.conj_mem_Q_of_mem_M hm.1).1 a haQ, ?_⟩
      · rw [Ut_conj_of_normalizes hmQ hmZ f, mem_conjSubgroup,
          show m⁻¹ * (m * a * m⁻¹) * m = a by group]
        exact haU
      · exact (sec7Op_pi hc hS hm haQ)
  intro s hs
  exact hle (Submodule.mem_map_of_mem hs)

end

end CFSG.RankThree.GF2n.Stroth80
