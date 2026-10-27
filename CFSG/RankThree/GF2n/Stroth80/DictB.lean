module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Stroth80.Conj
public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.isElemAbelian_Z (H : StrothHyp M Q Z) : CFSG.Open.IsElemAbelian 2 Z := by
  obtain ⟨n, k, -, hcp⟩ := H.cp
  exact ⟨H.maxAb.prop.2.2, sq_eq_one_of_cp hcp⟩

theorem Ctx.isElemAbelian_B (hc : Ctx M Q Z B) : CFSG.Open.IsElemAbelian 2 B := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [hg]
  exact CFSG.Open.IsElemAbelian.map hc.hyp.isElemAbelian_Z (MulAut.conj g).toMonoidHom

theorem Ctx.Z_le_Q (hc : Ctx M Q Z B) : Z ≤ Q := hc.hyp.Z_normal.1

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.dictB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    ∃ b : M₀.E, b ≠ 0 ∧ M₀.Qf b = 0 ∧ (∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) ∧
      (∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0) ∧
      Nat.card Q = Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) * Nat.card Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hZB : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hc.ne
  have hBQ : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hc.le
  obtain ⟨b, hb0, hb⟩ := h.line g hZB hBQ
  rw [← hg] at hb
  refine ⟨b, hb0, Tim79.QuadModel.IsLine.qf_zero h.reg (hc.le) hc.isElemAbelian_B hb,
    hb, fun x hx => Tim79.QuadModel.centralizer_iff h.reg hc.le hb hx, ?_⟩
  have := Tim79.QuadModel.card_centralizer h.reg hc.le hb0 hb
  rw [h.card] at this
  exact this

theorem Ctx.exists_swap (hc : Ctx M Q Z B) :
    ∃ n : G, conjSubgroup n Q = QB B ∧ conjSubgroup n (QB B) = Q := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hc.le
  obtain ⟨n, -, h1, h2⟩ := hc.hyp.toHyp79.exists_swap hgV hgQ
  have hQB := (Ctx.QB_eq hc hg).2
  exact ⟨n, h1.trans hQB.symm, by rw [hQB]; exact h2⟩

end CFSG.RankThree.GF2n.Stroth80
