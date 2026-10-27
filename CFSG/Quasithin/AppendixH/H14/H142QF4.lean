module

public import CFSG.Quasithin.AppendixH.H14.H142Q
public import CFSG.Quasithin.AppendixH.H14.H142TabF4

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Open
open scoped Pointwise

@[expose] noncomputable def qAct :
    ↥stdMQ →* MulAut (Multiplicative (Fin 2 → GF4)) :=
  actHom stdEQ_normal (tabEquiv qTab_ok)

theorem qAct_rep_apply {k : ℕ} (hk : k < 360) {n : ℕ} (hn : n < 16) :
    qAct ⟨qRep k, (qRep_spec hk).2⟩ (Multiplicative.ofAdd (wOfCode n)) =
      Multiplicative.ofAdd (wOfCode (qMat k n)) := by
  let hN : ∀ g ∈ stdMQ, ∀ e ∈ tabSub qTabArr qTab_ok, g * e * g⁻¹ ∈ tabSub qTabArr qTab_ok :=
    stdEQ_normal
  change actHom hN (tabEquiv qTab_ok) ⟨qRep k, (qRep_spec hk).2⟩
      (Multiplicative.ofAdd (wOfCode n)) = Multiplicative.ofAdd (wOfCode (qMat k n))
  rw [← tabEquiv_apply qTab_ok hn]
  rw [actHom_apply]
  simp only [Subtype.coe_mk]
  refine (congrArg (tabEquiv qTab_ok) ?_).trans (tabEquiv_apply qTab_ok (qMat_lt k hk n hn))
  apply Subtype.ext
  exact qRep_conj hk hn

theorem qAct_eq_rep (x : ↥stdMQ) :
    ∃ (k : ℕ) (hk : k < 360), qAct x = qAct ⟨qRep k, (qRep_spec hk).2⟩ := by
  obtain ⟨g, hg⟩ := x
  obtain ⟨k, hk, e, he, hge⟩ := stdMQ_decomp g hg
  subst g
  refine ⟨k, hk, ?_⟩
  apply MulEquiv.ext
  intro v
  obtain ⟨y, rfl⟩ := (tabEquiv qTab_ok).surjective v
  obtain ⟨n, hn, hy⟩ := (mem_tabSub qTab_ok).mp y.2
  obtain ⟨m, hm, heq⟩ := (mem_tabSub qTab_ok).mp he
  have hcomm : e * (y : S24) = (y : S24) * e := by
    rw [heq, hy]
    exact tabPerm_comm qTab_ok hm hn
  let hN : ∀ g ∈ stdMQ, ∀ e ∈ tabSub qTabArr qTab_ok, g * e * g⁻¹ ∈ tabSub qTabArr qTab_ok :=
    stdEQ_normal
  change actHom hN (tabEquiv qTab_ok) (⟨qRep k * e, hg⟩ : ↥stdMQ) ((tabEquiv qTab_ok) y) =
    actHom hN (tabEquiv qTab_ok) ⟨qRep k, (qRep_spec hk).2⟩ ((tabEquiv qTab_ok) y)
  conv_lhs => rw [actHom_apply]
  conv_rhs => rw [actHom_apply]
  simp only [Subtype.coe_mk]
  refine congrArg (tabEquiv qTab_ok) ?_
  apply Subtype.ext
  calc
    (qRep k * e) * (y : S24) * (qRep k * e)⁻¹
        = qRep k * (e * (y : S24)) * (qRep k * e)⁻¹ := by group
    _ = qRep k * ((y : S24) * e) * (qRep k * e)⁻¹ := by rw [hcomm]
    _ = qRep k * (y : S24) * (qRep k)⁻¹ := by group

theorem qAct_rep_semilinear {k : ℕ} (hk : k < 360) :
    SemilinearOf (sigE (qSig k)) (qAct ⟨qRep k, (qRep_spec hk).2⟩) := by
  intro c w
  have hw : qAct ⟨qRep k, (qRep_spec hk).2⟩ (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (wOfCode (qMat k (codeOf w))) := by
    conv_lhs => rw [← wOfCode_codeOf w]
    exact qAct_rep_apply hk (codeOf_lt w)
  have hcw : qAct ⟨qRep k, (qRep_spec hk).2⟩ (Multiplicative.ofAdd (c • w)) =
      Multiplicative.ofAdd (wOfCode (qMat k (codeOf (c • w)))) := by
    conv_lhs => rw [← wOfCode_codeOf (c • w)]
    exact qAct_rep_apply hk (codeOf_lt (c • w))
  rw [hcw, hw]
  simp only [toAdd_ofAdd]
  rcases qMat_semilin k hk with ⟨hs, -, -, hsem⟩
  have h := semilinear_of_code (M := qMat k) (qSig k) hs (qMat_lt k hk) hsem c w
  rw [← sigE_apply (qSig k) c] at h
  exact congrArg Multiplicative.ofAdd h

theorem qAct_mem (x : ↥stdMQ) :
    qAct x ∈ gammaLset 2 GF4 := by
  obtain ⟨k, hk, hxk⟩ := qAct_eq_rep x
  rw [hxk, mem_gammaLset2_iff]
  exact ⟨sigE (qSig k), qAct_rep_semilinear hk⟩

theorem qAct_surj :
    ∀ γ ∈ gammaLset 2 GF4, ∃ x : ↥stdMQ, qAct x = γ := by
  intro γ hγ
  obtain ⟨s, hs, v0, hv0, v1, hv1, hgood, h0, h1, hσ⟩ :=
    exists_triple_of_mem_gammaLset hγ
  obtain ⟨k, hk, hsig, hV0, hV1⟩ := qTriples_cover s hs v0 hv0 v1 hv1 hgood
  refine ⟨⟨qRep k, (qRep_spec hk).2⟩, ?_⟩
  have hsem : SemilinearOf (sigE s) (qAct ⟨qRep k, (qRep_spec hk).2⟩) := by
    simpa only [hsig] using qAct_rep_semilinear hk
  have hq1 : qMat k 1 = v0 := by rw [(qMat_semilin k hk).2.1, hV0]
  have hq4 : qMat k 4 = v1 := by rw [(qMat_semilin k hk).2.2.1, hV1]
  apply eq_of_triple hsem hσ
  · rw [qAct_rep_apply hk (by norm_num), hq1, h0]
  · rw [qAct_rep_apply hk (by norm_num), hq4, h1]

theorem stdMQ_conjIso :
    ConjIso stdMQ stdEQ (Multiplicative (Fin 2 → GF4)) (gammaLset 2 GF4) (tabEquiv qTab_ok)
      qAct := by
  exact conjIso_of_actHom stdEQ_le_stdMQ stdEQ_normal (tabEquiv qTab_ok) (gammaLset 2 GF4)
    qAct_mem qAct_surj stdEQ_selfCentralizing

theorem stdMQ_conjIsoModel :
    ConjIsoModel stdMQ stdEQ (Multiplicative (Fin 2 → GF4)) (gammaLset 2 GF4) :=
  ⟨tabEquiv qTab_ok, qAct, stdMQ_conjIso⟩

end CFSG.Quasithin.AppendixH.H14
