module

public import CFSG.LocalAnalysis.StandardType.GGPZNbrResRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwA5Three_torDataNbr
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hnb : GGNbr 3 B x D J y K)
    (hInn : GGInnerDiagOn Bs K) {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    ∃ (f : ℕ) (hN : Bs ≤ Subgroup.normalizer (K : Set G)), 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧
      GGTorusTorData (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) ↥K
        (ggGamma K hN).range := by
  obtain ⟨htw, hr5, hdvd⟩ := htag
  have hmk := ggInnerDiagOn_relabel hRig hInn hΛ hl
  have hmk' : GGInnerDiagOnLabel (fun _ lab => lab = labX) 3 Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1, hP.2⟩) hmk
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs K := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
    obtain ⟨hlab, hN', hBsI⟩ := hP
    subst hlab
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hmark
    (fun hN => ggTwA5Three_rank hLB hPJ hcfg hnb (Or.inr rfl) hmk' ⟨htw, hr5, hdvd⟩ hN)
  exact ⟨f, hN, hf, hpq, hTor⟩

theorem ggPZNbrResDatum_of_rest
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (h : GGPZNbrResDatumRest) : GGPZNbrResDatum := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb hMark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  by_cases hc : lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1
  · obtain ⟨htw, hr5, hp3, hdvd⟩ := hc
    subst hp3
    have hl : GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) :=
      largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨-, -, θ, -⟩ := hQ
        exact ⟨θ⟩) hraw
    have hcfg : GGConfig 3 B Bs x L D J := hprem.1.1
    have hInn : GGInnerDiagOn Bs Y := hprem.1.2.2.1.2 (z : G) Y hnb
    obtain ⟨f, hN, hf, hpq, hTor⟩ :=
      ggTwA5Three_torDataNbr hRig hLB hPJ hcfg hnb hInn hlab hl ⟨htw, hr5, hdvd⟩
    have hodd : Odd (2 ^ f + 1) := by
      obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
      rw [pow_succ]
      exact ⟨2 ^ g, by omega⟩
    have hrefl : CoxeterMatrix.A 5 = (CoxeterMatrix.A 5).reindex (Equiv.refl (Fin 5)) := by
      apply CoxeterMatrix.ext
      ext i j
      rw [CoxeterMatrix.reindex_apply]
      simp
    have hWM : GGIsWeylMatrix (CoxeterMatrix.A 5) :=
      Or.inl ⟨5, Equiv.refl _, by norm_num, Or.inl hrefl⟩
    exact (ggResXDatum_of_torData (by norm_num : (3 : ℕ) ≠ 2) hodd hpq hWM (ggIntCartan_A 5)
      hcfg.tableB_facts.2.1 hcfg.2.1.2.2.2 hN hTor).toSurj
  · refine h G p B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb ⟨hperf, lab, hlab, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨hs, hna, θ, hθ⟩ := hQ
      exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw

end CFSG.StandardType

end
