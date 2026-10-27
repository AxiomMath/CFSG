module

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeAx
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusTorW_uni_six_three_label_all
    {f : ℕ} (hf : 1 ≤ f) (hpq : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ I _ =>
      GGTorusTorW 3 4 (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) R I := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, hQ', ggTorusTorW_unitary_six_three_two hK⟩
  · exact ggTorusTorW_uni_six_three_label h2 hpq

theorem ggTwA5Three_torData
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {X : Subgroup G}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs X)
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ f : ℕ, 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧
      GGHasLabel ⟨.twA, 5, f⟩ (↥X ⧸ Subgroup.center ↥X) ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        GGTorusTorData (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5)
          ↥X (ggGamma X hN).range := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP, -⟩ := hQ₀
  obtain ⟨t, r, f⟩ := lab
  change t = .twA ∧ r = 5 ∧ 3 ∣ ggTorM ⟨t, r, f⟩ at hP
  obtain ⟨rfl, rfl, hpq'⟩ := hP
  have hpq : 3 ∣ 2 ^ f + 1 := by simpa [ggTorM] using hpq'
  have hf : 1 ≤ f := hlab.1
  have hHas : GGHasLabel ⟨.twA, 5, f⟩ (↥X ⧸ Subgroup.center ↥X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R, iR, I, F, hQ, hWtor⟩ :=
    largeEvenRawDatum_exists (ggTorusTorW_uni_six_three_label_all hf hpq _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_card hcfg (by norm_num : 3 ≤ 4) hperf θ hN
    (fun b hb => ggLAut_mem_of_induces X θ hN hBsI hb) (hr hN)
  exact ⟨f, hf, hpq, hHas, hN, hWtor ↥X (ggQuotHom θ) (ggGamma X hN).range hTB⟩

theorem ggTwA5Three_rank
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hnb : GGNbr 3 B x D J y K)
    {X : Subgroup G} (hX : X = L ∨ X = K) {labX : LargeEvenLabel}
    (hmk : GGInnerDiagOnLabel (fun _ lab => lab = labX) 3 Bs X)
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  obtain ⟨htw, hr5, hdvd⟩ := htag
  rcases hX with rfl | rfl
  · have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs X := by
      refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
      obtain ⟨hlab, hN', hBsI⟩ := hP
      subst hlab
      exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩,
        Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩), hN', hBsI⟩
    have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x X D J hcfg hM
    obtain ⟨hp', hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
    have hS : LargeEvenSStar 3 B x X := hcfg.1.2.2.2.2.2.2.1
    have hmul := card_range_ggGamma_mul_of hp' hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp'.pos
  · have hM : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs X := by
      refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
      obtain ⟨hlab, hN', hBsI⟩ := hP
      subst hlab
      exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩, hN', hBsI⟩
    exact ggUnitDvd63NbrRankInput_holds hLB hPJ G 3 B Bs x L D J hcfg y X hnb hN hM

private theorem twA5Three_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {D : Subgroup G} {a b : G} (hD : D = Subgroup.closure ({a, b} : Set G))
    (hDea : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) : a ≠ 1 := by
  intro ha1
  have hbD : b ∈ D := hD ▸ Subgroup.subset_closure (by simp)
  have hcl : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers b := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro z hz
      rcases hz with hz | hz
      · rw [hz, ha1]
        exact Subgroup.one_mem _
      · simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Subgroup.mem_zpowers b
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have h1 : Nat.card D ≤ p := by
    rw [hD, hcl, Nat.card_zpowers]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos
      (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 b hbD))
  have : p ^ 2 ≤ p := by simpa [hDcard] using h1
  nlinarith [(Fact.out : p.Prime).two_le]

theorem ggResHyp_orderOf_xy {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : orderOf x = p ∧ orderOf y = p := by
  have hDcl : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hDea : IsElemAbelian p D := hH.1.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hx1 : x ≠ 1 := twA5Three_ne_one hDcl hDea hDcard
  have hy1 : y ≠ 1 := twA5Three_ne_one (b := x) (by rw [hDcl, Set.pair_comm]) hDea hDcard
  exact ⟨orderOf_eq_prime (hDea.2 x hxD) hx1, orderOf_eq_prime (hDea.2 y hyD) hy1⟩

theorem ggTwA5Three_torDataAt
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {z : G} (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) (hp3 : p = 3)
    {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    ∃ (f : ℕ) (hN : Bs ≤ Subgroup.normalizer (X : Set G)), 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧
      GGTorusTorData (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) ↥X
        (ggGamma X hN).range := by
  subst hp3
  obtain ⟨htw, hr5, hdvd⟩ := htag
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hX : X = L ∨ X = K := hXz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hInn : GGInnerDiagOn Bs X := by
    rcases hXz with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hH.2.2.1.1
    · exact hH.2.2.1.2 y X hnb
  have hmk := ggInnerDiagOn_relabel hRig hInn hΛ hl
  have hmk' : GGInnerDiagOnLabel (fun _ lab => lab = labX) 3 Bs X :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1, hP.2⟩) hmk
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs X := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
    obtain ⟨hlab, hN', hBsI⟩ := hP
    subst hlab
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hmark
    (fun hN => ggTwA5Three_rank hLB hPJ hcfg hnb hX hmk' ⟨htw, hr5, hdvd⟩ hN)
  exact ⟨f, hN, hf, hpq, hTor⟩

theorem ggTwA5Three_frame
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {z : G} (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) (hp3 : p = 3)
    {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    GGResXDatum p Bs X ∧ (z ∈ X → GGResXDatumAx p Bs X z 5) ∧
      Nonempty (↥(ggAutomizer X Bs) ≃* Equiv.Perm (Fin 6)) := by
  have hTor' := ggTwA5Three_torDataAt hRig hLB hPJ hH hXz hp3 hΛ hl htag
  subst hp3
  obtain ⟨f, hN, hf, hpq, hTor⟩ := hTor'
  obtain ⟨hox, hoy⟩ := ggResHyp_orderOf_xy hH
  have hzc : z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hXz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl'
      exact Subgroup.mem_centralizer_singleton_iff.mp (hH.1.tableB_facts.2.2.2.1 hl')
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hH.2.2.2.2.1.1.2.2.2.1 hk)
  have hzo : orderOf z = 3 := by
    rcases hXz with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hox
    · exact hoy
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hAx := ggResXDatumAx_of_torData_twA5 hodd hpq hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2 hN
    hzc hzo hTor
  refine ⟨?_, fun _ => hAx, ?_⟩
  · obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf',
      hcl, -⟩ := hAx
    exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf', hcl⟩
  · obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, -, -, -, -, -, ⟨fe, -⟩, -, -⟩ := hAx
    obtain ⟨e5, -⟩ := ggCoxeterA_mulEquivPerm 5
    subst hM
    exact ⟨(fe.symm.trans ((CoxeterMatrix.A 5).reindexGroupEquiv e)).trans e5⟩

end CFSG.StandardType

end
