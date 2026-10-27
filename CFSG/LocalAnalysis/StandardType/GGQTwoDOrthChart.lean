module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Chart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameLow
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

private theorem pmoc_eq_of_ggLabelIso_orth {lab lab' : LargeEvenLabel} (hiso : GGLabelIso lab lab')
    (hD : lab'.tag = .D ∨ lab'.tag = .twD) (h4 : 4 ≤ lab'.rank) : lab = lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only [LargeEvenLabel.mk.injEq] at hD h4 ⊢
  rcases hD with hD | hD <;> subst hD <;>
    unfold GGLabelIso at hiso <;>
    rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

section Chart

section OrthL

theorem qtwoOrthFrameCore_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (hn : lab.n = 1) (htag : lab.tag = .D ∨ lab.tag = .twD) :
    ∃ Φ : OrthTorus.OrthFrameCore p Bs L, Nat.card Φ.F = 2 ∧ Φ.r = lab.rank ∧
      4 ≤ Φ.r ∧ Subgroup.center ↥L = ⊥ ∧ B < Bs := by
  classical
  have hroute : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := hcfg.1
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hroute
  haveI : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hroute.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hrank4 : 4 ≤ lab.rank := ggQTwoD_four_le_rank hRig hroute hΛ hhas hn htag
  have hbase := ggL_baseLabel_of_nonSplit hroute hcfg.2.2.2.1 hle3 hcfg.2.2.1
  have hmark : GGInnerDiagOnLabel
      (fun p lab' => (ggRowP_EOmP p lab' ∨ ggRowP_EOmM p lab') ∧ lab' = lab) p Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_ hbase
    intro lab' hΛ' hhas' hrow
    have hiso : GGLabelIso lab' lab := hRig lab' lab _ hΛ' hΛ hhas' hhas
    have heq : lab' = lab := pmoc_eq_of_ggLabelIso_orth hiso htag hrank4
    subst heq
    refine ⟨?_, rfl⟩
    rcases hrow with h | h | h | ⟨-, -, h | h | h | h⟩
    · exfalso
      rcases h.1 with ⟨ht, -⟩ | ⟨ht, hr3⟩
      · rw [ht] at htag
        exact absurd htag (by decide)
      · omega
    · exact Or.inr h
    · exfalso
      rw [h.1] at htag
      exact absurd htag (by decide)
    · exact Or.inl h
    · exfalso
      rw [h.1] at htag
      exact absurd htag (by decide)
    · exfalso
      rw [h.1] at htag
      exact absurd htag (by decide)
    · exfalso
      rw [h.1] at htag
      exact absurd htag (by decide)
  have hmarkF : GGInnerDiagOnLabel
      (fun p lab' => (ggRowP_EOmP p lab' ∨ ggRowP_EOmM p lab') ∧ lab'.n = 1) p Bs L :=
    hmark.mono_label fun lab' h => ⟨h.1, by simpa only [h.2] using hn⟩
  have hZ : Subgroup.center ↥L = ⊥ := hconf.center_eq_bot_of_orthTwo hRig hmarkF
  have hlt : B < Bs := hconf.lt_bstar_of_orthTwo hRig hmarkF
  have hact : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), ∃ b : ↥Bs, ggGamma L hN b ≠ 1 :=
    fun hN => ggGamma_L_exists_ne_one hconf hN
  obtain ⟨lab', hP, -, Φ, hr, hcard, -, -, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hBs hSC (fun _ hP => hP.1)
      hmark (fun _ _ _ => hZ) hact
  rcases hP with ⟨-, rfl⟩
  exact ⟨Φ, by rw [hcard, hn, pow_one], hr, by omega, hZ, hlt⟩

theorem qtwoDL1Chart_orth_L_on {R : ℕ → Prop} (hFrame : GGQTwoFrameInputOn R) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (m : ℕ)
    (e' : Fin m ≃ ι) (hRm : R m) (hm : 6 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hcell : qtwoOrthL G L 𝒦) :
    ∃ Φ : OrthTorus.OrthFrameCore p Bs L, Nat.card Φ.F = 2 ∧ 5 ≤ Φ.r ∧
      Subgroup.center ↥L = ⊥ := by
  classical
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
  obtain ⟨Φ, hF, hr, -, hZ, -⟩ := qtwoOrthFrameCore_of_cfg hcfg
    (qtwo_label_le_three e' hM) hΛ hhas hn htag
  have hrank1 : lab.rank + 1 = m :=
    (hFrame G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM lab hΛ hhas hn htag).1
  exact ⟨Φ, hF, by omega, hZ⟩

theorem qtwoDL1Chart_orth_L (hFrame : GGQTwoFrameInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (m : ℕ) (e' : Fin m ≃ ι) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hcell : qtwoOrthL G L 𝒦) :
    ∃ Φ : OrthTorus.OrthFrameCore p Bs L, Nat.card Φ.F = 2 ∧ 5 ≤ Φ.r ∧
      Subgroup.center ↥L = ⊥ :=
  qtwoDL1Chart_orth_L_on hFrame hcfg m e' hm (by omega) hM hcell

end OrthL

end Chart

end CFSG.StandardType.QTwo

end
