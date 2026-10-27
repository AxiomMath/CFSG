module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank ExcFrames

@[expose] def GGExcF4SplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .F4 ∧ p ∣ 2 ^ f - 1

@[expose] def GGExcE7SplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E7 ∧ p ∣ 2 ^ f - 1

@[expose] def GGExcE8SplitLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ p ∣ 2 ^ f - 1

section Tags


theorem ggSixBstarExcFrameOn_F4Split :
    GGSixBstarExcFrameOn .F4 GGExcF4SplitLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_F4 hf hK hp2 hpK ψ hinj hBsR hBs h4
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  exact h

theorem ggSixBstarExcFrameOn_E8Split : GGSixBstarExcFrameOn .E8 GGExcE8SplitLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  have hBs : IsElemAbelian p Bs := hctx.2.1.2.1
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have h8 := rank_le_twoLocalRank (τ := .E8) (by decide) hp hpK
    (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)) ψ hinj
  have hr : p ^ Tag.E8.rank ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right hp.pos h8).trans (by rw [← hBc]; exact Subgroup.card_le_of_le hctx.2.1.1)
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_E7E8 (Or.inr rfl) hf hK hp2 hpK ψ hinj hBsR hBs hr
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  exact h

theorem ggSixBstarExcFrameOn_E7Split :
    GGSixBstarExcFrameOn .E7 GGExcE7SplitLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  set e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  set χ : adjointGroup .E7 (GaloisField 2 f) →* G := ψ.comp e.symm.toMonoidHom with hχ
  have hχinj : Function.Injective χ := hinj.comp e.symm.injective
  have hχr : ∀ b, b ∈ χ.range ↔ b ∈ ψ.range := fun b =>
    ⟨fun ⟨u, hu⟩ => ⟨e.symm u, hu⟩, fun ⟨u, hu⟩ => ⟨e u, by
      have h1 : e.symm (e u) = u := e.symm_apply_apply u
      show ψ (e.symm (e u)) = b
      rw [h1]
      exact hu⟩⟩
  have hBsR' : Bs ≤ χ.range := fun b hb => (hχr b).mpr (hBsR hb)
  have hBs : IsElemAbelian p Bs := hctx.2.1.2.1
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have h7 := rank_le_twoLocalRank (τ := .E7) (by decide) hp hpK
    (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))) χ hχinj
  have hr : p ^ Tag.E7.rank ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right hp.pos h7).trans (by rw [← hBc]; exact Subgroup.card_le_of_le hctx.2.1.1)
  obtain ⟨ι, hι, hιr, hact⟩ :=
    exists_weylFrame_E7E8 (Or.inl rfl) hf hK hp2 hpK χ hχinj hBsR' hBs hr
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  have hset : (χ.range : Set G) = (ψ.range : Set G) := Set.ext hχr
  rw [hset]
  exact h

end Tags

end CFSG.StandardType
