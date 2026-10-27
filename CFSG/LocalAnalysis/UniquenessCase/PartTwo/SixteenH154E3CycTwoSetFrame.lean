module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrameAG
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoSetFrame_exists
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) q)
    (hs2 : s15 D.M V₀ V hV L = 2) (hm : rk ↥(wTil V₀ V hV L) = n) :
    ∃ l ψ : MulAut (Vtil V₀ V hV), lBar V₀ V hV L = Subgroup.zpowers l ∧
      s16h_CycFrameG q n (Mbar D.M V₀ V hV) ψ l (wTil V₀ V hV L) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set W : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWdef
  set Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hLbdef
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMbdef
  have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hWsq : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (hsq (w : Vtil V₀ V hV))
  have hLbcard : Nat.card ↥Lb = q := by rw [hLbdef]; exact hLp.2
  haveI : IsCyclic ↥Lb := hLp.1
  letI : CommGroup ↥Lb := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Lb)
  set l : MulAut (Vtil V₀ V hV) := (g : MulAut (Vtil V₀ V hV)) with hldef
  have hlmem : l ∈ Lb := g.2
  have hLz : Lb = Subgroup.zpowers l := by
    have htop : Subgroup.zpowers g = ⊤ := (Subgroup.zpowers g).eq_top_iff'.mpr hg
    have hmap : (Subgroup.zpowers g).map Lb.subtype = Subgroup.zpowers l :=
      MonoidHom.map_zpowers Lb.subtype g
    rw [htop] at hmap
    rw [← hmap]
    exact le_antisymm (fun x hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)
      (Subgroup.map_subtype_le (⊤ : Subgroup ↥Lb))
  have hzord : orderOf l = q := by
    rw [← Nat.card_zpowers l, ← hLz, hLbcard]
  have hlMb : l ∈ Mb := by
    rw [hMbdef]
    exact barSub_mono V₀ V hV h.hyp151.le hlmem
  obtain ⟨t, htM, ht2, ht1, htr, hW'⟩ := hc
  have hconc : Conc4_136W Mb t Lb := hW'
  have hs2' : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} = 2 := hs2
  have hodd : Odd (Nat.card ↥Lb) := by
    rw [hLbcard]
    exact hq.odd_of_ne_two hq2
  have hZ : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb ⊓ fixV Lb = ⊥ :=
    s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  have hUW : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb = W := by
    rw [hWdef, hLbdef]
    rfl
  have hm' : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb) = n := by
    rw [hUW]
    exact hm
  have hcard : Nat.card ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb) = 2 ^ n := by
    have hpow := CFSG.Quasithin.card_eq_two_pow_rk
      (V := ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb))
      (fun v => Subtype.ext (hsq (v : Vtil V₀ V hV)))
    rw [hpow, hm']
  obtain ⟨ψ, F⟩ := s16h_e3_CycTwoFrameAG_frame (W := Vtil V₀ V hV) hsq hq.one_lt hlMb hzord
    hLz hconc hs2' hZ hcard
  exact ⟨l, ψ, hLz, F⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
