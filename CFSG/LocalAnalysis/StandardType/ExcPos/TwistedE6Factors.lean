module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
import CFSG.LieType.Chevalley.RootComponentType
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootComb
import CFSG.LocalAnalysis.StandardType.GGJ4dRankTwoBound
import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcHighThree
open CFSG.HardMathSupport.Timmesfeld.LangTorus (compRank)

variable {τ : Tag}

theorem compRank_empty : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by
  simp [compRank]

theorem compRank_mono {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (h : Ψ ⊆ Ψ') : compRank Ψ ≤ compRank Ψ' :=
  Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))

theorem twelve_le_numRoots_of_three_le_rank {t : TauCeti.DynkinType} (ht : t.Valid)
    (hsl : t.IsSimplyLaced) (h3 : 3 ≤ t.rank) : 12 ≤ t.numRoots := by
  cases t with
  | A n =>
    rw [TauCeti.DynkinType.rank_A] at h3
    rw [TauCeti.DynkinType.numRoots_A]
    exact le_trans (by norm_num) (Nat.mul_le_mul h3 (by omega : 4 ≤ n + 1))
  | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
    rw [TauCeti.DynkinType.rank_D] at h3
    have h4 := TauCeti.DynkinType.valid_D.1 ht
    rw [TauCeti.DynkinType.numRoots_D]
    exact le_trans (by norm_num : 12 ≤ 8 * 3)
      (Nat.mul_le_mul (by omega : 8 ≤ 2 * n) (by omega : 3 ≤ n - 1))
  | E6 =>
    rw [TauCeti.DynkinType.rank_E6] at h3
    rw [TauCeti.DynkinType.numRoots_E6]
    norm_num
  | E7 =>
    rw [TauCeti.DynkinType.rank_E7] at h3
    rw [TauCeti.DynkinType.numRoots_E7]
    norm_num
  | E8 =>
    rw [TauCeti.DynkinType.rank_E8] at h3
    rw [TauCeti.DynkinType.numRoots_E8]
    norm_num
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2


theorem exists_dynkinType_compRank (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h0 : 0 < compRank Ψ) :
    ∃ (t : TauCeti.DynkinType), t.Valid ∧ t.IsSimplyLaced ∧ compRank Ψ = t.rank ∧
      Ψ.ncard = t.numRoots := by
  have hne : Ψ.Nonempty := by
    rcases Set.eq_empty_or_nonempty Ψ with h | h
    · rw [h, compRank_empty] at h0
      omega
    · exact h
  obtain ⟨t, e, ht, hsl, -, hcard, hN⟩ := exists_dynkinType hτ hΨ hne
  exact ⟨t, ht, hsl,
    by rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, hcard], hN⟩

theorem compRank_ncard_ade (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) :
    compRank Ψ = 1 ∨ (2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1)) ∨
      (4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) ∨
      (compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 7 ∧ Ψ.ncard = 126) ∨
      (compRank Ψ = 8 ∧ Ψ.ncard = 240) := by
  obtain ⟨t, -, ht, hsl, -, hcard, hN⟩ := exists_dynkinType hτ hΨ hne
  rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, hcard, hN]
  cases t with
  | A n =>
    rw [TauCeti.DynkinType.rank_A, TauCeti.DynkinType.numRoots_A]
    rcases (TauCeti.DynkinType.valid_A.1 ht).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
    rw [TauCeti.DynkinType.rank_D, TauCeti.DynkinType.numRoots_D]
    exact Or.inr (Or.inr (Or.inl ⟨TauCeti.DynkinType.valid_D.1 ht, rfl⟩))
  | E6 =>
    rw [TauCeti.DynkinType.rank_E6, TauCeti.DynkinType.numRoots_E6]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  | E7 =>
    rw [TauCeti.DynkinType.rank_E7, TauCeti.DynkinType.numRoots_E7]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  | E8 =>
    rw [TauCeti.DynkinType.rank_E8, TauCeti.DynkinType.numRoots_E8]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

theorem exists_A3_simpleRoots (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h3 : 3 ≤ compRank Ψ) :
    ∃ β ∈ simpleRoots Ψ, ∃ γ ∈ simpleRoots Ψ, ∃ δ ∈ simpleRoots Ψ,
      iform β γ = -1 ∧ iform γ δ = -1 ∧ iform β δ = 0 := by
  classical
  have hne : Ψ.Nonempty := by
    rcases Set.eq_empty_or_nonempty Ψ with h | h
    · rw [h, compRank_empty] at h3
      omega
    · exact h
  have hcard3 : 3 ≤ (simpleRoots Ψ).card := by
    rw [← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ]
    exact h3
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.1 (by omega : 2 < (simpleRoots Ψ).card)
  set G : SimpleGraph (simpleRoots Ψ) :=
    TauCeti.diagramGraph (Matrix.of fun x y : simpleRoots Ψ =>
      corootPair (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)) with hG
  have hconn : G.Connected := by
    simpa only [hG] using
      CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hne
  have key : ∃ x y z : simpleRoots Ψ, G.Adj x y ∧ G.Adj y z ∧ x ≠ z := by
    rcases lt_or_ge 1 (G.dist ⟨a, ha⟩ ⟨b, hb⟩) with hd | hd
    · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨x, y, z, hxy, hyz, -, hxz⟩ :=
        SimpleGraph.Walk.exists_adj_adj_not_adj_ne (p := p) hp hd
      exact ⟨x, y, z, hxy, hyz, hxz⟩
    · have hd0 : G.dist ⟨a, ha⟩ ⟨b, hb⟩ ≠ 0 := by
        rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
        exact ⟨fun h => hab (congrArg Subtype.val h), hconn _ _⟩
      have hd1 : G.dist ⟨a, ha⟩ ⟨b, hb⟩ = 1 := by omega
      have hab_adj : G.Adj ⟨a, ha⟩ ⟨b, hb⟩ := SimpleGraph.dist_eq_one_iff_adj.1 hd1
      rcases lt_or_ge 1 (G.dist ⟨a, ha⟩ ⟨c, hc⟩) with hd2 | hd2
      · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist ⟨a, ha⟩ ⟨c, hc⟩
        obtain ⟨x, y, z, hxy, hyz, -, hxz⟩ :=
          SimpleGraph.Walk.exists_adj_adj_not_adj_ne (p := p) hp hd2
        exact ⟨x, y, z, hxy, hyz, hxz⟩
      · have hd0' : G.dist ⟨a, ha⟩ ⟨c, hc⟩ ≠ 0 := by
          rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
          exact ⟨fun h => hac (congrArg Subtype.val h), hconn _ _⟩
        have hd1' : G.dist ⟨a, ha⟩ ⟨c, hc⟩ = 1 := by omega
        have hac_adj : G.Adj ⟨a, ha⟩ ⟨c, hc⟩ := SimpleGraph.dist_eq_one_iff_adj.1 hd1'
        exact ⟨⟨b, hb⟩, ⟨a, ha⟩, ⟨c, hc⟩, hab_adj.symm, hac_adj,
          fun h => hbc (congrArg Subtype.val h)⟩
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := key
  have hneg : ∀ {u v : simpleRoots Ψ},
      G.Adj u v → iform (u : Fin τ.rank → ℤ) v = -1 := by
    intro u v huv
    rw [hG] at huv
    obtain ⟨hne', hne0, -⟩ := TauCeti.diagramGraph_adj.1 huv
    simp only [Matrix.of_apply] at hne0
    have h0 : iform (u : Fin τ.rank → ℤ) v ≠ 0 :=
      (CFSG.HardMathSupport.Timmesfeld.Proving.corootPair_ne_zero_iff u.2).1 hne0
    rcases iform_simpleRoots_eq_zero_or_eq_neg_one hτ hΨ u.2 v.2
      (fun h => hne' (Subtype.ext h)) with h | h
    · exact absurd h h0
    · exact h
  have hxy' : iform (x : Fin τ.rank → ℤ) y = -1 := hneg hxy
  have hyz' : iform (y : Fin τ.rank → ℤ) z = -1 := hneg hyz
  refine ⟨x, x.2, y, y.2, z, z.2, hxy', hyz', ?_⟩
  rcases iform_simpleRoots_eq_zero_or_eq_neg_one hτ hΨ x.2 z.2
    (fun h => hxz (Subtype.ext h)) with h | h
  · exact h
  · exfalso
    have hxz' : iform (x : Fin τ.rank → ℤ) z = -1 := h
    have hyx' : iform (y : Fin τ.rank → ℤ) x = -1 := by rw [iform_comm]; exact hxy'
    have hzy' : iform (z : Fin τ.rank → ℤ) y = -1 := by rw [iform_comm]; exact hyz'
    have hzx' : iform (z : Fin τ.rank → ℤ) x = -1 := by rw [iform_comm]; exact hxz'
    have hxx' : iform (x : Fin τ.rank → ℤ) x = 2 := kr_iform_self hτ (simpleRoots_isRoot x.2)
    have hyy' : iform (y : Fin τ.rank → ℤ) y = 2 := kr_iform_self hτ (simpleRoots_isRoot y.2)
    have hzz' : iform (z : Fin τ.rank → ℤ) z = 2 := kr_iform_self hτ (simpleRoots_isRoot z.2)
    have hsum :
        (x : Fin τ.rank → ℤ) + (y : Fin τ.rank → ℤ) + (z : Fin τ.rank → ℤ) ≠ 0 := by
      intro h0
      have h1 := simpleRoots_height_pos x.2
      have h2 := simpleRoots_height_pos y.2
      have h3' := simpleRoots_height_pos z.2
      have e1 := height_add (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)
      have e2 := height_add ((x : Fin τ.rank → ℤ) + (y : Fin τ.rank → ℤ))
        (z : Fin τ.rank → ℤ)
      rw [h0] at e2
      have h00 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
      rw [h00, e1] at e2
      omega
    have hpos := iform_self_pos hsum
    have hexp :
        iform ((x : Fin τ.rank → ℤ) + (y : Fin τ.rank → ℤ) + (z : Fin τ.rank → ℤ))
          ((x : Fin τ.rank → ℤ) + (y : Fin τ.rank → ℤ) + (z : Fin τ.rank → ℤ)) = 0 := by
      simp only [iform_add_left, iform_add_right, hxx', hyy', hzz', hxy', hyx', hxz', hzx',
        hyz', hzy']
      norm_num
    rw [hexp] at hpos
    exact lt_irrefl 0 hpos

theorem twelve_le_ncard_of_three_le_compRank (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h3 : 3 ≤ compRank Ψ) :
    12 ≤ Ψ.ncard := by
  obtain ⟨t, ht, hsl, hrank, hN⟩ := exists_dynkinType_compRank hτ hΨ (by omega)
  rw [hN]
  exact twelve_le_numRoots_of_three_le_rank ht hsl (by omega)

theorem ncard_le_six_of_compRank_lt_three (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h3 : compRank Ψ < 3) : Ψ.ncard ≤ 6 := by
  rcases Set.eq_empty_or_nonempty Ψ with rfl | ⟨α, hα⟩
  · simp
  · exact LangRat.j4d_closed_ncard_le_six_of_compRank_le_two hτ hΨ.isRoot hΨ.neg_mem hΨ.add_mem
      hΨ.reflection_mem ((finite_setOf_isRoot τ).subset fun x hx => hΨ.isRoot x hx) hα (by omega)

theorem three_le_compRank_of_ssubset (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hΨ' : IsRootComponent Ψ')
    (h2 : 2 ≤ compRank Ψ) (hss : Ψ ⊂ Ψ') : 3 ≤ compRank Ψ' := by
  obtain h2 | h3 := h2.eq_or_lt
  swap
  · exact h3.trans_le (compRank_mono hss.subset)
  have h6 : Ψ.ncard = 6 := LangRat.j4d_rank_two_ncard hτ hΨ h2.symm
  have hlt : Ψ.ncard < Ψ'.ncard :=
    Set.ncard_lt_ncard hss ((finite_setOf_isRoot τ).subset fun x hx => hΨ'.isRoot x hx)
  by_contra hlt3
  have h6' : Ψ'.ncard ≤ 6 := ncard_le_six_of_compRank_lt_three hτ hΨ' (by omega)
  omega

theorem compRank_lt_three_of_orthogonal_E6 (hτ : τ = .E6) {Ψ₁ Ψ₂ : Set (Fin τ.rank → ℤ)}
    (h₁ : IsRootComponent Ψ₁) (h₂ : IsRootComponent Ψ₂)
    (horth : ∀ α ∈ Ψ₁, ∀ β ∈ Ψ₂, iform α β = 0) (hr₁ : 3 ≤ compRank Ψ₁) :
    compRank Ψ₂ < 3 := by
  subst hτ
  by_contra hcon
  push Not at hcon
  have hτE : (Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8) :=
    Or.inr (Or.inl rfl)
  obtain ⟨β₁, hβ₁, γ₁, hγ₁, δ₁, hδ₁, hβγ₁, hγδ₁, hβδ₁⟩ :=
    exists_A3_simpleRoots hτE h₁ hr₁
  obtain ⟨β₂, hβ₂, γ₂, hγ₂, δ₂, hδ₂, hβγ₂, hγδ₂, hβδ₂⟩ :=
    exists_A3_simpleRoots hτE h₂ hcon
  refine CFSG.StandardType.TableCRes.e6_gram_false
    (kr_iform_self hτE (simpleRoots_isRoot hβ₁)) (kr_iform_self hτE (simpleRoots_isRoot hγ₁))
    (kr_iform_self hτE (simpleRoots_isRoot hδ₁)) (kr_iform_self hτE (simpleRoots_isRoot hβ₂))
    (kr_iform_self hτE (simpleRoots_isRoot hγ₂)) (kr_iform_self hτE (simpleRoots_isRoot hδ₂))
    (by rw [hβγ₂, hβγ₁]) (by rw [hβδ₂, hβδ₁]) (by rw [hγδ₂, hγδ₁])
    (horth β₁ (simpleRoots_subset hβ₁) β₂ (simpleRoots_subset hβ₂))
    (horth β₁ (simpleRoots_subset hβ₁) γ₂ (simpleRoots_subset hγ₂))
    (horth β₁ (simpleRoots_subset hβ₁) δ₂ (simpleRoots_subset hδ₂))
    (horth γ₁ (simpleRoots_subset hγ₁) β₂ (simpleRoots_subset hβ₂))
    (horth γ₁ (simpleRoots_subset hγ₁) γ₂ (simpleRoots_subset hγ₂))
    (horth γ₁ (simpleRoots_subset hγ₁) δ₂ (simpleRoots_subset hδ₂))
    (horth δ₁ (simpleRoots_subset hδ₁) β₂ (simpleRoots_subset hβ₂))
    (horth δ₁ (simpleRoots_subset hδ₁) γ₂ (simpleRoots_subset hγ₂))
    (horth δ₁ (simpleRoots_subset hδ₁) δ₂ (simpleRoots_subset hδ₂))
    (by
      simp only [CFSG.StandardType.TableCRes.gramDet3, hβγ₁, hβδ₁, hγδ₁]
      norm_num)

theorem compRank_componentRoots_lt_three_E6 (hτ : τ = .E6) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {i j : KernelComponent χ} (hij : i ≠ j)
    (hi : 3 ≤ compRank (componentRoots χ i)) : compRank (componentRoots χ j) < 3 := by
  subst hτ
  refine compRank_lt_three_of_orthogonal_E6 rfl (isRootComponent_componentRoots i)
    (isRootComponent_componentRoots j) ?_ hi
  intro α hα β hβ
  obtain ⟨hαk, hαi⟩ := hα
  obtain ⟨hβk, hβj⟩ := hβ
  refine iform_eq_zero_of_mk_ne (α := ⟨α, hαk⟩) (β := ⟨β, hβk⟩) ?_
  intro h
  exact hij (hαi.symm.trans (h.trans hβj))

theorem twE6_twoOrbit_is_A2_pair (hτ : τ = .E6) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {i j : KernelComponent χ} (hij : i ≠ j)
    (hi : 2 ≤ compRank (componentRoots χ i))
    (hcard : (componentRoots χ i).ncard = (componentRoots χ j).ncard) :
    compRank (componentRoots χ i) = 2 ∧ (componentRoots χ i).ncard = 6 ∧
      compRank (componentRoots χ j) = 2 ∧ (componentRoots χ j).ncard = 6 := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr (Or.inl hτ)
  have h2i : compRank (componentRoots χ i) = 2 := by
    by_contra h
    have h3 : 3 ≤ compRank (componentRoots χ i) := by omega
    have hj3 : compRank (componentRoots χ j) < 3 :=
      compRank_componentRoots_lt_three_E6 hτ χ hij h3
    have h12 : 12 ≤ (componentRoots χ i).ncard :=
      twelve_le_ncard_of_three_le_compRank hτ' (isRootComponent_componentRoots i) h3
    have h6 : (componentRoots χ j).ncard ≤ 6 :=
      ncard_le_six_of_compRank_lt_three hτ' (isRootComponent_componentRoots j) hj3
    omega
  have h6i : (componentRoots χ i).ncard = 6 :=
    LangRat.j4d_rank_two_ncard hτ' (isRootComponent_componentRoots i) h2i
  have h6j : (componentRoots χ j).ncard = 6 := by
    rw [← hcard]
    exact h6i
  exact ⟨h2i, h6i,
    LangRat.compRank_eq_two_of_ncard_eq_six (isRootComponent_componentRoots j) h6j, h6j⟩

theorem twE6_strictNeighbour_orbit_one (hτ : τ = .E6) {M M' : Type*} [CommGroup M]
    [CommGroup M'] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (χ' : Multiplicative (Fin τ.rank → ℤ) →* M') {i j : KernelComponent χ}
    {i' j' : KernelComponent χ'} (hij' : i' ≠ j') (hi : compRank (componentRoots χ i) = 2)
    (hj : compRank (componentRoots χ j) = 2) (hii' : componentRoots χ i ⊆ componentRoots χ' i')
    (hjj' : componentRoots χ j ⊆ componentRoots χ' j') :
    componentRoots χ i = componentRoots χ' i' ∨ componentRoots χ j = componentRoots χ' j' := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr (Or.inl hτ)
  by_contra hcon
  push Not at hcon
  obtain ⟨hnei, hnej⟩ := hcon
  have h3i : 3 ≤ compRank (componentRoots χ' i') :=
    three_le_compRank_of_ssubset hτ' (isRootComponent_componentRoots i)
      (isRootComponent_componentRoots i') hi.ge (hii'.ssubset_of_ne hnei)
  have h3j : 3 ≤ compRank (componentRoots χ' j') :=
    three_le_compRank_of_ssubset hτ' (isRootComponent_componentRoots j)
      (isRootComponent_componentRoots j') hj.ge (hjj'.ssubset_of_ne hnej)
  exact absurd (compRank_componentRoots_lt_three_E6 hτ χ' hij' h3i) (by omega)

end CFSG.StandardType.LieKnownR2.ExcPos
