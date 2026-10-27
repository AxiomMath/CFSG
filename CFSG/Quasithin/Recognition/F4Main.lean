module

public import CFSG.Quasithin.Recognition.F4Thirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace LieSetting

variable (S : LieSetting.{u, w})

@[expose] def N1 : Subgroup ↥S.N := (stv S.ι S.ι.xv).subgroupOf S.N

@[expose] def N12 : Subgroup ↥S.N := (stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv).subgroupOf S.N

@[expose] def IsExtension (M : Type*) [Group M] : Prop :=
  ∃ ν : ↥S.N →* M, Function.Injective ν ∧ ν.range.Normal ∧
    Subgroup.centralizer (ν.range : Set M) = ⊥ ∧
    ∀ g : M, g ∈ Subgroup.normalizer ((S.N12.map ν : Subgroup M) : Set M) →
      g ∈ Subgroup.normalizer ((S.N1.map ν : Subgroup M) : Set M)

@[expose] def F48Concl {Y : Type w'} [Group Y] (β : S.α.Completion Y) : Prop :=
  (∃ (Ġ : Type w') (_ : Group Ġ) (β' : S.α.Completion Ġ), β'.IsFaithful ∧
      Amalgam.Completion.IsEquivalent β.toCompletion β'.toCompletion ∧ S.IsExtension Ġ) ∧
  (S.N = ⊤ → Amalgam.Completion.IsQuasiEquivalent β.toCompletion S.ι.toCompletion)

end LieSetting

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}

namespace TransComp

variable (T : TransComp c m)

include T

theorem large_far_vertex (hl : c.IsLarge m) (a : c.Γ) : ∃ v, m < c.graph.dist a v := by
  obtain ⟨P, hP⟩ := GPath.exists_nbPaths T.hval a m
  rcases T.alt hP with ⟨hv, -⟩ | ⟨-, hii⟩
  · exact hv
  · exfalso
    obtain ⟨y₁, y₂, h1, h2, hne⟩ := T.exists_two_nbrs (P m)
    obtain ⟨t₁, ⟨ht10, ht1m, ht1g, ht1y⟩, -⟩ := hii.1 y₁ h1
    obtain ⟨t₂, ⟨ht20, ht2m, ht2g, ht2y⟩, -⟩ := hii.1 y₂ h2
    have := hl t₁ t₂ ht1g ht2g (by rw [ht10, ht20]) (by rw [ht1m, ht2m])
    apply hne
    rw [← ht1y, ← ht2y, this]

end TransComp

end RankTwoAmalgam.Completion

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] [Finite Y]

theorem Facts45L.ptsCard_lt_of_large (hS : S.Facts45L) (β : S.α.Completion Y)
    (hβ : β.IsFaithful) (hl : β.IsLarge S.m) : S.ι.ptsCard < β.ptsCard := by
  have hm := S.hm
  have F := hS.facts46 β hβ
  have Fι := hS.facts46 S.ι S.hι
  have hq1 := hS.thick1
  have hidx : 3 ≤ S.α.α1.range.index := by
    unfold RankTwoAmalgam.qOne at hq1
    omega
  have hsph_lt : ∀ k, k < S.m →
      Nat.card ↥(CosetGeom.sphere k β.xv) = Nat.card ↥(CosetGeom.sphere k S.ι.xv) := by
    intro k hk
    rw [F.card_sphere_lt hk, Fι.card_sphere_lt hk]
    exact card_nbPaths_eq β S.ι hβ S.hι k
  have hpos : 0 < Nat.card ↥(CosetGeom.sphere S.m S.ι.xv) := by
    obtain ⟨P, hP⟩ := GPath.exists_nbPaths Fι.hval S.ι.xv S.m
    have hmem : P S.m ∈ CosetGeom.sphere S.m S.ι.xv := Fι.dist_m _ P hP
    exact Nat.card_pos_iff.mpr ⟨⟨⟨_, hmem⟩⟩, inferInstance⟩
  have hsphm : Nat.card ↥(CosetGeom.sphere S.m S.ι.xv) <
      Nat.card ↥(CosetGeom.sphere S.m β.xv) := by
    have e1 := F.card_nbPaths_m_large hl
    have e2 := Fι.card_nbPaths_m (fun a b hab => hS.allBij_iota hab)
    rw [nbrs_xv_card (c := S.ι) S.hι] at e2
    have e3 := card_nbPaths_eq β S.ι hβ S.hι S.m
    rw [e1, e2] at e3
    rw [e3]
    nlinarith
  have hιpts := Facts46.card_pts (c := S.ι) hS.poly.diam_le
  have hβle := Facts46.card_ptsLe (c := β) S.m
  have hβle' := Facts46.ptsLe_le (c := β) S.m
  by_cases hev : Even S.m
  · have hlt : (∑ k ∈ Finset.range (S.m + 1),
          if Even k then Nat.card ↥(CosetGeom.sphere k S.ι.xv) else 0) <
        ∑ k ∈ Finset.range (S.m + 1),
          if Even k then Nat.card ↥(CosetGeom.sphere k β.xv) else 0 := by
      refine Finset.sum_lt_sum (fun k hk => ?_) ⟨S.m, Finset.mem_range.mpr (by omega), ?_⟩
      · rcases Nat.lt_or_ge k S.m with h | h
        · rw [hsph_lt k h]
        · have hk' : k = S.m := le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h
          rw [hk']
          simp only [hev, ite_true]
          exact hsphm.le
      · simp only [hev, ite_true]
        exact hsphm
    omega
  · have heq : (∑ k ∈ Finset.range (S.m + 1),
          if Even k then Nat.card ↥(CosetGeom.sphere k β.xv) else 0) =
        ∑ k ∈ Finset.range (S.m + 1),
          if Even k then Nat.card ↥(CosetGeom.sphere k S.ι.xv) else 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rcases Nat.lt_or_ge k S.m with h | h
      · rw [hsph_lt k h]
      · have hk' : k = S.m := le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h
        subst hk'
        simp only [hev, ite_false]
    have T := hS.transComp
    have Tβ : β.TransComp S.m :=
      ⟨hβ, hS.thick1, hS.thick2, pathTrans_transfer β hβ S.ι S.hι (S.m + 1) hS.trans, by omega⟩
    obtain ⟨w, hw⟩ := Tβ.large_far_vertex hl β.xv
    have hex : ∃ v : β.Γ, CosetGeom.vtype v = false ∧ S.m < β.graph.dist β.xv v := by
      obtain ⟨P, hP0, hPw, -⟩ := GPath.exists_geodesic (connected_graph β) β.xv w
      have hgeo : β.graph.dist (P 0) (P (β.graph.dist β.xv w)) = β.graph.dist β.xv w := by
        rw [hP0, hPw]
      have hz : β.graph.dist β.xv (P (S.m + 1)) = S.m + 1 := by
        have := GPath.dist_prefix (connected_graph β) P hgeo
          (show S.m + 1 ≤ β.graph.dist β.xv w by omega)
        rwa [hP0] at this
      refine ⟨P (S.m + 1), ?_, by rw [hz]; omega⟩
      have hpar := GPath.dist_even_iff (connected_graph β)
        (fun _ _ h => CosetGeom.vtype_ne_of_adj h) β.xv (P (S.m + 1))
      have hev' : Even (β.graph.dist β.xv (P (S.m + 1))) := by
        rw [hz]
        exact (Nat.not_even_iff_odd.mp hev).add_one
      have := hpar.mpr hev'
      exact this.symm
    have hlt := Facts46.ptsLe_lt (c := β) S.m hex
    omega

theorem card_G1_pos {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y]
    (c : α.Completion Y) (hc : c.IsFaithful) : 0 < Nat.card α.G1 := by
  have : Finite α.G1 := Finite.of_injective c.φ1 hc.1
  exact Nat.card_pos

theorem Facts45L.small_of_card_le (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hle : Nat.card Y ≤ Nat.card S.Yb) : β.IsSmall S.m := by
  by_contra h
  have hl : β.IsLarge S.m := not_not.mp h
  have hlt := hS.ptsCard_lt_of_large β hβ hl
  have e1 := card_Y_eq β hβ
  have e2 := card_Y_eq S.ι S.hι
  have hp := card_G1_pos β hβ
  have : S.ι.ptsCard * Nat.card S.α.G1 < β.ptsCard * Nat.card S.α.G1 :=
    Nat.mul_lt_mul_of_pos_right hlt hp
  omega

theorem Facts45L.lemma_F424 (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hle : Nat.card Y ≤ Nat.card S.Yb) (h48 : β.IsSmall S.m → S.F48Concl β) :
    Nat.card Y = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ) := by
  have hs := hS.small_of_card_le β hβ hle
  refine ⟨hS.lemma_F413_2 β hβ hs, ?_⟩
  obtain ⟨⟨Ġ, hG, β', -, ⟨φ, -⟩, hext⟩, -⟩ := h48 hs
  exact ⟨Ġ, hG, hext, ⟨φ⟩⟩

end LieSetting

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}

theorem Facts46.ptsCard_lt_of_large_even {Y' : Type w} [Group Y'] [Finite Y']
    {d : α.Completion Y'} (F : Facts46 c m) (Fd : Facts46 d m) (hev : Even m)
    (hl : c.IsLarge m) (hsd : d.IsSmall m) : d.ptsCard < c.ptsCard := by
  have hm := F.hm
  have hq1 := F.thick1
  have hidx : 3 ≤ α.α1.range.index := by
    unfold RankTwoAmalgam.qOne at hq1
    omega
  have hsph_lt : ∀ k, k < m →
      Nat.card ↥(CosetGeom.sphere k c.xv) = Nat.card ↥(CosetGeom.sphere k d.xv) := by
    intro k hk
    rw [F.card_sphere_lt hk, Fd.card_sphere_lt hk]
    exact card_nbPaths_eq c d F.faithful Fd.faithful k
  have hpos : 0 < Nat.card ↥(CosetGeom.sphere m d.xv) := by
    obtain ⟨P, hP⟩ := GPath.exists_nbPaths Fd.hval d.xv m
    have hmem : P m ∈ CosetGeom.sphere m d.xv := Fd.dist_m _ P hP
    exact Nat.card_pos_iff.mpr ⟨⟨⟨_, hmem⟩⟩, inferInstance⟩
  have hsphm : Nat.card ↥(CosetGeom.sphere m d.xv) < Nat.card ↥(CosetGeom.sphere m c.xv) := by
    have e1 := F.card_nbPaths_m_large hl
    have e2 := Fd.card_nbPaths_m (fun a b hab => Fd.allBij hsd hab)
    rw [nbrs_xv_card (c := d) Fd.faithful] at e2
    have e3 := card_nbPaths_eq c d F.faithful Fd.faithful m
    rw [e1, e2] at e3
    rw [e3]
    nlinarith
  have hdpts := Facts46.card_pts (c := d) (Fd.diam_le hsd)
  have hcle := Facts46.card_ptsLe (c := c) m
  have hcle' := Facts46.ptsLe_le (c := c) m
  have hlt : (∑ k ∈ Finset.range (m + 1),
        if Even k then Nat.card ↥(CosetGeom.sphere k d.xv) else 0) <
      ∑ k ∈ Finset.range (m + 1),
        if Even k then Nat.card ↥(CosetGeom.sphere k c.xv) else 0 := by
    refine Finset.sum_lt_sum (fun k hk => ?_) ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
    · rcases Nat.lt_or_ge k m with h | h
      · rw [hsph_lt k h]
      · have hk' : k = m := le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h
        rw [hk']
        simp only [hev, ite_true]
        exact hsphm.le
    · simp only [hev, ite_true]
      exact hsphm
  omega

end RankTwoAmalgam.Completion

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] [Finite Y]

theorem lemma_F424_even (hev : Even S.m) (hpoly : IsGenPolygon S.ι.graph S.m)
    (Fι : S.ι.Facts46 S.m) (β : S.α.Completion Y) (Fβ : β.Facts46 S.m)
    (hle : Nat.card Y ≤ Nat.card S.Yb) (h48 : β.IsSmall S.m → S.F48Concl β) :
    Nat.card Y = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ) := by
  have hsι : S.ι.IsSmall S.m := by
    obtain ⟨T, hT⟩ := hpoly.polygon
    exact Fι.isSmall_of_polygon hT
  have hs : β.IsSmall S.m := by
    by_contra h
    have hl : β.IsLarge S.m := not_not.mp h
    have hlt := Facts46.ptsCard_lt_of_large_even Fβ Fι hev hl hsι
    have e1 := card_Y_eq β Fβ.faithful
    have e2 := card_Y_eq S.ι Fι.faithful
    have hp := card_G1_pos β Fβ.faithful
    have : S.ι.ptsCard * Nat.card S.α.G1 < β.ptsCard * Nat.card S.α.G1 :=
      Nat.mul_lt_mul_of_pos_right hlt hp
    omega
  refine ⟨card_Y_eq_of_small Fβ Fι hs hsι, ?_⟩
  obtain ⟨⟨Ġ, hG, β', -, ⟨φ, -⟩, hext⟩, -⟩ := h48 hs
  exact ⟨Ġ, hG, hext, ⟨φ⟩⟩

end LieSetting

end CFSG.Quasithin
