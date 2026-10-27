module

public import CFSG.Quasithin.Background.F3Amalgam

public section

namespace CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin.F7

universe u w w'

theorem pathFix_transfer {α : RankTwoAmalgam.{u}} {Y : Type w} {Y' : Type w'} [Group Y]
    [Group Y'] (c : α.Completion Y) (c' : α.Completion Y') (hc : c.IsFaithful)
    (hc' : c'.IsFaithful) (n : ℕ)
    (h' : ∀ p : GPath c'.graph n, p.NoBack → ∀ g : ↥(c'.φ1.range ⊔ c'.φ2.range),
      (∀ i, i ≤ n → g • p i = p i) → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1) :
    ∀ p : GPath c.graph n, p.NoBack → ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
      (∀ i, i ≤ n → g • p i = p i) → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
  intro p hp g hfix hord
  obtain ⟨uh, huh⟩ := (c.graphCovering hc).surj (p 0)
  have hp_nb : p ∈ GPath.nbPaths c.graph (c.Θ hc uh) n := ⟨huh.symm, hp⟩
  obtain ⟨ph, hph, hphmap⟩ := ((c.lemma_F33_1 hc uh).2.2.2 n).surjOn hp_nb
  obtain ⟨hph0, hphnb⟩ := hph
  have hmap : ph.stabPath.map (c.theta0 hc) = p.stabPath := by
    rw [(c.lemma_F33_3 hc uh ph hph0).1, hphmap]
  have hinj : Set.InjOn (c.theta0 hc)
      ((ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) :
        Set ↥(α.Ghat1 ⊔ α.Ghat2)) := (c.lemma_F33_3 hc uh ph hph0).2.1
  have hgmem : g ∈ (p.stabPath : Subgroup ↥(c.φ1.range ⊔ c.φ2.range)) :=
    GraphCovering.mem_stabPath.mpr hfix
  have hgmem' : g ∈ ph.stabPath.map (c.theta0 hc) := by
    rw [hmap]
    exact hgmem
  obtain ⟨gh, hgh, htheq⟩ := hgmem'
  let gh' : ↥(ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) := ⟨gh, hgh⟩
  have hinj_comp : Function.Injective
      ((c.theta0 hc).comp (ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).subtype) :=
    fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hordc : orderOf g = orderOf gh := by
    have h1 : orderOf (c.theta0 hc gh) = orderOf gh' :=
      orderOf_injective ((c.theta0 hc).comp
        (ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).subtype) hinj_comp gh'
    have h2 : orderOf gh' = orderOf gh := Subgroup.orderOf_mk gh hgh
    rw [htheq] at h1
    exact h1.trans h2
  let p' : GPath c'.graph n := (c'.graphCovering hc').pathMap ph
  have hp'nb : p'.NoBack := ((c'.graphCovering hc').noBack_pathMap_iff ph).mpr hphnb
  have hmap' : ph.stabPath.map (c'.theta0 hc') = p'.stabPath :=
    (c'.lemma_F33_3 hc' uh ph hph0).1
  have hinj' : Set.InjOn (c'.theta0 hc')
      ((ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) :
        Set ↥(α.Ghat1 ⊔ α.Ghat2)) := (c'.lemma_F33_3 hc' uh ph hph0).2.1
  have hg'mem : c'.theta0 hc' gh ∈
      (p'.stabPath : Subgroup ↥(c'.φ1.range ⊔ c'.φ2.range)) := by
    rw [← hmap']
    exact Subgroup.mem_map_of_mem _ hgh
  have hfix' : ∀ i, i ≤ n → c'.theta0 hc' gh • p' i = p' i :=
    GraphCovering.mem_stabPath.mp hg'mem
  have hinj'_comp : Function.Injective
      ((c'.theta0 hc').comp (ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).subtype) :=
    fun a b hab => Subtype.ext (hinj' a.2 b.2 hab)
  have hordc' : orderOf (c'.theta0 hc' gh) = orderOf gh := by
    have h1 : orderOf (c'.theta0 hc' gh) = orderOf gh' :=
      orderOf_injective ((c'.theta0 hc').comp
        (ph.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)).subtype) hinj'_comp gh'
    have h2 : orderOf gh' = orderOf gh := Subgroup.orderOf_mk gh hgh
    exact (h1.trans h2)
  have hord' : orderOf (c'.theta0 hc' gh) = orderOf g := hordc'.trans hordc.symm
  have hord'2 : ∃ k : ℕ, orderOf (c'.theta0 hc' gh) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, by rw [hord']; exact hk⟩
  have hg'1 : c'.theta0 hc' gh = 1 := h' p' hp'nb (c'.theta0 hc' gh) hfix' hord'2
  have hgh1 : gh = 1 :=
    hinj' hgh (Subgroup.one_mem _) (by rw [map_one]; exact hg'1)
  rw [← htheq, hgh1, map_one]

end CFSG.Quasithin.RankTwoAmalgam.Completion
