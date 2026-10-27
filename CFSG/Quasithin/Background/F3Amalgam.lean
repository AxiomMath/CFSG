module

public import CFSG.Quasithin.Background.F3Coset
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7

universe u w

namespace RankTwoAmalgam

variable (α : RankTwoAmalgam.{u})

abbrev Ghat : Type u := Amalgam.gp α.toAmalgam

@[expose] def Ghat1 : Subgroup α.Ghat := (Amalgam.ξ α.toAmalgam RankTwoIndex.one).range

@[expose] def Ghat2 : Subgroup α.Ghat := (Amalgam.ξ α.toAmalgam RankTwoIndex.two).range

theorem Ghat1_sup_Ghat2 : α.Ghat1 ⊔ α.Ghat2 = ⊤ := by
  rw [eq_top_iff, ← Amalgam.iSup_range_ξ (α := α.toAmalgam)]
  refine iSup_le fun d => ?_
  cases d
  · exact le_sup_left
  · exact le_sup_right
  · rintro _ ⟨x, rfl⟩
    have : Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo x =
        Amalgam.ξ α.toAmalgam RankTwoIndex.one (α.α1 x) :=
      (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one)
        trivial x).symm
    rw [this]
    exact Subgroup.mem_sup_left ⟨_, rfl⟩

abbrev Γhat : Type u := CosetGeom (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2

abbrev graphHat : SimpleGraph α.Γhat := CosetGeom.graph (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2

namespace Completion

variable {α} {Y : Type w} [Group Y] (c : α.Completion Y)

@[expose] noncomputable def theta : α.Ghat →* Y := c.toCompletion.hat

theorem theta_ξ1 (g : α.G1) : c.theta (Amalgam.ξ α.toAmalgam RankTwoIndex.one g) = c.φ1 g :=
  Amalgam.Completion.hat_ξ c.toCompletion RankTwoIndex.one g

theorem theta_ξ2 (g : α.G2) : c.theta (Amalgam.ξ α.toAmalgam RankTwoIndex.two g) = c.φ2 g :=
  Amalgam.Completion.hat_ξ c.toCompletion RankTwoIndex.two g

theorem theta_ξ12 (g : α.G12) : c.theta (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g) = c.φ12 g :=
  Amalgam.Completion.hat_ξ c.toCompletion RankTwoIndex.onetwo g

theorem coverData (hc : c.IsFaithful) :
    CosetGeom.CoverData c.theta α.Ghat1 α.Ghat2 c.φ1.range c.φ2.range where
  inj₁ x hx h := by
    obtain ⟨g, rfl⟩ := hx
    have h' : c.φ1 g = 1 := (theta_ξ1 c g).symm.trans h
    have hg : g = 1 := hc.1 (h'.trans (map_one c.φ1).symm)
    rw [hg, map_one]
  inj₂ x hx h := by
    obtain ⟨g, rfl⟩ := hx
    have h' : c.φ2 g = 1 := (theta_ξ2 c g).symm.trans h
    have hg : g = 1 := hc.2.2 (h'.trans (map_one c.φ2).symm)
    rw [hg, map_one]
  map₁ := by
    unfold Ghat1
    rw [← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (MonoidHom.ext (theta_ξ1 c))
  map₂ := by
    unfold Ghat2
    rw [← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (MonoidHom.ext (theta_ξ2 c))
  inter := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩, rfl⟩
      exact ⟨⟨a, (theta_ξ1 c a).symm⟩, ⟨b, by rw [← hb]; exact (theta_ξ2 c b).symm⟩⟩
    · intro y hy
      have hy' : y ∈ c.φ12.range := by rw [← c.inter]; exact hy
      obtain ⟨g, rfl⟩ := hy'
      refine ⟨Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g, ⟨?_, ?_⟩, theta_ξ12 c g⟩
      · have : Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g =
            Amalgam.ξ α.toAmalgam RankTwoIndex.one (α.α1 g) :=
          (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one)
            trivial g).symm
        exact ⟨α.α1 g, this.symm⟩
      · have : Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g =
            Amalgam.ξ α.toAmalgam RankTwoIndex.two (α.α2 g) :=
          (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.two)
            trivial g).symm
        exact ⟨α.α2 g, this.symm⟩

abbrev Γ : Type w := CosetGeom (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range

abbrev graph : SimpleGraph c.Γ :=
  CosetGeom.graph (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range

@[expose] noncomputable def Θ (hc : c.IsFaithful) : α.Γhat → c.Γ := (c.coverData hc).Θ

theorem graphCovering (hc : c.IsFaithful) : GraphCovering α.graphHat c.graph (c.Θ hc) :=
  (c.coverData hc).graphCovering

theorem stabIso (hc : c.IsFaithful) (uh : α.Γhat) :
    GraphCovering.StabIso (θ := c.Θ hc) (θG := (c.coverData hc).hom0) uh :=
  (c.coverData hc).stabIso uh

@[expose] noncomputable def theta0 (hc : c.IsFaithful) :
    ↥(α.Ghat1 ⊔ α.Ghat2) →* ↥(c.φ1.range ⊔ c.φ2.range) := (c.coverData hc).hom0

@[simp] theorem coe_theta0 (hc : c.IsFaithful) (g : ↥(α.Ghat1 ⊔ α.Ghat2)) :
    ((c.theta0 hc g : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) = c.theta (g : α.Ghat) := rfl

theorem Θ_smul (hc : c.IsFaithful) (g : ↥(α.Ghat1 ⊔ α.Ghat2)) (v : α.Γhat) :
    c.Θ hc (g • v) = c.theta0 hc g • c.Θ hc v :=
  (c.coverData hc).Θ_smul g v

theorem lemma_F33_1 (hc : c.IsFaithful) (uh : α.Γhat) :
    Function.Bijective ((c.graphCovering hc).pathSetMap uh) ∧
      (∀ n, Set.BijOn (c.graphCovering hc).pathMap (GPath.paths α.graphHat uh n)
        (GPath.paths c.graph (c.Θ hc uh) n)) ∧
      Set.BijOn ((c.graphCovering hc).pathSetMap uh) {p | p.NoBack} {p | p.NoBack} ∧
      (∀ n, Set.BijOn (c.graphCovering hc).pathMap (GPath.nbPaths α.graphHat uh n)
        (GPath.nbPaths c.graph (c.Θ hc uh) n)) :=
  ⟨(c.graphCovering hc).pathSetMap_bijective uh, fun n => (c.graphCovering hc).bijOn_paths uh n,
    (c.graphCovering hc).pathSetMap_bijOn_noBack uh,
    fun n => (c.graphCovering hc).bijOn_nbPaths uh n⟩

theorem lemma_F33_2 (hc : c.IsFaithful) (uh : α.Γhat) :
    ∃ q : PermQuasiEquiv (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) uh) (PathSet α.graphHat uh)
      (MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range) (c.Θ hc uh)) (PathSet c.graph (c.Θ hc uh)),
      (∀ g, ((q.grp g : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) = c.theta ((g : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat)) ∧
      ∀ p, q.set p = (c.graphCovering hc).pathSetMap uh p :=
  ⟨GraphCovering.StabIso.quasiEquiv (c.graphCovering hc) (c.stabIso hc uh), fun _ => rfl,
    fun _ => rfl⟩

theorem lemma_F33_3 (hc : c.IsFaithful) (uh : α.Γhat) {n : ℕ} (p : GPath α.graphHat n)
    (hp : p 0 = uh) :
    p.stabPath.map (c.theta0 hc) = ((c.graphCovering hc).pathMap p).stabPath ∧
      Set.InjOn (c.theta0 hc) ((p.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) : Set ↥(α.Ghat1 ⊔ α.Ghat2)) ∧
      Nonempty (↥(p.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) ≃*
        ↥(((c.graphCovering hc).pathMap p).stabPath : Subgroup ↥(c.φ1.range ⊔ c.φ2.range))) :=
  ⟨(c.graphCovering hc).map_stabPath_eq (c.stabIso hc uh) p hp,
    fun _ h₁ _ h₂ h => GraphCovering.injOn_stabPath uh (c.stabIso hc uh) p hp h₁ h₂ h,
    ⟨(c.graphCovering hc).stabPathEquiv (c.stabIso hc uh) p hp⟩⟩

theorem lemma_F33_4 (hc : c.IsFaithful) (uh : α.Γhat) (n : ℕ)
    (htrans : ∀ q₁ q₂ : GPath α.graphHat n, q₁ ∈ GPath.nbPaths α.graphHat uh n →
      q₂ ∈ GPath.nbPaths α.graphHat uh n →
      ∃ g : ↥(α.Ghat1 ⊔ α.Ghat2), g • uh = uh ∧ g • q₁ = q₂)
    (p₁ p₂ : GPath c.graph n) (h₁ : p₁ ∈ GPath.nbPaths c.graph (c.Θ hc uh) n)
    (h₂ : p₂ ∈ GPath.nbPaths c.graph (c.Θ hc uh) n) :
    ∃ g : ↥(c.φ1.range ⊔ c.φ2.range), g • c.Θ hc uh = c.Θ hc uh ∧ g • p₁ = p₂ :=
  (c.graphCovering hc).transitive_of_transitive uh (c.stabIso hc uh) n htrans p₁ p₂ h₁ h₂

end Completion

end RankTwoAmalgam

end CFSG.Quasithin
