module

public import CFSG.Quasithin.Background.F3Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} {Y' : Type w'} [Group Y] [Group Y']
  (ι : α.Completion Y) (β : α.Completion Y') (hι : ι.IsFaithful) (hβ : β.IsFaithful)

@[expose] noncomputable def psi (uh : α.Γhat) :
    PathSet ι.graph (ι.Θ hι uh) ≃ PathSet β.graph (β.Θ hβ uh) :=
  GraphCovering.psi (ι.graphCovering hι) (β.graphCovering hβ) uh

@[expose] noncomputable def stabComp (uh : α.Γhat) :
    MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι uh) ≃*
      MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh) :=
  GraphCovering.StabIso.comp (ι.stabIso hι uh) (β.stabIso hβ uh)

@[expose] noncomputable def lemma_F34_1 (uh : α.Γhat) :
    PermQuasiEquiv (MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι uh))
      (PathSet ι.graph (ι.Θ hι uh))
      (MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh))
      (PathSet β.graph (β.Θ hβ uh)) :=
  GraphCovering.quasiEquivComp (ι.graphCovering hι) (β.graphCovering hβ) (ι.stabIso hι uh)
    (β.stabIso hβ uh)

theorem lemma_F34_1_grp (uh : α.Γhat) : (lemma_F34_1 ι β hι hβ uh).grp = stabComp ι β hι hβ uh :=
  rfl

theorem lemma_F34_1_set (uh : α.Γhat) : (lemma_F34_1 ι β hι hβ uh).set = psi ι β hι hβ uh :=
  rfl

theorem stabComp_theta (uh : α.Γhat) (g : MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) uh) :
    ((stabComp ι β hι hβ uh ((ι.stabIso hι uh).equiv g) :
      MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh)) : ↥(β.φ1.range ⊔ β.φ2.range)) =
      β.theta0 hβ g := by
  unfold stabComp
  rw [GraphCovering.StabIso.comp_spec]
  rfl

theorem lemma_F34_2 (uh : α.Γhat) (p : PathSet ι.graph (ι.Θ hι uh))
    (g : MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι uh)) :
    (g : ↥(ι.φ1.range ⊔ ι.φ2.range)) ∈ p.2.1.stabPath ↔
      ((stabComp ι β hι hβ uh g : MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh)) :
        ↥(β.φ1.range ⊔ β.φ2.range)) ∈ (psi ι β hι hβ uh p).2.1.stabPath :=
  GraphCovering.mem_stabPath_comp_iff (ι.graphCovering hι) (β.graphCovering hβ)
    (ι.stabIso hι uh) (β.stabIso hβ uh) p g

theorem lemma_F34_3 (uh : α.Γhat) (n : ℕ)
    (htrans : ∀ p₁ p₂ : GPath ι.graph n, p₁ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      p₂ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      ∃ g : ↥(ι.φ1.range ⊔ ι.φ2.range), g • ι.Θ hι uh = ι.Θ hι uh ∧ g • p₁ = p₂)
    (p₁ p₂ : GPath β.graph n) (h₁ : p₁ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n)
    (h₂ : p₂ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n) :
    ∃ g : ↥(β.φ1.range ⊔ β.φ2.range), g • β.Θ hβ uh = β.Θ hβ uh ∧ g • p₁ = p₂ :=
  lemma_F33_4 β hβ uh n
    (fun q₁ q₂ h₁ h₂ => (ι.graphCovering hι).transitive_of_transitive' uh (ι.stabIso hι uh) n
      htrans q₁ q₂ h₁ h₂) p₁ p₂ h₁ h₂

abbrev xhat : α.Γhat := CosetGeom.γ₀ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2

abbrev lhat : α.Γhat := CosetGeom.γ₁ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2

theorem stabComp_x (a : α.G1)
    (g : MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι xhat))
    (hg : ((g : ↥(ι.φ1.range ⊔ ι.φ2.range)) : Y) = ι.φ1 a) :
    (((stabComp ι β hι hβ xhat g : MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range)
      (β.Θ hβ xhat)) : ↥(β.φ1.range ⊔ β.φ2.range)) : Y') = β.φ1 a := by
  obtain ⟨gq, rfl⟩ := (ι.stabIso hι xhat).equiv.surjective g
  have hgq : ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) ∈ α.Ghat1 := by
    have h4 := CosetGeom.mem_stab_of_smul_eq (MulAction.mem_stabilizer_iff.mp gq.2)
    rwa [CosetGeom.stab_γ₀ (G₀ := α.Ghat1 ⊔ α.Ghat2) (G₂ := α.Ghat2) le_sup_left] at h4
  obtain ⟨a', ha'⟩ := hgq
  have h1 : ι.φ1 a' = ι.φ1 a := by
    rw [← hg]
    show ι.φ1 a' = ι.theta ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat)
    rw [← ha']
    exact (ι.theta_ξ1 a').symm
  have h2 : a' = a := hι.1 h1
  have h3 := stabComp_theta ι β hι hβ xhat gq
  have h4 := congrArg Subtype.val h3
  refine h4.trans ?_
  show β.theta ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) = β.φ1 a
  rw [← ha', h2]
  exact β.theta_ξ1 a

theorem stabComp_l (a : α.G2)
    (g : MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι lhat))
    (hg : ((g : ↥(ι.φ1.range ⊔ ι.φ2.range)) : Y) = ι.φ2 a) :
    (((stabComp ι β hι hβ lhat g : MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range)
      (β.Θ hβ lhat)) : ↥(β.φ1.range ⊔ β.φ2.range)) : Y') = β.φ2 a := by
  obtain ⟨gq, rfl⟩ := (ι.stabIso hι lhat).equiv.surjective g
  have hgq : ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) ∈ α.Ghat2 := by
    have h4 := CosetGeom.mem_stab_of_smul_eq (MulAction.mem_stabilizer_iff.mp gq.2)
    rwa [CosetGeom.stab_γ₁ (G₀ := α.Ghat1 ⊔ α.Ghat2) (G₁ := α.Ghat1) le_sup_right] at h4
  obtain ⟨a', ha'⟩ := hgq
  have h1 : ι.φ2 a' = ι.φ2 a := by
    rw [← hg]
    show ι.φ2 a' = ι.theta ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat)
    rw [← ha']
    exact (ι.theta_ξ2 a').symm
  have h2 : a' = a := hι.2.2 h1
  have h3 := stabComp_theta ι β hι hβ lhat gq
  have h4 := congrArg Subtype.val h3
  refine h4.trans ?_
  show β.theta ((gq : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat) = β.φ2 a
  rw [← ha', h2]
  exact β.theta_ξ2 a

end RankTwoAmalgam.Completion

end CFSG.Quasithin
