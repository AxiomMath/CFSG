module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem even_finrank_commSpace_of_triv [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {Z : Submodule K V}
    (hZ : (toQuadForm Q hQ).IsTotallySingular Z)
    (htriv : ∀ v ∈ (toQuadForm Q hQ).polar.perp Z, g v - v ∈ Z) :
    Even (finrank K (commSpace g)) := by
  set Φ := toQuadForm Q hQ with hΦ
  have hZ0 : Φ.prodNeg.IsTotallySingular (Z.prod ⊥) := by
    intro p hp
    rw [Submodule.mem_prod, Submodule.mem_bot] at hp
    rw [QuadForm.prodNeg_Q, hZ _ hp.1, hp.2, Φ.Q_zero, sub_zero]
  obtain ⟨X, hX, hZX⟩ := QuadForm.exists_isLagrangian_le Φ.isLagrangian_prodNeg_diagonal hZ0
  have hXperp : X ≤ Φ.prodNeg.polar.perp (Z.prod ⊥) :=
    hX.1.isTotallyIsotropic.trans (Φ.prodNeg.polar.perp_antitone hZX)
  set G : Module.End K (V × V) := (g : V →ₗ[K] V).prodMap LinearMap.id with hG
  have hGQ : ∀ p, Φ.prodNeg.Q (G p) = Φ.prodNeg.Q p :=
    QuadForm.prodNeg_Q_prodMap (toQuadForm_Q_apply hQ hg)
  have hGX : X.map G ≤ X := by
    rintro _ ⟨p, hp, rfl⟩
    have hp1 : p.1 ∈ Φ.polar.perp Z := fun z hz => by
      have h := hXperp hp (z, 0) (Submodule.mem_prod.mpr ⟨hz, Submodule.zero_mem _⟩)
      rw [QuadForm.prodNeg_polar_β, Φ.polar.β_zero_left, sub_zero] at h
      exact h
    have e : G p = p + (g p.1 - p.1, 0) := by
      ext <;> simp [hG]
    rw [e]
    exact add_mem hp (hZX (Submodule.mem_prod.mpr ⟨htriv _ hp1, Submodule.zero_mem _⟩))
  have hGXeq : X.map G = X :=
    Submodule.eq_of_le_of_finrank_eq hGX (QuadForm.finrank_map_of_Q hGQ X)
  have h0 : dicksonInvariant X G = 0 := by
    rw [dicksonInvariant, hGXeq, inf_idem, Nat.sub_self, Nat.cast_zero]
  have h1 := QuadForm.dicksonInvariant_eq Φ.isLagrangian_prodNeg_diagonal hX hGQ
  rw [h0, dicksonInvariant_diagonal] at h1
  exact (ZMod.natCast_eq_zero_iff_even).mp h1

theorem mem_omegaGroup_of_triv [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {Z : Submodule K V}
    (hZ : (toQuadForm Q hQ).IsTotallySingular Z)
    (htriv : ∀ v ∈ (toQuadForm Q hQ).polar.perp Z, g v - v ∈ Z) : g ∈ omegaGroup Q hQ :=
  mem_omegaGroup.mpr ⟨hg, even_finrank_commSpace_of_triv hQ hg hZ htriv⟩

end GGOppRadOmega

end CFSG.StandardType
