module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrSub
import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

namespace GGSFTr

private lemma mem_normalizer_of_mem_ggTorus {U : Type*} [Group U] (D : UniversalRootDatum U)
    {h : U} (hh : h ∈ ggTorus D) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    h ∈ Subgroup.normalizer (D.rootGroup γ : Set U) := by
  unfold ggTorus at hh
  exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ)) hγ

private lemma map_conj_eq_of_mem_iff {A : Type*} [Group A] (w : A) (X : Subgroup A)
    (h : ∀ a, a ∈ X ↔ w⁻¹ * a * w ∈ X) :
    X.map (MulAut.conj w).toMonoidHom = X := by
  ext a
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hx' : w⁻¹ * a * w = x := by
      rw [← hxa]
      change w⁻¹ * MulAut.conj w x * w = x
      rw [MulAut.conj_apply]
      group
    exact (h a).mpr (hx' ▸ hx)
  · intro ha
    refine ⟨w⁻¹ * a * w, (h a).mp ha, ?_⟩
    change MulAut.conj w (w⁻¹ * a * w) = a
    rw [MulAut.conj_apply]
    group

private lemma map_conj_eq_of_innerDiag {U : Type*} [Group U] {A : Type*} [Group A]
    (D : UniversalRootDatum U) (ψ : U →* A) {w : A} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) {h : U} (hh : h ∈ ggTorus D)
    (hconj : ∀ z ∈ D.rootGroup γ, w⁻¹ * ψ z * w = ψ (h * z * h⁻¹)) :
    ((D.rootGroup γ).map ψ).map (MulAut.conj w).toMonoidHom = (D.rootGroup γ).map ψ := by
  apply map_conj_eq_of_mem_iff
  intro a
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨h * z * h⁻¹,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_ggTorus D hh hγ) z).mp hz,
      (hconj z hz).symm⟩
  · rintro ⟨z', hz', hz'eq⟩
    have hhinv : h⁻¹ ∈ ggTorus D := Subgroup.inv_mem _ hh
    have hzmem : h⁻¹ * z' * h ∈ D.rootGroup γ := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_ggTorus D hhinv hγ) z').mp hz'
    refine ⟨h⁻¹ * z' * h, hzmem, ?_⟩
    have hconj' := hconj (h⁻¹ * z' * h) hzmem
    have hsimp : h * (h⁻¹ * z' * h) * h⁻¹ = z' := by group
    rw [hsimp] at hconj'
    have hcancel : ψ (h⁻¹ * z' * h) = a := by
      have h1 : w⁻¹ * ψ (h⁻¹ * z' * h) * w = w⁻¹ * a * w := by
        rw [hconj', hz'eq]
      exact mul_left_cancel (mul_right_cancel h1)
    exact hcancel

private lemma map_conj_map_psi {U : Type*} [Group U] {A : Type*} [Group A]
    (ψ : U →* A) (X : Subgroup U) (u : U) (κ : A) :
    ((X.map (MulAut.conj u).toMonoidHom).map ψ).map (MulAut.conj κ).toMonoidHom
      = (X.map ψ).map (MulAut.conj (κ * ψ u)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, mul_assoc]

variable {t : StatedLieTag} {n f p : ℕ} {M : GGKGModel t n f p} {G : Type} [Group G]
  {ψ : (ggU t n f).K →* G} {Bs : Subgroup G} (T : GGSFTr t n f p M ψ Bs)

theorem rf : GGClauseRF t n f p ψ Bs M.π T.coord := by
  intro α hαroot hαfix
  obtain ⟨δ, u₀, hδ, hnorm, hcent⟩ := M.rf α hαroot hαfix
  have hδroot : δ ∈ (ggU t n f).D.roots := hδ.1
  have hnegδroot : -δ ∈ (ggU t n f).D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (ggU t n f).D.isFiniteType hδroot
  obtain ⟨g, hg, hgdata⟩ := T.kappa_diag
  obtain ⟨hδ', hhδ', hconjδ⟩ := hgdata δ hδroot
  have hAδ : (((ggU t n f).D.rootGroup δ).map (ggPsiU t n f)).map
      (MulAut.conj (T.kappa * g)).toMonoidHom
      = ((ggU t n f).D.rootGroup δ).map (ggPsiU t n f) :=
    map_conj_eq_of_innerDiag (ggU t n f).D (ggPsiU t n f) hδroot hhδ' hconjδ
  obtain ⟨hnegδ', hhnegδ', hconjnegδ⟩ := hgdata (-δ) hnegδroot
  have hAnegδ : (((ggU t n f).D.rootGroup (-δ)).map (ggPsiU t n f)).map
      (MulAut.conj (T.kappa * g)).toMonoidHom
      = ((ggU t n f).D.rootGroup (-δ)).map (ggPsiU t n f) :=
    map_conj_eq_of_innerDiag (ggU t n f).D (ggPsiU t n f) hnegδroot hhnegδ' hconjnegδ
  have hB : ((((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map
      (ggPsiU t n f)).map (MulAut.conj (T.kappa * g)).toMonoidHom)
      = (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map
          (ggPsiU t n f)) := by
    simp only [Subgroup.map_sup]
    rw [hAδ, hAnegδ]
  have hInn_normal : ((ggPsiU t n f).range).Normal := GGSFCore.normal_range_ggPsiU t n f
  have hy₀ : ggPsiU t n f u₀ ∈ (ggPsiU t n f).range := ⟨u₀, rfl⟩
  have hconjInn : T.kappa⁻¹ * ggPsiU t n f u₀ * T.kappa ∈ (ggPsiU t n f).range := by
    simpa using hInn_normal.conj_mem (ggPsiU t n f u₀) hy₀ T.kappa⁻¹
  have hv_mem : T.kappa⁻¹ * ggPsiU t n f u₀ * T.kappa * g ∈ (ggPsiU t n f).range :=
    Subgroup.mul_mem _ hconjInn hg
  obtain ⟨u', hu'⟩ := hv_mem
  have hκv : T.kappa * ggPsiU t n f u' = ggPsiU t n f u₀ * (T.kappa * g) := by
    rw [hu']
    group
  have hJ_G_eq : (ggRankOneSub (ggU t n f).D ψ δ).map
      (MulAut.conj (ψ u')).toMonoidHom
      = ((((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map
          (MulAut.conj u').toMonoidHom).map ψ) := by
    rw [show ggRankOneSub (ggU t n f).D ψ δ
        = ((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map ψ from rfl]
    simp only [Subgroup.map_map]
    congr 1
    ext k
    simp [MulAut.conj_apply, map_mul]
  have hJG_le_N : (ggRankOneSub (ggU t n f).D ψ δ).map
      (MulAut.conj (ψ u')).toMonoidHom ≤ T.N := by
    rw [hJ_G_eq]
    exact (Subgroup.map_le_range ψ _).trans T.psi_le
  have hfwd : T.fwd ((ggRankOneSub (ggU t n f).D ψ δ).map
      (MulAut.conj (ψ u')).toMonoidHom)
      = (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ).map
          (MulAut.conj (ggPsiU t n f u₀)).toMonoidHom := by
    rw [hJ_G_eq, T.fwd_map_psi]
    rw [map_conj_map_psi (ggPsiU t n f)
      ((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)) u' T.kappa]
    rw [hκv]
    have hmul : (MulAut.conj (ggPsiU t n f u₀ * (T.kappa * g))).toMonoidHom
        = (MulAut.conj (ggPsiU t n f u₀)).toMonoidHom.comp
            (MulAut.conj (T.kappa * g)).toMonoidHom := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [hmul, ← Subgroup.map_map, hB]
    rfl
  refine ⟨δ, u', hδ, ?_, ?_⟩
  · intro b hb
    have hbN : (b : G) ∈ T.N := T.bs_le hb
    have hiff : (b : G) ∈ Subgroup.normalizer
        ((ggRankOneSub (ggU t n f).D ψ δ).map
          (MulAut.conj (ψ u')).toMonoidHom : Set G) ↔
        T.hom ⟨b, hbN⟩ ∈ Subgroup.normalizer
          (T.fwd ((ggRankOneSub (ggU t n f).D ψ δ).map
            (MulAut.conj (ψ u')).toMonoidHom) : Set (GGAutU t n f)) :=
      T.mem_normalizer_fwd_iff hJG_le_N ⟨b, hbN⟩
    refine hiff.mpr ?_
    rw [hfwd]
    have hthis : T.hom ⟨b, hbN⟩ = (T.toB ⟨b, hb⟩ : GGAutU t n f) := by
      rw [T.toB_val, T.toHom_apply]
    rw [hthis]
    exact hnorm (T.toB ⟨b, hb⟩).2
  · intro b
    have hbN : (b : G) ∈ T.N := T.bs_le b.2
    have hiff : (b : G) ∈ Subgroup.centralizer
        ((ggRankOneSub (ggU t n f).D ψ δ).map
          (MulAut.conj (ψ u')).toMonoidHom : Set G) ↔
        T.hom ⟨b, hbN⟩ ∈ Subgroup.centralizer
          (T.fwd ((ggRankOneSub (ggU t n f).D ψ δ).map
            (MulAut.conj (ψ u')).toMonoidHom) : Set (GGAutU t n f)) :=
      T.mem_centralizer_fwd_iff hJG_le_N ⟨b, hbN⟩
    rw [hiff, hfwd]
    have hthis : T.hom ⟨b, hbN⟩ = (T.toB b : GGAutU t n f) := by
      rw [T.toB_val, T.toHom_apply]
    rw [hthis, T.coord_apply]
    exact hcent (T.toB b)

end GGSFTr

end Universal

end CFSG.StandardType
