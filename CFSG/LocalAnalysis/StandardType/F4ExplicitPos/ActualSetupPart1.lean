module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ToralDescent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.ActualSetup

variable {K L X : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Group X] [Finite X]

theorem ThetaF4_mem_etaF4_range
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g0 : ModGL .F4 L) (b : B1) :
    ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b ∈
      (etaF4 (L := L) ψ G0 hG0 hker hcenter g0).range := by
  have hfix : Units.map (entrywiseHom Fr)
      ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b : adjointGroup .F4 L) :
        ModGL .F4 L) =
      ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b : adjointGroup .F4 L) :
        ModGL .F4 L) := by
    rw [← frobF4_coe_eq_unitsMap Fr hFr
      (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b)]
    exact congrArg Subtype.val
      (frobF4_thetaF4 Fr hFr ψ G0 B1 hG0 hker hcenter hBN hinner b)
  have hmem : ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
      adjointGroup .F4 L) : ModGL .F4 L) ∈
      (adjointGroup .F4 K).map (bcGL (τ := .F4) (algebraMap K L)) := by
    rw [f4_finite_field_fixed_eq_map (K := K) (Ω := L) Fr hFr]
    exact Subgroup.mem_inf.2 ⟨(thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b).2,
      hfix⟩
  have hz : ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
      adjointGroup .F4 L)) ∈
      (jF4 (K := K) (L := L)).range := by
    have h := hmem
    rw [← jF4_range_eq K L] at h
    obtain ⟨z, hz, hz'⟩ := h
    have hz_eq : z = (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
        adjointGroup .F4 L) := Subtype.ext hz'
    rw [← hz_eq]
    exact hz
  have hzr : ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
      adjointGroup .F4 L)) ∈
      (iotaF4 (L := L) ψ G0 hG0 hker hcenter).range := by
    rw [iotaF4_range (K := K) (Ω := L) ψ G0 hG0 hker hcenter]
    exact hz
  obtain ⟨y, hy⟩ := hzr
  refine ⟨y, ?_⟩
  simp only [ThetaF4_apply, etaF4_apply, hy]

theorem ThetaF4_range_le_model
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup .F4) {g0 : ModGL .F4 L} (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup .F4 L) :
      ModGL .F4 L) = g0 * canonicalRep (coxeterSystem .F4) L w) :
    (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0).range ≤
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).model := by
  intro z hz
  obtain ⟨b, rfl⟩ := hz
  rw [← etaF4_range_model (K := K) (L := L) ψ G0 hG0 hker hcenter Fr hFr w hg0C hg0]
  exact ThetaF4_mem_etaF4_range (K := K) (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
    Fr hFr g0 b

noncomputable def thetaDimage
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (D : Subgroup X) (_hDB : D ≤ B1) : Subgroup (adjointGroup .F4 L) :=
  (D.subgroupOf B1).map (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner)

noncomputable def thetaGLimage
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (D : Subgroup X) (hDB : D ≤ B1) : Subgroup (ModGL .F4 L) :=
  (thetaDimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB).map
    (adjointGroup .F4 L).subtype

theorem thetaGLimage_le_adjointGroup
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) :
    thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB ≤
      adjointGroup .F4 L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem thetaGLimage_finite
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) :
    Finite (thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB) := by
  have hfin : ((D.subgroupOf B1 : Set B1)).Finite := Set.toFinite _
  have h1 : (((D.subgroupOf B1).map (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN
      hinner) : Set (adjointGroup .F4 L))).Finite := by
    rw [Subgroup.coe_map]
    exact hfin.image _
  have h3 : ((thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB :
      Set (ModGL .F4 L))).Finite := by
    rw [thetaGLimage, thetaDimage, Subgroup.coe_map]
    exact h1.image _
  exact h3.to_subtype

theorem thetaGLimage_isElemAbelian
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) {p : ℕ} (hB1 : IsElemAbelian p B1) :
    IsElemAbelian p (thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB) := by
  rw [thetaGLimage, thetaDimage]
  exact ((IsElemAbelian.subgroupOf hB1 B1).mono fun y _ => y.2).map
    (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner) |>.map
      (adjointGroup .F4 L).subtype

theorem thetaGLimage_exp
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) {p : ℕ} (hB1 : IsElemAbelian p B1) :
    ∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB, a ^ p = 1 :=
  (thetaGLimage_isElemAbelian (L := L) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB hB1).2

theorem thetaGLimage_card_le
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) {p : ℕ} (hDcard : Nat.card D = p ^ 2) :
    Nat.card (thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB) ≤
      p ^ 2 := by
  have h := thetaD_image_card_le (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB hDcard
  rw [thetaGLimage]
  rwa [Subgroup.card_map_of_injective (K := thetaDimage (L := L) ψ G0 B1 hG0 hker hcenter
    hBN hinner D hDB) (f := (adjointGroup .F4 L).subtype) Subtype.coe_injective]

theorem thetaGLimage_frobF4_fixed
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
      Units.map (entrywiseHom Fr) a = a := by
  rintro a ⟨y, ⟨b, -, rfl⟩, rfl⟩
  have h := frobF4_thetaF4 (K := K) (L := L) Fr hFr ψ G0 B1 hG0 hker hcenter hBN hinner b
  have h' := congrArg (fun z : adjointGroup .F4 L => (z : ModGL .F4 L)) h
  rwa [frobF4_coe_eq_unitsMap] at h'

theorem units_map_entrywiseHom_eq_bcGL (Fr : L →+* L) :
    (Units.map (entrywiseHom Fr) : ModGL .F4 L →* ModGL .F4 L) = bcGL (τ := .F4) Fr := by
  rw [bcGL, bcEndHom_eq_entrywiseHom]

theorem units_map_entrywiseHom_rootDiagUnit
    (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (a : Fin Tag.F4.rank → Lˣ) :
    Units.map (entrywiseHom Fr) (rootDiagUnit .F4 a) =
      rootDiagUnit .F4 (a ^ Nat.card K) := by
  rw [units_map_entrywiseHom_eq_bcGL]
  rw [CFSG.StandardType.F4ExplicitPos.ToralDescent.bcGL_rootDiagUnit_F4]
  congr 1
  funext i
  exact Units.ext (hFr (a i))

theorem frobRootMap_langDatumF4
    (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hsurj : Function.Surjective Fr)
    (w : WeylGroup .F4) {g0 : ModGL .F4 L} (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup .F4 L) :
      ModGL .F4 L) = g0 * canonicalRep (coxeterSystem .F4) L w) :
    FrobRootMap (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0)
      (MulAction.toPerm w) := by
  refine ⟨fun γ => isRoot_smul_iff w, fun γ => by
    change w • (-γ) = -(w • γ)
    exact smul_neg w γ, fun γ δ => iform_smul w γ δ, ?_, ?_⟩
  · intro γ hγ
    have hstep : (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).step =
        (MulAut.conj (canonicalRep (coxeterSystem .F4) L w)).toMonoidHom.comp
          (Units.map (entrywiseHom Fr)) := rfl
    rw [hstep, ← Subgroup.map_map]
    rw [units_map_entrywiseHom_eq_bcGL]
    rw [CFSG.StandardType.F4ExplicitPos.PinnedBaseChange.map_bcGL_rootSubgroup_eq_of_surjective
      (τ := .F4) Fr hsurj γ]
    exact (canonical_weyl_root_transport .F4 L).2.1 w γ hγ
  · intro a ha γ hγ
    set n := canonicalRep (coxeterSystem .F4) L w with hn
    have hPhi : Units.map (entrywiseHom Fr) (rootDiagUnit .F4 a) =
        rootDiagUnit .F4 (a ^ Nat.card K) :=
      units_map_entrywiseHom_rootDiagUnit Fr hFr a
    have hconj : rootDiagUnit .F4 a = n * rootDiagUnit .F4 (a ^ Nat.card K) * n⁻¹ := by
      have h2 : n * Units.map (entrywiseHom Fr) (rootDiagUnit .F4 a) * n⁻¹ =
          rootDiagUnit .F4 a := ha.2
      rw [hPhi] at h2
      exact h2.symm
    have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) a (a ^ Nat.card K) w).1
      (by simpa [hn] using hconj) γ
    change rootChar a (w • γ) = rootChar a γ ^
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).q
    rw [hchar, CFSG.StandardType.F4ExplicitPos.LangPosition.rootChar_pow_no117]
    rfl

theorem iterateFrobenius_card_F4 [CharP L 2] (f : ℕ) (hf : 1 ≤ f) :
    ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card (GaloisField 2 f) := by
  intro c
  rw [iterateFrobenius_def, GaloisField.card 2 f (by omega)]

end CFSG.StandardType.F4ExplicitPos.ActualSetup
end

end
