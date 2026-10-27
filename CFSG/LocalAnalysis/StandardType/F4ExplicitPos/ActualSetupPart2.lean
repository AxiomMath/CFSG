module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ActualSetupPart1

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

theorem f4_coordinates_actual
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) {p : ℕ} (hB1 : IsElemAbelian p B1)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup .F4) {g0 : ModGL .F4 L} (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup .F4 L) :
      ModGL .F4 L) = g0 * canonicalRep (coxeterSystem .F4) L w)
    (htor : ∀ d : D, ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
      (Subgroup.inclusion hDB d) ∈
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).torus) :
    ∃ coord : D → Fin Tag.F4.rank → Lˣ,
      (∀ d : D, ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        (Subgroup.inclusion hDB d) = rootDiagUnit .F4 (coord d)) ∧
      (∀ (d : D) (i : Fin Tag.F4.rank), (coord d i) ^ p = 1) := by
  choose coord hcoord using fun d : D =>
    exists_rootDiagUnit_eq_of_mem_torusGroup (htor d).1
  refine ⟨coord, hcoord, fun d i => ?_⟩
  have hc : (Subgroup.inclusion hDB d) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hB1.2 (((Subgroup.inclusion hDB d : B1)) : X) (Subgroup.inclusion hDB d).2
  have h1 : rootDiagUnit .F4 (coord d ^ p) = 1 := by
    change (rootDiagUnitHom .F4 L) (coord d ^ p) = 1
    rw [map_pow (rootDiagUnitHom .F4 L) (coord d) p]
    change rootDiagUnit .F4 (coord d) ^ p = 1
    rw [← hcoord d,
      ← map_pow (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0)
        (Subgroup.inclusion hDB d) p, hc, map_one]
  have h2 : coord d ^ p = 1 :=
    rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  exact congrFun h2 i

theorem f4_actual_setup_of_toral
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X} {G0 B1 D : Subgroup X}
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) (hB1 : IsElemAbelian p B1)
    [IsAlgClosed L] [CharP L 2] [Algebra (GaloisField 2 f) L]
    (hf : 1 ≤ f) (hpq : Nat.Coprime p (2 ^ f))
    {g : ModGL .F4 L} (hg : g ∈ adjointGroup .F4 L)
    (hgA : ∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
      g⁻¹ * a * g ∈ torusGroup .F4 L) :
    ∃ (w : WeylGroup .F4) (g0 : ModGL .F4 L) (hg0C : g0 ∈ adjointGroup .F4 L)
      (hg0 : ((frobF4 (K := GaloisField 2 f) (L := L) (iterateFrobenius L 2 f)
        (iterateFrobenius_card_F4 (L := L) f hf) ⟨g0, hg0C⟩ : adjointGroup .F4 L) :
        ModGL .F4 L) = g0 * canonicalRep (coxeterSystem .F4) L w),
      let Δ := langDatumF4 (K := GaloisField 2 f) (L := L) (iterateFrobenius L 2 f)
        (iterateFrobenius_card_F4 (L := L) f hf) w hg0C hg0
      FrobRootMap Δ (MulAction.toPerm w) ∧ Finite Δ.model ∧
      (∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
        g0⁻¹ * a * g0 ∈ Δ.torus) ∧
      (∀ b : B1, Δ.step (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b) =
        ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b) ∧
      (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0).ker =
        (Subgroup.centralizer (G0 : Set X)).subgroupOf B1 ∧
      ∃ coord : D → Fin Tag.F4.rank → Lˣ,
        (∀ d : D, ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
          (Subgroup.inclusion hDB d) = rootDiagUnit .F4 (coord d)) ∧
        (∀ (d : D) (i : Fin Tag.F4.rank), (coord d i) ^ p = 1) := by
  have hFr := iterateFrobenius_card_F4 (L := L) f hf
  have hsurj : Function.Surjective (iterateFrobenius L 2 f) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos Nat.prime_two.pos f)
    exact ⟨x, by rw [iterateFrobenius_def, hx]⟩
  have hexp : ∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
      a ^ p = 1 :=
    thetaGLimage_exp (L := L) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB hB1
  have hFix : ∀ a ∈ thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
      entrywiseFrobGL .F4 L 2 f a = a :=
    thetaGLimage_frobF4_fixed (L := L) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB
      (iterateFrobenius L 2 f) hFr
  obtain ⟨w, g0, hg0C, hLang, hmem⟩ :=
    CFSG.StandardType.F4ExplicitPos.LangPosition.f4_exists_lang_torus_of_conj_torus
      (Ω := L) f hf hpq hexp hFix hg hgA
  have hg0 : ((frobF4 (K := GaloisField 2 f) (L := L) (iterateFrobenius L 2 f) hFr
      ⟨g0, hg0C⟩ : adjointGroup .F4 L) : ModGL .F4 L) =
      g0 * canonicalRep (coxeterSystem .F4) L w := by
    rw [frobF4_coe_eq_unitsMap]
    exact hLang
  refine ⟨w, g0, hg0C, hg0, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact frobRootMap_langDatumF4 (K := GaloisField 2 f) (L := L) (iterateFrobenius L 2 f)
      hFr hsurj w hg0C hg0
  · rw [← etaF4_range_model (K := GaloisField 2 f) (L := L) ψ G0 hG0 hker hcenter
      (iterateFrobenius L 2 f) hFr w hg0C hg0]
    exact Set.Finite.to_subtype (by
      rw [MonoidHom.coe_range]
      exact Finite.Set.finite_range (etaF4 (L := L) ψ G0 hG0 hker hcenter g0))
  · intro a ha
    obtain ⟨y, hy, hy'⟩ := hmem a ha
    rw [← hy']
    have he : g0⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g0)) y * g0 = y := by
      change g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y
      group
    rw [he]
    exact hy
  · intro b
    have hmem' := ThetaF4_range_le_model (K := GaloisField 2 f) (L := L) ψ G0 B1 hG0 hker
      hcenter hBN hinner (iterateFrobenius L 2 f) hFr w hg0C hg0 ⟨b, rfl⟩
    rw [LangDatum.mem_model] at hmem'
    simpa [LangDatum.step, MulAut.conj_apply] using hmem'.2
  · exact ThetaF4_ker (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
  · apply f4_coordinates_actual (L := L) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB hB1
      (iterateFrobenius L 2 f) hFr w hg0C hg0
    intro d
    have hdDsub : (Subgroup.inclusion hDB d) ∈ D.subgroupOf B1 :=
      Subgroup.mem_subgroupOf.mpr d.2
    have hthetaMap : thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
          (Subgroup.inclusion hDB d) ∈
        (D.subgroupOf B1).map (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner) :=
      Subgroup.mem_map_of_mem (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner) hdDsub
    have hmemA : ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
        (Subgroup.inclusion hDB d) : adjointGroup .F4 L) : ModGL .F4 L) ∈
        thetaGLimage (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB := by
      show ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
          (Subgroup.inclusion hDB d) : adjointGroup .F4 L) : ModGL .F4 L) ∈
        ((D.subgroupOf B1).map
          (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner)).map
          (adjointGroup .F4 L).subtype
      exact Subgroup.mem_map_of_mem (adjointGroup .F4 L).subtype hthetaMap
    obtain ⟨y, hy, hy'⟩ := hmem _ hmemA
    have hx : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        (Subgroup.inclusion hDB d) = y := by
      rw [show ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
            (Subgroup.inclusion hDB d) =
            g0⁻¹ * ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
              (Subgroup.inclusion hDB d) : adjointGroup .F4 L) : ModGL .F4 L) * g0
          from ThetaF4_apply (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
            (Subgroup.inclusion hDB d)]
      rw [← hy']
      have he : g0⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g0)) y * g0 = y := by
        change g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y
        group
      rw [he]
    rw [hx]
    exact hy

theorem f4_joint_attachment_actual
    (ψ : adjointGroup .F4 K →* X) (G0 B1 D : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup .F4) {g0 : ModGL .F4 L} (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup .F4 L) :
      ModGL .F4 L) = g0 * canonicalRep (coxeterSystem .F4) L w)
    {x d : X} (hxD : x ∈ D) (hdD : d ∈ D)
    (hgen : Subgroup.closure ({x, d} : Set X) = D)
    (coord : D → Fin Tag.F4.rank → Lˣ)
    (hcoord : ∀ d0 : D, ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
      (Subgroup.inclusion hDB d0) = rootDiagUnit .F4 (coord d0))
    {J : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (G0 ⊓ Subgroup.centralizer (D : Set X))) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0))
      ((langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).Γ ⊓
        Subgroup.centralizer
          ({rootDiagUnit .F4 (coord ⟨x, hxD⟩), rootDiagUnit .F4 (coord ⟨d, hdD⟩)} :
            Set (ModGL .F4 L))) :=
  isComponentOf_eta_joint (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner Fr hFr w hg0C hg0
    D hDB hxD hdD hgen (coord ⟨x, hxD⟩) (coord ⟨d, hdD⟩)
    (hcoord ⟨x, hxD⟩) (hcoord ⟨d, hdD⟩) hJ

end CFSG.StandardType.F4ExplicitPos.ActualSetup

end

end
