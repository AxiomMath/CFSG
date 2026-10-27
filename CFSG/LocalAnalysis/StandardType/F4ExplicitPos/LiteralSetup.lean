module

public import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ToralFinishPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointOrbitSelectionPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ActualSetupPart2

@[expose] public section

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

open CFSG.StandardType.ExcFramesHalf

open CFSG.StandardType.LieCore

open CFSG.Assembly

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.InnerDirect

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.ActualSetup

open CFSG.StandardType.F4ExplicitPos.DistinguishedL

open CFSG.StandardType.F4ExplicitPos.JointOrbitSelection

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped commutatorElement Pointwise

namespace CFSG.StandardType.F4ExplicitPos.LiteralSetup

variable {X : Type} [Group X] [Finite X]

abbrev F4Omega (f : ℕ) : Type := AlgebraicClosure (GaloisField 2 f)

structure F4PosData
    {n f p : ℕ} (ψ : (ggU .F4 n f).K →* X)
    (G₀ B₁ D J L : Subgroup X) (x : X) : Type where
  hG0 : ψ.range = G₀
  hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f))
  hBN : B₁ ≤ Subgroup.normalizer (G₀ : Set X)
  hinner : ∀ b ∈ B₁, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X)
  hDB : D ≤ B₁
  hB1 : IsElemAbelian p B₁
  hp : p.Prime
  hp2 : p ≠ 2
  hDcard : Nat.card D = p ^ 2
  hf : 1 ≤ f
  h17 : x ∈ D
  h15 : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))
  hL0G : L ≤ G₀

def F4PosData.ofHyp
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X} {G₀ B₁ D J L : Subgroup X}
    {x : X} (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    F4PosData (p := p) ψ G₀ B₁ D J L x := by
  have hinner := f4_exists_inner_correction_hH hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact ⟨h1, h2, h7, hinner, h11, h9, h5, h6, h12,
    (LieModel.admissible h3).2.1, h17, h15, h19⟩

theorem center_adjointGroup_F4_galoisField
    (f : ℕ) :
    Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
  CFSG.StandardType.F4ExplicitPos.CenterProofFast.center_adjointGroup_F4_charTwo_eq_bot
    (K := GaloisField 2 f)

theorem f4_actual_setup_literal
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X} {G0 B1 D : Subgroup X}
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (hDB : D ≤ B1) (hB1 : IsElemAbelian p B1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hDcard : Nat.card D = p ^ 2) (hf : 1 ≤ f) :
    ∃ (w : WeylGroup .F4) (g0 : ModGL .F4 (F4Omega f))
      (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
      (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f hf) ⟨g0,
            hg0C⟩ : adjointGroup .F4 (F4Omega f)) :
        ModGL .F4 (F4Omega f)) =
        g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w),
      let Δ := langDatumF4 (K := GaloisField 2 f) (L :=
          F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f hf) w hg0C hg0
      FrobRootMap Δ (MulAction.toPerm w) ∧ Finite Δ.model ∧
      (∀ a ∈ thetaGLimage (L := F4Omega f) ψ G0 B1 hG0 hker
          (center_adjointGroup_F4_galoisField f) hBN hinner D hDB,
        g0⁻¹ * a * g0 ∈ Δ.torus) ∧
      (∀ b : B1, Δ.step (ThetaF4 (L := F4Omega f) ψ G0 B1 hG0 hker
          (center_adjointGroup_F4_galoisField f) hBN hinner g0 b) =
        ThetaF4 (L := F4Omega f) ψ G0 B1 hG0 hker
          (center_adjointGroup_F4_galoisField f) hBN hinner g0 b) ∧
      (ThetaF4 (L := F4Omega f) ψ G0 B1 hG0 hker
          (center_adjointGroup_F4_galoisField f) hBN hinner g0).ker =
        (Subgroup.centralizer (G0 : Set X)).subgroupOf B1 ∧
      ∃ coord : D → Fin Tag.F4.rank → (F4Omega f)ˣ,
        (∀ d0 : D, ThetaF4 (L := F4Omega f) ψ G0 B1 hG0 hker
            (center_adjointGroup_F4_galoisField f) hBN hinner g0
            (Subgroup.inclusion hDB d0) = rootDiagUnit .F4 (coord d0)) ∧
        (∀ (d0 : D) (i : Fin Tag.F4.rank), (coord d0 i) ^ p = 1) := by
  have hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_F4_galoisField f
  have h2p : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  have hpq : Nat.Coprime p (2 ^ f) := Nat.prime_two.coprime_pow_of_not_dvd (m := f) h2p
  have halg : letI := ZMod.algebra (F4Omega f) 2; Algebra.IsAlgebraic (ZMod 2) (F4Omega f) :=
    CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (GaloisField 2 f)
  have htoral : IsToralSubgroup .F4 (F4Omega f)
      (thetaGLimage (L := F4Omega f) ψ G0 B1 hG0 hker hcenter hBN hinner D hDB) :=
    CFSG.StandardType.F4ExplicitPos.ToralFinish.isToralSubgroup_F4_of_card_le_sq
      (L := F4Omega f) halg hp hp2
      (thetaGLimage_le_adjointGroup (L := F4Omega f) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB)
      (thetaGLimage_finite (L := F4Omega f) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB)
      (thetaGLimage_isElemAbelian (L := F4Omega f) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB hB1)
      (thetaGLimage_card_le (L := F4Omega f) ψ G0 B1 D hG0 hker hcenter hBN hinner hDB hDcard)
  obtain ⟨g, hg, hgA⟩ := htoral
  exact f4_actual_setup_of_toral (L := F4Omega f) (ψ := ψ) (G0 := G0) (B1 := B1) (D := D)
    hG0 hker hcenter hBN hinner hDB hB1 hf hpq hg hgA

theorem f4_literal_setup
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    let FD := F4PosData.ofHyp hH
    ∃ (w : WeylGroup .F4) (g0 : ModGL .F4 (F4Omega f))
      (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
      (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) ⟨g0, hg0C⟩ :
        adjointGroup .F4 (F4Omega f)) : ModGL .F4 (F4Omega f)) =
        g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w),
      let Δ := langDatumF4 (K := GaloisField 2 f) (L :=
          F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0
      FrobRootMap Δ (MulAction.toPerm w) ∧ Finite Δ.model ∧
      (∀ a ∈ thetaGLimage (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner D FD.hDB,
        g0⁻¹ * a * g0 ∈ Δ.torus) ∧
      (∀ b : B₁, Δ.step (ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0 b) =
        ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0 b) ∧
      (ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0).ker =
        (Subgroup.centralizer (G₀ : Set X)).subgroupOf B₁ ∧
      ∃ (d : X) (hdD : d ∈ D) (coord : D → Fin Tag.F4.rank → (F4Omega f)ˣ),
        d ≠ 1 ∧ d ∉ Subgroup.centralizer (L : Set X) ∧
        Subgroup.closure ({x, d} : Set X) = D ∧
        (∀ d0 : D, ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
            (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0
            (Subgroup.inclusion FD.hDB d0) = rootDiagUnit .F4 (coord d0)) ∧
        (∀ (d0 : D) (i : Fin Tag.F4.rank), (coord d0 i) ^ p = 1) ∧
        coord ⟨d, hdD⟩ ≠ 1 ∧
        CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map
            (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
              (center_adjointGroup_F4_galoisField f) g0))
          (Δ.Γ ⊓ Subgroup.centralizer
            ({rootDiagUnit .F4 (coord ⟨x, FD.h17⟩), rootDiagUnit .F4 (coord ⟨d, hdD⟩)} :
              Set (ModGL .F4 (F4Omega f)))) ∧
        ∃ i : KernelComponent (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)),
          ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
              (center_adjointGroup_F4_galoisField f) g0)) ≤
            rootSpan .F4 (F4Omega f)
              (ratOrbit (fun u => (MulAction.toPerm w) u)
                (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) i)) := by
  set FD := F4PosData.ofHyp hH with hFD
  obtain ⟨w, g0, hg0C, hg0, hFrob, hFin, htor, hstep, hTheker, coord, hcoord, hexp⟩ :=
    f4_actual_setup_literal (ψ := ψ) (G0 := G₀) (B1 := B₁) (D := D)
      FD.hG0 FD.hker FD.hBN FD.hinner FD.hDB FD.hB1 FD.hp FD.hp2 FD.hDcard FD.hf
  obtain ⟨d, hdD, hd1, hdCL, hgen, -, -⟩ := f4_distinguished_L_cyclic_centralizer hH
  have hdCG : d ∉ Subgroup.centralizer (G₀ : Set X) := by
    intro hd
    apply hdCL
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro y hy
    exact hd y (FD.hL0G hy)
  have hbDker : (Subgroup.inclusion FD.hDB ⟨d, hdD⟩ : B₁) ∉
      (ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
        (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0).ker := by
    rw [hTheker, Subgroup.mem_subgroupOf]
    simpa using hdCG
  have hne : ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
      (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0
      (Subgroup.inclusion FD.hDB ⟨d, hdD⟩ : B₁) ≠ 1 :=
    fun h1 => hbDker (MonoidHom.mem_ker.mpr h1)
  have hcd : coord ⟨d, hdD⟩ ≠ 1 := by
    intro hc
    apply hne
    have h := hcoord ⟨d, hdD⟩
    rw [hc] at h
    simpa only [rootDiagUnit_one] using h
  have hTor : ∀ d0 : D, rootDiagUnit .F4 (coord d0) ∈
      (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0).torus := by
    intro d0
    unfold LangDatum.torus
    rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup (coord d0), ?_⟩
    have hfix : (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f)
        (iterateFrobenius (F4Omega f) 2 f) (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf)
        w hg0C hg0).step (rootDiagUnit .F4 (coord d0)) = rootDiagUnit .F4 (coord d0) := by
      rw [← hcoord d0]
      exact hstep (Subgroup.inclusion FD.hDB d0)
    simpa only [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] using hfix
  have hattach := f4_joint_attachment_actual (L := F4Omega f) ψ G₀ B₁ D FD.hG0 FD.hker
    (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner FD.hDB
    (iterateFrobenius (F4Omega f) 2 f) (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf)
    w hg0C hg0 FD.h17 hdD hgen coord hcoord FD.h15
  have : Finite (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f)
      (iterateFrobenius (F4Omega f) 2 f) (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf)
      w hg0C hg0).model := hFin
  have hsel := f4_component_le_jointOrbitRootSpan
    (langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0)
    (MulAction.toPerm w) hFrob (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)
    (hTor ⟨x, FD.h17⟩) (hTor ⟨d, hdD⟩)
    ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
      (center_adjointGroup_F4_galoisField f) g0)) hattach
  exact ⟨w, g0, hg0C, hg0, hFrob, hFin, htor, hstep, hTheker, d, hdD, coord,
    hd1, hdCL, hgen, hcoord, hexp, hcd, hattach, hsel⟩

end CFSG.StandardType.F4ExplicitPos.LiteralSetup

end

end
