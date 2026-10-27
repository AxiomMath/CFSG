module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSpSelfDual
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSpSelfDualTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSpDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSpFEPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSpFESelf

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckRPfsp_injective {X : Type} [Group X] {n f : ℕ}
    (φ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X)
    (hφk : φ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
    Function.Injective φ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro a b _
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> exact i.elim0
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hφk.trans (le_of_eq ?_)
    exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two
      (m := n) (F := GaloisField 2 f) hn

private theorem rckRPfsp_singleton {n f : ℕ} {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hsSp : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) (hsodd : Odd (orderOf s)) :
    (∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      a ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
    (∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ b ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute a b) ∧
    ∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Odd (orderOf a) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [Set.mem_singleton_iff.mp ha]
    exact hsSp
  · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  · rw [Set.mem_singleton_iff.mp ha]
    exact hsodd

private theorem rckRPfsp_flaggedModel
    {n f : ℕ} (hf : 1 ≤ f) {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hsSp : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hsplit : e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e ≠ e ∧
      ε = e + formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε,
        glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  obtain ⟨hSU, hS, hoddS⟩ := rckRPfsp_singleton hsSp hsodd
  rcases hsplit with rfl | ⟨-, hpair, rfl⟩
  · have hadj := hε.2.2.2.1
    rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_flaggedModel_PSp_selfDual n f hf {s} hS he hadj h1 hJ' hA6
    rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 4
      with h3 | h4
    · exact rckRP_flaggedModel_PSp_selfDualTwo n f {s} hSU hS hoddS he hadj h2 h3 hJ'
    · exact rckRP_flaggedModel_PSp_fieldExtSelf n f hf {s} hSU hS hoddS he hadj h4 hJ'
  · rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_flaggedModel_PSp_dualPair n f hf {s} hSU hS he hpair h1 hJ'
    · exact rckRP_flaggedModel_PSp_fieldExtPair n f hf {s} hSU hS hoddS he hpair h2 hJ'

theorem rckLemmaFAt_PSp
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFAt .PSp := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp hA6 _hRJ _hRmJ
    hroot
  rcases hmodel with ⟨n, f, φ, hf, hφr, hφk, hdiag⟩
  obtain ⟨s, hsSp, -, hsodd, ε, hε, ⟨e, he, -, hsplit⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSp hp hp2 (hBab.2 d hdB) hf φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hinj := rckRPfsp_injective φ hφk
  have hA6' : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) :=
    ⟨fun ψ => hA6.false
      (((Subgroup.equivMapOfInjective J' φ hinj).trans (MulEquiv.subgroupCongr hJ'map)).symm.trans
        ψ)⟩
  have hM := rckRPfsp_flaggedModel hf hsSp hsodd hε he hsplit hJ'comp hA6'
  obtain ⟨R', hR'map, hR'flag⟩ :=
    rckRP_glGeoFlag_of_flaggedModel hIRG _ φ hφk hJ'map hcomp.2.2 hroot hM
  exact ggRootPosFlag_of_glGeoFlag_PSp hf φ hφr hφk hR'map hR'flag

private theorem rckRPfsp_modelII
    {n f : ℕ} (hf : 1 ≤ f) {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hsSp : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hsplit : e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e ≠ e ∧
      ε = e + formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε,
        glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  obtain ⟨hSU, hS, hoddS⟩ := rckRPfsp_singleton hsSp hsodd
  rcases hsplit with rfl | ⟨-, hpair, rfl⟩
  · have hadj := hε.2.2.2.1
    rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_modelII_PSp_selfDual n f hf {s} hS he hadj h1 hJ' hA6
    rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 4
      with h3 | h4
    · exact rckRP_modelII_PSp_selfDualTwo n f hf {s} hSU hS hoddS he hadj h2 h3 hJ'
    · exact rckRP_modelII_of_big _
        (rckRP_modelBig_PSp_fieldExtSelf n f hf {s} hSU hS hoddS he hadj h4 hJ')
  · rcases lt_or_ge (blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_modelII_PSp_dualPair n f hf {s} hSU hS he hpair h1 hJ'
    · exact rckRP_modelII_of_big _
        (rckRP_modelBig_PSp_fieldExtPair n f hf {s} hSU hS hoddS he hpair h2 hJ')

theorem rckLemmaFIIAt_PSp
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFIIAt .PSp := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp _hrow hA6 _hRJ
    _hRmJ hroot hR2
  rcases hmodel with ⟨n, f, φ, hf, hφr, hφk, hdiag⟩
  obtain ⟨s, hsSp, -, hsodd, ε, hε, ⟨e, he, -, hsplit⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSp hp hp2 (hBab.2 d hdB) hf φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hinj := rckRPfsp_injective φ hφk
  have hA6' : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) :=
    ⟨fun ψ => hA6.false
      (((Subgroup.equivMapOfInjective J' φ hinj).trans (MulEquiv.subgroupCongr hJ'map)).symm.trans
        ψ)⟩
  have hM := rckRPfsp_modelII hf hsSp hsodd hε he hsplit hJ'comp hA6'
  obtain ⟨R', hR'map, hR'⟩ := rckRP_exists_of_modelII hIRG φ hφk hJ'map hcomp.2.2 hroot hR2 hM
  exact ggRootPosNbr_of_rootSubOf (t := .PSp) (by simp [GGPosTag]) (Or.inl rfl) hf φ hφr hφk
    hR'map hR'

end CFSG.StandardType.RCKRP
