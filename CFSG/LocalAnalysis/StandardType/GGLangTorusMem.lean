module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem torMem_units_map_pow {L : Type} [DivisionRing L] {q : ℕ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (c : Lˣ) : Units.map Fr.toMonoidHom c = c ^ q := by
  ext
  rw [Units.val_pow_eq_pow_val]
  exact hFr c

private theorem torMem_untwisted
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ}
    (h : ∀ γ, IsRoot τ γ → rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) :
    S.D.n * S.D.Φ (rootDiagUnit τ a) * S.D.n⁻¹ = rootDiagUnit τ a := by
  have hFr_unit : ∀ c : Lˣ, Units.map Fr.toMonoidHom c = c ^ S.D.q :=
    fun c => torMem_units_map_pow hFr c
  have hfixed : a ∈ twistedFixedTuples w Fr := by
    change weylTuple w (fun i => Units.map Fr.toMonoidHom (a i)) = a
    funext i
    have hu : IsRoot τ (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
      (isRoot_smul_iff w⁻¹).2 (IsRoot.basis i)
    have h1 := h _ hu
    rw [S.rho_eq_smul_of_frob hFr hΦ hn hu, smul_inv_smul, CTTorus.rootChar_single] at h1
    change rootChar (fun i => Units.map Fr.toMonoidHom (a i))
      (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) = a i
    rw [← map_rootChar, hFr_unit]
    exact h1.symm
  rw [hn, hΦ]
  exact (mem_twistedFixedTuples_iff_conj (τ := τ) (Fr := Fr) (w := w) (a := a)).1 hfixed

private theorem torMem_twisted
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ}
    (h : ∀ γ, IsRoot Tag.E6 γ → rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w) :
    S.D.n * S.D.Φ (rootDiagUnit Tag.E6 a) * S.D.n⁻¹ = rootDiagUnit Tag.E6 a := by
  have hq0 : 0 < S.D.q := Nat.pos_of_ne_zero fun h0 => by
    have h0' := hFr 0
    rw [map_zero, h0, pow_zero] at h0'
    exact zero_ne_one h0'
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem Tag.E6) L w) Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L w * (e6Diagram L *
        Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
    rw [hΦ, hn]
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice TwistTag.E6.cartan_perm) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hfix : weylTuple w (fun i => Units.map Fr.toMonoidHom (a (e6Graph.symm i))) = a := by
    funext i
    have huroot : IsRoot Tag.E6 (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      (isRoot_smul_iff w⁻¹).2 (IsRoot.basis i)
    have hxroot : IsRoot Tag.E6
        (permLattice e6Graph.symm (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) :=
      huroot.permLattice (cartan_perm_symm TwistTag.E6.cartan_perm)
    have h1 := h _ hxroot
    have hρx : S.ρ (permLattice e6Graph.symm
        (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = Pi.single i 1 := by
      rw [hρw _ hxroot, permLattice_permLattice_symm, smul_inv_smul]
    rw [hρx, CTTorus.rootChar_single] at h1
    change rootChar (fun k => Units.map Fr.toMonoidHom (a (e6Graph.symm k)))
      (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = a i
    rw [rootChar_map_tuple, ← rootChar_permLattice a e6Graph.symm
      (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)), torMem_units_map_pow hFr]
    exact h1.symm
  change S.D.step (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a
  rw [hst]
  exact (twFrob_rootDiagUnit (t := TwistTag.E6) (Fr := Fr) (v := w) (a := a)).trans
    (congrArg (rootDiagUnit Tag.E6) hfix)

theorem rootDiagUnit_mem_torus_of_rootChar
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : Fin τ.rank → Lˣ}
    (h : ∀ γ, IsRoot τ γ → rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q) :
    rootDiagUnit τ a ∈ S.D.torus := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have key : S.D.n * S.D.Φ (rootDiagUnit τ a) * S.D.n⁻¹ = rootDiagUnit τ a := by
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact torMem_untwisted S h hFr hΦ' hn
    · cases t with
      | D4 =>
        rw [← ht] at hτ
        rcases hτ with h | h | h | h <;> exact absurd h (by decide)
      | E6 =>
        have hτE6 : τ = .E6 := ht.symm
        subst hτE6
        have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g *
            (e6Diagram L)⁻¹ := hΦ
        exact torMem_twisted S h hFr hΦ' hn
  change rootDiagUnit τ a ∈ twistedTorusOf S.D.n S.D.Φ
  rw [mem_twistedTorusOf]
  exact ⟨rootDiagUnit_mem_torusGroup a, key⟩

end CFSG.StandardType.LangRat
