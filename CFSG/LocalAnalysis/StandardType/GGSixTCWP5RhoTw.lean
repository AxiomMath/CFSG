module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
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

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def tcRadE6 : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

theorem tcRadE6_cartan (i : Fin Tag.E6.rank) :
    (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * tcRadE6 j := by
  revert i
  decide +kernel

private theorem w5T_basis_decomp (v : Fin Tag.E6.rank → ℤ) :
    v = ∑ j, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  ext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private theorem w5T_smul_apply_sum (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ)
    (i : Fin Tag.E6.rank) :
    (w • v) i = ∑ j, v j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
  conv_lhs => rw [w5T_basis_decomp v]
  rw [Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_comm, Pi.smul_apply, smul_eq_mul]

private theorem w5T_smul_permLattice_apply_sum (w : WeylGroup Tag.E6)
    (π : Equiv.Perm (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    (w • permLattice π v) i = ∑ j, v j * (w • permLattice π (Pi.single j 1)) i := by
  have hv : permLattice π v = ∑ j, v j • permLattice π (Pi.single j 1) := by
    ext k
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single (π.symm k)]
    · rw [Pi.smul_apply, permLattice_single, Equiv.apply_symm_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one]
      rfl
    · intro j _ hj
      rw [Pi.smul_apply, permLattice_single, Pi.single_eq_of_ne ?_, smul_zero]
      intro h
      exact hj (by rw [h, Equiv.symm_apply_apply])
    · intro hk; exact absurd (Finset.mem_univ _) hk
  rw [hv, Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_comm, Pi.smul_apply, smul_eq_mul]

private theorem w5T_reflect_sub (i k : Fin Tag.E6.rank) {v : Fin Tag.E6.rank → ℤ}
    (hv : (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * v j) :
    (3 : ℤ) ∣ reflect Tag.E6 i v k - v k := by
  have h : reflect Tag.E6 i v k - v k =
      -(∑ j, Tag.E6.cartan i j * v j) *
        (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) k := by
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact dvd_mul_of_dvd_left (dvd_neg.mpr hv) _

private theorem w5T_radical_reflect (i : Fin Tag.E6.rank) {v : Fin Tag.E6.rank → ℤ}
    (hv : ∀ k, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan k j * v j) :
    ∀ k, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan k j * reflect Tag.E6 i v j := by
  have hsingle : ∀ k, ∑ j, Tag.E6.cartan k j *
        (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) j = Tag.E6.cartan k i := by
    intro k
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, mul_one]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  intro k
  have hc : (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * v j := hv i
  have hterm : ∀ j, Tag.E6.cartan k j * reflect Tag.E6 i v j =
      Tag.E6.cartan k j * v j -
        Tag.E6.cartan k j * ((∑ l, Tag.E6.cartan i l * v l) *
          (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) j) := by
    intro j
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_sub]
  have hexp : ∑ j, Tag.E6.cartan k j * reflect Tag.E6 i v j =
      (∑ j, Tag.E6.cartan k j * v j) -
        (∑ j, Tag.E6.cartan i j * v j) * Tag.E6.cartan k i := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
    congr 1
    have h2 : ∀ j, Tag.E6.cartan k j *
          ((∑ l, Tag.E6.cartan i l * v l) *
            (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) j) =
        (∑ l, Tag.E6.cartan i l * v l) *
          (Tag.E6.cartan k j * (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) j) := by
      intro j; ring
    rw [Finset.sum_congr rfl (fun j _ => h2 j), ← Finset.mul_sum, hsingle k]
  rw [hexp]
  exact dvd_sub (hv k) (dvd_mul_of_dvd_left hc _)

private theorem w5T_weyl_smul_rad (w : WeylGroup Tag.E6) :
    ∀ v : Fin Tag.E6.rank → ℤ, (∀ i, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * v j) →
      (∀ i, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * (w • v) j) ∧
      ∀ i, (3 : ℤ) ∣ (w • v) i - v i := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left with
  | one =>
      intro v hv
      exact ⟨by simpa using hv, fun i => by
        rw [one_smul, sub_self]; exact dvd_zero 3⟩
  | mul_simple_left w i₀ ih =>
      intro v hv
      obtain ⟨hrad, hcong⟩ := ih v hv
      constructor
      · intro k
        rw [mul_smul, simple_smul]
        exact w5T_radical_reflect i₀ hrad k
      · intro k
        rw [mul_smul, simple_smul]
        have h1 : (3 : ℤ) ∣ reflect Tag.E6 i₀ (w • v) k - (w • v) k :=
          w5T_reflect_sub i₀ k (hrad i₀)
        have h2 : (3 : ℤ) ∣ (w • v) k - v k := hcong k
        have heq : reflect Tag.E6 i₀ (w • v) k - v k =
            (reflect Tag.E6 i₀ (w • v) k - (w • v) k) + ((w • v) k - v k) := by ring
        rw [heq]
        exact dvd_add h1 h2

theorem weyl_smul_tcRadE6 (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank) :
    (3 : ℤ) ∣ (w • tcRadE6) i - tcRadE6 i :=
  (w5T_weyl_smul_rad w tcRadE6 tcRadE6_cartan).2 i

theorem permLattice_e6Graph_tcRadE6 (i : Fin Tag.E6.rank) :
    (3 : ℤ) ∣ permLattice e6Graph tcRadE6 i + tcRadE6 i := by
  revert i
  decide +kernel

private theorem w5T_rad_permLattice :
    ∀ i, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * permLattice e6Graph tcRadE6 j := by
  decide +kernel

section Radical

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem langSetup_rho_radical_twE6
    (S : LangSetup Tag.E6 L p) {w : WeylGroup Tag.E6}
    (hw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ) (i : Fin Tag.E6.rank) :
    (3 : ℤ) ∣ (∑ j, tcRadE6 j * S.ρ (Pi.single j 1) i) + tcRadE6 i := by
  have hsum : (∑ j, tcRadE6 j * S.ρ (Pi.single j 1) i) =
      (w • permLattice e6Graph tcRadE6) i := by
    rw [show (∑ j, tcRadE6 j * S.ρ (Pi.single j 1) i) =
        ∑ j, tcRadE6 j * (w • permLattice e6Graph (Pi.single j 1)) i from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw _ (IsRoot.basis j)]]
    rw [← w5T_smul_permLattice_apply_sum w e6Graph tcRadE6 i]
  have hA : (3 : ℤ) ∣ (w • permLattice e6Graph tcRadE6) i -
      permLattice e6Graph tcRadE6 i :=
    (w5T_weyl_smul_rad w (permLattice e6Graph tcRadE6) w5T_rad_permLattice).2 i
  have hB : (3 : ℤ) ∣ permLattice e6Graph tcRadE6 i + tcRadE6 i :=
    permLattice_e6Graph_tcRadE6 i
  rw [hsum]
  have heq : (w • permLattice e6Graph tcRadE6) i + tcRadE6 i =
      ((w • permLattice e6Graph tcRadE6) i - permLattice e6Graph tcRadE6 i) +
        (permLattice e6Graph tcRadE6 i + tcRadE6 i) := by ring
  rw [heq]
  exact dvd_add hA hB

theorem langSetup_rho_not_weyl_twE6
    (S : LangSetup Tag.E6 L p) {w : WeylGroup Tag.E6}
    (hw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ) :
    ¬ ∃ w' : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w' • γ := by
  rintro ⟨w', hw'⟩
  have hsum : (∑ j, tcRadE6 j * S.ρ (Pi.single j 1) 0) = (w' • tcRadE6) 0 := by
    rw [show (∑ j, tcRadE6 j * S.ρ (Pi.single j 1) 0) =
        ∑ j, tcRadE6 j * (w' • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw' _ (IsRoot.basis j)]]
    rw [← w5T_smul_apply_sum w' tcRadE6 0]
  have hrad := langSetup_rho_radical_twE6 S hw 0
  rw [hsum] at hrad
  have hfix := weyl_smul_tcRadE6 w' 0
  have h2 : (3 : ℤ) ∣ 2 * tcRadE6 0 := by
    have heq : 2 * tcRadE6 0 =
        ((w' • tcRadE6) 0 + tcRadE6 0) - ((w' • tcRadE6) 0 - tcRadE6 0) := by ring
    rw [heq]
    exact dvd_sub hrad hfix
  have h0 : tcRadE6 0 = 1 := by decide +kernel
  rw [h0, mul_one] at h2
  norm_num at h2

end Radical

end CFSG.StandardType.TableCRes

end
