module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedOmegaModel
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedOmegaInner
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.RankThree.PartOne.S12.AmbientTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Reduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Connected
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

theorem ggA6_transport_Omega
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (n f : ℕ) (X : Type) [Group X] [Finite X] (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ D J : Subgroup X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Φ : QuadForm F (ι → F))
        (P J' : Subgroup (GL ι F)), P ≤ orthGroup Φ.Q ∧ Odd (Nat.card P) ∧ Group.IsNilpotent ↥P ∧
        IsComponentOf J' (CFSG.Open.StatedOmega Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F))) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  intro hrange hker hLie hp hp2 hDN hdiag hab hcard hJ
  obtain ⟨hZ, P₀, hP₀le, hPp, hcent⟩ :=
    ggA6_omega_inner t ht n f X ψ p G₀ D hrange hker hLie hp hp2 hDN hdiag hab hcard
  have hJc : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (P₀ : Set X)) := hcent ▸ hJ
  have hJG : J ≤ G₀ := hJc.1.trans inf_le_left
  obtain ⟨F, hF, hFfin, hFchar, ι, hι, hιdec, Φ, ⟨e⟩⟩ :=
    ggA6_omega_model t ht n f ↥G₀ hZ hLie
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let S : Subgroup (GL ι F) := CFSG.Open.StatedOmega Φ.Q
  let P₀' : Subgroup ↥G₀ := P₀.subgroupOf G₀
  let J₀ : Subgroup ↥G₀ := J.subgroupOf G₀
  let K₀ : Subgroup ↥G₀ := (G₀ ⊓ Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀
  let φ : ↥G₀ →* GL ι F := S.subtype.comp (e : ↥G₀ →* ↥S)
  let P : Subgroup (GL ι F) := P₀'.map φ
  let J' : Subgroup (GL ι F) := J₀.map φ
  have hφ : Function.Injective φ := fun a b h => e.injective (S.subtype_injective h)
  have hJ0 : IsComponentOf (J.subgroupOf G₀)
      ((G₀ ⊓ Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀) := by
    have hmain : IsComponentOf ((J.subgroupOf G₀).map G₀.subtype)
        (((G₀ ⊓ Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀).map G₀.subtype) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le hJG, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := G₀.subtype)
      G₀.subtype_injective).1 hmain
  have hK₀ : K₀ = (Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀ := by
    show (G₀ ⊓ Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀ = _
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have h1 : K₀.map (e : ↥G₀ →* ↥S) =
      Subgroup.centralizer (P₀'.map (e : ↥G₀ →* ↥S)) := by
    rw [hK₀, ← CFSG.RankThree.PartOne.centralizer_subgroupOf_eq (S := P₀) (I := G₀) hP₀le]
    exact CFSG.LocalAnalysis.GLTheoremA.centralizer_map_mulEquiv (e : ↥G₀ ≃* ↥S) P₀'
  have hP_eq : (P₀'.map (e : ↥G₀ →* ↥S)).map S.subtype = P := by
    change _ = P₀'.map (S.subtype.comp (e : ↥G₀ →* ↥S))
    rw [Subgroup.map_map]
  have hKmap : ((G₀ ⊓ Subgroup.centralizer (P₀ : Set X)).subgroupOf G₀).map φ =
      S ⊓ Subgroup.centralizer (P : Set (GL ι F)) := by
    change K₀.map (S.subtype.comp (e : ↥G₀ →* ↥S)) = _
    rw [← Subgroup.map_map, h1,
      CFSG.LocalAnalysis.GLTheoremA.Y10F.map_centralizer_subtype, hP_eq]
  have hJ'c : IsComponentOf J' (S ⊓ Subgroup.centralizer (P : Set (GL ι F))) := by
    have hmap := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := φ) hφ).2 hJ0
    rw [hKmap] at hmap
    exact hmap
  have hPS : P ≤ S := by
    intro y hy
    rw [show P = P₀'.map φ from rfl, Subgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact (e x).2
  have hPorth : P ≤ orthGroup Φ.Q :=
    hPS.trans (CFSG.LieType.BorelTits.statedOmega_le_orthGroup Φ.Q)
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardP : Nat.card P = Nat.card P₀ := by
    show Nat.card (P₀'.map φ) = Nat.card P₀
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀le).toEquiv
  have hPpP : IsPGroup p ↥P := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := ↥P₀)).mp hPp
    exact (IsPGroup.iff_card (p := p) (G := ↥P)).mpr ⟨m, by rw [hcardP, hm]⟩
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := ↥P)).mp hPpP
    rw [hm]
    exact (Nat.Prime.odd_of_ne_two hp hp2).pow
  have hPnil : Group.IsNilpotent ↥P := hPpP.isNilpotent
  have hJJ' : ↥J ≃* ↥J' :=
    (Subgroup.subgroupOfEquivOfLe hJG).symm.trans
      (Subgroup.equivMapOfInjective J₀ φ hφ)
  refine ⟨F, hF, hFfin, hFchar, ι, hι, hιdec, Φ, P, J', hPorth, hPodd, hPnil, hJ'c, ?_⟩
  exact ⟨QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') hJJ'
    (Subgroup.map_center_eq hJJ')⟩

end CFSG.StandardType.A6Red

end
