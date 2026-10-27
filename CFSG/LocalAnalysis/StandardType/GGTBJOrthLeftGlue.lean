module

public import CFSG.LocalAnalysis.StandardType.GGTBJOrthSide
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigUnpack
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormB
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAmbientBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
import CFSG.RankThree.PartOne.KC.OrthogonalDeletionCoordinates
import CFSG.LocalAnalysis.StandardType.GGTBJOmSupportCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG CFSG.Assembly SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Type} [Group R]
  {eR : R ≃* ↥(orthDerived Q)} {r : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {Δ : TBJOmData Q p E r}
  {hE : E ≤ orthDerived Q}

theorem ggTBJOrthLeft_nf_of_cfg_with_fixed_centralizer (hcfg : GGConfig p B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    (hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma L hBsN).range : Set (MulAut ↥L)) → GGTorusWeylElt p (ggGamma L hBsN).range n)
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) (hr : 4 ≤ r) :
    (GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨y, hy, hy1, hJ, hcountA⟩ := ggTBJ_config_unpack hcfg hBsN
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  exact ggTBJOrth_nf_sideDatum_with_fixed_centralizer hp2 hBs hSC hBsN hQ hT hψsurj hker
    (ggTBJ_noPElt_center_of_not_dvd hZc) hψσ hΘA hWeyl hnf hr hy hy1 hJL hJ hcountA
    hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthLeft_nf_of_cfg (hcfg : GGConfig p B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    (hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma L hBsN).range : Set (MulAut ↥L)) → GGTorusWeylElt p (ggGamma L hBsN).range n)
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) (hr : 4 ≤ r) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  exact (ggTBJOrthLeft_nf_of_cfg_with_fixed_centralizer hcfg hBsN hQ hT hψsurj hker hZc hψσ hΘA
    hWeyl hnf hr).1

theorem ggTBJOrthLeft_fixed_of_cfg_with_fixed_centralizer (hcfg : GGConfig p B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    (hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma L hBsN).range : Set (MulAut ↥L)) → GGTorusWeylElt p (ggGamma L hBsN).range n)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 2 ≤ r) :
    (GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨y, hy, hy1, hJ, hcountA⟩ := ggTBJ_config_unpack hcfg hBsN
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  exact ggTBJOrth_fixed_sideDatum_with_fixed_centralizer hp2 hBs hSC hBsN hQ hT hψsurj hker
    (ggTBJ_noPElt_center_of_not_dvd hZc) hψσ hΘA hWeyl hW hr hy hy1 hJL hJ hcountA
    hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthLeft_fixed_of_cfg (hcfg : GGConfig p B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    (hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma L hBsN).range : Set (MulAut ↥L)) → GGTorusWeylElt p (ggGamma L hBsN).range n)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 2 ≤ r) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  exact (ggTBJOrthLeft_fixed_of_cfg_with_fixed_centralizer hcfg hBsN hQ hT hψsurj hker hZc hψσ hΘA
    hWeyl hW hr).1

theorem ggTBJOrthLeft_sparse_frame_data
    {NbrK : Subgroup G} {y : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J y NbrK)
    (hBsB : Bs = B)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    {Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) ≃* ↥Bs}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥L) : G) * c)
    {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {j : Fin n} (hj : j ≠ i0)
    (hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1)
    (hyoff : ∀ k, k ≠ i0 → k ≠ j →
      eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ k = 1) :
    let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
    let yA : ↥(ggGamma L hBsN).range :=
      ⟨ggGamma L hBsN yb, ⟨yb, rfl⟩⟩
    ∃ a : Fin r,
      (Θ.symm yb).1 a ≠ 1 ∧
      (∀ b, b ≠ a → (Θ.symm yb).1 b = 1) ∧
      ΘA.symm yA = (Θ.symm yb).1 ∧
      CFSG.Open.IsComponentOf (J.subgroupOf L)
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (ggGamma L hBsN yb)) ∧
      p ^ (r - 1) * Nat.card ↥((ggGamma L hBsN).range ⊓
        ⨅ z : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (z : ↥L)) =
        Nat.card ↥(ggGamma L hBsN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
  have hyj' : eta yb j ≠ 1 := hyj
  have hyoff' : ∀ k, k ≠ i0 → k ≠ j → eta yb k = 1 := hyoff
  obtain ⟨a, ha_ne, ha_off⟩ :=
    exists_one_active_of_bCoordinateBlock_eq hp hp2 hn Θ eta hcoord yb hj hyj' hyoff'
  have hJ_comp : CFSG.Open.IsComponentOf (J.subgroupOf L)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (ggGamma L hBsN yb)) := by
    have hfixEq : ggFix (ggGamma L hBsN yb) =
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (ggGamma L hBsN yb) :=
      Subgroup.ext fun _ => Iff.rfl
    have h1 := CFSG.Assembly.isComponentOf_iff_open.mp
      (isComponentOf_subgroupOf_ggFix_ggGamma_y hcfg hnb hBsN yb.2)
    rwa [hfixEq] at h1
  let yA : ↥(ggGamma L hBsN).range :=
    ⟨ggGamma L hBsN yb, ⟨yb, rfl⟩⟩
  have hactor : ΘA.symm yA = (Θ.symm yb).1 :=
    FrameBs.ggGamma_liftBs_symm hBsN σ ΘA hΘA Θ hΘ yb
  have hfixJ : (ggGamma L hBsN).range ⊓
      ⨅ z : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (z : ↥L) =
      ggFixingJ L J (ggGamma L hBsN).range :=
    iInf_stabilizer_subgroupOf_eq_ggFixingJ (X := L) (J := J)
      (A := (ggGamma L hBsN).range)
  have hcountJ : Nat.card ↥(ggFixingJ L J (ggGamma L hBsN).range) = p :=
    ggTBJ_card_fixingJ_eq_of_bstar_eq hcfg hBsB hBsN
  have hcardA : Nat.card ↥(ggGamma L hBsN).range = p ^ r := by
    rw [← Nat.card_congr ΘA.toEquiv]
    exact FrameBs.card_zmodFrame p r
  have hcount : p ^ (r - 1) * Nat.card ↥((ggGamma L hBsN).range ⊓
      ⨅ z : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (z : ↥L)) =
      Nat.card ↥(ggGamma L hBsN).range := by
    have hr1 : 1 ≤ r := Fin.pos a
    rw [hfixJ, hcountJ, hcardA]
    calc p ^ (r - 1) * p = p ^ (r - 1 + 1) := (pow_succ p (r - 1)).symm
      _ = p ^ r := by rw [Nat.sub_add_cancel hr1]
  exact ⟨a, ha_ne, ha_off, hactor, hJ_comp, hcount⟩

theorem ggTBJOrthLeft_component_eq_supportedFixedDerived_of_sparse
    {NbrK : Subgroup G} {y : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J y NbrK)
    (hBsB : Bs = B)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    {Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) ≃* ↥Bs}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥L) : G) * c)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v)
    {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {j : Fin n} (hj : j ≠ i0)
    (hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1)
    (hyoff : ∀ k, k ≠ i0 → k ≠ j →
      eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ k = 1)
    (hr : 3 ≤ r) :
    let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
    let f0 : Fin r → Multiplicative (ZMod p) := (Θ.symm yb).1
    ∃ a : Fin r,
      f0 a ≠ 1 ∧
      (∀ b, b ≠ a → f0 b = 1) ∧
      (((J.subgroupOf L).map ψ₀).map eR.toMonoidHom) =
        (CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q
          (Δ.τ f0)).subgroupOf (orthDerived Q) ∧
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (Δ.τ f0) =
        CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (Δ.F.U a) ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (Δ.τ f0)) =
        Module.finrank K V - 2 := by
  classical
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
  let f0 : Fin r → Multiplicative (ZMod p) := (Θ.symm yb).1
  obtain ⟨a, ha_ne, ha_off, hactor, hJ_comp, hcountEq⟩ :=
    ggTBJOrthLeft_sparse_frame_data (hcfg := hcfg) (hnb := hnb) (hBsB := hBsB)
      (hBsN := hBsN) (σ := σ) (ΘA := ΘA) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ)
      (hn := hn) (eta := eta) (i0 := i0) (hcoord := hcoord) (j := j)
      (hj := hj) (hyj := hyj) (hyoff := hyoff)
  let yA : ↥(ggGamma L hBsN).range :=
    ⟨ggGamma L hBsN yb, ⟨yb, rfl⟩⟩
  have hjA : (ΘA.symm yA) a ≠ 1 := by
    rw [hactor]
    exact ha_ne
  have hfA : ∀ b, b ≠ a → (ΘA.symm yA) b = 1 := by
    intro b hb
    rw [hactor]
    exact ha_off b hb
  have hgeom := ggTBJ_om_component_eq_supportedFixedDerived_one_active
    (L' := ↥L) (A := (ggGamma L hBsN).range) (Θ := ΘA)
    (Δ := Δ) (hE := hE) (eR := eR)
    hp2 hQ hψsurj hker hψσ hΘA hW hr
    (y := (yA : MulAut ↥L)) yA.2 (J := J.subgroupOf L) hJ_comp
    (j := a) hjA hfA hcountEq.le
  refine ⟨a, ha_ne, ha_off, ?_, ?_, ?_⟩
  · have hgeom' := hgeom
    rw [show (⟨(yA : MulAut ↥L), yA.2⟩ : ↥(ggGamma L hBsN).range) = yA from rfl,
      hactor] at hgeom'
    exact hgeom'
  · exact Δ.fixedSpace_eq_polarPerp_one_active ha_ne ha_off
  · exact Δ.finrank_fixedSpace_one_active hQ ha_ne ha_off

theorem ggTBJOrthLeft_component_map_eq_of_sparse
    {NbrK : Subgroup G} {y : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J y NbrK)
    (hBsB : Bs = B)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {ψ₀ : ↥L →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥L)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥L}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ f))
    {Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) ≃* ↥Bs}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥L) : G) * c)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v)
    {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {j : Fin n} (hj : j ≠ i0)
    (hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1)
    (hyoff : ∀ k, k ≠ i0 → k ≠ j →
      eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ k = 1)
    (hr : 3 ≤ r)
    {κ : ↥(orthDerived Q) →* G}
    (hJmap : (((J.subgroupOf L).map ψ₀).map eR.toMonoidHom).map κ = J) :
    let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
    let f0 : Fin r → Multiplicative (ZMod p) := (Θ.symm yb).1
    ∃ a : Fin r,
      f0 a ≠ 1 ∧
      (∀ b, b ≠ a → f0 b = 1) ∧
      ((CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (Δ.τ f0)).subgroupOf
        (orthDerived Q)).map κ = J := by
  let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
  let f0 : Fin r → Multiplicative (ZMod p) := (Θ.symm yb).1
  obtain ⟨a, ha_ne, ha_off, hgeom, -, -⟩ :=
    ggTBJOrthLeft_component_eq_supportedFixedDerived_of_sparse (hcfg := hcfg) (hnb := hnb)
      (hBsB := hBsB) (hBsN := hBsN) (hQ := hQ) (hψsurj := hψsurj) (hker := hker)
      (σ := σ) (ΘA := ΘA) (hψσ := hψσ) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ) (hW := hW)
      (hn := hn) (eta := eta) (i0 := i0) (hcoord := hcoord) (hj := hj) (hyj := hyj)
      (hyoff := hyoff) (hr := hr)
  refine ⟨a, ha_ne, ha_off, ?_⟩
  rw [← hgeom]
  exact hJmap

section OriginalLMarkedDeletionChart

variable {b c : K}

open Module QuadraticMap
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

local notation "I" => Fin (r + 1)
local notation "C" S => CFSG.RankThree.PartOne.KCOrthogonal.chartSubgroup (n := r + 2) (F := K) (b := b) (c := c) S
local notation "D0" => Finset.univ.erase (0 : I)

theorem ggTBJOrthLeft_exists_markedDeletionChart_of_sparse
    {NbrK : Subgroup G} {y : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J y NbrK)
    (hBsB : Bs = B)
    (hr : 3 ≤ r)
    (Δ : TBJOmData Q p E r)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hE : E ≤ orthDerived Q)
    (hdim : Module.finrank K V = 2 * (r + 1))
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hsplit : p ∣ Nat.card K - 1)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥L)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range)
    (hψσ : ∀ w, ggQuotHom θ (σ w) = eR.symm (Δ.τΩ hE w))
    (hΘA : ∀ w, ((ΘA w : ↥(ggGamma L hBsN).range) : MulAut ↥L) = MulAut.conj (σ w))
    (Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w u, ((Θ (w, u) : ↥Bs) : G) = ((σ w : ↥L) : G) * (u : G))
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ g ∈ E, g v = v)
    (κ : ↥(orthDerived Q) →* G)
    (hκτ : ∀ w, κ (Δ.τΩ hE w) = (σ w : G))
    (hκinj : Function.Injective κ) (hκrange : κ.range = L)
    (hJmap : (((J.subgroupOf L).map (ggQuotHom θ)).map eR.toMonoidHom).map κ = J)
    (eta : ↥Bs ≃* (I → Multiplicative (ZMod p))) (i0 j : I)
    (hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 1) p i0)
    (hj : j ≠ i0)
    (hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1)
    (hyoff : ∀ k, k ≠ i0 → k ≠ j →
      eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ k = 1) :
    ∃ (eL : ↥(orthDerived Q) ≃* ↥(C D0))
      (a : ↥(C D0) →* G) (ell : Equiv.Perm I),
      Function.Injective a ∧ a.range = L ∧ a.comp eL.toMonoidHom = κ ∧ ell 0 = i0 ∧
      (∀ (z : ↥Bs) (t : Fin r),
        (Θ.symm z).1 t = 1 ↔ eta z (ell t.succ) = 1) ∧
      (∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
        ((C S).subgroupOf (C D0)).map a =
          ggBlockComm Bs eta (ell '' (S : Set I))) ∧
      ((C (D0 ∩ Finset.univ.erase (ell.symm j))).subgroupOf (C D0)).map a = J := by
  classical
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hxBs, hxC⟩
  have hLC : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  let yb : ↥Bs := ⟨y, hcfg.2.1.1 hnb.1.2.1⟩
  let f0 : Fin r → Multiplicative (ZMod p) := (Θ.symm yb).1
  have hyj' : eta yb j ≠ 1 := hyj
  have hyoff' : ∀ k, k ≠ i0 → k ≠ j → eta yb k = 1 := hyoff
  have hΘκ : ∀ w u, ((Θ (w, u) : ↥Bs) : G) = κ (Δ.τΩ hE w) * (u : G) := by
    intro w u
    rw [hΘ w u, ← hκτ w]
  obtain ⟨ι, hι, hsmallDonor⟩ :=
    ggTBJOm_smallBlocks_eq_ggBlockComm (n := r + 1) (X := L) (z := x)
      hp2 (by omega : 4 ≤ r + 1) rfl Δ hQ hE hdim hminus (Or.inl hsplit)
      κ hκinj hκrange Θ hΘκ eta i0 hcoord hx (Or.inl hLC)
  let o : Fin r := ⟨0, by omega⟩
  obtain ⟨eL, hcan⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.CoordinateDeletion.exists_originalDeletion_chartSubgroup
      (F := K) (V := V) (A := E) (Q := Q) (r := r)
      hp2 Δ hQ hE (by omega : 1 ≤ r) hdim hminus hsplit b c hirr o
  let a : ↥(C D0) →* G := κ.comp eL.symm.toMonoidHom
  have hainj : Function.Injective a := hκinj.comp eL.symm.injective
  have hfac : a.comp eL.toMonoidHom = κ := by
    ext z
    exact congrArg κ (eL.symm_apply_apply z)
  have harange : a.range = L := by
    rw [show a = κ.comp eL.symm.toMonoidHom from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr eL.symm.surjective, Subgroup.map_top]
    exact hκrange
  have hthrough : ∀ T : Finset (Fin r),
      ((C (T.image Fin.succ)).subgroupOf (C D0)).map a =
        ((supportedDerived Q (Δ.originalAnchor ⊔ T.sup Δ.F.U)).subgroupOf
          (orthDerived Q)).map κ := by
    intro T
    have h := congrArg (Subgroup.map a) (hcan T)
    rw [Subgroup.map_map, hfac] at h
    exact h.symm
  have hcomp := ggTBJOrthLeft_component_map_eq_of_sparse
    (hcfg := hcfg) (hnb := hnb) (hBsB := hBsB) (hBsN := hBsN) (hQ := hQ)
    (ψ₀ := ggQuotHom θ) (hψsurj := ggQuotHom_surjective θ)
    (hker := (ker_ggQuotHom θ).le) (σ := σ) (ΘA := ΘA)
    (hψσ := hψσ) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ) (hW := hW)
    (hn := by omega) (eta := eta) (i0 := i0) (hcoord := hcoord) (j := j)
    (hj := hj) (hyj := hyj) (hyoff := hyoff) (hr := hr)
    (κ := κ) (hJmap := hJmap)
  obtain ⟨a0, ha0, hoff, hJ⟩ := hcomp
  have ha0' : f0 a0 ≠ 1 := ha0
  have hoff' : ∀ t, t ≠ a0 → f0 t = 1 := hoff
  have hJ' : ((supportedFixedDerived Q (Δ.τ f0)).subgroupOf (orthDerived Q)).map κ = J := hJ
  have hJset : (Finset.univ.erase a0).image Fin.succ =
      D0 ∩ Finset.univ.erase a0.succ := by
    ext k
    constructor
    · intro hk
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
      have htne : t ≠ a0 := (Finset.mem_erase.mp ht).1
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨Fin.succ_ne_zero t, fun h => htne (Fin.succ_inj.mp h)⟩
    · intro hk
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, true_and, and_true] at hk
      obtain ⟨hk0, hka⟩ := hk
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨t, rfl⟩
      · exact absurd rfl hk0
      · refine Finset.mem_image.mpr ⟨t, ?_, rfl⟩
        simp only [Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        intro hta
        exact hka (by rw [hta])
  let f : I → I := Fin.cases i0 (fun t : Fin r => (ι t).val)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · rfl
      · exfalso
        exact (ι y').property (by simpa [f] using hxy.symm)
    · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · exfalso
        exact (ι x').property (by simpa [f] using hxy)
      · have h : (ι x').val = (ι y').val := by simpa [f] using hxy
        have h' : ι x' = ι y' := Subtype.ext h
        rw [ι.injective h']
  have hf_surj : Function.Surjective f := by
    intro k
    by_cases hk : k = i0
    · refine ⟨0, ?_⟩
      simp [f, hk]
    · obtain ⟨t, ht⟩ := ι.surjective ⟨k, hk⟩
      refine ⟨t.succ, ?_⟩
      simp [f, ht]
  let ell : Equiv.Perm I := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hell0 : ell 0 = i0 := by
    change f 0 = i0
    simp [f]
  have hellsucc : ∀ t : Fin r, ell t.succ = (ι t).val := by
    intro t
    change f t.succ = (ι t).val
    simp [f]
  have hdict : ∀ (z : ↥Bs) (t : Fin r),
      (Θ.symm z).1 t = 1 ↔ eta z (ell t.succ) = 1 := by
    intro z t
    rw [hellsucc t]
    exact hι z t
  have hιa0_ne : eta yb (ι a0).val ≠ 1 := by
    intro h
    exact ha0' ((hι yb a0).mpr h)
  have hιa0_eq_j : (ι a0).val = j := by
    by_contra hne
    exact hιa0_ne (hyoff' (ι a0).val (ι a0).property hne)
  have hell_a0 : ell a0.succ = j := by
    rw [hellsucc a0, hιa0_eq_j]
  have hellsynmj : ell.symm j = a0.succ := by
    rw [← hell_a0, Equiv.symm_apply_apply]
  have hsmall : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a =
        ggBlockComm Bs eta (ell '' (S : Set I)) := by
    intro S hSne hScard hSD
    let T : Finset (Fin r) := Finset.univ.filter (fun t => t.succ ∈ S)
    have hTimage : T.image Fin.succ = S := by
      ext k
      constructor
      · intro hk
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
        exact (Finset.mem_filter.mp ht).2
      · intro hk
        have hk0 : k ≠ 0 := by
          have hkD : k ∈ D0 := hSD hk
          simpa using hkD
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨t, rfl⟩
        · exact absurd rfl hk0
        · exact Finset.mem_image.mpr
            ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
    have hTne : T.Nonempty := by
      obtain ⟨k, hk⟩ := hSne
      have hk' : k ∈ T.image Fin.succ := by
        rw [hTimage]
        exact hk
      obtain ⟨t, ht, -⟩ := Finset.mem_image.mp hk'
      exact ⟨t, ht⟩
    have hTcard : T.card ≤ 2 := by
      have hc : (T.image Fin.succ).card = T.card :=
        Finset.card_image_of_injective T (Fin.succ_injective r)
      rw [hTimage] at hc
      omega
    have hlabels : ((fun t : Fin r => (ι t).val) '' (T : Set (Fin r))) =
        ell '' (S : Set I) := by
      ext k
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t.succ, ?_, ?_⟩
        · have hmem : t.succ ∈ T.image Fin.succ := Finset.mem_image_of_mem _ ht
          rwa [hTimage] at hmem
        · rw [hellsucc t]
      · rintro ⟨s, hs, rfl⟩
        have hs' : s ∈ T.image Fin.succ := by
          rw [hTimage]
          exact hs
        obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs'
        refine ⟨t, ht, ?_⟩
        rw [← hts, hellsucc t]
    have hTthrough := hthrough T
    rw [hTimage] at hTthrough
    have hTsmall := hsmallDonor T hTne hTcard
    rw [hTthrough, hTsmall, hlabels]
  have hthroughT0 := hthrough (Finset.univ.erase a0)
  have hJthrough :
      ((supportedDerived Q (Δ.originalAnchor ⊔
        (Finset.univ.erase a0).sup Δ.F.U)).subgroupOf (orthDerived Q)).map κ = J := by
    have hWS : IsCompl Δ.originalAnchor Δ.originalActive :=
      Δ.originalMinusAnchor_isCompl hp2 hQ hE (by omega : 1 ≤ r) hdim hminus (Or.inl hsplit)
    have hT0compl : (Finset.univ.erase a0)ᶜ = ({a0} : Finset (Fin r)) := by
      rw [Finset.compl_erase, Finset.compl_univ, Finset.insert_empty]
    have hsup : Δ.originalAnchor ⊔ (Finset.univ.erase a0).sup Δ.F.U =
        polarPerp Q (Δ.F.U a0) := by
      rw [← Δ.polarPerp_compl_sup_eq_originalAnchor_sup hQ o hWS (Finset.univ.erase a0),
        hT0compl, Finset.sup_singleton]
    have hfix : fixedSpace (Δ.τ f0) = polarPerp Q (Δ.F.U a0) :=
      Δ.fixedSpace_eq_polarPerp_one_active ha0' hoff'
    have hsupp : supportedDerived Q (Δ.originalAnchor ⊔
        (Finset.univ.erase a0).sup Δ.F.U) = supportedFixedDerived Q (Δ.τ f0) := by
      rw [hsup, ← hfix]
      exact (Δ.oddOrderIsometry hp2 hQ hE f0).supportedDerived_fixedSpace
    rw [hsupp]
    exact hJ'
  have hJleft :
      ((C ((Finset.univ.erase a0).image Fin.succ)).subgroupOf (C D0)).map a = J :=
    hthroughT0.trans hJthrough
  have hJfinal :
      ((C (D0 ∩ Finset.univ.erase (ell.symm j))).subgroupOf (C D0)).map a = J := by
    rw [hellsynmj, ← hJset]
    exact hJleft
  exact ⟨eL, a, ell, hainj, harange, hfac, hell0, hdict, hsmall, hJfinal⟩

end OriginalLMarkedDeletionChart

end OrthTorus

end CFSG.StandardType

end
