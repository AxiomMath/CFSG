module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDetSurj
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggDet_overGamma {G : Type} [Group G] [Finite G] {p : ℕ} (hP : p.Prime)
    {Bs K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hc : ∀ a b : ↥Bs, a * b = b * a) (hp : ∀ a : ↥Bs, a ^ p = 1)
    (hcA : ∀ a b : ↥(ggGamma K hN).range, a * b = b * a)
    (hpA : ∀ a : ↥(ggGamma K hN).range, a ^ p = 1) {c : MulAut ↥Bs}
    {a : MulAut ↥(ggGamma K hN).range} (hca : GGOverGamma hN c a)
    (hfix : ∀ v ∈ (ggGamma K hN).rangeRestrict.ker, c v = v) :
    ggDetAut p hP hc hp c = ggDetAut p hP hcA hpA a :=
  ggDetAut_of_surjective p hP hc hp hcA hpA (ggGamma K hN).rangeRestrict_surjective hca hfix

@[expose] def GGTorusDetElt (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ ∃ (hP : p.Prime) (hc : ∀ a b : ↥A, a * b = b * a)
      (hp : ∀ a : ↥A, a ^ p = 1), ((ggDetAut p hP hc hp (ggConjAut A hn) : (ZMod p)ˣ)) ^ 2 ≠ 1

@[expose] def GGDetAt (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusDetElt p A

theorem ggNbr_exists_detElt {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (K ⧸ Subgroup.center K)) (hF : GGDetAt p lab) :
    ∃ c ∈ ggAutomizer K Bs, ∃ (hP : p.Prime) (hc : ∀ a b : ↥Bs, a * b = b * a)
      (hp : ∀ a : ↥Bs, a ^ p = 1), ((ggDetAut p hP hc hp c : (ZMod p)ˣ)) ^ 2 ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, _, hBsI, ⟨r, hl, hfr⟩⟩ :=
    exists_datum_of_label hRig hInnK hlab hhas hF hN
  obtain ⟨hP, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hInnK.1 θ hN hBsI hl
  obtain ⟨n, hn, hW, hPA, hcA, hpA, hdet⟩ := hfr K (ggQuotHom θ) (ggGamma K hN).range hTB
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hN hSC hW
  have hov : GGOverGamma hN (ggConjAut Bs hnN) (ggConjAut (ggGamma K hN).range hn) := by
    have h := ggOverGamma_conjAut (hN := hN) n.2 hnN
    have heq : ggConjAut (ggGamma K hN).range
          (conj_mem_normalizer_range_ggGamma hN n.2 hnN)
        = ggConjAut (ggGamma K hN).range hn :=
      MulEquiv.ext fun b => Subtype.ext rfl
    rwa [heq] at h
  have hc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hp : ∀ a : ↥Bs, a ^ p = 1 := fun a => Subtype.ext (hBs.2 a a.2)
  have hfix : ∀ v ∈ (ggGamma K hN).rangeRestrict.ker, ggConjAut Bs hnN v = v := by
    intro v hv
    have h1 : ggGamma K hN v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hv)
    have h2 := Subgroup.mem_centralizer_iff.mp ((ggGamma_eq_one_iff K hN v).mp h1) n n.2
    refine Subtype.ext ?_
    rw [ggConjAut_apply, h2]
    group
  refine ⟨ggConjAut Bs hnN, ggConjAut_mem_ggAutomizer n.2 hnN, hP, hc, hp, ?_⟩
  rw [ggDet_overGamma hP hN hc hp hcA hpA hov hfix]
  exact hdet

end CFSG.StandardType

end
