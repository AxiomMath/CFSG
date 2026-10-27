module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.Quasithin.Background.G1Basic

public section

namespace CFSG.StandardType.S2MathAs51600

open CFSG CFSG.Assembly

@[expose] def CentralFixedComponentTransfer : Prop :=
  ∀ {X Y : Type} [Group X] [Group Y] (pi : X →* Y),
    Function.Surjective pi → pi.ker ≤ Subgroup.center X →
      ∀ (sigma : MulAut X) (beta : MulAut Y), (∀ x, pi (sigma x) = beta (pi x)) →
        ∀ J : Subgroup X,
          Assembly.IsComponentOf J (ggAutFixedSubgroup sigma) →
            Assembly.IsComponentOf (J.map pi) (ggAutFixedSubgroup beta) ∧
              Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
                (↥(J.map pi) ⧸ Subgroup.center ↥(J.map pi)))

@[expose] def TypeALabel (lab : LargeEvenLabel) : Prop := lab.tag = .A ∨ lab.tag = .twA

@[expose] def RAComponentLabel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (sigma : MulAut X) (J : Subgroup X),
    Assembly.IsElemAbelian 3 A → sigma ∈ A →
      Assembly.IsComponentOf J (ggAutFixedSubgroup sigma) →
        LargeEvenMarking X (fun lab _ _ I _ theta => GGKacRA lab 3 ∧ GGInducedInn A theta I) →
          ∃ labC : LargeEvenLabel, LargeEvenInLambda2 labC ∧ TypeALabel labC ∧
            GGHasLabel labC (↥J ⧸ Subgroup.center ↥J)

@[expose] def NoD4On (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (sigma : MulAut X) (J : Subgroup X),
    Assembly.IsElemAbelian 3 A → sigma ∈ A →
      Assembly.IsComponentOf J (ggAutFixedSubgroup sigma) →
        LargeEvenMarking X (fun lab _ _ I _ theta => S lab ∧ GGInducedInn A theta I) →
          ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ → labJ.tag = .D → labJ.rank = 4 →
            GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → False

theorem innerOnD4_of_noD4 {S : LargeEvenLabel → Prop} (h : NoD4On S) : GGInnerOnD4On S := by
  intro X _ _ A sigma J hA hsigma hJ _hN hmark labJ hΛ htag hrk hlab a ha
  exact (h X A sigma J hA hsigma hJ hmark labJ hΛ htag hrk hlab).elim

private theorem not_ggLabelIso_of_d4_typeA {labJ labC : LargeEvenLabel}
    (htagJ : labJ.tag = .D) (hrkJ : labJ.rank = 4) (hTypeA : TypeALabel labC) :
    ¬ GGLabelIso labJ labC := by
  intro hIso
  unfold TypeALabel at hTypeA
  unfold GGLabelIso at hIso
  rcases hIso with heq | hBC | hD3 | hA3 | htwD3 | htwA3 | htwD2 | hA1
  ·
    rw [← heq] at hTypeA
    rcases hTypeA with hA | hA <;> rw [htagJ] at hA <;> cases hA
  ·
    obtain ⟨hBC, -⟩ := hBC
    rcases hBC with hB | hC
    · rw [htagJ] at hB; cases hB
    · rw [htagJ] at hC; cases hC
  ·
    obtain ⟨h1, -⟩ := hD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  ·
    obtain ⟨h1, -⟩ := hA3
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  ·
    obtain ⟨h1, -⟩ := htwD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  ·
    obtain ⟨h1, -⟩ := htwA3
    have hA : labJ.tag = .twA := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  ·
    obtain ⟨h1, -⟩ := htwD2
    have h2 : labJ.rank = 2 := congrArg LargeEvenLabel.rank h1
    omega
  ·
    obtain ⟨-, h1⟩ := hA1
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA

theorem raNoD4_of_componentLabel (hRig : GGLabelRigidInput) (h : RAComponentLabel) :
    NoD4On (fun lab => GGKacRA lab 3) := by
  intro X _ _ A sigma J hA hsigma hJ hmark labJ hΛJ htagJ hrkJ hlabJ
  obtain ⟨labC, hΛC, hTypeA, hlabC⟩ := h X A sigma J hA hsigma hJ hmark
  exact not_ggLabelIso_of_d4_typeA htagJ hrkJ hTypeA
    (hRig labJ labC (↥J ⧸ Subgroup.center ↥J) hΛJ hΛC hlabJ hlabC)

theorem raInner_of_componentLabel (hRig : GGLabelRigidInput) (h : RAComponentLabel) :
    GGInnerOnD4On (fun lab => GGKacRA lab 3) :=
  innerOnD4_of_noD4 (raNoD4_of_componentLabel hRig h)

theorem centralFixedImageNormal_holds :
    ∀ {X Y : Type} [Group X] [Group Y] (pi : X →* Y),
      Function.Surjective pi → pi.ker ≤ Subgroup.center X →
        ∀ (sigma : MulAut X) (beta : MulAut Y), (∀ x, pi (sigma x) = beta (pi x)) →
          ((ggAutFixedSubgroup sigma).map pi ≤ ggAutFixedSubgroup beta) ∧
            (((ggAutFixedSubgroup sigma).map pi).subgroupOf (ggAutFixedSubgroup beta)).Normal := by
  intro X Y _ _ pi hpi hker sigma beta hcomm
  constructor
  · rintro y ⟨x, hx, rfl⟩
    change sigma x = x at hx
    change beta (pi x) = pi x
    rw [← hcomm x, hx]
  · constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz⟩ := hpi (g : Y)
    have hgfix : beta (g : Y) = (g : Y) := g.2
    have hzfix : pi (sigma z) = pi z := by
      rw [hcomm z, hz]
      exact hgfix
    let d : X := z⁻¹ * sigma z
    have hd : d = z⁻¹ * sigma z := rfl
    have hdker : d ∈ pi.ker := by
      rw [hd, MonoidHom.mem_ker]
      simp [hzfix]
    have hdcent : d ∈ Subgroup.center X := hker hdker
    have hzd : sigma z = z * d := by
      rw [hd]; group
    have hcfix : sigma (z * c * z⁻¹) = z * c * z⁻¹ := by
      calc sigma (z * c * z⁻¹) = sigma z * sigma c * (sigma z)⁻¹ := by simp
        _ = (z * d) * c * (z * d)⁻¹ := by rw [hzd, hc]
        _ = z * (d * c) * d⁻¹ * z⁻¹ := by group
        _ = z * (c * d) * d⁻¹ * z⁻¹ := by
              rw [(Subgroup.mem_center_iff.mp hdcent c).symm]
        _ = z * c * z⁻¹ := by group
    rw [Subgroup.mem_map]
    refine ⟨z * c * z⁻¹, ?_, ?_⟩
    · rw [mem_ggAutFixedSubgroup]
      exact hcfix
    · simp [map_mul, map_inv, hz, hcx]

theorem centralFixedComponentTransfer_of_normal :
    CentralFixedComponentTransfer := by
  have h := @centralFixedImageNormal_holds
  intro X Y _ _ pi hpi hker sigma beta hcomm J hJ
  obtain ⟨hle, hnorm⟩ := h pi hpi hker sigma beta hcomm
  have hk : ∀ x : X, pi x = 1 → x ∈ Subgroup.center X :=
    fun x hx => hker (MonoidHom.mem_ker.2 hx)
  have hJopen : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup sigma) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hJ
  have hmapopen : CFSG.Open.IsComponentOf (J.map pi) ((ggAutFixedSubgroup sigma).map pi) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map pi hk hJopen
  have hsub : CFSG.Assembly.IsSubnormal ((ggAutFixedSubgroup sigma).map pi)
      (ggAutFixedSubgroup beta) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).2 hnorm.isSubnormal
  have hsubopen : CFSG.Open.IsSubnormal ((ggAutFixedSubgroup sigma).map pi)
      (ggAutFixedSubgroup beta) :=
    CFSG.Assembly.isSubnormal_iff_open.1 hsub
  have hcompopen : CFSG.Open.IsComponentOf (J.map pi) (ggAutFixedSubgroup beta) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans hmapopen hsubopen
  refine ⟨CFSG.Assembly.isComponentOf_iff_open.2 hcompopen, ?_⟩
  exact (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.centralImage_facts pi hk
    hJ.2.2).2

theorem centralFixedComponentTransfer_holds : CentralFixedComponentTransfer :=
  centralFixedComponentTransfer_of_normal

end CFSG.StandardType.S2MathAs51600

end
