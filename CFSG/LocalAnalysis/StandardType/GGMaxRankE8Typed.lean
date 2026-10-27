module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorLiftE8 : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .E8 →
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 (8 - ggTorEnn 3 lab) R

@[expose] def GGResE8SeparatedDatum {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V),
    (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
    (∀ i, GGIsReflection p (φ i)) ∧
    (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) ∧
    (∃ f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs),
      ∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
    ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
    (∀ b : ↥Bs, (∀ i, α i (ι (Additive.ofMul b)) = 0) ↔
      (b : G) ∈ Subgroup.centralizer (X : Set G))

private theorem l6m2_core_L (hT : GGTBTorE8) (hLift : GGTBTorLiftE8) (hLab : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {labX : LargeEvenLabel} (hΛX : LargeEvenInLambda2 labX)
    (hXhas : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (htag : labX.tag = .E8)
    (hp3 : p = 3) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      Odd (ggTorME8 labX) ∧ p ∣ ggTorME8 labX ∧
        GGIntCartan CoxeterMatrix.E₈ CartanMatrix.E₈ ∧
        GGTorusTorData (ggTorME8 labX) 8 CartanMatrix.E₈ CoxeterMatrix.E₈ ↥L
          (ggGamma L hN).range := by
  subst hp3
  have hp : Nat.Prime 3 := Fact.out
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrowX : GGTBTorRowAt 3 labX (8 - ggTorEnn 3 labX) (ggTorME8 labX) 8
      CartanMatrix.E₈ CoxeterMatrix.E₈ := GGTBTorRowAt.e8Three htag rfl
  have hinner : GGInnerDiagOn Bs L := hH.2.2.1.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := ggInnerDiagOn_relabel hLab hinner hΛX hXhas
  obtain ⟨_, _, _, _, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  have hWl := hT lab hΛX htag
  have hLl := hLift lab hΛX htag
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb) hlift
  have hTor := hWtor ↥L (ggQuotHom θ) (ggGamma L hN).range hTB
  obtain ⟨hom, hpm, _, hMC⟩ := l05nPlP1_row_facts hp hp2 hΛX hrowX
  exact ⟨hN, hom, hpm, hMC, hTor⟩

private theorem l6m2_core_K (hT : GGTBTorE8) (hLift : GGTBTorLiftE8) (hLab : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {labX : LargeEvenLabel} (hΛX : LargeEvenInLambda2 labX)
    (hXhas : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (htag : labX.tag = .E8)
    (hp3 : p = 3) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      Odd (ggTorME8 labX) ∧ p ∣ ggTorME8 labX ∧
        GGIntCartan CoxeterMatrix.E₈ CartanMatrix.E₈ ∧
        GGTorusTorData (ggTorME8 labX) 8 CartanMatrix.E₈ CoxeterMatrix.E₈ ↥K
          (ggGamma K hN).range := by
  subst hp3
  have hp : Nat.Prime 3 := Fact.out
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrowX : GGTBTorRowAt 3 labX (8 - ggTorEnn 3 labX) (ggTorME8 labX) 8
      CartanMatrix.E₈ CoxeterMatrix.E₈ := GGTBTorRowAt.e8Three htag rfl
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hinner : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨hperf, lab, hlab, hraw⟩ := ggInnerDiagOn_relabel hLab hinner hΛX hXhas
  obtain ⟨_, _, _, _, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  have hWl := hT lab hΛX htag
  have hLl := hLift lab hΛX htag
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hBsI hb) hlift
  have hTor := hWtor ↥K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨hom, hpm, _, hMC⟩ := l05nPlP1_row_facts hp hp2 hΛX hrowX
  exact ⟨hN, hom, hpm, hMC, hTor⟩

private theorem l6m2_e8Datum_of_torData {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hMC : GGIntCartan CoxeterMatrix.E₈ CartanMatrix.E₈)
    (hTor : GGTorusTorData m 8 CartanMatrix.E₈ CoxeterMatrix.E₈ ↥X (ggGamma X hN).range) :
    GGResE8SeparatedDatum p Bs X := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ :=
    exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin 8 → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin 8 → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  have hlin : ∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
      v - α i v • ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs)) := by
    intro i v
    rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  have hpair : ∀ i j, α i (ι (Additive.ofMul (⟨_, hbk j⟩ : ↥Bs))) =
      ((CartanMatrix.E₈ i j : ℤ) : ZMod p) := by
    intro i j
    rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨V, hVadd, hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, hlin, ?_, hpair, ⟨e, he⟩, hcl, ?_⟩
  · intro i
    exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))
  · intro b
    constructor
    · intro hb0
      refine (ggGamma_eq_one_iff X hN b).mp (hFsep b fun i => ?_)
      have := hb0 i
      rwa [hα, AddEquiv.symm_apply_apply, toMul_ofMul] at this
    · intro hb0 i
      rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
      exact hF1 i b ((ggGamma_eq_one_iff X hN b).mpr hb0)

theorem ggResE8Separated_of_tbTor (hT : GGTBTorE8) (hLift : GGTBTorLiftE8)
    (hLab : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    (GGResRowAt ggRowMaxRank p J L → GGResE8SeparatedDatum p Bs L) ∧
      (GGResRowAt ggRowMaxRank p J K → GGResE8SeparatedDatum p Bs K) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  constructor
  · intro hrowL
    obtain ⟨_, labX, _, hΛX, _, hXhas, hrowmax⟩ := hrowL
    have hp3 : p = 3 := by rcases hrowmax with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩ <;> exact h
    have htag : labX.tag = .E8 := by
      rcases hrowmax with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl
    obtain ⟨hN, hom, hpm, hMC, hTor⟩ := l6m2_core_L hT hLift hLab hH hΛX hXhas htag hp3
    exact l6m2_e8Datum_of_torData hp2 hom hpm hBs hS hN hMC hTor
  · intro hrowK
    obtain ⟨_, labX, _, hΛX, _, hXhas, hrowmax⟩ := hrowK
    have hp3 : p = 3 := by rcases hrowmax with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩ <;> exact h
    have htag : labX.tag = .E8 := by
      rcases hrowmax with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl
    obtain ⟨hN, hom, hpm, hMC, hTor⟩ := l6m2_core_K hT hLift hLab hH hΛX hXhas htag hp3
    exact l6m2_e8Datum_of_torData hp2 hom hpm hBs hS hN hMC hTor

end CFSG.StandardType

end
