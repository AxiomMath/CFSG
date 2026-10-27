module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenWeylLift
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Over

variable {G : Type} [Group G] {Bs K : Subgroup G} {hN : Bs ≤ Subgroup.normalizer (K : Set G)}

theorem GGOverGamma.orderOf_dvd {c : MulAut ↥Bs} {a : MulAut ↥(ggGamma K hN).range}
    (h : GGOverGamma hN c a) : orderOf a ∣ orderOf c := by
  rw [orderOf_dvd_iff_pow_eq_one]
  have h1 := h.pow (orderOf c)
  rw [pow_orderOf_eq_one] at h1
  exact GGOverGamma.eq_one_of_one h1

end Over

variable {G : Type} [Group G] [Finite G]

theorem exists_datum_of_label (hRig : GGLabelRigidInput) {Bs K : Subgroup G}
    (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (K ⧸ Subgroup.center K)) {P : LargeEvenRawCont}
    (hP : LargeEvenLabelAll lab P) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R) (I F : Set (MulAut R)),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) ∧ P R I F := by
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab) (P' := P)
    (fun lab' _ h' => by rw [h']; exact hP)
    (fun lab' R _ I F θ hPmark => hPmark.1) hmark
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN', hind⟩, hPR⟩ := hPθ
  refine ⟨R, ‹Group R›, θ, I, F, ?_, hPR⟩
  intro b hb
  obtain ⟨φ, hφI, hindφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
  have hφeq : φ = ggLAut K θ ⟨b⁻¹⁻¹,
      (Subgroup.normalizer (K : Set G)).inv_mem (hN' (Bs.inv_mem hb))⟩ :=
    eq_ggLAut_of_induces K θ (hN' (Bs.inv_mem hb)) hindφ
  have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem
      (hN' (Bs.inv_mem hb))⟩ : Subgroup.normalizer (K : Set G)) = ⟨b, hN hb⟩ :=
    Subtype.ext (inv_inv b)
  rw [hφeq, hb_eq] at hφI
  exact hφI

theorem ggNbr_card_dvd_of_label (hRig : GGLabelRigidInput) {p N : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hW : LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I)
    (hC : LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusAutCardDvdSCr p r R I N) :
    N ∣ Nat.card (ggAutomizer K Bs) := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, F, hBsI, ⟨r₁, hl₁, hT⟩, ⟨r₂, hl₂, hCard⟩⟩ :=
    exists_datum_of_label hRig hInnK hlab hhas (largeEvenLabelAll_and hW hC) hN
  have hK : commutator K = ⊤ := hInnK.1
  let A : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let H : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  have hTB₂ := ggTorusTBGroup_of_nbr hcfg hnb hK θ hN hBsI hl₂
  have hdvd : N ∣ Nat.card (ggAutomizer H A) := hCard K (ggQuotHom θ) A hTB₂
  have hlift := exists_overGamma_of_ggTorusReflGenW hcfg hnb hK θ hN hBsI hl₁ hT
  let Rel : Subgroup (MulAut ↥Bs × MulAut ↥A) :=
    { carrier := {q | q.1 ∈ ggAutomizer K Bs ∧ q.2 ∈ ggAutomizer H A ∧ GGOverGamma hN q.1 q.2}
      mul_mem' := fun {q q'} hq hq' =>
        ⟨Subgroup.mul_mem _ hq.1 hq'.1, Subgroup.mul_mem _ hq.2.1 hq'.2.1,
          hq.2.2.mul hq'.2.2⟩
      one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, GGOverGamma.one⟩
      inv_mem' := fun {q} hq =>
        ⟨Subgroup.inv_mem _ hq.1, Subgroup.inv_mem _ hq.2.1, hq.2.2.inv⟩ }
  let f₂ : Rel →* ↥(ggAutomizer H A) :=
    ((MonoidHom.snd _ _).comp Rel.subtype).codRestrict _ (fun q => q.2.2.1)
  let f₁ : Rel →* ↥(ggAutomizer K Bs) :=
    ((MonoidHom.fst _ _).comp Rel.subtype).codRestrict _ (fun q => q.2.1)
  have hf₂ : Function.Surjective f₂ := by
    rintro ⟨a, ha⟩
    obtain ⟨c, hcl, hover⟩ := hlift a ha
    have hCle : Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} ≤
        ggAutomizer K Bs := (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1)
    exact ⟨⟨(c, a), hCle hcl, ha, hover⟩, rfl⟩
  have hf₁ : Function.Injective f₁ := by
    intro q q' hq
    have h1 : q.1.1 = q'.1.1 := congrArg Subtype.val hq
    refine Subtype.ext (Prod.ext h1 ?_)
    refine MulEquiv.ext fun s => ?_
    obtain ⟨b, rfl⟩ := (ggGamma K hN).rangeRestrict_surjective s
    rw [← q.2.2.2 b, ← q'.2.2.2 b, h1]
  exact hdvd.trans
    ((Subgroup.card_dvd_of_surjective hf₂).trans (Subgroup.card_dvd_of_injective f₁ hf₁))

theorem ggNbr_exists_overGamma_lift (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (Q : ∀ (L' : Type) [Group L'], Subgroup (MulAut L') → Prop)
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → Q L' A) :
    ∃ hN : Bs ≤ Subgroup.normalizer (K : Set G), Q ↥K (ggGamma K hN).range ∧
      ∀ a ∈ ggTorusReflSet p (ggGamma K hN).range,
        ∃ c ∈ ggAutomizer K Bs, GGIsReflection p c ∧ GGOverGamma hN c a := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, F, hBsI, ⟨r, hl, hfr⟩⟩ :=
    exists_datum_of_label hRig hInnK hlab hhas hF hN
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hInnK.1 θ hN hBsI hl
  refine ⟨hN, hfr K (ggQuotHom θ) (ggGamma K hN).range hTB, ?_⟩
  rintro _ ⟨n, hn, hW, rfl, hr⟩
  obtain ⟨g, hgK, hg, hrefl, hov⟩ :=
    exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN hW hn hr
  exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgK hg, hrefl, hov⟩

theorem ggNbr_exists_frame_pair (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A) :
    ∃ c₁ ∈ ggAutomizer K Bs, ∃ c₂ ∈ ggAutomizer K Bs, GGIsReflection p c₁ ∧
      GGIsReflection p c₂ ∧ 4 ∣ orderOf (c₁ * c₂) := by
  obtain ⟨hN, ⟨a₁, ha₁, a₂, ha₂, hord⟩, hlift⟩ := ggNbr_exists_overGamma_lift hRig hcfg hnb hInnK
    hlab hhas (fun _ _ A => GGTorusFrame p A) hF
  obtain ⟨c₁, hc₁, hr₁, hov₁⟩ := hlift a₁ ha₁
  obtain ⟨c₂, hc₂, hr₂, hov₂⟩ := hlift a₂ ha₂
  exact ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, hord.trans (hov₁.mul hov₂).orderOf_dvd⟩

theorem ggNbr_exists_order_nine (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusOrderNine p A) :
    ∃ c ∈ ggAutomizer K Bs, 9 ∣ orderOf c := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, F, hBsI, ⟨r, hl, hfr⟩⟩ :=
    exists_datum_of_label hRig hInnK hlab hhas hF hN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hInnK.1 θ hN hBsI hl
  obtain ⟨n, hn, hW, h9⟩ := hfr K (ggQuotHom θ) (ggGamma K hN).range hTB
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hN hSC hW
  have hov : GGOverGamma hN (ggConjAut Bs hnN) (ggConjAut (ggGamma K hN).range hn) := by
    have h := ggOverGamma_conjAut (hN := hN) n.2 hnN
    have heq : ggConjAut (ggGamma K hN).range
          (conj_mem_normalizer_range_ggGamma hN n.2 hnN)
        = ggConjAut (ggGamma K hN).range hn := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rfl
    rwa [heq] at h
  exact ⟨ggConjAut Bs hnN, ggConjAut_mem_ggAutomizer n.2 hnN, h9.trans hov.orderOf_dvd⟩

end CFSG.StandardType

end
