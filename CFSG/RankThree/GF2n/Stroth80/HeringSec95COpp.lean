module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CN6
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_mem_V_of_mem_sup {hc : Ctx M Q Z B} {V : Subgroup G} (hVQ : V ≤ Q)
    (hBV : B ⊔ Z ≤ V) (hLV : ∀ l ∈ LB M Q B, ∀ v ∈ V, l * v * l⁻¹ ∈ V) {l x : G}
    (hl : l ∈ LB M Q B) (hx : x ∈ (QB B ⊓ Wt Q V) ⊔ V) : ⁅l, x⁆ ∈ V := by
  have hn : QB B ⊓ Wt Q V ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hn hx
  have haQ : a ∈ Q ⊓ QB B :=
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).1, (Subgroup.mem_inf.mp ha).1⟩
  have h1 : ⁅l, a⁆ ∈ V := hBV (comm_LB_inf_QB hc hl haQ)
  have h2 : ⁅l, v⁆ ∈ V := by
    have e : ⁅l, v⁆ = (l * v * l⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V.mul_mem (hLV l hl v hv) (V.inv_mem hv)
  have h3 : a * ⁅l, v⁆ * a⁻¹ = ⁅l, v⁆ := by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
      _ h2
    rw [← this]
    group
  have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, h3]
  exact V.mul_mem h1 h2

theorem isOppDecomp95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    IsOppDecomp (Wt Q (Vt M (LB M Q B) B Z t)) (Vt M (LB M Q B) B Z t)
      (LB M Q (conjSubgroup r B)) (LB M Q B)
      ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
      ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨hds, -⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, hinf⟩ := hds
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hcomm : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    hZV (hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy))
  have hsq : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), x ^ 2 ∈ Vt M (LB M Q B) B Z t := fun x hx =>
    hZV (hc.hyp.toHyp79.sq_mem_V (hWQ hx))
  have hRV : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      ρ * v * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t := fun ρ hρ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) v).mp hv
  have hLB_R : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA_R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hc' : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hBV : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt ht) hZV
  have hAV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt ht hrR
  have fixB : ∀ l ∈ LB M Q B, ∀ x ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t, ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := fun l hl x hx =>
    comm_mem_V_of_mem_sup (hc := hc) hVQ hBV (fun l hl v hv => hRV l (hLB_R hl) v hv) hl hx
  have fixA : ∀ l ∈ LB M Q (conjSubgroup r B), ∀ x ∈ (QB (conjSubgroup r B) ⊓
      Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t,
      ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := fun l hl x hx =>
    comm_mem_V_of_mem_sup (hc := hc') hVQ hAV (fun l hl v hv => hRV l (hLA_R hl) v hv) hl hx
  have closure : ∀ y : G, (∀ l ∈ LB M Q B, ⁅l, y⁆ ∈ Vt M (LB M Q B) B Z t) →
      (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, y⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ, y⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro y hB hA
    let S : Subgroup G :=
      { carrier := {ρ | ρ ∈ Rt M (LB M Q B) t ∧ ⁅ρ, y⁆ ∈ Vt M (LB M Q B) B Z t}
        mul_mem' := by
          rintro ρ σ ⟨hρ, hρy⟩ ⟨hσ, hσy⟩
          refine ⟨(Rt M (LB M Q B) t).mul_mem hρ hσ, ?_⟩
          have e : ⁅ρ * σ, y⁆ = ρ * ⁅σ, y⁆ * ρ⁻¹ * ⁅ρ, y⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (Vt M (LB M Q B) B Z t).mul_mem (hRV ρ hρ _ hσy) hρy
        one_mem' := ⟨(Rt M (LB M Q B) t).one_mem, by
          rw [commutatorElement_one_left]; exact (Vt M (LB M Q B) B Z t).one_mem⟩
        inv_mem' := by
          rintro ρ ⟨hρ, hρy⟩
          refine ⟨(Rt M (LB M Q B) t).inv_mem hρ, ?_⟩
          have e : ⁅ρ⁻¹, y⁆ = ρ⁻¹ * ⁅ρ, y⁆⁻¹ * ρ := by
            simp only [commutatorElement_def]; group
          rw [e]
          have := hRV ρ⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ) _
            ((Vt M (LB M Q B) B Z t).inv_mem hρy)
          simpa using this }
    have hle : Rt M (LB M Q B) t ≤ S := by
      rw [hr.gen]
      exact sup_le (fun l hl => ⟨hLB_R hl, hB l hl⟩) (fun l hl => ⟨hLA_R hl, hA l hl⟩)
    intro ρ hρ
    exact (hle hρ).2
  have hnorm : (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t ≤ Subgroup.normalizer
        (((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t : Subgroup G) :
          Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha b hb => ?_
    have hcb : ⁅a, b⁆ ∈ Vt M (LB M Q B) B Z t := hcomm a (hA₁W ha) b (hA₂W hb)
    have key : a * b * a⁻¹ = ⁅a, b⁆ * b := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact (Subgroup.mul_mem _ (hVA₂ hcb) hb)
  have hnV : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
  have hnV' : QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
  have hRW : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ρ * w * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun ρ hρ w hw =>
    sec9_conj_mem_Wt hc ht hρ hw
  have hrinv : r⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hrR
  refine ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, hinf, hcomm, hsq, ?_, ?_⟩
  ·
    intro x hx
    refine ⟨fun hxA l hl => fixA l hl x hxA, fun hfix => ?_⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm
      (hsup ▸ hx)
    subst hxa
    have ha₁W := hA₁W ha₁
    have ha₂W := hA₂W ha₂
    have hfix₂ : ∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, a₂⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro l hl
      have h1 := Om10.fixSec_inv_aux ha₁W (fixA l hl a₁ ha₁)
      have h2 := Om10.fixSec_mul_aux h1.1 h1.2 hx (hfix l hl)
      simpa using h2.2
    have hcl := closure a₂ (fun l hl => fixB l hl a₂ ha₂) hfix₂ r hrR
    obtain ⟨c, hc, v, hv, hcv⟩ := exists_mul_of_mem_sup_of_le_normalizer hnV ha₂
    have hrc : r * c * r⁻¹ ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
      refine ⟨?_, hRW r hrR c (Subgroup.mem_inf.mp hc).2⟩
      rw [QB_conj]
      exact mem_conjSubgroup.mpr (by
        rw [show r⁻¹ * (r * c * r⁻¹) * r = c by group]
        exact (Subgroup.mem_inf.mp hc).1)
    have hra : r * a₂ * r⁻¹ ∈ (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t := by
      rw [← hcv, show r * (c * v) * r⁻¹ = (r * c * r⁻¹) * (r * v * r⁻¹) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hrc)
        (Subgroup.mem_sup_right (hRV r hrR v hv))
    have ha₂A₁ : a₂ ∈ (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t := by
      have e : a₂ = ⁅r, a₂⁆⁻¹ * (r * a₂ * r⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hVA₁ ((Vt M (LB M Q B) B Z t).inv_mem hcl)) hra
    have ha₂V : a₂ ∈ Vt M (LB M Q B) B Z t := by
      rw [← hinf]
      exact ⟨ha₂A₁, ha₂⟩
    exact Subgroup.mul_mem _ ha₁ (hVA₁ ha₂V)
  ·
    intro x hx
    refine ⟨fun hxA l hl => fixB l hl x hxA, fun hfix => ?_⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm
      (hsup ▸ hx)
    subst hxa
    have ha₁W := hA₁W ha₁
    have ha₂W := hA₂W ha₂
    have hfix₁ : ∀ l ∈ LB M Q B, ⁅l, a₁⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro l hl
      have h1 := Om10.fixSec_inv_aux ha₂W (fixB l hl a₂ ha₂)
      have h2 := Om10.fixSec_mul_aux hx (hfix l hl) h1.1 h1.2
      simpa using h2.2
    have hcl := closure a₁ hfix₁ (fun l hl => fixA l hl a₁ ha₁) r⁻¹ hrinv
    obtain ⟨c, hc, v, hv, hcv⟩ := exists_mul_of_mem_sup_of_le_normalizer hnV' ha₁
    have hrc : r⁻¹ * c * r ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
      refine ⟨?_, ?_⟩
      · have h1 : c ∈ conjSubgroup r (QB B) := by
          rw [← QB_conj]
          exact (Subgroup.mem_inf.mp hc).1
        exact mem_conjSubgroup.mp h1
      · have := hRW r⁻¹ hrinv c (Subgroup.mem_inf.mp hc).2
        simpa using this
    have hra : r⁻¹ * a₁ * r ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t := by
      rw [← hcv, show r⁻¹ * (c * v) * r = (r⁻¹ * c * r) * (r⁻¹ * v * r) by group]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hrc) (Subgroup.mem_sup_right ?_)
      have := hRV r⁻¹ hrinv v hv
      simpa using this
    have ha₁A₂ : a₁ ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
      have e : a₁ = ⁅r⁻¹, a₁⁆⁻¹ * (r⁻¹ * a₁ * r) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hVA₂ ((Vt M (LB M Q B) B Z t).inv_mem hcl)) hra
    have ha₁V : a₁ ∈ Vt M (LB M Q B) B Z t := by
      rw [← hinf]
      exact ⟨ha₁, ha₁A₂⟩
    exact Subgroup.mul_mem _ (hVA₂ ha₁V) ha₂

end HS9

end CFSG.RankThree.GF2n.Stroth80
