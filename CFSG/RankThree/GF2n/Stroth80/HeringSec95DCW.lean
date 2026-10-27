module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Q7Moved
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec91b
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise


namespace HS9

variable {G : Type} [Group G]

def stabMod95 (V : Subgroup G) (y : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (V : Set G) ∧ ⁅g, y⁆ ∈ V}
  mul_mem' := by
    rintro g h ⟨hg, hgy⟩ ⟨hh, hhy⟩
    refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
    have e : ⁅g * h, y⁆ = (g * ⁅h, y⁆ * g⁻¹) * ⁅g, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp hhy) hgy
  one_mem' := ⟨Subgroup.one_mem _, by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro g ⟨hg, hgy⟩
    refine ⟨Subgroup.inv_mem _ hg, ?_⟩
    have e : ⁅g⁻¹, y⁆ = g⁻¹ * ⁅g, y⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (V.inv_mem hgy)

end HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_LB_X95 {C : Subgroup G} (hc : Ctx M Q Z C) {V W : Subgroup G} (hWQ : W ≤ Q)
    (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) (hCZV : C ⊔ Z ≤ V)
    {g : G} (hg : g ∈ LB M Q C) (hgV : g ∈ Subgroup.normalizer (V : Set G)) {b : G}
    (hb : b ∈ (QB C ⊓ W) ⊔ V) : ⁅g, b⁆ ∈ V := by
  have hnorm : V ≤ Subgroup.normalizer ((QB C ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv x hx
    have e : v * x * v⁻¹ = x := by rw [hVW v hv x hx.2]; group
    rw [e]; exact hx
  have hb' : b ∈ ((QB C ⊓ W : Subgroup G) : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]; exact hb
  obtain ⟨x, hx, v, hv, rfl⟩ := hb'
  have hgx : ⁅g, x⁆ ∈ V := hCZV (hc.comm_mem_sup_Z_of_mem_LB hg ⟨hWQ hx.2, hx.1⟩)
  have hgv : ⁅g, v⁆ ∈ V := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
    rw [commutatorElement_def]; exact V.mul_mem h1 (V.inv_mem hv)
  have e : ⁅g, x * v⁆ = ⁅g, x⁆ * (x * ⁅g, v⁆ * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine V.mul_mem hgx ?_
  have e2 : x * ⁅g, v⁆ * x⁻¹ = ⁅g, v⁆ := by rw [← hVW _ hgv x hx.2]; group
  rw [e2]; exact hgv


theorem cwr95_of (h91b : Stroth91bStatement) (hA : Sec9AExistsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        (∀ g ∈ Rt M (LB M Q B) t, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) → w ∈ Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs w hwW hw
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr := hc.conj_of_mem hrM
  set V := Vt M (LB M Q B) B Z t with hVd
  set W := Wt Q V with hWd
  obtain ⟨⟨hVXA, hXAW, hVXB, hXBW, hsup, hinf⟩, -⟩ :=
    h91b G M Q Z B hc n t hs r hr V W rfl rfl
  have hWQ : W ≤ Q := inf_le_left
  have hVW : ∀ v ∈ V, ∀ x ∈ W, v * x = x * v := fun v hv x hx =>
    Subgroup.mem_centralizer_iff.mp hx.2 v hv
  have hLBR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt _ ht
  have hLAR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hr.gen ▸ le_sup_right
  have hRV := hc.Rt_normalizes_Vt ht
  have hSB : ∀ g ∈ LB M Q B, ∀ b ∈ (QB B ⊓ W) ⊔ V, ⁅g, b⁆ ∈ V := fun g hg b hb =>
    comm_LB_X95 hc hWQ hVW (sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt) hg (hRV (hLBR hg)) hb
  have hSA : ∀ g ∈ LB M Q (conjSubgroup r B), ∀ b ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V,
      ⁅g, b⁆ ∈ V := fun g hg b hb =>
    comm_LB_X95 hcr hWQ hVW (hc.conj_Rt_le_Vt ht hrR) hg (hRV (hLAR hg)) hb
  have hcommW : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ V := fun x hx y hy =>
    sec39_Z_le_Vt (hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy))
  have hconj : conjSubgroup r ((QB B ⊓ W) ⊔ V) = (QB (conjSubgroup r B) ⊓ W) ⊔ V := by
    rw [show conjSubgroup r ((QB B ⊓ W) ⊔ V) = conjSubgroup r (QB B ⊓ W) ⊔ conjSubgroup r V from
      Subgroup.map_sup _ _ _, QB_conj, conjSubgroup_inf, sec9_conj_Wt_eq hc ht hrR,
      sec9_conj_Vt_eq hc ht hrR]
  have hnormX : (QB B ⊓ W) ⊔ V ≤
      Subgroup.normalizer (((QB (conjSubgroup r B) ⊓ W) ⊔ V : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    have e : k * x * k⁻¹ = ⁅k, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hVXA (hcommW k (hXBW hk) x (hXAW hx))) hx
  have hw' : w ∈ (((QB (conjSubgroup r B) ⊓ W) ⊔ V : Subgroup G) : Set G) *
      (((QB B ⊓ W) ⊔ V : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormX, hsup]; exact hwW
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have haW : a ∈ W := hXAW ha
  have haV : a ∈ V := by
    have hstab : Rt M (LB M Q B) t ≤ HS9.stabMod95 V a := by
      rw [hr.gen]
      refine sup_le (fun g hg => ⟨hRV (hLBR hg), ?_⟩) (fun g hg => ⟨hRV (hLAR hg), hSA g hg a ha⟩)
      have h1 := hw g (hLBR hg)
      have h2 := hSB g hg b hb
      have h3 : a * ⁅g, b⁆ * a⁻¹ = ⁅g, b⁆ := by rw [← hVW _ h2 a haW]; group
      have e : ⁅g, a⁆ = ⁅g, a * b⁆ * (a * ⁅g, b⁆ * a⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e, h3]; exact V.mul_mem h1 (V.inv_mem h2)
    have hr' : ⁅r⁻¹, a⁆ ∈ V := (hstab (Subgroup.inv_mem _ hrR)).2
    have hara : r⁻¹ * a * r ∈ (QB B ⊓ W) ⊔ V := by
      have : a ∈ conjSubgroup r ((QB B ⊓ W) ⊔ V) := by rw [hconj]; exact ha
      exact mem_conjSubgroup.mp this
    have e : a = ⁅r⁻¹, a⁆⁻¹ * (r⁻¹ * a * r) := by simp only [commutatorElement_def]; group
    have haXB : a ∈ (QB B ⊓ W) ⊔ V := by
      rw [e]; exact Subgroup.mul_mem _ (hVXB (V.inv_mem hr')) hara
    rw [← hinf]; exact ⟨ha, haXB⟩
  have hbV : b ∈ V := by
    have hrb : ⁅r, b⁆ ∈ V := by
      have h1 := hw r hrR
      have hra : ⁅r, a⁆ ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hRV hrR) a).mp haV
        rw [commutatorElement_def]; exact V.mul_mem this (V.inv_mem haV)
      have e : ⁅r, b⁆ = a⁻¹ * (⁅r, a⁆⁻¹ * ⁅r, a * b⁆) * a := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact V.mul_mem (V.mul_mem (V.inv_mem haV) (V.mul_mem (V.inv_mem hra) h1)) haV
    have hrbA : r * b * r⁻¹ ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V := by
      rw [← hconj]; exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using hb)
    have e : b = ⁅r, b⁆⁻¹ * (r * b * r⁻¹) := by simp only [commutatorElement_def]; group
    have hbXA : b ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V := by
      rw [e]; exact Subgroup.mul_mem _ (hVXA (V.inv_mem hrb)) hrbA
    rw [← hinf]; exact ⟨hbXA, hb⟩
  exact V.mul_mem haV hbV

theorem cwlb95_of (h91b : Stroth91bStatement) (hA : Sec9AExistsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        (∀ g ∈ LB M Q B, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) →
          w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs w hwW hw
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr := hc.conj_of_mem hrM
  set V := Vt M (LB M Q B) B Z t with hVd
  set W := Wt Q V with hWd
  obtain ⟨⟨hVXA, hXAW, hVXB, hXBW, hsup, hinf⟩, -⟩ :=
    h91b G M Q Z B hc n t hs r hr V W rfl rfl
  have hWQ : W ≤ Q := inf_le_left
  have hVW : ∀ v ∈ V, ∀ x ∈ W, v * x = x * v := fun v hv x hx =>
    Subgroup.mem_centralizer_iff.mp hx.2 v hv
  have hLBR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt _ ht
  have hLAR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hr.gen ▸ le_sup_right
  have hRV := hc.Rt_normalizes_Vt ht
  have hSB : ∀ g ∈ LB M Q B, ∀ b ∈ (QB B ⊓ W) ⊔ V, ⁅g, b⁆ ∈ V := fun g hg b hb =>
    comm_LB_X95 hc hWQ hVW (sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt) hg (hRV (hLBR hg)) hb
  have hSA : ∀ g ∈ LB M Q (conjSubgroup r B), ∀ b ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V,
      ⁅g, b⁆ ∈ V := fun g hg b hb =>
    comm_LB_X95 hcr hWQ hVW (hc.conj_Rt_le_Vt ht hrR) hg (hRV (hLAR hg)) hb
  have hcommW : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ V := fun x hx y hy =>
    sec39_Z_le_Vt (hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy))
  have hnormX : (QB B ⊓ W) ⊔ V ≤
      Subgroup.normalizer (((QB (conjSubgroup r B) ⊓ W) ⊔ V : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    have e : k * x * k⁻¹ = ⁅k, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hVXA (hcommW k (hXBW hk) x (hXAW hx))) hx
  have hw' : w ∈ (((QB (conjSubgroup r B) ⊓ W) ⊔ V : Subgroup G) : Set G) *
      (((QB B ⊓ W) ⊔ V : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormX, hsup]; exact hwW
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have haW : a ∈ W := hXAW ha
  have hstab : Rt M (LB M Q B) t ≤ HS9.stabMod95 V a := by
    rw [hr.gen]
    refine sup_le (fun g hg => ⟨hRV (hLBR hg), ?_⟩) (fun g hg => ⟨hRV (hLAR hg), hSA g hg a ha⟩)
    have h1 := hw g hg
    have h2 := hSB g hg b hb
    have h3 : a * ⁅g, b⁆ * a⁻¹ = ⁅g, b⁆ := by rw [← hVW _ h2 a haW]; group
    have e : ⁅g, a⁆ = ⁅g, a * b⁆ * (a * ⁅g, b⁆ * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, h3]; exact V.mul_mem h1 (V.inv_mem h2)
  have haV : a ∈ V :=
    cwr95_of h91b hA G M Q Z B hc n t hs a haW fun g hg => (hstab hg).2
  exact Subgroup.mul_mem _ (hVXB haV) hb

end CFSG.RankThree.GF2n.Stroth80
