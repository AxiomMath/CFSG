module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem comm_mul_left91 (hc : Ctx M Q Z B) {a b c : G} (ha : a ∈ Q) (hb : b ∈ Q) (hcQ : c ∈ Q) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have h1 : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := hc.conj_Z_of_mem_Q ha (comm_Q91 hc hb hcQ)
  have h3 : ⁅b, c⁆ * ⁅a, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ :=
    comm_Z_Q91 hc (hc.Z_le_Q (comm_Q91 hc hb hcQ)) (comm_Q91 hc ha hcQ)
  rw [h1, h2, h3]

theorem comm_mul_right91 (hc : Ctx M Q Z B) {a b c : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (hcQ : c ∈ Q) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]; group
  have h2 : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := hc.conj_Z_of_mem_Q hb (comm_Q91 hc ha hcQ)
  rw [h1, h2]

theorem comm_Q_le_V91 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    {y : G} (hy : y ∈ Q) : ⁅s, y⁆ ∈ Vt M (LB M Q B) B Z t := by
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hsW := comm_Wt_le_Z91 h34 h91b hs hr hZ0 hsZ
  have hxQ : ⁅s, y⁆ ∈ Q := by
    have : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact Q.mul_mem (conj_mem_Q91 hc hsM hy) (Q.inv_mem hy)
  refine hc.centralizer_Wt_le_Vt t hxQ fun w hw => ?_
  have hwQ : w ∈ Q := hw.1
  set z₁ := ⁅s, w⁆ with hz₁
  have hz₁Z : z₁ ∈ Z := hsW w hw
  have hz₁Q : z₁ ∈ Q := hc.Z_le_Q hz₁Z
  have hinv : s⁻¹ * z₁⁻¹ * s = z₁⁻¹ := by
    have := Rt_cent_Z91 hc t ((Rt M (LB M Q B) t).inv_mem hsR) (Z.inv_mem hz₁Z)
    simpa using this
  have e1 : s⁻¹ * w * s = z₁⁻¹ * w := by
    have hz : z₁⁻¹ = w * s * w⁻¹ * s⁻¹ := by
      rw [hz₁]; simp only [commutatorElement_def]; group
    calc s⁻¹ * w * s = s⁻¹ * (w * s * w⁻¹ * s⁻¹) * s * w := by group
      _ = s⁻¹ * z₁⁻¹ * s * w := by rw [hz]
      _ = z₁⁻¹ * w := by rw [hinv]
  have hsyQ : s * y * s⁻¹ ∈ Q := conj_mem_Q91 hc hsM hy
  have e2 : ⁅s * y * s⁻¹, w⁆ = ⁅y, w⁆ := by
    have h1 : ⁅s * y * s⁻¹, w⁆ = s * ⁅y, s⁻¹ * w * s⁆ * s⁻¹ := by
      simp only [commutatorElement_def]; group
    have hsw' : s⁻¹ * w * s ∈ Q := by
      rw [e1]
      exact Q.mul_mem (Q.inv_mem hz₁Q) hwQ
    have h2 : ⁅y, s⁻¹ * w * s⁆ = ⁅y, w⁆ := by
      rw [e1, comm_mul_right91 hc hy (Q.inv_mem hz₁Q) hwQ]
      have : ⁅y, z₁⁻¹⁆ = 1 := by
        have := comm_Z_Q91 hc hy (Z.inv_mem hz₁Z)
        simp only [commutatorElement_def]
        rw [mul_assoc, this]; group
      rw [this, one_mul]
    rw [h1, h2]
    exact Rt_cent_Z91 hc t hsR (comm_Q91 hc hy hwQ)
  have e3 : ⁅⁅s, y⁆, w⁆ = ⁅s * y * s⁻¹, w⁆ * ⁅y⁻¹, w⁆ := by
    have : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact comm_mul_left91 hc hsyQ (Q.inv_mem hy) hwQ
  have e4 : ⁅y⁻¹, w⁆ = ⁅y, w⁆⁻¹ := by
    have h := comm_mul_left91 hc (Q.inv_mem hy) hy hwQ
    rw [inv_mul_cancel] at h
    have h0 : ⁅(1 : G), w⁆ = 1 := by simp [commutatorElement_def]
    rw [h0] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  rw [e3, e2, e4]
  group

def centModV91 (hc : Ctx M Q Z B) (t : G) (ht : t ∈ LB M Q B) : Subgroup G where
  carrier := {g | g ∈ Rt M (LB M Q B) t ∧ ∀ y ∈ Q, ⁅y, g⁆ ∈ Vt M (LB M Q B) B Z t}
  mul_mem' := by
    rintro g g' ⟨hg, hgV⟩ ⟨hg', hgV'⟩
    refine ⟨(Rt M (LB M Q B) t).mul_mem hg hg', fun y hy => ?_⟩
    have e : ⁅y, g * g'⁆ = ⁅y, g⁆ * (g * ⁅y, g'⁆ * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hgV y hy)
      ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hg) _).mp (hgV' y hy))
  one_mem' := ⟨(Rt M (LB M Q B) t).one_mem, fun y _ => by
    simpa [commutatorElement_def] using (Vt M (LB M Q B) B Z t).one_mem⟩
  inv_mem' := by
    rintro g ⟨hg, hgV⟩
    refine ⟨(Rt M (LB M Q B) t).inv_mem hg, fun y hy => ?_⟩
    have e : ⁅y, g⁻¹⁆ = g⁻¹ * ⁅y, g⁆⁻¹ * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem hg)) _).mp
      ((Vt M (LB M Q B) B Z t).inv_mem (hgV y hy))
    simpa using h1

theorem centre_clause91 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    (hsQ : s ∉ Q) :
    ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hb : ∀ y ∈ Q, ⁅y, s⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro y hy
    rw [← commutatorElement_inv]
    exact (Vt M (LB M Q B) B Z t).inv_mem (comm_Q_le_V91 h34 h91b hs hr hZ0 hsZ hy)
  have hnormZ : ∀ y ∈ Vt M (LB M Q B) B Z t, y ∈ Subgroup.normalizer (Z : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun z hz => zconj91 hc (hQM (hVQ hy)) hz
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G,
      U = Subgroup.closure (Set.range fun y : ↥Q => ⁅(y : G), s⁆) ⊔ Z := ⟨_, rfl⟩
  have hclV : Subgroup.closure (Set.range fun y : ↥Q => ⁅(y : G), s⁆) ≤
      Vt M (LB M Q B) B Z t := by
    rw [Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    exact hb y y.2
  have hZU : Z ≤ U := by rw [hU]; exact le_sup_right
  have hUV : U ≤ Vt M (LB M Q B) B Z t := by rw [hU]; exact sup_le hclV hZV
  have hclU : ∀ y ∈ Q, ⁅y, s⁆ ∈ U := fun y hy => by
    rw [hU]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩)
  have hgen : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * ⁅y, s⁆ * ρ⁻¹ ∈ U := by
    intro ρ hρ y hy
    have hρM : ρ ∈ M := hc.Rt_le_M t hρ
    have hq₁ : ⁅ρ, s⁆ ∈ Q := by
      have := hZ0.comm_mem hsZ hρ
      rw [← commutatorElement_inv]
      exact Q.inv_mem this
    set q₁ := ⁅ρ, s⁆ with hq₁def
    set y' := ρ * y * ρ⁻¹ with hy'
    have hy'Q : y' ∈ Q := conj_mem_Q91 hc hρM hy
    have hy's : ⁅y', s⁆ ∈ Q := by
      have : ⁅y', s⁆ = y' * (s * y'⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact Q.mul_mem hy'Q (conj_mem_Q91 hc hsM (Q.inv_mem hy'Q))
    have e : ρ * ⁅y, s⁆ * ρ⁻¹ = ⁅y', q₁⁆ * (⁅q₁, ⁅y', s⁆⁆ * ⁅y', s⁆) := by
      simp only [hq₁def, hy', commutatorElement_def]; group
    rw [e]
    have hz1 : ⁅y', q₁⁆ ∈ Z := comm_Q91 hc hy'Q hq₁
    have hz2 : ⁅q₁, ⁅y', s⁆⁆ ∈ Z := comm_Q91 hc hq₁ hy's
    exact U.mul_mem (hZU hz1) (U.mul_mem (hZU hz2) (hclU y' hy'Q))
  have hRU : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    intro ρ hρ u hu
    rw [hU] at hu
    obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (fun y hy => hnormZ y (hclV hy)) hu
    have hρM := hc.Rt_le_M t hρ
    have e : ρ * (a * z) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * z * ρ⁻¹) := by group
    rw [e]
    refine U.mul_mem ?_ (hZU (zconj91 hc hρM hz))
    refine Subgroup.closure_induction (p := fun x _ => ρ * x * ρ⁻¹ ∈ U) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨y, rfl⟩
      exact hgen ρ hρ y y.2
    · simpa using U.one_mem
    · intro x y _ _ hx hy
      have e : ρ * (x * y) * ρ⁻¹ = (ρ * x * ρ⁻¹) * (ρ * y * ρ⁻¹) := by group
      rw [e]
      exact U.mul_mem hx hy
    · intro x _ hx
      have e : ρ * x⁻¹ * ρ⁻¹ = (ρ * x * ρ⁻¹)⁻¹ := by group
      rw [e]
      exact U.inv_mem hx
  rcases sec9VtIrred91 hs hZU hUV hRU with hUZ | hUVeq
  · exfalso
    apply hsQ
    refine hc.hyp.centralizer_Qt s hsM fun y hy => ?_
    have h1 : ⁅y, s⁆ ∈ Z := by rw [← hUZ]; exact hclU y hy
    rw [← commutatorElement_inv]
    exact Z.inv_mem h1
  · apply le_antisymm
    · refine sup_le ?_ hZV
      refine Subgroup.commutator_le.mpr fun y hy g hg => ?_
      have hsT : s ∈ centModV91 hc t ht := ⟨hsR, fun y hy => hb y hy⟩
      have hgT := (Subgroup.zpowers_le.mpr hsT) hg
      exact hgT.2 y hy
    · rw [← hUVeq, hU]
      refine sup_le_sup_right ?_ Z
      rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers s)

end HS9

end CFSG.RankThree.GF2n.Stroth80
