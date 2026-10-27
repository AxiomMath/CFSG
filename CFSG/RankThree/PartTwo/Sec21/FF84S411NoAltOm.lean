module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411R
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmAlt

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

theorem pm_add_left (x y z : F6) :
    polarMinus (x + y) z = polarMinus x z + polarMinus y z := by
  simp only [polarMinus, Pi.add_apply]
  ring

theorem pm_add_right (x y z : F6) :
    polarMinus x (y + z) = polarMinus x y + polarMinus x z := by
  simp only [polarMinus, Pi.add_apply]
  ring

theorem pm_smul_left (c : ZMod 2) (x z : F6) : polarMinus (c • x) z = c * polarMinus x z := by
  simp only [polarMinus, Pi.smul_apply, smul_eq_mul]
  ring

theorem pm_zero_left (z : F6) : polarMinus 0 z = 0 := by
  simp [polarMinus]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem F6_add_self : ∀ x : F6, x + x = 0 := by decide +kernel

theorem F6_sub_eq_add : ∀ a b : F6, a - b = a + b := by decide +kernel

theorem tau0_add_tau0 : (tau0 : F6) + tau0 = 0 := F6_add_self _

theorem eich_comp_vec (k₁ k₂ x : F6) (h₁ : polarMinus k₁ tau0 = 0) (h₂ : polarMinus k₂ tau0 = 0) :
    x + polarMinus x tau0 • k₂ + (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) • tau0 +
        polarMinus (x + polarMinus x tau0 • k₂ + (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) •
          tau0) tau0 • k₁ +
      (polarMinus (x + polarMinus x tau0 • k₂ +
          (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) • tau0) k₁ +
        qMinus k₁ * polarMinus (x + polarMinus x tau0 • k₂ +
          (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) • tau0) tau0) • tau0 =
    x + polarMinus x tau0 • (k₁ + k₂) +
      (polarMinus x (k₁ + k₂) + qMinus (k₁ + k₂) * polarMinus x tau0) • tau0 := by
  have hτ : polarMinus tau0 k₁ = 0 := by rw [polarMinus_comm]; exact h₁
  have hb : polarMinus (x + polarMinus x tau0 • k₂ +
      (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) • tau0) tau0 = polarMinus x tau0 := by
    rw [pm_add_left, pm_add_left, pm_smul_left, pm_smul_left, h₂, polarMinus_self]
    ring
  have hk : polarMinus (x + polarMinus x tau0 • k₂ +
      (polarMinus x k₂ + qMinus k₂ * polarMinus x tau0) • tau0) k₁ =
      polarMinus x k₁ + polarMinus x tau0 * polarMinus k₂ k₁ := by
    rw [pm_add_left, pm_add_left, pm_smul_left, pm_smul_left, hτ]
    ring
  rw [hb, hk, pm_add_right x k₁ k₂, qMinus_add k₁ k₂, polarMinus_comm k₂ k₁]
  module

@[expose] def prK (x : F6) : F6 := x + polarMinus x sig0 • tau0

theorem prK_add : ∀ x y : F6, prK (x + y) = prK x + prK y := by decide +kernel

theorem prK_zero : prK 0 = 0 := by decide

theorem prK_tau0 : prK tau0 = 0 := by decide

theorem prK_mem : ∀ x : F6, polarMinus x tau0 = 0 →
    polarMinus (prK x) sig0 = 0 ∧ polarMinus (prK x) tau0 = 0 := by decide +kernel

theorem pm_act (g : OmG) (x y : F6) : polarMinus (g • x) (g • y) = polarMinus x y :=
  polarMinus_apply_of_mem g.2 x y

theorem smul_comm_F6 (g : OmG) (c : ZMod 2) (v : F6) : g • (c • v) = c • (g • v) :=
  map_smul (g : F6 ≃ₗ[ZMod 2] F6) c v

theorem Eτ_fix_tau {g : OmG} (hg : g ∈ Eτ) : g • tau0 = tau0 := by
  obtain ⟨g', _, rfl⟩ := Subgroup.mem_map.mp hg
  exact mem_stabilizer_iff.mp g'.2

theorem eichOm_mem_Eτ' {w : F6} (hw : polarMinus w tau0 = 0) : eichOm w ∈ Eτ :=
  rootGroupOm_le_Eτ (eichOm_mem_rootGroupOm hw)

theorem eichOm_mul {k₁ k₂ : F6} (hk₁ : k₁ ∈ Kperp) (hk₂ : k₂ ∈ Kperp) :
    eichOm k₁ * eichOm k₂ = eichOm (k₁ + k₂) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have h12 : polarMinus (k₁ + k₂) tau0 = 0 := by rw [pm_add_left, hk₁.2, hk₂.2, add_zero]
  show (eichOm k₁ * eichOm k₂) • x = eichOm (k₁ + k₂) • x
  rw [mul_smul, eichOm_smul hk₂.2 x, eichOm_smul hk₁.2, eichOm_smul h12 x]
  exact eich_comp_vec k₁ k₂ x hk₁.2 hk₂.2

theorem conj_eichOm {h : OmG} (hh : h ∈ P2) {v : F6} (hv : polarMinus v tau0 = 0) :
    h * eichOm v * h⁻¹ = eichOm (h • v) := by
  have ht : h • tau0 = tau0 := (mem_P2.1 hh).2
  have hv' : polarMinus (h • v) tau0 = 0 := by
    have := pm_act h v tau0
    rw [ht] at this
    rw [this, hv]
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  show (h * eichOm v * h⁻¹) • x = eichOm (h • v) • x
  rw [mul_smul, mul_smul, eichOm_smul hv', eichOm_smul hv]
  have e1 : polarMinus (h⁻¹ • x) tau0 = polarMinus x tau0 := by
    have := pm_act h (h⁻¹ • x) tau0
    rw [ht, smul_inv_smul] at this
    exact this.symm
  have e2 : polarMinus (h⁻¹ • x) v = polarMinus x (h • v) := by
    have := pm_act h (h⁻¹ • x) v
    rw [smul_inv_smul] at this
    exact this.symm
  have e3 : qMinus v = qMinus (h • v) := (qMinus_apply_of_mem h.2 v).symm
  rw [smul_add, smul_add, smul_comm_F6, smul_comm_F6, smul_inv_smul, ht, e1, e2, e3]

theorem isPGroup_Eτ : IsPGroup 2 ↥Eτ := by
  intro x
  obtain ⟨g', hg', hx⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥(MulAction.stabilizer OmG tau0))
    ⟨g', hg'⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : g' ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h3 : (x : OmG) ^ (2 ^ k) = 1 := by
    rw [← hx]
    show ((MulAction.stabilizer OmG tau0).subtype g') ^ (2 ^ k) = 1
    rw [← map_pow, h1, map_one]
  simpa using h3

theorem prK_eq_self {x : F6} (hx : polarMinus x sig0 = 0) : prK x = x := by
  unfold prK
  rw [hx, zero_smul, add_zero]

theorem prK_add_smul_tau (c : ZMod 2) (y : F6) : prK (y + c • tau0) = prK y := by
  rw [prK_add]
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, prK_zero, add_zero]
  · rw [one_smul, prK_tau0, add_zero]

abbrev KperpPt : Type := {x : F6 // polarMinus x sig0 = 0 ∧ polarMinus x tau0 = 0}

theorem card_KperpPt : Nat.card KperpPt = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem prK_smul_mul {g₁ : OmG} (h₁ : g₁ ∈ Eτ) (y : F6) :
    prK (g₁ • prK y) = prK (g₁ • y) := by
  have h : g₁ • (y + polarMinus y sig0 • tau0) = g₁ • y + polarMinus y sig0 • tau0 := by
    rw [smul_add, smul_comm_F6, Eτ_fix_tau h₁]
  have : prK y = y + polarMinus y sig0 • tau0 := rfl
  rw [this, h, prK_add_smul_tau]

@[instance_reducible] noncomputable def actW : MulAction ↥Eτ KperpPt where
  smul g x := ⟨prK (g.1 • x.1), by
    have hg := Eτ_fix_tau g.2
    have h1 : polarMinus (g.1 • x.1) tau0 = 0 := by
      have := pm_act g.1 x.1 tau0
      rw [hg] at this
      rw [this]
      exact x.2.2
    exact prK_mem _ h1⟩
  one_smul x := Subtype.ext (by
    show prK ((1 : ↥Eτ).1 • x.1) = x.1
    rw [show ((1 : ↥Eτ) : OmG) = 1 from rfl, one_smul]
    exact prK_eq_self x.2.1)
  mul_smul g₁ g₂ x := Subtype.ext (by
    show prK ((g₁ * g₂).1 • x.1) = prK (g₁.1 • prK (g₂.1 • x.1))
    rw [prK_smul_mul g₁.2]
    rw [show ((g₁ * g₂ : ↥Eτ) : OmG) = g₁.1 * g₂.1 from rfl, mul_smul])

theorem exists_fixed_Kperp :
    ∃ x : F6, x ≠ 0 ∧ polarMinus x sig0 = 0 ∧ polarMinus x tau0 = 0 ∧
      ∀ g ∈ Eτ, prK (g • x) = x := by
  letI : MulAction ↥Eτ KperpPt := actW
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := isPGroup_Eτ.card_modEq_card_fixedPoints (α := KperpPt)
  rw [card_KperpPt] at hmod
  let z0 : KperpPt := ⟨0, pm_zero_left _, pm_zero_left _⟩
  have hz0 : z0 ∈ fixedPoints ↥Eτ KperpPt := by
    intro g
    refine Subtype.ext ?_
    show prK (g.1 • (0 : F6)) = 0
    rw [smul_zero, prK_zero]
  have hpos : 0 < Nat.card (fixedPoints ↥Eτ KperpPt) := by
    haveI : Nonempty (fixedPoints ↥Eτ KperpPt) := ⟨⟨z0, hz0⟩⟩
    exact Nat.card_pos
  have hgt : 1 < Nat.card (fixedPoints ↥Eτ KperpPt) := by
    unfold Nat.ModEq at hmod
    omega
  haveI : Nontrivial (fixedPoints ↥Eτ KperpPt) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨y, hy⟩ := exists_ne (⟨z0, hz0⟩ : fixedPoints ↥Eτ KperpPt)
  refine ⟨y.1.1, ?_, y.1.2.1, y.1.2.2, fun g hg => ?_⟩
  · intro h0
    apply hy
    exact Subtype.ext (Subtype.ext h0)
  · exact congrArg Subtype.val (y.2 ⟨g, hg⟩)

def Ysub : Submodule (ZMod 2) F6 where
  carrier := {x | polarMinus x tau0 = 0 ∧ ∀ g ∈ Eτ, g • x - x = 0 ∨ g • x - x = tau0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨by rw [pm_add_left, hx1, hy1, add_zero], fun g hg => ?_⟩
    have e : g • (x + y) - (x + y) = (g • x - x) + (g • y - y) := by
      rw [smul_add]
      abel
    rw [e]
    rcases hx2 g hg with h | h <;> rcases hy2 g hg with h' | h' <;> rw [h, h'] <;>
      simp [tau0_add_tau0]
  zero_mem' := ⟨pm_zero_left _, fun g _ => Or.inl (by simp)⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨by simp [pm_zero_left], fun g _ => Or.inl (by simp)⟩
    · rw [one_smul]
      exact ⟨hx1, hx2⟩

theorem mem_Ysub {x : F6} : x ∈ Ysub ↔
    polarMinus x tau0 = 0 ∧ ∀ g ∈ Eτ, g • x - x = 0 ∨ g • x - x = tau0 := Iff.rfl

theorem Ysub_smul_P2 {h : OmG} (hh : h ∈ P2) {y : F6} (hy : y ∈ Ysub) : h • y ∈ Ysub := by
  have ht : h • tau0 = tau0 := (mem_P2.1 hh).2
  rw [mem_Ysub] at hy ⊢
  refine ⟨?_, fun g hg => ?_⟩
  · have := pm_act h y tau0
    rw [ht] at this
    rw [this, hy.1]
  · have hg' : h⁻¹ * g * h ∈ Eτ := by
      have := eich_conj_P2 hg (inv_mem hh)
      rwa [inv_inv] at this
    have e : g • (h • y) - h • y = h • ((h⁻¹ * g * h) • y - y) := by
      rw [smul_sub]
      simp [mul_smul]
    rw [e]
    rcases hy.2 _ hg' with h0 | h0 <;> rw [h0]
    · left
      exact smul_zero h
    · right
      exact ht

def Wsub : Submodule (ZMod 2) F6 := Ysub ⊔ Submodule.span (ZMod 2) {sig0}

theorem sig0_mem_Wsub : sig0 ∈ Wsub :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem tau0_mem_Ysub : tau0 ∈ Ysub := by
  rw [mem_Ysub]
  refine ⟨polarMinus_self _, fun g hg => Or.inl ?_⟩
  rw [Eτ_fix_tau hg, sub_self]

theorem tau0_mem_Wsub : tau0 ∈ Wsub := Submodule.mem_sup_left tau0_mem_Ysub

theorem Wsub_smul_P2 : ∀ g : OmG, g • sig0 = sig0 → g • tau0 = tau0 → ∀ w ∈ Wsub, g • w ∈ Wsub := by
  intro g hs ht w hw
  have hgP : g ∈ P2 := mem_P2.2 ⟨hs, ht⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  refine Submodule.mem_sup.mpr ⟨g • y, Ysub_smul_P2 hgP hy, g • (c • sig0), ?_, (smul_add g y _).symm⟩
  rw [smul_comm_F6, hs]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem sub_of_prK {a b : F6} (h : prK a = b) : a - b = 0 ∨ a - b = tau0 := by
  unfold prK at h
  rcases zmod2_cases (polarMinus a sig0) with hc | hc <;> rw [hc] at h
  · left
    rw [zero_smul, add_zero] at h
    rw [h, sub_self]
  · right
    rw [one_smul] at h
    rw [← h, F6_sub_eq_add, ← add_assoc, F6_add_self, zero_add]

theorem F6_cancel : ∀ a b : F6, b + (a + b) = a := by decide +kernel

theorem F6_add_cancel : ∀ a b : F6, (a + b) + b = a := by decide +kernel

theorem eq_add_of_sub {a b t : F6} (h : a - b = t) : a = b + t := by
  rw [F6_sub_eq_add] at h
  have := F6_cancel a b
  rw [h] at this
  exact this.symm

theorem Eτ_trivial_perp {g : OmG} (hg : g ∈ Eτ) {x : F6} (hx : polarMinus x tau0 = 0) :
    g • x - x = 0 ∨ g • x - x = tau0 := by
  obtain ⟨x₀, hx0, hx0s, hx0t, hfix⟩ := exists_fixed_Kperp
  have hx0Y : x₀ ∈ Ysub := by
    rw [mem_Ysub]
    exact ⟨hx0t, fun g hg => sub_of_prK (hfix g hg)⟩
  have hx0W : x₀ ∈ Wsub := Submodule.mem_sup_left hx0Y
  have htop : Wsub = ⊤ := by
    rcases om_pair_irred sig0_mem_Wsub tau0_mem_Wsub Wsub_smul_P2 with h | h
    · exfalso
      rw [h] at hx0W
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx0W
      have key : ∀ a b : ZMod 2, polarMinus (a • sig0 + b • tau0) sig0 = 0 →
          polarMinus (a • sig0 + b • tau0) tau0 = 0 → a • sig0 + b • tau0 = 0 := by
        decide +kernel
      rw [← hab] at hx0s hx0t
      exact hx0 (by rw [← hab]; exact key a b hx0s hx0t)
    · exact h
  have hx' : x ∈ Wsub := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c = 0 := by
    have := congrArg (fun v => polarMinus v tau0) hyz
    simp only [pm_add_left, pm_smul_left, hy.1, polarMinus_sig0_tau0, hx] at this
    simpa using this
  rw [hc, zero_smul, add_zero] at hyz
  rw [← hyz]
  exact hy.2 g hg

theorem key_scalar : ∀ y w : F6, polarMinus w tau0 = 0 → ∀ c : ZMod 2,
    polarMinus (y + c • tau0) (sig0 + w) = polarMinus y sig0 → c = polarMinus y w := by
  decide +kernel

theorem eich_final : ∀ x w : F6, polarMinus x tau0 = 1 → polarMinus w tau0 = 0 →
    qMinus w + polarMinus sig0 w = 0 →
    ((x + sig0) + polarMinus (x + sig0) w • tau0) + (sig0 + w) =
      x + polarMinus x tau0 • w + (polarMinus x w + qMinus w * polarMinus x tau0) • tau0 := by
  decide +kernel

theorem scalar_q : ∀ a b c : ZMod 2, a = a + b + c → b + c = 0 := by decide

theorem Eτ_eq_eichOm {g : OmG} (hg : g ∈ Eτ) :
    ∃ w, polarMinus w tau0 = 0 ∧ g = eichOm w := by
  have hgt : g • tau0 = tau0 := Eτ_fix_tau hg
  set w₀ : F6 := g • sig0 + sig0 with hw₀
  have hgs : g • sig0 = sig0 + w₀ := by
    rw [hw₀, F6_cancel]
  have hB : polarMinus (g • sig0) tau0 = 1 := by
    have := pm_act g sig0 tau0
    rw [hgt, polarMinus_sig0_tau0] at this
    exact this
  have hw0 : polarMinus w₀ tau0 = 0 := by
    rw [hw₀, pm_add_left, hB, polarMinus_sig0_tau0]
    decide
  have hq : qMinus w₀ + polarMinus sig0 w₀ = 0 := by
    have h := qMinus_add sig0 w₀
    have e : qMinus (g • sig0) = qMinus sig0 := qMinus_apply_of_mem g.2 sig0
    rw [← hgs, e] at h
    exact scalar_q _ _ _ h
  have key1 : ∀ y : F6, polarMinus y tau0 = 0 → g • y = y + polarMinus y w₀ • tau0 := by
    intro y hy
    have hiso := pm_act g y sig0
    rw [hgs] at hiso
    have hcase : ∃ c : ZMod 2, g • y = y + c • tau0 := by
      rcases Eτ_trivial_perp hg hy with h | h
      · exact ⟨0, by rw [zero_smul, add_zero]; exact sub_eq_zero.mp h⟩
      · exact ⟨1, by rw [one_smul]; exact eq_add_of_sub h⟩
    obtain ⟨c, hc⟩ := hcase
    rw [hc] at hiso ⊢
    rw [key_scalar y w₀ hw0 c hiso]
  have key2 : ∀ x : F6, g • x = eichOm w₀ • x := by
    intro x
    rw [eichOm_smul hw0 x]
    rcases zmod2_cases (polarMinus x tau0) with h0 | h1
    · rw [key1 x h0, h0]
      simp
    · have hy : polarMinus (x + sig0) tau0 = 0 := by
        rw [pm_add_left, h1, polarMinus_sig0_tau0]
        decide
      have e : g • x = g • (x + sig0) + g • sig0 := by
        rw [← smul_add, F6_add_cancel]
      rw [e, key1 _ hy, hgs]
      exact eich_final x w₀ h1 hw0 hq
  exact ⟨w₀, hw0, Subtype.ext (LinearEquiv.ext fun x => key2 x)⟩

theorem eichprK_vec : ∀ x w : F6, polarMinus w tau0 = 0 →
    x + polarMinus x tau0 • prK w + (polarMinus x (prK w) + qMinus (prK w) * polarMinus x tau0) •
        tau0 =
      x + polarMinus x tau0 • w + (polarMinus x w + qMinus w * polarMinus x tau0) • tau0 := by
  decide +kernel

theorem eichOm_prK {w : F6} (hw : polarMinus w tau0 = 0) : eichOm (prK w) = eichOm w := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  show eichOm (prK w) • x = eichOm w • x
  rw [eichOm_smul (prK_mem w hw).2 x, eichOm_smul hw x]
  exact eichprK_vec x w hw

theorem Eτ_eq_eichOm_K {g : OmG} (hg : g ∈ Eτ) : ∃ k ∈ Kperp, g = eichOm k := by
  obtain ⟨w, hw, rfl⟩ := Eτ_eq_eichOm hg
  exact ⟨prK w, prK_mem w hw, (eichOm_prK hw).symm⟩

theorem hypOmNoAlt : HypOmNoAlt := by
  intro F hmem hadd1 hadd2 halt hP g₁ hg₁ g₂ hg₂
  obtain ⟨k₁, hk₁, rfl⟩ := Eτ_eq_eichOm_K hg₁
  obtain ⟨k₂, hk₂, rfl⟩ := Eτ_eq_eichOm_K hg₂
  have hE : ∀ k ∈ Kperp, eichOm k ∈ Eτ := fun k hk => eichOm_mem_Eτ' hk.2
  refine om_alt_zero (fun v w => F (eichOm v) (eichOm w)) ?_ ?_ ?_ ?_ ?_ k₁ hk₁ k₂ hk₂
  · intro v₁ hv₁ v₂ hv₂ w hw
    show F (eichOm (v₁ + v₂)) (eichOm w) = F (eichOm v₁) (eichOm w) + F (eichOm v₂) (eichOm w)
    rw [← eichOm_mul hv₁ hv₂]
    exact hadd1 _ (hE _ hv₁) _ (hE _ hv₂) _ (hE _ hw)
  · intro v hv w₁ hw₁ w₂ hw₂
    show F (eichOm v) (eichOm (w₁ + w₂)) = F (eichOm v) (eichOm w₁) + F (eichOm v) (eichOm w₂)
    rw [← eichOm_mul hw₁ hw₂]
    exact hadd2 _ (hE _ hv) _ (hE _ hw₁) _ (hE _ hw₂)
  · intro v hv
    exact halt _ (hE _ hv)
  · intro v hv w hw
    exact hmem _ (hE _ hv) _ (hE _ hw)
  · intro g hg v hv w hw
    have hgP : g ∈ P2 := hg
    show F (eichOm (g • v)) (eichOm (g • w)) = g • F (eichOm v) (eichOm w)
    rw [← conj_eichOm hgP hv.2, ← conj_eichOm hgP hw.2]
    exact hP g hgP _ (hE _ hv) _ (hE _ hw)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
