module

public import CFSG.Quasithin.EmptyFaithful.S146zNCount
public import CFSG.Quasithin.Background.C1PackS1461Five
public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Quasithin.Background.A1cA133Three

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Mutual

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_mem_pCoreOf_of_mutual {P E : Subgroup G} (hE : IsPGroup 2 E)
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) (hPE : P ≤ Subgroup.normalizer (E : Set G)) :
    ∀ e ∈ E, ∀ k ∈ P, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 P := by
  intro e he k hk
  have hN : P ⊓ E ≤ pCoreOf 2 P := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hE.to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hPE hx⟩
  refine hN ⟨?_, ?_⟩
  · exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEP he) k).mp hk) (P.inv_mem hk)
  · have h1 : k * e⁻¹ * k⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hPE hk) e⁻¹).mp (E.inv_mem he)
    have e1 : e * k * e⁻¹ * k⁻¹ = e * (k * e⁻¹ * k⁻¹) := by group
    rw [e1]
    exact E.mul_mem he h1

end Mutual

section Lemma1462

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.Z_le_commutator_of_mem_cComp (S : Setting146 G T M) (c19 : Conc14619 T M)
    {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) : Zz ≤ ⁅uOfL22 T M, K⁆ := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have h5 := stage1461Five G T M S (mcOf T) hG
  have hX1 : K ≠ ⊥ := ne_bot_of_mem_cComp hK
  have hX2 : oTwoUpper K = K := oTwoUpper_eq_of_perfect_F9 (perfect_of_mem_cComp hK)
  have hXF : K ≤ oTwoFstarIn (mcOf T) := le_oTwoFstarIn_of_mem_cComp (c19 (mcOf T) hG).1 hK
  have hQX : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (K : Set G) :=
    P134.pCoreOf_le_normalizer_of_mem_cComp hK
  exact S.lemma_14_6_2 hG h5 hX1 hX2 hXF hQX

end Lemma1462

end CFSG.Quasithin.ThreeD

namespace CFSG.Quasithin.ThreeC

section Submod

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem CCtx.submodule_cases (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {W : Subgroup G}
    (hZW : Zz ≤ W) (hWU : W ≤ U₁ ⊔ U₂) (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    W = Zz ∨ W = U₁ ∨ W = U₂ ∨ W = U₁ ⊔ U₂ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have hN₁₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy => hcommU x (c.hU₁U hx) y (c.hU₂U hy)
  have hdec : ∀ w ∈ U₁ ⊔ U₂, ∃ a ∈ U₁, ∃ b ∈ U₂, w = a * b := by
    intro w hw
    have hw' : w ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₁₂] at hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    exact ⟨a, ha, b, hb, rfl⟩
  have hKinf₁ : K ≤ Subgroup.normalizer ((W ⊓ U₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW hk, c.hSec.KU hk⟩
  have hKinf₂ : K ≤ Subgroup.normalizer ((W ⊓ U₂ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW hk, c.le_normalizer_U₂ hk⟩
  have h1 := c.hSec.irr (W ⊓ U₁) (le_inf hZW c.hSec.le) inf_le_right hKinf₁
  have h2 := c.irr₂ (le_inf hZW c.hZU₂) inf_le_right hKinf₂
  have hZU₁ := c.hSec.le
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    left
    have hcomW : ∀ x ∈ W, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy =>
      hcommU x ((sup_le c.hU₁U c.hU₂U) (hWU hx)) y (c.hU₂U hy)
    set V := W ⊔ U₂ with hV
    have hZV : Zz ≤ V := hZW.trans le_sup_left
    have hVU : V ≤ U₁ ⊔ U₂ := sup_le hWU le_sup_right
    have hKV : K ≤ Subgroup.normalizer (V : Set G) := by
      intro k hk
      apply mem_normalizer_of_conjSub_eq
      rw [hV, conjSub_sup, conjSub_eq_of_mem_normalizer (hKW hk),
        conjSub_eq_of_mem_normalizer (c.le_normalizer_U₂ hk)]
    have hKVU₁ : K ≤ Subgroup.normalizer ((V ⊓ U₁ : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKV hk, c.hSec.KU hk⟩
    rcases c.hSec.irr (V ⊓ U₁) (le_inf hZV hZU₁) inf_le_right hKVU₁ with hv | hv
    ·
      have hVU₂ : V ≤ U₂ := by
        intro v hv'
        obtain ⟨a, ha, b, hb, rfl⟩ := hdec v (hVU hv')
        have haV : a ∈ V := by
          have := V.mul_mem hv' (V.inv_mem ((show U₂ ≤ V from le_sup_right) hb))
          simpa using this
        have : a ∈ V ⊓ U₁ := ⟨haV, ha⟩
        rw [hv] at this
        exact U₂.mul_mem (c.hZU₂ this) hb
      have hWU₂ : W ≤ U₂ := le_sup_left.trans hVU₂
      rw [← h2]
      exact (inf_eq_left.mpr hWU₂).symm
    ·
      exfalso
      have hU₁V : U₁ ≤ V := inf_eq_right.mp hv
      have hVeq : V = U₁ ⊔ U₂ := le_antisymm hVU (sup_le hU₁V le_sup_right)
      obtain ⟨hc1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W U₂ hcomW
      rw [← hV, h2] at hc1
      obtain ⟨hc2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
        (fun x hx y hy => hcommU x (c.hU₁U hx) y (c.hU₂U hy))
      rw [c.inf_U₂_eq] at hc2
      have hcard2 : Nat.card U₂ = Nat.card U₁ := by rw [c.hU₂, natCard_conjSub_eq]
      rw [← hVeq] at hc2
      have hZpos : 0 < Nat.card Zz := Nat.card_pos
      have hcW : Nat.card W = Nat.card U₁ := by
        have : Nat.card W * Nat.card U₂ = Nat.card U₁ * Nat.card U₂ := hc1.symm.trans hc2
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
      rcases c.sub_eq_or S hZW hWU hKW hcW with hW | hW
      · rw [hW] at h1
        have hU₁Z : U₁ = Zz := (inf_idem U₁).symm.trans h1
        have h8 := c.hSec.card
        rw [← hU₁Z, Subgroup.relIndex_self] at h8
        omega
      · rw [hW] at h2
        have hU₂Z : U₂ = Zz := (inf_idem U₂).symm.trans h2
        have hle : U₂ ≤ U₁ := hU₂Z.le.trans hZU₁
        exact c.ne_U₂ (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2])).symm
  ·
    right; right; left
    refine le_antisymm ?_ (inf_eq_right.mp h2)
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w (hWU hw)
    have hbW : b ∈ W := (inf_eq_right.mp h2) hb
    have haW : a ∈ W := by
      have := W.mul_mem hw (W.inv_mem hbW)
      simpa using this
    have : a ∈ W ⊓ U₁ := ⟨haW, ha⟩
    rw [h1] at this
    exact U₂.mul_mem (c.hZU₂ this) hb
  ·
    right; left
    refine le_antisymm ?_ (inf_eq_right.mp h1)
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w (hWU hw)
    have haW : a ∈ W := (inf_eq_right.mp h1) ha
    have hbW : b ∈ W := by
      have := W.mul_mem (W.inv_mem haW) hw
      simpa using this
    have : b ∈ W ⊓ U₂ := ⟨hbW, hb⟩
    rw [h2] at this
    exact U₁.mul_mem ha (hZU₁ this)
  ·
    right; right; right
    exact le_antisymm hWU (sup_le (inf_eq_right.mp h1) (inf_eq_right.mp h2))

end Submod

end CFSG.Quasithin.ThreeC
