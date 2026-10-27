module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightBasic
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le_card {B R : Subgroup G} {e : G} (h : ∀ b ∈ B, ⁅e, b⁆ ∈ R) :
    (Subgroup.centralizer ({e} : Set G)).relIndex B ≤ Nat.card R := by
  classical
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_le_card_of_injective
    (fun q : B ⧸ (Subgroup.centralizer ({e} : Set G)).subgroupOf B =>
      (⟨⁅e, ((Quotient.out q : B) : G)⁆, h _ (Quotient.out q).2⟩ : R)) fun q₁ q₂ hq => ?_
  set b₁ : B := Quotient.out q₁ with hb₁
  set b₂ : B := Quotient.out q₂ with hb₂
  have hEq : e * (b₁ : G) * e⁻¹ * (b₁ : G)⁻¹ = e * (b₂ : G) * e⁻¹ * (b₂ : G)⁻¹ := by
    have := congrArg Subtype.val hq
    simpa only [commutatorElement_def] using this
  have h1 : (b₁ : G) * e⁻¹ * (b₁ : G)⁻¹ = (b₂ : G) * e⁻¹ * (b₂ : G)⁻¹ := by
    refine mul_left_cancel (a := e) ?_
    simpa only [mul_assoc] using hEq
  have h2 : e⁻¹ * ((b₁ : G)⁻¹ * b₂) = ((b₁ : G)⁻¹ * b₂) * e⁻¹ := by
    calc e⁻¹ * ((b₁ : G)⁻¹ * b₂) = (b₁ : G)⁻¹ * ((b₁ : G) * e⁻¹ * (b₁ : G)⁻¹) * b₂ := by group
      _ = (b₁ : G)⁻¹ * ((b₂ : G) * e⁻¹ * (b₂ : G)⁻¹) * b₂ := by rw [h1]
      _ = ((b₁ : G)⁻¹ * b₂) * e⁻¹ := by group
  have h3 : e * ((b₁ : G)⁻¹ * b₂) = ((b₁ : G)⁻¹ * b₂) * e := by
    have := (show Commute e⁻¹ ((b₁ : G)⁻¹ * b₂) from h2).inv_left
    rwa [inv_inv] at this
  have h4 : (b₁⁻¹ * b₂ : B) ∈ (Subgroup.centralizer ({e} : Set G)).subgroupOf B := by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using h3
  have h5 : (b₁ : B ⧸ (Subgroup.centralizer ({e} : Set G)).subgroupOf B) = b₂ :=
    QuotientGroup.eq.2 h4
  rw [hb₁, hb₂] at h5
  simpa using h5

theorem commutator_eB_le {A V₀' E F B : Subgroup G} (hV : V₀' ≤ A)
    (h : ∀ e ∈ E, (∀ b ∈ B, ⁅e, b⁆ ∈ F) → ∀ a ∈ A, ⁅e, a⁆ ∈ V₀') :
    ⁅A, eB E F B⁆ ≤ V₀' := by
  have key : ∀ x : G, (∀ a ∈ A, ⁅x, a⁆ ∈ V₀') → ∀ v ∈ V₀', x * v * x⁻¹ ∈ V₀' := by
    intro x hx v hv
    have e : x * v * x⁻¹ = ⁅x, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V₀'.mul_mem (hx v (hV hv)) hv
  let S : Subgroup G :=
    { carrier := {z | ∀ a ∈ A, ⁅z, a⁆ ∈ V₀'}
      one_mem' := fun a _ => by rw [commutatorElement_one_left]; exact V₀'.one_mem
      mul_mem' := fun {x y} hx hy a ha => by
        have eq : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
          simp only [commutatorElement_def]
          group
        rw [eq]
        exact V₀'.mul_mem (key x hx _ (hy a ha)) (hx a ha)
      inv_mem' := fun {x} hx a ha => by
        have hxn : x ∈ normalizer (V₀' : Set G) := E1.mem_normalizer_of_conj_mem (key x hx)
        have eq : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxn) ⁅x, a⁆⁻¹).1
          (V₀'.inv_mem (hx a ha))
        rw [eq]
        simpa using h1 }
  have hle : eB E F B ≤ S := (Subgroup.closure_le S).2 fun e he => h e he.1 he.2
  refine Subgroup.commutator_le.2 fun a ha z hz => ?_
  have h1 : ⁅z, a⁆ ∈ V₀' := hle hz a ha
  rw [← commutatorElement_inv]
  exact V₀'.inv_mem h1

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem two_lt_rMV (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) : (2 : ℕ∞) < rMV D.M V := by
  have h1 : 2 < mBar D.M V₀ V c.setting.isElemAbelian := by have := c.two_lt_mBar; omega
  have h2 := h162 D V₀ V c.setting c.ne_bot h1
  refine lt_of_lt_of_le ?_ h2
  have h3 := c.two_lt_mBar
  exact_mod_cast (by omega : 2 < mBar D.M V₀ V c.setting.isElemAbelian + mSub V₀)

theorem comm_le_V₀_of_card_le_two (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) {g : G}
    {E F B : Subgroup G} (hE : IsElemAbelian 2 E)
    (hAE : conjSubgroup V g ≤ normalizer (E : Set G))
    (hB : B ∈ E3.gammaSet V 1 (conjSubgroup V g)) (hcard : Nat.card ↥(commEB E F B) ≤ 2) :
    ⁅conjSubgroup V g, eB E F B⁆ ≤ conjSubgroup V₀ g := by
  obtain ⟨hBA, hmB⟩ := (c.mem_gammaSet_one_iff).1 hB
  refine commutator_eB_le (E3.conjSubgroup_mono_left g c.V₀_le_V) fun e he hF a ha => ?_
  have hcomm : ∀ b ∈ B, ⁅e, b⁆ ∈ commEB E F B := fun b hb =>
    Subgroup.commutator_mem_commutator (mem_eB_of he hF) hb
  have hidx : (Subgroup.centralizer ({e} : Set G)).relIndex B ≤ 2 :=
    (relIndex_centralizer_le_card hcomm).trans hcard
  have hm1 : E3.mQuot B (B ⊓ Subgroup.centralizer ({e} : Set G)) ≤ 1 := by
    have h1 : (B ⊓ Subgroup.centralizer ({e} : Set G)).relIndex B =
        (Subgroup.centralizer ({e} : Set G)).relIndex B := Subgroup.inf_relIndex_left _ _
    have h0 : (Subgroup.centralizer ({e} : Set G)).relIndex B ≠ 0 := E3.relIndex_ne_zero' B _
    unfold E3.mQuot
    rw [h1]
    generalize (Subgroup.centralizer ({e} : Set G)).relIndex B = n at hidx h0 ⊢
    interval_cases n <;> simp
  have hm2 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer ({e} : Set G))
      ≤ 2 := by
    have h1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer ({e} : Set G))
        ≤ E3.mQuot (conjSubgroup V g) (B ⊓ Subgroup.centralizer ({e} : Set G)) :=
      E3.mQuot_mono (inf_le_inf_right _ hBA)
    have h2 := E3.mQuot_add (V := conjSubgroup V g)
      (U := B ⊓ Subgroup.centralizer ({e} : Set G)) (U' := B) inf_le_left hBA
    omega
  have hVg := E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g
  have hMnormg : normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]
  have hM₀g : conjSubgroup D.M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g c.setting.pair.le_normalizer₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hr : (2 : ℕ∞) < rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
    rw [rMV_conj c.setting.normalizer_eq g]
    exact c.two_lt_rMV h162
  have hmb : (2 : ℕ∞) < mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg := by
    rw [mBar_conj D.M V₀ V c.setting.isElemAbelian c.V₀_le_V c.setting.pair.le_normalizer
      c.setting.pair.le_normalizer₀ g]
    exact_mod_cast c.two_lt_mBar
  have hlt : (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer ({e} : Set G))
      : ℕ∞) + ((0 : ℕ) : ℕ∞) <
      min (rMV (conjSubgroup D.M g) (conjSubgroup V g))
        (mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg : ℕ∞) := by
    rw [Nat.cast_zero, add_zero]
    exact lt_min (lt_of_le_of_lt (by exact_mod_cast hm2) hr)
      (lt_of_le_of_lt (by exact_mod_cast hm2) hmb)
  have h14 := commutator_le_inf_of_mQuot_add_lt (M := conjSubgroup D.M g)
    (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (A := conjSubgroup V g)
    (B := conjSubgroup V g ⊓ Subgroup.centralizer ({e} : Set G)) (E := E) hVg
    (E3.conjSubgroup_mono_left g c.V₀_le_V) hMnormg.ge hM₀g le_rfl
    (i := 0) (E3.mQuot_self _) inf_le_left hAE hE.isPGroup hlt
  have heC : e ∈ E ⊓ Subgroup.centralizer
      ((conjSubgroup V g ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
    refine ⟨he, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hy.2
  exact (Subgroup.mem_inf.1 (h14 (Subgroup.commutator_mem_commutator heC ha))).2

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
