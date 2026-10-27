module

public import CFSG.LocalAnalysis.StandardType.GGRCCardJoin
public import CFSG.LocalAnalysis.StandardType.GGRCSmallOfCard
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_finrank_le_of_fix {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x : G} (hx : x ^ p = 1) {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hfix : ∀ b : Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers x) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let W : Submodule (ZMod p) (Module.Dual (ZMod p) V) := Submodule.span (ZMod p) (Set.range α)
  have hker : ∀ w ∈ W.dualCoannihilator, ((Additive.toMul (ι.symm w) : Bs) : G) ∈
      Subgroup.zpowers x := by
    intro w hw
    refine hfix _ fun i => ?_
    have hαi : α i w = 0 :=
      (Submodule.mem_dualCoannihilator w).mp hw _ (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := hlin i w
    rw [hαi, zero_smul, sub_zero, ggLin_apply] at h1
    have h2 := congrArg ι.symm h1
    rw [AddEquiv.symm_apply_apply] at h2
    exact Additive.ofMul.injective (by rw [h2]; rfl)
  let e : W.dualCoannihilator → Subgroup.zpowers x := fun w => ⟨_, hker w.1 w.2⟩
  have he : Function.Injective e := by
    intro w w' hww
    have h0 : ((Additive.toMul (ι.symm w.1) : Bs) : G) =
        ((Additive.toMul (ι.symm w'.1) : Bs) : G) :=
      congrArg (fun z : Subgroup.zpowers x => (z : G)) hww
    have h1 : (Additive.toMul (ι.symm w.1) : Bs) = Additive.toMul (ι.symm w'.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  have hcard : Nat.card W.dualCoannihilator ≤ p := by
    refine (Nat.card_le_card_of_injective e he).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hx
  have hkerrank : Module.finrank (ZMod p) W.dualCoannihilator ≤ 1 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W.dualCoannihilator
    have h2 : p ^ Module.finrank (ZMod p) W.dualCoannihilator ≤ p ^ 1 := by
      rw [h1, pow_one]; exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hW : Module.finrank (ZMod p) W ≤ Fintype.card Λ := finrank_range_le_card (R := ZMod p) α
  have hV : Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
    rw [← Subspace.finrank_add_finrank_dualCoannihilator_eq W]
    omega
  exact hV

theorem ggRC_isTransvection_of_lin {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : MulAut ↥Bs)
    (h : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι φ)) = 1 ∧
      ∀ w, ggLin (p := p) ι φ (ggLin (p := p) ι φ w - w) = ggLin (p := p) ι φ w - w) :
    GGIsTransvection p φ := by
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  rw [ggIsTransvection_iff_ggLin ι φ]
  refine ⟨h.1, ?_⟩
  intro w hw
  rw [ggLinMove, LinearMap.mem_range] at hw
  obtain ⟨v, rfl⟩ := hw
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  exact h.2 v

private def l05nC2a_stabEquiv {G : Type*} [Group G] (S A : Subgroup G) :
    ↥(S.subgroupOf A) ≃ ↥(A ⊓ S) where
  toFun x := ⟨((x : ↥A) : G), (x : ↥A).2, x.2⟩
  invFun x := ⟨⟨(x : G), x.2.1⟩, x.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

theorem ggRC_card_join_le_of_orbit (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) (S : Set ↥Bs)
    (hS : ∀ a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, a ⟨x, hx⟩ ∈ S) :
    Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Nat.card S * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := by
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let pt : ↥Bs := ⟨x, hx⟩
  have hstab : Nat.card ↥(MulAction.stabilizer (↥A') pt) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := by
    have hstab_eq : Nat.card ↥(MulAction.stabilizer (↥A') pt) =
        Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) pt) := by
      rw [← MulAction.stabilizer_subgroupOf A' pt]
      exact Nat.card_congr
        (l05nC2a_stabEquiv (MulAction.stabilizer (MulAut ↥Bs) pt) A')
    rw [hstab_eq]
    exact hOrb G p B Bs x L D J y K hH hx
  let _ : Fintype ↥A' := Fintype.ofFinite ↥A'
  let _ : Fintype ↥(MulAction.orbit (↥A') pt) := Fintype.ofFinite ↥(MulAction.orbit (↥A') pt)
  let _ : Fintype ↥(MulAction.stabilizer (↥A') pt) :=
    Fintype.ofFinite ↥(MulAction.stabilizer (↥A') pt)
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A') pt
  simp only [← Nat.card_eq_fintype_card] at hOS
  change Nat.card ↥A' ≤ Nat.card S * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs))
  rw [← hOS]
  refine Nat.mul_le_mul ?_ hstab
  have hmem : ∀ o : ↥(MulAction.orbit (↥A') pt), o.1 ∈ S := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hb
    change b ∈ S
    rw [← ha]
    have hsa : (a : MulAut ↥Bs) pt ∈ S := hS (a : MulAut ↥Bs) a.2
    exact hsa
  refine Nat.card_le_card_of_injective
    (fun o : ↥(MulAction.orbit (↥A') pt) => (⟨o.1, hmem o⟩ : S)) ?_
  intro o o' h
  exact Subtype.ext (congrArg (fun z : S => (z : ↥Bs)) h)

theorem ggRC_small_of_card_II
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (ML : CoxeterMatrix Λ) (hWL : GGIsWeylMatrix ML) (h9 : 9 ≤ Fintype.card Λ)
    {Nj NU : ℕ} (hNU : NU = p ^ Fintype.card Λ)
    (hjoin : Nj ≤ NU * ((p - 1) * 6 * Nat.card ML.Group)) :
    8 * Nj < p ^ (Fintype.card Λ * (Fintype.card Λ - 1) / 2) := by
  have hW : Nat.card ML.Group ≤ 2 ^ Fintype.card Λ * (Fintype.card Λ).factorial ∨
      (Fintype.card Λ = 9 ∧ Nat.card ML.Group = 696729600) := by
    rcases ggRC_card_weyl_le ML hWL (by omega : 8 ≤ Fintype.card Λ) with h | ⟨hcard, hord⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hord⟩
  have harith := ggRC_arith hp hp2 h9 hW
  have hjoin' : Nj ≤ p ^ Fintype.card Λ * ((p - 1) * 6 * Nat.card ML.Group) := by
    rw [← hNU]
    exact hjoin
  calc
    8 * Nj ≤ 8 * (p ^ Fintype.card Λ * ((p - 1) * 6 * Nat.card ML.Group)) :=
      Nat.mul_le_mul_left 8 hjoin'
    _ < p ^ (Fintype.card Λ * (Fintype.card Λ - 1) / 2) := harith

end CFSG.StandardType
