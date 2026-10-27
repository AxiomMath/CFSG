module

public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.PartTwo.Sec4.E27.TwoLines
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofTransport

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

variable {X : Type} [Group X]

theorem aut_mul_conj_mul_inv (f : MulAut X) (g : X) :
    f * MulAut.conj g * f⁻¹ = MulAut.conj (f g) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem commute_conj_iff_fixes (hZ : Subgroup.center X = ⊥) (f : MulAut X) (l : X) :
    f * MulAut.conj l = MulAut.conj l * f ↔ f l = l := by
  have hinj := conj_injective_of_center_bot hZ
  constructor
  · intro h
    have h1 : MulAut.conj (f l) = MulAut.conj l := by
      rw [← aut_mul_conj_mul_inv, h]
      group
    exact hinj h1
  · intro h
    have h1 : f * MulAut.conj l * f⁻¹ = MulAut.conj l := by
      rw [aut_mul_conj_mul_inv, h]
    calc f * MulAut.conj l = (f * MulAut.conj l * f⁻¹) * f := by group
      _ = MulAut.conj l * f := by rw [h1]

variable [Finite X]

theorem seitzHyperGamma_eq_top_of_two_lines (hZ : Subgroup.center X = ⊥)
    {E : Subgroup (MulAut X)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    {f₁ f₂ : MulAut X} (hf₁E : f₁ ∈ E) (hf₂E : f₂ ∈ E) (hf₁ : f₁ ≠ 1) (hf₂ : f₂ ≠ 1)
    {L₁ L₂ : Subgroup X} (hfix₁ : ∀ l ∈ L₁, f₁ l = l) (hfix₂ : ∀ l ∈ L₂, f₂ l = l)
    (hpl₁ : L₁ ≤ Subgroup.closure {l | l ∈ L₁ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₁ ∧ x l = l})
    (hpl₂ : L₂ ≤ Subgroup.closure {l | l ∈ L₂ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₂ ∧ x l = l})
    (hgen : L₁ ⊔ L₂ = ⊤) : seitzHyperGamma 3 E = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine seitzHyperGamma_eq_top_of_hyperGen hZ E ?_
  have hmapL : ∀ (L : Subgroup X) (f : MulAut X), (∀ l ∈ L, f l = l) →
      ∀ y ∈ L.map (MulAut.conj : X →* MulAut X), f * y = y * f := by
    rintro L f hf _ ⟨l, hl, rfl⟩
    exact (commute_conj_iff_fixes hZ f l).2 (hf l hl)
  have hplane : ∀ (L : Subgroup X) (f : MulAut X),
      L ≤ Subgroup.closure {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x l = l} →
      L.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.closure
        {y | y ∈ L.map (MulAut.conj : X →* MulAut X) ∧
          ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x * y = y * x} := by
    intro L f hpl
    refine (Subgroup.map_mono hpl).trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨l, ⟨hl, x, hxE, hxf, hxl⟩, rfl⟩
    exact ⟨⟨l, hl, rfl⟩, x, hxE, hxf, (commute_conj_iff_fixes hZ x l).2 hxl⟩
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)
  refine hyperGen_of_two_lines (Y := MulAut X)
    (K := (MulAut.conj : X →* MulAut X).range) (p := 3) hE hc hf₁E hf₂E hf₁ hf₂
    (L₁ := L₁.map (MulAut.conj : X →* MulAut X)) (L₂ := L₂.map (MulAut.conj : X →* MulAut X))
    ?_ ?_ (hmapL L₁ f₁ hfix₁) (hmapL L₂ f₂ hfix₂) (hplane L₁ f₁ hpl₁) (hplane L₂ f₂ hpl₂) ?_
  · rintro _ ⟨l, -, rfl⟩
    exact ⟨l, rfl⟩
  · rintro _ ⟨l, -, rfl⟩
    exact ⟨l, rfl⟩
  · rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map]

@[expose] noncomputable def restrictAut (L : Subgroup X) (α : MulAut X) (h : ∀ l ∈ L, α l ∈ L)
    (h' : ∀ l ∈ L, α⁻¹ l ∈ L) : MulAut L where
  toFun l := ⟨α l, h l l.2⟩
  invFun l := ⟨α⁻¹ l, h' l l.2⟩
  left_inv l := Subtype.ext (by simp)
  right_inv l := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[expose] noncomputable def restrictHom (L : Subgroup X) (E : Subgroup (MulAut X))
    (hinv : ∀ e ∈ E, ∀ l ∈ L, e l ∈ L) : E →* MulAut L where
  toFun e := restrictAut L e (hinv e e.2) (hinv e⁻¹ (E.inv_mem e.2))
  map_one' := MulEquiv.ext fun l => Subtype.ext rfl
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext rfl

theorem coe_restrictHom (L : Subgroup X) (E : Subgroup (MulAut X))
    (hinv : ∀ e ∈ E, ∀ l ∈ L, e l ∈ L) (e : E) (l : L) :
    (restrictHom L E hinv e l : X) = (e : MulAut X) l := rfl

open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen in
theorem le_closure_fixed_of_plane (hA : Sec19.SeitzThreeLThreePi) {p m : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (h2 : 2 < p ^ m) (h4 : ¬ (p = 2 ∧ m = 2)) {L : Subgroup X}
    (hL : IsoLThreePi ↥L p m) {E : Subgroup (MulAut X)} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) (hinv : ∀ e ∈ E, ∀ l ∈ L, e l ∈ L) {f : MulAut X} (hfE : f ∈ E)
    (hf1 : f ≠ 1) (hfix : ∀ l ∈ L, f l = l)
    (hker : ∀ e ∈ E, (∀ l ∈ L, e l = l) → e ∈ Subgroup.zpowers f) :
    L ≤ Subgroup.closure {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x l = l} := by
  set ρ := restrictHom L E hinv with hρ
  have hf3 : f ^ 3 = 1 := hE.2 f hfE
  have hford : orderOf f = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hf3 hf1
  have hzE : Subgroup.zpowers f ≤ E := (Subgroup.zpowers_le).2 hfE
  let Stab : Subgroup (MulAut X) :=
    { carrier := {g | ∀ l ∈ L, g l = l}
      mul_mem' := fun {a b} ha hb l hl => by rw [MulAut.mul_apply, hb l hl, ha l hl]
      one_mem' := fun l _ => rfl
      inv_mem' := fun {a} ha l hl => by
        calc a⁻¹ l = a⁻¹ (a l) := by rw [ha l hl]
          _ = l := by simp }
  have hzStab : Subgroup.zpowers f ≤ Stab := (Subgroup.zpowers_le).2 hfix
  have hρ1 : ∀ e : E, ρ e = 1 ↔ ∀ l ∈ L, (e : MulAut X) l = l := by
    intro e
    constructor
    · intro h l hl
      have h1 : (ρ e ⟨l, hl⟩ : X) = l := by rw [h]; rfl
      exact (coe_restrictHom L E hinv e ⟨l, hl⟩).symm.trans h1
    · intro h
      exact MulEquiv.ext fun l => Subtype.ext (h l l.2)
  have hker' : ρ.ker = (Subgroup.zpowers f).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, hρ1, Subgroup.mem_subgroupOf]
    exact ⟨fun h => hker e e.2 h, fun h => hzStab h⟩
  have hkerCard : Nat.card ρ.ker = 3 := by
    rw [hker']
    have : Nat.card ((Subgroup.zpowers f).subgroupOf E) = Nat.card (Subgroup.zpowers f) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzE).toEquiv
    rw [this, Nat.card_zpowers, hford]
  have hrange : Nat.card ρ.range = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have h2 : Nat.card (E ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [hc, h2, hkerCard] at h1
    omega
  have hFel : IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨e₁, he₁⟩ := a.2
      obtain ⟨e₂, he₂⟩ := b.2
      apply Subtype.ext
      show (a : MulAut L) * b = b * a
      rw [← he₁, ← he₂, ← map_mul, ← map_mul]
      have := hE.1
      rw [mul_comm' e₁ e₂]
    · rintro _ ⟨e, rfl⟩
      rw [← map_pow]
      have h3 : e ^ 3 = 1 := Subtype.ext (hE.2 e e.2)
      rw [h3, map_one]
  have hcl := Sec19.SeitzScopeProof.closure_fixSet_of_lThreePi hA hm h2 hL h4 ρ.range hFel hrange
  intro l hl
  have h1 : (⟨l, hl⟩ : L) ∈ Subgroup.closure (fixSet ρ.range) := hcl ▸ Subgroup.mem_top _
  have h2' : l ∈ Subgroup.map L.subtype (Subgroup.closure (fixSet ρ.range)) := ⟨⟨l, hl⟩, h1, rfl⟩
  rw [MonoidHom.map_closure] at h2'
  refine (Subgroup.closure_mono ?_) h2'
  rintro _ ⟨⟨y, hy⟩, ⟨φ, ⟨e, rfl⟩, hφ1, hφy⟩, rfl⟩
  refine ⟨hy, e, e.2, ?_, ?_⟩
  · intro hmem
    exact hφ1 ((hρ1 e).2 (fun l hl => hzStab hmem l hl))
  · have := congrArg (fun a : L => (a : X)) hφy
    exact (coe_restrictHom L E hinv e ⟨y, hy⟩).symm.trans this

theorem seitzHyperGamma_eq_top_of_two_subfield_lines (hA : Sec19.SeitzThreeLThreePi) {p m : ℕ}
    [Fact p.Prime] (hm : 1 ≤ m) (h2 : 2 < p ^ m) (h4 : ¬ (p = 2 ∧ m = 2))
    (hZ : Subgroup.center X = ⊥) {E : Subgroup (MulAut X)} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) {f₁ f₂ : MulAut X} (hf₁E : f₁ ∈ E) (hf₂E : f₂ ∈ E)
    (hf₁ : f₁ ≠ 1) (hf₂ : f₂ ≠ 1) {L₁ L₂ : Subgroup X} (hL₁ : IsoLThreePi ↥L₁ p m)
    (hL₂ : IsoLThreePi ↥L₂ p m) (hinv₁ : ∀ e ∈ E, ∀ l ∈ L₁, e l ∈ L₁)
    (hinv₂ : ∀ e ∈ E, ∀ l ∈ L₂, e l ∈ L₂) (hfix₁ : ∀ l ∈ L₁, f₁ l = l)
    (hfix₂ : ∀ l ∈ L₂, f₂ l = l)
    (hker₁ : ∀ e ∈ E, (∀ l ∈ L₁, e l = l) → e ∈ Subgroup.zpowers f₁)
    (hker₂ : ∀ e ∈ E, (∀ l ∈ L₂, e l = l) → e ∈ Subgroup.zpowers f₂)
    (hgen : L₁ ⊔ L₂ = ⊤) : seitzHyperGamma 3 E = ⊤ :=
  seitzHyperGamma_eq_top_of_two_lines hZ hE hc hf₁E hf₂E hf₁ hf₂ hfix₁ hfix₂
    (le_closure_fixed_of_plane hA hm h2 h4 hL₁ hE hc hinv₁ hf₁E hf₁ hfix₁ hker₁)
    (le_closure_fixed_of_plane hA hm h2 h4 hL₂ hE hc hinv₂ hf₂E hf₂ hfix₂ hker₂) hgen

end CFSG.RankThree.PartTwo.Sec4.E27
