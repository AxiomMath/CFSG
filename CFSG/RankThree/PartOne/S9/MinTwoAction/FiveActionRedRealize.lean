module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedSetup
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingModule

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36
  CFSG.RankThree.PartOne.Lifting36
open scoped IsMulCommutative commutatorElement

section Frattini

variable {G : Type*} [Group G]

theorem mem_inSubgroup_frattini_iff {P : Subgroup G} (y : ↥P) :
    (y : G) ∈ inSubgroup frattini P ↔ y ∈ frattini ↥P := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    subst this
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem mk_eq_iff {X D : Subgroup G} (hXD : X ≤ D)
    (hfr : X ⊓ inSubgroup frattini D = inSubgroup frattini X) (x y : ↥X) :
    (x : ↥X ⧸ frattini ↥X) = (y : ↥X ⧸ frattini ↥X) ↔
      ((⟨x, hXD x.2⟩ : ↥D) : ↥D ⧸ frattini ↥D) = ((⟨y, hXD y.2⟩ : ↥D) : ↥D ⧸ frattini ↥D) := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← mem_inSubgroup_frattini_iff,
    ← mem_inSubgroup_frattini_iff, ← hfr, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨(x⁻¹ * y).2, h⟩⟩

theorem mk_eq_one_iff {X D : Subgroup G} (hXD : X ≤ D)
    (hfr : X ⊓ inSubgroup frattini D = inSubgroup frattini X) (x : ↥X) :
    (x : ↥X ⧸ frattini ↥X) = 1 ↔ ((⟨x, hXD x.2⟩ : ↥D) : ↥D ⧸ frattini ↥D) = 1 := by
  rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, ← mem_inSubgroup_frattini_iff,
    ← mem_inSubgroup_frattini_iff, ← hfr, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

end Frattini

section Image

variable {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] {L D : Subgroup G}
  [Fact (IsPGroup q ↥D)]

@[expose] noncomputable def imageSub (hLD : L ≤ Subgroup.normalizer (D : Set G))
    {X : Subgroup G} (hLX : L ≤ Subgroup.normalizer (X : Set G)) :
    Subrepresentation (FRep q hLD) where
  toSubmodule := toSubmodule q ((X.subgroupOf D).map (QuotientGroup.mk' (frattini ↥D)))
  apply_mem_toSubmodule l w hw := by
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
    obtain ⟨y, hy, hyv⟩ := (mem_toSubmodule q _ _).mp hw
    have hyv' : v = (y : ↥D ⧸ frattini ↥D) := hyv.symm
    subst hyv'
    rw [FRep_apply_mk, mem_toSubmodule]
    refine ⟨conjHom hLD l y, ?_, rfl⟩
    show (l : G) * (y : G) * (l : G)⁻¹ ∈ X
    exact (Subgroup.mem_normalizer_iff.mp (hLX l.2) y).mp hy

theorem mem_imageSub (hLD : L ≤ Subgroup.normalizer (D : Set G))
    {X : Subgroup G} (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (w : Additive (↥D ⧸ frattini ↥D)) :
    w ∈ imageSub (q := q) hLD hLX ↔
      ∃ x : ↥D, (x : G) ∈ X ∧ Additive.ofMul (x : ↥D ⧸ frattini ↥D) = w := by
  change Additive.toMul w ∈ (X.subgroupOf D).map (QuotientGroup.mk' (frattini ↥D)) ↔ _
  constructor
  · rintro ⟨y, hy, hyw⟩
    exact ⟨y, hy, congrArg Additive.ofMul hyw⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end Image

section Realize

variable {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]

theorem exists_realization_of_atom (hq2 : q ≠ 2) {A D R : Subgroup G} [hDq : Fact (IsPGroup q ↥D)]
    (hR2 : IsPGroup 2 R) (hAord : ¬ q ∣ Nat.card A) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hLD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) (U : Subrepresentation (FRep q hLD))
    (hU : IsAtom U) :
    ∃ X : Subgroup G, X ≤ D ∧ R ⊔ A ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ inSubgroup frattini D = inSubgroup frattini X ∧
      (∀ x : ↥D, (x : G) ∈ X → Additive.ofMul (x : ↥D ⧸ frattini ↥D) ∈ U) ∧
      (∀ r : ↥(R ⊔ A), (r : G) ∈ Subgroup.centralizer (X : Set G) → ∀ u ∈ U,
        FRep q hLD r u = u) := by
  classical
  have hq : q.Prime := Fact.out
  let L : Subgroup G := R ⊔ A
  let _ := conjAction hLD
  let _ := SteinbergBY.frattiniQuotientAction ↥L ↥D
  have hLq : ¬ q ∣ Nat.card ↥L := not_dvd_card_sup hq hq2 hR2 hAord hAR
  let W : Subgroup (↥D ⧸ frattini ↥D) := toSubgroup q U.toSubmodule
  have hW1 : W ≠ ⊥ := fun h =>
    hU.1 (Subrepresentation.ext ((toSubgroup_eq_bot_iff q U.toSubmodule).mp h))
  have hWinv : ∀ l : ↥L, ∀ w ∈ W, l • w ∈ W :=
    toSubgroup_invariant q U.toSubmodule fun e w hw => U.apply_mem_toSubmodule e hw
  have hWirr : ∀ W' : Subgroup (↥D ⧸ frattini ↥D), W' ≤ W → (∀ l : ↥L, ∀ w ∈ W', l • w ∈ W') →
      W' = ⊥ ∨ W' = W := by
    intro W' hle hinv
    let V' : Subrepresentation (FRep q hLD) :=
      ⟨toSubmodule q W', fun l w hw => by
        obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
        have h1 : v ∈ W' := (mem_toSubmodule q W' _).mp hw
        have h2 := frattiniRep_apply (E := ↥L) (X := ↥D) q l v
        change frattiniRep (E := ↥L) (X := ↥D) q l (Additive.ofMul v) ∈ toSubmodule q W'
        rw [h2, mem_toSubmodule]
        exact hinv l v h1⟩
    have hV'U : V' ≤ U := fun w hw => hle ((mem_toSubmodule q W' w).mp hw)
    rcases hU.le_iff.mp hV'U with h0 | h1
    · left
      have h2 : toSubmodule q W' = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [← toSubgroup_toSubmodule q W', h2]
      exact (toSubgroup_eq_bot_iff q ⊥).mpr rfl
    · right
      have h2 : toSubmodule q W' = U.toSubmodule := congrArg Subrepresentation.toSubmodule h1
      rw [← toSubgroup_toSubmodule q W', h2]
  obtain ⟨X₀, hX₀inv, hX₀W, hX₀frat, -, hX₀C, -, -⟩ :=
    SteinbergBM.invariant_frattini_module_realization hq hDq.out hLq W hW1 hWinv hWirr
  have hsm : ∀ (l : ↥L) (x : ↥D), ((l • x : ↥D) : G) = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  let X : Subgroup G := X₀.map D.subtype
  have hXD : X ≤ D := Subgroup.map_subtype_le _
  have hmemX : ∀ x : ↥D, (x : G) ∈ X ↔ x ∈ X₀ := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by rwa [← Subtype.ext hyx], fun hx => ⟨x, hx, rfl⟩⟩
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_conj_mem fun c hc g hg => ?_
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨(⟨c, hc⟩ : ↥L) • x, hX₀inv ⟨c, hc⟩ x hx, rfl⟩
  have hΦX : inSubgroup frattini X = (X₀ ⊓ frattini ↥D).map D.subtype := by
    rw [inSubgroup_frattini_map' D.subtype D.subtype_injective X₀, hX₀frat]
    rfl
  have hXfrat : X ⊓ inSubgroup frattini D = inSubgroup frattini X := by
    rw [hΦX]
    show X₀.map D.subtype ⊓ (frattini ↥D).map D.subtype = _
    exact (Subgroup.map_inf X₀ (frattini ↥D) D.subtype D.subtype_injective).symm
  refine ⟨X, hXD, hLX, hXfrat, ?_, ?_⟩
  · intro x hx
    have h1 : (x : ↥D ⧸ frattini ↥D) ∈ W := by
      rw [← hX₀W]
      exact ⟨x, (hmemX x).mp hx, rfl⟩
    exact h1
  · intro r hr u hu
    have h1 : ∀ w ∈ W, r • w = w := by
      refine (hX₀C r).mp (fun x hx => ?_)
      apply Subtype.ext
      rw [hsm]
      have h2 := Subgroup.mem_centralizer_iff.mp hr (x : G) ((hmemX x).mpr hx)
      calc (r : G) * x * (r : G)⁻¹ = (x * r) * (r : G)⁻¹ := by rw [← h2]
        _ = x := by group
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = u := ⟨Additive.toMul u, rfl⟩
    have h3 := frattiniRep_apply (E := ↥L) (X := ↥D) q r v
    change frattiniRep (E := ↥L) (X := ↥D) q r (Additive.ofMul v) = Additive.ofMul v
    rw [h3, h1 v hu]

end Realize

end CFSG.RankThree.PartOne.FiveAction.Red
