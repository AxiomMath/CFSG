module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPerm
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6aR_moves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ : Type} {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (U : Submodule (ZMod p) V) (hU : ∀ o, h o ∈ U)
    (A' : Subgroup (MulAut ↥Bs)) (hA' : A' = Subgroup.closure (Set.range φ)) :
    ∀ a ∈ A'.map (ggLin (p := p) ι), ∀ w, a w - w ∈ U := by
  intro a ha
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  rw [hA'] at hψ
  let Q : MulAut ↥Bs → Prop := fun ψ => ∀ w, ggLin (p := p) ι ψ w - w ∈ U
  have hgenQ : ∀ o : Option Λ, Q (φ o) := by
    intro o w
    have h1 := hφ o w
    rw [h1]
    have hsub : w - α o w • h o - w = -(α o w) • h o := by
      rw [sub_sub_cancel_left, ← neg_smul]
    rw [hsub]
    exact U.smul_mem _ (hU o)
  have honeQ : Q 1 := by
    intro w
    show ggLin (p := p) ι (1 : MulAut ↥Bs) w - w ∈ U
    rw [map_one]
    simpa using (Submodule.zero_mem U : (0 : V) ∈ U)
  have hmulQ : ∀ a b : MulAut ↥Bs, Q a → Q b → Q (a * b) := by
    intro a b ha hb w
    have h1 : ggLin (p := p) ι b w - w ∈ U := hb w
    have h2 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
        (ggLin (p := p) ι b w - w) ∈ U := ha (ggLin (p := p) ι b w - w)
    have h3 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) ∈ U := by
      have hsum : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) =
          (ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
            (ggLin (p := p) ι b w - w)) + (ggLin (p := p) ι b w - w) := by abel_nf
      rw [hsum]
      exact Submodule.add_mem _ h2 h1
    have h4 : ggLin (p := p) ι a w - w ∈ U := ha w
    have hmul : ggLin (p := p) ι a (ggLin (p := p) ι b w) - w =
        ggLin (p := p) ι a (ggLin (p := p) ι b w - w) + (ggLin (p := p) ι a w - w) := by
      rw [map_sub]
      abel_nf
    rw [map_mul, LinearEquiv.mul_apply, hmul]
    exact Submodule.add_mem _ h3 h4
  have hinvQ : ∀ a : MulAut ↥Bs, Q a → Q a⁻¹ := by
    intro a ha w
    have h := ha ((ggLin (p := p) ι a)⁻¹ w)
    have hw : w - (ggLin (p := p) ι a)⁻¹ w ∈ U := by simpa using h
    have hneg : (ggLin (p := p) ι a)⁻¹ w - w =
        -(w - (ggLin (p := p) ι a)⁻¹ w) := by abel_nf
    rw [map_inv, hneg]
    exact Submodule.neg_mem _ hw
  refine Subgroup.closure_induction (k := Set.range φ) (p := fun a _ => Q a) ?_ ?_ ?_ ?_ hψ
  · rintro x ⟨o, rfl⟩
    exact hgenQ o
  · exact honeQ
  · intro x y _ _ hx hy
    exact hmulQ x y hx hy
  · intro x _ hx
    exact hinvQ x hx

theorem ggIndep_card_A1 {p N : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : 5 ≤ N)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {z : G} (hz : z ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    {Λ : Type} [Fintype Λ] {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {A₁ : Subgroup (MulAut ↥Bs)} (hA₁ : A₁ = Subgroup.closure (Set.range φ))
    (e : Fin (N - 1) ≃ Λ)
    (F : GGIndepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨z, hz⟩))) :
    Nat.card ↥A₁ ≤ Nat.factorial N := by
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
  obtain ⟨ρ, hρswap, hρmem, -, -⟩ :=
    ggIndep_perm_embed (p := p) (N := N) hN F r hr
  have hmap : A₁.map (ggLin (p := p) ι) = Subgroup.closure (Set.range r) := by
    rw [hA₁, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, by simp [r]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
  have hcard_eq : Nat.card ↥A₁ = Nat.card ↥(A₁.map (ggLin (p := p) ι)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective A₁
      (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv
  have hle1 : Subgroup.closure (Set.range r) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨Equiv.swap (ggDepALeft N i) (ggDepARight N i), hρswap i⟩
  have hle2 : ρ.range ≤ Subgroup.closure (Set.range r) := by
    intro y hy
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hρmem σ
  have hρrange : Subgroup.closure (Set.range r) = ρ.range := le_antisymm hle1 hle2
  calc Nat.card ↥A₁
      = Nat.card ↥(A₁.map (ggLin (p := p) ι)) := hcard_eq
    _ = Nat.card ↥(Subgroup.closure (Set.range r)) := by rw [hmap]
    _ = Nat.card ↥(ρ.range) := by rw [hρrange]
    _ ≤ Nat.card (Equiv.Perm (Fin N)) :=
        Nat.card_le_card_of_surjective
          (fun σ : Equiv.Perm (Fin N) => (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range))
          (fun y => by
            obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp y.2
            exact ⟨σ, Subtype.ext hσ⟩)
    _ = Nat.factorial N := by rw [Nat.card_perm, Nat.card_fin]

theorem ggIndep_nt
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hNT : GGNoTransvection p Bs) {A' : Subgroup (MulAut ↥Bs)} (hA' : A' ≤ ggAutomizer ⊤ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} (hφ : ∀ i, φ i ∈ A') {t : MulAut ↥Bs} (ht : t ∈ A') :
    ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  classical
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgenL : ∀ i : Fin (N - 1), ggLin (p := p) ι (φ (e i)) ∈ A_V := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφ (e i), rfl⟩
  have hgenN : ggLin (p := p) ι t ∈ A_V := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
  have hle : Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t}) ≤ A_V := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · obtain ⟨i, rfl⟩ := hy
      exact hgenL i
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hgenN
  intro g hg hcond
  have hgA : g ∈ A_V := hle hg
  obtain ⟨ψ, hψA, hψeq⟩ := Subgroup.mem_map.mp hgA
  have hψind : ψ ∈ ggInduced ⊤ Bs := by
    have hmem := hA' hψA
    rw [ggAutomizer_eq] at hmem
    exact hmem
  have hcond' : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
      ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) = ggLin (p := p) ι ψ w - w := by
    rwa [hψeq]
  exact hNT ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond')

theorem ggIndep_card_join_le {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (A' : Subgroup (MulAut ↥Bs)) (pt : ↥Bs) {c : ℕ}
    (hstab : Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) pt) ≤ c) :
    Nat.card ↥A' ≤ Nat.card ↥Bs * c := by
  classical
  have hstab' : Nat.card ↥(MulAction.stabilizer (↥A') pt) ≤ c := by
    have hstab_eq : Nat.card ↥(MulAction.stabilizer (↥A') pt) =
        Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) pt) := by
      rw [← MulAction.stabilizer_subgroupOf A' pt]
      exact Nat.card_congr
        { toFun := fun x => ⟨((x : ↥A') : MulAut ↥Bs), (x : ↥A').2, x.2⟩
          invFun := fun x => ⟨⟨(x : MulAut ↥Bs), x.2.1⟩, x.2.2⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun x => Subtype.ext rfl }
    rw [hstab_eq]
    exact hstab
  let _ : Fintype ↥A' := Fintype.ofFinite ↥A'
  let _ : Fintype ↥(MulAction.orbit (↥A') pt) := Fintype.ofFinite ↥(MulAction.orbit (↥A') pt)
  let _ : Fintype ↥(MulAction.stabilizer (↥A') pt) :=
    Fintype.ofFinite ↥(MulAction.stabilizer (↥A') pt)
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A') pt
  simp only [← Nat.card_eq_fintype_card] at hOS
  rw [← hOS]
  refine Nat.mul_le_mul ?_ hstab'
  exact Nat.card_le_card_of_injective
    (Subtype.val : ↥(MulAction.orbit (↥A') pt) → ↥Bs) Subtype.val_injective

theorem ggIndep_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Bs : Subgroup G} {z : G} (hz : z ∈ Bs) {A₁ A₂ : Subgroup (MulAut ↥Bs)}
    {N : ℕ} (hN : 5 ≤ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hA₁ : A₁ = Subgroup.closure (Set.range φ))
    (F : GGIndepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨z, hz⟩)))
    {t : MulAut ↥Bs} (htm : t ∈ A₂) {ha : V} {αa : Module.Dual (ZMod p) V}
    (hform : ∀ w, ggLin (p := p) ι t w = w - αa w • ha)
    (W : Submodule (ZMod p) V) (hhW : ∀ i, h (e i) ∈ W) (hhaW : ha ∈ W)
    (hstab : Nat.card ↥((A₁ ⊔ A₂) ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥A₁) :
    Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
      p ^ Module.finrank (ZMod p) ↥W * (6 * (p - 1) * Nat.factorial N) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  let R : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r ∪ {ra})
  let z' : V := ι (Additive.ofMul ⟨z, hz⟩)
  let Φ : Option (Fin (N - 1)) → MulAut ↥Bs := fun o => match o with
    | none => t
    | some i => φ (e i)
  let Hf : Option (Fin (N - 1)) → V := fun o => match o with
    | none => ha
    | some i => h (e i)
  let Af : Option (Fin (N - 1)) → Module.Dual (ZMod p) V := fun o => match o with
    | none => αa
    | some i => α (e i)
  let A0 : Subgroup (MulAut ↥Bs) := Subgroup.closure (Set.range Φ)
  have hΦform : ∀ o w, ggLin (p := p) ι (Φ o) w = w - Af o w • Hf o := by
    intro o w
    cases o with
    | none => simpa [Φ, Af, Hf] using hform w
    | some i => simpa [Φ, Af, Hf] using hφ (e i) w
  have hWmem : ∀ o : Option (Fin (N - 1)), Hf o ∈ W := by
    intro o
    cases o with
    | none => exact hhaW
    | some i => exact hhW i
  have hmoves := l6aR_moves (p := p) ι hΦform W hWmem A0 rfl
  have hR_eq : R = A0.map (ggLin (p := p) ι) := by
    show Subgroup.closure (Set.range r ∪ {ra}) = Subgroup.map (ggLin (p := p) ι) A0
    rw [show A0 = Subgroup.closure (Set.range Φ) from rfl, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨φ (e i), ⟨some i, by simp [Φ]⟩, rfl⟩
      · exact ⟨t, ⟨none, by simp [Φ]⟩, rfl⟩
    · rintro ⟨g, ⟨o, rfl⟩, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i, rfl⟩
  have hmovesR : ∀ g ∈ R, g z' - z' ∈ W := by
    intro g hg
    rw [hR_eq] at hg
    exact hmoves g hg z'
  let orb := MulAction.orbit (↥R) z'
  have hOrbW : Nat.card orb ≤ Nat.card W := by
    refine Nat.card_le_card_of_injective
      (fun o : orb => (⟨(o : V) - z', ?_⟩ : W)) ?_
    · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp o.2
      rw [← hg]
      exact hmovesR g.1 g.2
    · intro o o' h
      apply Subtype.ext
      have hh := congrArg (fun z : W => (z : V)) h
      have h1 := congrArg (fun v : V => v + z') hh
      simpa using h1
  haveI : Finite W := Finite.of_injective (fun u : W => (u : V)) Subtype.val_injective
  have hWcard : Nat.card W = p ^ Module.finrank (ZMod p) ↥W :=
    (FiniteField.pow_finrank_eq_natCard p W).symm
  let A' : Subgroup (MulAut ↥Bs) := A₁ ⊔ A₂
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hOrb_card : Nat.card orb ≤ p ^ Module.finrank (ZMod p) ↥W := hOrbW.trans hWcard.le
  have hRle : R ≤ A_V := by
    rw [Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | rfl)
    · refine Subgroup.mem_map.mpr ⟨φ (e i), Subgroup.mem_sup_left ?_, rfl⟩
      rw [hA₁]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨t, Subgroup.mem_sup_right htm, rfl⟩
  let orb := MulAction.orbit (↥R) z'
  have hstabR : Nat.card ↥(MulAction.stabilizer (↥R) z') ≤
      (p - 1) * 6 * Nat.card ↥A₁ := by
    let E : ↥A' ≃* ↥A_V :=
      Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)
    let fA : ↥(MulAction.stabilizer (↥R) z') → ↥A' :=
      fun s => E.symm ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩
    have hfA : Function.Injective fA := by
      intro s s' h
      have hE1 : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by
        simp [fA]
      have hE2 : E (fA s') = ⟨(s'.1 : V ≃ₗ[ZMod p] V), hRle s'.1.2⟩ := by
        simp [fA]
      have hg : (s.1 : V ≃ₗ[ZMod p] V) = (s'.1 : V ≃ₗ[ZMod p] V) := by
        have hEE : E (fA s) = E (fA s') := by rw [h]
        have := congrArg (fun z : ↥A_V => (z : V ≃ₗ[ZMod p] V)) (hE1.symm.trans (hEE.trans hE2))
        simpa using this
      exact Subtype.ext (Subtype.ext hg)
    let f : ↥(MulAction.stabilizer (↥R) z') →
        ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) :=
      fun s => ⟨(fA s : MulAut ↥Bs), ⟨(fA s).2, by
        change (fA s : MulAut ↥Bs) • (⟨z, hz⟩ : ↥Bs) = ⟨z, hz⟩
        have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by
          simp [fA]
        have hval : ggLin (p := p) ι (fA s : MulAut ↥Bs) = (s.1 : V ≃ₗ[ZMod p] V) := by
          have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by simp [fA]
          have h2 := congrArg (fun z : ↥A_V => (z : V ≃ₗ[ZMod p] V)) hE
          change (E (fA s) : V ≃ₗ[ZMod p] V) = (s.1 : V ≃ₗ[ZMod p] V)
          exact h2
        have hgx : (s.1 : V ≃ₗ[ZMod p] V) z' = z' := by
          have hs := MulAction.mem_stabilizer_iff.mp s.2
          change (s.1 : V ≃ₗ[ZMod p] V) z' = z' at hs
          exact hs
        have hlin : ggLin (p := p) ι (fA s : MulAut ↥Bs) z' = z' := by
          rw [hval]; exact hgx
        have hpt : (fA s : MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs) = ⟨z, hz⟩ := by
          have h2 := hlin
          simp only [z', ggLin_apply_ofMul] at h2
          exact Additive.ofMul.injective (ι.injective h2)
        simpa using hpt⟩⟩
    have hf : Function.Injective f := by
      intro s s' h
      have h1 : ((f s).1 : MulAut ↥Bs) = ((f s').1 : MulAut ↥Bs) :=
        congrArg (fun z => (z.1 : MulAut ↥Bs)) h
      exact hfA (Subtype.ext h1)
    calc Nat.card ↥(MulAction.stabilizer (↥R) z')
        ≤ Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ (p - 1) * 6 * Nat.card ↥A₁ := hstab
  have hAl : Nat.card ↥A₁ ≤ Nat.factorial N := ggIndep_card_A1 hp hN hz ι hφ hA₁ e F
  have hRcard : Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) z') := by
    haveI : Finite (V ≃ₗ[ZMod p] V) :=
      Finite.of_injective (fun g : V ≃ₗ[ZMod p] V => (g : V → V))
        (fun _ _ h => LinearEquiv.ext (congrFun h))
    haveI : Finite ↥R := Finite.of_injective (fun g : ↥R => (g : V ≃ₗ[ZMod p] V))
      Subtype.val_injective
    haveI : Fintype ↥R := Fintype.ofFinite ↥R
    haveI : Fintype orb := Fintype.ofFinite orb
    haveI : Fintype ↥(MulAction.stabilizer (↥R) z') := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥R) z'
    simp only [← Nat.card_eq_fintype_card] at hOS
    exact hOS.symm
  calc Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) z') := hRcard
    _ ≤ p ^ Module.finrank (ZMod p) ↥W * ((p - 1) * 6 * Nat.card ↥A₁) :=
        Nat.mul_le_mul hOrb_card hstabR
    _ ≤ p ^ Module.finrank (ZMod p) ↥W * ((p - 1) * 6 * Nat.factorial N) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAl)
    _ = p ^ Module.finrank (ZMod p) ↥W * (6 * (p - 1) * Nat.factorial N) := by
        have heq : ((p - 1) * 6) * Nat.factorial N = (6 * (p - 1)) * Nat.factorial N := by
          rw [Nat.mul_comm (p - 1) 6]
        rw [heq]


end CFSG.StandardType

end
