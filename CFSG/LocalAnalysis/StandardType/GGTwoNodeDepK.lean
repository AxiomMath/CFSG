module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepACaseI
public import CFSG.LocalAnalysis.StandardType.GGDepACaseII
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTK_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem l05nTK_rtg_symm {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ a c, R a c → R c a) {a b : α}
    (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsymm _ _ hbc)

private theorem l05nTK_first_edge {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ a c, R a c → R c a) {start b : α}
    (h : Relation.ReflTransGen R start b) (hb : b ≠ start) : ∃ c, R start c := by
  have h' : Relation.ReflTransGen R b start := l05nTK_rtg_symm hsymm h
  have hgoal : b = start ∨ ∃ c, R start c :=
    Relation.ReflTransGen.head_induction_on (r := R) (b := start) h'
      (motive := fun x _ => x = start ∨ ∃ c, R start c)
      (Or.inl rfl)
      (by
        intro p q hpq _ ih
        rcases ih with hq | hex
        · rw [hq] at hpq
          exact Or.inr ⟨p, hsymm _ _ hpq⟩
        · exact Or.inr hex)
  rcases hgoal with hh | hex
  · exact absurd hh hb
  · exact hex

private theorem l05nTK_nonempty_of_weyl {ι : Type} {M : CoxeterMatrix ι}
    (hW : GGIsWeylMatrix M) : Nonempty ι := by
  rcases hW with ⟨n, e, hn, -⟩ | hE6 | hE7 | hE8 | hF4 | hG2
  · exact ⟨e ⟨0, by omega⟩⟩
  · obtain ⟨e, -⟩ := hE6
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hE7
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hE8
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hF4
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hG2
    exact ⟨e 0⟩

private theorem l05nTK_refl_mul_comm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {rc ra : V ≃ₗ[ZMod p] V} {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (h0c : αc ha = 0) (h0a : αa hc = 0) :
    rc * ra = ra * rc := by
  have h1 : rc ha = ha := by rw [hc' ha, h0c, zero_smul, sub_zero]
  have h2 : ra hc = hc := by rw [ha' hc, h0a, zero_smul, sub_zero]
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hl : rc (ra v) = v - αc v • hc - αa v • ha := by
    calc rc (ra v) = rc (v - αa v • ha) := by rw [ha' v]
      _ = rc v - rc (αa v • ha) := by rw [map_sub]
      _ = rc v - αa v • rc ha := by rw [map_smul]
      _ = rc v - αa v • ha := by rw [h1]
      _ = (v - αc v • hc) - αa v • ha := by rw [hc' v]
      _ = v - αc v • hc - αa v • ha := by abel
  have hr : ra (rc v) = v - αc v • hc - αa v • ha := by
    calc ra (rc v) = ra (v - αc v • hc) := by rw [hc' v]
      _ = ra v - ra (αc v • hc) := by rw [map_sub]
      _ = ra v - αc v • ra hc := by rw [map_smul]
      _ = ra v - αc v • hc := by rw [h2]
      _ = (v - αa v • ha) - αc v • hc := by rw [ha' v]
      _ = v - αc v • hc - αa v • ha := by abel
  rw [hl, hr]

private theorem l05nTK_nt
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    {t : MulAut ↥Bs} (htm : t ∈ ggAutomizer K Bs) :
    ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  classical
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgenL : ∀ i : Fin (N - 1), ggLin (p := p) ι (φ (e i)) ∈ A_V := by
    intro i
    refine Subgroup.mem_map.mpr ⟨φ (e i), ?_, rfl⟩
    exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hgenN : ggLin (p := p) ι t ∈ A_V := by
    refine Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩
    exact Subgroup.mem_sup_right htm
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
  have hψsup : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := hψA
  have hψind : ψ ∈ ggInduced ⊤ Bs := by
    have hle_top : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs (le_top)) (ggAutomizer_mono Bs (le_top))
    have hmem := hle_top hψsup
    rw [ggAutomizer_eq] at hmem
    exact hmem
  have hcond' : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
      ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) = ggLin (p := p) ι ψ w - w := by
    rwa [hψeq]
  exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond')

private theorem l05nTK3_finrank_U {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) (t : V) :
    Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
      Submodule.span (ZMod p) ({t} : Set V)) ≤ N - 1 := by
  obtain ⟨-, -, hfin⟩ := ggDepA_relation F
  have hN2 : 2 ≤ N := by
    by_contra h
    have h0 : N - 1 = 0 := by omega
    apply F.dep
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hi : (i : ℕ) < 0 := by omega
    exact (Nat.not_lt_zero i.val hi).elim
  have hle := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span (ZMod p) (Set.range h)) (Submodule.span (ZMod p) ({t} : Set V))
  have hsingle : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) ≤ 1 :=
    finrank_le_one ⟨t, Submodule.mem_span_singleton_self t⟩ (fun w => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩)
  calc Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) ({t} : Set V))
      ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) +
        Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := hle
    _ = (N - 2) + Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := by
        rw [hfin]
    _ ≤ (N - 2) + 1 := by omega
    _ = N - 1 := by omega

private theorem l05nTK3_moves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
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

private theorem l05nTK3_card_Al {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 5 ≤ N)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {x : G} (hx : x ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    {Λ : Type} [Fintype Λ] {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (e : Fin (N - 1) ≃ Λ)
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N := by
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
  obtain ⟨ρ, hρswap, hρmem, -, -⟩ :=
    ggDepA_perm_embed (p := p) (N := N) hp hN F r hr
  have hmap : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range r) := by
    rw [hAL, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, by simp [r]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
  have hcard_eq : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
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
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) := hcard_eq
    _ = Nat.card ↥(Subgroup.closure (Set.range r)) := by rw [hmap]
    _ = Nat.card ↥(ρ.range) := by rw [hρrange]
    _ ≤ Nat.card (Equiv.Perm (Fin N)) :=
        Nat.card_le_card_of_surjective
          (fun σ : Equiv.Perm (Fin N) => (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range))
          (fun y => by
            obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp y.2
            exact ⟨σ, Subtype.ext hσ⟩)
    _ = Nat.factorial N := by rw [Nat.card_perm, Nat.card_fin]

private theorem l05nTK_card
    (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 11 ≤ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    {t : MulAut ↥Bs} (htm : t ∈ ggAutomizer K Bs)
    {ha : V} {αa : Module.Dual (ZMod p) V}
    (hform : ∀ w, ggLin (p := p) ι t w = w - αa w • ha) :
    Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let h' : Fin (N - 1) → V := fun i => h (e i)
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  let R : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r ∪ {ra})
  let U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h') ⊔
      Submodule.span (ZMod p) ({ha} : Set V)
  let x' : V := ι (Additive.ofMul ⟨x, hx⟩)
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
  have hUmem : ∀ o : Option (Fin (N - 1)), Hf o ∈ U := by
    intro o
    cases o with
    | none => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton ha))
    | some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, by simp [Hf, h']⟩)
  have hmoves := l05nTK3_moves (p := p) ι hΦform U hUmem A0 rfl
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
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hA0le : A0 ≤ A' := by
    rw [show A0 = Subgroup.closure (Set.range Φ) from rfl, Subgroup.closure_le]
    rintro g ⟨o, rfl⟩
    cases o with
    | none => exact Subgroup.mem_sup_right htm
    | some i => exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hRle : R ≤ A_V := by
    rw [hR_eq]
    exact Subgroup.map_mono hA0le
  have hmovesR : ∀ g ∈ R, g x' - x' ∈ U := by
    intro g hg
    rw [hR_eq] at hg
    exact hmoves g hg x'
  let orb := MulAction.orbit (↥R) x'
  have hOrbU : Nat.card orb ≤ Nat.card U := by
    refine Nat.card_le_card_of_injective
      (fun o : orb => (⟨(o : V) - x', ?_⟩ : U)) ?_
    · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp o.2
      rw [← hg]
      exact hmovesR g.1 g.2
    · intro o o' h
      apply Subtype.ext
      have hh := congrArg (fun z : U => (z : V)) h
      have h1 := congrArg (fun v : V => v + x') hh
      simpa using h1
  haveI : Finite U := Finite.of_injective (fun u : U => (u : V)) Subtype.val_injective
  have hUcard : Nat.card U = p ^ Module.finrank (ZMod p) ↥U :=
    (FiniteField.pow_finrank_eq_natCard p U).symm
  have hOrb_card : Nat.card orb ≤ p ^ (N - 1) := by
    calc Nat.card orb ≤ Nat.card U := hOrbU
      _ = p ^ Module.finrank (ZMod p) ↥U := hUcard
      _ ≤ p ^ (N - 1) := Nat.pow_le_pow_right (by omega : 1 ≤ p) (l05nTK3_finrank_U F ha)
  have hstab : Nat.card ↥(MulAction.stabilizer (↥R) x') ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := by
    let E : ↥A' ≃* ↥A_V :=
      Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)
    let fA : ↥(MulAction.stabilizer (↥R) x') → ↥A' :=
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
    let f : ↥(MulAction.stabilizer (↥R) x') →
        ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
      fun s => ⟨(fA s : MulAut ↥Bs), ⟨(fA s).2, by
        change (fA s : MulAut ↥Bs) • (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩
        have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by
          simp [fA]
        have hval : ggLin (p := p) ι (fA s : MulAut ↥Bs) = (s.1 : V ≃ₗ[ZMod p] V) := by
          have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by simp [fA]
          have h2 := congrArg (fun z : ↥A_V => (z : V ≃ₗ[ZMod p] V)) hE
          change (E (fA s) : V ≃ₗ[ZMod p] V) = (s.1 : V ≃ₗ[ZMod p] V)
          exact h2
        have hgx : (s.1 : V ≃ₗ[ZMod p] V) x' = x' := by
          have hs := MulAction.mem_stabilizer_iff.mp s.2
          change (s.1 : V ≃ₗ[ZMod p] V) x' = x' at hs
          exact hs
        have hlin : ggLin (p := p) ι (fA s : MulAut ↥Bs) x' = x' := by
          rw [hval]; exact hgx
        have hpt : (fA s : MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
          have h2 := hlin
          simp only [x', ggLin_apply_ofMul] at h2
          exact Additive.ofMul.injective (ι.injective h2)
        simpa using hpt⟩⟩
    have hf : Function.Injective f := by
      intro s s' h
      have h1 : ((f s).1 : MulAut ↥Bs) = ((f s').1 : MulAut ↥Bs) :=
        congrArg (fun z => (z.1 : MulAut ↥Bs)) h
      exact hfA (Subtype.ext h1)
    calc Nat.card ↥(MulAction.stabilizer (↥R) x')
        ≤ Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hOrb G p B Bs x L D J y K hH hx
  have hAl : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N :=
    l05nTK3_card_Al hp (by omega : 5 ≤ N) hx ι hφ hAL e F
  have hRcard : Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) x') := by
    haveI : Finite (V ≃ₗ[ZMod p] V) :=
      Finite.of_injective (fun g : V ≃ₗ[ZMod p] V => (g : V → V))
        (fun _ _ h => LinearEquiv.ext (congrFun h))
    haveI : Finite ↥R := Finite.of_injective (fun g : ↥R => (g : V ≃ₗ[ZMod p] V))
      Subtype.val_injective
    haveI : Fintype ↥R := Fintype.ofFinite ↥R
    haveI : Fintype orb := Fintype.ofFinite orb
    haveI : Fintype ↥(MulAction.stabilizer (↥R) x') := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥R) x'
    simp only [← Nat.card_eq_fintype_card] at hOS
    exact hOS.symm
  calc Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) x') := hRcard
    _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
        Nat.mul_le_mul hOrb_card hstab
    _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.factorial N) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAl)
    _ ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
        have hpow : p ^ (N - 1) ≤ p ^ N :=
          Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : N - 1 ≤ N)
        have heq : ((p - 1) * 6) * Nat.factorial N = (6 * (p - 1)) * Nat.factorial N := by
          rw [Nat.mul_comm (p - 1) 6]
        rw [heq]
        exact Nat.mul_le_mul_right _ hpow


private theorem l05nTK_core
    (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResSideDatum p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V),
      t ∈ ggAutomizer K Bs ∧ (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) := by
  classical
  obtain ⟨ΛK, iKf, iKd, bK, MK, CK, MJ, VK, iKac, iKm, ιK, φK, hKc, αK,
    hWMK, hCK, hWMJ, hMJ, hlinK, hreflK, hpairK, hKf, hclosK, hKfJ, hclosJ, hconjK⟩ := hK
  letI := iKf
  letI := iKd
  letI := iKac
  letI := iKm
  obtain ⟨fK, hfKp⟩ := hKf
  have hJL : J ≤ L := (hH.1.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  have hp2 : p ≠ 2 := by omega
  let eK : VK ≃ₗ[ZMod p] V := LinearEquiv.ofBijective
      ((ιK.symm.trans ι).toAddMonoidHom.toZModLinearMap p) (ιK.symm.trans ι).bijective
  have he : ∀ w : VK, eK w = ι (ιK.symm w) := by
    intro w
    change (ιK.symm.trans ι) w = ι (ιK.symm w)
    rfl
  have hes : ∀ w : V, eK.symm w = ιK (ι.symm w) := by
    intro w
    apply eK.injective
    rw [LinearEquiv.apply_symm_apply, he]
    simp
  let t : MulAut ↥Bs := φK bK
  let ha : V := eK (hKc bK)
  let αa : Module.Dual (ZMod p) V := (αK bK).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap
  have hform : ∀ w, ggLin (p := p) ι t w = w - αa w • ha := by
    intro w
    have h1 : ggLin (p := p) ι t w = eK (ggLin (p := p) ιK t (eK.symm w)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [h1, hlinK bK (eK.symm w), map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hha : αa ha = 2 := by
    show (αK bK).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap (eK (hKc bK)) = 2
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    have h1 := hpairK bK bK
    rw [hCK.1 bK] at h1
    simpa using h1
  have htm : t ∈ ggAutomizer K Bs := by
    rw [hclosK]
    exact Subgroup.subset_closure ⟨bK, rfl⟩
  have hxne : αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 := by
    have hval : αa (ι (Additive.ofMul ⟨x, hx⟩)) =
        αK bK (ιK (Additive.ofMul ⟨x, hx⟩)) := by
      show (αK bK).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap
        (ι (Additive.ofMul ⟨x, hx⟩)) = _
      rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hes]
      congr 1
      rw [AddEquiv.symm_apply_apply]
    rw [hval]
    intro h0
    let bb : ↥Bs := ⟨x, hx⟩
    have h0' : αK bK (ιK (Additive.ofMul bb)) = 0 := by simpa [bb] using h0
    have hx0 : ∀ i : Λ, α i (ι (Additive.ofMul bb)) = 0 := by
      intro i
      have := F.x_ker (e.symm i)
      simpa using this
    have hALfix : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
      rw [hAL]
      refine ggFixed_of_mem_closure φ bb ?_
      intro i
      refine (ggLin_fix_iff (p := p) ι (φ i) bb).mpr ?_
      rw [hφ i, hx0 i, zero_smul, sub_zero]
    have hAJle : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJL
    have hfixJ : ∀ ψ ∈ ggAutomizer J Bs, ψ bb = bb := fun ψ hψ => hALfix ψ (hAJle hψ)
    have hfixgen : ∀ jj : {j : ΛK // j ≠ bK}, φK jj bb = bb := fun jj =>
      hfixJ (φK jj) (by rw [hclosJ]; exact Subgroup.subset_closure ⟨jj, rfl⟩)
    have hfixb : φK bK bb = bb := by
      refine (ggLin_fix_iff (p := p) ιK (φK bK) bb).mpr ?_
      rw [hlinK bK, h0', zero_smul, sub_zero]
    have hχ : ∀ i : ΛK, φK i bb = bb := by
      intro i
      by_cases hi : i = bK
      · subst hi; exact hfixb
      · exact hfixgen ⟨i, hi⟩
    have hfixK' : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
      rw [hclosK]
      exact ggFixed_of_mem_closure φK bb hχ
    have hbb1 : (bb : G) = 1 :=
      hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
        hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb (Subgroup.mem_zpowers x) hfixK'
    have hx1 : x = 1 := by simpa [bb] using hbb1
    exact l05nTK_x_ne_one hH hx1
  have hjoin : ∃ c : Fin (N - 1), αa (h (e c)) ≠ 0 := by
    by_contra hno
    push Not at hno
    let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
    let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
    let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure
      (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})
    have hntA := l05nTK_nt hH hx e hφ hAL htm
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ΛK, j₀ ≠ bK := by
      obtain ⟨j₀⟩ := l05nTK_nonempty_of_weyl hWMJ
      exact ⟨j₀.1, j₀.2⟩
    have hpath := ggRC_weyl_connected hWMK bK j₀
    have hsymm : ∀ a c : ΛK, (a ≠ c ∧ MK.M a c ≠ 2) → (c ≠ a ∧ MK.M c a ≠ 2) := by
      rintro a c ⟨hne, h2⟩
      exact ⟨hne.symm, by rwa [MK.symmetric c a]⟩
    obtain ⟨j, hj⟩ := l05nTK_first_edge hsymm hpath hj₀
    have hjj : j ≠ bK := hj.1.symm
    have hφjJ : φK j ∈ ggAutomizer J Bs := by
      rw [hclosJ]
      exact Subgroup.subset_closure ⟨⟨j, hjj⟩, rfl⟩
    have hφjL : φK j ∈ ggAutomizer L Bs := (ggAutomizer_mono Bs hJL) hφjJ
    have hmapAL : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
        Subgroup.closure (Set.range r) := by
      rw [hAL, MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨e.symm i, by simp [r]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
    have hlinj : ggLin (p := p) ι (φK j) ∈ Subgroup.closure (Set.range r) := by
      rw [← hmapAL]
      exact Subgroup.mem_map.mpr ⟨φK j, hφjL, rfl⟩
    have hcomm_c : ∀ c : Fin (N - 1), r c * ra = ra * r c := by
      intro c
      have h0a : αa (h (e c)) = 0 := hno c
      have h0c : α (e c) ha = 0 :=
        ggDepA_pair_zero_symm (p := p) hp2 A hntA
          (rc := ra) (ra := r c) (hc := ha) (ha := h (e c)) (αc := αa) (αa := α (e c))
          (hrc := Subgroup.subset_closure (Or.inr rfl))
          (hra := Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
          (hc' := by intro w; exact hform w)
          (ha' := by intro w; exact hφ (e c) w)
          (hαc := hha)
          (hαa := by simpa [CartanMatrix.A] using F.pair c c)
          (h0 := h0a)
      exact l05nTK_refl_mul_comm (rc := r c) (ra := ra) (hc := h (e c)) (ha := ha)
        (αc := α (e c)) (αa := αa) (hc' := by intro w; exact hφ (e c) w)
        (ha' := by intro w; exact hform w) (h0c := h0c) (h0a := h0a)
    have hle_cz : Subgroup.closure (Set.range r) ≤
        Subgroup.centralizer ({ra} : Set (V ≃ₗ[ZMod p] V)) := by
      rw [Subgroup.closure_le]
      rintro g ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_c c)
    have hcomm_j : ggLin (p := p) ι (φK j) * ra = ra * ggLin (p := p) ι (φK j) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle_cz hlinj)
    have hcomm_tj : t * φK j = φK j * t := by
      have hcomm_j' : ggLin (p := p) ι (φK j * t) = ggLin (p := p) ι (t * φK j) := by
        rw [map_mul, map_mul]
        simpa [ra] using hcomm_j
      exact (ggLin_injective (p := p) ι hcomm_j').symm
    have hcomm_group : MK.simple bK * MK.simple j = MK.simple j * MK.simple bK := by
      apply fK.injective
      apply Subtype.ext
      rw [map_mul, map_mul]
      show ((fK (MK.simple bK) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) *
            ((fK (MK.simple j) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) =
          ((fK (MK.simple j) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) *
            ((fK (MK.simple bK) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs)
      rw [hfKp bK, hfKp j]
      exact hcomm_tj
    have hb2 : MK.simple bK * MK.simple bK = 1 := by
      have := CoxeterSystem.simple_mul_simple_self MK.toCoxeterSystem bK
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
    have hj2 : MK.simple j * MK.simple j = 1 := by
      have := CoxeterSystem.simple_mul_simple_self MK.toCoxeterSystem j
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
    have h2 : (MK.simple bK * MK.simple j)^2 = 1 := by
      have key : (MK.simple bK * MK.simple j) * (MK.simple bK * MK.simple j) =
          MK.simple bK * MK.simple bK * (MK.simple j * MK.simple j) := by
        calc (MK.simple bK * MK.simple j) * (MK.simple bK * MK.simple j)
            = MK.simple bK * (MK.simple j * MK.simple bK) * MK.simple j := by group
          _ = MK.simple bK * (MK.simple bK * MK.simple j) * MK.simple j := by
                rw [← hcomm_group]
          _ = MK.simple bK * MK.simple bK * (MK.simple j * MK.simple j) := by group
      rw [pow_two, key, hb2, hj2, mul_one]
    have hord : orderOf (MK.simple bK * MK.simple j) = MK.M bK j := by
      have := CoxeterSystem.orderOf_simple_mul_simple MK.toCoxeterSystem bK j
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
    have hdvd : MK.M bK j ∣ 2 := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h2
    have hM1 : MK.M bK j ≠ 1 := MK.off_diagonal bK j (fun h => hjj h.symm)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2'
    · exact hM1 h1
    · exact hj.2 h2'
  exact ⟨t, ha, αa, htm, hform, hha, hxne, hjoin⟩

theorem ggTwoNode_kside (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 11 ≤ N) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResSideDatum p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
          {ggLin (p := p) ι t}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
        p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  obtain ⟨t, ha, αa, htm, hform, hha, hxne, hjoin⟩ :=
    l05nTK_core hFixK hp hH hx e hφ hAL F hK
  exact ⟨t, ha, αa, htm, hform, hha, hxne, hjoin,
    l05nTK_nt hH hx e hφ hAL htm,
    l05nTK_card hOrb hp hH hx hN e hφ hAL F htm hform⟩

end CFSG.StandardType
