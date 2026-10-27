module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCubic
import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteParity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.Quasithin.Fan86.Tutte

open CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type} {Γ : SimpleGraph V}

structure SubdivCubic (Γ : SimpleGraph V) (Δ : Set V) (sm : V → Prop) : Prop where
  bip : ∀ u v, Γ.Adj u v → (sm u ↔ ¬ sm v)
  card_nbrs : ∀ y ∈ Δ, sm y → Nat.card (Γ.neighborSet y) = 3
  nbr_mem : ∀ y ∈ Δ, sm y → ∀ v, Γ.Adj y v → v ∈ Δ
  two : ∀ e ∈ Δ, ¬ sm e → ∃ y₁ y₂, y₁ ≠ y₂ ∧ ∀ v, (v ∈ Δ ∧ Γ.Adj e v) ↔ (v = y₁ ∨ v = y₂)
  simple : ∀ y ∈ Δ, sm y → ∀ e₁ e₂ y', Γ.Adj y e₁ → Γ.Adj y e₂ → y' ∈ Δ → y' ≠ y →
    Γ.Adj e₁ y' → Γ.Adj e₂ y' → e₁ = e₂
  conn : ∀ u ∈ Δ, ∀ v ∈ Δ, Relation.ReflTransGen (fun a b => a ∈ Δ ∧ b ∈ Δ ∧ Γ.Adj a b) u v

namespace SubdivCubic

variable {Δ : Set V} {sm : V → Prop}

private theorem nbr_of_sm (h : SubdivCubic Γ Δ sm) {y : V} (hy : y ∈ Δ) (hsm : sm y) {e : V}
    (he : Γ.Adj y e) : e ∈ Δ ∧ ¬ sm e :=
  ⟨h.nbr_mem y hy hsm e he, (h.bip y e he).1 hsm⟩

private theorem sm_of_adj_not_sm (h : SubdivCubic Γ Δ sm) {e y : V} (he : ¬ sm e)
    (hey : Γ.Adj e y) : sm y := by
  by_contra hy
  exact he ((h.bip e y hey).2 hy)

private theorem eq_of_ne (h : SubdivCubic Γ Δ sm) {e a b c : V} (he : e ∈ Δ) (hesm : ¬ sm e)
    (ha : a ∈ Δ) (hb : b ∈ Δ) (hc : c ∈ Δ) (hea : Γ.Adj e a) (heb : Γ.Adj e b)
    (hec : Γ.Adj e c) (hba : b ≠ a) (hca : c ≠ a) : b = c := by
  obtain ⟨y₁, y₂, -, hy⟩ := h.two e he hesm
  have ha' := (hy a).1 ⟨ha, hea⟩
  have hb' := (hy b).1 ⟨hb, heb⟩
  have hc' := (hy c).1 ⟨hc, hec⟩
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl <;>
    first | rfl | exact absurd rfl hba | exact absurd rfl hca

private theorem exists_other_nbr (h : SubdivCubic Γ Δ sm) {e a : V} (he : e ∈ Δ) (hesm : ¬ sm e)
    (ha : a ∈ Δ) (hea : Γ.Adj e a) : ∃ b, b ∈ Δ ∧ Γ.Adj e b ∧ b ≠ a ∧ sm b := by
  obtain ⟨y₁, y₂, hne, hy⟩ := h.two e he hesm
  have h₁ := (hy y₁).2 (Or.inl rfl)
  have h₂ := (hy y₂).2 (Or.inr rfl)
  rcases (hy a).1 ⟨ha, hea⟩ with rfl | rfl
  · exact ⟨y₂, h₂.1, h₂.2, hne.symm, h.sm_of_adj_not_sm hesm h₂.2⟩
  · exact ⟨y₁, h₁.1, h₁.2, hne, h.sm_of_adj_not_sm hesm h₁.2⟩

private theorem exists_nbr_ne (h : SubdivCubic Γ Δ sm) {y : V} (hy : y ∈ Δ) (hsm : sm y) (a : V) :
    ∃ b, Γ.Adj y b ∧ b ≠ a := by
  have h3 : (Γ.neighborSet y).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_nbrs y hy hsm
  obtain ⟨p, q, r, hpq, -, -, hset⟩ := Set.ncard_eq_three.1 h3
  have hp : Γ.Adj y p := by
    have : p ∈ Γ.neighborSet y := by rw [hset]; simp
    exact this
  have hq : Γ.Adj y q := by
    have : q ∈ Γ.neighborSet y := by rw [hset]; simp
    exact this
  by_cases hpa : p = a
  · exact ⟨q, hq, fun hqa => hpq (hpa.trans hqa.symm)⟩
  · exact ⟨p, hp, hpa⟩

private theorem exists_ray (h : SubdivCubic Γ Δ sm) {e y : V} (he : e ∈ Δ) (hesm : ¬ sm e)
    (hy : y ∈ Δ) (hey : Γ.Adj e y) :
    ∃ a b c d : V, Γ.Adj y a ∧ a ≠ e ∧ Γ.Adj a b ∧ b ≠ y ∧ Γ.Adj b c ∧ c ≠ a ∧ Γ.Adj c d ∧
      d ≠ b ∧ a ∈ Δ ∧ b ∈ Δ ∧ c ∈ Δ ∧ d ∈ Δ ∧ sm d := by
  have hysm : sm y := h.sm_of_adj_not_sm hesm hey
  obtain ⟨a, hya, hae⟩ := h.exists_nbr_ne hy hysm e
  obtain ⟨haΔ, hasm⟩ := h.nbr_of_sm hy hysm hya
  obtain ⟨b, hbΔ, hab, hby, hbsm⟩ := h.exists_other_nbr haΔ hasm hy hya.symm
  obtain ⟨c, hbc, hca⟩ := h.exists_nbr_ne hbΔ hbsm a
  obtain ⟨hcΔ, hcsm⟩ := h.nbr_of_sm hbΔ hbsm hbc
  obtain ⟨d, hdΔ, hcd, hdb, hdsm⟩ := h.exists_other_nbr hcΔ hcsm hbΔ hbc.symm
  exact ⟨a, b, c, d, hya, hae, hab, hby, hbc, hca, hcd, hdb, haΔ, hbΔ, hcΔ, hdΔ, hdsm⟩

theorem exists_arc (h : SubdivCubic Γ Δ sm) {e : V} (he : e ∈ Δ) (hesm : ¬ sm e) :
    ∃ P : Arc Γ 10, P.vert 5 = e ∧ sm (P.vert 0) ∧ ∀ i, i ≤ 10 → P.vert i ∈ Δ := by
  obtain ⟨y₁, y₂, hne, hy⟩ := h.two e he hesm
  have h₁ := (hy y₁).2 (Or.inl rfl)
  have h₂ := (hy y₂).2 (Or.inr rfl)
  obtain ⟨a₁, b₁, c₁, d₁, hya₁, hae₁, hab₁, hby₁, hbc₁, hca₁, hcd₁, hdb₁, ha₁Δ, hb₁Δ, hc₁Δ,
    hd₁Δ, hd₁sm⟩ := h.exists_ray he hesm h₁.1 h₁.2
  obtain ⟨a₂, b₂, c₂, d₂, hya₂, hae₂, hab₂, hby₂, hbc₂, hca₂, hcd₂, hdb₂, ha₂Δ, hb₂Δ, hc₂Δ,
    hd₂Δ, hd₂sm⟩ := h.exists_ray he hesm h₂.1 h₂.2
  have s₀ := hcd₁.symm
  have s₁ := hbc₁.symm
  have s₂ := hab₁.symm
  have s₃ := hya₁.symm
  have s₄ := h₁.2.symm
  have t₅ := hae₂.symm
  have t₆ := hby₂.symm
  have t₇ := hca₂.symm
  have t₈ := hdb₂.symm
  refine ⟨⟨fun i => match i with
    | 0 => d₁ | 1 => c₁ | 2 => b₁ | 3 => a₁ | 4 => y₁ | 5 => e | 6 => y₂ | 7 => a₂ | 8 => b₂
    | 9 => c₂ | _ => d₂, ?_, ?_⟩, rfl, hd₁sm, ?_⟩
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    all_goals first | assumption | exact h₂.2
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    all_goals assumption
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 := by omega
    all_goals first | assumption | exact h₁.1 | exact h₂.1 | exact he

private abbrev SmVert (Δ : Set V) (sm : V → Prop) : Type := {y : V // y ∈ Δ ∧ sm y}

private def sigmaGraph (Γ : SimpleGraph V) (Δ : Set V) (sm : V → Prop) :
    SimpleGraph (SmVert Δ sm) where
  Adj y y' := (y : V) ≠ y' ∧ ∃ e, Γ.Adj y e ∧ Γ.Adj e y'
  symm := ⟨fun _ _ hy => ⟨fun h => hy.1 h.symm, by
    obtain ⟨e, h₁, h₂⟩ := hy.2
    exact ⟨e, h₂.symm, h₁.symm⟩⟩⟩
  loopless := ⟨fun _ hy => hy.1 rfl⟩

private theorem sigmaGraph_adj {y y' : SmVert Δ sm} :
    (sigmaGraph Γ Δ sm).Adj y y' ↔ (y : V) ≠ y' ∧ ∃ e, Γ.Adj y e ∧ Γ.Adj e y' :=
  Iff.rfl

private theorem sigma_card (h : SubdivCubic Γ Δ sm) (y : SmVert Δ sm) :
    Nat.card ((sigmaGraph Γ Δ sm).neighborSet y) = 3 := by
  have hex : ∀ e : Γ.neighborSet (y : V), ∃ y' : SmVert Δ sm,
      (sigmaGraph Γ Δ sm).Adj y y' ∧ Γ.Adj e y' := by
    rintro ⟨e, he⟩
    obtain ⟨heΔ, hesm⟩ := h.nbr_of_sm y.2.1 y.2.2 he
    obtain ⟨b, hbΔ, heb, hby, hbsm⟩ := h.exists_other_nbr heΔ hesm y.2.1 he.symm
    exact ⟨⟨b, hbΔ, hbsm⟩, sigmaGraph_adj.2 ⟨fun hh => hby hh.symm, e, he, heb⟩, heb⟩
  choose g hg1 hg2 using hex
  have hcard : Nat.card (Γ.neighborSet (y : V)) =
      Nat.card ((sigmaGraph Γ Δ sm).neighborSet y) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun e : Γ.neighborSet (y : V) => (⟨g e, hg1 e⟩ : (sigmaGraph Γ Δ sm).neighborSet y))
      ⟨?_, ?_⟩)
    · intro e₁ e₂ heq
      have hg : g e₁ = g e₂ := congrArg Subtype.val heq
      refine Subtype.ext (h.simple y y.2.1 y.2.2 e₁ e₂ (g e₁) e₁.2 e₂.2 (g e₁).2.1 ?_
        (hg2 e₁) ?_)
      · exact (sigmaGraph_adj.1 (hg1 e₁)).1.symm
      · rw [hg]
        exact hg2 e₂
    · rintro ⟨y', hy'⟩
      obtain ⟨hne, e, he₁, he₂⟩ := sigmaGraph_adj.1 hy'
      refine ⟨⟨e, he₁⟩, Subtype.ext (Subtype.ext ?_)⟩
      obtain ⟨heΔ, hesm⟩ := h.nbr_of_sm y.2.1 y.2.2 he₁
      exact h.eq_of_ne heΔ hesm y.2.1 (g ⟨e, he₁⟩).2.1 y'.2.1 he₁.symm (hg2 ⟨e, he₁⟩) he₂
        (fun hh => (sigmaGraph_adj.1 (hg1 ⟨e, he₁⟩)).1 hh.symm) (fun hh => hne hh.symm)
  rw [← hcard]
  exact h.card_nbrs _ y.2.1 y.2.2

private theorem sigma_preconnected (h : SubdivCubic Γ Δ sm) :
    (sigmaGraph Γ Δ sm).Preconnected := by
  have key : ∀ a b : V, Relation.ReflTransGen (fun a b => a ∈ Δ ∧ b ∈ Δ ∧ Γ.Adj a b) a b →
      ∀ y : SmVert Δ sm, (a = (y : V) ∨ Γ.Adj a y) →
        ∃ y' : SmVert Δ sm, (b = (y' : V) ∨ Γ.Adj b y') ∧ (sigmaGraph Γ Δ sm).Reachable y y' := by
    intro a b hab
    induction hab with
    | refl => exact fun y hy => ⟨y, hy, SimpleGraph.Reachable.refl y⟩
    | @tail b c _ hbc ih =>
      intro y hy
      obtain ⟨y', hy', hr⟩ := ih y hy
      obtain ⟨hb, hc, hbc⟩ := hbc
      by_cases hbsm : sm b
      · have hby : b = (y' : V) := by
          rcases hy' with hy' | hy'
          · exact hy'
          · exact absurd y'.2.2 ((h.bip _ _ hy').1 hbsm)
        exact ⟨y', Or.inr (hby ▸ hbc.symm), hr⟩
      · have hby : Γ.Adj b y' := by
          rcases hy' with hy' | hy'
          · exact absurd (hy' ▸ y'.2.2) hbsm
          · exact hy'
        have hcsm : sm c := h.sm_of_adj_not_sm hbsm hbc
        refine ⟨⟨c, hc, hcsm⟩, Or.inl rfl, ?_⟩
        by_cases hcy : c = (y' : V)
        · have : (⟨c, hc, hcsm⟩ : SmVert Δ sm) = y' := Subtype.ext hcy
          rw [this]
          exact hr
        · exact hr.trans (SimpleGraph.Adj.reachable
            (sigmaGraph_adj.2 ⟨fun hh => hcy hh.symm, b, hby.symm, hbc⟩))
  intro u v
  obtain ⟨y', hy', hr⟩ := key u v (h.conn u u.2.1 v v.2.1) u (Or.inl rfl)
  have hvy : (v : V) = y' := by
    rcases hy' with hy' | hy'
    · exact hy'
    · exact absurd y'.2.2 ((h.bip _ _ hy').1 v.2.2)
  rw [show v = y' from Subtype.ext hvy]
  exact hr

section Act

variable {A : Type} [Group A] [MulAction A V]

private theorem smul_eq_of_fix_two (h : SubdivCubic Γ Δ sm) {n : A}
    (hadj : ∀ u v : V, Γ.Adj (n • u) (n • v) ↔ Γ.Adj u v) (hn : ∀ v ∈ Δ, n • v ∈ Δ) {y e₁ e₂ : V}
    (hy : y ∈ Δ) (hsm : sm y) (he₁ : Γ.Adj y e₁) (he₂ : Γ.Adj y e₂) (hne : e₁ ≠ e₂)
    (hf₁ : n • e₁ = e₁) (hf₂ : n • e₂ = e₂) : n • y = y := by
  by_contra hny
  refine hne (h.simple y hy hsm e₁ e₂ (n • y) he₁ he₂ (hn y hy) hny ?_ ?_)
  · have := (hadj y e₁).2 he₁
    rw [hf₁] at this
    exact this.symm
  · have := (hadj y e₂).2 he₂
    rw [hf₂] at this
    exact this.symm

private theorem smul_eq_of_fix_edge (h : SubdivCubic Γ Δ sm) {n : A}
    (hadj : ∀ u v : V, Γ.Adj (n • u) (n • v) ↔ Γ.Adj u v) (hn : ∀ v ∈ Δ, n • v ∈ Δ) {y e x : V}
    (hy : y ∈ Δ) (hsm : sm y) (hye : Γ.Adj y e) (hfy : n • y = y) (hfe : n • e = e)
    (hx : x ∈ Δ) (hex : Γ.Adj e x) (hxy : x ≠ y) : n • x = x := by
  obtain ⟨heΔ, hesm⟩ := h.nbr_of_sm hy hsm hye
  have h₁ : Γ.Adj e (n • x) := by
    have := (hadj e x).2 hex
    rwa [hfe] at this
  exact h.eq_of_ne heΔ hesm hy (hn x hx) hx hye.symm h₁ hex
    (fun heq => hxy (smul_left_cancel n (heq.trans hfy.symm))) hxy

private theorem smul_eq_of_fix_end (h : SubdivCubic Γ Δ sm) {n : A}
    (hadj : ∀ u v : V, Γ.Adj (n • u) (n • v) ↔ Γ.Adj u v) {y e x : V} (hy : y ∈ Δ) (hsm : sm y)
    (hye : Γ.Adj y e) (hfy : n • y = y) (hx : x ∈ Δ) (hxy : x ≠ y) (hex : Γ.Adj e x)
    (hfx : n • x = x) : n • e = e := by
  refine (h.simple y hy hsm e (n • e) x hye ?_ hx hxy hex ?_).symm
  · have := (hadj y e).2 hye
    rwa [hfy] at this
  · have := (hadj e x).2 hex
    rwa [hfx] at this

@[instance_reducible] private def smAct (N : Subgroup A) (hNΔ : ∀ n ∈ N, ∀ v ∈ Δ, n • v ∈ Δ)
    (hNsm : ∀ n ∈ N, ∀ v, sm (n • v) ↔ sm v) : MulAction ↥N (SmVert Δ sm) where
  smul n y := ⟨(n : A) • (y : V), hNΔ n n.2 y y.2.1, (hNsm n n.2 y).2 y.2.2⟩
  one_smul y := Subtype.ext (one_smul A (y : V))
  mul_smul m n y := Subtype.ext (mul_smul (m : A) (n : A) (y : V))

private theorem sigma_adj_smul {N : Subgroup A} [MulAction ↥N (SmVert Δ sm)]
    (hadj : ∀ (a : A) (u v : V), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V))
    (a : ↥N) (u v : SmVert Δ sm) :
    (sigmaGraph Γ Δ sm).Adj (a • u) (a • v) ↔ (sigmaGraph Γ Δ sm).Adj u v := by
  simp only [sigmaGraph_adj, hval]
  constructor
  · rintro ⟨hne, e, h₁, h₂⟩
    refine ⟨fun hh => hne (by rw [hh]), (a : A)⁻¹ • e, ?_, ?_⟩
    · have := (hadj (a : A)⁻¹ _ _).2 h₁
      rwa [inv_smul_smul] at this
    · have := (hadj (a : A)⁻¹ _ _).2 h₂
      rwa [inv_smul_smul] at this
  · rintro ⟨hne, e, h₁, h₂⟩
    exact ⟨fun hh => hne (smul_left_cancel _ hh), (a : A) • e, (hadj _ _ _).2 h₁,
      (hadj _ _ _).2 h₂⟩

private theorem sigma_htrans {N : Subgroup A} [MulAction ↥N (SmVert Δ sm)]
    (hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V))
    (htrans : ∀ y ∈ Δ, sm y → ∀ y' ∈ Δ, sm y' → ∃ n ∈ N, n • y = y') (u v : SmVert Δ sm) :
    ∃ a : ↥N, a • u = v := by
  obtain ⟨n, hn, hnu⟩ := htrans u u.2.1 u.2.2 v v.2.1 v.2.2
  exact ⟨⟨n, hn⟩, Subtype.ext (by rw [hval]; exact hnu)⟩

private theorem sigma_hloc {N : Subgroup A} [MulAction ↥N (SmVert Δ sm)]
    (h : SubdivCubic Γ Δ sm)
    (hadj : ∀ (a : A) (u v : V), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V))
    (hloc : ∀ y ∈ Δ, sm y → ∀ e e', Γ.Adj y e → Γ.Adj y e' →
      ∃ n ∈ N, n • y = y ∧ n • e = e')
    (w u v : SmVert Δ sm) (hwu : (sigmaGraph Γ Δ sm).Adj w u)
    (hwv : (sigmaGraph Γ Δ sm).Adj w v) :
    ∃ a ∈ MulAction.stabilizer ↥N w, a • u = v := by
  obtain ⟨hwu₁, e, hwe, heu⟩ := sigmaGraph_adj.1 hwu
  obtain ⟨hwv₁, e', hwe', hev⟩ := sigmaGraph_adj.1 hwv
  obtain ⟨n, hn, hnw, hne⟩ := hloc w w.2.1 w.2.2 e e' hwe hwe'
  refine ⟨⟨n, hn⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext (by rw [hval]; exact hnw)),
    Subtype.ext ?_⟩
  rw [hval]
  obtain ⟨he'Δ, he'sm⟩ := h.nbr_of_sm w.2.1 w.2.2 hwe'
  have hnuΔ : n • (u : V) ∈ Δ := by
    have := (((⟨n, hn⟩ : ↥N) • u).2).1
    rwa [hval] at this
  have hnu : Γ.Adj e' (n • (u : V)) := by
    have := (hadj n e u).2 heu
    rwa [hne] at this
  exact h.eq_of_ne he'Δ he'sm w.2.1 hnuΔ v.2.1 hwe'.symm hnu hev
    (fun hh => hwu₁ (smul_left_cancel n (hh.trans hnw.symm)).symm) (fun hh => hwv₁ hh.symm)

private theorem sigma_harc {N : Subgroup A} [MulAction ↥N (SmVert Δ sm)]
    (hadj : ∀ (a : A) (u v : V), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V))
    (hvt : ∀ u v : SmVert Δ sm, ∃ a : ↥N, a • u = v)
    (hlc : ∀ w u v : SmVert Δ sm, (sigmaGraph Γ Δ sm).Adj w u → (sigmaGraph Γ Δ sm).Adj w v →
      ∃ a ∈ MulAction.stabilizer ↥N w, a • u = v) (u v u' v' : SmVert Δ sm)
    (huv : (sigmaGraph Γ Δ sm).Adj u v) (hu'v' : (sigmaGraph Γ Δ sm).Adj u' v') :
    ∃ a : ↥N, a • u = u' ∧ a • v = v' := by
  obtain ⟨a₁, ha₁⟩ := hvt u u'
  have h₁ : (sigmaGraph Γ Δ sm).Adj u' (a₁ • v) := by
    rw [← ha₁]
    exact (sigma_adj_smul hadj hval a₁ u v).2 huv
  obtain ⟨a₂, ha₂, ha₂'⟩ := hlc u' (a₁ • v) v' h₁ hu'v'
  refine ⟨a₂ * a₁, ?_, ?_⟩
  · rw [mul_smul, ha₁]
    exact MulAction.mem_stabilizer_iff.1 ha₂
  · rw [mul_smul]
    exact ha₂'

private theorem sigma_fix5 [Finite A] {N : Subgroup A} [MulAction ↥N (SmVert Δ sm)]
    (h : SubdivCubic Γ Δ sm)
    (hadj : ∀ (a : A) (u v : V), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V))
    (htrans : ∀ y ∈ Δ, sm y → ∀ y' ∈ Δ, sm y' → ∃ n ∈ N, n • y = y')
    (hloc : ∀ y ∈ Δ, sm y → ∀ e e', Γ.Adj y e → Γ.Adj y e' →
      ∃ n ∈ N, n • y = y ∧ n • e = e')
    (y₀ : SmVert Δ sm) (Q : Arc (sigmaGraph Γ Δ sm) 5) (a : ↥N)
    (hQ : ∀ i, i ≤ 5 → a • Q.vert i = Q.vert i) : ∀ w : SmVert Δ sm, a • w = w := by
  haveI : Nonempty (SmVert Δ sm) := ⟨y₀⟩
  exact fixes_of_fixes_fiveArc (W := SmVert Δ sm) (Γ := sigmaGraph Γ Δ sm)
    ⟨sigma_preconnected h⟩ (sigma_card h) (sigma_adj_smul hadj hval) (sigma_htrans hval htrans)
    (fun _ => inferInstance) (sigma_hloc h hadj hval hloc) Q a hQ

end Act

section Main

variable {A : Type} [Group A] [MulAction A V] [Finite A]
  (hadj : ∀ (a : A) (u v : V), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
  (N : Subgroup A)
  (hNΔ : ∀ n ∈ N, ∀ v ∈ Δ, n • v ∈ Δ)
  (hNsm : ∀ n ∈ N, ∀ v, sm (n • v) ↔ sm v)
  (htrans : ∀ y ∈ Δ, sm y → ∀ y' ∈ Δ, sm y' → ∃ n ∈ N, n • y = y')
  (hloc : ∀ y ∈ Δ, sm y → ∀ e e', Γ.Adj y e → Γ.Adj y e' → ∃ n ∈ N, n • y = y ∧ n • e = e')

include hadj hNΔ hNsm htrans hloc

theorem fixes_of_fixes_arc (h : SubdivCubic Γ Δ sm) {n : A} (hn : n ∈ N) (P : Arc Γ 10)
    (hP0 : sm (P.vert 0)) (hPΔ : ∀ i, i ≤ 10 → P.vert i ∈ Δ)
    (hPn : ∀ i, i ≤ 10 → n • P.vert i = P.vert i) : ∀ v ∈ Δ, n • v = v := by
  have hpar : ∀ i, i ≤ 10 → (sm (P.vert i) ↔ i % 2 = 0) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨fun _ => rfl, fun _ => hP0⟩
    | succ k ih =>
      intro hk
      have h₁ := h.bip _ _ (P.adj k (by omega))
      have h₂ := ih (by omega)
      constructor
      · intro hs
        have h₃ : ¬ sm (P.vert k) := fun hk' => (h₁.1 hk') hs
        have h₄ : ¬ k % 2 = 0 := fun hk0 => h₃ (h₂.2 hk0)
        omega
      · intro hk1
        have h₃ : ¬ k % 2 = 0 := by omega
        by_contra hs
        exact h₃ (h₂.1 (h₁.2 hs))
  letI : MulAction ↥N (SmVert Δ sm) := smAct N hNΔ hNsm
  have hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V) :=
    fun _ _ => rfl
  obtain ⟨Q, hQvert⟩ : ∃ Q : Arc (sigmaGraph Γ Δ sm) 5,
      ∀ i, i ≤ 5 → ((Q.vert i : SmVert Δ sm) : V) = P.vert (2 * i) := by
    refine ⟨{ vert := fun j => ⟨P.vert (2 * min j 5), hPΔ _ (by omega),
        (hpar _ (by omega)).2 (by omega)⟩, adj := ?_, nb := ?_ }, ?_⟩
    · intro j hj
      have e₁ : min j 5 = j := by omega
      have e₂ : min (j + 1) 5 = j + 1 := by omega
      have e₃ : 2 * (j + 1) = 2 * j + 2 := by omega
      refine sigmaGraph_adj.2 ⟨?_, P.vert (2 * j + 1), ?_, ?_⟩
      · show P.vert (2 * min j 5) ≠ P.vert (2 * min (j + 1) 5)
        rw [e₁, e₂, e₃]
        exact P.nb (2 * j) (by omega)
      · show Γ.Adj (P.vert (2 * min j 5)) (P.vert (2 * j + 1))
        rw [e₁]
        exact P.adj (2 * j) (by omega)
      · show Γ.Adj (P.vert (2 * j + 1)) (P.vert (2 * min (j + 1) 5))
        rw [e₂, e₃]
        exact P.adj (2 * j + 1) (by omega)
    · intro j hj heq
      have heq' : P.vert (2 * min j 5) = P.vert (2 * min (j + 2) 5) := congrArg Subtype.val heq
      have e₁ : min j 5 = j := by omega
      have e₂ : min (j + 2) 5 = j + 2 := by omega
      have e₃ : 2 * (j + 2) = 2 * j + 4 := by omega
      rw [e₁, e₂, e₃] at heq'
      have hs₂ : sm (P.vert (2 * j + 2)) := (hpar _ (by omega)).2 (by omega)
      exact P.nb (2 * j + 1) (by omega) (h.simple (P.vert (2 * j + 2)) (hPΔ _ (by omega)) hs₂
        (P.vert (2 * j + 1)) (P.vert (2 * j + 3)) (P.vert (2 * j))
        (P.adj (2 * j + 1) (by omega)).symm (P.adj (2 * j + 2) (by omega)) (hPΔ _ (by omega))
        (P.nb (2 * j) (by omega)) (P.adj (2 * j) (by omega)).symm
        (by rw [heq']; exact P.adj (2 * j + 3) (by omega)))
    · intro i hi
      show P.vert (2 * min i 5) = P.vert (2 * i)
      rw [min_eq_left hi]
  have hQ : ∀ i, i ≤ 5 → (⟨n, hn⟩ : ↥N) • Q.vert i = Q.vert i := by
    intro i hi
    refine Subtype.ext ?_
    rw [hval]
    show n • ((Q.vert i : SmVert Δ sm) : V) = ((Q.vert i : SmVert Δ sm) : V)
    rw [hQvert i hi]
    exact hPn _ (by omega)
  have hall := sigma_fix5 h hadj hval htrans hloc (⟨P.vert 0, hPΔ 0 (by omega), hP0⟩ :
    SmVert Δ sm) Q ⟨n, hn⟩ hQ
  have hsmfix : ∀ y : V, y ∈ Δ → sm y → n • y = y := fun y hy hsy => by
    have := congrArg Subtype.val (hall ⟨y, hy, hsy⟩)
    rw [hval] at this
    exact this
  intro v hv
  by_cases hsv : sm v
  · exact hsmfix v hv hsv
  · obtain ⟨y₁, y₂, hne, hy⟩ := h.two v hv hsv
    have h₁ := (hy y₁).2 (Or.inl rfl)
    have h₂ := (hy y₂).2 (Or.inr rfl)
    have hs₁ : sm y₁ := h.sm_of_adj_not_sm hsv h₁.2
    have hs₂ : sm y₂ := h.sm_of_adj_not_sm hsv h₂.2
    have hf₁ := hsmfix y₁ h₁.1 hs₁
    have hf₂ := hsmfix y₂ h₂.1 hs₂
    refine (h.simple y₁ h₁.1 hs₁ v (n • v) y₂ h₁.2.symm ?_ h₂.1 hne.symm h₂.2 ?_).symm
    · have := (hadj n y₁ v).2 h₁.2.symm
      rwa [hf₁] at this
    · have := (hadj n v y₂).2 h₂.2
      rwa [hf₂] at this

theorem fixes_nbrs_of_fixes (h : SubdivCubic Γ Δ sm) {n : A} (hn : n ∈ N) {y : V} (hy : y ∈ Δ)
    (hsm : sm y) {e₁ e₂ e₃ : V} (he₁ : Γ.Adj y e₁) (he₂ : Γ.Adj y e₂) (he₃ : Γ.Adj y e₃)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) {y₁ y₂ y₃ : V} (hy₁ : y₁ ∈ Δ)
    (hy₂ : y₂ ∈ Δ) (hy₃ : y₃ ∈ Δ) (h₁ : Γ.Adj e₁ y₁) (h₂ : Γ.Adj e₂ y₂) (h₃ : Γ.Adj e₃ y₃)
    (hy₁y : y₁ ≠ y) (hy₂y : y₂ ≠ y) (hy₃y : y₃ ≠ y) (hfy : ∀ v, Γ.Adj y v → n • v = v)
    (hfy₂ : ∀ v, Γ.Adj y₂ v → n • v = v) (hfy₃ : ∀ v, Γ.Adj y₃ v → n • v = v) :
    ∀ v, Γ.Adj y₁ v → n • v = v := by
  have hnΔ : ∀ v ∈ Δ, n • v ∈ Δ := hNΔ n hn
  have hadjn : ∀ u v : V, Γ.Adj (n • u) (n • v) ↔ Γ.Adj u v := hadj n
  have hny : n • y = y :=
    smul_eq_of_fix_two h hadjn hnΔ hy hsm he₁ he₂ h₁₂ (hfy e₁ he₁) (hfy e₂ he₂)
  have hs₁ : sm y₁ := h.sm_of_adj_not_sm (h.nbr_of_sm hy hsm he₁).2 h₁
  have hs₂ : sm y₂ := h.sm_of_adj_not_sm (h.nbr_of_sm hy hsm he₂).2 h₂
  have hs₃ : sm y₃ := h.sm_of_adj_not_sm (h.nbr_of_sm hy hsm he₃).2 h₃
  have hd₁₂ : y₁ ≠ y₂ := fun heq =>
    h₁₂ (h.simple y hy hsm e₁ e₂ y₁ he₁ he₂ hy₁ hy₁y h₁ (by rw [heq]; exact h₂))
  have hd₁₃ : y₁ ≠ y₃ := fun heq =>
    h₁₃ (h.simple y hy hsm e₁ e₃ y₁ he₁ he₃ hy₁ hy₁y h₁ (by rw [heq]; exact h₃))
  have hd₂₃ : y₂ ≠ y₃ := fun heq =>
    h₂₃ (h.simple y hy hsm e₂ e₃ y₂ he₂ he₃ hy₂ hy₂y h₂ (by rw [heq]; exact h₃))
  have hny₁ : n • y₁ = y₁ :=
    smul_eq_of_fix_edge h hadjn hnΔ hy hsm he₁ hny (hfy e₁ he₁) hy₁ h₁ hy₁y
  have hny₂ : n • y₂ = y₂ :=
    smul_eq_of_fix_edge h hadjn hnΔ hy hsm he₂ hny (hfy e₂ he₂) hy₂ h₂ hy₂y
  have hny₃ : n • y₃ = y₃ :=
    smul_eq_of_fix_edge h hadjn hnΔ hy hsm he₃ hny (hfy e₃ he₃) hy₃ h₃ hy₃y
  letI : MulAction ↥N (SmVert Δ sm) := smAct N hNΔ hNsm
  have hval : ∀ (a : ↥N) (y : SmVert Δ sm), ((a • y : SmVert Δ sm) : V) = (a : A) • (y : V) :=
    fun _ _ => rfl
  have hfixS : ∀ (z : V) (hz : z ∈ Δ) (hzs : sm z), n • z = z → (∀ v, Γ.Adj z v → n • v = v) →
      ∀ x : SmVert Δ sm, (sigmaGraph Γ Δ sm).Adj ⟨z, hz, hzs⟩ x → (⟨n, hn⟩ : ↥N) • x = x := by
    intro z hz hzs hnz hfz x hx
    obtain ⟨hxz, e, hze, hex⟩ := sigmaGraph_adj.1 hx
    refine Subtype.ext ?_
    rw [hval]
    exact smul_eq_of_fix_edge h hadjn hnΔ hz hzs hze hnz (hfz e hze) x.2.1 hex
      (fun hh => hxz hh.symm)
  have h5 := sigma_fix5 h hadj hval htrans hloc (⟨y, hy, hsm⟩ : SmVert Δ sm)
  have harc := sigma_harc hadj hval (sigma_htrans hval htrans) (sigma_hloc h hadj hval hloc)
  have key := fixes_nbrs_of_fixes_two_stars (Γ := sigmaGraph Γ Δ sm) (sigma_card h)
    (sigma_adj_smul hadj hval) harc h5
    (v := ⟨y, hy, hsm⟩) (w₁ := ⟨y₁, hy₁, hs₁⟩) (w₂ := ⟨y₂, hy₂, hs₂⟩) (w₃ := ⟨y₃, hy₃, hs₃⟩)
    (sigmaGraph_adj.2 ⟨hy₁y.symm, e₁, he₁, h₁⟩) (sigmaGraph_adj.2 ⟨hy₂y.symm, e₂, he₂, h₂⟩)
    (sigmaGraph_adj.2 ⟨hy₃y.symm, e₃, he₃, h₃⟩)
    (fun heq => hd₁₂ (congrArg Subtype.val heq)) (fun heq => hd₁₃ (congrArg Subtype.val heq))
    (fun heq => hd₂₃ (congrArg Subtype.val heq)) (n := ⟨n, hn⟩)
    (hfixS y hy hsm hny hfy) (hfixS y₂ hy₂ hs₂ hny₂ hfy₂) (hfixS y₃ hy₃ hs₃ hny₃ hfy₃)
  intro v hv
  obtain ⟨hvΔ, hvsm⟩ := h.nbr_of_sm hy₁ hs₁ hv
  obtain ⟨b, hbΔ, hvb, hby₁, hbsm⟩ := h.exists_other_nbr hvΔ hvsm hy₁ hv.symm
  have hb : n • b = b := by
    have := congrArg Subtype.val (key ⟨b, hbΔ, hbsm⟩
      (sigmaGraph_adj.2 ⟨fun hh => hby₁ hh.symm, v, hv, hvb⟩))
    rw [hval] at this
    exact this
  exact smul_eq_of_fix_end h hadjn hy₁ hs₁ hv hny₁ hbΔ hby₁ hvb hb

end Main

end SubdivCubic

end CFSG.Quasithin.Fan86.Tutte
