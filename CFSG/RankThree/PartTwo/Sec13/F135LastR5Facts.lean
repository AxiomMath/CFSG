module

public import CFSG.RankThree.PartTwo.Sec13.F135LastParts
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2Plane

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem r5gl_Y_inf_eq_bot {p : ℕ} (hp : p.Prime) {Y Φ : Subgroup G} (hY : Nat.card Y = p)
    (hYΦ : ¬ Y ≤ Φ) : Y ⊓ Φ = ⊥ := by
  have hd : Nat.card (Y ⊓ Φ : Subgroup G) ∣ p := hY ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    apply hYΦ
    have hYeq : Y ⊓ Φ = Y := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hY])
    rw [← hYeq]
    exact inf_le_right

theorem r5gl_conj_mem_centralizer {S : Set G} {g x : G} (hg : g ∈ Subgroup.centralizer S)
    (hx : x ∈ Subgroup.centralizer S) : g * x * g⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hg hx ⊢
  intro h hh
  have h1 : h * g = g * h := hg h hh
  have h2 : h * x = x * h := hx h hh
  have h3 : g⁻¹ * h = h * g⁻¹ := by
    calc g⁻¹ * h = g⁻¹ * (h * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * h) * g⁻¹ := by rw [h1]
      _ = h * g⁻¹ := by group
  calc h * (g * x * g⁻¹) = (h * g) * x * g⁻¹ := by group
    _ = (g * h) * x * g⁻¹ := by rw [h1]
    _ = g * (h * x) * g⁻¹ := by group
    _ = g * (x * h) * g⁻¹ := by rw [h2]
    _ = g * x * (h * g⁻¹) := by group
    _ = g * x * (g⁻¹ * h) := by rw [h3]
    _ = (g * x * g⁻¹) * h := by group

theorem r5gl_mem_centralizer_sup {f u : G} {Y : Subgroup G}
    (hfY : f ∈ Subgroup.centralizer (Y : Set G)) (hfu : f ∈ Subgroup.centralizer ({u} : Set G)) :
    f ∈ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
  have hle : Y ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({f} : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact (Subgroup.mem_centralizer_iff.mp hfY y hy).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk]
      exact (Subgroup.mem_centralizer_iff.mp hfu u (Set.mem_singleton u)).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (hle hh) f (Set.mem_singleton f)).symm

theorem r5gl_commutator_le {A B : Subgroup G}
    (hBA : ∀ b ∈ B, ∀ x ∈ A, b * x * b⁻¹ ∈ A) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := mul_mem ha (hBA b hb a⁻¹ (inv_mem ha))
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact h

theorem r5gl_commutator_conj {A B : Subgroup G} {g : G}
    (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ B) {n : G}
    (hn : n ∈ ⁅A, B⁆) : g * n * g⁻¹ ∈ ⁅A, B⁆ := by
  have hle : Subgroup.map (MulAut.conj g).toMonoidHom ⁅A, B⁆ ≤ ⁅A, B⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hA x hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hB x hx
  exact hle (Subgroup.mem_map_of_mem _ hn)

theorem r5gl_A_conj {u : G} {Y D : Subgroup G} {b x : G}
    (hb : b ∈ D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G))
    (hx : x ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G)) :
    b * x * b⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) := by
  have hbT : b ∈ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hb).2
  have huT : u ∈ ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :=
    (le_sup_right : Subgroup.zpowers u ≤ Y ⊔ Subgroup.zpowers u) (Subgroup.mem_zpowers u)
  have hbu : b ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact Subgroup.mem_centralizer_iff.mp hbT u huT
  have hbY : b ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hbT y ((le_sup_left : Y ≤ Y ⊔ Subgroup.zpowers u) hy)
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨(CFSG.RankThree.PartTwo.Sec13.F135Last.mem_pCoreOf_conj 2 _ hbu x).mp hxP,
    r5gl_conj_mem_centralizer hbY hxC⟩

theorem r5gl_B_conj {u : G} {Y D : Subgroup G} {g x : G}
    (hg : g ∈ D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G))
    (hx : x ∈ D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)) :
    g * x * g⁻¹ ∈ D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
  obtain ⟨hgD, hgC⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hgD hxD) (inv_mem hgD),
    r5gl_conj_mem_centralizer hgC hxC⟩

theorem r5gl_S_le_B {u : G} {Y D : Subgroup G} {f : G}
    (hf : f ∈ D ⊓ Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) :
    f ∈ D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
  obtain ⟨hfDY, hfu⟩ := Subgroup.mem_inf.mp hf
  obtain ⟨hfD, hfY⟩ := Subgroup.mem_inf.mp hfDY
  exact Subgroup.mem_inf.mpr ⟨hfD, r5gl_mem_centralizer_sup hfY hfu⟩

theorem r5g_E_facts {p : ℕ} [Fact p.Prime] {D Y : Subgroup G} (hD : IsPGroup p D)
    (hexp : ∀ x ∈ D, x ^ p = 1) (hYD : Y ≤ D) (hY : Nat.card Y = p)
    (hYΦ : ¬ Y ≤ frattiniOf D) :
    IsPGroup p (eOf D Y) ∧ (∀ e ∈ eOf D Y, e ^ p = 1) ∧ Y.subgroupOf (cM Y) ≤ eOf D Y ∧
      ∀ x ∈ eOf D Y, ∀ y ∈ eOf D Y, x * y * x⁻¹ * y⁻¹ ∈ Y.subgroupOf (cM Y) →
        x * y * x⁻¹ * y⁻¹ = 1 := by
  have hp : p.Prime := Fact.out
  have hmem : ∀ e : cM Y, e ∈ eOf D Y ↔ (e : G) ∈ D := by
    intro e
    show (e : G) ∈ D ⊓ cM Y ↔ (e : G) ∈ D
    rw [Subgroup.mem_inf]
    exact ⟨fun h => (Subgroup.mem_inf.mp h).1, fun h => Subgroup.mem_inf.mpr ⟨h, e.2⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsPGroup.comap_subtype (hD.to_le (inf_le_left : D ⊓ cM Y ≤ D))
  · intro e he
    apply Subtype.ext
    simpa using hexp _ ((hmem e).mp he)
  · intro y hy
    rw [hmem y]
    exact hYD (Subgroup.mem_subgroupOf.mp hy)
  · intro x hx y hy hc
    have hxD : (x : G) ∈ D := (hmem x).mp hx
    have hyD : (y : G) ∈ D := (hmem y).mp hy
    have hcY : ⁅(x : G), (y : G)⁆ ∈ Y := by
      have h := Subgroup.mem_subgroupOf.mp hc
      rw [commutatorElement_def]
      simpa using h
    have hcΦ : ⁅(x : G), (y : G)⁆ ∈ frattiniOf D :=
      CFSG.RankThree.PartTwo.Sec13.F135Last.r2a_comm_mem hD hexp hxD hyD
    have hmemb : ⁅(x : G), (y : G)⁆ ∈ Y ⊓ frattiniOf D :=
      Subgroup.mem_inf.mpr ⟨hcY, hcΦ⟩
    rw [r5gl_Y_inf_eq_bot hp hY hYΦ, Subgroup.mem_bot] at hmemb
    apply Subtype.ext
    rw [commutatorElement_def] at hmemb
    simpa using hmemb

theorem r5g_U_facts {u : G} {Y D U : Subgroup G}
    (hU : U = ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G),
      D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆) :
    IsPGroup 2 U ∧ ∀ f ∈ D ⊓ cM Y ⊓ Subgroup.centralizer ({u} : Set G),
      f ∈ Subgroup.normalizer (U : Set G) := by
  subst hU
  have hpA : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G) :=
    (CFSG.RankThree.PartTwo.Sec13.F135Last.isPGroup_pCoreOf 2
      (Subgroup.centralizer ({u} : Set G))).to_inf_left
  refine ⟨hpA.to_le (r5gl_commutator_le fun b hb x hx => r5gl_A_conj hb hx), ?_⟩
  intro f hf
  have hfB := r5gl_S_le_B hf
  have hfinv : f⁻¹ ∈ D ⊓ Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer ({u} : Set G) :=
    inv_mem hf
  have hfinvB := r5gl_S_le_B hfinv
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact r5gl_commutator_conj (fun x hx => r5gl_A_conj hfB hx)
      (fun x hx => r5gl_B_conj hfB hx) hn
  · intro hn
    have h := r5gl_commutator_conj (fun x hx => r5gl_A_conj hfinvB hx)
      (fun x hx => r5gl_B_conj hfinvB hx) hn
    have e : f⁻¹ * (f * n * f⁻¹) * f⁻¹⁻¹ = n := by group
    rwa [e] at h

end CFSG.RankThree.PartTwo.Sec13.F135Last
