module

import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
import CFSG.LocalAnalysis.UniquenessCase.UC6Grp
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uniqueFourConj_zpowers (g w : G) :
    uniqueFourConj g (Subgroup.zpowers w) =
      Subgroup.zpowers ((MulAut.conj g⁻¹) w) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (map_zpow (MulAut.conj g⁻¹) w k).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨w ^ k, ⟨k, rfl⟩, by rw [map_zpow]; exact hk⟩

private theorem inf_eq_bot_of_card_prime {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hAB : A ≠ B) : A ⊓ B = ⊥ := by
  have hdvd : Nat.card ↥(A ⊓ B) ∣ p := by
    have h1 : Nat.card ↥((A ⊓ B).subgroupOf A) ∣ Nat.card ↥A :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card ↥((A ⊓ B).subgroupOf A) = Nat.card ↥(A ⊓ B) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rwa [h2, hA] at h1
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have heq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hA])
    have hBA : A ≤ B := by rw [← heq]; exact inf_le_right
    exact hAB (Subgroup.eq_of_le_of_card_ge hBA (by rw [hA, hB]))

private theorem sup_eq_of_point_ne {p : ℕ} (hp : p.Prime) {E A Z : Subgroup G}
    (hEcard : Nat.card E = p ^ 2) (hA : Nat.card A = p) (hAE : A ≤ E)
    (hZ : Nat.card Z = p) (hZE : Z ≤ E) (hZA : Z ≠ A) : A ⊔ Z = E := by
  have hle : A ⊔ Z ≤ E := sup_le hAE hZE
  have hlt : Nat.card A < Nat.card ↥(A ⊔ Z) := by
    apply Subgroup.card_lt_of_lt
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    have hZA' : Z ≤ A := hEq ▸ le_sup_right
    exact hZA (Subgroup.eq_of_le_of_card_ge hZA' (by rw [hA, hZ]))
  have hdvd : Nat.card ↥(A ⊔ Z) ∣ p ^ 2 := by
    have h1 : Nat.card ↥((A ⊔ Z).subgroupOf E) ∣ Nat.card ↥E :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card ↥((A ⊔ Z).subgroupOf E) = Nat.card ↥(A ⊔ Z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rwa [h2, hEcard] at h1
  have hcard : Nat.card ↥(A ⊔ Z) = p ^ 2 := by
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk2, hk⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      rw [hk, hA] at hlt
      exact absurd hlt (by have := hp.two_le; omega)
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [pow_one] at hk
      rw [hk, hA] at hlt
      exact lt_irrefl _ hlt
    have hk_eq : k = 2 := by omega
    rw [hk, hk_eq]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hEcard])

private theorem conj_eq_of_mem_centralizer {A R : Subgroup G} (h : R ≤ centralizer (A : Set G))
    {r : G} (hr : r ∈ R) {a : G} (ha : a ∈ A) : r⁻¹ * a * r = a := by
  have hc : a * r = r * a := (Subgroup.mem_centralizer_iff.mp (h hr)) a ha
  calc r⁻¹ * a * r = r⁻¹ * (a * r) := by group
    _ = r⁻¹ * (r * a) := by rw [hc]
    _ = a := by group

private theorem le_normalizer_of_commutator_le {E A R : Subgroup G}
    (hRC : ⁅R, E⁆ ≤ A) (hAE : A ≤ E) : R ≤ normalizer (A : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro r hr a ha
  have hcom : ⁅r, a⁆ ∈ A := (Subgroup.commutator_le.mp hRC) r hr a (hAE ha)
  have : r * a * r⁻¹ = ⁅r, a⁆ * a := by rw [commutatorElement_def]; group
  rw [this]
  exact A.mul_mem hcom ha

private theorem le_centralizer_of_card_prime {p : ℕ} (hp : p.Prime) {C R : Subgroup G}
    (hC : Nat.card C = p) (hRnorm : R ≤ normalizer (C : Set G)) (hRp : IsPGroup p R) :
    R ≤ centralizer (C : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ↥R →* ↥(normalizer (C : Set G)) :=
    { toFun := fun r => ⟨r, hRnorm r.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  letI : MulAction ↥R ↥C := MulAction.compHom ↥C f
  have hmod := hRp.card_modEq_card_fixedPoints ↥C
  rw [Nat.ModEq, hC] at hmod
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints ↥R ↥C) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa [Nat.mod_self] using hmod.symm
  have hle : Nat.card (MulAction.fixedPoints ↥R ↥C) ≤ p := by
    have := Nat.card_le_card_of_injective
      (fun x : MulAction.fixedPoints ↥R ↥C => (x : ↥C)) (fun a b h => Subtype.ext h)
    rwa [hC] at this
  have hfix1 : (1 : ↥C) ∈ MulAction.fixedPoints ↥R ↥C := by
    rw [MulAction.mem_fixedPoints]
    intro r
    rw [MulAction.compHom_smul_def]
    exact smul_one (f r)
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥R ↥C) :=
    Finite.card_pos_iff.mpr ⟨⟨1, hfix1⟩⟩
  have hcard : Nat.card (MulAction.fixedPoints ↥R ↥C) = p :=
    le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have hfixall : MulAction.fixedPoints ↥R ↥C = Set.univ :=
    (Set.eq_univ_iff_ncard _).mpr (by rw [← Nat.card_coe_set_eq, hcard, hC])
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hmem : (⟨c, hc⟩ : ↥C) ∈ MulAction.fixedPoints ↥R ↥C := by
    rw [hfixall]; exact Set.mem_univ _
  rw [MulAction.mem_fixedPoints] at hmem
  have h1 := hmem ⟨r, hr⟩
  show c * r = r * c
  have h2 : (r : G) * c * (r : G)⁻¹ = c := by
    rw [MulAction.compHom_smul_def] at h1
    exact congrArg Subtype.val h1
  have h3 : (r : G) * c = c * (r : G) := by
    calc (r : G) * c = (r : G) * c * (r : G)⁻¹ * (r : G) := by group
      _ = c * (r : G) := by rw [h2]
  exact h3.symm

private theorem exists_mul_ne_of_not_le_centralizer {E R : Subgroup G}
    (h : ¬ R ≤ centralizer (E : Set G)) :
    ∃ r ∈ R, ∃ x ∈ E, r * x * r⁻¹ ≠ x := by
  by_contra hc
  apply h
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_contra hne
  apply hc
  refine ⟨r, hr, x, hx, fun hconj => hne (?_ : x * r = r * x)⟩
  have hxr : r * x = x * r := by
    calc r * x = (r * x * r⁻¹) * r := by group
      _ = x * r := by rw [hconj]
  exact hxr.symm

private theorem point_eq_zpowers_mul {p : ℕ} (hp : p.Prime) {E A Z : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hA : Nat.card A = p)
    (hAE : A ≤ E) {x0 : G} (hx0E : x0 ∈ E) (hx0A : x0 ∉ A)
    (hZ : Nat.card Z = p) (hZE : Z ≤ E) (hZA : Z ≠ A) :
    ∃ a ∈ A, Z = Subgroup.zpowers (x0 * a) := by
  have hsup : A ⊔ Z = E := sup_eq_of_point_ne hp hEcard hA hAE hZ hZE hZA
  have hx0sup : x0 ∈ A ⊔ Z := by rw [hsup]; exact hx0E
  have hcommE : ∀ {u v : G}, u ∈ E → v ∈ E → u * v = v * u := fun {u v} hu hv =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hc : ∀ x ∈ A, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    exact hcommE (hAE hx) (hZE hy)
  obtain ⟨a', ha', z, hz, hxz⟩ := exists_mul_of_mem_sup_of_commute hc hx0sup
  refine ⟨a'⁻¹, A.inv_mem ha', ?_⟩
  have hz_eq : z = x0 * a'⁻¹ := by
    have h1 : z = a'⁻¹ * x0 := by rw [hxz]; group
    rw [h1, hcommE (hAE (A.inv_mem ha')) hx0E]
  have hz1 : z ≠ 1 := by
    intro h
    apply hx0A
    rw [hxz, h, mul_one]
    exact ha'
  have horder : orderOf z = p := by
    have hdvd : orderOf z ∣ p := by
      have h1 : Nat.card ↥((Subgroup.zpowers z).subgroupOf Z) ∣ Nat.card ↥Z :=
        Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card ↥((Subgroup.zpowers z).subgroupOf Z) = Nat.card ↥(Subgroup.zpowers z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hz)).toEquiv
      rwa [h2, Nat.card_zpowers, hZ] at h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  rw [← hz_eq]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers, horder, hZ])).symm

private theorem trans_of_action {p : ℕ} (hp : p.Prime) {E A R : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hAE : A ≤ E)
    (hRp : IsPGroup p R) (hRC : ⁅R, E⁆ ≤ A)
    (hRnt : ¬ R ≤ centralizer (E : Set G)) :
    ∀ Z1 Z2 : Subgroup G, Z1 ≤ E → Nat.card Z1 = p → Z2 ≤ E → Nat.card Z2 = p →
      Z1 ≠ A → Z2 ≠ A → ∃ r ∈ R, uniqueFourConj r Z1 = Z2 := by
  intro Z1 Z2 hZ1E hZ1 hZ2E hZ2 hZ1A hZ2A
  have hRnorm : R ≤ normalizer (A : Set G) := le_normalizer_of_commutator_le hRC hAE
  have hcentA : R ≤ centralizer (A : Set G) :=
    le_centralizer_of_card_prime hp hA hRnorm hRp
  obtain ⟨r0, hr0, x0, hx0E, hx0ne⟩ := exists_mul_ne_of_not_le_centralizer hRnt
  have hcommE : ∀ {u v : G}, u ∈ E → v ∈ E → u * v = v * u := fun {u v} hu hv =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hx0A : x0 ∉ A := by
    intro hxA
    have hc : x0 * r0 = r0 * x0 := (Subgroup.mem_centralizer_iff.mp (hcentA hr0)) x0 hxA
    exact hx0ne (by
      calc r0 * x0 * r0⁻¹ = (r0 * x0) * r0⁻¹ := by group
        _ = (x0 * r0) * r0⁻¹ := by rw [hc]
        _ = x0 := by group)
  have hER : ⁅E, R⁆ ≤ A := by rw [Subgroup.commutator_comm]; exact hRC
  have hmemA : ∀ r : ↥R, (r : G)⁻¹ * x0 * (r : G) * x0⁻¹ ∈ A := by
    intro r
    have h1 : (r : G)⁻¹ * x0 * (r : G) * x0⁻¹ = (r : G)⁻¹ * ⁅x0, (r : G)⁆ * (r : G) := by
      rw [commutatorElement_def]; group
    rw [h1]
    simpa using (Subgroup.le_normalizer_iff.mp hRnorm) _ (R.inv_mem r.2) _
      ((Subgroup.commutator_le.mp hER) x0 hx0E (r : G) r.2)
  let rR : ↥R := ⟨r0, hr0⟩
  have hφr0ne : (r0 : G)⁻¹ * x0 * (r0 : G) * x0⁻¹ ≠ 1 := by
    intro h1
    apply hx0ne
    have h2 : (r0 : G)⁻¹ * x0 * (r0 : G) = x0 := by
      have := congrArg (fun t => t * x0) h1
      simpa [mul_assoc] using this
    calc (r0 : G) * x0 * (r0 : G)⁻¹
        = (r0 : G) * ((r0 : G)⁻¹ * x0 * (r0 : G)) * (r0 : G)⁻¹ := by rw [h2]
      _ = x0 := by group
  let φ : ↥R →* ↥A :=
    { toFun := fun r => ⟨(r : G)⁻¹ * x0 * (r : G) * x0⁻¹, hmemA r⟩
      map_one' := by
        apply Subtype.ext
        show ((1 : ↥R) : G)⁻¹ * x0 * ((1 : ↥R) : G) * x0⁻¹ = 1
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        have hs : (s : G)⁻¹ * ((r : G)⁻¹ * x0 * (r : G) * x0⁻¹) * (s : G) =
            (r : G)⁻¹ * x0 * (r : G) * x0⁻¹ :=
          conj_eq_of_mem_centralizer hcentA s.2 (hmemA r)
        show ((r : G) * (s : G))⁻¹ * x0 * ((r : G) * (s : G)) * x0⁻¹ =
          ((r : G)⁻¹ * x0 * (r : G) * x0⁻¹) * ((s : G)⁻¹ * x0 * (s : G) * x0⁻¹)
        calc ((r : G) * (s : G))⁻¹ * x0 * ((r : G) * (s : G)) * x0⁻¹
            = (s : G)⁻¹ * ((r : G)⁻¹ * x0 * (r : G)) * (s : G) * x0⁻¹ := by group
          _ = (s : G)⁻¹ * (((r : G)⁻¹ * x0 * (r : G) * x0⁻¹) * x0) * (s : G) * x0⁻¹ := by
                group
          _ = ((s : G)⁻¹ * ((r : G)⁻¹ * x0 * (r : G) * x0⁻¹) * (s : G)) *
                ((s : G)⁻¹ * x0 * (s : G)) * x0⁻¹ := by group
          _ = ((r : G)⁻¹ * x0 * (r : G) * x0⁻¹) *
                ((s : G)⁻¹ * x0 * (s : G) * x0⁻¹) := by rw [hs]; group
    }
  have hφr0ne' : φ rR ≠ 1 := fun h => hφr0ne (congrArg Subtype.val h)
  have hrange : φ.range = ⊤ := by
    have hdvd : Nat.card ↥φ.range ∣ p := by
      have h1 : Nat.card ↥φ.range ∣ Nat.card ↥A := Subgroup.card_subgroup_dvd_card _
      rwa [hA] at h1
    have hcard : Nat.card ↥φ.range = p := by
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exfalso
        have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp h1
        have : φ rR ∈ (⊥ : Subgroup ↥A) := by rw [← hbot]; exact ⟨rR, rfl⟩
        exact hφr0ne' (Subgroup.mem_bot.mp this)
      · exact h1
    have htop : Nat.card ↥(⊤ : Subgroup ↥A) = p := by
      rw [show Nat.card ↥(⊤ : Subgroup ↥A) = Nat.card ↥A from
        Nat.card_congr Subgroup.topEquiv.toEquiv, hA]
    exact Subgroup.eq_of_le_of_card_ge le_top (by rw [hcard, htop])
  obtain ⟨a1, ha1, hZ1eq⟩ := point_eq_zpowers_mul hp hEel hEcard hA hAE hx0E hx0A hZ1 hZ1E hZ1A
  obtain ⟨a2, ha2, hZ2eq⟩ := point_eq_zpowers_mul hp hEel hEcard hA hAE hx0E hx0A hZ2 hZ2E hZ2A
  let a : ↥A := ⟨a1⁻¹ * a2, A.mul_mem (A.inv_mem ha1) ha2⟩
  have hmem : a ∈ φ.range := by rw [hrange]; exact Subgroup.mem_top a
  obtain ⟨r, hrφ⟩ := hmem
  refine ⟨r, r.2, ?_⟩
  rw [hZ1eq, hZ2eq, uniqueFourConj_zpowers]
  congr 1
  rw [MulAut.conj_apply, inv_inv]
  show (r : G)⁻¹ * (x0 * a1) * (r : G) = x0 * a2
  have hφval : (r : G)⁻¹ * x0 * (r : G) * x0⁻¹ = a1⁻¹ * a2 := congrArg Subtype.val hrφ
  have ha1c : (r : G)⁻¹ * a1 * (r : G) = a1 := conj_eq_of_mem_centralizer hcentA r.2 ha1
  calc (r : G)⁻¹ * (x0 * a1) * (r : G)
      = ((r : G)⁻¹ * x0 * (r : G)) * ((r : G)⁻¹ * a1 * (r : G)) := by group
    _ = ((r : G)⁻¹ * x0 * (r : G)) * a1 := by rw [ha1c]
    _ = ((a1⁻¹ * a2) * x0) * a1 := by
          rw [show (r : G)⁻¹ * x0 * (r : G) = (a1⁻¹ * a2) * x0 by rw [← hφval]; group]
    _ = x0 * a2 := by
          rw [hcommE (hAE (A.mul_mem (A.inv_mem ha1) ha2)) hx0E]
          have hsub : a1⁻¹ * a2 * a1 = a2 := by
            rw [show a1⁻¹ * a2 * a1 = a1⁻¹ * (a2 * a1) by group,
              hcommE (hAE ha2) (hAE ha1)]
            group
          rw [show (x0 * (a1⁻¹ * a2)) * a1 = x0 * (a1⁻¹ * a2 * a1) by group, hsub]

private theorem uniqueFourConj_mul' (a b : G) (Y : Subgroup G) :
    uniqueFourConj (a * b) Y = uniqueFourConj b (uniqueFourConj a Y) := by
  ext x
  rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff, mem_uniqueFourConj_iff]
  constructor
  · intro h
    have : a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
    rw [this]; exact h
  · intro h
    have : (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [this]; exact h

private theorem third_point_exists {p : ℕ} (hp : p.Prime) {E A B : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hAE : A ≤ E) (hB : Nat.card B = p) (hBE : B ≤ E)
    (hAB : A ≠ B) :
    ∃ C : Subgroup G, C ≤ E ∧ Nat.card C = p ∧ C ≠ A ∧ C ≠ B := by
  have hABot : A ⊓ B = ⊥ := inf_eq_bot_of_card_prime hp hA hB hAB
  haveI : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; exact hp.one_lt)
  haveI : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hB]; exact hp.one_lt)
  obtain ⟨a0, ha0ne⟩ := exists_ne (1 : ↥A)
  obtain ⟨b0, hb0ne⟩ := exists_ne (1 : ↥B)
  set u : G := (a0 : G) * (b0 : G) with hu
  have huE : u ∈ E := E.mul_mem (hAE a0.2) (hBE b0.2)
  have hu1 : u ≠ 1 := by
    intro h
    have hbA : (b0 : G) ∈ A := by
      have : (b0 : G) = (a0 : G)⁻¹ * u := by rw [hu]; group
      rw [this, h, mul_one]
      exact A.inv_mem a0.2
    have : (b0 : G) ∈ A ⊓ B := ⟨hbA, b0.2⟩
    rw [hABot] at this
    exact hb0ne (Subtype.ext (Subgroup.mem_bot.mp this))
  have hupow : u ^ p = 1 := hEel.2 u huE
  refine ⟨Subgroup.zpowers u, Subgroup.zpowers_le.mpr huE, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    have hdvd : orderOf u ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hupow
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h1
  · intro hC
    have huA : u ∈ A := by rw [← hC]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have hbA : (b0 : G) ∈ A := by
      have : (b0 : G) = (a0 : G)⁻¹ * u := by rw [hu]; group
      rw [this]
      exact A.mul_mem (A.inv_mem a0.2) huA
    have : (b0 : G) ∈ A ⊓ B := ⟨hbA, b0.2⟩
    rw [hABot] at this
    exact hb0ne (Subtype.ext (Subgroup.mem_bot.mp this))
  · intro hC
    have huB : u ∈ B := by rw [← hC]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have haB : (a0 : G) ∈ B := by
      have : (a0 : G) = u * (b0 : G)⁻¹ := by rw [hu]; group
      rw [this]
      exact B.mul_mem huB (B.inv_mem b0.2)
    have : (a0 : G) ∈ A ⊓ B := ⟨a0.2, haB⟩
    rw [hABot] at this
    exact ha0ne (Subtype.ext (Subgroup.mem_bot.mp this))

private theorem trans_of_H {p : ℕ} (hp : p.Prime) {E A B R Q : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hAE : A ≤ E) (hB : Nat.card B = p) (hBE : B ≤ E) (hAB : A ≠ B)
    (hRp : IsPGroup p R) (hQp : IsPGroup p Q) (hRA : ⁅R, E⁆ ≤ A) (hQB : ⁅Q, E⁆ ≤ B)
    (hRnt : ¬ R ≤ centralizer (E : Set G)) (hQnt : ¬ Q ≤ centralizer (E : Set G)) :
    ∀ Z1 Z2 : Subgroup G, Z1 ≤ E → Nat.card Z1 = p → Z2 ≤ E → Nat.card Z2 = p →
      ∃ h ∈ R ⊔ Q, uniqueFourConj h Z1 = Z2 := by
  intro Z1 Z2 hZ1E hZ1 hZ2E hZ2
  have hRt := trans_of_action hp hEel hEcard hA hAE hRp hRA hRnt
  have hQt := trans_of_action hp hEel hEcard hB hBE hQp hQB hQnt
  obtain ⟨C, hCE, hC, hCA, hCB⟩ := third_point_exists hp hEel hEcard hA hAE hB hBE hAB
  by_cases hZ1Z2 : Z1 = Z2
  · subst hZ1Z2
    exact ⟨1, one_mem _, uniqueFourConj_eq_self_iff.mpr (Subgroup.one_mem _)⟩
  by_cases hZ1A : Z1 = A
  · rw [hZ1A]
    by_cases hZ2B : Z2 = B
    · rw [hZ2B]
      obtain ⟨q, hqQ, hq⟩ := hQt A C hAE hA hCE hC hAB hCB
      obtain ⟨r, hrR, hr⟩ := hRt C B hCE hC hBE hB hCA hAB.symm
      exact ⟨q * r, (R ⊔ Q).mul_mem ((le_sup_right : Q ≤ R ⊔ Q) hqQ)
          ((le_sup_left : R ≤ R ⊔ Q) hrR), by rw [uniqueFourConj_mul', hq, hr]⟩
    · obtain ⟨q, hqQ, hq⟩ := hQt A Z2 hAE hA hZ2E hZ2 hAB hZ2B
      exact ⟨q, (le_sup_right : Q ≤ R ⊔ Q) hqQ, hq⟩
  · by_cases hZ2A : Z2 = A
    · rw [hZ2A]
      by_cases hZ1B : Z1 = B
      · rw [hZ1B]
        obtain ⟨r, hrR, hr⟩ := hRt B C hBE hB hCE hC hAB.symm hCA
        obtain ⟨q, hqQ, hq⟩ := hQt C A hCE hC hAE hA hCB hAB
        exact ⟨r * q, (R ⊔ Q).mul_mem ((le_sup_left : R ≤ R ⊔ Q) hrR)
          ((le_sup_right : Q ≤ R ⊔ Q) hqQ), by rw [uniqueFourConj_mul', hr, hq]⟩
      · obtain ⟨q, hqQ, hq⟩ := hQt Z1 A hZ1E hZ1 hAE hA hZ1B hAB
        exact ⟨q, (le_sup_right : Q ≤ R ⊔ Q) hqQ, hq⟩
    · obtain ⟨r, hrR, hr⟩ := hRt Z1 Z2 hZ1E hZ1 hZ2E hZ2 hZ1A hZ2A
      exact ⟨r, (le_sup_left : R ≤ R ⊔ Q) hrR, hr⟩

private theorem points_map {p : ℕ} (hp : p.Prime) {E A B R Q : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hAE : A ≤ E) (hB : Nat.card B = p) (hBE : B ≤ E) (hAB : A ≠ B)
    (hRp : IsPGroup p R) (hQp : IsPGroup p Q) (hRA : ⁅R, E⁆ ≤ A) (hQB : ⁅Q, E⁆ ≤ B)
    (hRE : R ≤ normalizer (E : Set G)) (hQE : Q ≤ normalizer (E : Set G))
    (hRnt : ¬ R ≤ centralizer (E : Set G)) (hQnt : ¬ Q ≤ centralizer (E : Set G)) :
    ∀ Z1 Z2 : Subgroup G, Z1 ≤ E → Nat.card Z1 = p → Z2 ≤ E → Nat.card Z2 = p →
      Z1 ≠ Z2 → ∃ h ∈ R ⊔ Q, uniqueFourConj h A = Z1 ∧ uniqueFourConj h B = Z2 := by
  intro Z1 Z2 hZ1E hZ1 hZ2E hZ2 hne
  have hRt := trans_of_action hp hEel hEcard hA hAE hRp hRA hRnt
  have hHt := trans_of_H hp hEel hEcard hA hAE hB hBE hAB hRp hQp hRA hQB hRnt hQnt
  have hRN : R ≤ normalizer (A : Set G) := le_normalizer_of_commutator_le hRA hAE
  have hHEN : R ⊔ Q ≤ normalizer (E : Set G) := sup_le hRE hQE
  obtain ⟨h1, hh1H, hA1⟩ := hHt A Z1 hAE hA hZ1E hZ1
  have hh1N : h1 ∈ normalizer (E : Set G) := hHEN hh1H
  let Z2' : Subgroup G := uniqueFourConj h1⁻¹ Z2
  have hZ2'E : Z2' ≤ E := by
    intro x hx
    rw [mem_uniqueFourConj_iff] at hx
    have hyE : h1⁻¹ * x * h1 ∈ E := hZ2E (by simpa [inv_inv] using hx)
    have hx' : h1 * (h1⁻¹ * x * h1) * h1⁻¹ ∈ E :=
      (Subgroup.le_normalizer_iff.mp hHEN) h1 hh1H _ hyE
    rwa [show h1 * (h1⁻¹ * x * h1) * h1⁻¹ = x by group] at hx'
  have hZ2'card : Nat.card Z2' = p := by
    rw [card_uniqueFourConj, hZ2]
  have hZ2'A : Z2' ≠ A := by
    intro h
    apply hne
    have : uniqueFourConj h1 Z2' = uniqueFourConj h1 A := by rw [h]
    rw [uniqueFourConj_conj_inv, hA1] at this
    exact this.symm
  obtain ⟨r, hrR, hr⟩ := hRt B Z2' hBE hB hZ2'E hZ2'card hAB.symm hZ2'A
  have hrA : uniqueFourConj r A = A := uniqueFourConj_eq_self_iff.mpr (hRN hrR)
  refine ⟨r * h1, (R ⊔ Q).mul_mem ((le_sup_left : R ≤ R ⊔ Q) hrR) hh1H, ?_, ?_⟩
  · rw [uniqueFourConj_mul', hrA, hA1]
  · rw [uniqueFourConj_mul', hr, uniqueFourConj_conj_inv]

private theorem conj_eq_of_point_eq {A V : Subgroup G}
    (hNA : normalizer (A : Set G) ≤ normalizer (V : Set G)) {h1 h2 : G}
    (h : uniqueFourConj h1 A = uniqueFourConj h2 A) :
    uniqueFourConj h1 V = uniqueFourConj h2 V := by
  have hm : h1 * h2⁻¹ ∈ normalizer (A : Set G) := by
    have := congrArg (uniqueFourConj h2⁻¹) h
    rw [← uniqueFourConj_mul', uniqueFourConj_inv_conj] at this
    exact uniqueFourConj_eq_self_iff.mp this
  have hV : uniqueFourConj (h1 * h2⁻¹) V = V := uniqueFourConj_eq_self_iff.mpr (hNA hm)
  have := congrArg (uniqueFourConj h2) hV
  rw [← uniqueFourConj_mul'] at this
  simpa using this

private theorem family_pairwise {p : ℕ} (hp : p.Prime) {E A B R Q V : Subgroup G}
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hAE : A ≤ E) (hB : Nat.card B = p) (hBE : B ≤ E) (hAB : A ≠ B)
    (hRp : IsPGroup p R) (hQp : IsPGroup p Q) (hRA : ⁅R, E⁆ ≤ A) (hQB : ⁅Q, E⁆ ≤ B)
    (hRE : R ≤ normalizer (E : Set G)) (hQE : Q ≤ normalizer (E : Set G))
    (hRnt : ¬ R ≤ centralizer (E : Set G)) (hQnt : ¬ Q ≤ centralizer (E : Set G))
    (hNA : normalizer (A : Set G) ≤ normalizer (V : Set G))
    {h0 : G} (hh0H : h0 ∈ R ⊔ Q) (hAh0 : uniqueFourConj h0 A = B)
    (hV_NW : V ≤ normalizer (uniqueFourConj h0 V)) :
    ∀ h1 ∈ R ⊔ Q, ∀ h2 ∈ R ⊔ Q,
      uniqueFourConj h1 V ≤ normalizer (uniqueFourConj h2 V) := by
  intro h1 hh1 h2 hh2
  by_cases hAA : uniqueFourConj h1 A = uniqueFourConj h2 A
  · rw [conj_eq_of_point_eq hNA hAA]
    exact le_normalizer
  · have hEN : R ⊔ Q ≤ normalizer (E : Set G) := sup_le hRE hQE
    have hZ1E : uniqueFourConj h1 A ≤ E :=
      (uniqueFourConj_mono hAE h1).trans (le_of_eq (uniqueFourConj_eq_self_iff.mpr (hEN hh1)))
    have hZ2E : uniqueFourConj h2 A ≤ E :=
      (uniqueFourConj_mono hAE h2).trans (le_of_eq (uniqueFourConj_eq_self_iff.mpr (hEN hh2)))
    have hpn := points_map hp hEel hEcard hA hAE hB hBE hAB hRp hQp hRA hQB hRE hQE hRnt hQnt
    obtain ⟨k, hkH, hAk, hBk⟩ :=
      hpn (uniqueFourConj h1 A) (uniqueFourConj h2 A) hZ1E
        ((card_uniqueFourConj A h1).trans hA) hZ2E ((card_uniqueFourConj A h2).trans hA) hAA
    have hS : uniqueFourConj h1 V = uniqueFourConj k V := conj_eq_of_point_eq hNA hAk.symm
    have hT : uniqueFourConj h2 V = uniqueFourConj (h0 * k) V := by
      apply conj_eq_of_point_eq hNA
      rw [← hBk, ← hAh0]
      exact (uniqueFourConj_mul' h0 k A).symm
    have hnorm : uniqueFourConj k V ≤ normalizer (uniqueFourConj k (uniqueFourConj h0 V)) := by
      have := uniqueFourConj_mono hV_NW k
      rwa [uniqueFourConj_normalizer] at this
    rw [hS, hT, uniqueFourConj_mul' h0 k V]
    exact hnorm

private theorem map_finset_sup (f : G →* G) (F : Finset (Subgroup G)) :
    (F.sup id).map f = F.sup (fun S => S.map f) := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | insert S F hS ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Subgroup.map_sup, ih]
      rfl

private theorem isPGroup_finset_sup {p : ℕ} (F : Finset (Subgroup G))
    (hF : ∀ S ∈ F, IsPGroup p S) (hN : ∀ S ∈ F, ∀ T ∈ F, S ≤ normalizer T) :
    IsPGroup p (F.sup id : Subgroup G) := by
  classical
  induction F using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      exact IsPGroup.of_bot
  | insert S F hS ih =>
      rw [Finset.sup_insert]
      have hSF : IsPGroup p S := hF S (Finset.mem_insert_self S F)
      have hF' : ∀ T ∈ F, IsPGroup p T := fun T hT => hF T (Finset.mem_insert_of_mem hT)
      have hN' : ∀ T ∈ F, ∀ U ∈ F, T ≤ normalizer U :=
        fun T hT U hU => hN T (Finset.mem_insert_of_mem hT) U (Finset.mem_insert_of_mem hU)
      have ih' : IsPGroup p (F.sup id : Subgroup G) := ih hF' hN'
      have hle : F.sup id ≤ normalizer S :=
        Finset.sup_le fun T hT => hN T (Finset.mem_insert_of_mem hT) S (Finset.mem_insert_self S F)
      have := IsPGroup.to_sup_of_normal_right' ih' hSF hle
      rwa [sup_comm] at this

theorem r6_10_part3 (D : Data G) {p : ℕ} (hp : p.Prime) {g : G}
    {E A B R Q : Subgroup G} (hEel : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hAE : A ≤ E) (hBE : B ≤ E) (hAB : A ≠ B)
    (hRp : IsPGroup p R) (hQp : IsPGroup p Q)
    (hRE : R ≤ normalizer (E : Set G)) (hQE : Q ≤ normalizer (E : Set G))
    (hRA : ⁅R, E⁆ ≤ A) (hQB : ⁅Q, E⁆ ≤ B)
    (hRnt : ¬ R ≤ centralizer (E : Set G)) (hQnt : ¬ Q ≤ centralizer (E : Set G))
    (hRloc : ∀ L : Subgroup G, IsTwoLocal L → R ≤ L → L ≤ D.M)
    (hQloc : ∀ L : Subgroup G, IsTwoLocal L → Q ≤ L → L ≤ uniqueFourConj g D.M)
    (hNA : normalizer (A : Set G) ≤ D.M) (hQM : Q ⊓ D.M ≤ centralizer (E : Set G))
    {V : Subgroup G} (hV : InCalV D.M V) (hVg : V ≤ uniqueFourConj g D.M) : False := by
  classical
  haveI : Fintype ↥(R ⊔ Q) := Fintype.ofFinite _
  have hVne : V ≠ ⊥ := hV.1
  have hVp : IsPGroup 2 V := hV.2.2.2.isPGroup
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hNV : normalizer (V : Set G) = D.M := by
    have hloc : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hVne, hVp, rfl⟩
    exact D.maxLocal.2 _ hloc hMV
  obtain ⟨h0, hh0H, hAh0, _hBh0⟩ :=
    points_map hp hEel hEcard hA hAE hB hBE hAB hRp hQp hRA hQB hRE hQE hRnt hQnt
      B A hBE hB hAE hA hAB.symm
  have hNA' : normalizer (A : Set G) ≤ normalizer (V : Set G) := by rw [hNV]; exact hNA
  let W : Subgroup G := uniqueFourConj h0 V
  have hNW : normalizer (W : Set G) = uniqueFourConj h0 D.M := by
    rw [show W = uniqueFourConj h0 V from rfl, ← uniqueFourConj_normalizer V h0, hNV]
  have hQNB : Q ≤ normalizer (B : Set G) := le_normalizer_of_commutator_le hQB hBE
  have hQN : Q ≤ normalizer (W : Set G) := by
    intro q hq
    rw [← uniqueFourConj_eq_self_iff]
    have hBq : uniqueFourConj q B = B := uniqueFourConj_eq_self_iff.mpr (hQNB hq)
    have hqA : uniqueFourConj (h0 * q) A = uniqueFourConj h0 A := by
      rw [uniqueFourConj_mul', hAh0, hBq]
    have hmem : h0 * q * h0⁻¹ ∈ normalizer (A : Set G) := by
      have := congrArg (uniqueFourConj h0⁻¹) hqA
      rw [← uniqueFourConj_mul', uniqueFourConj_inv_conj] at this
      exact uniqueFourConj_eq_self_iff.mp this
    have hVfix : uniqueFourConj (h0 * q * h0⁻¹) V = V :=
      uniqueFourConj_eq_self_iff.mpr (by rw [hNV]; exact hNA hmem)
    show uniqueFourConj q (uniqueFourConj h0 V) = uniqueFourConj h0 V
    rw [← uniqueFourConj_mul' h0 q V]
    rw [show h0 * q = (h0 * q * h0⁻¹) * h0 by group, uniqueFourConj_mul', hVfix]
  have hWne : W ≠ ⊥ := uniqueFourConj_ne_bot hVne h0
  have hWp : IsPGroup 2 W := isPGroup_uniqueFourConj hVp h0
  have hlocW : IsTwoLocal (normalizer (W : Set G)) := ⟨W, hWne, hWp, rfl⟩
  have hQlocW : normalizer (W : Set G) ≤ uniqueFourConj g D.M := hQloc _ hlocW hQN
  have hMeq : uniqueFourConj h0 D.M = uniqueFourConj g D.M :=
    ((isMaxTwoLocal_conj D.maxLocal h0).2 _ (isMaxTwoLocal_conj D.maxLocal g).1
      (by rwa [hNW] at hQlocW)).symm
  have hNWg : normalizer (W : Set G) = uniqueFourConj g D.M := by rw [hNW, hMeq]
  have hV_NW : V ≤ normalizer (W : Set G) := by rw [hNWg]; exact hVg
  let H : Subgroup G := R ⊔ Q
  let F : Finset (Subgroup G) := Finset.univ.image (fun h : ↥H => uniqueFourConj (h : G) V)
  have hFmem : ∀ S ∈ F, ∃ h : ↥H, uniqueFourConj (h : G) V = S := by
    intro S hS
    change S ∈ Finset.univ.image (fun h : ↥H => uniqueFourConj (h : G) V) at hS
    obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hS
    exact ⟨h, hh⟩
  have hF : ∀ S ∈ F, IsPGroup 2 S := by
    intro S hS
    obtain ⟨h, rfl⟩ := hFmem S hS
    exact isPGroup_uniqueFourConj hVp _
  have hN : ∀ S ∈ F, ∀ T ∈ F, S ≤ normalizer T := by
    intro S hS T hT
    obtain ⟨h1, rfl⟩ := hFmem S hS
    obtain ⟨h2, rfl⟩ := hFmem T hT
    exact family_pairwise hp hEel hEcard hA hAE hB hBE hAB hRp hQp hRA hQB hRE hQE
      hRnt hQnt hNA' hh0H hAh0 hV_NW h1 h1.2 h2 h2.2
  let U : Subgroup G := F.sup id
  have hUp : IsPGroup 2 U := isPGroup_finset_sup F hF hN
  have hVU : V ≤ U := by
    have hmem : V ∈ F := by
      change V ∈ Finset.univ.image (fun h : ↥H => uniqueFourConj (h : G) V)
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _,
        uniqueFourConj_eq_self_iff.mpr (Subgroup.one_mem _)⟩
    exact Finset.le_sup (f := id) hmem
  have hUne : U ≠ ⊥ := fun h => hVne (le_bot_iff.mp (hVU.trans (le_of_eq h)))
  have hUloc : IsTwoLocal (normalizer (U : Set G)) := ⟨U, hUne, hUp, rfl⟩
  have hFinv : ∀ r ∈ H, uniqueFourConj r U = U := by
    intro r hrH
    have hFimage : F.image (fun S => uniqueFourConj r S) = F := by
      apply Finset.ext
      intro S
      constructor
      · intro hS
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
        obtain ⟨h, rfl⟩ := hFmem T hT
        exact Finset.mem_image.mpr ⟨⟨(h : G) * r, H.mul_mem h.2 hrH⟩, Finset.mem_univ _,
          uniqueFourConj_mul' (h : G) r V⟩
      · intro hS
        obtain ⟨h, rfl⟩ := hFmem S hS
        refine Finset.mem_image.mpr ⟨uniqueFourConj r⁻¹ (uniqueFourConj (h : G) V), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨⟨(h : G) * r⁻¹, H.mul_mem h.2 (H.inv_mem hrH)⟩,
            Finset.mem_univ _, uniqueFourConj_mul' (h : G) r⁻¹ V⟩
        · exact uniqueFourConj_conj_inv
    change (F.sup id).map (MulAut.conj r⁻¹).toMonoidHom = F.sup id
    have hmap : (F.sup id).map (MulAut.conj r⁻¹).toMonoidHom =
        F.sup (fun S => uniqueFourConj r S) := by
      rw [map_finset_sup]
      rfl
    rw [hmap]
    rw [show F.sup (fun S => uniqueFourConj r S) =
        (F.image (fun S => uniqueFourConj r S)).sup id from
      (Finset.sup_image F (fun S => uniqueFourConj r S) id).symm]
    rw [hFimage]
  have hHN : H ≤ normalizer (U : Set G) := fun h hh =>
    uniqueFourConj_eq_self_iff.mp (hFinv h hh)
  have hRNU : R ≤ normalizer (U : Set G) := le_trans le_sup_left hHN
  have hQNU : Q ≤ normalizer (U : Set G) := le_trans le_sup_right hHN
  have hNUM : normalizer (U : Set G) ≤ D.M := hRloc _ hUloc hRNU
  have hQDM : Q ≤ D.M := hQNU.trans hNUM
  exact hQnt ((le_inf le_rfl hQDM).trans hQM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end