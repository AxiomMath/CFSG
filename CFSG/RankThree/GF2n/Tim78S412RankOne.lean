module

public import CFSG.RankThree.GF2n.Tim78RankOne218
import CFSG.Timmesfeld.RankOne.Lift

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_rankOne_pair {P₁ P₂ L H E : Subgroup G}
    (hH : H = P₁ ⊔ P₂)
    (hL₁ : P₁ ≤ Subgroup.normalizer (L : Set G)) (hL₂ : P₂ ≤ Subgroup.normalizer (L : Set G))
    (hcomm₁ : ∀ p ∈ P₁, ∀ p' ∈ P₁, ⁅p, p'⁆ ∈ Subgroup.centralizer (L : Set G))
    (hcomm₂ : ∀ u ∈ P₂, ∀ u' ∈ P₂, ⁅u, u'⁆ ∈ Subgroup.centralizer (L : Set G))
    (hsq₁ : ∀ p ∈ P₁, p * p ∈ Subgroup.centralizer (L : Set G))
    (hsq₂ : ∀ u ∈ P₂, u * u ∈ Subgroup.centralizer (L : Set G))
    (hMouf : ∀ p ∈ P₁, p ∉ Subgroup.centralizer (L : Set G) →
      ∃ u ∈ P₂, u ∉ Subgroup.centralizer (L : Set G) ∧ conjSubgroup u P₁ = conjSubgroup p P₂)
    (hMouf' : ∀ u ∈ P₂, u ∉ Subgroup.centralizer (L : Set G) →
      ∃ p ∈ P₁, p ∉ Subgroup.centralizer (L : Set G) ∧ conjSubgroup p P₂ = conjSubgroup u P₁)
    (hne : ∀ p ∈ P₁, ∀ u ∈ P₂, p ∉ Subgroup.centralizer (L : Set G) →
      p⁻¹ * u ∉ Subgroup.centralizer (L : Set G))
    (hEP : E ≤ P₁) (hE1 : ∀ e ∈ E, e ∈ Subgroup.centralizer (L : Set G) → e = 1)
    (hEfac : ∀ p ∈ P₁, ∃ e ∈ E, ∃ c ∈ Subgroup.centralizer (L : Set G), c ∈ P₁ ∧ p = e * c)
    (hE4 : 4 ≤ Nat.card E) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card E = 2 ^ n ∧
      ∃ φ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n), Function.Surjective φ ∧
        (∀ z : H, φ z = 1 ↔ (z : G) ∈ Subgroup.centralizer (L : Set G)) ∧
        (P₁.subgroupOf H).map φ = upperUnipotent (GaloisField 2 n) ∧
        (P₂.subgroupOf H).map φ = lowerUnipotent (GaloisField 2 n) := by
  classical
  set Cen := Subgroup.centralizer (L : Set G) with hCen
  have hP₁H : P₁ ≤ H := hH ▸ le_sup_left
  have hP₂H : P₂ ≤ H := hH ▸ le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := hH ▸ sup_le hL₁ hL₂
  have hHNC : H ≤ Subgroup.normalizer (Cen : Set G) := fun z hz =>
    mem_normalizer_centralizer (hHN hz)
  have hnorm : (Cen.subgroupOf H).Normal := by
    refine ⟨fun k hk z => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hHNC z.2) (k : G)).mp hk
  set π := QuotientGroup.mk' (Cen.subgroupOf H) with hπdef
  have hπ1 : ∀ z : H, π z = 1 ↔ (z : G) ∈ Cen := fun z => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ z z' : H, π z = π z' ↔ ((z : G)⁻¹ * z') ∈ Cen := fun z z' => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    rfl
  set A := (P₁.subgroupOf H).map π with hA
  set B := (P₂.subgroupOf H).map π with hB
  have hmemA : ∀ a ∈ A, ∃ p : H, (p : G) ∈ P₁ ∧ π p = a := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨p, Subgroup.mem_subgroupOf.mp hp, rfl⟩
  have hmemB : ∀ b ∈ B, ∃ u : H, (u : G) ∈ P₂ ∧ π u = b := fun b hb => by
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  have hπA : ∀ p : H, (p : G) ∈ P₁ → π p ∈ A := fun p hp =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  have hπB : ∀ u : H, (u : G) ∈ P₂ → π u ∈ B := fun u hu =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
  have hAcard : Nat.card A = Nat.card E := by
    let f : E → A := fun e => ⟨π ⟨e, hP₁H (hEP e.2)⟩, hπA _ (hEP e.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro e e' hee'
        have h1 : π ⟨e, hP₁H (hEP e.2)⟩ = π ⟨e', hP₁H (hEP e'.2)⟩ := congrArg Subtype.val hee'
        have h2 := (hπeq _ _).mp h1
        have hmem : (e : G)⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem e.2) e'.2
        have h3 := hE1 _ hmem h2
        exact Subtype.ext (inv_mul_eq_one.mp h3)
      · rintro ⟨a, ha⟩
        obtain ⟨p, hp, rfl⟩ := hmemA a ha
        obtain ⟨e, he, c, hcC, hcP, hpec⟩ := hEfac p hp
        refine ⟨⟨e, he⟩, Subtype.ext ((hπeq _ _).mpr ?_)⟩
        have : (e : G)⁻¹ * (p : G) = c := by rw [hpec]; group
        simpa [this] using hcC
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hA4 : 4 ≤ Nat.card A := hAcard ▸ hE4
  have hrank : IsElemAbRankOne A B := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA, hB, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hP₁H hP₂H, ← hH,
        Subgroup.subgroupOf_self]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    · intro hAB
      obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
        haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨a, ha1⟩ := exists_ne (1 : A)
        exact ⟨a, a.2, fun h => ha1 (Subtype.ext h)⟩
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      have hpC : (p : G) ∉ Cen := fun h => ha1 ((hπ1 p).mpr h)
      have hmem : π p ∈ B := hAB ▸ hπA _ hp
      obtain ⟨u, hu, hup⟩ := hmemB _ hmem
      exact hne _ hp _ hu hpC ((hπeq _ _).mp hup.symm)
    · intro a ha a' ha'
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      obtain ⟨p', hp', rfl⟩ := hmemA a' ha'
      show π p * π p' = π p' * π p
      rw [← map_mul, ← map_mul, hπeq]
      have : ((p * p' : H) : G)⁻¹ * ((p' * p : H) : G) = ⁅(p' : G)⁻¹, (p : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, commutatorElement_def]; group
      rw [this]
      exact hcomm₁ _ (P₁.inv_mem hp') _ (P₁.inv_mem hp)
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      rw [← map_mul, hπ1]
      exact hsq₁ _ hp
    · intro a ha ha1
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      have hpC : (p : G) ∉ Cen := fun h => ha1 ((hπ1 p).mpr h)
      obtain ⟨u, hu, huC, hueq⟩ := hMouf p hp hpC
      refine ⟨π ⟨u, hP₂H hu⟩, hπB _ hu, fun h1 => huC ((hπ1 _).mp h1), ?_⟩
      rw [hA, hB, map_conj_map_mk P₁ ⟨u, hP₂H hu⟩, map_conj_map_mk P₂ p, hueq]
    · intro b hb hb1
      obtain ⟨u, hu, rfl⟩ := hmemB b hb
      have huC : (u : G) ∉ Cen := fun h => hb1 ((hπ1 u).mpr h)
      obtain ⟨p, hp, hpC, hpeq⟩ := hMouf' u hu huC
      refine ⟨π ⟨p, hP₁H hp⟩, hπA _ hp, fun h1 => hpC ((hπ1 _).mp h1), ?_⟩
      rw [hA, hB, map_conj_map_mk P₂ ⟨p, hP₁H hp⟩, map_conj_map_mk P₁ u, hpeq]
  obtain ⟨n, hn2, hAn, φ₀, hφA, hφB⟩ := rankOne_mulEquiv_SL2 hrank hA4
  refine ⟨n, hn2, hAcard ▸ hAn, φ₀.toMonoidHom.comp π,
    φ₀.surjective.comp (QuotientGroup.mk'_surjective _), fun z => ?_, ?_, ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ φ₀.injective, hπ1]
  · rw [← Subgroup.map_map, ← hA]
    exact hφA
  · rw [← Subgroup.map_map, ← hB]
    exact hφB

end CFSG.RankThree.GF2n.Tim78
