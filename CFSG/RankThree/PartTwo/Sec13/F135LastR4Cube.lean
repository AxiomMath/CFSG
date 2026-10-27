module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r4d_card_sup {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let f : H × K →* G := H.subtype.noncommCoprod K.subtype (fun x y => hc x x.2 y y.2)
  have hf : ∀ (x : H) (y : K), f (x, y) = (x : G) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    rw [hf] at h
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hxK : (x : G) ∈ H ⊓ K := ⟨x.2, by rw [hx]; exact K.inv_mem y.2⟩
    rw [hHK, Subgroup.mem_bot] at hxK
    have hy : (y : G) = 1 := by rw [hxK, one_mul] at h; exact h
    exact Prod.ext (Subtype.ext hxK) (Subtype.ext hy)
  have hrange : f.range = H ⊔ K := by
    apply le_antisymm
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hf]
      exact mul_mem ((le_sup_left : H ≤ H ⊔ K) x.2) ((le_sup_right : K ≤ H ⊔ K) y.2)
    · apply sup_le
      · intro x hx
        refine MonoidHom.mem_range.2 ⟨(⟨x, hx⟩, 1), ?_⟩
        rw [hf]
        simp
      · intro y hy
        refine MonoidHom.mem_range.2 ⟨(1, ⟨y, hy⟩), ?_⟩
        rw [hf]
        simp
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem r4d_exists_coatom_not_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hexp : ∀ x : G, x ^ p = 1) {Y : Subgroup G} (hY : Y ≠ ⊥)
    (hYc : Y ⊓ commutator G = ⊥) : ∃ H : Subgroup G, IsCoatom H ∧ ¬ Y ≤ H := by
  by_contra hcon
  push_neg at hcon
  have hle : Y ≤ frattini G := by
    unfold frattini Order.radical
    exact le_iInf₂ fun H hH => hcon H hH
  rw [frattini_eq_commutator hG hexp] at hle
  have h2 : Y ≤ Y ⊓ commutator G := le_inf le_rfl hle
  rw [hYc, le_bot_iff] at h2
  exact hY h2

theorem r4_exists_cube {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime] {X Y : Subgroup M}
    (hX : IsPGroup p X) (hexp : ∀ x ∈ X, x ^ p = 1) (hYX : Y ≤ X) (hY : Nat.card Y = p)
    (hYc : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y)
    (hYΦ : Y ⊓ (commutator ↥X).map X.subtype = ⊥) (h3 : p ^ 3 ≤ Nat.card X) :
    ∃ A : Subgroup M, A ≤ X ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
  have hp : p.Prime := Fact.out
  have hexpG : ∀ g : X, g ^ p = 1 := fun g => Subtype.ext (by simp [hexp g.1 g.2])
  have hZcard : Nat.card (Y.subgroupOf X) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv]
    exact hY
  have hZne : Y.subgroupOf X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    have := hp.one_lt
    omega
  have hZcen : ∀ z ∈ Y.subgroupOf X, ∀ g : X, z * g = g * z := by
    intro z hz g
    exact Subtype.ext (hYc (z : M) hz (g : M) g.2)
  have hZc : Y.subgroupOf X ⊓ commutator ↥X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgZ, hgC⟩ := Subgroup.mem_inf.1 hg
    have h2 : (g : M) ∈ (commutator ↥X).map X.subtype :=
      Subgroup.mem_map_of_mem X.subtype hgC
    have h3' : (g : M) ∈ Y ⊓ (commutator ↥X).map X.subtype :=
      Subgroup.mem_inf.2 ⟨hgZ, h2⟩
    rw [hYΦ, Subgroup.mem_bot] at h3'
    exact Subtype.ext h3'
  obtain ⟨H, hHc, hHZ⟩ := r4d_exists_coatom_not_le hX hexpG hZne hZc
  have hsup : H ⊔ Y.subgroupOf X = ⊤ := by
    obtain ⟨-, hmax⟩ := hHc
    apply hmax
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hHZ
    rw [heq]
    exact le_sup_right
  have hHZinf : H ⊓ Y.subgroupOf X = ⊥ := by
    have hdvd : Nat.card ↥(H ⊓ Y.subgroupOf X) ∣ p := by
      have h7 := Subgroup.card_dvd_of_le (inf_le_right : H ⊓ Y.subgroupOf X ≤ Y.subgroupOf X)
      rwa [hZcard] at h7
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | h1
    · rw [Subgroup.card_eq_one] at h1
      exact h1
    · exfalso
      have heq : H ⊓ Y.subgroupOf X = Y.subgroupOf X :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      exact hHZ (heq.symm.le.trans inf_le_left)
  have hcardG : Nat.card X = Nat.card H * p := by
    have h5 := r4d_card_sup (H := H) (K := Y.subgroupOf X)
      (fun x _ y hy => (hZcen y hy x).symm) hHZinf
    rw [hsup, Subgroup.card_top, hZcard] at h5
    exact h5
  have hH2 : p ^ 2 ≤ Nat.card H := by
    have h4 : p ^ 2 * p ≤ Nat.card H * p := by
      have h6 : p ^ 2 * p = p ^ 3 := by ring
      rw [h6, ← hcardG]
      exact h3
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  obtain ⟨K, hKH, hKcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n := 2) hp hX hH2
  have hKcomm : IsMulCommutative ↥K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hKcard
  have hKel : CFSG.Open.IsElemAbelian p K := ⟨hKcomm, fun x _ => hexpG x⟩
  have hZel : CFSG.Open.IsElemAbelian p (Y.subgroupOf X) :=
    ⟨⟨⟨fun a b => Subtype.ext (hZcen a.1 a.2 b.1)⟩⟩, fun x _ => hexpG x⟩
  have hZcomm : ∀ x ∈ Y.subgroupOf X, ∀ y ∈ K, x * y = y * x :=
    fun x hx y _ => hZcen x hx y
  have hZK : Y.subgroupOf X ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgZ, hgK⟩ := Subgroup.mem_inf.1 hg
    have hgH : g ∈ H ⊓ Y.subgroupOf X := Subgroup.mem_inf.2 ⟨hKH hgK, hgZ⟩
    rw [hHZinf, Subgroup.mem_bot] at hgH
    exact hgH
  have hAel : CFSG.Open.IsElemAbelian p (Y.subgroupOf X ⊔ K) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hZel hKel hZcomm
  have hcardA : Nat.card (Y.subgroupOf X ⊔ K : Subgroup ↥X) = p ^ 3 := by
    have h7 := r4d_card_sup hZcomm hZK
    rw [hZcard, hKcard] at h7
    rw [h7, show p * p ^ 2 = p ^ 3 by ring]
  refine ⟨(Y.subgroupOf X ⊔ K).map X.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hcomm : ∀ a ∈ (Y.subgroupOf X ⊔ K).map X.subtype,
        ∀ b ∈ (Y.subgroupOf X ⊔ K).map X.subtype, a * b = b * a := by
      intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hb
      rw [← map_mul, ← map_mul, hAel.comm hg hg']
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hAel.2 g hg, map_one]
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hcardA

end CFSG.RankThree.PartTwo.Sec13.F135Last
