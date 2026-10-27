module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Edge
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem lamSet_not_trans {a b c : V} (hab : Γ.Adj a b) {L : Subgroup G}
    (hL : L ∈ LamSet Γ G a b c) :
    ¬ ∀ u w, Γ.Adj b u → Γ.Adj b w → ∃ g ∈ L ⊓ MulAction.stabilizer G b, g • u = w := by
  intro htr
  obtain ⟨Q, hQ0, hQ, hLQ, hloc, -⟩ := hL
  refine hQ0 (F.eq_bot_of_locTrans L hab (U := Q)
    (fun u hu => ⟨MulAction.mem_stabilizer_iff.1 (hQ hu).1,
      MulAction.mem_stabilizer_iff.1 (hQ hu).2⟩) hLQ.le (fun u w hu hw => ?_)
    (fun u w hu hw => ?_))
  · obtain ⟨g, hg, hgu⟩ := hloc u w hu hw
    exact ⟨g, hg.1, MulAction.mem_stabilizer_iff.1 hg.2, hgu⟩
  · obtain ⟨g, hg, hgu⟩ := htr u w hu hw
    exact ⟨g, hg.1, MulAction.mem_stabilizer_iff.1 hg.2, hgu⟩

end FanTree

theorem fan41_nt (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) {L : Subgroup G}
    (hL : L ∈ LamSet Γ G a b c) :
    ¬ ∀ u w, Γ.Adj b u → Γ.Adj b w → ∃ g ∈ L ⊓ MulAction.stabilizer G b, g • u = w :=
  F.lamSet_not_trans hab hL

theorem fan41_1 (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c) {L : Subgroup G}
    (hL : L ∈ LamSet Γ G a b c) :
    L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b = L ⊓ nbrStab Γ G b := by
  have hL' := hL
  obtain ⟨Q, hQ0, hQ, hLQ, hloc, ⟨g₀, hg₀, hg₀a⟩⟩ := hL
  rcases F.fixes_or_trans b (inf_le_right : L ⊓ MulAction.stabilizer G b ≤ _) with
    ⟨w, hw, hfix⟩ | htr
  swap
  · exact absurd htr (F.lamSet_not_trans hab hL')
  have hwa : a ≠ w := by
    rintro rfl
    exact hac (hg₀a.symm.trans (hfix g₀ hg₀)).symm
  ext g
  constructor
  · rintro ⟨⟨hgL, hga⟩, hgb⟩
    refine ⟨hgL, fun z hz => ?_⟩
    exact F.frobenius_two b a w hab.symm hw hwa g hgb (MulAction.mem_stabilizer_iff.1 hga)
      (hfix g ⟨hgL, hgb⟩) z hz
  · rintro ⟨hgL, hgK⟩
    exact ⟨⟨hgL, MulAction.mem_stabilizer_iff.2 (hgK a hab.symm)⟩, F.nbrStab_le_stabilizer b hgK⟩

theorem fan41_max (F : FanTree Γ G) {a b c : V} {L : Subgroup G} (hL : L ∈ LamSet Γ G a b c) :
    ∃ L' : Subgroup G, LamMax Γ G a b c L' ∧
      L ⊓ MulAction.stabilizer G a ≤ L' ⊓ MulAction.stabilizer G a := by
  classical
  have hfin := F.loc_finite a
  let P : ℕ → Prop := fun n => ∃ L' ∈ LamSet Γ G a b c,
    L ⊓ MulAction.stabilizer G a ≤ L' ⊓ MulAction.stabilizer G a ∧
      Nat.card ↥(L' ⊓ MulAction.stabilizer G a) = n
  have hbdd : BddAbove {n | P n} := by
    refine ⟨Nat.card ↥(MulAction.stabilizer G a), ?_⟩
    rintro n ⟨L', -, -, rfl⟩
    exact Subgroup.card_le_of_le inf_le_right
  have hne : {n | P n}.Nonempty := ⟨_, L, hL, le_rfl, rfl⟩
  obtain ⟨L', hL', hle, hn⟩ := Nat.sSup_mem hne hbdd
  refine ⟨L', ⟨hL', fun L'' hL'' h => ?_⟩, hle⟩
  have hP'' : P (Nat.card ↥(L'' ⊓ MulAction.stabilizer G a)) := ⟨L'', hL'', hle.trans h, rfl⟩
  have hcard := le_csSup hbdd hP''
  rw [← hn] at hcard
  have : Finite ↥(L'' ⊓ MulAction.stabilizer G a) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right :
      L'' ⊓ MulAction.stabilizer G a ≤ _)) (Subgroup.inclusion_injective _)
  exact (Subgroup.eq_of_le_of_card_ge h hcard).ge

theorem fan41_noChar (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c)
    {L : Subgroup G} (hL : LamMax Γ G a b c L) (K : Subgroup G)
    (hK : K ≤ L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) (hK0 : K ≠ ⊥)
    (hchar : (K.subgroupOf
      (L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)).Characteristic) :
    ¬ (K.subgroupOf (L ⊓ MulAction.stabilizer G a)).Normal := by
  intro hN
  have hKL : K ≤ L ⊓ MulAction.stabilizer G a := hK.trans inf_le_left
  have hLa : L ⊓ MulAction.stabilizer G a ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    mem_normalizer_of_normal_subgroupOf hKL hN hg
  have hnormR : ∀ n ∈ Subgroup.normalizer
      ((L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) : Set G),
      n ∈ Subgroup.normalizer (K : Set G) := fun n hn =>
    mem_normalizer_of_characteristic hK hchar hn
  have hR : L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b = L ⊓ nbrStab Γ G b :=
    fan41_1 F hab hac hL.1
  have hnormLK : ∀ g ∈ L ⊓ MulAction.stabilizer G b,
      g ∈ Subgroup.normalizer ((L ⊓ nbrStab Γ G b : Subgroup G) : Set G) := by
    have key : ∀ g ∈ L ⊓ MulAction.stabilizer G b, ∀ h ∈ L ⊓ nbrStab Γ G b,
        g * h * g⁻¹ ∈ L ⊓ nbrStab Γ G b := fun g hg h hh =>
      ⟨L.mul_mem (L.mul_mem hg.1 hh.1) (L.inv_mem hg.1),
        nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hg.2) hh.2⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have := key g⁻¹ ((L ⊓ MulAction.stabilizer G b).inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hnormK : ∀ g ∈ L ⊓ MulAction.stabilizer G b, g ∈ Subgroup.normalizer (K : Set G) :=
    fun g hg => hnormR g (by rw [hR]; exact hnormLK g hg)
  have hNlam : Subgroup.normalizer (K : Set G) ∈ LamSet Γ G a b c := by
    obtain ⟨Q, hQ0, hQ, hLQ, hloc, ⟨g₀, hg₀, hg₀a⟩⟩ := hL.1
    refine ⟨K, hK0, fun g hg => ⟨(hK hg).1.2, (hK hg).2⟩, rfl, ?_,
      ⟨g₀, ⟨hnormK g₀ hg₀, hg₀.2⟩, hg₀a⟩⟩
    intro u v hu hv
    obtain ⟨g, hg, hgu⟩ := hloc u v hu hv
    exact ⟨g, ⟨hLa hg, hg.2⟩, hgu⟩
  have hBfin : Finite ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) :=
    F.finite_stabilizer_inf a b
  have hB2 : IsPGroup 2 ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) :=
    F.edge_two a b hab
  have hRB : L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ≤
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := fun g hg => ⟨hg.1.2, hg.2⟩
  obtain ⟨g₁, hg₁b, hg₁a, c', hc', hg₁c'⟩ := F.frobenius_nonreg b a hab.symm
  have hex : ∃ x ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b,
      x ∉ L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
    refine ⟨g₁, ⟨MulAction.mem_stabilizer_iff.2 hg₁a, hg₁b⟩, fun hx => ?_⟩
    rw [hR] at hx
    exact hg₁c' (hx.2 c' hc')
  obtain ⟨n, hnB, hnR, hnnorm⟩ := exists_mem_normalizer_not_mem hB2 hRB hex
  have hnK := hnormR n hnnorm
  have hmax := hL.2 _ hNlam (fun g hg => ⟨hLa hg, hg.2⟩)
  have : n ∈ L ⊓ MulAction.stabilizer G a := hmax ⟨hnK, hnB.1⟩
  exact hnR ⟨this, hnB.2⟩

end CFSG.Quasithin.Fan86
