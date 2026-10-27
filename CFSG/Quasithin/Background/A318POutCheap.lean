module

public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace A318P

theorem finite_outer (T : Type) [Group T] [Finite T] : Finite (Outer T) := by
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  infer_instance

theorem not_dvd_of_le_two {n p : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ n := by
  intro h
  have := Nat.le_of_dvd hn h
  have := hp.two_le
  omega

theorem not_dvd_outer_of_card_le_two {T : Type} [Group T] [Finite T]
    (h : Nat.card (Outer T) ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer T) := by
  have := finite_outer T
  exact not_dvd_of_le_two Nat.card_pos h hp hp2

theorem not_dvd_card_of_isPGroup_two {G : Type*} [Group G] [Finite G] (h : IsPGroup 2 G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card G := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
  rw [hk] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem isPGroup_two_outer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsPGroup 2 (Outer H)) : IsPGroup 2 (Outer G) :=
  h.of_equiv (equivalence e).symm

theorem card_outer_le_two_of_card_mulAut_le {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) (h : Nat.card (MulAut T) ≤ 2 * Nat.card T) :
    Nat.card (Outer T) ≤ 2 := by
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have : g ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut T => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = (g * y * g⁻¹) * g := by rw [this]
        _ = g * y := by group
    rw [hZ] at this
    exact this
  have hinner : Nat.card (inner T) = Nat.card T :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h1 := (inner T).card_eq_card_quotient_mul_card_subgroup
  rw [hinner] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  have h2 : Nat.card (Outer T) * Nat.card T ≤ 2 * Nat.card T := by
    rw [← h1]
    exact h
  exact Nat.le_of_mul_le_mul_right h2 hpos


theorem not_dvd_outer_of_carrier {s : TauCeti.SporadicName} {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier s) (h : Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  have := Finite.of_equiv S e.toEquiv
  have hc : Nat.card (Outer S) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [hc]
  exact not_dvd_outer_of_card_le_two h hp hp2

theorem not_dvd_outer_alternating {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer S) := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h.trans
    (CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six
      hn e)))

theorem outer_card_dvd_of_psl_two {S : Type} [Group S] {p f : ℕ}
    (hm : StatedClassicalModel S .PSL 2 p f) :
    Nat.card (Outer S) ∣ f * Nat.gcd 2 (p ^ f - 1) := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  exact (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp K hK).2 S
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩

theorem not_dvd_outer_psl_two_odd {S : Type} [Group S] {r f : ℕ} (hf : f = 1 ∨ f = 2)
    (hm : StatedClassicalModel S .PSL 2 r f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer S) := by
  intro h
  have h1 := h.trans (outer_card_dvd_of_psl_two hm)
  have h2 : f * Nat.gcd 2 (r ^ f - 1) ∣ 4 := by
    have : f * Nat.gcd 2 (r ^ f - 1) ∣ f * 2 := Nat.mul_dvd_mul_left f (Nat.gcd_dvd_left 2 _)
    refine this.trans ?_
    rcases hf with rfl | rfl <;> decide
  have h3 := h1.trans h2
  have h4 : p ∣ 2 ^ 2 := by simpa using h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))

theorem pRank_le_one_psl_two_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSL 2 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  let e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Finite.of_equiv S e'.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic hp
    (fun R => CFSG.Timmesfeld.RankOne.isCyclic_sylow_psl2 hf p hp2 R)

theorem pRank_le_one_suzuki' {S : Type} [Group S] [Finite S] {f : ℕ} (hm : SuzukiModel S 2 f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 :=
  CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hm hp hp2

theorem not_dvd_outer_tits
    {S : Type} [Group S] [Finite S] (hm : ReeTitsModel S .Tits 2 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  have := finite_outer S
  exact not_dvd_card_of_isPGroup_two
    (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 hm).1 hp hp2

end A318P

end CFSG.Quasithin
