module

public import CFSG.Quasithin.Vol2.Ch11SecGFacts2
public import CFSG.Quasithin.Vol2.Ch11SecGTBar
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Case1Struct (X : Type) [Group X] : Prop :=
  Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) ≤ CFSG.fittingSubgroup X ∧
    (∀ r : ℕ, r.Prime → r ∣ Nat.card (CFSG.fittingSubgroup X) → 5 ≤ r) ∧
    ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ ∃ ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q),
      Function.Surjective ψ ∧ ψ.ker = CFSG.fittingSubgroup X

theorem five_le_of_mod_five {p : ℕ} (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4 ∨ p = 5) :
    5 ≤ p := by
  by_contra hlt
  push Not at hlt
  have h2 := hp.two_le
  interval_cases p
  all_goals first | omega | exact absurd hp (by norm_num)

theorem case1Struct_of_a36Case4 {X : Type} [Group X] [Finite X] (h : A36Case4 X) :
    Case1Struct X := by
  obtain ⟨hFF, -, ⟨e⟩, hpr⟩ := h
  refine ⟨?_, fun r hr hrF => five_le_of_mod_five hr (hpr r hr hrF).1, 5, Nat.prime_five, le_rfl,
    e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · have := CFSG.centralizer_generalizedFitting_le X
    rwa [hFF] at this
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    simp

theorem case1Struct_of_natural {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : p % 5 = 1 ∨ p % 5 = 4)
    (hFF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X)
    (hE : IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X))
    (hN : NaturalSL2Action p X (CFSG.fittingSubgroup X)) : Case1Struct X := by
  have hp5' : 5 ≤ p := five_le_of_mod_five hp (by tauto)
  obtain ⟨-, ψ, hψ, hker, -⟩ := hN
  obtain ⟨eF⟩ := hE
  have hcard : Nat.card (CFSG.fittingSubgroup X) = p ^ 2 := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
  refine ⟨?_, fun r hr hrF => ?_, p, hp, hp5', ψ, hψ, hker⟩
  · have := CFSG.centralizer_generalizedFitting_le X
    rwa [hFF] at this
  · rw [hcard] at hrF
    have := (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrF)
    omega

theorem exists_oddCore_of_case11_1_2One {G : Type} [Group G] {K : Subgroup G}
    (h : Case11_1_2One K) :
    ∃ p : ℕ, p.Prime ∧ (p = 5 ∨ 11 ≤ p) ∧
      ∃ φ : Bar.KBar K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
        Function.Surjective φ ∧ φ.ker = CFSG.oddCore (Bar.KBar K) := by
  obtain ⟨p, hp, hp', φ, hφ, hker⟩ := h
  have hle : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  refine ⟨p, hp, hp', QuotientGroup.lift _ φ hle, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨x, QuotientGroup.lift_mk _ hle x⟩
  · ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem case1Struct_of_fact (hF : FactCase1Shape) {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hlist : List11_1_1Two (Bar.KBar K) 2 ∨ List11_1_1Three (Bar.KBar K))
    (h1 : Case11_1_2One K) : Case1Struct (Bar.KBar K) := by
  rcases hF (Bar.KBar K) hlist (exists_oddCore_of_case11_1_2One h1) with
    h | ⟨p, hp, hp5, -, hFF, hE, hN⟩
  · exact case1Struct_of_a36Case4 h
  · exact case1Struct_of_natural hp hp5 hFF hE hN

end CFSG.Quasithin.Vol2.Ch11.SecG
