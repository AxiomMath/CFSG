module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.CharacterTheory.Burnside
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem isSolvable_of_prime_dvd {X : Type*} [Group X] [Finite X] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = p ∨ r = q) :
    Group.IsSolvable X := by
  have hpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ r ∈ (Nat.card X).factorization.support, r = p ∨ r = q := fun r hr => by
    rw [Nat.support_factorization] at hr
    exact h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  by_cases hpq : p = q
  · subst hpq
    have : Fact p.Prime := ⟨hp⟩
    have hsupp : (Nat.card X).factorization.support ⊆ {p} := fun r hr => by
      rcases hmem r hr with h | h <;> simp [h]
    have hP : IsPGroup p X := by
      refine IsPGroup.of_card (n := (Nat.card X).factorization p) ?_
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
      rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
        Finset.prod_singleton]
    have : Group.IsNilpotent X := hP.isNilpotent
    infer_instance
  · have := Fintype.ofFinite X
    have hsupp : (Nat.card X).factorization.support ⊆ {p, q} := fun r hr => by
      rcases hmem r hr with h | h <;> simp [h]
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
      (a := (Nat.card X).factorization p) (b := (Nat.card X).factorization q) ?_
    rw [← Nat.card_eq_fintype_card]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
    rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _), Finset.prod_pair hpq]

theorem isSolvable_of_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y) [Group.IsSolvable Y]
    (hk : Group.IsSolvable f.ker) : Group.IsSolvable X :=
  Group.isSolvable_of_ker_le_range f.ker.subtype f (Subgroup.range_subtype _).ge

theorem isSolvable_of_isBorelIn {Γ : Type} [Group Γ] [Finite Γ] {X B : Subgroup Γ}
    (h : IsBorelIn X B) : Group.IsSolvable B := by
  obtain ⟨S, ⟨hSX, hS2, hSi⟩, rfl⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSB : S ≤ X ⊓ Subgroup.normalizer (S : Set Γ) := le_inf hSX Subgroup.le_normalizer
  set N := S.subgroupOf (X ⊓ Subgroup.normalizer (S : Set Γ)) with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr inf_le_right
  have hNsolv : Group.IsSolvable N := by
    have hNp : IsPGroup 2 N := hS2.comap_subtype
    have : Group.IsNilpotent N := hNp.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (↥(X ⊓ Subgroup.normalizer (S : Set Γ)) ⧸ N)) := by
    have hmul := Subgroup.relIndex_mul_relIndex S (X ⊓ Subgroup.normalizer (S : Set Γ)) X hSB
      inf_le_left
    have hdvd : S.relIndex (X ⊓ Subgroup.normalizer (S : Set Γ)) ∣ S.relIndex X :=
      ⟨_, hmul.symm⟩
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h2 => hSi (h2.trans hdvd)
  have hQ : Group.IsSolvable (↥(X ⊓ Subgroup.normalizer (S : Set Γ)) ⧸ N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact isSolvable_of_ker (QuotientGroup.mk' N) (by rw [QuotientGroup.ker_mk']; exact hNsolv)

theorem two_le_pRank_of_surjective {G : Type} [Group G] [Finite G] {K : Subgroup G} {Q : Type}
    [Group Q] [Finite Q] (f : ↥K →* Q) (hf : Function.Surjective f) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Q)) :
    2 ≤ CFSG.Open.pRank p K := by
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup Q)
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨P', hEP'⟩ := hEp.exists_le_sylow
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p P'
  have hnc : ¬ IsCyclic ↥(P : Subgroup ↥K) := by
    intro hcyc
    have hcyc' : IsCyclic ↥((P : Subgroup ↥K).map f) :=
      isCyclic_of_surjective (f.subgroupMap (P : Subgroup ↥K)) (f.subgroupMap_surjective _)
    have hcyc'' : IsCyclic ↥(Sylow.mapSurjective hf P : Subgroup Q) := hcyc'
    have hcycE : IsCyclic ↥E := Subgroup.isCyclic_of_le hEP'
    obtain ⟨g, hg⟩ := hcycE.exists_generator
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
    have h1 := orderOf_dvd_of_pow_eq_one hgp
    rw [hord, hEcard] at h1
    have h2 : p ^ 2 ∣ p := (pow_dvd_pow p h).trans h1
    have h3 : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos h2
    have h4 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega
  have h2 := CFSG.Quasithin.A3Facts.two_le_pRank_of_not_isCyclic hp2 P.isPGroup' hnc
  rwa [pRank_top_subtype] at h2

end CFSG.Quasithin.H13.Ch4.T425C27
