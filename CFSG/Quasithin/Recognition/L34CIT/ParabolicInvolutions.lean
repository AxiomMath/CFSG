module

public import CFSG.Quasithin.Recognition.L34CIT.OppositeCount

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

theorem nonidentityInvolutions_inf (P Q : Subgroup A) :
    nonidentityInvolutions (P ⊓ Q) = nonidentityInvolutions P ∩ nonidentityInvolutions Q := by
  ext e
  constructor
  · rintro ⟨he2, he1, hPQ⟩
    exact ⟨⟨he2, he1, hPQ.1⟩, he2, he1, hPQ.2⟩
  · rintro ⟨⟨he2, he1, hP⟩, -, -, hQ⟩
    exact ⟨he2, he1, hP, hQ⟩

namespace Config

theorem ncard_involutions_K1 (C : Config A) [Finite A] :
    (nonidentityInvolutions C.K₁).ncard = 75 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (Sylow 2 A) := Fintype.ofFinite _
  have hfin : ({P : Sylow 2 A | C.L ≤ (P : Subgroup A)} : Set (Sylow 2 A)).Finite :=
    Set.toFinite _
  set S : Finset (Sylow 2 A) := hfin.toFinset with hS
  have hfinP : ∀ P : Sylow 2 A, (nonidentityInvolutions (P : Subgroup A) \
      nonidentityInvolutions C.L).Finite := fun P => Set.toFinite _
  set f : Sylow 2 A → Finset A := fun P => (hfinP P).toFinset with hf
  have hmemf : ∀ (P : Sylow 2 A) {e : A}, e ∈ f P ↔
      (e ∈ nonidentityInvolutions (P : Subgroup A) ∧
        e ∉ nonidentityInvolutions C.L) := by
    intro P e
    rw [show f P = (hfinP P).toFinset from rfl, Set.Finite.mem_toFinset]
    rfl
  have hSmem : ∀ P : Sylow 2 A, P ∈ S ↔ C.L ≤ (P : Subgroup A) := by
    intro P
    rw [show P ∈ S ↔ P ∈ ({P : Sylow 2 A | C.L ≤ (P : Subgroup A)} : Set (Sylow 2 A)) from
      Set.Finite.mem_toFinset hfin]
    rfl
  have hScard : S.card = 5 := by
    rw [show S.card = ({P : Sylow 2 A | C.L ≤ (P : Subgroup A)} : Set (Sylow 2 A)).ncard from
      (Set.ncard_eq_toFinset_card _ hfin).symm]
    exact C.ncard_sylow_ge_L
  have h12 : ∀ P ∈ S, (f P).card = 12 := by
    intro P hP
    have hcoe : Nat.card {e : A // e ∈ nonidentityInvolutions (P : Subgroup A) ∧
        e ∉ nonidentityInvolutions C.L} = (f P).card := by
      rw [show f P = (hfinP P).toFinset from rfl,
        Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
      rfl
    rw [← hcoe]
    exact C.ncard_involutions_sylow_sdiff P ((hSmem P).1 hP)
  have hdisj : (S : Set (Sylow 2 A)).PairwiseDisjoint f := by
    intro P hP Q hQ hne
    change Disjoint (f P) (f Q)
    rw [Finset.disjoint_left]
    intro e heP heQ
    rw [hmemf] at heP heQ
    have hPQ : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.L :=
      C.inf_eq_L_of_ne ((hSmem P).1 hP) ((hSmem Q).1 hQ) hne
    have hmem : e ∈ nonidentityInvolutions ((P : Subgroup A) ⊓ (Q : Subgroup A)) := by
      rw [nonidentityInvolutions_inf]
      exact ⟨heP.1, heQ.1.1, heQ.1.2.1, heQ.1.2.2⟩
    rw [hPQ] at hmem
    exact heP.2 hmem
  have hfinU : (nonidentityInvolutions C.K₁ \ nonidentityInvolutions C.L).Finite := Set.toFinite _
  have hunion : S.biUnion f = hfinU.toFinset := by
    ext e
    rw [Finset.mem_biUnion, Set.Finite.mem_toFinset hfinU]
    constructor
    · rintro ⟨P, hP, heP⟩
      rw [hmemf] at heP
      exact ⟨⟨heP.1.1, heP.1.2.1,
        C.le_normalizer_L_of_le_sylow ((hSmem P).1 hP) heP.1.2.2⟩, heP.2⟩
    · rintro ⟨he, heL⟩
      obtain ⟨he2, he1, heK⟩ := he
      obtain ⟨P, hL, heP⟩ := C.exists_sylowThroughL_of_mem he2 he1 heK
      exact ⟨P, (hSmem P).2 hL, (hmemf P).2 ⟨⟨he2, he1, heP⟩, heL⟩⟩
  have hcard : (nonidentityInvolutions C.K₁ \ nonidentityInvolutions C.L).ncard = 60 := by
    rw [Set.ncard_eq_toFinset_card _ hfinU, ← hunion, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl h12, Finset.sum_const, hScard]
    norm_num
  have hsub : nonidentityInvolutions C.L ⊆ nonidentityInvolutions C.K₁ := by
    rintro e ⟨he2, he1, heL⟩
    exact ⟨he2, he1, Subgroup.le_normalizer heL⟩
  have h := Set.ncard_sdiff hsub
  rw [hcard, C.ncard_nonidentityInvolutions_L] at h
  omega

theorem ncard_involutions_K2 (C : Config A) [Finite A] :
    (nonidentityInvolutions C.K₂).ncard = 75 :=
  C.swap.ncard_involutions_K1

end Config

theorem mem_of_mem_normalizer_of_pow_eq_one {p : ℕ} [Fact p.Prime] {P : Sylow p A} {x : A}
    {n : ℕ} (hx : x ^ p ^ n = 1) (hxN : x ∈ normalizer (P : Set A)) :
    x ∈ (P : Subgroup A) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hx)
  have hP : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hinf : Subgroup.zpowers x ⊓ normalizer (P : Set A) =
      Subgroup.zpowers x ⊓ (P : Subgroup A) :=
    IsPGroup.inf_normalizer_sylow hP P
  have hmem : x ∈ Subgroup.zpowers x ⊓ normalizer (P : Set A) :=
    ⟨Subgroup.mem_zpowers x, hxN⟩
  rw [hinf] at hmem
  exact hmem.2

namespace Config

theorem nonidentityInvolutions_normalizer_T (C : Config A) [Finite A] :
    nonidentityInvolutions (normalizer (C.T : Set A)) =
      nonidentityInvolutions (C.T : Subgroup A) := by
  ext e
  constructor
  · rintro ⟨he2, he1, heB⟩
    exact ⟨he2, he1,
      mem_of_mem_normalizer_of_pow_eq_one (p := 2) (n := 1) (by simpa [pow_two] using he2) heB⟩
  · rintro ⟨he2, he1, heT⟩
    exact ⟨he2, he1, Subgroup.le_normalizer heT⟩

theorem nonidentityInvolutions_inf_K1_K2 (C : Config A) [Finite A] :
    nonidentityInvolutions C.K₁ ∩ nonidentityInvolutions C.K₂ =
      nonidentityInvolutions (C.T : Subgroup A) := by
  rw [← nonidentityInvolutions_inf, ← C.normalizer_T_eq_inf,
    C.nonidentityInvolutions_normalizer_T]

theorem ncard_involutions_union (C : Config A) [Finite A] :
    (nonidentityInvolutions C.K₁ ∪ nonidentityInvolutions C.K₂).ncard = 123 := by
  have h := Set.ncard_union_add_ncard_inter (nonidentityInvolutions C.K₁)
    (nonidentityInvolutions C.K₂)
  rw [C.nonidentityInvolutions_inf_K1_K2, C.ncard_involutions_K1, C.ncard_involutions_K2,
    C.ncard_nonidentityInvolutions_sylow C.T] at h
  omega

theorem ncard_involutions_not_mem (C : Config A) [Finite A] :
    ({e : A | e * e = 1 ∧ e ≠ 1 ∧ e ∉ C.K₁ ∧ e ∉ C.K₂}).ncard =
      3 * Nat.card (Sylow 2 A) - 123 := by
  have hsub : nonidentityInvolutions C.K₁ ∪ nonidentityInvolutions C.K₂ ⊆
      {e : A | e * e = 1 ∧ e ≠ 1} := by
    rintro e (⟨he2, he1, -⟩ | ⟨he2, he1, -⟩) <;> exact ⟨he2, he1⟩
  have hset : {e : A | e * e = 1 ∧ e ≠ 1} \
      (nonidentityInvolutions C.K₁ ∪ nonidentityInvolutions C.K₂) =
      {e : A | e * e = 1 ∧ e ≠ 1 ∧ e ∉ C.K₁ ∧ e ∉ C.K₂} := by
    ext e
    constructor
    · rintro ⟨⟨he2, he1⟩, hK⟩
      refine ⟨he2, he1, ?_, ?_⟩
      · intro h; exact hK (Or.inl ⟨he2, he1, h⟩)
      · intro h; exact hK (Or.inr ⟨he2, he1, h⟩)
    · rintro ⟨he2, he1, h1, h2⟩
      refine ⟨⟨he2, he1⟩, ?_⟩
      rintro (⟨-, -, h⟩ | ⟨-, -, h⟩) <;> exact absurd h (by assumption)
  have h := Set.ncard_sdiff hsub
  rw [hset, C.ncard_involutions_union, C.ncard_involutions] at h
  omega

end Config

end CFSG.Quasithin.L34CIT
