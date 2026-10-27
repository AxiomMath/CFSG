module

public import CFSG.Permutation.FiveTransitive.Degree31LargePrimeSubgroup
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.PrimeCyclicFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree31LargePrimeSmall

open MulAction Subgroup SylowFixedActionCore PrimeCyclicFixedAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 11 ∨ p = 13)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  classical
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  let H := fixingSubgroup P (s : Set X)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) p hd
  have hZ : IsPGroup p (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  let Q := sylowImage X P (s : Set X) S
  have hQ : IsPGroup p Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hSge : p ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hQne : Q ≠ ⊥ := by
    intro he
    have h := hSge
    rw [← hQcard,he] at h
    have hp2 := hp.two_le
    simp at h
    omega
  have hQprime := Degree31LargePrimeSubgroup.card_eq_prime p hp hcases P hcard h5 hnotAlt Q hQ hQne
  have hQfixed := Degree31LargePrimeSubgroup.fixed_card p hp hcases P hcard h5 hnotAlt Q hQ hQne
  let r : P := u
  have hr : orderOf r = p := (Subgroup.orderOf_coe u).trans hu
  have hRQ : zpowers r = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hr,hQprime]
  let F := cyclicFixedPoints X P r
  let FC := cyclicComplement X P r
  let N := cyclicNormalizer P r
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype FC := Fintype.ofFinite _
  have hFcard : Fintype.card F = 31 - 2 * p := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (FixedNormalizerAction.Fixed (X := X) (zpowers r)) = 31 - 2 * p
    rw [FixedNormalizerAction.fixed_eq,hRQ]
    exact hQfixed
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hNfive : ∀ a b : Fin 5 → F, Function.Injective a → Function.Injective b →
      ∃ g : N, ∀ i, g • a i = b i := by
    have htransport (A : Subgroup P) (hA : A = Q) :
        ∀ a b : Fin 5 → FixedNormalizerAction.Fixed (X := X) A,
          Function.Injective a → Function.Injective b →
          ∃ g : FixedNormalizerAction.Normalizer A, ∀ i, g • a i = b i := by
      subst A
      exact sylowNormalizer_five_transitive_on_fixedPoints X P hexp
        (s : Set X) (by simpa only [Set.ncard_coe_finset] using hs) S
    exact htransport (zpowers r) hRQ
  let J := (toPermHom N F).range
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g,hg⟩ := hNfive a b a.injective b.injective
    refine ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,?_⟩
    ext i
    exact congrArg Subtype.val (hg i)
  have hFcases : Fintype.card F = 5 ∨ Fintype.card F = 9 := by
    rcases hcases with rfl | rfl <;> omega
  have hAlt : alternatingGroup F ≤ J := by
    rcases hFcases with hFfive | hFnine
    · have htop : J = ⊤ := Equiv.Perm.eq_top_of_isMultiplyPretransitive (by
        rw [Nat.card_eq_fintype_card,hFfive]
        let _ := hJ5
        exact isMultiplyPretransitive_of_le (G := J) (α := F) (n := 5)
          (by norm_num) (by rw [Nat.card_eq_fintype_card,hFfive]))
      rw [htop]
      exact le_top
    · let _ : Fintype J := Fintype.ofFinite J
      have hJexp : ∀ a b : Fin 5 → F, Function.Injective a → Function.Injective b →
          ∃ j : J, ∀ i, j • a i = b i := by
        intro a b ha hb
        obtain ⟨j,hj⟩ := hJ5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
        exact ⟨j,fun i => DFunLike.congr_fun hj i⟩
      have hNested := Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_nine
        J F hFnine hJexp
      apply hNested.trans
      rintro σ ⟨j,rfl⟩
      exact j.property
  let c := complementPerm X P r
  have hcorder : orderOf c = p := orderOf_complementPerm X P r hp hr
  have hcprime : Nat.Prime (orderOf c) := by rw [hcorder]; exact hp
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hcprime
  have hcsupport : c.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support,Finset.mem_univ,iff_true]
    exact complementPerm_fixedPointFree X P r x
  have hFCcard : Fintype.card FC = 2 * p := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ((F : Set X)ᶜ : Set X) = 2 * p
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq]
    change Nat.card X - Nat.card F = 2 * p
    rw [Nat.card_eq_fintype_card,hcard,Nat.card_eq_fintype_card,hFcard]
    rcases hcases with rfl | rfl <;> norm_num
  have hshape : Fintype.card FC = p * c.cycleType.card := by
    calc
      _ = c.support.card := by rw [hcsupport,Finset.card_univ]
      _ = c.cycleType.sum := c.sum_cycleType.symm
      _ = _ := by
        rw [hm,hcorder]
        simp only [Multiset.sum_replicate,Multiset.card_replicate,nsmul_eq_mul,Nat.cast_id]
        exact Nat.mul_comm _ _
  have hcycles : c.cycleType.card < Fintype.card F := by
    rw [hFCcard] at hshape
    rw [hFcard]
    rcases hcases with rfl | rfl <;> omega
  exact hnotAlt (alternatingGroup_le_of_prime_cyclic_fixed_action_cycle_count
    X P (by omega) hexp r hp hr (by rw [hFcard]; rcases hcases with rfl | rfl <;> norm_num) hAlt hcycles)

end FiveTransitive.Degree31LargePrimeSmall

end CFSG
