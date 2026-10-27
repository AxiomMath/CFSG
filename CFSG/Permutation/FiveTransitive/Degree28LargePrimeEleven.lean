module

public import CFSG.Permutation.FiveTransitive.Degree28LargePrimeElevenBound
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.PrimeCyclicFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree28LargePrimeEleven

open MulAction Subgroup SylowFixedActionCore PrimeCyclicFixedAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) :
    ¬ 11 ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  classical
  intro hd
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let H := fixingSubgroup P (s : Set X)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 11 hd
  have hZ : IsPGroup 11 (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  let Q := sylowImage X P (s : Set X) S
  have hQ : IsPGroup 11 Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hSge : 11 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hQne : Q ≠ ⊥ := by
    intro he
    have h := hSge
    rw [← hQcard,he] at h
    simp at h
  have hsQ : (s : Set X) ⊆ fixedPoints Q X := by
    intro x hx q
    obtain ⟨v,hv,he⟩ := q.property
    change q.val • x = x
    rw [← he]
    exact (mem_fixingSubgroup_iff P).mp v.property x hx
  have hfixed : 5 ≤ Nat.card (fixedPoints Q X) := by
    rw [Nat.card_coe_set_eq]
    have h := Set.ncard_le_ncard hsQ
    simpa only [Set.ncard_coe_finset,hs] using h
  have hQeleven := Degree28LargePrimeElevenBound.card_eq_eleven P hcard h5 hnotAlt Q hQ hQne hfixed
  have hQsix := Degree28LargePrimeElevenBound.fixed_card_eq_six P hcard h5 hnotAlt Q hQ hQne hfixed
  let r : P := u
  have hr : orderOf r = 11 := (Subgroup.orderOf_coe u).trans hu
  have hRQ : zpowers r = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hr,hQeleven]
  let F := cyclicFixedPoints X P r
  let FC := cyclicComplement X P r
  let N := cyclicNormalizer P r
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype FC := Fintype.ofFinite _
  have hFsix : Fintype.card F = 6 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (FixedNormalizerAction.Fixed (X := X) (zpowers r)) = 6
    rw [FixedNormalizerAction.fixed_eq,hRQ]
    exact hQsix
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
  have htop : J = ⊤ := Equiv.Perm.eq_top_of_isMultiplyPretransitive (by
    simpa only [Nat.card_eq_fintype_card,hFsix] using hJ5)
  have hAlt : alternatingGroup F ≤ J := by rw [htop]; exact le_top
  let c := complementPerm X P r
  have hcorder : orderOf c = 11 := orderOf_complementPerm X P r (by norm_num) hr
  have hcprime : Nat.Prime (orderOf c) := by rw [hcorder]; norm_num
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hcprime
  have hcsupport : c.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support,Finset.mem_univ,iff_true]
    exact complementPerm_fixedPointFree X P r x
  have hFCcard : Fintype.card FC = 22 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ((F : Set X)ᶜ : Set X) = 22
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq]
    change Nat.card X - Nat.card F = 22
    rw [Nat.card_eq_fintype_card,hcard,Nat.card_eq_fintype_card,hFsix]
  have hshape : Fintype.card FC = 11 * c.cycleType.card := by
    calc
      _ = c.support.card := by rw [hcsupport,Finset.card_univ]
      _ = c.cycleType.sum := c.sum_cycleType.symm
      _ = _ := by rw [hm,hcorder]; simp [Nat.mul_comm]; omega
  have hcycles : c.cycleType.card < Fintype.card F := by rw [hFCcard] at hshape; rw [hFsix]; omega
  exact hnotAlt (alternatingGroup_le_of_prime_cyclic_fixed_action_cycle_count
    X P (by omega) hexp r (by norm_num) hr (by rw [hFsix]; omega) hAlt hcycles)

end FiveTransitive.Degree28LargePrimeEleven

end CFSG
