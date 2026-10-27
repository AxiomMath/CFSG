module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCount
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  [NeZero n] {L : Type} [Field L] [Algebra K L] [Module.Finite K L] {ζ : L}
  {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E) {ψ : StatedSp n K →* G} {Bs : Subgroup G}

namespace SpFrame

omit [Finite G] [Finite K] [CharP K 2] [NeZero n] in
theorem map_centralizer_eq (hψ : Function.Injective ψ) (X : StatedSp n K) :
    (Subgroup.centralizer ({X} : Set (StatedSp n K))).map ψ =
      ψ.range ⊓ Subgroup.centralizer {ψ X} := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩

theorem false_of_commute {H : Type*} [Group H] {Q : Subgroup H} (hQ : CFSG.IsQuasisimple Q)
    (h : ∀ g ∈ Q, ∀ g' ∈ Q, g * g' = g' * g) : False := by
  obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hQ
  exact hab (Subtype.ext (h a a.2 b b.2))

theorem choice_core (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3) (hL : finrank K L = 2)
    (hs : 4 ≤ F.s) (hψ : Function.Injective ψ) (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g)
    {β : Fin F.s → ZMod 3} (hβ : β ≠ 0) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {ψ (F.tor β)}))
    (hL₁c : Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ 3 ^ 2)
    {D : Subgroup G} (hDB : D ≤ Bs) (hD9 : Nat.card D = 9) {J : Subgroup G}
    (hJq : CFSG.IsQuasisimple J) (hJG : J ≤ ψ.range) (hJD : J ≤ Subgroup.centralizer (D : Set G))
    (hJc : Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 3 ^ 3) :
    ∃ m ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  classical
  have hζ := hζo.pow_eq_one
  obtain ⟨t₁, t₂, hind, hD⟩ := F.exists_basis hζo hψ hBs hDB hD9
  have hJmap : (J.comap ψ).map ψ = J := Subgroup.map_comap_eq_self hJG
  have hJ'q : CFSG.IsQuasisimple (J.comap ψ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hJmap).symm.trans
        ((J.comap ψ).equivMapOfInjective ψ hψ).symm) hJq
  have hJ'c : ∀ a, J.comap ψ ≤ Subgroup.centralizer {F.tor (comb2 t₁ t₂ a)} := by
    intro a g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψ
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp (hJD hg) _ ((hD _).mpr ⟨a, rfl⟩)).symm
  have hcount : ∀ U : Finset (Fin F.s), (∀ i ∈ U, ∀ g ∈ J.comap ψ,
      F.tor (Pi.single i 1) * g = g * F.tor (Pi.single i 1)) → 3 ^ U.card ≤ 27 := by
    intro U hU
    refine (F.pow_card_le_of_single hζo hψ hBs J U fun i hi => ?_).trans
      (by simpa using hJc)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨g, rfl⟩ := hJG hh
    rw [← map_mul, ← map_mul, hU i hi g hh]
  obtain ⟨⟨j₁, j₂, hj, ε, hε⟩, hzero⟩ :=
    F.chars_of_quasisimple hK hζo hL hs t₁ t₂ hind hJ'q hJ'c hcount
  rw [← map_centralizer_eq hψ (F.tor β)] at hL₁
  obtain ⟨hL₁', hmapL⟩ := isComponentOf_comap_of_injective ψ hψ hL₁
  have hL₁G : L₁ ≤ ψ.range := hmapL ▸ Subgroup.map_le_range ψ _
  have hmemL : ∀ Y, Y ∈ L₁.comap ψ → ψ Y ∈ L₁ := fun Y hY => hY
  have hL₁'q : CFSG.IsQuasisimple (L₁.comap ψ) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hL₁'.2.2
  have hL₁'p : ⁅L₁.comap ψ, L₁.comap ψ⁆ = L₁.comap ψ :=
    LayerFacts.ggCommutator_eq_of_isQuasisimple hL₁'q
  have blocks := F.blocks_tor hK hζo hβ
  obtain ⟨k, hk, hLO⟩ := SevSpNs.exists_le_spSupported blocks hL₁'
  have hT3 : spEnd (F.tor β) ^ 3 = 1 := by
    rw [← spEnd_pow, F.tor_pow_three hζ β, spEnd_one]
  have hdim := F.spFixedDim_tor hζo hL β
  have hsplit : (F.zeroSet β).card + (F.suppSet β).card = F.s := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin F.s)))
      (fun l => β l = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  rcases primaryFactor_cases hK hT3 hk with rfl | rfl
  ·
    have hLO' : L₁.comap ψ ≤ spFixedFactor (F.tor β) := by
      change L₁.comap ψ ≤ spSupported _ {X - 1}
      rwa [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton] at hLO
    rcases (show (F.zeroSet β).card ≤ 1 ∨ (F.zeroSet β).card = 2 ∨
        3 ≤ (F.zeroSet β).card by omega) with hz | hz | hz
    ·
      exfalso
      rcases (show (F.zeroSet β).card = 0 ∨ (F.zeroSet β).card = 1 by omega) with hz0 | hz1
      · have hbot : spFixedFactor (F.tor β) ≤ ⊥ := by
          intro g hg
          rw [Subgroup.mem_bot]
          refine eq_of_spEnd_eq' fun v => ?_
          obtain ⟨d, rfl⟩ := F.Φ.surjective v
          rw [spEnd_one_apply]
          refine fix_of_mem_spSupported hg (phi3_irreducible hK) monic_phi3
            (fun h => phi3_ne_X_sub_one h) ?_
          rw [aeval_phi3_apply, F.tor_phi3_iff hζo]
          intro i hi
          have : i ∈ F.zeroSet β := F.mem_zeroSet.mpr hi
          rw [Finset.card_eq_zero.mp hz0] at this
          exact absurd this (Finset.notMem_empty i)
        have hsolv : Group.IsSolvable (⊥ : Subgroup (StatedSp n K)) :=
          Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
        exact ClNonsplit.not_isQuasisimple_of_le hsolv (hLO'.trans hbot) hL₁'q
      · have hd2 : spFixedDim (F.tor β) = 2 := by rw [hdim, hz1]
        have hcard := card_spFixedFactor_of_dim_two blocks hd2
        rw [hK] at hcard
        exact ClNonsplit.not_isQuasisimple_of_le
          (isSolvable_of_card_primeFactors_le_two
            (by rw [hcard]; exact SevSpNs.card_primeFactors_six)) hLO' hL₁'q
    ·
      have hcount₁ := F.pow_card_le_of_single hζo hψ hBs L₁ (F.suppSet β) fun i hi => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨g, rfl⟩ := hL₁G hh
        have hmem := F.tor_mem_spSupported hK hζo β (Pi.single i 1) (fun l hl => by
          by_cases hli : l = i
          · subst hli
            exact absurd hl (F.mem_suppSet.mp hi)
          · exact Pi.single_eq_of_ne hli 1) (O := {phi3 K}) rfl
        have hc := commute_of_mem_spFixedFactor hK (F.tor_pow_three hζ β)
          (fun h => phi3_ne_X_sub_one (Set.mem_singleton_iff.mp h).symm) (hLO' hh) hmem
        rw [← map_mul, ← map_mul, hc]
      have hs4 : F.s = 4 := by
        have h1 := hcount₁.trans hL₁c
        have h2 : (F.suppSet β).card ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
        omega
      obtain ⟨j₁', j₂', hj', hz'⟩ := hzero hs4
      obtain ⟨z₁, z₂, hz12, hzset⟩ := Finset.card_eq_two.mp hz
      refine F.choice_of_zero hK hζo hBs hD hL₁.2.2 hL₁G hLO' hz12 hj' (fun l hl => ?_) hz'
      have : l ∈ F.zeroSet β := F.mem_zeroSet.mpr hl
      rw [hzset, Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    ·
      have hlist : SpFixedListed (F.tor β) := ⟨by omega, fun h => by omega⟩
      have hq := spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (by rw [hK, pow_one])
        Nat.prime_two le_rfl blocks hlist (fun h => by omega)
      have hPc := SpNonsplitComp.isComponentOf_of_normalizes (spFixedFactor_le_centralizer _)
        (spFixedFactor_normalized _) hq
      have hLeq : L₁.comap ψ = spFixedFactor (F.tor β) := by
        rcases isComponentOf_eq_or_commute hL₁' hPc with h | h
        · exact h
        · exfalso
          apply not_le_centralizer_self_of_isQuasisimple hL₁'.2.2
          rw [Subgroup.commutator_comm] at h
          exact hLO'.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ :=
        Finset.two_lt_card.mp (show 2 < (F.zeroSet β).card by omega)
      have hg := F.swap_mem_spFixedFactor hK hζo β false (F.mem_zeroSet.mp hi₁)
        (F.mem_zeroSet.mp hi₂) (i := i₁) (j := i₂)
      have hl := F.swap_mem_spFixedFactor hK hζo β false (F.mem_zeroSet.mp hi₁)
        (F.mem_zeroSet.mp hi₃) (i := i₁) (j := i₃)
      rw [← hLeq] at hg hl
      exact F.choice_of_swap hζo hψ hBs hD h12 h13 h23 hj hε (hmemL _ hg) (hmemL _ hl)
  ·
    have hX1 : (X - 1 : K[X]) ∉ ({phi3 K, reciprocalPolynomial (phi3 K)} : Set K[X]) := by
      rw [reciprocal_phi3, Set.pair_eq_singleton]
      exact fun h => phi3_ne_X_sub_one (Set.mem_singleton_iff.mp h).symm
    have hw : 3 ≤ (F.suppSet β).card := by
      by_contra hw
      have hle := F.le_spFixedFactor hK hζo hL (c := β) (by omega) hL₁'p hL₁'.1
      exact false_of_commute hL₁'q fun g hg g' hg' =>
        commute_of_mem_spFixedFactor hK (F.tor_pow_three hζ β) hX1 (hle hg) (hLO hg')
    have hq := SevSpNs.isQuasisimple_spPull_of_le (h := ⟨phi3 K, hk⟩) Nat.prime_three
      (by norm_num) le_rfl blocks phi3_ne_X_sub_one hL₁' hLO
    have hLeq := SevSpNs.eq_spPull_of_le hL₁' hLO hq
    obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ :=
      Finset.two_lt_card.mp (show 2 < (F.suppSet β).card by omega)
    have hβ1 := F.mem_suppSet.mp hi₁
    have hβ2 := F.mem_suppSet.mp hi₂
    have hβ3 := F.mem_suppSet.mp hi₃
    obtain ⟨bsw, hbsw⟩ : ∃ b, β i₁ = sgnZ b (β i₂) := by
      rcases exists_sgnZ_of_ne_zero _ _ hβ1 hβ2 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨bsw', hbsw'⟩ : ∃ b, β i₁ = sgnZ b (β i₃) := by
      rcases exists_sgnZ_of_ne_zero _ _ hβ1 hβ3 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hg := mem_spPull_of_mul_self hK
      (F.swap_mem_spSupported hK hζo β bsw hβ1 hβ2 hbsw (O := {phi3 K,
        reciprocalPolynomial (phi3 K)}) (Set.mem_insert _ _)) (F.swap_mul_self h12 bsw)
    have hl := mem_spPull_of_mul_self hK
      (F.swap_mem_spSupported hK hζo β bsw' hβ1 hβ3 hbsw' (O := {phi3 K,
        reciprocalPolynomial (phi3 K)}) (Set.mem_insert _ _)) (F.swap_mul_self h13 bsw')
    rw [← hLeq] at hg hl
    exact F.choice_of_swap hζo hψ hBs hD h12 h13 h23 hj hε (hmemL _ hg) (hmemL _ hl)

end SpFrame

end ChoiceTwo

end CFSG.StandardType
