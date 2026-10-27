module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ChevOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Case

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalEmbed
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LieType.Chevalley.E8FrameLines
import CFSG.LieType.Chevalley.SectionalTwoRankMonomial
import CFSG.CGT.PushingUpLit.SolK.GenFour
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem sectionalTwoRankLE_two_alternatingGroup {n : ℕ} (hn : n ≤ 7) :
    CFSG.GH74.SectionalTwoRankLE (alternatingGroup (Fin n)) 2 := by
  interval_cases n
  · have hcard : Nat.card (alternatingGroup (Fin 0)) = 1 := by
      have hle : Nat.card (alternatingGroup (Fin 0)) ≤ 1 := by
        simpa [Nat.card_perm] using
          Nat.card_le_card_of_injective (Subgroup.subtype (alternatingGroup (Fin 0)))
            Subtype.val_injective
      have hpos : 0 < Nat.card (alternatingGroup (Fin 0)) := Nat.card_pos
      omega
    exact CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) (by
      rw [hcard]
      norm_num)
  · have hcard : Nat.card (alternatingGroup (Fin 1)) = 1 := by
      have hle : Nat.card (alternatingGroup (Fin 1)) ≤ 1 := by
        simpa [Nat.card_perm] using
          Nat.card_le_card_of_injective (Subgroup.subtype (alternatingGroup (Fin 1)))
            Subtype.val_injective
      have hpos : 0 < Nat.card (alternatingGroup (Fin 1)) := Nat.card_pos
      omega
    exact CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) (by
      rw [hcard]
      norm_num)
  · refine CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) ?_
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · refine CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) ?_
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · refine CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) ?_
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · refine CFSG.LieType.Chevalley.sectionalTwoRankLE_of_not_two_pow_dvd (r := 2) ?_
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · let c : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5]
    have hc : c ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    let x : alternatingGroup (Fin 6) := ⟨c, hc⟩
    have hx2 : x ^ 2 ≠ 1 := by
      intro h
      have h2 : (x : Equiv.Perm (Fin 6)) ((x : Equiv.Perm (Fin 6)) 0) = 2 := by
        change (c : Equiv.Perm (Fin 6)) ((c : Equiv.Perm (Fin 6)) 0) = 2
        decide +kernel
      have h0 : ((x ^ 2 : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) 0 = 0 := by
        rw [h]
        rfl
      have h0' : (x : Equiv.Perm (Fin 6)) ((x : Equiv.Perm (Fin 6)) 0) = 0 := by
        simpa [pow_two] using h0
      rw [h2] at h0'
      omega
    have hx4 : x ^ 4 = 1 := by
      apply Subtype.ext
      show (c : Equiv.Perm (Fin 6)) ^ 4 = (1 : Equiv.Perm (Fin 6))
      decide +kernel
    have hP : IsPGroup 2 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card_dvd_pow (p := 2) (n := 2) ?_
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
      simpa using hdvd
    obtain ⟨S, hxS⟩ := hP.exists_le_sylow
    have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hfac : (360 : ℕ).factorization 2 = 3 := by
      rw [show 360 = 2 ^ 3 * 45 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45)]
    have hS8 : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity, hcard, hfac]
      norm_num
    have hSsec : CFSG.GH74.SectionalTwoRankLE (S : Subgroup (alternatingGroup (Fin 6))) 2 :=
      CFSG.LieType.Chevalley.E8Lines.sectionalTwoRankLE_two_of_card_eq_eight
        (X := ↥S) (x := ⟨x, hxS (Subgroup.mem_zpowers x)⟩) hS8 (by
          intro h
          exact hx2 (Subtype.ext_iff.mp h))
    exact CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S hSsec
  · let c : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5]
    have hc : c ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    let x : alternatingGroup (Fin 7) := ⟨c, hc⟩
    have hx2 : x ^ 2 ≠ 1 := by
      intro h
      have h2 : (x : Equiv.Perm (Fin 7)) ((x : Equiv.Perm (Fin 7)) 0) = 2 := by
        change (c : Equiv.Perm (Fin 7)) ((c : Equiv.Perm (Fin 7)) 0) = 2
        decide +kernel
      have h0 : ((x ^ 2 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) 0 = 0 := by
        rw [h]
        rfl
      have h0' : (x : Equiv.Perm (Fin 7)) ((x : Equiv.Perm (Fin 7)) 0) = 0 := by
        simpa [pow_two] using h0
      rw [h2] at h0'
      omega
    have hx4 : x ^ 4 = 1 := by
      apply Subtype.ext
      show (c : Equiv.Perm (Fin 7)) ^ 4 = (1 : Equiv.Perm (Fin 7))
      decide +kernel
    have hP : IsPGroup 2 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card_dvd_pow (p := 2) (n := 2) ?_
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
      simpa using hdvd
    obtain ⟨S, hxS⟩ := hP.exists_le_sylow
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hfac : (2520 : ℕ).factorization 2 = 3 := by
      rw [show 2520 = 2 ^ 3 * 315 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
    have hS8 : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity, hcard, hfac]
      norm_num
    have hSsec : CFSG.GH74.SectionalTwoRankLE (S : Subgroup (alternatingGroup (Fin 7))) 2 :=
      CFSG.LieType.Chevalley.E8Lines.sectionalTwoRankLE_two_of_card_eq_eight
        (X := ↥S) (x := ⟨x, hxS (Subgroup.mem_zpowers x)⟩) hS8 (by
          intro h
          exact hx2 (Subtype.ext_iff.mp h))
    exact CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S hSsec


theorem asch54Alt_of (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : Asch54Alt := by
  intro Q _ _ L T hK hLn hLs hLnab hC hP hL0 hT hnu
  obtain ⟨n, hn5, ⟨e⟩⟩ := hP
  have hL0facts : ∀ (X : Type) [Group X], IsCalL0 X →
      ∃ _ : Finite X, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) ∧
        ∃ a b : X, a * b ≠ b * a :=
    fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
      CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
      ((isCalL0_iff_asc1930ListB X).1 hX)
  by_cases hn6 : n ≤ 6
  · have hsmall : ∀ (X : Type) [Group X] [Finite X],
        (∃ m : ℕ, m ≤ 6 ∧ Nonempty (X ≃* alternatingGroup (Fin m))) →
        CFSG.GH74.SectionalTwoRankLE X 2 := by
      intro X _ _ ⟨m, hm6, ⟨eX⟩⟩
      exact (sectionalTwoRankLE_two_alternatingGroup (le_trans hm6 (by norm_num))).of_mulEquiv
        eX.symm
    exact asch54Case_of_sectionalTwoRankLE hS hsmall Q L T hK hLn hLs hLnab hC
      ⟨n, hn6, ⟨e⟩⟩ hL0 hT hnu
  · by_cases hn9 : n = 9
    · subst n
      have hcal : IsCalL0 ↥L := by
        unfold IsCalL0
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))
      exact (hL0 hcal).elim
    · by_cases hn11 : n ≤ 11
      · obtain ⟨φ, hφ, hA⟩ :=
          @CFSG.AGLEmbedding.exists_embedding_alternating_of_ne_six Q _ n hn5 (by omega)
            L hLn e hC
        let ψ : ↥(⊤ : Subgroup Q) →* Equiv.Perm (Fin n) :=
          φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom
        have hψ : Function.Injective ψ := hφ.comp (Subgroup.topEquiv (G := Q)).injective
        have hrange : ψ.range = φ.range := by
          change (φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom).range = φ.range
          rw [MonoidHom.range_comp,
            MonoidHom.range_eq_top.mpr (Subgroup.topEquiv (G := Q)).surjective,
            Subgroup.map_top]
        have hAψ : alternatingGroup (Fin n) ≤ ψ.range := by
          rw [hrange]
          exact hA
        exact Or.inl (Asch59.eq_lGen_of_injective_perm hL0facts (by omega) hn11 (by omega)
          ψ hψ hAψ le_top hT.isPGroup).symm
      · have hn12 : 12 ≤ n := by omega
        obtain ⟨φ, hφ, hA⟩ :=
          @CFSG.AGLEmbedding.exists_embedding_alternating_of_ne_six Q _ n hn5 (by omega)
            L hLn e hC
        let ψ : ↥(⊤ : Subgroup Q) →* Equiv.Perm (Fin n) :=
          φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom
        have hψ : Function.Injective ψ := hφ.comp (Subgroup.topEquiv (G := Q)).injective
        have hrange : ψ.range = φ.range := by
          change (φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom).range = φ.range
          rw [MonoidHom.range_comp,
            MonoidHom.range_eq_top.mpr (Subgroup.topEquiv (G := Q)).surjective,
            Subgroup.map_top]
        have hAψ : alternatingGroup (Fin n) ≤ ψ.range := by
          rw [hrange]
          exact hA
        obtain ⟨h3, h1⟩ := Asch59.pRank_three_of_injective_perm hL0facts hn12 ψ hψ hAψ
          le_top hT.isPGroup
        exact Or.inr ⟨3, Nat.prime_three, by norm_num, h3, h1⟩

end CFSG.LocalAnalysis.WeakClosure81
