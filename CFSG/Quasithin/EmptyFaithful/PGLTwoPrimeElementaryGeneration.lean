module

public import CFSG.Quasithin.EmptyFaithful.PGLTwoPrimeE1Generation
public import CFSG.Quasithin.Background.FFC4NatS3
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  (pslRange pslRange_normal pslRange_index_eq_two)

theorem pgl2_prime_sup_isE_one_eq_top_of_elemAbelian
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 5 < p)
    {S B : Subgroup (PGL2 K)}
    (hS : IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsElemAbelian 2 B) (hBne : B ≠ ⊥) :
    S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) | IsE 1 ⊤ S B I}, I) = ⊤ := by
  classical
  have hp_ne_six : p ≠ 6 := by
    intro h
    have hp6 : Nat.Prime 6 := h ▸ Fact.out
    norm_num at hp6
  have hp7 : 7 ≤ p := by omega
  have hodd : IsOddPrimePower (Nat.card K) := e22pl2pgl_isOddPrimePower hp7 hK
  have hcard : 3 < Nat.card K := by rw [hK]; omega
  haveI : Finite (PGL2 K) := e22pl2pgl_finite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 B := isPGroup_of_isElemAbelian hB
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hBcard_ne_one : Nat.card B ≠ 1 := by
    intro h
    exact hBne (Subgroup.card_eq_one.mp h)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      apply hBcard_ne_one
      simp [hk, hk0]
    · exact hkpos
  have hk_le_two : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := by omega
    have hpow : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    have hle : Nat.card B ≤ 4 :=
      CFSG.Quasithin.H13.card_le_four_of_isElemAbelian_pgl2_614 hodd hcard B hB
    omega
  interval_cases k
  ·
    have hB2 : Nat.card B = 2 := by simpa using hk
    haveI : (pslRange K).Normal := pslRange_normal hodd hcard
    haveI : IsSimpleGroup ↥(pslRange K) := e22pl2pgl_simple_J hcard
    have hE : IsE 1 ⊤ S B ⊤ :=
      isE_one_top_of_almostSimple (pslRange K) S B
        (e22pl2pgl_nonabelian_J hcard)
        (e22pl2pgl_centralizer_J hodd hcard)
        hS (e22pl2pgl_sup_eq_top hodd hS) hBS hB2
    refine top_le_iff.mp ?_
    refine le_sup_of_le_right ?_
    exact le_iSup₂_of_le (f := fun I (_ : IsE 1 ⊤ S B I) => I) ⊤ hE le_rfl
  ·
    have hB4 : Nat.card B = 4 := by simpa using hk
    have hKlein : IsKleinFour ↥B :=
      CFSG.Quasithin.FFC.isKleinFour_of_card_four hB4
        (fun u => by
          apply Subtype.ext
          simpa using hB.2 u.val u.property)
    exact pgl2_prime_sup_isE_one_eq_top hK hp hS hBS hKlein

end CFSG.Quasithin.E22L2

end
