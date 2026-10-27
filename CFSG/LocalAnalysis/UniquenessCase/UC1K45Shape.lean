module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem uc45_quotient_pPrimeCore_isPerfect (c : Front45 p G D) :
    Group.IsPerfect (G ⧸ CFSG.pPrimeCore 3 G) := by
  haveI : Group.IsPerfect G := ⟨c.perfect⟩
  infer_instance

theorem uc45_quotient_pPrimeCore_nonabelian (c : Front45 p G D) :
    ∃ a b : G ⧸ CFSG.pPrimeCore 3 G, a * b ≠ b * a := by
  haveI : IsSimpleGroup (G ⧸ CFSG.pPrimeCore 3 G) :=
    isSimpleGroup_quotient_pPrimeCore (D := D) c.card_three c.gen c.rank
  haveI : Group.IsPerfect (G ⧸ CFSG.pPrimeCore 3 G) :=
    uc45_quotient_pPrimeCore_isPerfect c
  by_contra h
  simp only [not_exists, not_not] at h
  exact Group.IsPerfect.not_isMulCommutative (G ⧸ CFSG.pPrimeCore 3 G)
    (isMulCommutative_iff.mpr h)

theorem uc45_quotient_pPrimeCore_pRank (c : Front45 p G D) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 G)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := G)
  rw [CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := G) (N := CFSG.pPrimeCore 3 G)
    ((Nat.prime_three.coprime_iff_not_dvd).1 hcop)]
  exact c.rank

theorem uc45_card_D_map_pPrimeCore (c : Front45 p G D)
    (hW : Wker G = CFSG.pPrimeCore 3 G) :
    Nat.card ↥(D.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G))) = 3 := by
  have hfun : (QuotientGroup.quotientMulEquivOfEq hW).toMonoidHom.comp
        (QuotientGroup.mk' (Wker G)) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 G) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
  have hmap : (D.map (QuotientGroup.mk' (Wker G))).map
        (QuotientGroup.quotientMulEquivOfEq hW).toMonoidHom =
      D.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) := by
    rw [Subgroup.map_map, hfun]
  calc
    Nat.card ↥(D.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)))
        = Nat.card ↥((D.map (QuotientGroup.mk' (Wker G))).map
            (QuotientGroup.quotientMulEquivOfEq hW).toMonoidHom) := by rw [← hmap]
      _ = Nat.card ↥(D.map (QuotientGroup.mk' (Wker G))) :=
            Subgroup.card_map_of_injective
              (QuotientGroup.quotientMulEquivOfEq hW).injective
      _ = 3 := uc45_card_D_map c.toPre45

theorem uc45_map_conj_mk' (g : G) :
    (D.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G))).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pPrimeCore 3 G) g)).toMonoidHom =
      (D.map (MulAut.conj g).toMonoidHom).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) := by
  have hfun : (MulAut.conj (QuotientGroup.mk' (CFSG.pPrimeCore 3 G) g)).toMonoidHom.comp
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) =
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)).comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, hfun]

theorem uc45_alt5 (hPair : PairX) (hInsp : InspPairShape) (c : Front45 p G D)
    (hW : Wker G = CFSG.pPrimeCore 3 G) :
    CFSG.Quasithin.IsAlt 5 (G ⧸ CFSG.pPrimeCore 3 G) := by
  by_contra hnot
  have hK : CFSG.Open.IsKGroup (G ⧸ CFSG.pPrimeCore 3 G) :=
    c.kgroup.quotient (CFSG.pPrimeCore 3 G)
  have hsimple : IsSimpleGroup (G ⧸ CFSG.pPrimeCore 3 G) :=
    isSimpleGroup_quotient_pPrimeCore (D := D) c.card_three c.gen c.rank
  have hnonab := uc45_quotient_pPrimeCore_nonabelian c
  have hrank := uc45_quotient_pPrimeCore_pRank c
  have hcardDbar := uc45_card_D_map_pPrimeCore c hW
  obtain ⟨g', hg'⟩ := hInsp (G ⧸ CFSG.pPrimeCore 3 G) hK hsimple hnonab hrank hnot
    (D.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G))) hcardDbar
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 G) g'
  have hpair := uc45_pair_shape hPair c.toPre45 (CFSG.pPrimeCore 3 G) hW.symm g
  rw [← hg] at hg'
  rw [uc45_map_conj_mk' (D := D) g] at hg'
  rw [Subgroup.map_sup] at hpair
  exact hg' hpair

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
