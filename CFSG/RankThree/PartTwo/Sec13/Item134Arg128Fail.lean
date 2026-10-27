module

public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailHJ
public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailBalance
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
open CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail
open CFSG.ABGLocalTools (IsSylowOf)

theorem Item134Arg128Fail.mem_B_of_autIn_equiv {G : Type} [Group G] [Finite G]
    {A L K : Subgroup G} {c d : G} (H : Base A c L d K)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (haA : a ∈ A) {J : Subgroup G} (hJa : J ≤ Subgroup.centralizer ({a} : Set G))
    {Q : Type} [Group Q] (e : Sec4.autIn J A ≃* Q) {q : Q} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) :
    a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  set σ := e.symm q with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hq3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hq1
    have := congrArg e h
    rwa [hσ, MulEquiv.apply_symm_apply, map_one] at this
  exact mem_B_of_autIn H hW haA hJa σ.2
    (by rw [← Subgroup.coe_pow, hσ3, Subgroup.coe_one]) (fun h => hσ1 (Subtype.ext h))

theorem omegaA_eq_of_central
    (h45 : Sec4.Item4_5) (h131 : Item131) (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    (h414 : Sec4.Item4_14_local) (h422 : Sec4.Item4_22) (h48 : Sec4.Item4_8)
    (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (d : G) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    (K : Subgroup G) (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hcen : ∀ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
      A ⊓ Sec4.thetaQuotCentralizer K ≤ (Subgroup.center P).map P.subtype) :
    omegaA A = {Subgroup.zpowers c} := by
  have H := base_of_central h45 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6 hcen
  obtain ⟨-, heq, -, -⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
  obtain ⟨S, hSD⟩ := H.exists_sylowData
  obtain ⟨T, hTD⟩ := H.exists_tData hSD
  ext F
  rw [Set.mem_singleton_iff]
  constructor
  · intro hF
    have hFΩ := hF
    obtain ⟨hFA, hF3, a, rfl, -⟩ := hF
    have haA : a ∈ A := hFA (Subgroup.mem_zpowers a)
    have ha3 : a ^ 3 = 1 := h.isElemAbelian.2 a haA
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF3
      norm_num at hF3
    by_contra hne
    have hac : a ∉ Subgroup.zpowers c := fun hmem => hne
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
        rw [hF3, h.card_zpowers]))
    have had : a ∉ Subgroup.zpowers d := by
      intro hmem
      apply zpowers_d_not_mem_omegaA h422 H heq
      have heq' : Subgroup.zpowers a = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
          rw [hF3, Nat.card_zpowers, H.orderOf_d])
      exact heq' ▸ hFΩ
    obtain ⟨J, hJ'⟩ := exists_sec13Data h422 h45 h hFΩ
    have hJa : J ≤ Subgroup.centralizer ({a} : Set G) := hJ'.le_centralizer
    rcases cases131 h131 hspor slTwoCenter hJ' with ⟨-, -, -, hc1⟩ | ⟨haJ, h9, hMJ, hS3⟩ |
        ⟨haJ, -, hZ3, hx⟩ | ⟨haJ, h7⟩
    ·
      rcases hc1 with ⟨-, hQ | hSL⟩ | ⟨-, hZ4⟩ | ⟨-, hQ⟩
      · obtain ⟨e⟩ := hQ
        exact false_of_autIn_pow_six h.isElemAbelian h.card_eq hW haA hdA hd1 had hJa e
          (q := QuaternionGroup.xa 0) (by decide)
      · obtain ⟨e⟩ := hSL
        exact false_of_autIn_pow_six h.isElemAbelian h.card_eq hW haA hdA hd1 had hJa e
          (q := ⟨!![0, -1; 1, 0], by decide⟩) (by decide)
      · obtain ⟨e⟩ := hZ4
        exact false_of_autIn_pow_six h.isElemAbelian h.card_eq hW haA hdA hd1 had hJa e
          (q := Multiplicative.ofAdd (1 : ZMod 4)) (by decide)
      · obtain ⟨e⟩ := hQ
        exact false_of_autIn_pow_six h.isElemAbelian h.card_eq hW haA hdA hd1 had hJa e
          (q := QuaternionGroup.xa 0) (by decide)
    ·
      exact false_of_sporadic h414 H hSD hTD hW hac had hJ' haJ h9 hMJ hS3
    ·
      obtain ⟨e⟩ := hZ3
      have haB := Item134Arg128Fail.mem_B_of_autIn_equiv H hW haA hJa e
        (q := Multiplicative.ofAdd (1 : ZMod 3)) (by decide) (by decide)
      exact false_of_pgl h48 H heq haB ha1 hJ' haJ hx
    ·
      rcases h7 with hSL | ⟨hHeis, hWa⟩
      · exact false_of_isSLThreePiTwo H hTD hW had hJ' hSL
      · by_cases haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
        · exact false_of_mem_of_mem_B h48 H heq haB had hJ' haJ (Or.inr hHeis)
        · exact false_of_normalizer_le H hSD hW haA haB hWa
  · rintro rfl
    exact h.zpowers_mem_omegaA

theorem item134Arg128_of_central
    (h45 : Sec4.Item4_5) (h131 : Item131) (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    (h414 : Sec4.Item4_14_local) (h422 : Sec4.Item4_22) (h48 : Sec4.Item4_8)
    (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (d : G) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    (K : Subgroup G) (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hcen : ∀ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
      A ⊓ Sec4.thetaQuotCentralizer K ≤ (Subgroup.center P).map P.subtype) :
    omegaA A = {Subgroup.zpowers c} ∨
    CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
      IsSylowOf 3 (oThreeWStar A) (wStar A) ∧
      ((omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧ (omegaA A).ncard = 3) ∨
        ∃ I ∈ thetaComponentsAt 3 d, d ∈ I ∧
          Sec4.IsTripleCover (I ⧸ aschbacherSolvableCore 3 I) (alternatingGroup (Fin 6)) ∧
          ∃ a ∈ A ⊓ K, a ∉ Subgroup.zpowers d ∧
            omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
              orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 ∧
            ∃ La : Subgroup G, lA A a = {La} ∧
              Nonempty (La ⧸ aschbacherSolvableCore 3 La ≃*
                CFSG.Blueprint.NativeSporadic.J2)) :=
  Or.inl (omegaA_eq_of_central h45 h131 hspor h415 h414 h422 h48 G A c L h hJ d hdA hd1 hS K hK
    hLK hKeq hA6 hW hcen)

end CFSG.RankThree.PartTwo.Sec13
