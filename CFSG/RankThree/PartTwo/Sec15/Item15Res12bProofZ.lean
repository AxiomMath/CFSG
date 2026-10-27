module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofZLoc
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof15Res12b

variable {G : Type} [Group G] [Finite G]

theorem not_inf_centralizer_le_y4 {A L Y : Subgroup G} {d : G} (D : Data1523Y4 A L Y d)
    (hd3 : d ^ 3 = 1) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {S : Subgroup G}
    (hSY : S ≤ Y) (hS2 : IsPGroup 2 S) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSQ : ¬ S ≤ CFSG.Open.pCoreOf 2 Y) :
    ¬ S ⊓ Subgroup.centralizer ({d} : Set G) ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  set X := oPrimeResidualOf 3 (Y ⊓ k1523 A d) with hX
  have hXd : X ≤ Subgroup.centralizer ({d} : Set G) :=
    (oPrimeResidualOf_le_self 3 _).trans (inf_le_right.trans
      ((oPrimeResidualOf_le_self 3 _).trans (delta_le _)))
  have hXY : X ≤ Y := (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  have hdQ : d ∈ Subgroup.normalizer (Q : Set G) :=
    (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) D.mem_d
  have hSXQ : S ≤ Q ⊔ X := by
    rw [sup_comm, ← D.eq_y]
    exact hSY
  have hSd : ⁅S, Subgroup.zpowers d⁆ ≤ Q :=
    Proof15Res11.commutator_zpowers_le_of_le_sup hdQ
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hXd hSXQ
  have hdS : Subgroup.zpowers d ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.mpr (hAS D.mem_d)
  have hdp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Sec13.card_zpowers_of_pow_three hd3 D.ne_d, pow_one])
  have hS3 : ¬ 3 ∣ Nat.card S := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three (Subgroup.zpowers d) S hdp hS3 hdS
  have hcz : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcz] at hfac
  intro hle
  apply hSQ
  rw [hfac]
  exact sup_le hSd hle

end Proof15Res12b

open Proof15Res11 Proof15Res12b

theorem step1523ZY4R_of_res12b
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hP : Step1523ZPickY4) (hZL : Step1523ZLoc) : Step1523ZY4R := by
  intro G _ _ A c L h _ hJ Y hY hm d D hQd
  obtain ⟨b, hbA, hbd, S, hSYb, hS2, hAS, hSQ⟩ := hP G A c L h hJ Y hY hm d D hQd
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hd3 : d ^ 3 = 1 := hA.1.2 d D.mem_d
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  obtain ⟨hWd, h12, hpts⟩ := onType_facts h134 h48 h hJ D.mem_d D.ne_d D.central_d D.type_k
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  set Z := S ⊓ Subgroup.centralizer ({d} : Set G) with hZ
  have hSY : S ≤ Y := hSYb.trans inf_le_left
  have hSb : S ≤ Subgroup.centralizer ({b} : Set G) := hSYb.trans inf_le_right
  have hdb : d ∉ Subgroup.zpowers b := Proof152ResW.not_mem_zpowers_symm hA D.ne_d hbA hbd
  have hZ2 : IsPGroup 2 Z := hS2.to_le inf_le_left
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := by
    refine Late.le_normalizer_inf hAS ?_
    intro a ha
    exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
      (hD.commute ha D.mem_d))
  refine ⟨b, Z, (hpts b hbA hbd).1, hdb, inf_le_left.trans hSY,
    not_inf_centralizer_le_y4 D hd3 hAY hSY hS2 hAS hSQ, fun F hF hF3 hFd => ?_⟩
  have hBA : Subgroup.closure {b, d} ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hbA
    · exact D.mem_d
  obtain ⟨f, hfF⟩ : ∃ f, F = Subgroup.zpowers f := by
    have h3 : Nat.Prime (Nat.card F) := hF3 ▸ Nat.prime_three
    have : IsCyclic F := isCyclic_of_prime_card (hp := ⟨h3⟩) rfl
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F)
    refine ⟨g, le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr g.2)⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hfA : f ∈ A := hBA (hF (hfF ▸ Subgroup.mem_zpowers f))
  have hfd : f ∉ Subgroup.zpowers d := by
    intro hmem
    apply hFd
    rw [hfF]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
    rw [← hfF, hF3, Sec13.card_zpowers_of_pow_three hd3 D.ne_d]
  obtain ⟨-, w, hwA, hwf⟩ := hpts f hfA hfd
  have hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := hWd hwA
  have hFw : F = Subgroup.zpowers (w * c * w⁻¹) := by
    rw [hfF, hwf, Proof15Res4.map_conj_zpowers]
  have hRw : Sec15R G A (w * c * w⁻¹) (L.map (MulAut.conj w).toMonoidHom) :=
    { h with
      zpowers_mem_omegaA := by
        rw [← Proof15Res4.map_conj_zpowers]
        exact (map_conj_mem_omegaA_iff hwA).mpr hD.zpowers_mem_omegaA
      mem_lA := (map_conj_mem_lA_iff hwA).mpr hD.mem_lA }
  have hJw := nonempty_j2_conj hJ w
  have hΩw : omegaA A ≠ {Subgroup.zpowers (w * c * w⁻¹)} := by
    intro heq
    rw [heq, Set.ncard_singleton] at h12
    omega
  have hdw : IsThreeCentralIn (L.map (MulAut.conj w).toMonoidHom) d := by
    have h1 := Item148PtRes.isThreeCentralIn_map_conj D.central_d w
    have h2 : d ∈ Subgroup.zpowers (w * d * w⁻¹) := by
      rw [zpowers_conj_eq_of_mem_normalizer hwd]
      exact Subgroup.mem_zpowers d
    exact Item148PtRes.isThreeCentralIn_of_mem_zpowers h1 h2
  have hCF : Subgroup.centralizer (F : Set G) =
      Subgroup.centralizer ({w * c * w⁻¹} : Set G) := by
    rw [hFw, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set QF := Q ⊓ Subgroup.centralizer (F : Set G) with hQF
  have hZF : Z ≤ Subgroup.centralizer (F : Set G) := by
    intro z hz
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := hSb hz.1
    have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := hz.2
    have hle : Subgroup.closure ({b, d} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hzb).symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hzd).symm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hle (hF hx)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hZQF : Z ≤ Subgroup.normalizer (QF : Set G) :=
    Late.le_normalizer_inf ((inf_le_left.trans hSY).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) (hZF.trans Subgroup.le_normalizer)
  have hQF2 : IsPGroup 2 QF :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left
  have hU2 : IsPGroup 2 ↥(Z ⊔ QF) := IsPGroup.to_sup_of_normal_right' hZ2 hQF2 hZQF
  have hAF : A ≤ Subgroup.centralizer (F : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hD.commute (hBA (hF hx)) ha
  have hAQF : A ≤ Subgroup.normalizer (QF : Set G) :=
    Late.le_normalizer_inf (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (hAF.trans Subgroup.le_normalizer)
  have hUc : Z ⊔ QF ≤ Subgroup.centralizer ({w * c * w⁻¹} : Set G) :=
    hCF ▸ sup_le hZF inf_le_right
  have hloc := hZL G A (w * c * w⁻¹) (L.map (MulAut.conj w).toMonoidHom) hRw hJw hΩw d D.mem_d
    D.ne_d hdw (Z ⊔ QF) hUc hU2 (le_normalizer_sup hAZ hAQF)
  have hZU : Z ≤ (Z ⊔ QF) ⊓ Subgroup.centralizer ({d} : Set G) := le_inf le_sup_left inf_le_right
  exact Subgroup.le_centralizer_iff.mpr
    (le_sup_right.trans (Subgroup.le_centralizer_iff.mp (hZU.trans hloc)))

theorem step1523ZY4R_of_res12b'
    (h134 : Item134) (h48 : Sec4.Item4_8) (h152 : Item152R)
    (h1514 : Item1514HJR) (hP : Step1523ZPickY4) (hK : KS1523HJTwo) : Step1523ZY4R :=
  step1523ZY4R_of_res12b h134 h48 hP (step1523ZLoc_of h152 h1514 hK)

end CFSG.RankThree.PartTwo.Sec15
