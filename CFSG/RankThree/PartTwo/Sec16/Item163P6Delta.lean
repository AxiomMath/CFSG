module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
public import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec10.Item107ProofGood
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec5
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

private theorem mem_commutatorInSubgroup_map_conj {P D : Subgroup G} {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) {x : G}
    (hx : x ∈ commutatorInSubgroup P D) :
    g * x * g⁻¹ ∈ commutatorInSubgroup P D := by
  refine mem_commutatorInSubgroup.mpr ⟨?_, fun q hq => ?_⟩
  · exact (Subgroup.normalizer (D : Set G)).mul_mem
      ((Subgroup.normalizer (D : Set G)).mul_mem hgD
        (mem_commutatorInSubgroup.mp hx).1)
      ((Subgroup.normalizer (D : Set G)).inv_mem hgD)
  · have hq' : g⁻¹ * q * g ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (inv_mem hgP : g⁻¹ ∈ Subgroup.normalizer (P : Set G)) q).mp hq
    have hd : ⁅g⁻¹ * q * g, x⁆ ∈ D := (mem_commutatorInSubgroup.mp hx).2 _ hq'
    have hconj : ⁅q, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * q * g, x⁆ * g⁻¹ := by
      rw [conjugate_commutatorElement,
        show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hgD _).mp hd

private theorem map_conj_commutatorInSubgroup {P D : Subgroup G} {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    (commutatorInSubgroup P D).map (MulAut.conj g).toMonoidHom =
      commutatorInSubgroup P D := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact mem_commutatorInSubgroup_map_conj hgP hgD hx
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · simpa using mem_commutatorInSubgroup_map_conj
        (P := P) (D := D) (g := g⁻¹) (inv_mem hgP) (inv_mem hgD) hy
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem normalizer_le_normalizer_pCoreOf_inf_sup (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) ⊓
          (D ⊔ Subgroup.centralizer (D : Set G)) : Subgroup G) : Set G) := by
  have hP : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2
        (Subgroup.normalizer (D : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (D : Set G))
  have hM : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((D ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    (le_inf le_rfl (Sec10.Item107Proof.normalizer_le_normalizer_centralizer (D := D))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup D _)
  exact le_normalizer_inf hP hM

private theorem isPGroup_centralizer_inf_commutatorInSubgroup
    (hG : CFSG.Open.IsCharTwoType G) {D : Subgroup G} (hD1 : D ≠ ⊥)
    (hD2 : IsPGroup 2 D) :
    IsPGroup 2 (Subgroup.centralizer (D : Set G) ⊓
      commutatorInSubgroup (CFSG.Open.pCoreOf 2
        (Subgroup.normalizer (D : Set G))) D : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) with hPdef
  set T := commutatorInSubgroup P D with hTdef
  set St := Subgroup.centralizer (D : Set G) ⊓ T with hStdef
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (D : Set G))
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card St) with
    ⟨k, hk⟩ | ⟨r, hr, hdvd, hodd⟩
  · exact IsPGroup.of_card (p := 2) (n := k) hk
  · haveI : Fact (Nat.Prime r) := ⟨hr⟩
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hzordG : orderOf (z : G) = r := by rw [Subgroup.orderOf_coe, hzord]
    have hzSt : (z : G) ∈ St := z.2
    have hzC : (z : G) ∈ Subgroup.centralizer (D : Set G) :=
      (Subgroup.mem_inf.mp hzSt).1
    have hzT : (z : G) ∈ T := (Subgroup.mem_inf.mp hzSt).2
    have hzN : (z : G) ∈ Subgroup.normalizer (D : Set G) :=
      (mem_commutatorInSubgroup.mp hzT).1
    have hzP : (z : G) ∈ P := by
      have hcomm : ⁅P, Subgroup.zpowers (z : G)⁆ ≤ D := by
        rw [Subgroup.commutator_le]
        intro p hp w hw
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (mem_commutatorInSubgroup.mp (Subgroup.zpow_mem (K := T) hzT j)).2 p hp
      have hzp2 : IsPGroup r (Subgroup.zpowers (z : G)) :=
        IsPGroup.of_card (p := r) (n := 1) (by rw [Nat.card_zpowers, hzordG, pow_one])
      have hcop : ¬ r ∣ Nat.card P := by
        refine CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := r) hP2 hr ?_
        obtain ⟨m, hm⟩ := hodd
        omega
      have hnorm : Subgroup.zpowers (z : G) ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.zpowers_le.mpr
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
            (Subgroup.normalizer (D : Set G)) hzN)
      have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
        r hr (Subgroup.zpowers (z : G)) P hzp2 hcop hnorm
      have hDz : ⁅D, Subgroup.zpowers (z : G)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hcomm : Commute d (z : G) := Subgroup.mem_centralizer_iff.mp hzC d hd
        exact (hcomm.zpow_right j).symm
      have hle : ⁅⁅P, Subgroup.zpowers (z : G)⁆, Subgroup.zpowers (z : G)⁆ ≤
          ⁅D, Subgroup.zpowers (z : G)⁆ :=
        Subgroup.commutator_mono hcomm le_rfl
      rw [hDz] at hle
      have hbot : ⁅P, Subgroup.zpowers (z : G)⁆ = ⊥ := by
        rw [← hidem]
        exact le_bot_iff.mp hle
      have hzCP : (z : G) ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.commutator_comm] at hbot
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
          (Subgroup.mem_zpowers (z : G))
      exact hG (Subgroup.normalizer (D : Set G)) ⟨D, hD1, hD2, rfl⟩ ⟨hzN, hzCP⟩
    have hdvdP : r ∣ Nat.card P := by
      rw [← hzordG]
      exact Subgroup.orderOf_dvd_natCard P hzP
    exfalso
    exact (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := r) hP2 hr (by
      obtain ⟨m, hm⟩ := hodd
      omega)) hdvdP

theorem commutatorInSubgroup_centralizer_le (hG : CFSG.Open.IsCharTwoType G)
    {D : Subgroup G} (hD1 : D ≠ ⊥) (hD2 : IsPGroup 2 D) :
    Subgroup.centralizer (D : Set G) ⊓
      commutatorInSubgroup (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G))) D ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) ⊓
        (D ⊔ Subgroup.centralizer (D : Set G)) := by
  set P := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) with hPdef
  set T := commutatorInSubgroup P D with hTdef
  set St := Subgroup.centralizer (D : Set G) ⊓ T with hStdef
  have hSt2 : IsPGroup 2 St := isPGroup_centralizer_inf_commutatorInSubgroup hG hD1 hD2
  have hStN : St ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    (Subgroup.centralizer_le_normalizer (D : Set G)) (Subgroup.mem_inf.mp hx).1
  have hNSt : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (St : Set G) := by
    have hNT : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (T : Set G) := by
      intro n hn
      exact mem_normalizer_of_map_conj_eq (map_conj_commutatorInSubgroup
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
          (Subgroup.normalizer (D : Set G)) hn) hn)
    exact le_normalizer_inf
      (Sec10.Item107Proof.normalizer_le_normalizer_centralizer (D := D)) hNT
  have hStP : St ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hStN hNSt hSt2
  exact le_inf hStP (inf_le_left.trans le_sup_right)

theorem lt_delta_pCoreOf_inf_sup (hG : CFSG.Open.IsCharTwoType G) (hA : Late.IsE27 A)
    (h1444 : Item1444 A (lB A)) {D H U : Subgroup G} (hD : D ∈ scriptQ A (lB A))
    (hD1 : D ≠ ⊥) (hD2 : IsPGroup 2 D) (hH : IsHyperplane A H)
    (hU : U ∈ scriptQZero A (lB A)) (hU1 : U ≠ ⊥)
    (hUH : U ≤ Subgroup.centralizer (H : Set G))
    (hUD : U ≤ Subgroup.centralizer (D : Set G)) (hUD' : U ⊓ D = ⊥) :
    D < delta A (lB A)
      (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) ⊓
        (D ⊔ Subgroup.centralizer (D : Set G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) with hPdef
  set M := D ⊔ Subgroup.centralizer (D : Set G) with hMdef
  set V := P ⊓ M with hVdef
  set R := delta A (lB A) V with hRdef
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (D : Set G))
  have hP3' : IsPiSubgroup (piCompl 3) P :=
    (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hP2
        Nat.prime_three (by norm_num))
  have hP_ND : P ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (Subgroup.normalizer (D : Set G))
  have hA_ND : A ≤ Subgroup.normalizer (D : Set G) := hD.1.2.2
  have hA_NP : A ≤ Subgroup.normalizer (P : Set G) := hA_ND.trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (D : Set G)))
  have hU_ND : U ≤ Subgroup.normalizer (D : Set G) := hUD.trans
    (Subgroup.centralizer_le_normalizer (D : Set G))
  have hU_NP : U ≤ Subgroup.normalizer (P : Set G) := hU_ND.trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (D : Set G)))
  have hD_P : D ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hD2
  have hD_V : D ≤ V := le_inf hD_P le_sup_left
  have hD_R : D ≤ R := le_delta hD hD_V
  have hcommMem : ∀ h ∈ H, h ≠ 1 →
      ⁅U, P ⊓ Subgroup.centralizer ({h} : Set G)⁆ ∈
        collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({h} : Set G)) := by
    intro h hh hh1
    have hhA : h ∈ A := hH.1 hh
    have hUC : U ≤ Subgroup.centralizer ({h} : Set G) := hUH.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hh))
    have hAhC : A ≤ Subgroup.centralizer ({h} : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hhA))
    have hQ : U ∈ collectionIn (scriptQZero A (lB A))
        (Subgroup.centralizer ({h} : Set G)) := ⟨hU, hUC⟩
    have hS : P ⊓ Subgroup.centralizer ({h} : Set G) ∈
        invariantPiSubgroups (Subgroup.centralizer ({h} : Set G)) (A ⊔ U) (piCompl 3) :=
      ⟨inf_le_right, isPiSubgroup_piCompl_of_le hP3' inf_le_left,
        sup_le (le_normalizer_inf hA_NP (hAhC.trans
            Subgroup.le_normalizer))
          (le_normalizer_inf hU_NP (hUC.trans
            Subgroup.le_normalizer))⟩
    exact h1444 h hhA hh1 U hQ _ hS
  have hcommV : ∀ h ∈ H, h ≠ 1 →
      ⁅U, P ⊓ Subgroup.centralizer ({h} : Set G)⁆ ≤ V := by
    intro h hh hh1
    have hUP : ⁅U, P⁆ ≤ P :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp hU_NP
    have hUC : ⁅U, P⁆ ≤ Subgroup.centralizer (D : Set G) := by
      have hUN : ⁅U, Subgroup.normalizer (D : Set G)⁆ ≤
          Subgroup.centralizer (D : Set G) :=
        CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel.commutator_le_centralizer
          Subgroup.le_normalizer inferInstance
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUD)
      exact (Subgroup.commutator_mono le_rfl hP_ND).trans hUN
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
      (le_inf hUP (hUC.trans le_sup_right))
  have hcommR : ∀ h ∈ H, h ≠ 1 →
      ⁅U, P ⊓ Subgroup.centralizer ({h} : Set G)⁆ ≤ R := fun h hh hh1 =>
    le_delta (hcommMem h hh hh1).1 (hcommV h hh hh1)
  by_cases hβ : ∀ h ∈ H, h ≠ 1 →
      ⁅U, P ⊓ Subgroup.centralizer ({h} : Set G)⁆ ≤ D
  · have hP_le_TU : P ≤ commutatorInSubgroup U D := by
      refine Sec5.le_of_forall_inf_centralizer_le (p := 3) (V := H) (X := P)
        (M := commutatorInSubgroup U D) Nat.prime_three
        (Sec5.isElemAbelian_of_le hA.1 hH.1) ?_ ?_ ?_ ?_
      · have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
        rw [h9]
        have := hH.2
        rw [hA.2] at this
        omega
      · exact hH.1.trans hA_NP
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hP2
            Nat.prime_three (by norm_num))
      · intro v hv hv1 x hx
        refine mem_commutatorInSubgroup.mpr ⟨hP_ND hx.1, fun u hu => ?_⟩
        exact hβ v hv hv1 (Subgroup.commutator_mem_commutator hu hx)
    have hU_le_TP : U ≤ commutatorInSubgroup P D := by
      intro u hu
      refine mem_commutatorInSubgroup.mpr ⟨hU_ND hu, fun p hp => ?_⟩
      have hpD : ⁅u, p⁆ ∈ D := (mem_commutatorInSubgroup.mp (hP_le_TU hp)).2 u hu
      rw [← commutatorElement_inv u p]
      exact D.inv_mem hpD
    have hU_le_V : U ≤ V := (le_inf hUD hU_le_TP).trans
      (commutatorInSubgroup_centralizer_le hG hD1 hD2)
    have hU_le_R : U ≤ R := le_delta hU.1 hU_le_V
    have hne : R ≠ D := by
      intro hRD
      have hUDle : U ≤ D := hRD.symm ▸ hU_le_R
      have hUinf : U ⊓ D = U := inf_eq_left.mpr hUDle
      rw [hUD'] at hUinf
      exact hU1 hUinf.symm
    exact lt_of_le_of_ne hD_R hne.symm
  · push Not at hβ
    obtain ⟨h, hh, hh1, hnot⟩ := hβ
    refine lt_of_le_of_ne hD_R fun hDR => hnot ?_
    exact hDR.symm ▸ hcommR h hh hh1

theorem exists_delta_of_hyperplane (hA : Late.IsE27 A) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hG : CFSG.Open.IsCharTwoType G) {D H U : Subgroup G}
    (hD : D ∈ scriptQ A (lB A)) (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hX : xA A ≤ Subgroup.normalizer (D : Set G)) (hH : IsHyperplane A H)
    (hU : U ∈ scriptQZero A (lB A)) (hU1 : U ≠ ⊥)
    (hUH : U ≤ Subgroup.centralizer (H : Set G))
    (hUD : U ≤ Subgroup.centralizer (D : Set G)) (hUD' : U ⊓ D = ⊥) :
    ∃ R : Subgroup G, R ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧
      xA A ≤ Subgroup.normalizer (R : Set G) ∧ D < R ∧
      R ≤ D ⊔ Subgroup.centralizer (D : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (D : Set G)) with hPdef
  set M := D ⊔ Subgroup.centralizer (D : Set G) with hMdef
  set V := P ⊓ M with hVdef
  set R := delta A (lB A) V with hRdef
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (D : Set G))
  have hP3' : IsPiSubgroup (piCompl 3) P :=
    (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hP2
        Nat.prime_three (by norm_num))
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hD.1.2.2.trans (normalizer_le_normalizer_pCoreOf_inf_sup D)
  have hVmem : V ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_of_le hP3' inf_le_left, hAV⟩
  have hRq : R ∈ scriptQ A (lB A) := delta_mem_scriptQ hA h146 hVmem
  have hRV : R ≤ V := delta_le V
  have hR2 : IsPGroup 2 R := hP2.to_le (hRV.trans inf_le_left)
  have hRpi : R ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hRq, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩
  have hxV : xA A ≤ Subgroup.normalizer (V : Set G) :=
    hX.trans (normalizer_le_normalizer_pCoreOf_inf_sup D)
  have hxR : xA A ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    have hxA : x ∈ Subgroup.normalizer (A : Set G) :=
      (Sec14.pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _) hx
    exact mem_normalizer_of_map_conj_eq (by
      rw [Sec17.HeadProof.map_conj_delta hxA, map_conj_eq_of_mem_normalizer (hxV hx)])
  exact ⟨R, hRpi, hxR, lt_delta_pCoreOf_inf_sup hG hA h1444 hD hD1 hD2 hH
    hU hU1 hUH hUD hUD', hRV.trans inf_le_right⟩

namespace Conf685

variable {c : G} {L Y S : Subgroup G}

theorem exists_delta (h : Conf685 A c L Y S)
    (hX : xA A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) {H U : Subgroup G}
    (hH : IsHyperplane A H) (hU : U ∈ scriptQZero A (lB A)) (hU1 : U ≠ ⊥)
    (hUH : U ≤ Subgroup.centralizer (H : Set G))
    (hUD : U ≤ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G))
    (hUD' : U ⊓ (S ⊓ L) = ⊥) :
    ∃ R : Subgroup G, R ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧
      xA A ≤ Subgroup.normalizer (R : Set G) ∧ S ⊓ L < R ∧
      R ≤ (S ⊓ L) ⊔ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := by
  have hA : Late.IsE27 A := isE27_of_mem_partTwoE h.sec15R.toSec13Data.mem_partTwoE
  have hDpi : S ⊓ L ∈ scriptQPi A (lB A) L (piOf 2) := h.mem_d.prop
  exact exists_delta_of_hyperplane hA h.item1444 h.item146 h.sec15R.charTwoType
    hDpi.1.1 (isPiSubgroup_piOf_iff Nat.prime_two _ |>.mp hDpi.2) h.d_ne_bot hX hH
    hU hU1 hUH hUD hUD'

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6
