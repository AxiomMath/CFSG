module

public import CFSG.GroupTheory.PElementCommutator
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyCentral
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.OddCentral
import CFSG.GH74.Uniqueness.Section4Residual
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Q S : Type} [Group Q] [Group S] [Finite Q] [Finite S]

omit [Finite S] in
private theorem map_opp_comap {ρ : Q →* S} (hρ : Function.Surjective ρ) (L : Subgroup S) :
    (Opp 2 (L.comap ρ)).map ρ = Opp 2 L := by
  unfold Opp
  rw [s13_pElementSubgroup_map Nat.prime_two,
    Subgroup.map_comap_eq_self_of_surjective hρ]

private theorem lift_pCoreOf_map {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) {P : Subgroup Q} (hP : ρ.ker ≤ P) :
    (pCoreOf 2 P).map ρ = pCoreOf 2 (P.map ρ) := by
  set Obar := pCoreOf 2 (P.map ρ)
  set R := Obar.comap ρ
  have hRP : R ≤ P :=
    (Subgroup.comap_mono (pCoreOf_le 2 (P.map ρ))).trans_eq (Subgroup.comap_map_eq_self hP)
  have hRnil : Group.IsNilpotent ↥R :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.isNilpotent_comap ρ hZ
      (pCoreOf_isPGroup 2 (P.map ρ))
  have hOppR : Opp 2 R ≤ pCoreOf 2 R := by
    unfold Opp
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, k, hk⟩
    have hpow : x ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    exact CFSG.Quasithin.F6.mem_pCoreOf_of_isNilpotent hxR hpow
  have hRnorm : P ≤ normalizer (R : Set Q) := fun p hp =>
    Subgroup.le_normalizer_comap ρ (Subgroup.mem_comap.mpr
      (le_normalizer_pCoreOf 2 (P.map ρ) (Subgroup.mem_map_of_mem ρ hp)))
  have hcoreR : pCoreOf 2 R ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le 2 R |>.trans hRP)
      (hRnorm.trans (normalizer_le_normalizer_pCoreOf 2 R)) (pCoreOf_isPGroup 2 R)
  have hObar : Obar ≤ Opp 2 Obar := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (P.map ρ)) ⟨x, hx⟩
    exact Subgroup.subset_closure ⟨hx, ⟨k, (Subgroup.orderOf_coe _).trans hk⟩⟩
  have hRmap : R.map ρ = Obar := Subgroup.map_comap_eq_self_of_surjective hρ Obar
  refine le_antisymm ?_ ?_
  · refine le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono (pCoreOf_le 2 P)) ?_
      (pCoreOf_isPGroup 2 P |>.map ρ)
    exact (Subgroup.map_mono (le_normalizer_pCoreOf 2 P)).trans (Subgroup.le_normalizer_map ρ)
  · calc Obar = Opp 2 Obar := le_antisymm hObar (close16_opp_le 2 Obar)
      _ = Opp 2 (R.map ρ) := (congrArg (Opp 2) hRmap).symm
      _ = (Opp 2 R).map ρ := by
          rw [hRmap]
          exact (map_opp_comap hρ Obar).symm
      _ ≤ (pCoreOf 2 P).map ρ := Subgroup.map_mono (hOppR.trans hcoreR)

private theorem lift_map_sup {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) {P : Subgroup Q} (hP : ρ.ker ≤ P) {L : Subgroup S}
    (hEq : L = Opp 2 L ⊔ pCoreOf 2 (P.map ρ)) :
    (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P).map ρ = L := by
  rw [Subgroup.map_sup, map_opp_comap hρ, lift_pCoreOf_map hρ hZ hP]
  exact hEq.symm

omit [Finite S] in
private theorem lift_opp_self {ρ : Q →* S} {P : Subgroup Q} {L : Subgroup S} :
    Opp 2 (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P) = Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P := by
  refine le_antisymm (close16_opp_le 2 _) ?_
  refine sup_le ?_ ?_
  · have h : CFSG.RankThree.PartOne.pElementSubgroup 2 (Opp 2 (L.comap ρ)) ≤
        CFSG.RankThree.PartOne.pElementSubgroup 2 (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P) :=
      s13_Thirteen2_pElementSubgroup_mono (p := 2)
        (X := Opp 2 (L.comap ρ)) (Y := Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P) le_sup_left
    change Opp 2 (Opp 2 (L.comap ρ)) ≤ Opp 2 (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P) at h
    rwa [close16_opp_idem] at h
  · exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two (pCoreOf_isPGroup 2 P) le_sup_right

omit [Finite S] in
private theorem lift_normal {ρ : Q →* S} {P : Subgroup Q} {L : Subgroup S}
    (hP : ρ.ker ≤ P) (hLe : L ≤ P.map ρ) (hN : (L.subgroupOf (P.map ρ)).Normal) :
    ((Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P).subgroupOf P).Normal := by
  have hLnorm : P.map ρ ≤ normalizer (L : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLe).mp hN
  have hle : Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P ≤ P :=
    sup_le ((close16_opp_le 2 _).trans ((Subgroup.comap_mono hLe).trans_eq
      (Subgroup.comap_map_eq_self hP))) (pCoreOf_le 2 P)
  have hcomap : P ≤ normalizer ((L.comap ρ : Subgroup Q) : Set Q) := fun p hp =>
    Subgroup.le_normalizer_comap ρ
      (Subgroup.mem_comap.mpr (hLnorm (Subgroup.mem_map_of_mem ρ hp)))
  have hA : P ≤ normalizer ((Opp 2 (L.comap ρ) : Subgroup Q) : Set Q) := fun p hp =>
    close16_mem_normalizer_opp 2 (hcomap hp)
  have hO : P ≤ normalizer ((pCoreOf 2 P : Subgroup Q) : Set Q) := le_normalizer_pCoreOf 2 P
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    ((le_inf hA hO).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _))

private theorem lift_commutator_le {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {A B : Subgroup Q} {A' B' : Subgroup S}
    (hA : A = Opp 2 A ⊔ pCoreOf 2 P) (hAle : A ≤ P) (hBle : B ≤ P)
    (hA' : A.map ρ = A') (hB' : B.map ρ = B')
    (hcomm : ⁅A', B'⁆ ≤ pCoreOf 2 (P.map ρ)) : ⁅A, B⁆ ≤ pCoreOf 2 P := by
  have hOmap := lift_pCoreOf_map hρ hZ hP
  have hcomap : (pCoreOf 2 (P.map ρ)).comap ρ = pCoreOf 2 P ⊔ ρ.ker := by
    rw [← hOmap, Subgroup.comap_map_eq]
  have hle : ⁅A, B⁆ ≤ pCoreOf 2 P ⊔ ρ.ker := by
    rw [← hcomap]
    refine Subgroup.map_le_iff_le_comap.mp ?_
    rw [Subgroup.map_commutator, hA', hB']
    exact hcomm
  exact CFSG.GroupTheory.commutator_le_of_le_sup_of_le_center hA
    (hAle.trans (le_normalizer_pCoreOf 2 P)) (hBle.trans (le_normalizer_pCoreOf 2 P))
    hZ hZodd hle

omit [Finite Q] [Finite S] in
private theorem mem_of_map_mem_of_pow_two {ρ : Q →* S} (hZ : ρ.ker ≤ center Q)
    (hZodd : Odd (Nat.card ρ.ker)) {W : Subgroup Q} {t : Q} {k : ℕ}
    (ht : t ^ 2 ^ k = 1) (htW : ρ t ∈ W.map ρ) : t ∈ W := by
  have hmem : t ∈ W ⊔ ρ.ker := by
    rw [← Subgroup.comap_map_eq (f := ρ) W]
    exact htW
  refine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.mem_of_sup_central hZ ?_ hmem k ht
  intro x hx
  refine hZodd.of_dvd_nat ?_
  simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard (⟨x, hx⟩ : ρ.ker)

omit [Finite Q] in
private theorem opp_le_iff {X P : Subgroup Q} :
    Opp 2 P ≤ X ↔ {t : Q | t ∈ P ∧ ∃ k, orderOf t = 2 ^ k} ⊆ X := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact Subgroup.closure_le X

private theorem opp_le_iSup_lift {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) :
    Opp 2 P ≤ ⨆ i, (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) := by
  refine opp_le_iff.mpr ?_
  rintro t ⟨htP, k, hk⟩
  have hmapLi : ∀ i, (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P).map ρ = L i := fun i =>
    lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  refine mem_of_map_mem_of_pow_two hZ hZodd (k := k) (by rw [← hk]; exact pow_orderOf_eq_one t) ?_
  rw [Subgroup.map_iSup]
  have hmem : ρ t ∈ ⨆ i, L i := by
    rw [hL.iSup_eq]
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem ρ htP, ?_⟩)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ orderOf_map_dvd ρ t)
    exact ⟨j, hj⟩
  simpa only [hmapLi] using hmem

private theorem lift_iSup_eq {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) :
    (⨆ i, (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)) =
      Opp 2 P ⊔ pCoreOf 2 P := by
  have hmapLi : ∀ i, (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P).map ρ = L i := fun i =>
    lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => ?_
    have h1 : Opp 2 ((L i).comap ρ) ≤ Opp 2 P :=
      s13_Thirteen2_pElementSubgroup_mono (p := 2) (X := (L i).comap ρ) (Y := P)
        ((Subgroup.comap_mono (hL.le i)).trans (le_of_eq (Subgroup.comap_map_eq_self hP)))
    exact sup_le (h1.trans le_sup_left) le_sup_right
  · refine sup_le ?_ ?_
    · exact opp_le_iSup_lift hρ hZ hZodd hP hL
    · intro x hx
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 P) ⟨x, hx⟩
      refine mem_of_map_mem_of_pow_two hZ hZodd (k := k) ?_ ?_
      · have hxord : orderOf x = 2 ^ k :=
          (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(pCoreOf 2 P))).trans hk
        rw [← hxord]
        exact pow_orderOf_eq_one x
      · rw [Subgroup.map_iSup]
        have hmem : ρ x ∈ ⨆ i, L i := by
          rw [hL.iSup_eq]
          exact Subgroup.mem_sup_right ((lift_pCoreOf_map hρ hZ hP) ▸
            Subgroup.mem_map_of_mem ρ hx)
        simpa only [hmapLi] using hmem

private theorem closure_pow_two_eq_closure_orderOf (Y : Type) [Group Y] :
    Subgroup.closure {y : Y | ∃ k, y ^ 2 ^ k = 1} =
      Subgroup.closure {y : Y | ∃ k, orderOf y = 2 ^ k} := by
  congr 1
  ext y
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_iff_pow_eq_one.mpr hk)
    exact ⟨j, hj⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one y⟩

private theorem isPGroup_two_of_central_kernel {Y P : Type} [Group Y] [Finite Y] [Group P]
    [Finite P]
    (f : Y →* P) (hker : f.ker ≤ center Y) (hP : IsPGroup 2 P)
    (hgen : Subgroup.closure {y : Y | ∃ k, orderOf y = 2 ^ k} = ⊤) : IsPGroup 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have : Group.IsNilpotent Y := Subgroup.isNilpotent_of_ker_le_center f hker
  have h : IsPGroup 2 (Subgroup.closure {y : Y | ∃ k, y ^ 2 ^ k = 1}) :=
    CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (p := 2)
      (S := {y : Y | ∃ k, y ^ 2 ^ k = 1}) fun s hs => hs
  rw [closure_pow_two_eq_closure_orderOf, hgen] at h
  exact h.of_equiv Subgroup.topEquiv

private theorem opp_top_eq_top_of_opp_eq {H : Subgroup Q} (hH : Opp 2 H = H) :
    Opp 2 (⊤ : Subgroup ↥H) = ⊤ := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  apply Subgroup.map_injective H.subtype_injective
  change (CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup ↥H)).map H.subtype =
    Subgroup.map H.subtype ⊤
  rw [s13_pElementSubgroup_map Nat.prime_two H.subtype, htop]
  exact hH

private theorem opp_top_eq_top_of_surjective {H Y : Type} [Group H] [Finite H] [Group Y]
    (f : H →* Y) (hf : Function.Surjective f) (hH : Opp 2 (⊤ : Subgroup H) = ⊤) :
    Opp 2 (⊤ : Subgroup Y) = ⊤ := by
  have h := s13_pElementSubgroup_map Nat.prime_two f (⊤ : Subgroup H)
  change CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup H) = ⊤ at hH
  rw [hH, Subgroup.map_top_of_surjective f hf] at h
  exact h.symm

private theorem map_le_center_quotient {Y : Type} [Group Y] {N Z : Subgroup Y} [N.Normal]
    (hZ : Z ≤ center Y) : Z.map (QuotientGroup.mk' N) ≤ center (Y ⧸ N) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N w
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz) w]

private theorem lift_tits_up {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) (i : Fin d) (N : Subgroup Q)
    (hON : pCoreOf 2 P ≤ N) (hNL : N ≤ Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)
    (hNnorm : (N.subgroupOf (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)).Normal)
    (hcomm : ¬ ⁅N, Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P⁆ ≤ pCoreOf 2 P) :
    S17.oUpperTwo (L i) ≤ N.map ρ := by
  have hOmap := lift_pCoreOf_map hρ hZ hP
  have hmapLi : (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P).map ρ = L i :=
    lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hOle : pCoreOf 2 (P.map ρ) ≤ N.map ρ := by
    rw [← hOmap]
    exact Subgroup.map_mono hON
  have hNle : N.map ρ ≤ L i := by
    rw [← hmapLi]
    exact Subgroup.map_mono hNL
  have hNnormS : ((N.map ρ).subgroupOf (L i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNle]
    have h1 : Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P ≤ normalizer (N : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hNnorm
    have h2 : (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P).map ρ ≤
        normalizer ((N.map ρ : Subgroup S) : Set S) :=
      (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map ρ)
    rwa [Subgroup.map_sup, map_opp_comap hρ, hOmap, ← hL.eq_opp_sup i] at h2
  have hnot : ¬ ⁅N.map ρ, L i⁆ ≤ pCoreOf 2 (P.map ρ) := by
    intro hc
    apply hcomm
    have hmapcomm : (⁅N, Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P⁆).map ρ =
        ⁅N.map ρ, L i⁆ := by
      rw [Subgroup.map_commutator, hmapLi]
    have hle' : ⁅N, Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P⁆ ≤
        (pCoreOf 2 (P.map ρ)).comap ρ := by
      rw [← Subgroup.map_le_iff_le_comap, hmapcomm]
      exact hc
    have hcomap : (pCoreOf 2 (P.map ρ)).comap ρ = pCoreOf 2 P ⊔ ρ.ker := by
      rw [← hOmap, Subgroup.comap_map_eq]
    rw [hcomap, Subgroup.commutator_comm] at hle'
    have hAeq : Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P =
        Opp 2 (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) ⊔ pCoreOf 2 P := by
      rw [lift_opp_self (ρ := ρ) (P := P) (L := L i)]
      exact (sup_eq_left.mpr le_sup_right).symm
    have hleP : Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P ≤ P :=
      sup_le ((close16_opp_le 2 _).trans
        ((Subgroup.comap_mono (hL.le i)).trans (le_of_eq (Subgroup.comap_map_eq_self hP))))
        (pCoreOf_le 2 P)
    have hAN : ⁅Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P, N⁆ ≤ pCoreOf 2 P :=
      CFSG.GroupTheory.commutator_le_of_le_sup_of_le_center hAeq
        (hleP.trans (le_normalizer_pCoreOf 2 P))
        ((hNL.trans hleP).trans (le_normalizer_pCoreOf 2 P)) hZ hZodd hle'
    rw [Subgroup.commutator_comm] at hAN
    exact hAN
  exact hL.tits i (N.map ρ) hOle hNle hNnormS hnot

private theorem closure_two_bar2_eq_top {N : Subgroup Q} (hN : Opp 2 N = N) :
    Subgroup.closure {y : Bar2 N | ∃ k, orderOf y = 2 ^ k} = ⊤ := by
  have h := opp_top_eq_top_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥N))
    (QuotientGroup.mk'_surjective _) (opp_top_eq_top_of_opp_eq hN)
  simpa only [Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.mem_top, true_and] using h

omit [Finite Q] [Finite S] in
private theorem lift_quotient_map_ker {ρ : Q →* S} {P : Subgroup Q} {L : Subgroup S}
    (hmapLi : (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P).map ρ = L) (N : Subgroup Q)
    (hNL : N ≤ Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P)
    (hNnorm : (N.subgroupOf (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P)).Normal)
    (hMbar : ((N.map ρ).subgroupOf L).Normal) :
    ∃ f : (↥(Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P) ⧸
        N.subgroupOf (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P)) →*
        (↥L ⧸ (N.map ρ).subgroupOf L),
      f.ker ≤ ((ρ.ker ⊓ (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P)).subgroupOf
          (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P)).map
        (QuotientGroup.mk' (N.subgroupOf (Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P))) := by
  set Li := Opp 2 (L.comap ρ) ⊔ pCoreOf 2 P with hLidef
  set Nsub : Subgroup ↥Li := N.subgroupOf Li with hNsubdef
  set Nbar : Subgroup S := N.map ρ with hNbardef
  set Mbar : Subgroup ↥L := Nbar.subgroupOf L with hMbardef
  have hNbar_le : Nbar ≤ L := by
    change Subgroup.map ρ N ≤ L
    rw [← hmapLi]
    exact Subgroup.map_mono hNL
  have hMbar_norm : Mbar.Normal := hMbar
  have : Mbar.Normal := hMbar_norm
  let φ : ↥Li →* ↥L := (ρ.comp Li.subtype).codRestrict L fun x =>
    hmapLi ▸ Subgroup.mem_map_of_mem ρ x.2
  let ψ : ↥Li →* (↥L ⧸ Mbar) := (QuotientGroup.mk' Mbar).comp φ
  have hker_le : Nsub ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine (QuotientGroup.eq_one_iff (N := Mbar) (x := φ x)).mpr ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    change ρ (x : Q) ∈ N.map ρ
    exact Subgroup.mem_map_of_mem ρ hx
  let f : (↥Li ⧸ Nsub) →* (↥L ⧸ Mbar) := QuotientGroup.lift Nsub ψ hker_le
  refine ⟨f, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Nsub y
  have h1 : (QuotientGroup.mk' Mbar) (φ x) = 1 := by
    have h2 : f (QuotientGroup.mk' Nsub x) = 1 := hy
    rwa [show f (QuotientGroup.mk' Nsub x) = (QuotientGroup.mk' Mbar) (φ x) from
      QuotientGroup.lift_mk' Nsub (φ := ψ) hker_le x] at h2
  have hφx : φ x ∈ Mbar := (QuotientGroup.eq_one_iff _).mp h1
  have hρx : ρ (x : Q) ∈ Nbar := by
    simpa [φ] using Subgroup.mem_subgroupOf.mp hφx
  obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hρx
  have hzker : ρ ((x : Q) * n⁻¹) = 1 := by rw [map_mul, map_inv, hρn, mul_inv_cancel]
  have hnLi : n ∈ Li := hNL hn
  have hzLi : (x : Q) * n⁻¹ ∈ Li := Li.mul_mem x.2 (Li.inv_mem hnLi)
  refine ⟨⟨_, hzLi⟩, Subgroup.mem_subgroupOf.mpr ⟨hzker, hzLi⟩, ?_⟩
  have hnk : (QuotientGroup.mk' Nsub) (⟨n, hnLi⟩ : ↥Li) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
  have h1 : (⟨(x : Q) * n⁻¹, hzLi⟩ : ↥Li) = x * (⟨n, hnLi⟩ : ↥Li)⁻¹ := Subtype.ext rfl
  rw [h1, map_mul, map_inv, hnk, inv_one, mul_one]

private theorem isPGroup_two_quotient_of_oUpperTwo_le {L N : Subgroup S}
    [(N.subgroupOf L).Normal] (hup : S17.oUpperTwo L ≤ N) :
    IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
  have : ((S17.oUpperTwo L).subgroupOf L).Normal :=
    CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf L
  have h1 : IsPGroup 2 (↥L ⧸ (S17.oUpperTwo L).subgroupOf L) := by
    obtain ⟨k, hk⟩ := CFSG.GroupTheory.index_oddOrderClosure_eq_two_pow L
    exact IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card]; exact hk)
  have hle : (S17.oUpperTwo L).subgroupOf L ≤ N.subgroupOf L := Subgroup.subgroupOf_mono L hup
  let q : (↥L ⧸ (S17.oUpperTwo L).subgroupOf L) →* (↥L ⧸ N.subgroupOf L) :=
    QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using hle)
  refine IsPGroup.of_surjective h1 q ?_
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) y
  refine ⟨QuotientGroup.mk' _ z, ?_⟩
  show (QuotientGroup.map _ _ (MonoidHom.id (↥L)) _)
    (QuotientGroup.mk' ((S17.oUpperTwo L).subgroupOf L) z) = QuotientGroup.mk' (N.subgroupOf L) z
  exact QuotientGroup.map_mk _ _ (MonoidHom.id (↥L)) _ z

private theorem lift_quotient_two {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) {P : Subgroup Q} (hP : ρ.ker ≤ P)
    {d : ℕ} {L : Fin d → Subgroup S} (hL : IsLeviFamily (P.map ρ) d L) (i : Fin d)
    (N : Subgroup Q) (hNL : N ≤ Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)
    (hNnorm : (N.subgroupOf (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)).Normal)
    (hup : S17.oUpperTwo (L i) ≤ N.map ρ) :
    IsPGroup 2 (↥(Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) ⧸
      N.subgroupOf (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)) := by
  set Li := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P with hLidef
  set Nsub : Subgroup ↥Li := N.subgroupOf Li with hNsubdef
  have hmapLi : Li.map ρ = L i := lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hNbar_norm : ((N.map ρ).subgroupOf (L i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((Subgroup.map_mono hNL).trans_eq hmapLi)]
    have h1 : Li ≤ normalizer (N : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hNnorm
    have h2 : Li.map ρ ≤ normalizer ((N.map ρ : Subgroup S) : Set S) :=
      (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map ρ)
    rwa [hmapLi] at h2
  obtain ⟨f, hfker⟩ := lift_quotient_map_ker hmapLi N hNL hNnorm hNbar_norm
  have hZc : (ρ.ker ⊓ Li).subgroupOf Li ≤ center ↥Li := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz).1) (y : Q)
  have hfker' : f.ker ≤ center (↥Li ⧸ Nsub) :=
    hfker.trans (map_le_center_quotient hZc)
  have hPgroup : IsPGroup 2 (↥(L i) ⧸ (N.map ρ).subgroupOf (L i)) :=
    isPGroup_two_quotient_of_oUpperTwo_le hup
  have hLi_opp : Opp 2 Li = Li := by
    refine le_antisymm (close16_opp_le 2 Li) ?_
    refine sup_le ?_ ?_
    · have h : CFSG.RankThree.PartOne.pElementSubgroup 2 (Opp 2 ((L i).comap ρ)) ≤
          CFSG.RankThree.PartOne.pElementSubgroup 2 Li :=
        s13_Thirteen2_pElementSubgroup_mono (p := 2)
          (X := Opp 2 ((L i).comap ρ))
          (Y := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) le_sup_left
      change Opp 2 (Opp 2 ((L i).comap ρ)) ≤ Opp 2 Li at h
      rwa [close16_opp_idem] at h
    · exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two (pCoreOf_isPGroup 2 P) le_sup_right
  have hgen : Subgroup.closure {y : ↥Li ⧸ Nsub | ∃ k, orderOf y = 2 ^ k} = ⊤ := by
    have h := opp_top_eq_top_of_surjective (QuotientGroup.mk' Nsub)
      (QuotientGroup.mk'_surjective Nsub) (opp_top_eq_top_of_opp_eq hLi_opp)
    simpa only [Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.mem_top, true_and] using h
  exact isPGroup_two_of_central_kernel f hfker' hPgroup hgen

private theorem lift_tits {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) (i : Fin d) (N : Subgroup Q)
    (hON : pCoreOf 2 P ≤ N) (hNL : N ≤ Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)
    (hNnorm : (N.subgroupOf (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)).Normal)
    (hcomm : ¬ ⁅N, Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P⁆ ≤ pCoreOf 2 P) :
    S17.oUpperTwo (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) ≤ N := by
  set Li := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P with hLidef
  have hup := lift_tits_up hρ hZ hZodd hP hL i N hON hNL hNnorm hcomm
  have hYtwo : IsPGroup 2 (↥Li ⧸ N.subgroupOf Li) :=
    lift_quotient_two hρ hZ hP hL i N hNL hNnorm hup
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨huLi, huodd⟩
  set x : ↥Li := ⟨u, huLi⟩ with hxdef
  have hxodd : Odd (orderOf ((QuotientGroup.mk' (N.subgroupOf Li)) x)) := by
    have hdvd : orderOf ((QuotientGroup.mk' (N.subgroupOf Li)) (⟨u, huLi⟩ : ↥Li)) ∣
        orderOf u := by
      simpa using orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf Li)) (⟨u, huLi⟩ : ↥Li)
    exact huodd.of_dvd_nat hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hYtwo ((QuotientGroup.mk' (N.subgroupOf Li)) x)
  have hx1 : (QuotientGroup.mk' (N.subgroupOf Li)) x = 1 := by
    have h1 : orderOf ((QuotientGroup.mk' (N.subgroupOf Li)) x) = 1 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0] at hk
        simpa using hk
      · exfalso
        have h2 : 2 ∣ orderOf ((QuotientGroup.mk' (N.subgroupOf Li)) x) := by
          rw [hk]
          exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
        exact (Nat.not_even_iff_odd.mpr hxodd) (even_iff_two_dvd.mpr h2)
    exact orderOf_eq_one_iff.mp h1
  exact (QuotientGroup.eq_one_iff (x := x)).mp hx1

theorem IsLeviFamily.lift_of_le_center {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q} (hP : ρ.ker ≤ P)
    {d : ℕ} {L : Fin d → Subgroup S} (hL : IsLeviFamily (P.map ρ) d L) :
    IsLeviFamily P d (fun i => Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) := by
  have hmapLi : ∀ i, (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P).map ρ = L i := fun i =>
    lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hle : ∀ i, Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P ≤ P := fun i => by
    have h1 : Opp 2 ((L i).comap ρ) ≤ P :=
      (close16_opp_le 2 _).trans
        ((Subgroup.comap_mono (hL.le i)).trans (le_of_eq (Subgroup.comap_map_eq_self hP)))
    exact sup_le h1 (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hopp : ∀ i, Opp 2 (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) =
      Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P := fun i =>
    lift_opp_self (ρ := ρ) (P := P) (L := L i)
  refine
    { pCoreOf_le := fun i => le_sup_right
      le := hle
      normal := fun i => lift_normal hP (hL.le i) (hL.normal i)
      eq_opp_sup := ?_
      ne := ?_
      commutator_le := ?_
      iSup_eq := lift_iSup_eq hρ hZ hZodd hP hL
      tits := fun i N hON hNL hNnorm hcomm =>
        lift_tits hρ hZ hZodd hP hL i N hON hNL hNnorm hcomm }
  · intro i
    rw [hopp i, sup_eq_left.mpr le_sup_right]
  · intro i h
    exact hL.ne i (by rw [← hmapLi i, h, lift_pCoreOf_map hρ hZ hP])
  · intro i j hij
    exact lift_commutator_le hρ hZ hZodd hP (by rw [hopp i, sup_eq_left.mpr le_sup_right])
      (hle i) (hle j) (hmapLi i) (hmapLi j) (hL.commutator_le i j hij)

private theorem eq_one_of_orderOf_eq_two_pow_of_odd {Y : Type} [Group Y] {x : Y} {k : ℕ}
    (hodd : Odd (orderOf x)) (hk : orderOf x = 2 ^ k) : x = 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      (hk ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)))

private theorem transfer_apply_eq_one_of_odd {T : Type} [Group T] [Finite T]
    {N : Subgroup T} [N.Normal] [N.FiniteIndex]
    (hgen : Subgroup.closure {x : T | ∃ k, orderOf x = 2 ^ k} = ⊤)
    (hquot : IsPGroup 2 (T ⧸ N))
    {A : Type} [CommGroup A] (hodd : Odd (Nat.card A))
    (φ : N →* A) {z : N} (hz : (z : T) ∈ Subgroup.center T) : φ z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : ∀ x : T, (∃ k, orderOf x = 2 ^ k) → MonoidHom.transfer φ x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    have hdvd : orderOf (MonoidHom.transfer φ x) ∣ 2 ^ k := by
      rw [← hk]
      exact orderOf_map_dvd _ x
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact eq_one_of_orderOf_eq_two_pow_of_odd
      (hodd.of_dvd_nat (orderOf_dvd_natCard (MonoidHom.transfer φ x))) hj
  have htriv : MonoidHom.transfer φ (z : T) = 1 := by
    have hle : Subgroup.closure {x : T | ∃ k, orderOf x = 2 ^ k} ≤
        (MonoidHom.transfer φ).ker := by
      rw [Subgroup.closure_le]
      exact fun x hx => MonoidHom.mem_ker.mpr (hV x hx)
    rw [hgen] at hle
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _))
  have hkey : ∀ (k : ℕ) (g₀ : T), g₀⁻¹ * (z : T) ^ k * g₀ ∈ N →
      g₀⁻¹ * (z : T) ^ k * g₀ = (z : T) ^ k := by
    intro k g₀ _
    have hzpow : (z : T) ^ k ∈ Subgroup.center T := Subgroup.pow_mem (Subgroup.center T) hz k
    rw [Subgroup.mem_center_iff.mp hzpow g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hcast : (z ^ N.index : N) = ⟨(z : T) ^ N.index,
      MonoidHom.transfer_eq_pow_aux (z : T) hkey⟩ :=
    Subtype.ext (Subgroup.coe_pow N z N.index)
  rw [MonoidHom.transfer_eq_pow φ (z : T) hkey] at htriv
  have hpow : φ z ^ N.index = 1 := by
    rw [← map_pow]
    rwa [hcast]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2) (G := T ⧸ N)).mp hquot
  have hidx : N.index = 2 ^ j := by rw [Subgroup.index_eq_card, hj]
  have hdvd : orderOf (φ z) ∣ 2 ^ j := by
    rw [← hidx]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact eq_one_of_orderOf_eq_two_pow_of_odd
    (hodd.of_dvd_nat (orderOf_dvd_natCard (φ z))) hi

omit [Finite Q] [Finite S] in
private theorem bar2_quot_mem_ker_image {ρ : Q →* S} {N : Subgroup Q} {Nbar : Subgroup S}
    (hPc_map : (pCoreOf 2 N).map ρ = pCoreOf 2 Nbar)
    {x : ↥N} (hx : ρ (x : Q) ∈ pCoreOf 2 Nbar) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) x ∈
      ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) := by
  have hx' : ρ (x : Q) ∈ (pCoreOf 2 N).map ρ := by rwa [hPc_map]
  obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hx'
  have hnN : n ∈ N := pCoreOf_le 2 N hn
  have hzker : ρ ((x : Q) * n⁻¹) = 1 := by rw [map_mul, map_inv, hρn, mul_inv_cancel]
  have hzN : (x : Q) * n⁻¹ ∈ N := N.mul_mem x.2 (N.inv_mem hnN)
  refine Subgroup.mem_map.mpr ⟨⟨_, hzN⟩, Subgroup.mem_subgroupOf.mpr ⟨hzker, hzN⟩, ?_⟩
  have hnk : (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) (⟨n, hnN⟩ : ↥N) = 1 := by
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [← CFSG.openPCoreOf_subgroupOf 2 N]
    exact Subgroup.mem_subgroupOf.mpr hn
  have h1 : (⟨(x : Q) * n⁻¹, hzN⟩ : ↥N) = x * (⟨n, hnN⟩ : ↥N)⁻¹ := Subtype.ext rfl
  rw [h1, map_mul, map_inv, hnk, inv_one, mul_one]

private theorem bar2_map_pCore {ρ : Q →* S} (hZ : ρ.ker ≤ center Q)
    (hZodd : Odd (Nat.card ρ.ker)) {N : Subgroup Q} {Nbar : Subgroup S}
    (hmap : N.map ρ = Nbar) :
    (pCoreOf 2 N).map ρ = pCoreOf 2 Nbar := by
  let φ : ↥N →* ↥Nbar := (ρ.comp N.subtype).codRestrict Nbar fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ x.2
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : S) ∈ N.map ρ := hmap ▸ y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφker : φ.ker ≤ center ↥N := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxker : (x : Q) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg (fun z : ↥Nbar => (z : S)) (MonoidHom.mem_ker.mp hx)
    exact Subgroup.mem_center_iff.mp (hZ hxker) (y : Q)
  have hφodd : Odd (Nat.card φ.ker) := by
    have hker_eq : φ.ker = (ρ.ker ⊓ N).subgroupOf N := by
      ext x
      constructor
      · intro hx
        rw [MonoidHom.mem_ker] at hx
        refine Subgroup.mem_subgroupOf.mpr ⟨MonoidHom.mem_ker.mpr ?_, x.2⟩
        exact congrArg (fun z : ↥Nbar => (z : S)) hx
      · intro hx
        rw [MonoidHom.mem_ker]
        have hxker : (x : Q) ∈ ρ.ker := (Subgroup.mem_subgroupOf.mp hx).1
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hxker
    rw [hker_eq]
    rw [← Subgroup.card_subtype N ((ρ.ker ⊓ N).subgroupOf N),
      Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    exact hZodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hPc : CFSG.pCore 2 ↥Nbar = (CFSG.pCore 2 ↥N).map φ :=
    CFSG.RankThree.Theta.TwoPlane.pCore_two_eq_map_of_central_kernel φ hφsurj hφker hφodd
  have hPc_map : (pCoreOf 2 N).map ρ = pCoreOf 2 Nbar := by
    have hcomp : Nbar.subtype.comp φ = ρ.comp N.subtype := MonoidHom.ext fun _ => rfl
    rw [CFSG.openPCoreOf_eq_map_pCore, CFSG.openPCoreOf_eq_map_pCore]
    calc ((CFSG.pCore 2 ↥N).map N.subtype).map ρ
        = (CFSG.pCore 2 ↥N).map (ρ.comp N.subtype) := by rw [Subgroup.map_map]
      _ = (CFSG.pCore 2 ↥N).map (Nbar.subtype.comp φ) := by rw [hcomp]
      _ = ((CFSG.pCore 2 ↥N).map φ).map Nbar.subtype := by rw [Subgroup.map_map]
      _ = (CFSG.pCore 2 ↥Nbar).map Nbar.subtype := by rw [← hPc]
  exact hPc_map

omit [Finite Q] [Finite S] in
private theorem bar2_map_data {ρ : Q →* S} {N : Subgroup Q} {Nbar : Subgroup S}
    (hPc_map : (pCoreOf 2 N).map ρ = pCoreOf 2 Nbar) (hmap : N.map ρ = Nbar) :
    ∃ f : Bar2 N →* Bar2 Nbar, Function.Surjective f ∧
      f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) := by
  let φ : ↥N →* ↥Nbar := (ρ.comp N.subtype).codRestrict Nbar fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ x.2
  let ψ : ↥N →* Bar2 Nbar := (QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar)).comp φ
  have hle : CFSG.pCore 2 ↥N ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxN : (x : Q) ∈ pCoreOf 2 N := by
      have hx' : x ∈ (pCoreOf 2 N).subgroupOf N := by
        rw [CFSG.openPCoreOf_subgroupOf 2 N]
        exact hx
      exact Subgroup.mem_subgroupOf.mp hx' 
    have hρx : ρ (x : Q) ∈ pCoreOf 2 Nbar := by
      rw [← hPc_map]
      exact Subgroup.mem_map_of_mem ρ hxN
    refine (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Nbar) (x := φ x)).mpr ?_
    rw [← CFSG.openPCoreOf_subgroupOf 2 Nbar, Subgroup.mem_subgroupOf]
    simpa [φ] using hρx
  let f : Bar2 N →* Bar2 Nbar := QuotientGroup.lift (CFSG.pCore 2 ↥N) ψ hle
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Nbar) y
    have hz : (z : S) ∈ N.map ρ := by
      rw [hmap]
      exact z.2
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨x, hx⟩, ?_⟩
    show (QuotientGroup.lift (CFSG.pCore 2 ↥N) ψ hle)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨x, hx⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar) z
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hx⟩ = (↑(⟨x, hx⟩ : ↥N) : Bar2 N)
        from rfl,
      QuotientGroup.lift_mk' (CFSG.pCore 2 ↥N) (φ := ψ) hle ⟨x, hx⟩]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar)) (φ ⟨x, hx⟩) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar)) z
    rw [show φ ⟨x, hx⟩ = z from Subtype.ext hxz]
  refine ⟨f, hsurj, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) y
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar)) (φ x) = 1 := by
    have h2 : f (QuotientGroup.mk' (CFSG.pCore 2 ↥N) x) = 1 := hy
    rwa [show f (QuotientGroup.mk' (CFSG.pCore 2 ↥N) x) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Nbar)) (φ x) from
      QuotientGroup.lift_mk' (CFSG.pCore 2 ↥N) (φ := ψ) hle x] at h2
  have hφx : φ x ∈ (pCoreOf 2 Nbar).subgroupOf Nbar := by
    rw [CFSG.openPCoreOf_subgroupOf 2 Nbar]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hρx : ρ (x : Q) ∈ pCoreOf 2 Nbar := hPc_map ▸ Subgroup.mem_subgroupOf.mp hφx
  exact bar2_quot_mem_ker_image hPc_map hρx

private theorem odd_card_quotient_commutator_of_central_odd {H M : Type} [Group H] [Finite H]
    [Group M] (f : H →* M) (hf : Function.Surjective f) (hker : f.ker ≤ center H)
    (hM : commutator M = ⊤) (hodd : Odd (Nat.card f.ker)) :
    Odd (Nat.card (H ⧸ commutator H)) := by
  obtain ⟨hsup, -, -⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hf hker ⟨hM⟩
  let q : H →* H ⧸ commutator H := QuotientGroup.mk' (commutator H)
  have hqker : q.ker = commutator H := QuotientGroup.ker_mk' _
  have htop : (⊤ : Subgroup (H ⧸ commutator H)) = f.ker.map q := by
    have h := congrArg (Subgroup.map q) hsup
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff (commutator H)).mpr (by rw [hqker]),
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at h
    simpa using h.symm
  have hcard : Nat.card (H ⧸ commutator H) = Nat.card (f.ker.map q) := by
    rw [← Subgroup.card_top (G := H ⧸ commutator H), htop]
  rw [hcard]
  exact hodd.of_dvd_nat (Subgroup.card_map_dvd f.ker q)

private theorem commutator_eq_top_of_central_odd {H M : Type} [Group H] [Finite H] [Group M]
    (f : H →* M) (hf : Function.Surjective f) (hker : f.ker ≤ center H)
    (hM : Group.IsPerfect M) (hodd : Odd (Nat.card f.ker))
    (hgen : Subgroup.closure {x : H | ∃ k, orderOf x = 2 ^ k} = ⊤) :
    commutator H = ⊤ := by
  have hoddq : Odd (Nat.card (H ⧸ commutator H)) :=
    odd_card_quotient_commutator_of_central_odd f hf hker hM.commutator_eq_top hodd
  let q : H →* H ⧸ commutator H := QuotientGroup.mk' (commutator H)
  have hqgen : Subgroup.closure (q '' {x : H | ∃ k, orderOf x = 2 ^ k}) = ⊤ := by
    have h := congrArg (Subgroup.map q) hgen
    rwa [MonoidHom.map_closure, Subgroup.map_top_of_surjective q
      (QuotientGroup.mk'_surjective _)] at h
  have hqbot : Subgroup.closure (q '' {x : H | ∃ k, orderOf x = 2 ^ k}) = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    refine Subgroup.mem_bot.mpr ?_
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ orderOf_map_dvd q x)
    exact eq_one_of_orderOf_eq_two_pow_of_odd
      (hoddq.of_dvd_nat (orderOf_dvd_natCard (q x))) hj
  rw [eq_top_iff]
  intro x _
  have hx : q x = 1 := by
    have hmem : q x ∈ Subgroup.closure (q '' {x : H | ∃ k, orderOf x = 2 ^ k}) := by
      rw [hqgen]
      exact Subgroup.mem_top _
    rw [hqbot] at hmem
    simpa using hmem
  exact (QuotientGroup.eq_one_iff (x := x)).mp hx

omit [Finite Q] [Finite S] in
private theorem bar2_map_ker_center {ρ : Q →* S} (hZ : ρ.ker ≤ center Q)
    {N : Subgroup Q} {Nbar : Subgroup S} {f : Bar2 N →* Bar2 Nbar}
    (hker : f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) :
    f.ker ≤ center (Bar2 N) := by
  have hZc : (ρ.ker ⊓ N).subgroupOf N ≤ center ↥N := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz).1) (y : Q)
  exact hker.trans (map_le_center_quotient hZc)

omit [Finite Q] [Finite S] in
private theorem bar2_map_ker_odd {ρ : Q →* S} (hZodd : Odd (Nat.card ρ.ker))
    {N : Subgroup Q} {Nbar : Subgroup S} {f : Bar2 N →* Bar2 Nbar}
    (hker : f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) :
    Odd (Nat.card f.ker) := by
  have h1 : Nat.card ↥f.ker ∣
      Nat.card ↥(((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) :=
    Subgroup.card_dvd_of_le hker
  have h2 : Nat.card ↥(((ρ.ker ⊓ N).subgroupOf N).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) ∣
      Nat.card ↥((ρ.ker ⊓ N).subgroupOf N) := Subgroup.card_map_dvd _ _
  have h3 : Nat.card ↥((ρ.ker ⊓ N).subgroupOf N) = Nat.card ↥(ρ.ker ⊓ N) := by
    rw [← Subgroup.card_subtype N ((ρ.ker ⊓ N).subgroupOf N),
      Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  exact hZodd.of_dvd_nat (h1.trans (h2.trans (h3.symm ▸ Subgroup.card_dvd_of_le inf_le_left)))

omit [Finite S] in
private theorem bar2_ker_le_commutator {ρ : Q →* S} (hZ : ρ.ker ≤ center Q)
    {T : Subgroup Q} {N : Subgroup Q} {Nbar : Subgroup S} (hNT : N ≤ T)
    [hNnorm : (N.subgroupOf T).Normal]
    (hgen : Subgroup.closure {x : ↥T | ∃ k, orderOf x = 2 ^ k} = ⊤)
    (hquot : IsPGroup 2 (↥T ⧸ N.subgroupOf T))
    {f : Bar2 N →* Bar2 Nbar}
    (hker : f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)))
    (hodd : Odd (Nat.card (Abelianization (Bar2 N)))) :
    f.ker ≤ commutator (Bar2 N) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (hker hy)
  have hxker : (x : Q) ∈ ρ.ker := (Subgroup.mem_subgroupOf.mp hx).1
  let e : ↥(N.subgroupOf T) ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNT
  let zT : ↥(N.subgroupOf T) :=
    ⟨⟨(x : Q), hNT x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
  have hzcenter : (zT : ↥T) ∈ center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Q) * (x : Q) = (x : Q) * (g : Q)
    exact Subgroup.mem_center_iff.mp (hZ hxker) (g : Q)
  let φ : ↥(N.subgroupOf T) →* Abelianization (Bar2 N) :=
    (Abelianization.of.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥N))).comp e.toMonoidHom
  have hφ : φ zT = 1 := transfer_apply_eq_one_of_odd hgen hquot hodd φ hzcenter
  have hx' : e zT = x := Subtype.ext (Subgroup.subgroupOfEquivOfLe_apply_coe hNT zT)
  have h1 : Abelianization.of (QuotientGroup.mk' (CFSG.pCore 2 ↥N) x) = 1 := by
    simpa [φ, hx'] using hφ
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥N) x ∈ commutator (Bar2 N) := by
    have := MonoidHom.mem_ker.mpr h1
    rwa [Abelianization.ker_of (Bar2 N)] at this
  rwa [← hxy]

private theorem bar2_lift_isQuasisimple {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) (i : Fin d)
    (hqi : CFSG.Open.IsQuasisimple (Bar2 (L i))) :
    CFSG.Open.IsQuasisimple (Bar2 (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)) := by
  set Li := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P with hLidef
  have hmapLi : Li.map ρ = L i := lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hPc_map := bar2_map_pCore hZ hZodd hmapLi
  obtain ⟨f, hsurj, hker⟩ := bar2_map_data hPc_map hmapLi
  have hkerC : f.ker ≤ center (Bar2 Li) := bar2_map_ker_center hZ hker
  have hgen : Subgroup.closure {y : Bar2 Li | ∃ k, orderOf y = 2 ^ k} = ⊤ :=
    closure_two_bar2_eq_top (lift_opp_self (ρ := ρ) (P := P) (L := L i))
  have hodd : Odd (Nat.card f.ker) := bar2_map_ker_odd hZodd hker
  have hcomm : commutator (Bar2 Li) = ⊤ :=
    commutator_eq_top_of_central_odd f hsurj hkerC ⟨hqi.1⟩ hodd hgen
  exact CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly.isQuasisimple_of_central_quotient
    hsurj hcomm hkerC hqi

private theorem false_of_isL2_bar2 {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L)
    (hno : ∀ (i : Fin d) (N : Subgroup S) (n : ℕ), pCoreOf 2 (P.map ρ) ≤ N → N ≤ L i →
      (N.subgroupOf (L i)).Normal → 3 ≤ n → ¬ IsL2 (Bar2 N) n)
    (i : Fin d) (N : Subgroup Q) (n : ℕ) (hON : pCoreOf 2 P ≤ N)
    (hNL : N ≤ Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)
    (hNnorm : (N.subgroupOf (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)).Normal)
    (hn : 3 ≤ n) (hL2 : IsL2 (Bar2 N) n) : False := by
  set Li := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P with hLidef
  have hmapLi : Li.map ρ = L i := lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hNbar_le : N.map ρ ≤ L i := by
    rw [← hmapLi]
    exact Subgroup.map_mono hNL
  have hOle : pCoreOf 2 (P.map ρ) ≤ N.map ρ := by
    rw [← lift_pCoreOf_map hρ hZ hP]
    exact Subgroup.map_mono hON
  have hNbar_norm : ((N.map ρ).subgroupOf (L i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNbar_le]
    have h1 : Li ≤ normalizer (N : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hNnorm
    have h2 : Li.map ρ ≤ normalizer ((N.map ρ : Subgroup S) : Set S) :=
      (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map ρ)
    rwa [hmapLi] at h2
  obtain ⟨f, hsurj, hker⟩ :=
    bar2_map_data (bar2_map_pCore hZ hZodd (N := N) (Nbar := N.map ρ) rfl) rfl
  have hkerC : f.ker ≤ center (Bar2 N) := bar2_map_ker_center hZ hker
  have hcenter : center (Bar2 N) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_center_bot hL2
  have hkerbot : f.ker = ⊥ := le_bot_iff.mp (hkerC.trans (le_of_eq hcenter))
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hkerbot
  let e : Bar2 N ≃* Bar2 (N.map ρ) := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact hno i (N.map ρ) n hOle hNbar_le hNbar_norm hn
    (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)

theorem LeviAlt.lift_of_le_center {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q} (hP : ρ.ker ≤ P)
    {d : ℕ} {L : Fin d → Subgroup S} (hL : IsLeviFamily (P.map ρ) d L)
    (h : LeviAlt (P.map ρ) d L) :
    LeviAlt P d (fun i => Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) := by
  rcases h with ⟨hd, hq⟩ | hno
  · exact Or.inl ⟨hd, fun i => bar2_lift_isQuasisimple hρ hZ hZodd hP hL i (hq i)⟩
  · exact Or.inr fun i N n hON hNL hNnorm hn hL2 =>
      false_of_isL2_bar2 hρ hZ hZodd hP hL hno i N n hON hNL hNnorm hn hL2

omit [Finite S] in
private theorem bar2_lift_block_quasi {ρ : Q →* S} {T N : Subgroup Q} {Nbar : Subgroup S}
    (hZ : ρ.ker ≤ center Q) (hNT : N ≤ T)
    [hNnorm : (N.subgroupOf T).Normal]
    (hgen : Subgroup.closure {x : ↥T | ∃ k, orderOf x = 2 ^ k} = ⊤)
    (hquot : IsPGroup 2 (↥T ⧸ N.subgroupOf T))
    {f : Bar2 N →* Bar2 Nbar}
    (hker : f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)))
    (hsurj : Function.Surjective f) (hkerC : f.ker ≤ center (Bar2 N))
    (hKodd : Odd (Nat.card f.ker))
    (hquasi : CFSG.Open.IsQuasisimple (Bar2 Nbar)) :
    CFSG.Open.IsQuasisimple (Bar2 N) := by
  have hoddA : Odd (Nat.card (Abelianization (Bar2 N))) :=
    odd_card_quotient_commutator_of_central_odd f hsurj hkerC hquasi.1 hKodd
  have hcomm : f.ker ≤ commutator (Bar2 N) :=
    bar2_ker_le_commutator hZ hNT hgen hquot hker hoddA
  obtain ⟨hsup, -, -⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hsurj hkerC ⟨hquasi.1⟩
  have hperf : commutator (Bar2 N) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le le_rfl hcomm
  exact CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly.isQuasisimple_of_central_quotient
    hsurj hperf (fun x hx => hkerC hx) hquasi

omit [Finite S] in
private theorem bar2_lift_block_cyclic {ρ : Q →* S} {T N : Subgroup Q} {Nbar : Subgroup S}
    (hZ : ρ.ker ≤ center Q) (hNT : N ≤ T)
    [hNnorm : (N.subgroupOf T).Normal]
    (hgen : Subgroup.closure {x : ↥T | ∃ k, orderOf x = 2 ^ k} = ⊤)
    (hquot : IsPGroup 2 (↥T ⧸ N.subgroupOf T))
    {f : Bar2 N →* Bar2 Nbar}
    (hker : f.ker ≤ ((ρ.ker ⊓ N).subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)))
    (hsurj : Function.Surjective f) (hkerC : f.ker ≤ center (Bar2 N))
    (hKodd : Odd (Nat.card f.ker))
    (e3 : Bar2 Nbar ≃* Multiplicative (ZMod 3)) :
    Nonempty (Bar2 N ≃* Multiplicative (ZMod 3)) := by
  have hcyc : IsCyclic (Bar2 Nbar) := (MulEquiv.isCyclic e3).mpr inferInstance
  have hcommutative : ∀ a b : Bar2 N, a * b = b * a :=
    commutative_of_cyclic_center_quotient f hkerC
  have hcommbot : commutator (Bar2 N) = ⊥ :=
    (commutator_eq_bot_iff (Bar2 N)).mpr ⟨Std.Commutative.mk hcommutative⟩
  have hcardNbar : Nat.card (Bar2 Nbar) = 3 := by
    simpa using Nat.card_congr e3.toEquiv
  have hcardN : Nat.card (Bar2 N) = Nat.card f.ker * 3 := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hsurj, hcardNbar]
  have hoddN : Odd (Nat.card (Bar2 N)) := by
    rw [hcardN]
    exact hKodd.mul (by norm_num)
  have hsurj_of : Function.Surjective
      (Abelianization.of : Bar2 N →* Abelianization (Bar2 N)) := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (commutator (Bar2 N)) x
    exact ⟨y, hy⟩
  have hoddA : Odd (Nat.card (Abelianization (Bar2 N))) :=
    hoddN.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj_of)
  have hcomm : f.ker ≤ commutator (Bar2 N) :=
    bar2_ker_le_commutator hZ hNT hgen hquot hker hoddA
  have hkerbot : f.ker = ⊥ := by
    rw [hcommbot] at hcomm
    exact le_bot_iff.mp hcomm
  let e : Bar2 N ≃* Bar2 Nbar :=
    MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hkerbot, hsurj⟩
  exact ⟨e.trans e3⟩

private theorem bar2_oUpperTwo_lift_block {two : Prop} {ρ : Q →* S}
    (hρ : Function.Surjective ρ) (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker))
    {P : Subgroup Q} (hP : ρ.ker ≤ P) {d : ℕ} {L : Fin d → Subgroup S}
    (hL : IsLeviFamily (P.map ρ) d L) (i : Fin d)
    (hqi : 3 ∣ Nat.card (Bar2 (S17.oUpperTwo (L i))) ∧
      (CFSG.Open.IsQuasisimple (Bar2 (S17.oUpperTwo (L i))) ∨
        (Nonempty (Bar2 (S17.oUpperTwo (L i)) ≃* Multiplicative (ZMod 3)) ∧ two))) :
    3 ∣ Nat.card (Bar2 (S17.oUpperTwo (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P))) ∧
      (CFSG.Open.IsQuasisimple (Bar2 (S17.oUpperTwo (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P))) ∨
        (Nonempty (Bar2 (S17.oUpperTwo (Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P)) ≃*
          Multiplicative (ZMod 3)) ∧ two)) := by
  set Li := Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P with hLi
  set N := S17.oUpperTwo Li with hN
  set Nbar := S17.oUpperTwo (L i) with hNbar
  have hmapLi : Li.map ρ = L i := lift_map_sup hρ hZ hP (hL.eq_opp_sup i)
  have hmap : N.map ρ = Nbar := by
    rw [hN, hNbar]
    change (CFSG.ComponentClassification.AS76b.oUpperTwo Li).map ρ =
      CFSG.ComponentClassification.AS76b.oUpperTwo (L i)
    rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, hmapLi]
  have hNle : N ≤ Li := by rw [hN]; exact S17.oUpperTwo_le Li
  have hNsub_eq : N.subgroupOf Li = Subgroup.closure {y : ↥Li | Odd (orderOf y)} := by
    apply Subgroup.map_injective Li.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hNle, hN, S17.oUpperTwo_eq_closure,
      MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx.1⟩, by simpa [Subgroup.orderOf_coe] using hx.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [Subgroup.orderOf_coe] using hy⟩
  have hNnormal : (N.subgroupOf Li).Normal := by
    rw [hNsub_eq]
    exact CFSG.GH74.Uniqueness.closure_odd_normal
  have hgen : Subgroup.closure {x : ↥Li | ∃ k, orderOf x = 2 ^ k} = ⊤ := by
    have h := opp_top_eq_top_of_opp_eq (lift_opp_self (ρ := ρ) (P := P) (L := L i))
    change Subgroup.closure {x : ↥Li | x ∈ (⊤ : Subgroup ↥Li) ∧
      ∃ k, orderOf x = 2 ^ k} = ⊤ at h
    have hset : {x : ↥Li | x ∈ (⊤ : Subgroup ↥Li) ∧ ∃ k, orderOf x = 2 ^ k} =
        {x : ↥Li | ∃ k, orderOf x = 2 ^ k} := by
      ext x
      simp
    rw [hset] at h
    exact h
  have hquot : IsPGroup 2 (↥Li ⧸ N.subgroupOf Li) :=
    IsPGroup.of_equiv (CFSG.GH74.Uniqueness.isPGroup_two_quotient_closure_odd (G := ↥Li))
      (QuotientGroup.quotientMulEquivOfEq hNsub_eq).symm
  have hPc_map := bar2_map_pCore hZ hZodd hmap
  obtain ⟨f, hsurj, hker⟩ := bar2_map_data hPc_map hmap
  have hkerC : f.ker ≤ center (Bar2 N) := bar2_map_ker_center hZ hker
  have hKodd : Odd (Nat.card f.ker) := bar2_map_ker_odd hZodd hker
  have hdvd : 3 ∣ Nat.card (Bar2 N) := hqi.1.trans (Subgroup.card_dvd_of_surjective hsurj)
  refine ⟨hdvd, ?_⟩
  rcases hqi.2 with hquasi | ⟨e3, htwo⟩
  · exact Or.inl (bar2_lift_block_quasi hZ hNle hgen hquot hker hsurj hkerC hKodd hquasi)
  · exact Or.inr ⟨bar2_lift_block_cyclic hZ hNle hgen hquot hker hsurj hkerC hKodd e3.some,
      htwo⟩

theorem LeviBlk.lift_of_le_center {two big : Prop} {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q} (hP : ρ.ker ≤ P)
    {d : ℕ} {L : Fin d → Subgroup S} (hL : IsLeviFamily (P.map ρ) d L)
    (h : LeviBlk two big d L) :
    LeviBlk two big d (fun i => Opp 2 ((L i).comap ρ) ⊔ pCoreOf 2 P) :=
  ⟨fun i => bar2_oUpperTwo_lift_block (two := two) hρ hZ hZodd hP hL i (h.1 i), h.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
