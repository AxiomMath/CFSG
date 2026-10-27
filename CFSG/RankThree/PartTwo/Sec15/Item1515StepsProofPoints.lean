module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thetaComponentsAt_eq_of_zpowers_eq {c c' : G}
    (h : Subgroup.zpowers c' = Subgroup.zpowers c) :
    thetaComponentsAt 3 c' = thetaComponentsAt 3 c := by
  rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
    centralizer_singleton_eq_of_zpowers_eq h]

theorem eq_of_mem_lA_of_zpowers_eq {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h3 : 3 ∣ Nat.card L) {c' : G} (hcc : Subgroup.zpowers c' = Subgroup.zpowers c)
    {L' : Subgroup G} (hL' : L' ∈ lA A c') : L' = L := by
  have hc' : Subgroup.zpowers c' ∈ omegaA A := hcc ▸ h.zpowers_mem_omegaA
  have hLc' : L ∈ thetaComponentsAt 3 c' :=
    (thetaComponentsAt_eq_of_zpowers_eq hcc) ▸ h.mem_lA.1
  exact ((h.chosen136.2 c' hc' L' hL').2 L hLc' h3).symm

theorem exists_conj_of_transOmega {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h3 : 3 ∣ Nat.card L)
    (hT : ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
      F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom)
    {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ∃ w ∈ Subgroup.normalizer (A : Set G), L' = L.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨w, hwA, hw⟩ := hT _ hc'
  have hz : Subgroup.zpowers c' = Subgroup.zpowers ((MulAut.conj w) c) := by
    rw [hw, MonoidHom.map_zpowers]
    rfl
  have hLw : L.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 c' := by
    rw [thetaComponentsAt_eq_of_zpowers_eq hz]
    exact map_mem_thetaComponentsAt (MulAut.conj w) h.mem_lA.1
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj w).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective]
  exact ⟨w, hwA, ((h.chosen136.2 c' hc' L' hL').2 _ hLw h3').symm⟩

theorem nonempty_thetaQuot_equiv_of_transOmega {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h3 : 3 ∣ Nat.card L)
    (hT : ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
      F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom)
    {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  obtain ⟨w, -, rfl⟩ := exists_conj_of_transOmega h h3 hT hc' hL'
  exact ⟨(thetaQuotEquiv (MulAut.conj w) L).symm⟩

omit [Finite G] in
theorem three_dvd_card_of_thetaQuot {L : Subgroup G}
    (h : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : 3 ∣ Nat.card L :=
  h.trans (Subgroup.card_quotient_dvd_card _)

omit [Finite G] in
theorem three_dvd_card_of_mulEquiv {L : Subgroup G} {S : Type*} [Mul S]
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* S) (h : 3 ∣ Nat.card S) : 3 ∣ Nat.card L :=
  three_dvd_card_of_thetaQuot ((Nat.card_congr e.toEquiv).symm ▸ h)

theorem multFree_alternatingGroup_seven : MultFree (alternatingGroup (Fin 7)) :=
  fun X _ _ Z _ hX hZc hcop hS => KFacts.KS14.ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inl hS))

theorem multFree_M22 : MultFree CFSG.Blueprint.NativeSporadic.M22 :=
  fun X _ _ Z _ hX hZc hcop hS => KFacts.KS14.ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inr hS))

theorem multFree_M12 : MultFree CFSG.Blueprint.NativeSporadic.M12 :=
  fun X _ _ Z _ hX hZc hcop hS => KFacts.KS14.ks18Mult_sporadic X Z hX hZc hcop (Or.inl hS)

theorem multFree_J2 :
    MultFree CFSG.Blueprint.NativeSporadic.J2 :=
  fun X _ _ Z _ hX hZc hcop hS => KFacts.KS14.ks18Mult_j2 X Z hX hZc hcop hS

theorem multFree_of_isLThreePi
    {S : Type} [Group S] (hS : IsLThreePi S) : MultFree S :=
  fun X _ _ Z _ hX hZc hcop ⟨e⟩ =>
    KFacts.KS14.ks18Mult_lThreePi X Z hX hZc hcop (isLThreePi_of_mulEquiv e hS)

theorem nonempty_quot_pCore_two_equiv_of_multFree {A Y : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hY : Y ∈ scriptY4 A LB) {S : Type} [Mul S]
    (hS : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* S)) (hmult : MultFree S) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* S) := by
  obtain ⟨e⟩ := hS
  have : Nontrivial (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_quot_pPrimeCore hY)
  have : Nontrivial S := e.symm.surjective.nontrivial
  have heq := pPrimeCore_three_eq_pCore_two_of_multFree hY.2.2.2 ⟨e⟩ hmult
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans e⟩

theorem pPrimeCore_eq_pCore_of_mem_scriptY4 {A Y : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hY : Y ∈ scriptY4 A LB) {S : Type} [Mul S]
    (hS : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* S)) (hmult : MultFree S) :
    CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y := by
  obtain ⟨e⟩ := hS
  have : Nontrivial (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_quot_pPrimeCore hY)
  have : Nontrivial S := e.symm.surjective.nontrivial
  exact pPrimeCore_three_eq_pCore_two_of_multFree hY.2.2.2 ⟨e⟩ hmult

theorem eq_deltaZero_of_mem_scriptY4 (hbot : Item145BotS14) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) :
    Y = deltaZero A (lB A) Y :=
  rank3II_15_1_lB h.isE27 (hbot G A c L h.toSec14Std) hY

end CFSG.RankThree.PartTwo.Sec15.Proof1515
