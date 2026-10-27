module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi8b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xg
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
import CFSG.CGT.PushingUpLit.Transport
import CFSG.CGT.PushingUpLit.Statements
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22k8

variable {D : Data G} {Y : Subgroup (MBar D.M D.U)} {K : Subgroup G}

theorem isMax_inf_sup (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (i : Fin m) {A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian D.T A) :
    CFSG.Quasithin.IsMaxElemAbelian D.T
      ((A ⊓ centralizer (proofIi D (preN D (Nb i)) : Set G)) ⊔ proofIi D (preN D (Nb i))) := by
  set Ii : Subgroup G := proofIi D (preN D (Nb i)) with hIidef
  have hIU : Ii ≤ D.U := P22x.proofIi_le D (preN_le_M D (Nb i))
  have hIel : IsElemAbelian 2 Ii := (uc22p22xf_hel D).mono hIU
  have hIT : Ii ≤ D.T := hIU.trans (uc22p22xf_UleT D)
  have hAJ : A ≤ jOf D.T := le_jOf_of_isMax hA
  have hAN : A ≤ proofN D := hAJ.trans (uc22p22e_jOf_le D.sylowM)
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  have hCIA : centralizer (A : Set G) ⊓ Ii ≤ A := by
    have hle : A ⊔ (centralizer (A : Set G) ⊓ Ii) ≤ D.T := sup_le hAT (inf_le_right.trans hIT)
    have hel : IsElemAbelian 2 (A ⊔ (centralizer (A : Set G) ⊓ Ii)) :=
      hAel.sup_of_commute (hIel.mono inf_le_right) fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.1 a ha
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ _) (hAmax _ hle hel)
    exact le_sup_right.trans heq.symm.le
  set B : Subgroup G := A ⊓ centralizer (Ii : Set G) with hBdef
  have hBI : ∀ b ∈ B, ∀ x ∈ Ii, b * x = x * b := fun b hb x hx =>
    (Subgroup.mem_centralizer_iff.1 hb.2 x hx).symm
  have hBIel : IsElemAbelian 2 (B ⊔ Ii) := (hAel.mono inf_le_left).sup_of_commute hIel hBI
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B Ii hBI
  have hBinf : B ⊓ Ii = centralizer (A : Set G) ⊓ Ii := by
    apply le_antisymm
    · rintro x ⟨⟨hxA, -⟩, hxI⟩
      exact ⟨Subgroup.mem_centralizer_iff.2 fun a ha => hAel.comm ha hxA, hxI⟩
    · rintro x ⟨hxc, hxI⟩
      exact ⟨⟨hCIA ⟨hxc, hxI⟩, Subgroup.mem_centralizer_iff.2 fun y hy => hIel.comm hy hxI⟩, hxI⟩
  rw [hBinf] at hprod
  have hloc := P22sp.relIndex_mul_card_le D Ch h3 h51 hH c m Nb hNb i hAN (D.sylowM.isPGroup.to_le hAT)
  have eA := Subgroup.relIndex_mul_card (H := centralizer (Ii : Set G)) (K := A)
  rw [inf_comm] at eA
  have hcpos : 0 < Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := Nat.card_pos
  have hcardBI : Nat.card A ≤ Nat.card ↥(B ⊔ Ii) := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(centralizer (A : Set G) ⊓ Ii)) ?_ hcpos
    calc Nat.card A * Nat.card ↥(centralizer (A : Set G) ⊓ Ii)
        = (centralizer (Ii : Set G)).relIndex A * Nat.card ↥(centralizer (A : Set G) ⊓ Ii) * Nat.card B := by
          rw [← eA]; ring
      _ ≤ Nat.card Ii * Nat.card B := Nat.mul_le_mul_right _ hloc
      _ = Nat.card ↥(B ⊔ Ii) * Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := by rw [hprod]; ring
  exact ⟨sup_le (inf_le_left.trans hAT) hIT, hBIel, fun Z hZT hZel => (hAmax Z hZT hZel).trans hcardBI⟩

theorem KLift.proofIi_le_pCoreOf (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    proofIi D (preN D (Nb i)) ≤ pCoreOf 2 (K ⊔ proofS D) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hIH, hHI, -, -⟩ := KLift.isTwoReducedIn D Ch h2 h3 h51 hH c hNb hK
  have hIU : proofIi D (preN D (Nb i)) ≤ D.U := P22x.proofIi_le D (preN_le_M D (Nb i))
  have hI2 : IsPGroup 2 (proofIi D (preN D (Nb i))) := fun x =>
    ⟨1, Subtype.ext (by simpa using (uc22p22xf_hel D).2 _ (hIU x.2))⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hIH hHI hI2

theorem KLift.proofIi_le_omegaZJ22 (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    proofIi D (preN D (Nb i)) ≤ omegaZJ22 (pCoreOf 2 (K ⊔ proofS D)) := by
  have hIR := KLift.proofIi_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK
  have hRC := KLift.pCoreOf_le_centralizer D Ch h2 h3 h51 hH c hNb hK
  have hIU : proofIi D (preN D (Nb i)) ≤ D.U := P22x.proofIi_le D (preN_le_M D (Nb i))
  intro z hz
  refine uc22p22e_mem_omegaZJ'.2 ⟨hIR hz, fun j hj => ?_, (uc22p22xf_hel D).2 z (hIU hz)⟩
  exact (Subgroup.mem_centralizer_iff.1 (hRC (uc22p22e_jOf_le_self _ hj)) z hz).symm

theorem KLift.inf_centralizer_le_pCoreOf (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    proofS D ⊓ centralizer (proofIi D (preN D (Nb i)) : Set G) ≤ pCoreOf 2 (K ⊔ proofS D) := fun s hs =>
  KLift.kerN_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK
    ⟨Subgroup.mem_sup_right hs.1, P22sp.inf_centralizer_le_preMbar D Ch h2 h3 h51 hH c m Nb hNb i hs⟩

theorem KLift.eq_sup_of_isMax (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian D.T A) :
    omegaZJ22 (pCoreOf 2 (K ⊔ proofS D)) =
      proofIi D (preN D (Nb i)) ⊔ (omegaZJ22 (pCoreOf 2 (K ⊔ proofS D)) ⊓ centralizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := pCoreOf 2 (K ⊔ proofS D) with hRdef
  set W : Subgroup G := omegaZJ22 R with hWdef
  set Ii : Subgroup G := proofIi D (preN D (Nb i)) with hIidef
  have hRT : R ≤ D.T := hK.pCoreOf_le_T
  have hWR : W ≤ R := (uc22p22e_omegaZJ_le_jOf R).trans (uc22p22e_jOf_le_self R)
  have hWT : W ≤ D.T := hWR.trans hRT
  have hWel := P22sp.isElemAbelian_omegaZJ22 R
  have hIW := KLift.proofIi_le_omegaZJ22 D Ch h2 h3 h51 hH c hNb hK
  have hAJ : A ≤ jOf D.T := le_jOf_of_isMax hA
  have hAS : A ≤ proofS D := hAJ.trans (P22s.jOf_le_proofS D)
  have hAN : A ≤ proofN D := hAJ.trans (uc22p22e_jOf_le D.sylowM)
  have hBmax := isMax_inf_sup D Ch h3 h51 hH c hNb i hA
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  set B : Subgroup G := A ⊓ centralizer (Ii : Set G) with hBdef
  have hBR : B ≤ R := fun b hb =>
    KLift.inf_centralizer_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK ⟨hAS hb.1, hb.2⟩
  have hBImax : CFSG.Quasithin.IsMaxElemAbelian R (B ⊔ Ii) :=
    ⟨sup_le hBR (hIW.trans hWR), hBmax.2.1, fun Z hZR hZel => hBmax.2.2 Z (hZR.trans hRT) hZel⟩
  have hBW : B ≤ centralizer (W : Set G) := fun b hb => Subgroup.mem_centralizer_iff.2 fun w hw =>
    ((uc22p22e_mem_omegaZJ.1 hw).2.1 b (le_jOf_of_isMax hBImax (Subgroup.mem_sup_left hb))).symm
  have hloc := P22sp.relIndex_mul_card_le D Ch h3 h51 hH c m Nb hNb i hAN (D.sylowM.isPGroup.to_le hAT)
  have eI := Subgroup.relIndex_mul_card (H := centralizer (A : Set G)) (K := Ii)
  have eW := Subgroup.relIndex_mul_card (H := centralizer (A : Set G)) (K := W)
  have hcpos : 0 < Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := Nat.card_pos
  have h1 : (centralizer (A : Set G)).relIndex W ≤ (centralizer (W : Set G)).relIndex A :=
    uc22p22xf_relIndex_le hWT hWel ⟨hAT, hAel, hAmax⟩
  have h2' : (centralizer (W : Set G)).relIndex A ≤ (centralizer (Ii : Set G)).relIndex A := by
    rw [← Subgroup.inf_relIndex_right (centralizer (W : Set G)),
      ← Subgroup.inf_relIndex_right (centralizer (Ii : Set G))]
    refine Subgroup.relIndex_le_of_le_left ?_ Subgroup.index_ne_zero_of_finite
    exact le_inf (fun b hb => hBW ⟨hb.2, hb.1⟩) inf_le_right
  have h3' : (centralizer (Ii : Set G)).relIndex A ≤ (centralizer (A : Set G)).relIndex Ii := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [eI]
    exact hloc
  have h4 : (centralizer (A : Set G)).relIndex Ii ≤ (centralizer (A : Set G)).relIndex W :=
    Subgroup.relIndex_le_of_le_right hIW Subgroup.index_ne_zero_of_finite
  have heq : (centralizer (A : Set G)).relIndex Ii = (centralizer (A : Set G)).relIndex W :=
    le_antisymm h4 (h1.trans (h2'.trans h3'))
  set D' : Subgroup G := W ⊓ centralizer (A : Set G) with hD'def
  have hID : ∀ x ∈ Ii, ∀ y ∈ D', x * y = y * x := fun x hx y hy => hWel.comm (hIW hx) hy.1
  obtain ⟨hprod2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ii D' hID
  have hinf2 : Ii ⊓ D' = centralizer (A : Set G) ⊓ Ii := by
    rw [hD'def, ← inf_assoc, inf_eq_left.2 hIW, inf_comm]
  rw [hinf2] at hprod2
  have hD'card : Nat.card D' = Nat.card ↥(centralizer (A : Set G) ⊓ W) := by rw [hD'def, inf_comm]
  have hcard : Nat.card W ≤ Nat.card ↥(Ii ⊔ D') := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(centralizer (A : Set G) ⊓ Ii)) ?_ hcpos
    calc Nat.card W * Nat.card ↥(centralizer (A : Set G) ⊓ Ii)
        = (centralizer (A : Set G)).relIndex W * Nat.card ↥(centralizer (A : Set G) ⊓ W) *
            Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := by rw [eW]
      _ = (centralizer (A : Set G)).relIndex Ii * Nat.card ↥(centralizer (A : Set G) ⊓ Ii) * Nat.card D' := by
          rw [← heq, hD'card]; ring
      _ = Nat.card Ii * Nat.card D' := by rw [eI]
      _ ≤ Nat.card ↥(Ii ⊔ D') * Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := hprod2.symm.le
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hIW inf_le_left) hcard).symm

theorem KLift.commutator_omegaZJ22_le (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    ⁅omegaZJ22 (pCoreOf 2 (K ⊔ proofS D)), jOf D.T⁆ ≤ proofEiHat D (preN D (Nb i)) := by
  set W : Subgroup G := omegaZJ22 (pCoreOf 2 (K ⊔ proofS D)) with hWdef
  set Ii : Subgroup G := proofIi D (preN D (Nb i)) with hIidef
  set Q : Subgroup G := proofEiHat D (preN D (Nb i)) with hQdef
  have hWel := P22sp.isElemAbelian_omegaZJ22 (pCoreOf 2 (K ⊔ proofS D))
  have hIW := KLift.proofIi_le_omegaZJ22 D Ch h2 h3 h51 hH c hNb hK
  have hJQ : jOf D.T ≤ normalizer (Q : Set G) := by
    intro a ha
    have haS := P22s.jOf_le_proofS D ha
    exact mem_normalizer_commutator (uc22p22x_S_normalizes D Ch h2 h3 h51 hH c m Nb hNb i haS).2.2
      (Subgroup.le_normalizer ha)
  let Yg : Subgroup G :=
    { carrier := {a | a ∈ normalizer (Q : Set G) ∧ ∀ w ∈ W, ⁅w, a⁆ ∈ Q}
      mul_mem' := by
        rintro a b ⟨ha, haW⟩ ⟨hb, hbW⟩
        refine ⟨mul_mem ha hb, fun w hw => ?_⟩
        have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (haW w hw) ((mem_normalizer_iff.1 ha _).1 (hbW w hw))
      one_mem' := ⟨one_mem _, fun w _ => by rw [commutatorElement_one_right]; exact Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, haW⟩
        refine ⟨inv_mem ha, fun w hw => ?_⟩
        have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (Q.inv_mem (haW w hw)) }
  have hJY : jOf D.T ≤ Yg := by
    refine jOf_le_of_forall_isMax fun A hA => ?_
    have hAJ : A ≤ jOf D.T := le_jOf_of_isMax hA
    have hW := KLift.eq_sup_of_isMax D Ch h2 h3 h51 hH c hNb hK hA
    intro a ha
    refine ⟨hJQ (hAJ ha), fun w hw => ?_⟩
    have hW' : W = Ii ⊔ (W ⊓ centralizer (A : Set G)) := hW
    rw [hW'] at hw
    have hDN : W ⊓ centralizer (A : Set G) ≤ normalizer (Ii : Set G) := by
      intro y hy
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hWel.comm hy.1 (hIW hx)]
        simpa [mul_assoc] using hx
      · intro hx
        have hx' : x ∈ W := by
          have h := W.mul_mem (W.mul_mem (W.inv_mem hy.1) (hIW hx)) hy.1
          simpa [mul_assoc] using h
        have : y * x * y⁻¹ = x := by
          rw [hWel.comm hy.1 hx']
          group
        rwa [this] at hx
    obtain ⟨x, hx, y, hy, rfl⟩ := P22s.exists_mul_of_mem_sup hDN hw
    have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.1 hy.2 a ha).symm
    have e : ⁅x * y, a⁆ = ⁅x, a⁆ := by
      simp only [commutatorElement_def]
      calc x * y * a * (x * y)⁻¹ * a⁻¹ = x * (y * a) * y⁻¹ * x⁻¹ * a⁻¹ := by group
        _ = x * (a * y) * y⁻¹ * x⁻¹ * a⁻¹ := by rw [hya]
        _ = x * a * x⁻¹ * a⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx (hAJ ha)
  rw [Subgroup.commutator_le]
  intro w hw a ha
  exact (hJY ha).2 w hw

theorem KLift.idStar_b (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    ⁅jOf D.T, omegaZJ22 (pCoreOf 2 (K ⊔ proofS D))⁆ = proofEiHat D (preN D (Nb i)) := by
  rw [Subgroup.commutator_comm]
  refine le_antisymm (KLift.commutator_omegaZJ22_le D Ch h2 h3 h51 hH c hNb hK) ?_
  exact Subgroup.commutator_mono (KLift.proofIi_le_omegaZJ22 D Ch h2 h3 h51 hH c hNb hK) le_rfl

theorem preN_inf_centralizer_le (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (i : Fin m) :
    preN D (Nb i) ⊓ centralizer (proofIi D (preN D (Nb i)) : Set G) ≤ centralizer (D.U : Set G) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  rintro x ⟨hx, hxc⟩
  obtain ⟨-, hxM, hxY⟩ := (mem_preN D).1 hx
  have hfix := (P22sp.mem_centralizer_iff_fix D e ρ hc (d.le i) hxM).1 hxc
  exact (uc22br_gt_mk_eq_one_iff (uc22p22xf_hV D) ⟨x, hxM⟩).1 (d.faithful i hxY hfix)

theorem KLift.dvd_card (hK : KLift D Y K) {p : ℕ} (hp : p ∣ Nat.card ↥Y) : p ∣ Nat.card ↥(K ⊔ proofS D) := by
  rw [← hK.image] at hp
  have h1 : Nat.card ↥(mbarImage D.M D.U K) ∣ Nat.card ↥(K.subgroupOf D.M) :=
    Subgroup.card_map_dvd (H := K.subgroupOf D.M) (QuotientGroup.mk' (kerAct D.M D.U).normalCore)
  have h2 : Nat.card ↥(K.subgroupOf D.M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.le_M).toEquiv
  rw [h2] at h1
  exact (hp.trans h1).trans (Subgroup.card_dvd_of_le le_sup_left)

theorem KLift.not_inClassX (h640 : UC6.R6_40_1 D) (hK : KLift D Y K) :
    ¬ InClassX ↥(oResidualTwo ↥(K ⊔ proofS D)) := by
  intro hX
  set H : Subgroup G := K ⊔ proofS D with hHdef
  have hHK : H ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK.le_normalizer_S
  set K₂ : Subgroup G := (oResidualTwo ↥H).map H.subtype with hK₂
  have hK₂K : K₂ ≤ K := by
    have hN : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHK
    have hle := oResidualTwo_le hN (fun x => by
      obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup (D.sylowM.isPGroup.to_le inf_le_left) hK.le_normalizer_S x.2
      exact ⟨k, by simpa [Subgroup.mem_subgroupOf] using hk⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy
  have hKM : K ≤ D.M := hK.le_M
  have hK₂M : K₂ ≤ D.M := hK₂K.trans hKM
  have hK₂norm : (K₂.subgroupOf K).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    have hg : (g : G) ∈ H := Subgroup.mem_sup_left g.2
    have := (oResidualTwo_normal ↥H).conj_mem y hy ⟨g, hg⟩
    have hyx' : (y : G) = x := hyx
    refine ⟨_, this, ?_⟩
    simp [hyx']
  have hsub : (K₂.subgroupOf D.M).IsSubnormal := isSubnormal_subgroupOf_step hK₂K hKM hK₂norm hK.subnormal
  have hKX : InClassX ↥(K₂.subgroupOf D.M) := by
    have e1 : ↥(oResidualTwo ↥H) ≃* ↥K₂ :=
      (oResidualTwo ↥H).equivMapOfInjective H.subtype H.subtype_injective
    have e2 : ↥(K₂.subgroupOf D.M) ≃* ↥K₂ := Subgroup.subgroupOfEquivOfLe hK₂M
    exact CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv (e1.trans e2.symm) hX
  exact h640 D.M D.maxLocal (K₂.subgroupOf D.M) ⟨hsub, hKX⟩

end P22k8

open P22k8

theorem uc22k_hiPkgK_of_klift (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h640 : UC6.R6_40_1 D) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m} {K : Subgroup G}
    (hK : KLift D (Nb i) K) (h6 : 6 < Nat.card ↥(Nb i)) : HiPkgK D (Nb i) (K ⊔ proofS D) := by
  have hb := KLift.idStar_b D Ch h2 h3 h51 hH c hNb hK
  obtain ⟨hnE, hnZ⟩ := KLift.sup_not_le_centralizer D Ch h2 h3 h51 hH c hNb hK
  refine ⟨le_sup_right, KLift.inClassG D Ch h2 h3 h51 hH c hNb hK h6, hnZ, KLift.not_inClassX h640 hK, hb, ?_,
    sup_le hK.le_M (proofS_le_M D), fun p _ _ hp => hK.dvd_card hp, hnE, proofIi D (preN D (Nb i)),
    KLift.proofIi_le_omegaZJ22 D Ch h2 h3 h51 hH c hNb hK, KLift.pCoreOf_le_centralizer D Ch h2 h3 h51 hH c hNb hK,
    KLift.inf_centralizer_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK, fun A hA => isMax_inf_sup D Ch h3 h51 hH c hNb i hA,
    P22x.proofIi_le D (preN_le_M D (Nb i)), preN_inf_centralizer_le D Ch h3 h51 hH c hNb i⟩
  refine le_inf ?_ ?_
  · rw [← hb]
    exact Subgroup.commutator_mono ((jOf_le_proofS D).trans le_sup_right) le_rfl
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.1
      (uc22p22sb_proofS_le_centralizer D Ch h2 h3 h51 hH c m Nb hNb i hs)) z hz).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
