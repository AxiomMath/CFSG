module

public import CFSG.RankThree.PartOne.K133.Lift
public import CFSG.RankThree.PartOne.K133.Count
public import CFSG.RankThree.PartOne.K133.Union
public import CFSG.RankThree.PartOne.K133.Two
public import CFSG.RankThree.PartOne.K133.ParA
public import CFSG.RankThree.PartOne.K133.ParAFix
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_thetaQuotientCentralizer_of_rel {p : ℕ} {E I J : Subgroup G} {b : G} (hbE : b ∈ E)
    (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hJb : J ≤ Subgroup.centralizer ({b} : Set G)) (hIJ : sectionTenRel p I J) :
    b ∈ thetaQuotientCentralizer p E I := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hbE, hEI hbE, fun y hy => ?_⟩
  have hy' : y ∈ ((I ⊓ J : Subgroup G) : Set G) *
      (inSubgroup (aschbacherSolvableCore p) I : Set G) := by
    rw [← sectionTenRel_iff.1 hIJ]
    exact hy
  obtain ⟨j, hj, n, hn, rfl⟩ := hy'
  have hjb : j * b = b * j :=
    Subgroup.mem_centralizer_singleton_iff.1 (hJb (Subgroup.mem_inf.1 hj).2)
  have hbj : b * j * b⁻¹ = j := by rw [← hjb]; group
  have hbn : b * n * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I :=
    theta_conj_mem_of_normalizer p I (hEI hbE) hn
  have hkey : b * (j * n) * b⁻¹ * (j * n)⁻¹ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by
    calc b * (j * n) * b⁻¹ * (j * n)⁻¹
        = (b * j * b⁻¹) * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by group
      _ = j * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by rw [hbj]
      _ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by group
  rw [hkey]
  exact theta_conj_mem p I (Subgroup.mem_inf.1 hj).1
    ((inSubgroup (aschbacherSolvableCore p) I).mul_mem hbn
      ((inSubgroup (aschbacherSolvableCore p) I).inv_mem hn))

theorem moves_not_mem {p : ℕ} {E I : Subgroup G} {b : G} (hmov : MovesTwoQuot p I b) :
    b ∉ thetaQuotientCentralizer p E I := by
  intro hbD
  obtain ⟨hbN, Sq, -, -, x, -, hxm⟩ := hmov
  have hone : thetaQuotientConj p I ⟨b, hbN⟩ = 1 :=
    (thetaQuotientConj_eq_one_iff p I ⟨b, hbN⟩).2 (mem_thetaQuotientCentralizer_iff.1 hbD).2.2
  apply hxm
  rw [hone]
  rfl

@[expose] def KF133ResNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      c ∉ thetaQuotientCentralizer p E I →
      (p ^ 2 ∣ Nat.card (thetaQuotientCentralizer p E I) ∧ ∃ b ∈ E, MovesTwoQuot p I b) ∨
      (thetaQuotientCentralizer p E I ≤ Subgroup.zpowers e ∧
        ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ e ∈ B ∧ I ∈ sectionTenZero p B)

theorem kf133TwoNe_of_res (hS : SchreierFor InCatalog)
    (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) (hRes : KF133ResNe) : KF133TwoNe := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK e he he1 I hI hKI
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  have : Fact p.Prime := ⟨hp⟩
  have heE : e ∈ E := (Subgroup.map_subtype_le _) he
  have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpowE : ∀ x ∈ E, x ^ p = 1 := fun x hx => by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  have hmemD : e ∈ thetaQuotientCentralizer p E I := by
    rw [mem_thetaQuotientCentralizer_iff]
    refine ⟨heE, hEI heE, fun k hk => ?_⟩
    have hke : k * e = e * k := Subgroup.mem_centralizer_singleton_iff.1
      ((mem_thetaComponentsAt_iff.1 hI).1 hk)
    have : e * k * e⁻¹ * k⁻¹ = 1 := by rw [← hke]; group
    rw [this]
    exact Subgroup.one_mem _
  have hadm : ∀ {B : Subgroup G}, B ≤ E → Nat.card B = p ^ 3 → I ∈ sectionTenZero p B →
      B ∈ admissibleTriples p E := by
    intro B hBE hBcard hIB
    obtain ⟨-, S, -, hS1, hS2, hSB, -⟩ := hIB
    exact ⟨hBE, isElementaryAbelian_of_le h.E_elem hBE, hBcard, S, hS1, hS2, hSB⟩
  by_cases hcD : c ∈ thetaQuotientCentralizer p E I
  ·
    have hKq : CFSG.IsQuasisimple ↥K := by
      obtain ⟨-, r, hr1, hr12, hrow, -, hrA, hr9⟩ := hF.three
      have hr9' : 9 ≤ r := by
        by_contra hlt
        exact hEA (hrA (by omega))
      obtain ⟨f, -, hKR, -⟩ :=
        hTypes r hr9' hr12 G p A c L E h hF hF13 hT hrow hrA hr9 t ht htL K hK
      have hmod : StatedClassicalModel ↥K .PSL 2 2 f := by
        interval_cases r <;> exact hKR
      exact S15K.isQuasisimple_of_model hmod
    exact ⟨L, hF13.inZeroStar, sectionTenRel_of_trivial_action_fix hS h hKq.1
      (Sec125.ne_bot_of_isQuasisimple hKq) (hF13.kt_le L hF13.inZeroStar t ht htL K hK) he1 heE hI
      hKI (Subgroup.map_subtype_le _ : autFixedInG E t ≤ E) (isKt_le_centralizer_fixed hK)
      (isKt_centralizes_fixed_theta hp hK he) (commutator_zpowers_le_theta hcD)⟩
  rcases hRes G p A c L E h hF hF13 hT hEA t ht htL K hK e he he1 I hI hKI hcD with
    ⟨hD2, b, hbE, hmov⟩ | ⟨hDe, B, hBE, hBcard, heB, hIB⟩
  ·
    obtain ⟨T, hTI, hT1, hT2, hPT, hTc⟩ := exists_invariant_two_subgroup hp hp2 h.E_elem hbE hmov
    set D := thetaQuotientCentralizer p E I with hD
    have hDE : D ≤ E := fun d hd => (mem_thetaQuotientCentralizer_iff.1 hd).1
    have hbD : b ∉ D := moves_not_mem hmov
    have hb1 : b ≠ 1 := fun h1 => hbD (h1 ▸ D.one_mem)
    have hbord : orderOf b = p := orderOf_eq_prime (hpowE b hbE) hb1
    have heord : orderOf e = p := orderOf_eq_prime (hpowE e heE) he1
    have hclaim : ∀ b'' ∈ D, ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ e ∈ B ∧ b'' ∈ B ∧
        I ∈ sectionTenZero p B := by
      intro b'' hb''
      obtain ⟨a, ha2, hX0⟩ : ∃ a, a ≤ 2 ∧
          Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers b'') = p ^ a := by
        by_cases hbe : b'' ∈ Subgroup.zpowers e
        · refine ⟨1, by norm_num, ?_⟩
          have : Subgroup.zpowers e ⊔ Subgroup.zpowers b'' = Subgroup.zpowers e :=
            sup_eq_left.2 (Subgroup.zpowers_le.2 hbe)
          rw [this, Nat.card_zpowers, heord, pow_one]
        · have hb1' : b'' ≠ 1 := fun h1 => hbe (h1 ▸ Subgroup.one_mem _)
          have hbord' : orderOf b'' = p := orderOf_eq_prime (hpowE b'' (hDE hb'')) hb1'
          refine ⟨2, le_rfl, ?_⟩
          rw [card_sup_zpowers hp hbord' (fun y hy => hcommE y ((Subgroup.zpowers_le.2 heE) hy) b''
            (hDE hb'')) hbe, Nat.card_zpowers, heord]
          ring
      obtain ⟨D2, hXD2, hD2D, hD2card⟩ := exists_subgroup_card_between hp
        (sup_le (Subgroup.zpowers_le.2 hmemD) (Subgroup.zpowers_le.2 hb'')) hX0 ha2 hD2
      have hbD2 : b ∉ D2 := fun hb2 => hbD (hD2D hb2)
      have hBcard : Nat.card ↥(D2 ⊔ Subgroup.zpowers b) = p ^ 3 := by
        rw [card_sup_zpowers hp hbord (fun y hy => hcommE y (hDE (hD2D hy)) b hbE) hbD2, hD2card]
        ring
      have hBsub : D2 ⊔ Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ D :=
        sup_le (hD2D.trans le_sup_right) le_sup_left
      have hBN : D2 ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (T : Set G) := hBsub.trans hPT
      refine ⟨D2 ⊔ Subgroup.zpowers b, sup_le (hD2D.trans hDE) (Subgroup.zpowers_le.2 hbE), hBcard,
        Subgroup.mem_sup_left (hXD2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers e))),
        Subgroup.mem_sup_left (hXD2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers b''))), ?_⟩
      refine ⟨mem_thetaComponentFamily_iff.2 ⟨e, ?_, he1, hI⟩, T, hTI, hT1, hT2, hBN, ?_⟩
      · exact Subgroup.mem_sup_left (hXD2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)))
      · refine le_antisymm ?_ (Subgroup.le_normalizer_iff_commutator_le_left.1 hBN)
        calc T = ⁅T, Subgroup.zpowers b⁆ := hTc.symm
          _ ≤ ⁅T, D2 ⊔ Subgroup.zpowers b⁆ := Subgroup.commutator_mono le_rfl le_sup_right
    obtain ⟨B0, hB0E, hB0card, heB0, -, hIB0⟩ := hclaim e hmemD
    have hIU : I ∈ thetaCompE p E :=
      ⟨B0, hadm hB0E hB0card hIB0, mem_thetaComponentFamily_iff.2 ⟨e, heB0, he1, hI⟩⟩
    refine exists_zeroStar_above_E hS h hIU (fun b'' hb'' _ J hJ hIJ => ?_)
    have hb''D := mem_thetaQuotientCentralizer_of_rel hb'' hEI (mem_thetaComponentsAt_iff.1 hJ).1 hIJ
    obtain ⟨B, hBE, hBcard, -, hb''B, hIB⟩ := hclaim b'' hb''D
    exact ⟨B, hBE, hBcard, hb''B, hIB⟩
  ·
    have hIU : I ∈ thetaCompE p E :=
      ⟨B, hadm hBE hBcard hIB, mem_thetaComponentFamily_iff.2 ⟨e, heB, he1, hI⟩⟩
    refine exists_zeroStar_above_E hS h hIU (fun b hb _ J hJ hIJ => ⟨B, hBE, hBcard, ?_, hIB⟩)
    have hbD := mem_thetaQuotientCentralizer_of_rel hb hEI (mem_thetaComponentsAt_iff.1 hJ).1 hIJ
    exact (Subgroup.zpowers_le.2 heB) (hDe hbD)

end CFSG.RankThree.PartOne.K133
