module

public import CFSG.RankThree.PartTwo.Sec17.Ronan172ATransport
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofEmpty
import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrderTools
import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofE
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan172A

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {w : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers w) := by
  obtain ⟨k, hk⟩ := hw
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hn, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hk, one_zpow]

theorem mem_centralizer_of_mem_normalizer {F : Subgroup G} (hF : Nat.card F = 3) {w : G}
    (hw : ∃ k : ℕ, w ^ 3 ^ k = 1) (hwF : w ∈ Subgroup.normalizer (F : Set G)) :
    w ∈ Subgroup.centralizer (F : Set G) :=
  Res6Order.le_centralizer_of_card_three (isPGroup_zpowers_of_pow hw) hF
    (Subgroup.zpowers_le.mpr hwF) (Subgroup.mem_zpowers w)

theorem mem_centralizer_of_omega_eq {A B : Subgroup G} {c : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc3 : orderOf c = 3) (hΩ : omegaA A = {Subgroup.zpowers c}) (hB : IsHyperplane A B)
    (hcB : c ∉ B) {w : G} (hwN : w ∈ Subgroup.normalizer (A : Set G))
    (hwB : w ∈ Subgroup.centralizer (B : Set G)) (hw3 : ∃ k : ℕ, w ^ 3 ^ k = 1) :
    w ∈ Subgroup.centralizer (A : Set G) := by
  have hcΩ : Subgroup.zpowers c ∈ omegaA A := hΩ ▸ Set.mem_singleton _
  have hmap : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
    (map_conj_mem_omegaA_iff hwN).mpr hcΩ
  rw [hΩ, Set.mem_singleton_iff] at hmap
  have hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  have hwC := mem_centralizer_of_mem_normalizer hcard hw3 hwc
  have hwcc : w ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hwC c (Subgroup.mem_zpowers c)).symm
  exact mem_centralizer_of_le_sup (le_sup_zpowers_of_not_mem hA hB hcA hcB) hwB hwcc

theorem lB_le_residual_of_omega_eq {A L : Subgroup G} {c : G}
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hLc : L ∈ lA A c)
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) (hcA : c ∈ A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {D : Subgroup G} (hDA : D ≤ A) {b : G}
    (hbD : b ∈ D) :
    lB A D ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  refine iSup_le fun b' => iSup_le fun d' => iSup_le fun Lb => iSup_le fun hcfg => ?_
  obtain ⟨hD, hbΩ, hLb, -, hd'Lb, -⟩ := hcfg
  have hbc : Subgroup.zpowers b' = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    exact hbΩ
  have hLLb : L = Lb := by
    have hL' : L ∈ lA A b' := (Proof1424Steps.lA_eq_of_zpowers_eq hbc) ▸ hLc
    rw [hLb] at hL'
    exact hL'
  subst hLLb
  have hd'D : d' ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton d'))
  have hd'A : d' ∈ A := hDA hd'D
  have hDeq : D = Subgroup.zpowers c ⊔ Subgroup.zpowers d' := by
    rw [hD, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hbc]
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d' : Set G) :=
    Subgroup.zpowers_le.mpr (centralizer_singleton_le_normalizer_zpowers d'
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm c hcA d' hd'A)))
  have hbD' : b ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d' : Subgroup G) : Set G) := by
    rw [← hDeq]
    exact hbD
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hbD'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hbD'
  refine Sec6.inSubgroup_perfectResidual_mono fun l hl => ⟨hl.1, ?_⟩
  have hlc : Commute l c := (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl.1))
  have hld : Commute l d' := (Subgroup.mem_centralizer_singleton_iff.mp hl.2)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((hlc.zpow_right m).mul_right (hld.zpow_right n)).eq

theorem xb172_le_of_omega_eq (hbal : Step143Balance) {A L Y₀ : Subgroup G} {c : G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) {b : G} (hbA : b ∈ A)
    (hb1 : b ≠ 1) (hbc : Subgroup.zpowers b ≠ Subgroup.zpowers c) :
    xb172 A b ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h14 : Sec14Std G A c L := h.toSec14Std
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hcA : c ∈ A := hD13.mem_A
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    exact hbc
  set Cb := Subgroup.centralizer ({b} : Set G) with hCbdef
  set Ob := pPrimeCoreOf 3 Cb with hObdef
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOAdef
  set X := inSubgroup perfectResidual (L ⊓ Cb) with hXdef
  have h3L : 3 ∣ Nat.card L := Sec14.three_dvd_card_of_types148
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Cb :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
  have hΔ : delta A (lB A) Cb ≤ Ob ⊔ OA ⊔ X :=
    Proof17Res9.delta_le_sup_of_lB_le hbal h14 hbA hb1 hbΩ fun D hD hbD =>
      (lB_le_residual_of_omega_eq hΩ hD13.mem_lA hD13.le_centralizer hcA hAcomm hD.1 hbD).trans
        le_sup_right
  have hOAX : OA ≤ Subgroup.normalizer (X : Set G) := by
    have hOAL : OA ≤ Subgroup.normalizer (L : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAc).trans (centralizer_le_normalizer_of_three_dvd h14 h3L)
    have hOACb : OA ≤ Subgroup.normalizer (Cb : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAb).trans Subgroup.le_normalizer
    exact (Late.le_normalizer_inf hOAL hOACb).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hOAOb : OA ≤ Subgroup.normalizer (Ob : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAb).trans (le_normalizer_pPrimeCoreOf 3 Cb)
  have hOAJ : OA ≤ Subgroup.normalizer ((Ob ⊔ X : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hOAOb hOAX
  have hOA3 : ¬ 3 ∣ Nat.card OA :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hO3 : oPrimeResidualOf 3 (delta A (lB A) Cb) ≤ Ob ⊔ X := by
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hyD, k, hyk⟩
    have hy : y ∈ OA ⊔ (Ob ⊔ X) := by
      have := hΔ hyD
      rwa [sup_comm Ob OA, sup_assoc] at this
    exact Proof176Steps.mem_of_three_element_sup hOAJ hOA3 hy hyk
  exact sup_le le_sup_left hO3

theorem le_xb172_c_of_omega_eq (h142 : Item142R) {A L Y₀ : Subgroup G} {c : G}
    (h : Sec17Std G A c L Y₀)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    L ≤ xb172 A c := by
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hcA : c ∈ A := h.toSec13Data.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨-, halt⟩ := h142 G A c L h.toSec15R Qs hQs
  rcases halt with ⟨⟨e⟩, -⟩ | ⟨hKH, -⟩
  · exact ((Proof166Res3.isEmpty_lBarA_l34 h.toSec13Data h.not_l34 hprod).false e).elim
  · have hKH' : delta A (lB A) H = L ⊔ pPrimeCoreOf 3 H ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := hKH
    have hLR : L ≤ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({c} : Set G))) := by
      rw [Proof171Steps.eq_oPrimeResidualOf_of_types h.mem_lA.1
        (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1]
      refine Proof171Steps.oPrimeResidualOf_mono_three ?_
      refine le_trans ?_ (Proof171Steps.delta_normalizer_le hcA hc)
      rw [hKH']
      exact le_sup_of_le_left le_sup_left
    exact hLR.trans le_sup_right

theorem lB_eq_bot_of_a7 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hT : TransOmegaThree A c) (D : Subgroup G) : lB A D = ⊥ := by
  refine lB_eq_bot fun b d Lb hcfg => ?_
  obtain ⟨-, hbΩ, hLb, ⟨ψ⟩, -⟩ := hcfg
  obtain ⟨φ⟩ := h7
  obtain ⟨w, hwN, hbw⟩ := hT.2 _ hbΩ
  have hLw : L.map (MulAut.conj w).toMonoidHom ∈ lA A (w * c * w⁻¹) :=
    (map_conj_mem_lA_iff hwN).mpr hD.mem_lA
  have hzw : Subgroup.zpowers (w * c * w⁻¹) = Subgroup.zpowers b := by
    rw [hbw, MonoidHom.map_zpowers]
    rfl
  rw [Proof1424Steps.lA_eq_of_zpowers_eq hzw, hLb, Set.mem_singleton_iff] at hLw
  have hcardL : Nat.card Lb = Nat.card L := by
    rw [← hLw, Subgroup.card_map_of_injective (MulAut.conj w).injective]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lb)
  rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h1
  rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeJ2] at h2
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  apply hθ3
  have h3 : 2520 * Nat.card (aschbacherSolvableCore 3 ↥L) =
      604800 * Nat.card (CFSG.pCore 2 ↥Lb) := by
    rw [← h1, ← h2, hcardL]
  exact ⟨80 * Nat.card (CFSG.pCore 2 ↥Lb), by omega⟩

theorem map_conj_eq_of_ncard_three {A : Subgroup G} {w : G}
    (hwN : w ∈ Subgroup.normalizer (A : Set G)) (hΩ3 : (omegaA A).ncard = 3)
    {F₀ : Subgroup G} (hF₀ : F₀ ∈ omegaA A) (hwF₀ : F₀.map (MulAut.conj w).toMonoidHom = F₀)
    (hw3 : ∃ k : ℕ, w ^ 3 ^ k = 1) {F : Subgroup G} (hF : F ∈ omegaA A) :
    w ∈ Subgroup.normalizer (F : Set G) := by
  set f : Subgroup G → Subgroup G := fun K => K.map (MulAut.conj w).toMonoidHom with hf
  have hfinj : Function.Injective f := Subgroup.map_injective (MulAut.conj w).injective
  have hfΩ : ∀ K ∈ omegaA A, f K ∈ omegaA A := fun K hK => (map_conj_mem_omegaA_iff hwN).mpr hK
  have hff : f (f F) = F := by
    by_cases hFF₀ : F = F₀
    · rw [hFF₀]
      simp only [hf]
      rw [hwF₀, hwF₀]
    by_cases h1 : f F = F
    · rw [h1, h1]
    by_contra h2
    have hfF₀ : f F ≠ F₀ := fun h => hFF₀ (hfinj (h.trans hwF₀.symm))
    have hffF₀ : f (f F) ≠ F₀ := fun h => hfF₀ (hfinj (h.trans hwF₀.symm))
    have h21 : f (f F) ≠ f F := fun h => h1 (hfinj h)
    have hsub : ({F₀, F, f F, f (f F)} : Set (Subgroup G)) ⊆ omegaA A := by
      intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl | rfl | rfl
      exacts [hF₀, hF, hfΩ _ hF, hfΩ _ (hfΩ _ hF)]
    have hcard : ({F₀, F, f F, f (f F)} : Set (Subgroup G)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h21.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hFF₀ h.symm, fun h => hfF₀ h.symm, fun h => hffF₀ h.symm⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hw2 : w ^ 2 ∈ Subgroup.normalizer (F : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show F.map (MulAut.conj (w ^ 2)).toMonoidHom = F
    rw [pow_two, ← Late.map_conj_map_conj]
    exact hff
  obtain ⟨k, hk⟩ := hw3
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := by
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, hm⟩
  have hw : w = ((w ^ 2) ^ m)⁻¹ := by
    have h1 : w ^ (2 * m + 1) = 1 := by rw [← hm, hk]
    rw [pow_succ, pow_mul] at h1
    exact eq_inv_of_mul_eq_one_right h1
  rw [hw]
  exact inv_mem (Subgroup.pow_mem _ hw2 m)

theorem mem_centralizer_of_a7 (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L)
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hΩ3 : (omegaA A).ncard = 3) {B : Subgroup G} {b : G} (hbB : b ∈ B)
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) {w : G} (hwN : w ∈ Subgroup.normalizer (A : Set G))
    (hwB : w ∈ Subgroup.centralizer (B : Set G)) (hw3 : ∃ k : ℕ, w ^ 3 ^ k = 1) :
    w ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA : c ∈ A := hD.mem_A
  obtain ⟨φ⟩ := h7
  obtain ⟨hcL, h9, -⟩ := Res9A7.exists_sq_inv h131 hD φ
  have hwb : w * b * w⁻¹ = b := by
    rw [← Subgroup.mem_centralizer_iff.mp hwB b hbB, mul_inv_cancel_right]
  have hbfix : (Subgroup.zpowers b).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    show Subgroup.zpowers (w * b * w⁻¹) = Subgroup.zpowers b
    rw [hwb]
  have hcent : ∀ F ∈ omegaA A, w ∈ Subgroup.centralizer (F : Set G) := fun F hF =>
    mem_centralizer_of_mem_normalizer hF.2.1 hw3
      (map_conj_eq_of_ncard_three hwN hΩ3 hbΩ hbfix hw3 hF)
  have hcΩ : Subgroup.zpowers c ∈ omegaA A := hD.zpowers_mem_omegaA
  have h2 : (omegaA A \ {Subgroup.zpowers c}).ncard = 2 := by
    rw [Set.ncard_diff_singleton_of_mem hcΩ, hΩ3]
  obtain ⟨F, F', hFF', hFF⟩ := Set.ncard_eq_two.mp h2
  have hFmem : F ∈ omegaA A \ {Subgroup.zpowers c} := by rw [hFF]; exact Set.mem_insert _ _
  have hF'mem : F' ∈ omegaA A \ {Subgroup.zpowers c} := by
    rw [hFF]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hle : ∀ K ∈ omegaA A \ {Subgroup.zpowers c}, K ≤ A ⊓ L := by
    rintro K ⟨hK, hKc⟩
    obtain ⟨hKA, -, e, hKe, -⟩ := id hK
    subst hKe
    have heL : e ∈ L := Res9A7.mem_of_mem_omegaA h131 hD ⟨φ⟩ hΩ3 hK
      (fun h => hKc (Set.mem_singleton_iff.mpr h))
    exact Subgroup.zpowers_le.mpr ⟨hKA (Subgroup.mem_zpowers e), heL⟩
  have hFL := hle F hFmem
  have hF'L := hle F' hF'mem
  have hF3 : Nat.card F = 3 := hFmem.1.2.1
  have hF'3 : Nat.card F' = 3 := hF'mem.1.2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFN : F ≤ Subgroup.normalizer (F' : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hAcomm y (hF'L hy).1 x (hFL hx).1)
  have hinf : F ⊓ F' = ⊥ := by
    have hdvd : Nat.card ↥(F ⊓ F') ∣ 3 := hF3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hFF'
      have e1 : F ⊓ F' = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hF3])
      have e2 : F ⊓ F' = F' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hF'3])
      exact e1.symm.trans e2
  have hsup9 : Nat.card ↥(F ⊔ F') = 9 := by
    have h := Sec6.card_sup_mul_card_inf hFN
    rw [hinf, Subgroup.card_bot, mul_one, hF3, hF'3] at h
    exact h
  have hAL : F ⊔ F' = A ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (sup_le hFL hF'L) (by rw [hsup9, h9])
  have hwAL : w ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    have hle' : A ⊓ L ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← hAL]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hcent F hFmem.1) x hx)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hcent F' hF'mem.1) x hx)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle' hx)
  have hwc : w ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hcent _ hcΩ) c (Subgroup.mem_zpowers c)).symm
  have hhyp : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9]⟩
  exact mem_centralizer_of_le_sup (le_sup_zpowers_of_not_mem hA hhyp hcA fun h => hcL h.2)
    hwAL hwc

theorem step172PermPt_of_items (h149 : Sec16.Item149S14) (h142 : Item142R) (h175 : Item175R)
    (hbal : Step143Balance) (hMeets : Claim1715Meets) (h131 : Item131) : Step172PermPt := by
  intro G _ _ A c L Y₀ h h1514 B hB g hg b hbB hb1 _ hcb hspecial
  have hS14 : Sec14Std G A c L := h.toSec14Std
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hF3 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A := fun x hx hx3 =>
    Sec4.mem_of_maximal_of_commute hS14.maximal_isElemAbelian hx3 fun a ha =>
      Subgroup.mem_centralizer_iff.mp hx a ha
  have hcA : c ∈ A := hD.mem_A
  have hbA : b ∈ A := hB.1 hbB
  have hle : ∀ x ∈ B, x ≠ 1 → xb172 A x ≤ xB172 A B := fun x hx hx1 =>
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 le_rfl))
  have hconj1 : ∀ {y x : G}, y * x * y⁻¹ = 1 → x = 1 := fun {y x} h1 => by
    have := congrArg (fun z => y⁻¹ * z * y) h1
    simpa [mul_assoc] using this
  have hfin : (∃ u ∈ Subgroup.centralizer (B : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (B : Set G) ∧ g = u * w) →
      (xb172 A b).map (MulAut.conj g).toMonoidHom ≤ xB172 A B := by
    rintro ⟨u, huC, w, hwN, hwB, rfl⟩
    have hwb : w * b * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hwB b).mp hbB
    have hwb1 : w * b * w⁻¹ ≠ 1 := fun h1 => hb1 (hconj1 h1)
    have huN : u ∈ Subgroup.normalizer (xb172 A (w * b * w⁻¹) : Set G) :=
      le_normalizer_xb172 h149 hS14 (hB.1 hwb) hwb1
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwb) huC)
    rw [← Late.map_conj_map_conj, map_conj_xb172 hwN b, Late.map_conj_eq_of_mem_normalizer huN]
    exact hle _ hwb hwb1
  have h15 := h1514 Y₀ h.mem_y0Star (hMeets G A c L Y₀ h)
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  ·
    have hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
      rcases h15 with ⟨-, -, -, hprod, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, -, -, hnot, -⟩
      · exact hprod
      · exfalso
        have h3 := hT.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
      · exact absurd h.le_y0 (hnot Y₀ h.mem_y0Star)
    have hc3 : orderOf c = 3 := hD.orderOf_eq
    by_cases hcB : c ∈ B
    ·
      have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
        have hgcB : g * c * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg c).mp hcB
        have hle' : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
            Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
          rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
          exact Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
            (hD.A_le_centralizer (hB.1 hgcB))
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h175 G A c L h.toSec15R hΩ g hle')
      have h3L : 3 ∣ Nat.card L := Sec14.three_dvd_card_of_types148
        (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
      have hLg : L.map (MulAut.conj g).toMonoidHom = L := Late.map_conj_eq_of_mem_normalizer
        (Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L hgH)
      have hgb : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
      have hgb1 : g * b * g⁻¹ ≠ 1 := fun h1 => hb1 (hconj1 h1)
      refine (Subgroup.map_mono (xb172_le_of_omega_eq hbal h hΩ hbA hb1 (hcb hΩ))).trans ?_
      rw [Subgroup.map_sup, map_pPrimeCoreOf 3 (MulAut.conj g),
        map_centralizer_singleton (MulAut.conj g) b]
      refine sup_le (le_sup_left.trans (hle _ hgb hgb1)) ?_
      calc (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))).map
            (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_left)
        _ = L := hLg
        _ ≤ xb172 A c := le_xb172_c_of_omega_eq h142 h hprod
        _ ≤ xB172 A B := hle c hcB hD.ne_one
    · exact hfin (exists_mul_eq_of_mem_normalizer hAab hA3 hB.1 hF3
        (fun w hwN hwB hw3 => mem_centralizer_of_omega_eq hA hcA hc3 hΩ hB hcB hwN hwB hw3) hg)
  ·
    obtain ⟨h7, -, hT, -⟩ := (h15.resolve_left fun h1 => hΩ h1.2.2.1).resolve_right
      fun h3 => hΩ h3.2.2.2.1
    have hbΩ : Subgroup.zpowers b ∈ omegaA A := by
      rcases hspecial with hbΩ | ⟨H, -, -, hLH⟩
      · exact hbΩ
      · exact absurd (lB_eq_bot_of_a7 hD h7 hT H) hLH
    exact hfin (exists_mul_eq_of_mem_normalizer hAab hA3 hB.1 hF3
      (fun w hwN hwB hw3 => mem_centralizer_of_a7 h131 hD h7 hT.1 hbB hbΩ hwN hwB hw3) hg)

end CFSG.RankThree.PartTwo.Sec17.Ronan172A
