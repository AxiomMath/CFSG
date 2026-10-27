module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import Certificates.Certificate9950
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12Q
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
import CFSG.Sporadic.Mathieu.Simple
import CFSG.RankThree.Asc83Table.PermWords
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res5GenM12

open CFSG.GH74.M12.Hyp (G12 wordP wordP_mem)
open CFSG.Sporadic.Mathieu

@[expose] def w00 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [1, 5] * List.formPerm [2, 9] * List.formPerm [4, 8] *
    List.formPerm [6, 11] * List.formPerm [7, 10]

@[expose] def w01 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 4] * List.formPerm [1, 6] * List.formPerm [2, 10] * List.formPerm [3, 8] *
    List.formPerm [5, 11] * List.formPerm [7, 9]

@[expose] def w10 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 5] * List.formPerm [1, 10] * List.formPerm [2, 8] * List.formPerm [3, 4] *
    List.formPerm [6, 11] * List.formPerm [7, 9]

@[expose] def w11 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6] * List.formPerm [1, 7] * List.formPerm [2, 3] * List.formPerm [4, 8] *
    List.formPerm [5, 11] * List.formPerm [9, 10]

@[expose] def w20 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7] * List.formPerm [1, 4] * List.formPerm [2, 5] * List.formPerm [3, 8] *
    List.formPerm [6, 11] * List.formPerm [9, 10]

@[expose] def w21 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 9] * List.formPerm [1, 8] * List.formPerm [2, 6] * List.formPerm [3, 4] *
    List.formPerm [5, 11] * List.formPerm [7, 10]

@[expose] def wP : Fin 3 → Fin 2 → Equiv.Perm (Fin 12) :=
  ![![w00, w01], ![w10, w11], ![w20, w21]]

@[expose] def wWord : Fin 3 → Fin 2 → List Int :=
  ![![[1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2],
      [-2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2,
        1, 2, 1, 2]],
    ![[1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
        -2],
      [2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2,
        1, 2, 1, 2]],
    ![[1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2,
        1, -2, 1, 2, 1, 2],
      [1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1,
        -2, 1, 2, 1]]]

theorem wP_eq_wordP : ∀ i j, wP i j = wordP (wWord i j) := by
  decide +kernel

theorem wP_mem (i : Fin 3) (j : Fin 2) : wP i j ∈ Blueprint.NativeSporadic.M12 :=
  (wP_eq_wordP i j) ▸ wordP_mem _

@[expose] def wG (i : Fin 3) (j : Fin 2) : G12 := ⟨wP i j, wP_mem i j⟩

theorem wP_facts : ∀ i : Fin 3, wP i 0 * wP i 0 = 1 ∧ wP i 1 * wP i 1 = 1 ∧
    wP i 0 * wP i 1 = wP i 1 * wP i 0 ∧ wP i 0 ≠ 1 ∧ wP i 1 ≠ 1 ∧ wP i 0 ≠ wP i 1 := by
  decide +kernel

theorem wG_sq0 (i : Fin 3) : wG i 0 * wG i 0 = 1 := Subtype.ext (wP_facts i).1

theorem wG_sq1 (i : Fin 3) : wG i 1 * wG i 1 = 1 := Subtype.ext (wP_facts i).2.1

theorem wG_comm (i : Fin 3) : wG i 0 * wG i 1 = wG i 1 * wG i 0 :=
  Subtype.ext (wP_facts i).2.2.1

@[expose] def W (i : Fin 3) : Subgroup G12 :=
  CFSG.LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf (wG i 0) (wG i 1) (wG_sq0 i)
    (wG_sq1 i) (wG_comm i)

theorem card_W (i : Fin 3) : Nat.card (W i) = 4 :=
  CFSG.LocalAnalysis.ComponentInitial.FourGroup.card_kleinFourOf
    (fun h => (wP_facts i).2.2.2.1 (congrArg Subtype.val h))
    (fun h => (wP_facts i).2.2.2.2.1 (congrArg Subtype.val h))
    (fun h => (wP_facts i).2.2.2.2.2 (congrArg Subtype.val h))

@[expose] def xP : Equiv.Perm (Fin 12) :=
  List.formPerm [3, 5, 10] * List.formPerm [4, 6, 7] * List.formPerm [8, 11, 9]

@[expose] def yP : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1, 2] * List.formPerm [5, 11, 6] * List.formPerm [7, 9, 10]

@[expose] def zP : Equiv.Perm (Fin 12) :=
  List.formPerm [3, 4, 8] * List.formPerm [5, 6, 11] * List.formPerm [7, 9, 10]

theorem wordP_wX : wordP Toolkit.M12.wX = xP := by
  decide +kernel

theorem wordP_wY : wordP Toolkit.M12.wY = yP := by
  decide +kernel

theorem commutator_xP_yP : ⁅xP, yP⁆ = zP := by
  decide +kernel

theorem conj_facts_z : ∀ (i : Fin 3) (j : Fin 2),
    zP * wP i j * zP⁻¹ = 1 ∨ zP * wP i j * zP⁻¹ = wP i 0 ∨ zP * wP i j * zP⁻¹ = wP i 1 ∨
      zP * wP i j * zP⁻¹ = wP i 0 * wP i 1 := by
  decide +kernel

theorem conj_facts_xy : ∀ (i : Fin 3) (j : Fin 2),
    (xP * yP) * wP i j * (xP * yP)⁻¹ = 1 ∨ (xP * yP) * wP i j * (xP * yP)⁻¹ = wP i 0 ∨
      (xP * yP) * wP i j * (xP * yP)⁻¹ = wP i 1 ∨
      (xP * yP) * wP i j * (xP * yP)⁻¹ = wP i 0 * wP i 1 := by
  decide +kernel

theorem mem_normalizer_W {i : Fin 3} {t : G12}
    (ht : ∀ j : Fin 2, (t : Equiv.Perm (Fin 12)) * wP i j * (t : Equiv.Perm (Fin 12))⁻¹ = 1 ∨
      (t : Equiv.Perm (Fin 12)) * wP i j * (t : Equiv.Perm (Fin 12))⁻¹ = wP i 0 ∨
      (t : Equiv.Perm (Fin 12)) * wP i j * (t : Equiv.Perm (Fin 12))⁻¹ = wP i 1 ∨
      (t : Equiv.Perm (Fin 12)) * wP i j * (t : Equiv.Perm (Fin 12))⁻¹ = wP i 0 * wP i 1) :
    t ∈ Subgroup.normalizer ((W i : Subgroup G12) : Set G12) := by
  have hgen : ∀ j : Fin 2, t * wG i j * t⁻¹ ∈ W i := by
    intro j
    rcases ht j with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rcases hv with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact (W i).one_mem
  · exact hgen 0
  · exact hgen 1
  · rw [show t * (wG i 0 * wG i 1) * t⁻¹ = (t * wG i 0 * t⁻¹) * (t * wG i 1 * t⁻¹) by group]
    exact mul_mem (hgen 0) (hgen 1)

theorem A_le_normalizer_W (i : Fin 3) :
    Toolkit.M12.A ≤ Subgroup.normalizer ((W i : Subgroup G12) : Set G12) := by
  have hx : ((Toolkit.M12.x : G12) : Equiv.Perm (Fin 12)) = xP := wordP_wX
  have hy : ((Toolkit.M12.y : G12) : Equiv.Perm (Fin 12)) = yP := wordP_wY
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · refine mem_normalizer_W fun j => ?_
    have hz : ((Toolkit.M12.basisA.a : G12) : Equiv.Perm (Fin 12)) = zP := by
      change ⁅((Toolkit.M12.x : G12) : Equiv.Perm (Fin 12)),
        ((Toolkit.M12.y : G12) : Equiv.Perm (Fin 12))⁆ = zP
      rw [hx, hy, commutator_xP_yP]
    rw [hz]
    exact conj_facts_z i j
  · refine mem_normalizer_W fun j => ?_
    have hxy : ((Toolkit.M12.basisA.b : G12) : Equiv.Perm (Fin 12)) = xP * yP := by
      change ((Toolkit.M12.x : G12) : Equiv.Perm (Fin 12)) *
        ((Toolkit.M12.y : G12) : Equiv.Perm (Fin 12)) = xP * yP
      rw [hx, hy]
    rw [hxy]
    exact conj_facts_xy i j

theorem m12gA_eq :
    m12gA = wP 1 0 * wP 1 1 * wP 2 1 * wP 1 0 * wP 2 0 * wP 1 1 * wP 2 0 * wP 2 1 := by
  decide +kernel

theorem m12gB_eq : m12gB =
    wP 0 0 * wP 1 0 * wP 2 1 * wP 1 1 * wP 0 1 * wP 1 0 * wP 0 1 * wP 2 1 * wP 1 0 := by
  decide +kernel

theorem iSup_W_eq_top : ⨆ i, W i = ⊤ := by
  set T := ⨆ i, W i with hT
  have hw : ∀ i j, wG i j ∈ T := by
    intro i j
    refine le_iSup W i ?_
    fin_cases j
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  have ha : m12a ∈ T := by
    have he : m12a = wG 1 0 * wG 1 1 * wG 2 1 * wG 1 0 * wG 2 0 * wG 1 1 * wG 2 0 * wG 2 1 :=
      Subtype.ext m12gA_eq
    rw [he]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hw 1 0) (hw 1 1))
      (hw 2 1)) (hw 1 0)) (hw 2 0)) (hw 1 1)) (hw 2 0)) (hw 2 1)
  have hb : m12b ∈ T := by
    have he : m12b = wG 0 0 * wG 1 0 * wG 2 1 * wG 1 1 * wG 0 1 * wG 1 0 * wG 0 1 * wG 2 1 *
        wG 1 0 := Subtype.ext m12gB_eq
    rw [he]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hw 0 0)
      (hw 1 0)) (hw 2 1)) (hw 1 1)) (hw 0 1)) (hw 1 0)) (hw 0 1)) (hw 2 1)) (hw 1 0)
  rw [eq_top_iff, ← closure_pair_eq_top m12_eq m12a.2 m12b.2, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem sSup_eq_top_of_conj_mem_A {X : Type*} [Group X] (φ : X ≃* G12) {E : Subgroup X}
    {g : G12} (hgE : ∀ x ∈ E, ∃ p ∈ Toolkit.M12.A, g * p * g⁻¹ = φ x) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ :=
  Res5Gen.sSup_eq_top_of_conj_mem φ hgE W (fun i => by rw [card_W]; norm_num)
    A_le_normalizer_W iSup_W_eq_top

variable {G : Type} [Group G] [Finite G]

theorem autIn_perm_three_of_M12
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* G12) :
    Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3)) := by
  have hspor := Sec13.sporadicModels131
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ hspor.2.1.2
  have hnL3 := not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12
  rcases cases131 h131 hspor slTwoCenter h.toSec13Data with ⟨-, -, -, hcase⟩ | ⟨-, -, -, hS3⟩ |
      ⟨-, hPGL, -⟩ | ⟨hcL, -⟩
  · exfalso
    rcases hcase with ⟨hL3, -⟩ | ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
    · exact hnL3 hL3
    · have h1 := Nat.card_congr (ψ.symm.trans φ).toEquiv
      rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1, KFacts.KS14.card_nativeM12] at h1
      norm_num at h1
    · have h1 := Nat.card_congr (ψ.symm.trans φ).toEquiv
      rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeM12] at h1
      norm_num at h1
  · exact hS3
  · exact absurd (facts_of_isZ3PGLThreePi h.toSec13Data hPGL).1 hnL3
  · exact absurd hcL (not_mem_of_center_eq_bot h.toSec13Data hZ)

theorem pow_six_conj_eq {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hS3 : Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3)))
    {n : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hn : n ∈ Subgroup.normalizer
      ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
        Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    {e : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (he : e ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) :
    n ^ 6 * e * (n ^ 6)⁻¹ = e := by
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) n
  have hD := h.toSec13Data
  have hLc := hD.le_centralizer
  have hcA := hD.mem_A
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set P := (A ⊓ L).subgroupOf L with hP
  set Eb := P.map π with hEb
  have hP3 : IsPGroup 3 P := fun x => by
    have hx3 : ((x : L) : G) ^ 3 = 1 := hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2).1
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx3))⟩
  have hEab : ∀ u ∈ Eb, ∀ v ∈ Eb, u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hu).1
      (Subgroup.mem_subgroupOf.mp hv).1)
  obtain ⟨w, hwN, e', he', hsplit⟩ := Sec4.Item424Proof.exists_normalizer_lift hP3 (n := n₀) hn
  have hwAL : ∀ y ∈ A ⊓ L, (w : G) * y * (w : G)⁻¹ ∈ A ⊓ L := by
    intro y hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hwN ⟨y, hy.2⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp h1
  have hwc : ∀ k : ℕ, (w : G) * c ^ k * (w : G)⁻¹ = c ^ k := by
    intro k
    have h1 : Commute (w : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hLc w.2)
    rw [(h1.pow_right k).eq, mul_inv_cancel_right]
  have hwA : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hD.isElemAbelian hcA hAc ha
    rw [show (w : G) * (c ^ k * b) * (w : G)⁻¹ =
      ((w : G) * c ^ k * (w : G)⁻¹) * ((w : G) * b * (w : G)⁻¹) by group, hwc k]
    exact mul_mem (pow_mem hcA k) (hwAL b hb).1
  set τ := A.normalizerMonoidHom ⟨(w : G), hwA⟩ with hτdef
  have hτ : τ ∈ Sec4.autIn L A := Sec4.mem_autIn_iff.mpr ⟨w, hwA, w.2, rfl⟩
  obtain ⟨ψ⟩ := hS3
  have hS6 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide
  have hτ6 : τ ^ 6 = 1 := by
    have h1 : (⟨τ, hτ⟩ : Sec4.autIn L A) ^ 6 = 1 :=
      ψ.injective (by rw [map_pow, hS6, map_one])
    exact congrArg Subtype.val h1
  have hw6 : ∀ β ∈ P, w ^ 6 * β * (w ^ 6)⁻¹ = β := by
    intro β hβ
    have hβA : (β : G) ∈ A := (Subgroup.mem_subgroupOf.mp hβ).1
    have h1 := congrArg (fun σ : MulAut ↥A => ((σ ⟨(β : G), hβA⟩ : ↥A) : G)) hτ6
    simp only [MulAut.one_apply] at h1
    rw [normalizerMonoidHom_pow_apply_val] at h1
    exact Subtype.ext (by simpa using h1)
  have hπwN : π w ∈ Subgroup.normalizer (Eb : Set (↥L ⧸ θ)) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hwN)
  have hagree : ∀ x ∈ Eb, (n₀ : ↥L ⧸ θ) * x * (n₀ : ↥L ⧸ θ)⁻¹ = π w * x * (π w)⁻¹ := by
    intro x hx
    rw [hsplit]
    have hy : π w * x * (π w)⁻¹ ∈ Eb := (Subgroup.mem_normalizer_iff.mp hπwN x).mp hx
    have hw' : ((w : ↥L) : ↥L ⧸ θ) = π w := rfl
    rw [hw']
    calc e' * π w * x * (e' * π w)⁻¹ = e' * (π w * x * (π w)⁻¹) * e'⁻¹ := by group
      _ = (π w * x * (π w)⁻¹) * e' * e'⁻¹ := by rw [hEab e' he' _ hy]
      _ = π w * x * (π w)⁻¹ := by group
  have hiter : ∀ k : ℕ, ∀ x ∈ Eb,
      (n₀ : ↥L ⧸ θ) ^ k * x * ((n₀ : ↥L ⧸ θ) ^ k)⁻¹ = π w ^ k * x * (π w ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hy : π w * x * (π w)⁻¹ ∈ Eb := (Subgroup.mem_normalizer_iff.mp hπwN x).mp hx
      rw [pow_succ, pow_succ]
      calc (n₀ : ↥L ⧸ θ) ^ k * (n₀ : ↥L ⧸ θ) * x * ((n₀ : ↥L ⧸ θ) ^ k * (n₀ : ↥L ⧸ θ))⁻¹ =
            (n₀ : ↥L ⧸ θ) ^ k * ((n₀ : ↥L ⧸ θ) * x * (n₀ : ↥L ⧸ θ)⁻¹) *
              ((n₀ : ↥L ⧸ θ) ^ k)⁻¹ := by group
        _ = (n₀ : ↥L ⧸ θ) ^ k * (π w * x * (π w)⁻¹) * ((n₀ : ↥L ⧸ θ) ^ k)⁻¹ := by
            rw [hagree x hx]
        _ = π w ^ k * (π w * x * (π w)⁻¹) * (π w ^ k)⁻¹ := ih _ hy
        _ = π w ^ k * π w * x * (π w ^ k * π w)⁻¹ := by group
  obtain ⟨β, hβ, rfl⟩ := he
  change (n₀ : ↥L ⧸ θ) ^ 6 * π β * ((n₀ : ↥L ⧸ θ) ^ 6)⁻¹ = π β
  rw [hiter 6 _ ⟨β, hβ, rfl⟩, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hw6 β hβ]

theorem pow_six_conj_ne {t z u : G12} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (htz : t * z * t⁻¹ = u) (htu : t * u * t⁻¹ = z ^ 2) : t ^ 6 * z * (t ^ 6)⁻¹ ≠ z := by
  have hconj : ∀ (s : G12) (k : ℕ), t * s ^ k * t⁻¹ = (t * s * t⁻¹) ^ k := fun s k => by
    rw [conj_pow]
  have h2 : t ^ 2 * z * (t ^ 2)⁻¹ = z ^ 2 := by
    rw [show t ^ 2 * z * (t ^ 2)⁻¹ = t * (t * z * t⁻¹) * t⁻¹ by rw [pow_two]; group, htz, htu]
  have h4 : t ^ 4 * z * (t ^ 4)⁻¹ = z := by
    rw [show t ^ 4 * z * (t ^ 4)⁻¹ = t ^ 2 * (t ^ 2 * z * (t ^ 2)⁻¹) * (t ^ 2)⁻¹ by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; group, h2, ← conj_pow, h2, ← pow_mul,
      show 2 * 2 = 3 + 1 from rfl, pow_succ, hz3, one_mul]
  have h6 : t ^ 6 * z * (t ^ 6)⁻¹ = z ^ 2 := by
    rw [show t ^ 6 * z * (t ^ 6)⁻¹ = t ^ 2 * (t ^ 4 * z * (t ^ 4)⁻¹) * (t ^ 2)⁻¹ by
      rw [show (6 : ℕ) = 2 + 4 from rfl, pow_add]; group, h4, h2]
  rw [h6]
  intro h
  apply hz1
  rw [pow_two] at h
  exact mul_left_cancel (h.trans (mul_one z).symm)

theorem exists_conj_mem_A
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hS3 : Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3)))
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* G12) :
    ∃ g : G12, ∀ x ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      ∃ p ∈ Toolkit.M12.A, g * p * g⁻¹ = φ x := by
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
    with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf h h9
  set T := Eb.map φ.toMonoidHom with hT
  have hT9 : Nat.card T = 9 := by rw [hT, Subgroup.card_map_of_injective φ.injective, hE9]
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_P0_m12 hT3
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hmem : T' ∈ ({Toolkit.M12.E, Toolkit.M12.F, Toolkit.M12.A, Toolkit.M12.A'} :
      Set (Subgroup G12)) := by
    rw [← Toolkit.M12.nine_eq]
    exact ⟨hg, by rw [hT', Subgroup.card_map_of_injective (MulAut.conj g).injective, hT9]⟩
  have hkey : ∀ t : G12, (∀ s ∈ T', t * s * t⁻¹ ∈ T') →
      ∀ s ∈ T', t ^ 6 * s * (t ^ 6)⁻¹ = s := by
    intro t ht s hs
    set n := φ.symm (g⁻¹ * t * g) with hn
    have hnN : n ∈ Subgroup.normalizer (Eb : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have h1 : g * φ x * g⁻¹ ∈ T' := ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨s', ⟨x', hx', hx'e⟩, hs'e⟩ := ht _ h1
      refine (show n * x * n⁻¹ = x' from ?_) ▸ hx'
      apply φ.injective
      have e1 : (MulAut.conj g).toMonoidHom s' = g * s' * g⁻¹ := rfl
      have e2 : φ.toMonoidHom x' = φ x' := rfl
      rw [e1] at hs'e
      rw [e2] at hx'e
      rw [map_mul, map_mul, map_inv, hn, MulEquiv.apply_symm_apply, hx'e]
      calc g⁻¹ * t * g * φ x * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * (g * φ x * g⁻¹) * t⁻¹) * g := by
            group
        _ = g⁻¹ * (g * s' * g⁻¹) * g := by rw [hs'e]
        _ = s' := by group
    obtain ⟨s₀, ⟨x, hx, rfl⟩, rfl⟩ := hs
    have h6 := pow_six_conj_eq h hAc hS3 hnN hx
    have hc : (g⁻¹ * t * g) ^ 6 = g⁻¹ * t ^ 6 * g := by
      have h1 := conj_pow (a := g⁻¹) (b := t) (i := 6)
      rwa [inv_inv] at h1
    have h7 : φ (n ^ 6 * x * (n ^ 6)⁻¹) = φ x := congrArg φ h6
    rw [map_mul, map_mul, map_inv, map_pow, hn, MulEquiv.apply_symm_apply, hc] at h7
    change t ^ 6 * (g * φ x * g⁻¹) * (t ^ 6)⁻¹ = g * φ x * g⁻¹
    calc t ^ 6 * (g * φ x * g⁻¹) * (t ^ 6)⁻¹ =
          g * (g⁻¹ * t ^ 6 * g * φ x * (g⁻¹ * t ^ 6 * g)⁻¹) * g⁻¹ := by group
      _ = g * φ x * g⁻¹ := by rw [h7]
  have hz3 : ⁅Toolkit.M12.x, Toolkit.M12.y⁆ ^ 3 = 1 :=
    Toolkit.M12.cube_of_mem_P0 Toolkit.M12.z_mem_P0
  rcases hmem with hE | hF | hA | hA'
  · exfalso
    obtain ⟨g', hgz, hgx⟩ := Proof1413Res2.exists_conj_E
    have hnorm : ∀ s ∈ T', g' * s * g'⁻¹ ∈ T' := by
      rw [hE]
      intro s hs
      have hN : g' ∈ Subgroup.normalizer (Toolkit.M12.E : Set G12) := by
        refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
        rintro _ (rfl | rfl)
        · change g' * ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * g'⁻¹ ∈ Toolkit.M12.E
          rw [hgz]
          exact Toolkit.M12.x_mem_E
        · change g' * Toolkit.M12.x * g'⁻¹ ∈ Toolkit.M12.E
          rw [hgx]
          exact pow_mem (Toolkit.M12.z_mem_sub 0) 2
      exact (Subgroup.mem_normalizer_iff.mp hN s).mp hs
    exact pow_six_conj_ne hz3 Toolkit.M12.z_ne_one hgz hgx
      (hkey g' hnorm _ (hE ▸ Toolkit.M12.z_mem_sub 0))
  · exfalso
    obtain ⟨g', hgz, hgy⟩ := Proof1413Res2.exists_conj_F
    have hnorm : ∀ s ∈ T', g' * s * g'⁻¹ ∈ T' := by
      rw [hF]
      intro s hs
      have hN : g' ∈ Subgroup.normalizer (Toolkit.M12.F : Set G12) := by
        refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
        rintro _ (rfl | rfl)
        · change g' * ⁅Toolkit.M12.x, Toolkit.M12.y⁆ * g'⁻¹ ∈ Toolkit.M12.F
          rw [hgz]
          exact Toolkit.M12.y_mem_F
        · change g' * Toolkit.M12.y * g'⁻¹ ∈ Toolkit.M12.F
          rw [hgy]
          exact pow_mem (Toolkit.M12.z_mem_sub 1) 2
      exact (Subgroup.mem_normalizer_iff.mp hN s).mp hs
    exact pow_six_conj_ne hz3 Toolkit.M12.z_ne_one hgz hgy
      (hkey g' hnorm _ (hF ▸ Toolkit.M12.z_mem_sub 1))
  · refine ⟨g⁻¹, fun x hx => ⟨g * φ x * g⁻¹, ?_, by group⟩⟩
    rw [← hA]
    exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
  · refine ⟨(Toolkit.M12.g0 * g)⁻¹, fun x hx => ⟨(Toolkit.M12.g0 * g) * φ x *
      (Toolkit.M12.g0 * g)⁻¹, ?_, by group⟩⟩
    rw [← Toolkit.M12.map_g0_A', ← hA']
    refine ⟨g * φ x * g⁻¹, ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    change Toolkit.M12.g0 * (g * φ x * g⁻¹) * Toolkit.M12.g0⁻¹ =
      Toolkit.M12.g0 * g * φ x * (Toolkit.M12.g0 * g)⁻¹
    group

end Res5GenM12

open Res5Gen Res5GenM12 in
theorem step142LowerGenM12_of
    (h131 : Item131) :
    Step142LowerGenM12 := by
  intro G _ _ A c L h ⟨φ⟩
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.2.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12)
  obtain ⟨g, hg⟩ := exists_conj_mem_A h hAc h9 (autIn_perm_three_of_M12 h131 h φ) φ
  exact sSup_autThetaQuot_eq_top_of_inner h hAc (sSup_eq_top_of_conj_mem_A φ hg)

end CFSG.RankThree.PartTwo.Sec14
