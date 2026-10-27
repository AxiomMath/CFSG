module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2Proof1420
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut thetaQuotMulAut_mk InducesTypeOn
  normalizerMonoidHom_apply_coe)
open scoped commutatorElement Pointwise

namespace Proof1413Res5

variable {G : Type} [Group G] [Finite G]

theorem transOn_of_le_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {V Y : Subgroup G}
    (hYQ : Y ∈ scriptQ A LB) (hYV : Y ≤ V) (hle : ∀ R ∈ scriptQPi A LB V (piOf 2), R ≤ Y) :
    TransOn A LB (xA A) V := by
  have hsub : ∀ S ∈ scriptQPiStar A LB V (piOf 2), S ∈ scriptQPiStar A LB Y (piOf 2) := by
    intro S hS
    refine ⟨⟨⟨hS.prop.1.1, hle S hS.prop⟩, hS.prop.2⟩, fun T hT hST => ?_⟩
    exact hS.2 ⟨⟨hT.1.1, hT.1.2.trans hYV⟩, hT.2⟩ hST
  intro S hS T hT
  obtain ⟨x, hx, hxT⟩ := transOn_of_mem_scriptQ hA hbot hYQ S (hsub S hS) T (hsub T hT)
  exact ⟨x, ⟨(Subgroup.mem_inf.mp hx).1, hYV (Subgroup.mem_inf.mp hx).2⟩, hxT⟩

theorem isConjIn_of_le_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {Y Z : Subgroup G}
    (hZQ : Z ∈ scriptQ A LB) (hZY : Z ≤ Y) {S T : Subgroup G}
    (hS : S ∈ scriptQPiStar A LB Y (piOf 2)) (hT : T ∈ scriptQPiStar A LB Y (piOf 2))
    (hSZ : S ≤ Z) (hTZ : T ≤ Z) : IsConjIn (xA A ⊓ Y) S T := by
  have hsub : ∀ U ∈ scriptQPiStar A LB Y (piOf 2), U ≤ Z →
      U ∈ scriptQPiStar A LB Z (piOf 2) := by
    intro U hU hUZ
    refine ⟨⟨⟨hU.prop.1.1, hUZ⟩, hU.prop.2⟩, fun V hV hUV => ?_⟩
    exact hU.2 ⟨⟨hV.1.1, hV.1.2.trans hZY⟩, hV.2⟩ hUV
  obtain ⟨x, hx, hxT⟩ :=
    transOn_of_mem_scriptQ hA hbot hZQ S (hsub S hS hSZ) T (hsub T hT hTZ)
  exact ⟨x, ⟨(Subgroup.mem_inf.mp hx).1, hZY (Subgroup.mem_inf.mp hx).2⟩, hxT⟩

theorem mem_theta_of_conj_mem {L : Subgroup G} {w : G}
    (hwN : w ∈ Subgroup.normalizer (L : Set G))
    (hfix : ∀ u : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) u = u → u ^ 2 = 1 → u = 1)
    {t : G} (htL : t ∈ L) {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (hwt : w * t * w⁻¹ * t⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    t ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  set σ := thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) with hσ
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set u : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ t' with hu
  have hσu : σ u = u := by
    rw [hσ, hu, QuotientGroup.mk'_apply, thetaQuotMulAut_mk, QuotientGroup.eq_iff_div_mem]
    obtain ⟨y, hy, hyeq⟩ := hwt
    have : L.normalizerMonoidHom ⟨w, hwN⟩ t' / t' = y := by
      apply Subtype.ext
      rw [show (y : G) = w * t * w⁻¹ * t⁻¹ from hyeq]
      simp [div_eq_mul_inv, ht']
    rw [this]
    exact hy
  have huk : u ^ 2 ^ k = 1 := by
    have h1 : t' ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    rw [hu, ← map_pow, h1, map_one]
  have key : ∀ m : ℕ, ∀ v, σ v = v → v ^ 2 ^ m = 1 → v = 1 := by
    intro m
    induction m with
    | zero => intro v _ hv; simpa using hv
    | succ m ih =>
      intro v hv hvm
      refine ih v hv (hfix _ (by rw [map_pow, hv]) ?_)
      rw [← pow_mul, ← pow_succ]
      exact hvm
  have hu1 := key k u hσu huk
  exact ⟨t', (QuotientGroup.eq_one_iff t').mp hu1, rfl⟩

theorem pow_apply_eq_of_apply_eq {X : Type*} [Group X] {σ : MulAut X} {u : X} (hu : σ u = u)
    (n : ℕ) : (σ ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hu, ih]

theorem fix_of_not_mem_sup {A L : Subgroup G} {c d x a : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hcA : c ∈ A) (hdA : d ∈ A)
    (hxA : x ∈ A) (haA : a ∈ A) (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9)
    (hx : InducesTypeOn L x 3) (hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (ha : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ∀ u : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, hAN haA⟩) u = u → u ^ 2 = 1 → u = 1 := by
  intro u hu hu2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨i, j, m, hm3, hxeq⟩ := Proof142Res.exists_pow_mul_eq hA h27 hcA hdA haA h9 ha hxA
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hxd : x * d = d * x := hcomm x hxA d hdA
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hxcd
    rw [hxeq, pow_zero, mul_one]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers d j))
  have ham : a ^ m = x * d ^ (-j) * c ^ (-i) := by
    rw [hxeq]
    have h1 : c ^ i * d ^ j * a ^ m * d ^ (-j) * c ^ (-i) =
        (c ^ i * c ^ (-i)) * (d ^ j * d ^ (-j)) * a ^ m := by
      have hc1 : Commute (c ^ (-i)) (a ^ m) := Commute.zpow_left
        ((Commute.pow_right (hcomm c hcA a haA) m)) (-i)
      have hc2 : Commute (d ^ (-j)) (a ^ m) := Commute.zpow_left
        ((Commute.pow_right (hcomm d hdA a haA) m)) (-j)
      calc c ^ i * d ^ j * a ^ m * d ^ (-j) * c ^ (-i) =
          c ^ i * d ^ j * (a ^ m * d ^ (-j)) * c ^ (-i) := by group
        _ = c ^ i * d ^ j * (d ^ (-j) * a ^ m) * c ^ (-i) := by rw [hc2.eq]
        _ = c ^ i * (d ^ j * d ^ (-j)) * (a ^ m * c ^ (-i)) := by group
        _ = c ^ i * (d ^ j * d ^ (-j)) * (c ^ (-i) * a ^ m) := by rw [hc1.eq]
        _ = c ^ i * ((d ^ j * d ^ (-j)) * c ^ (-i)) * a ^ m := by group
        _ = c ^ i * (c ^ (-i) * (d ^ j * d ^ (-j))) * a ^ m := by
          rw [← zpow_add, add_neg_cancel, zpow_zero, mul_one, one_mul]
        _ = (c ^ i * c ^ (-i)) * (d ^ j * d ^ (-j)) * a ^ m := by group
    rw [h1, ← zpow_add, ← zpow_add, add_neg_cancel, add_neg_cancel, zpow_zero, zpow_zero,
      one_mul, one_mul]
  have hzN : x * d ^ (-j) ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (hAN hxA) (Subgroup.zpow_mem _ (hAN hdA) _)
  have hckN : c ^ (-i) ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ (hAN hcA) _
  have hσc : thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ (-i), hckN⟩) = 1 :=
    Proof142Res.thetaQuotMulAut_eq_one_of_commute hckN fun l hl =>
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)) (-i)).eq
  have hamN : a ^ m ∈ Subgroup.normalizer (L : Set G) := pow_mem (hAN haA) m
  have hσam : thetaQuotMulAut L (L.normalizerMonoidHom ⟨a ^ m, hamN⟩) =
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨x * d ^ (-j), hzN⟩) := by
    have e1 : (⟨a ^ m, hamN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨x * d ^ (-j), hzN⟩ * ⟨c ^ (-i), hckN⟩ := Subtype.ext ham
    rw [e1, map_mul, map_mul, hσc, mul_one]
  have hu' : thetaQuotMulAut L (L.normalizerMonoidHom ⟨a ^ m, hamN⟩) u = u := by
    have e2 : (⟨a ^ m, hamN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, hAN haA⟩ ^ m :=
      Subtype.ext (by simp)
    rw [e2, map_pow, map_pow]
    exact pow_apply_eq_of_apply_eq hu m
  rw [hσam] at hu'
  exact Sec16.Proof1613Fix.fix_of_type3 hdL hd3 hd1 hxd hx (-j) hzN u hu' hu2

theorem mem_theta_of_mem_sup {Γ : Type*} [Group Γ] [Finite Γ] {Y S : Subgroup Γ} {x : Γ}
    (hxS : x ∈ S) {ρ : Γ}
    (hρ : ρ ∈ inSubgroup (aschbacherSolvableCore 3) (Y ⊓ Subgroup.centralizer {x}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Y ⊓ Subgroup.centralizer (S : Set Γ)))
    (hρS : ρ ∈ Subgroup.centralizer (S : Set Γ)) :
    ρ ∈ inSubgroup (aschbacherSolvableCore 3) (Y ⊓ Subgroup.centralizer (S : Set Γ)) := by
  set Y₁ := Y ⊓ Subgroup.centralizer {x} with hY₁
  set Y₂ := Y ⊓ Subgroup.centralizer (S : Set Γ) with hY₂
  set M := inSubgroup (aschbacherSolvableCore 3) Y₁ with hM
  set N := inSubgroup (aschbacherSolvableCore 3) Y₂ with hN
  have hCS : Subgroup.centralizer (S : Set Γ) ≤ Subgroup.centralizer {x} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxS)
  have hY₂₁ : Y₂ ≤ Y₁ := inf_le_inf_left Y hCS
  have hMY : M ≤ Y₁ := Subgroup.map_subtype_le _
  have hNY : N ≤ Y₂ := Subgroup.map_subtype_le _
  have hY₁M : Y₁ ≤ Subgroup.normalizer (M : Set Γ) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta Y₁)
  have hNM : N ≤ Subgroup.normalizer (M : Set Γ) := (hNY.trans hY₂₁).trans hY₁M
  have hρ' : ρ ∈ (M : Set Γ) * (N : Set Γ) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M N hNM]
    exact hρ
  obtain ⟨m, hm, n, hn, rfl⟩ := hρ'
  have hnS : n ∈ Subgroup.centralizer (S : Set Γ) := (hNY hn).2
  have hmS : m ∈ Subgroup.centralizer (S : Set Γ) := by
    have h1 : m = (m * n) * n⁻¹ := by group
    rw [h1]
    exact mul_mem hρS (inv_mem hnS)
  obtain ⟨hMs, hM3⟩ := Sec6.theta_solvable_and_not_dvd Y₁
  have hle : M ⊓ Subgroup.centralizer (S : Set Γ) ≤ Y₂ :=
    le_inf ((inf_le_left.trans hMY).trans inf_le_left) inf_le_right
  have hnorm : Y₂ ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (S : Set Γ) : Subgroup Γ) : Set Γ) :=
    le_normalizer_inf (hY₂₁.trans hY₁M)
      (inf_le_right.trans Subgroup.le_normalizer)
  have hsol : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer (S : Set Γ)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (S : Set Γ)) := fun h =>
    hM3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hmN : m ∈ N := Sec6.le_theta_of_normal hle hnorm hsol h3 ⟨hm, hmS⟩
  exact mul_mem hmN hn

theorem not_three_dvd_pCoreOf (X : Subgroup G) : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 X) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)

structure Pt142 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  std : Sec14Std G A c L
  eq_k : k142 A (lB A) c =
    L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))

namespace Pt142

variable {A L : Subgroup G} {c : G} (P : Pt142 A c L)
include P

theorem l_le : L ≤ k142 A (lB A) c := by
  rw [P.eq_k]
  exact le_sup_left.trans le_sup_left

theorem x_le : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ k142 A (lB A) c := by
  rw [P.eq_k]
  exact le_sup_right

theorem k_le_centralizer : k142 A (lB A) c ≤ Subgroup.centralizer ({c} : Set G) := by
  have hD := P.std.toSec13Data
  refine sSup_le fun Q hQ => ?_
  exact le_centralizer_of_le_normalizer_zpowers (Late.isE27_of_mem_partTwoE hD.mem_partTwoE)
    hD.mem_A hQ.1 hQ.2

theorem three_dvd : 3 ∣ Nat.card L :=
  three_dvd_card_of_types148 (P.std.chosen136.2 c P.std.toSec13Data.zpowers_mem_omegaA L
    P.std.toSec13Data.mem_lA).1

theorem k_le_normalizer : k142 A (lB A) c ≤ Subgroup.normalizer (L : Set G) :=
  P.k_le_centralizer.trans (centralizer_le_normalizer_of_three_dvd P.std P.three_dvd)

theorem theta_le :
    inSubgroup (aschbacherSolvableCore 3) L ≤ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans P.l_le)
    (P.k_le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3

theorem mem_theta_of_mem (hspor : SporadicModels131) {g : G}
    (hgO : g ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) (hgL : g ∈ L) :
    g ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have h := Item148PtRes2.inf_le_theta hspor P.std (not_three_dvd_pCoreOf _)
    (P.l_le.trans (le_normalizer_pPrimeCoreOf 3 _))
    ((pPrimeCoreOf_le 3 _).trans P.k_le_centralizer)
  exact ⟨⟨g, hgL⟩, h (Subgroup.mem_subgroupOf.mpr hgO), rfl⟩

theorem sup_le_normalizer :
    pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c ≤
      Subgroup.normalizer (L : Set G) :=
  sup_le ((pPrimeCoreOf_le 3 _).trans P.k_le_normalizer)
    (Subgroup.zpowers_le.mpr (P.std.toSec13Data.le_normalizer P.std.toSec13Data.mem_A))

theorem le_normalizer_sup :
    L ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c : Subgroup G) : Set G) :=
  Proof142Res.le_normalizer_sup_of (P.l_le.trans (le_normalizer_pPrimeCoreOf 3 _))
    (P.std.toSec13Data.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))

theorem commutator_mem_theta (hspor : SporadicModels131) {k l : G}
    (hk : k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) (hl : l ∈ L) :
    k * l * k⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  refine P.mem_theta_of_mem hspor ?_ ?_
  · have h1 : l * k⁻¹ * l⁻¹ ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (P.le_normalizer_sup hl) _).mp (inv_mem hk)
    rw [show k * l * k⁻¹ * l⁻¹ = k * (l * k⁻¹ * l⁻¹) by group]
    exact mul_mem hk h1
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (P.sup_le_normalizer hk) l).mp hl) (inv_mem hl)

theorem zpow_eq_one_of_mem (hspor : SporadicModels131) {i : ℤ}
    (hci : c ^ i ∈ k142 A (lB A) c) : c ^ i = 1 := by
  have hD := P.std.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set OK := pPrimeCoreOf 3 K with hOK
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  have hKH : K ≤ H := delta_le _
  have hOHK : pPrimeCoreOf 3 H ≤ K := by
    rw [hKdef, P.eq_k]
    exact le_sup_right.trans le_sup_left
  have hOH : pPrimeCoreOf 3 H ≤ OK :=
    le_pPrimeCoreOf hOHK (hKH.trans (le_normalizer_pPrimeCoreOf 3 H))
      (coprime_card_pPrimeCoreOf 3 H)
  have hK' : K ≤ L ⊔ OK ⊔ X :=
    P.eq_k.le.trans (sup_le_sup_right (sup_le_sup_left hOH L) X)
  have hKN : K ≤ Subgroup.normalizer (OK : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hXN : X ≤ Subgroup.normalizer ((L ⊔ OK : Subgroup G) : Set G) :=
    Proof142Res.le_normalizer_sup_of (P.x_le.trans P.k_le_normalizer) (P.x_le.trans hKN)
  have hLN : L ≤ Subgroup.normalizer (OK : Set G) := P.l_le.trans hKN
  have hci' : c ^ i ∈ ((L ⊔ OK : Subgroup G) : Set G) * (X : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (L ⊔ OK) X hXN]
    exact hK' hci
  obtain ⟨m, hm, y, hy, hmy⟩ := hci'
  have hyc : Commute y (c ^ i) := by
    have h1 : c * y = y * c :=
      Subgroup.mem_centralizer_iff.mp ((pPrimeCoreOf_le 3 _) hy) c hD.mem_A
    exact (Commute.zpow_right h1.symm i)
  set n := Nat.card X with hn
  have hn3 : ¬ 3 ∣ n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hyn : y ^ n = 1 := by
    have h1 : (⟨y, hy⟩ : X) ^ n = 1 := pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  have hmeq : m = c ^ i * y⁻¹ := by rw [← hmy]; group
  have hcin : c ^ (i * n) ∈ L ⊔ OK := by
    have h1 : m ^ n = c ^ (i * n) := by
      rw [hmeq, (hyc.symm.inv_right).mul_pow, inv_pow, hyn, inv_one, mul_one, ← zpow_natCast,
        ← zpow_mul]
    rw [← h1]
    exact pow_mem hm n
  have hcin' : c ^ (i * n) ∈ (L : Set G) * (OK : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L OK hLN]
    exact hcin
  obtain ⟨l, hl, o, ho, hlo⟩ := hcin'
  have hlO : l ∈ OK ⊔ Subgroup.zpowers c := by
    rw [show l = c ^ (i * n) * o⁻¹ by rw [← hlo]; group]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c _))
      (Subgroup.mem_sup_left (inv_mem ho))
  have hlOK : l ∈ OK := P.theta_le (P.mem_theta_of_mem hspor hlO hl)
  have hcOK : c ^ (i * n) ∈ OK := hlo ▸ mul_mem hlOK ho
  have hc3 : orderOf c = 3 := hD.orderOf_eq
  have hcin1 : c ^ (i * n) = 1 := by
    by_contra hne
    have h3 : (c ^ (i * n)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show c ^ 3 = 1 from hc3 ▸ pow_orderOf_eq_one c, one_zpow]
    have ho3 : orderOf (c ^ (i * n)) = 3 := orderOf_eq_prime h3 hne
    exact not_three_dvd_pCoreOf _ (ho3 ▸ Subgroup.orderOf_dvd_natCard OK hcOK)
  have h3in : (3 : ℤ) ∣ i * n := by
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr hcin1
    rw [hc3] at h1
    exact_mod_cast h1
  have h3i : (3 : ℤ) ∣ i := by
    rcases Int.prime_three.dvd_or_dvd h3in with h | h
    · exact h
    · exact absurd (Int.natCast_dvd_natCast.mp h) hn3
  rw [← orderOf_dvd_iff_zpow_eq_one, hc3]
  exact_mod_cast h3i

theorem mem_pCore_of_mem (hspor : SporadicModels131) {k : G} (hk : k ∈ k142 A (lB A) c)
    (hker : k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) :
    k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (OK : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hoc : Commute o c :=
      Subgroup.mem_centralizer_singleton_iff.mp ((pPrimeCoreOf_le 3 K).trans
        P.k_le_centralizer ho)
    rw [hoc.symm.eq, mul_inv_cancel_right]
    exact ho
  have hx : k ∈ (OK : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OK _ hcN]
    exact hker
  obtain ⟨o, ho, z, hz, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzK : c ^ i ∈ K := by
    rw [show c ^ i = o⁻¹ * (o * c ^ i) by group]
    exact mul_mem (inv_mem (pPrimeCoreOf_le 3 K ho)) hk
  rw [P.zpow_eq_one_of_mem hspor hzK]
  simpa using ho

theorem xA_le_pCore
    (hcent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  set K := k142 A (lB A) c with hKdef
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  set OK := pPrimeCoreOf 3 K with hOK
  have hKH : K ≤ H := delta_le _
  have hOHK : pPrimeCoreOf 3 H ≤ K := by
    rw [hKdef, P.eq_k]
    exact le_sup_right.trans le_sup_left
  have hOH : pPrimeCoreOf 3 H ≤ OK :=
    le_pPrimeCoreOf hOHK (hKH.trans (le_normalizer_pPrimeCoreOf 3 H))
      (coprime_card_pPrimeCoreOf 3 H)
  have hKOK : K ≤ Subgroup.normalizer (OK : Set G) := le_normalizer_pPrimeCoreOf 3 K
  set M := X ⊔ OK with hM
  have hMK : M ≤ K := sup_le P.x_le (pPrimeCoreOf_le 3 K)
  have hM3 : IsPiSubgroup (piCompl 3) M := by
    refine isPiSubgroup_piCompl_sup ?_ ?_ (P.x_le.trans hKOK)
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (not_three_dvd_pCoreOf _)
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (not_three_dvd_pCoreOf _)
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hle : M ≤ M.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (fun o ho => ?_)
      · show l * r * l⁻¹ ∈ M
        have hθ := P.theta_le (hcent r⁻¹ (inv_mem hr) l hl)
        rw [show l * r * l⁻¹ = r * ⁅r⁻¹, l⁆ by rw [commutatorElement_def]; group]
        exact mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hθ)
      · show l * o * l⁻¹ ∈ M
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hKOK (P.l_le hl)) o).mp ho)
    exact hle hm
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := by
    rw [hKdef, P.eq_k]
    refine sup_le (sup_le hLM ?_) ?_
    · exact hOH.trans (le_sup_right.trans Subgroup.le_normalizer)
    · exact le_sup_left.trans Subgroup.le_normalizer
  have h2 : M ≤ OK := le_pPrimeCoreOf hMK hKM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three M).mp hM3))
  exact le_sup_left.trans h2

section Quot

variable [(ker142 A (lB A) c).Normal]

omit P in
theorem alpha_c_eq_one (hcA : c ∈ A) : alpha142 A (lB A) c c hcA = 1 := by
  rw [alpha142, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

omit P in
theorem alpha_mem_img {a : G} (ha : a ∈ A) : alpha142 A (lB A) c a ha ∈ img142 A (lB A) c A :=
  ⟨⟨a, Subgroup.mem_sup_right ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

omit P in
theorem alpha_zpow_mul {a b : G} (ha : a ∈ A) (hb : b ∈ A) (i j : ℤ)
    (hab : a ^ i * b ^ j ∈ A) :
    alpha142 A (lB A) c (a ^ i * b ^ j) hab =
      alpha142 A (lB A) c a ha ^ i * alpha142 A (lB A) c b hb ^ j := by
  simp only [alpha142, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul]
  congr 1

theorem img_le_of_le (hspor : SporadicModels131) {d x : G} (hdA : d ∈ A) (hdL : d ∈ L)
    (hd1 : d ≠ 1) (hcL : c ∉ L) (hxA : x ∈ A) (hx : InducesTypeOn L x 3)
    (hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) {a : G} (haA : a ∈ A)
    (ha1 : alpha142 A (lB A) c a haA ≠ 1) {Q : Subgroup G}
    (hQα : img142 A (lB A) c Q =
      thetaC142 A (lB A) c (alpha142 A (lB A) c a haA) ⊔ thetaCA142 A (lB A) c)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRQ : R ≤ Q) (hRK : R ≤ k142 A (lB A) c)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    img142 A (lB A) c R ≤
      thetaC142 A (lB A) c (alpha142 A (lB A) c d hdA) ⊔ thetaCA142 A (lB A) c := by
  have hD := P.std.toSec13Data
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz => hD.commute hy hz
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set N0 := ker142 A (lB A) c with hN0
  set aα := alpha142 A (lB A) c a haA with haα
  set dα := alpha142 A (lB A) c d hdA with hdα
  have hRQα : img142 A (lB A) c R ≤ img142 A (lB A) c Q :=
    Subgroup.map_mono (Subgroup.comap_mono hRQ)
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have hcα := alpha_c_eq_one hcA
  by_cases hacd : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hcomm c hcA d hdA) hacd
    have haeq : aα = dα ^ j := by
      have h1 := alpha_zpow_mul (c := c) hcA hdA i j (hij ▸ haA)
      simp only [hcα, one_zpow, one_mul] at h1
      rw [haα, ← h1]
      congr 1
    have hdα3 : dα ^ 3 = 1 := by
      have h1 : d ^ 3 = 1 := hA.2 d hdA
      rw [hdα, alpha142, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
      rw [QuotientGroup.eq_one_iff]
      have h2 : (⟨d, Subgroup.mem_sup_right hdA⟩ : ↥KA) ^ 3 = 1 :=
        Subtype.ext (by simpa using h1)
      rw [h2]
      exact one_mem _
    have hzp : Subgroup.zpowers aα = Subgroup.zpowers dα := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hle : Subgroup.zpowers aα ≤ Subgroup.zpowers dα := by
        rw [Subgroup.zpowers_le, haeq]
        exact Subgroup.zpow_mem_zpowers dα j
      have ha3 : aα ^ 3 = 1 := by
        rw [haeq, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdα3, one_zpow]
      have hd1' : dα ≠ 1 := fun h => ha1 (by rw [haeq, h, one_zpow])
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
        orderOf_eq_prime hdα3 hd1']
    have hC := Sec13.centralizer_singleton_eq_of_zpowers_eq hzp
    have hM : thetaC142 A (lB A) c aα = thetaC142 A (lB A) c dα := by
      rw [thetaC142, thetaC142, hC]
    rw [← hM, ← hQα]
    exact hRQα
  ·
    have hfix := fix_of_not_mem_sup hA h27 hcA hdA hxA haA hdL hd1 hD.le_centralizer
      hD.le_normalizer h9 hx hxcd hacd
    have haS : aα ∈ img142 A (lB A) c A := alpha_mem_img haA
    have hdS : dα ∈ img142 A (lB A) c A := alpha_mem_img hdA
    have hθC : thetaC142 A (lB A) c aα ≤ Subgroup.centralizer {aα} :=
      (Subgroup.map_subtype_le _).trans inf_le_right
    have hθCA : thetaCA142 A (lB A) c ≤ Subgroup.centralizer {aα} :=
      ((Subgroup.map_subtype_le _).trans inf_le_right).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haS))
    rintro ρ ⟨⟨r, hrKA⟩, hrR, rfl⟩
    have hrR' : r ∈ R := Subgroup.mem_subgroupOf.mp hrR
    have hrK : r ∈ K := hRK hrR'
    set ρ := QuotientGroup.mk' N0 (⟨r, hrKA⟩ : ↥KA) with hρ
    have hρQ : ρ ∈ thetaC142 A (lB A) c aα ⊔ thetaCA142 A (lB A) c :=
      hQα ▸ hRQα ⟨⟨r, hrKA⟩, hrR, rfl⟩
    have hρa : ρ ∈ Subgroup.centralizer {aα} := sup_le hθC hθCA hρQ
    have haKA : a ∈ KA := Subgroup.mem_sup_right haA
    have hdKA : d ∈ KA := Subgroup.mem_sup_right hdA
    have hk : a * r * a⁻¹ * r⁻¹ ∈ pPrimeCoreOf 3 K ⊔ Subgroup.zpowers c := by
      have h1 : QuotientGroup.mk' N0 ((⟨a, haKA⟩ : ↥KA) * ⟨r, hrKA⟩ * (⟨a, haKA⟩ : ↥KA)⁻¹ *
          (⟨r, hrKA⟩ : ↥KA)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have h2 : ρ * aα = aα * ρ := Subgroup.mem_centralizer_singleton_iff.mp hρa
        change aα * ρ * aα⁻¹ * ρ⁻¹ = 1
        rw [← h2]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    set t := r * d * r⁻¹ * d⁻¹ with ht
    have htR : t ∈ R := by
      have h1 : d * r⁻¹ * d⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hAR hdA) r⁻¹).mp (inv_mem hrR')
      rw [ht, show r * d * r⁻¹ * d⁻¹ = r * (d * r⁻¹ * d⁻¹) by group]
      exact mul_mem hrR' h1
    have htL : t ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (P.k_le_normalizer hrK) d).mp hdL) (inv_mem hdL)
    set k := a * r * a⁻¹ * r⁻¹ with hkdef
    have hada : a * d * a⁻¹ = d := by rw [hcomm a haA d hdA, mul_inv_cancel_right]
    have hat : a * t * a⁻¹ * t⁻¹ = (k * t * k⁻¹ * t⁻¹) * (t * (k * d * k⁻¹ * d⁻¹) * t⁻¹) := by
      have e1 : a * t * a⁻¹ =
          (a * r * a⁻¹) * (a * d * a⁻¹) * (a * r * a⁻¹)⁻¹ * (a * d * a⁻¹)⁻¹ := by
        rw [ht]
        group
      rw [e1, hada, hkdef, ht]
      group
    have hθN : t ∈ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) : Set G) :=
      Sec6.normalizer_le_normalizer_theta L (Subgroup.le_normalizer htL)
    have hatθ : a * t * a⁻¹ * t⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [hat]
      exact mul_mem (P.commutator_mem_theta hspor hk htL)
        ((Subgroup.mem_normalizer_iff.mp hθN _).mp (P.commutator_mem_theta hspor hk hdL))
    obtain ⟨m, hm⟩ := hR2 ⟨t, htR⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have htθ := mem_theta_of_conj_mem (hD.le_normalizer haA) hfix htL htm hatθ
    have htOK : t ∈ pPrimeCoreOf 3 K := P.theta_le htθ
    have hρd : ρ * dα = dα * ρ := by
      have h1 : QuotientGroup.mk' N0 ((⟨r, hrKA⟩ : ↥KA) * ⟨d, hdKA⟩ * (⟨r, hrKA⟩ : ↥KA)⁻¹ *
          (⟨d, hdKA⟩ : ↥KA)⁻¹) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left htOK)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      change ρ * dα * ρ⁻¹ * dα⁻¹ = 1 at h1
      calc ρ * dα = (ρ * dα * ρ⁻¹ * dα⁻¹) * dα * ρ := by group
        _ = dα * ρ := by rw [h1, one_mul]
    have hρA : ρ ∈ Subgroup.centralizer (img142 A (lB A) c A : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro β ⟨⟨b, hbKA⟩, hbA, rfl⟩
      have hbA' : b ∈ A := Subgroup.mem_subgroupOf.mp hbA
      obtain ⟨i, j, n, -, hbeq⟩ :=
        Proof142Res.exists_pow_mul_eq hA h27 hcA hdA haA h9 hacd hbA'
      have hβ : QuotientGroup.mk' N0 (⟨b, hbKA⟩ : ↥KA) = dα ^ j * aα ^ n := by
        have h1 : (⟨b, hbKA⟩ : ↥KA) = (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥KA) ^ i *
            (⟨d, hdKA⟩ : ↥KA) ^ j * (⟨a, haKA⟩ : ↥KA) ^ n :=
          Subtype.ext (by simp [hbeq])
        rw [h1, map_mul, map_mul, map_zpow, map_zpow, map_pow]
        change (alpha142 A (lB A) c c hcA) ^ i * dα ^ j * aα ^ n = _
        rw [hcα, one_zpow, one_mul]
      rw [hβ]
      have hca : Commute ρ aα := (Subgroup.mem_centralizer_singleton_iff.mp hρa)
      have hcd' : Commute ρ dα := hρd
      exact ((hcd'.zpow_right j).mul_right (hca.pow_right n)).symm.eq
    exact (le_sup_right : thetaCA142 A (lB A) c ≤ thetaC142 A (lB A) c dα ⊔ _)
      (mem_theta_of_mem_sup haS hρQ hρA)

end Quot

end Pt142

theorem exists_type3_of_pgl
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    ∃ x ∈ A, InducesTypeOn L x 3 := by
  have hcL : c ∉ L :=
    Sec13.not_mem_of_center_eq_bot hD (facts_of_isZ3PGLThreePi hD hPGL).2.1
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
      ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, -, hx⟩ | ⟨hcL', -⟩
  · exact (Sec16.Proof1614.false_of_pgl_of_prod Sec16.Proof1613.kSPGLProper hD hPGL ψ).elim
  · exfalso
    obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := (sporadicModels131 : SporadicModels131)
    have hL3 := (facts_of_isZ3PGLThreePi hD hPGL).1
    rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := Sec13.facts_of_prod hD hM12p hM12z χ
      exact not_isLThreePi_of_mulEquiv χ' (fun p e _ => KFacts.KS14.not_isoLThreePi_M12 p e) hL3
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := Sec13.facts_of_prod hD hJ2p hJ2z χ
      exact not_isLThreePi_of_mulEquiv χ'
        (fun p e _ => Item148PtRes2.not_isoLThreePi_J2 p e) hL3
  · exact hx
  · exact (hcL hcL').elim


theorem exists_mem_scriptQ_of_pgl (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hx : ∃ x ∈ A, InducesTypeOn L x 3)
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A) :
    ∃ Y ∈ scriptQ A (lB A), Y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      ∀ R ∈ scriptQPi A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
        R ≤ Y := by
  have hD := h.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have hcA := hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set K := k142 A (lB A) c with hKdef
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) ∧ _ := h142
  have hRK : ∀ R ∈ scriptQPi A (lB A) H (piOf 2), R ≤ K := fun R hR => le_delta hR.1.1 hR.1.2
  have hRQ : ∀ R ∈ scriptQPi A (lB A) H (piOf 2),
      ∃ Q ∈ maxInvariantPiSubgroups H A (piCompl 3), R ≤ Q := by
    intro R hR
    exact exists_le_mem_maxInvariantPiSubgroups ⟨hR.1.2,
      isPiSubgroup_piCompl_three_of_piOf_two hR.2, hR.1.1.1.2.2⟩
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨hQ₀q, hQ₀b⟩ := h142' Q₀ hQ₀
  rcases hQ₀b with ⟨-, hQK, -, -⟩ | ⟨hK, -⟩
  ·
    have hKq : K ∈ scriptQ A (lB A) := by
      rw [hKdef, ← hQK]
      exact hQ₀q.1
    exact ⟨K, hKq, delta_le _, hRK⟩
  ·
    have P : Pt142 A c L := ⟨h, hK⟩
    obtain ⟨hL3, hZ, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD hZ
    obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
      (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL)
    obtain ⟨x, hxA, hxt⟩ := hx
    have hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
      Proof142Res.not_mem_sup_of_inducesTypeOn_three hD.mem_thetaComponentsAt hD.le_centralizer
        (hD.le_normalizer hcA) (hD.commute hcA hdAL.1) hdAL.2 hxt
    obtain ⟨ψ⟩ := Item148PtRes2.nonempty_img142_equiv hspor h hK
    set dα := alpha142 A (lB A) c d hdAL.1 with hdα
    set J := thetaC142 A (lB A) c dα ⊔ thetaCA142 A (lB A) c with hJ
    have hRJ : ∀ R ∈ scriptQPi A (lB A) H (piOf 2), img142 A (lB A) c R ≤ J := by
      intro R hR
      obtain ⟨Q, hQ, hRQ'⟩ := hRQ R hR
      obtain ⟨-, hQb⟩ := h142' Q hQ
      rcases hQb with ⟨-, hQK, -, -⟩ | ⟨-, hQb⟩
      · exfalso
        have hK3 : ¬ 3 ∣ Nat.card K :=
          (isPiSubgroup_piCompl_iff Nat.prime_three K).mp
            (by rw [hKdef, ← hQK]; exact hQ.prop.2.1)
        exact hK3 (P.three_dvd.trans (Subgroup.card_dvd_of_le P.l_le))
      rcases hQb with ⟨-, a, haA, ha1, hQα⟩ | ⟨⟨χ⟩, -⟩ | ⟨⟨χ⟩, -⟩
      · have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR
        exact P.img_le_of_le hspor hdAL.1 hdAL.2 hd1 hcL hxA hxt hxcd haA ha1 hQα hR2 hRQ'
          (hRK R hR) hR.1.1.1.2.2
      · exact absurd hL3 (not_isLThreePi_of_mulEquiv (ψ.symm.trans χ)
          fun p e _ => KFacts.KS14.not_isoLThreePi_M22 p e)
      · exact absurd hL3 (not_isLThreePi_of_mulEquiv (ψ.symm.trans χ)
          fun p e _ => Item148PtRes2.not_isoLThreePi_J2 p e)
    have hJ3 : ¬ 3 ∣ Nat.card J := by
      have hdS : dα ∈ img142 A (lB A) c A := Pt142.alpha_mem_img hdAL.1
      have hNM : thetaCA142 A (lB A) c ≤
          Subgroup.normalizer (thetaC142 A (lB A) c dα : Set _) :=
        ((Subgroup.map_subtype_le _).trans (inf_le_inf_left _
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdS)))).trans
          (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
      have h1 := isPiSubgroup_piCompl_sup
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
          (Sec6.theta_solvable_and_not_dvd _).2)
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
          (Sec6.theta_solvable_and_not_dvd _).2) hNM
      rw [hJ, sup_comm]
      exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp h1
    set N0 := ker142 A (lB A) c with hN0
    set Ñ := K ⊓ (J.comap (QuotientGroup.mk' N0)).map (kA142 A (lB A) c).subtype with hÑ
    have hÑ3 : ¬ 3 ∣ Nat.card Ñ := by
      intro h3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ñ) 3 h3
      have hyK : (y : G) ∈ K := y.2.1
      obtain ⟨z, hzJ, hzy⟩ := y.2.2
      have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
      have hz3 : z ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        change (kA142 A (lB A) c).subtype z ^ 3 = 1
        rw [hzy, ← hy3, pow_orderOf_eq_one]
      have hαz : QuotientGroup.mk' N0 z = 1 := by
        have hdvd : orderOf (QuotientGroup.mk' N0 z) ∣ 3 :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hz3, map_one])
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
        · exact orderOf_eq_one_iff.mp h1
        · exact absurd (h1 ▸ Subgroup.orderOf_dvd_natCard J hzJ) hJ3
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hαz
      have hzO : (z : G) ∈ pPrimeCoreOf 3 K ⊔ Subgroup.zpowers c :=
        Subgroup.mem_subgroupOf.mp hαz
      have hyO := P.mem_pCore_of_mem hspor hyK (hzy ▸ hzO)
      exact not_three_dvd_pCoreOf _ (hy3 ▸ Subgroup.orderOf_dvd_natCard _ hyO)
    set Y := sSup (scriptQPi A (lB A) H (piOf 2)) with hYdef
    have hYÑ : Y ≤ Ñ := by
      refine sSup_le fun R hR => le_inf (hRK R hR) fun r hr => ?_
      have hrKA : r ∈ kA142 A (lB A) c := Subgroup.mem_sup_left (hRK R hR hr)
      exact ⟨⟨r, hrKA⟩, hRJ R hR ⟨⟨r, hrKA⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩, rfl⟩
    have hYH : Y ≤ H := sSup_le fun R hR => hR.1.2
    have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 => hÑ3 (h3.trans (Subgroup.card_dvd_of_le hYÑ))
    have hYinv : Y ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hYH, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3,
        le_normalizer_sSup fun R hR => hR.1.1.1.2.2⟩
    obtain ⟨Q', hQ', hYQ'⟩ := exists_le_mem_maxInvariantPiSubgroups hYinv
    have hYq : Y ∈ scriptQ A (lB A) := mem_scriptQ_of_le (h142' Q' hQ').1.1 hYQ' hYinv.2.2
    exact ⟨Y, hYq, hYH, fun R hR => le_sSup hR⟩

theorem transOn_normalizer_of_pgl (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hx : ∃ x ∈ A, InducesTypeOn L x 3)
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) :
    TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  obtain ⟨Y, hYq, hYH, hle⟩ := exists_mem_scriptQ_of_pgl hspor h hPGL hx h142
  exact transOn_of_le_mem_scriptQ h.isE27 hbot hYq hYH hle

end Proof1413Res5

open Proof1413Res5 in
theorem item1412NotPGLR_of
    (h131 : Item131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) : Item1412NotPGLR := by
  intro G _ _ A c L hR _ c' hc' L' hL' hPGL
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hx := exists_type3_of_pgl h131 hD hPGL
  exact hc'.2 (transOn_normalizer_of_pgl sporadicModels131 h' hPGL hx (h142 G A c' L' h')
    (hbot G A c' L' h'))

end CFSG.RankThree.PartTwo.Sec14
