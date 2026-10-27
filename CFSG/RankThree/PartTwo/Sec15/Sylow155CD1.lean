module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.RankThree.PartTwo.Sec15.Sylow155CD1Core
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDR4
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDPoint
import CFSG.RankThree.PartTwo.Sec15.Sylow155NODeg
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.KFacts.KS44Transport
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Twin
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155CD1

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

private theorem isTripleCover_map_quot {H : Type} [Group H] [Finite H] {K' : Subgroup H}
    (hK' : K' ∈ thetaComponents 3 H)
    (hT : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover ↥(K'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
      (alternatingGroup (Fin 6)) := by
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hK'.2.1
  exact KFacts.KS14.isTripleCover_congr η hT

private theorem isTripleCover_of_map_subtype {C : Subgroup G} {K' : Subgroup ↥C}
    (hT : Sec4.IsTripleCover (↥(K'.map C.subtype) ⧸ aschbacherSolvableCore 3 ↥(K'.map C.subtype))
      (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)) :=
  KFacts.KS14.isTripleCover_congr
    (KFacts.thetaQuotEquivOfMap C.subtype K'
      (KFacts.thetaQuotMap_iff_of_injective C.subtype Subtype.val_injective K')).symm hT

private theorem theta_map_le {C : Subgroup G} {K' : Subgroup ↥C} (hK' : K'.IsSubnormal) :
    inSubgroup (aschbacherSolvableCore 3) (K'.map C.subtype) ≤
      (aschbacherSolvableCore 3 ↥C).map C.subtype := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨l, rfl⟩ := C.subtype.subgroupMap_surjective K' t
  have hl : l ∈ aschbacherSolvableCore 3 ↥K' :=
    (KFacts.thetaQuotMap_iff_of_injective C.subtype Subtype.val_injective K' l).mp ht
  rw [aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hK', Subgroup.mem_subgroupOf] at hl
  exact ⟨(l : ↥C), hl, rfl⟩

private theorem map_quot_eq {C : Subgroup G} {K' : Subgroup ↥C} {X : Subgroup G}
    (hK' : K'.IsSubnormal) (hXC : X ≤ C) (hXK : X ≤ K'.map C.subtype)
    (hKX : K'.map C.subtype = X ⊔ inSubgroup (aschbacherSolvableCore 3) (K'.map C.subtype)) :
    K'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) =
      (X.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) := by
  apply le_antisymm
  · have h1 : K'.map C.subtype ≤
        (X.subgroupOf C ⊔ aschbacherSolvableCore 3 ↥C).map C.subtype := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXC]
      exact hKX.le.trans (sup_le_sup_left (theta_map_le hK') _)
    have h2 := (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp h1
    calc K'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C))
        ≤ (X.subgroupOf C ⊔ aschbacherSolvableCore 3 ↥C).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) := Subgroup.map_mono h2
      _ = (X.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  · refine Subgroup.map_mono fun x hx => ?_
    obtain ⟨k, hk, hkx⟩ := hXK (Subgroup.mem_subgroupOf.mp hx)
    obtain rfl : k = x := Subtype.ext hkx
    exact hk

private theorem normalizer_or_commute_of_isComponent {Q : Type} [Group Q] [Finite Q]
    {J : Subgroup Q} (hJ : IsComponent J) (h : Q) :
    h ∈ Subgroup.normalizer (J : Set Q) ∨
      ∀ a ∈ J, ∀ b ∈ J, a * (h * b * h⁻¹) = (h * b * h⁻¹) * a := by
  rcases CFSG.LocalCores.distinct_components_commute hJ
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj h) hJ) with heq | hcomm
  · left
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : h * x * h⁻¹ ∈ J.map (MulAut.conj h).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [← heq] at h1
    · intro hx
      rw [heq] at hx
      obtain ⟨x', hx', hxx'⟩ := hx
      have h1 : h * x' * h⁻¹ = h * x * h⁻¹ := hxx'
      have h2 : x' = x := by simpa using h1
      rwa [← h2]
  · right
    intro a ha b hb
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) (h * b * h⁻¹) ⟨b, hb, rfl⟩).symm

private theorem false_of_le_centralizer {Q : Type} [Group Q] [Finite Q] {J Ā : Subgroup Q}
    (hT : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (hĀC : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → q ∈ Ā)
    (h : Ā ≤ Subgroup.centralizer (J : Set Q)) : False := by
  obtain ⟨x, hx3, hxZ⟩ := Sylow155NO.exists_pow_three_not_mem_center hT
  have hxA : (x : Q) ∈ Subgroup.centralizer (Ā : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (h ha) x x.2).symm
  have hx3' : (x : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hx := h (hĀC x hxA hx3')
  apply hxZ
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)

private theorem eq_of_mk'_eq {A C : Subgroup G} {N : Subgroup ↥C} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {a b : ↥C} (ha : (a : G) ∈ A)
    (hb : (b : G) ∈ A) (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  have hu : a⁻¹ * b ∈ N := (QuotientGroup.eq (s := N)).mp hab
  have hmem : ((a⁻¹ * b : ↥C) : G) ∈ A := by
    have : ((a⁻¹ * b : ↥C) : G) = (a : G)⁻¹ * b := rfl
    rw [this]
    exact A.mul_mem (A.inv_mem ha) hb
  have hu3 : (a⁻¹ * b) ^ 3 = 1 := Subtype.ext (hA3 _ hmem)
  have hdvd1 : orderOf (a⁻¹ * b) ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hdvd2 : orderOf (a⁻¹ * b) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hu
  have hg : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  have h1 := Nat.dvd_gcd hdvd1 hdvd2
  rw [Nat.Coprime.gcd_eq_one hg] at h1
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

private theorem mem_map_comap_iff {C : Subgroup G} {Q : Type*} [Group Q] (f : ↥C →* Q)
    (T : Subgroup Q) (g : ↥C) : (g : G) ∈ (T.comap f).map C.subtype ↔ f g ∈ T := by
  constructor
  · rintro ⟨g', hg', hgg⟩
    obtain rfl : g' = g := Subtype.ext hgg
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

private theorem isPSolvable_centralizer_quot {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {C : Subgroup G} {d y : G} {X : Subgroup G} {K' : Subgroup ↥C}
    (hAC : A ≤ C) (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L) (hcA : c ∈ A) (hyA : y ∈ A)
    (hCd : ∀ x ∈ C, x * d = d * x) (hK' : K' ∈ thetaComponents 3 ↥C) (hXC : X ≤ C)
    (hXK : X ≤ K'.map C.subtype)
    (hKX : K'.map C.subtype = X ⊔ inSubgroup (aschbacherSolvableCore 3) (K'.map C.subtype))
    (hT : Sec4.IsTripleCover (↥(K'.map C.subtype) ⧸ aschbacherSolvableCore 3 ↥(K'.map C.subtype))
      (alternatingGroup (Fin 6)))
    (hAX : A ⊓ L ≤ X) (hcX : X ≤ Subgroup.centralizer ({c} : Set G))
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hA7 : A = (A ⊓ L) ⊔ Subgroup.zpowers y)
    (hA56 : A = Subgroup.zpowers d ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers c)
    (hcd : c ∉ Subgroup.zpowers d) :
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C) ⟨y, hAC hyA⟩} :
        Set (↥C ⧸ aschbacherSolvableCore 3 ↥C))) := by
  have hD := h.toSec13Data
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hD.isElemAbelian.2
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥C) :=
    (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).2.2.1
  have hdC : d ∈ C := hAC hdA
  have hcC : c ∈ C := hAC hcA
  have hyC : y ∈ C := hAC hyA
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C) with hπ
  have hJc : IsComponent (K'.map π) := isComponent_map_of_mem_thetaComponents Nat.prime_three hK'
  have hperf : commutator ↥(K'.map π) = ⊤ := (Group.isPerfect_def (G := _)).1 hJc.1.1
  have hTJ : Sec4.IsTripleCover ↥(K'.map π) (alternatingGroup (Fin 6)) :=
    isTripleCover_map_quot hK' (isTripleCover_of_map_subtype hT)
  have hJX : K'.map π = (X.subgroupOf C).map π := map_quot_eq hK'.2.1 hXC hXK hKX
  have hinj : ∀ a b : ↥C, (a : G) ∈ A → (b : G) ∈ A → π a = π b → a = b :=
    fun a b ha hb hab => eq_of_mk'_eq hθ3 hA3 ha hb hab
  have hdX : d ∈ X := hAX ⟨hdA, hdL⟩
  have hdbJ : π ⟨d, hdC⟩ ∈ K'.map π := by
    rw [hJX]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hdX)
  have hdbZ : ∀ q : ↥C ⧸ aschbacherSolvableCore 3 ↥C, π ⟨d, hdC⟩ * q = q * π ⟨d, hdC⟩ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥C) q
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hCd x x.2).symm)
  have hdb1 : π ⟨d, hdC⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨d, hdC⟩ : ↥C) = 1 := hinj _ 1 hdA (by simp) (by rw [h1, map_one])
    exact hd1 (by simpa using congrArg Subtype.val h2)
  have hdb3 : π ⟨d, hdC⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hA3 d hdA)
    rw [this, map_one]
  have hdbord : orderOf (π ⟨d, hdC⟩) = 3 := orderOf_eq_prime hdb3 hdb1
  have hcard : Nat.card (Sec14.Item148PtRes.centerIn (K'.map π)) = 3 := by
    rw [Sec14.Item148PtRes.centerIn, Subgroup.card_map_of_injective (K'.map π).subtype_injective]
    exact hTJ.1
  have hle : Subgroup.zpowers (π ⟨d, hdC⟩) ≤ Sec14.Item148PtRes.centerIn (K'.map π) := by
    rw [Subgroup.zpowers_le]
    refine Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨hdbJ, Subgroup.mem_center_iff.mpr fun g => ?_⟩
    exact Subtype.ext (hdbZ g).symm
  have hZeq : Subgroup.zpowers (π ⟨d, hdC⟩) = Sec14.Item148PtRes.centerIn (K'.map π) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hdbord])
  have hZ : Sec14.Item148PtRes.centerIn (K'.map π) ≤
      Subgroup.center (↥C ⧸ aschbacherSolvableCore 3 ↥C) := by
    rw [← hZeq, Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.mpr fun q => (hdbZ q).symm
  have hcomp := normalizer_or_commute_of_isComponent hJc
  have hR4 : ∀ E T : Subgroup (↥C ⧸ aschbacherSolvableCore 3 ↥C),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 81 → IsPGroup 2 T → T ≠ ⊥ →
        E ≤ Subgroup.normalizer (T : Set (↥C ⧸ aschbacherSolvableCore 3 ↥C)) → False :=
    fun E T hE hE81 hT2 hT1 hET =>
      Sylow155CD.false_of_elemAbelian_quot h hθ3 hE hE81 hT2 hT1 hET
  have hy₀N : (⟨y, hyC⟩ : ↥C) ∈ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hyX (x : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  have hybN : π ⟨y, hyC⟩ ∈ Subgroup.normalizer
      ((K'.map π : Subgroup (↥C ⧸ aschbacherSolvableCore 3 ↥C)) : Set _) := by
    rw [hJX]
    exact Subgroup.le_normalizer_map π ⟨⟨y, hyC⟩, hy₀N, rfl⟩
  have hyJ : ∀ x ∈ K'.map π, π ⟨y, hyC⟩ * x * (π ⟨y, hyC⟩)⁻¹ ∈ K'.map π :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hybN x).mp hx
  have hy3 : π ⟨y, hyC⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hA3 y hyA)
    rw [this, map_one]
  have hcbJ : ∀ x ∈ K'.map π, π ⟨c, hcC⟩ * x = x * π ⟨c, hcC⟩ := by
    intro x hx
    rw [hJX] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    refine congrArg π (Subtype.ext ?_)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcX (Subgroup.mem_subgroupOf.mp hx₀))).symm
  have hy1 : ∃ x ∈ K'.map π, π ⟨y, hyC⟩ * x * (π ⟨y, hyC⟩)⁻¹ ≠ x := by
    by_contra hcon
    have hybJ : ∀ x ∈ K'.map π, x * π ⟨y, hyC⟩ = π ⟨y, hyC⟩ * x := fun x hx =>
      (mul_inv_eq_iff_eq_mul.mp (by_contra fun hne => hcon ⟨x, hx, hne⟩)).symm
    have hAS : A ≤ ((Subgroup.centralizer
        ((K'.map π : Subgroup (↥C ⧸ aschbacherSolvableCore 3 ↥C)) : Set _)).comap π).map
          C.subtype := by
      rw [hA56]
      refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
        (Subgroup.zpowers_le.mpr ?_)
      · exact (mem_map_comap_iff π _ ⟨d, hdC⟩).mpr
          (Subgroup.mem_centralizer_iff.mpr fun x _ => (hdbZ x).symm)
      · exact (mem_map_comap_iff π _ ⟨y, hyC⟩).mpr
          (Subgroup.mem_centralizer_iff.mpr fun x hx => hybJ x hx)
      · exact (mem_map_comap_iff π _ ⟨c, hcC⟩).mpr
          (Subgroup.mem_centralizer_iff.mpr fun x hx => (hcbJ x hx).symm)
    have hĀ : (A.subgroupOf C).map π ≤ Subgroup.centralizer
        ((K'.map π : Subgroup (↥C ⧸ aschbacherSolvableCore 3 ↥C)) : Set _) := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_map_comap_iff π _ a).mp (hAS (Subgroup.mem_subgroupOf.mp ha))
    exact false_of_le_centralizer hTJ
      (fun q hq hq3 => Sylow155T.mem_map_of_mem_centralizer h.mem_partTwoF hAC hθ3 hq hq3) hĀ
  have hyJ' : π ⟨y, hyC⟩ ∉ K'.map π := by
    intro hyJ'
    have hAS : A ≤ ((K'.map π).comap π).map C.subtype := by
      rw [hA7]
      refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr ?_)
      · refine (mem_map_comap_iff π (K'.map π) ⟨a, hAC ha.1⟩).mpr ?_
        rw [hJX]
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (hAX ha))
      · exact (mem_map_comap_iff π (K'.map π) ⟨y, hyC⟩).mpr hyJ'
    have hcbJ' : π ⟨c, hcC⟩ ∈ K'.map π := (mem_map_comap_iff π (K'.map π) ⟨c, hcC⟩).mp (hAS hcA)
    have hcbZ : π ⟨c, hcC⟩ ∈ Sec14.Item148PtRes.centerIn (K'.map π) :=
      Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨hcbJ', Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (hcbJ g g.2).symm⟩
    rw [← hZeq] at hcbZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcbZ
    have hbA : ((⟨d, hdC⟩ ^ k : ↥C) : G) ∈ A := by
      rw [Subgroup.coe_zpow]
      exact zpow_mem hdA k
    have h2 : (⟨c, hcC⟩ : ↥C) = ⟨d, hdC⟩ ^ k :=
      hinj _ _ hcA hbA (by rw [map_zpow]; exact hk.symm)
    apply hcd
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using (congrArg Subtype.val h2).symm⟩
  exact isPSolvable_centralizer hperf hTJ hZ hcomp hR4 hyJ hy3 hy1 hyJ'

theorem isPConstrained_centralizer_of_ncard_three
    (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : (omegaA A).ncard = 3) {B : Subgroup G} (hBA : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) (hBL : B ≠ A ⊓ L) :
    CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G)) := by
  have h := hR.toSec14Std
  have hD := hR.toSec13Data
  have hA := h.isE27'
  obtain ⟨d, hdA, hd1, hdZ⟩ : ∃ d ∈ A, d ≠ 1 ∧ IsZCentral L d := by
    obtain ⟨d, hdA, hd1, hdL, S, hdS, hSd⟩ := exists_three_central_of_j2 hD hJ
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    obtain ⟨hS, hZ⟩ :=
      center_sylow_eq_zpowers_of_quot_j2 Sec4.Sporadic.rank3II_4_15 hθ3 hJ hdL hd1 S hdS hSd
    exact ⟨d, hdA, hd1, _, hS, hZ⟩
  have hcd : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Proof15Res11.isLBConfig_of hR hJ hdZ
  obtain ⟨hdL, -⟩ := hcd.2.2.2.2
  have hBcd : IsHyperplane A (Subgroup.closure {c, d}) :=
    Proof15Res11.isHyperplane_of hR hJ hdA hd1 hdL
  obtain ⟨-, -, -, -, -, -, -, -, -, hdc⟩ := Ronan152SL25.lbConfig_facts hA hBcd hcd
  have hdB' : d ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hLK⟩ := Desc143X.exists_mem_le_residual h48 h hBcd hcd hdB' hd1 hdc
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hLK with
    ⟨-, -, hΩ1⟩ | ⟨hKX, hT, -, -, -, -, hΩ⟩ | ⟨-, -, -, h12⟩
  · rw [hΩ1, Set.ncard_singleton] at h3
    omega
  · rcases hΩ with ⟨-, -⟩ | ⟨-, -, -, -, a, ha, had, hΩa, h6, La, hLa, hJa⟩
    ·
      have hΩc : omegaA A ≠ {Subgroup.zpowers c} := fun h1 => by
        rw [h1, Set.ncard_singleton] at h3
        omega
      have hdB : d ∈ B :=
        Sylow155CD.mem_of_forall_not_mem_omegaA h134 h48 h hBcd hcd hΩc hBA hfree
      obtain ⟨hcL, hAL9, -⟩ := j2_point_facts hD hJ
      have hB9 : Nat.card B = 9 := by
        have h2 := hBA.2
        rw [hA.2] at h2
        omega
      obtain ⟨y, hyB, hyL⟩ : ∃ y ∈ B, y ∉ L := by
        by_contra hcon
        apply hBL
        have hle : B ≤ A ⊓ L := fun b hb =>
          ⟨hBA.1 hb, by_contra fun hbL => hcon ⟨b, hb, hbL⟩⟩
        exact Subgroup.eq_of_le_of_card_ge hle (by omega)
      have hyA : y ∈ A := hBA.1 hyB
      have hcA : c ∈ A := hD.mem_A
      have hcB : c ∉ B := fun hcB => hfree c hcB hD.ne_one hD.zpowers_mem_omegaA
      have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
      have hdyz : y ∉ Subgroup.zpowers d := fun hy => hyL (Subgroup.zpowers_le.mpr hdL hy)
      have hBdy : Subgroup.zpowers d ⊔ Subgroup.zpowers y = B :=
        Item148HJ.sup_zpowers_eq_of_isHyperplane (A := B) (B := Subgroup.zpowers d)
          ⟨Subgroup.zpowers_le.mpr hdB, by rw [hB9, Nat.card_zpowers, hd3]⟩ hyB hdyz
      have hA56 : A = Subgroup.zpowers d ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers c := by
        rw [hBdy]
        exact (Item148HJ.sup_zpowers_eq_of_isHyperplane hBA hcA hcB).symm
      have hALhyp : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by have := hA.2; omega⟩
      have hA7 : A = (A ⊓ L) ⊔ Subgroup.zpowers y :=
        (Item148HJ.sup_zpowers_eq_of_isHyperplane hALhyp hyA (fun hy => hyL hy.2)).symm
      have hcdz : c ∉ Subgroup.zpowers d := fun hc => hcB (Subgroup.zpowers_le.mpr hdB hc)
      have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hdA)
      have hyN : y ∈ Subgroup.normalizer
          ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_inf, Subgroup.mem_inf,
          Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hyA) x,
          Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hAC hyA)) x]
      have hyX :=
        CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
          _ hyN
      obtain ⟨K', hK', hKeq⟩ := hK
      have hKeq' : K = K'.map (Subgroup.centralizer ({d} : Set G)).subtype := hKeq.symm
      subst hKeq'
      have hsolv := isPSolvable_centralizer_quot h hAC hdA hd1 hdL hcA hyA
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp hx) hK'
        (Item148HJ.residual_le_centralizer_singleton L d) hLK hKX hT
        (Item148HJ.inf_le_residual h hBcd hcd)
        ((Item148HJ.residual_le L d).trans hD.le_centralizer) hyX hA7 hA56 hcdz
      refine isPConstrained_of_isPSolvable ?_
      have hBC : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB)
      have hθ3 : ¬ 3 ∣ Nat.card
          (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({d} : Set G))) :=
        (solvable_prime_complement_core_characterization
          (H := ↥(Subgroup.centralizer ({d} : Set G))) Nat.prime_three).2.2.1
      have hH := isPSolvable_of_le_centralizer_map hθ3 hsolv
        (H := (Subgroup.centralizer (B : Set G)).subgroupOf (Subgroup.centralizer ({d} : Set G)))
        (fun x hx => by
          rw [Subgroup.mem_subgroupOf] at hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y hyB).symm)
      exact isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBC) hH
    · omega
  · omega

end Sylow155CD1

end CFSG.RankThree.PartTwo.Sec15
