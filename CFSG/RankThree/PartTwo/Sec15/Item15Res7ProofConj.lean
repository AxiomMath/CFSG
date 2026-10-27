module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofConjPt
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofNorm
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofPoint

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

@[expose] noncomputable def zHJ (L Y : Subgroup G) (d : G) : Subgroup G :=
  oPrimeResidualOf 3 (inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)))

namespace Proof15Res7

omit [Finite G] in
theorem zHJ_le_residual (L Y : Subgroup G) (d : G) :
    zHJ L Y d ≤
      inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)) :=
  oPrimeResidualOf_le_self 3 _

omit [Finite G] in
theorem zHJ_le (L Y : Subgroup G) (d : G) :
    zHJ L Y d ≤ (L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G) :=
  (zHJ_le_residual L Y d).trans (Subgroup.map_subtype_le _)

theorem residual_inf_isPerfect (L Y : Subgroup G) (d : G) :
    Group.IsPerfect
      ↥(inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G))) := by
  have h := (perfect_residual_characterization
    (G := ↥((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
  exact Group.IsPerfect.ofSurjective
    (f := ((perfectResidual ↥((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G))).equivMapOfInjective _
      (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)

theorem zHJ_le_residual_inf (L Y : Subgroup G) (d : G) :
    zHJ L Y d ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
  (zHJ_le_residual L Y d).trans
    (Sec6.le_inSubgroup_perfectResidual_of_isPerfect (residual_inf_isPerfect L Y d)
      ((Subgroup.map_subtype_le _).trans (inf_le_inf_right _ inf_le_left)))

theorem le_normalizer_zHJ {H L Y : Subgroup G} {d : G}
    (hL : H ≤ Subgroup.normalizer (L : Set G)) (hY : H ≤ Subgroup.normalizer (Y : Set G))
    (hd : H ≤ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G)) :
    H ≤ Subgroup.normalizer (zHJ L Y d : Set G) :=
  le_normalizer_oPrimeResidualOf ((Late.le_normalizer_inf (Late.le_normalizer_inf hL hY) hd).trans
    (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _))

omit [Finite G] in
theorem mem_normalizer_inf {H K : Subgroup G} {x : G} (hH : x ∈ Subgroup.normalizer (H : Set G))
    (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  Late.le_normalizer_inf (A := Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hH)
    (Subgroup.zpowers_le.mpr hK) (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem inf_centralizer_le_centralizer {c d a : G} (ha : a ∈ Subgroup.closure {c, d}) :
    Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := by
  intro x hx
  have hxB : x ∈ Subgroup.centralizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hxB) a ha).symm

end Proof15Res7

open Proof15Res4 Proof15Res7

section Certificates


theorem Conf1515HJ.map_zHJ (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    ((zHJ L Y d).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  have hOθ : CFSG.Open.pCoreOf 2 L ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
    obtain ⟨-, -, -, -, -, -, hr⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.map_mono (hr 2 Nat.prime_two (by norm_num))
  have hcov : ((L ⊓ Y).subgroupOf L).map π = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    have hl : (l : G) ∈ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := by rw [← h.eq_L]; exact l.2
    obtain ⟨m, hm, o, ho, hmo⟩ := exists_mul_of_mem_sup
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)) hl
    refine ⟨⟨m, hm.1⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t, ht, hto⟩ := hOθ ho
    have he : (⟨m, hm.1⟩ : ↥L)⁻¹ * l = t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hmo, ← hto]
      simp
    rw [he]
    exact ht
  have hdW : d ∈ Subgroup.normalizer ((L ⊓ Y : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hdL) (h.A_le_normalizer hdA)
  have hZ₀ : (((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π = C := by
    rw [map_inf_centralizer_eq_inf inf_le_left hdW hdL hd3, hcov, top_inf_eq]
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  have hzc := Item148HJ.exists_sylow_quot hdL' ⟨S, hdS, hSd⟩
  have hz1 : π ⟨d, hdL⟩ ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  have htop : perfectResidual ↥C = ⊤ :=
    KFacts.KS14.Native.j2_perfectResidual_centralizer_eq_top h.j2 hz1 hzc
  have htop3 : oPrimeResidual 3 ↥C = ⊤ :=
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover
      (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc)
      Sec17.Proof171Steps.oPrimeResidual_alternatingGroup_six
  have hZ₀L : (L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G) ≤ L := inf_le_left.trans inf_le_left
  have hJ₁ : ((inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G))).subgroupOf
      L).map π = C := by
    rw [map_inSubgroup_perfectResidual_subgroupOf hZ₀L, hZ₀, inSubgroup, htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJ₁L : inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans hZ₀L
  rw [zHJ, map_oPrimeResidualOf_subgroupOf hJ₁L, hJ₁, oPrimeResidualOf, htop3,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem Conf1515HJ.quot_three_central (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ≠ 1 ∧
      ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ∈ (P : Subgroup _) ∧
          (P : Subgroup _) ≤ Subgroup.centralizer
            {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} := by
  have hd3 : d ^ 3 = 1 := h.sec13Data.isElemAbelian.2 d hdA
  refine ⟨fun h1 => ?_, ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  · obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
    exact Item148HJ.exists_sylow_quot hdL' ⟨S, hdS, hSd⟩

theorem Conf1515HJ.zHJ_quot (h : Conf1515HJ A c L Y) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    Nonempty (↥(zHJ L Y d) ⧸ CFSG.pCore 2 ↥(zHJ L Y d) ≃*
      ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  set Z := zHJ L Y d with hZdef
  have hZL : Z ≤ L := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_left)
  have hmem : ∀ x : ↥Z, (π.comp (Subgroup.inclusion hZL)) x ∈ C := fun x => by
    rw [← hmap]
    exact ⟨Subgroup.inclusion hZL x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set ρ : ↥Z →* ↥C := (π.comp (Subgroup.inclusion hZL)).codRestrict C hmem with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hmap] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hθ2 : IsPGroup 2 θ := Proof152Gen.isPGroup_theta_of_j2 h.sec15R.toSec14Std h.j2
  have hker : IsPGroup 2 ρ.ker := by
    have hk : ρ.ker = θ.comap (Subgroup.inclusion hZL) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
    rw [hk]
    exact hθ2.comap_of_injective _ (Subgroup.inclusion_injective hZL)
  exact nonempty_quot_pCore_two_equiv ρ hρs hker
    (KFacts.KS14.Native.j2_pCore_two_centralizer_eq_bot h.j2 hz1 hzc)

theorem Conf1515HJ.le_theta_conj
    (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d}) :
    ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({w * c * w⁻¹} : Set G),
        Subgroup.zpowers d⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (L.map (MulAut.conj w).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  have hXB := h.residual_eq_conj hdA hd1 hdZ hwA hwd hwcB
  have hc' := h.isLBConfig_conj hdZ hwA hwd hwcB
  have hB := h.isHyperplane hdA hd1 hdL
  have hRa := h.sec15R_conj hwA
  have hSa := hRa.toSec14Std
  have hJa := nonempty_j2_conj h.j2 w
  obtain ⟨-, -, -, -, hd'L', S', hdS', hSd'⟩ := hc'
  have hzwc := Item148HJ.exists_sylow_quot hd'L' ⟨S', hdS', hSd'⟩
  set a := w * c * w⁻¹ with ha
  set Lw := L.map (MulAut.conj w).toMonoidHom with hLw
  set d' := w * d * w⁻¹ with hd'
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  have hzd : Subgroup.zpowers d' = Subgroup.zpowers d := zpowers_conj_eq_of_mem_normalizer hwd
  have hdLw : d ∈ Lw := (Subgroup.zpowers_le.mpr hd'L') (hzd ▸ Subgroup.mem_zpowers d)
  have hCd : Subgroup.centralizer ({d'} : Set G) = Subgroup.centralizer ({d} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq hzd
  set U := ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers d⁆
    with hU
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Lw : Set G) :=
    centralizer_le_normalizer_of_j2 hSa hJa
  have hULw : U ≤ Lw := by
    rw [hU, Subgroup.commutator_le]
    intro x hx y hy
    have hyL : y ∈ Lw := (Subgroup.zpowers_le.mpr hdLw) hy
    rw [commutatorElement_def]
    exact Lw.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCa hx.2) y).mp hyL) (Lw.inv_mem hyL)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 Y := by
    rw [hU, Subgroup.commutator_le]
    intro x hx y hy
    have hyN := h.A_le_normalizer_pCoreOf ((Subgroup.zpowers_le.mpr hdA) hy)
    have h1 : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hx.1)
    rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx.1 h1
  have hU2 : IsPGroup 2 U := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hUO
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) :=
    (hZle.trans (inf_le_left.trans inf_le_left)).trans hD.le_centralizer
  have hZa : Z ≤ Subgroup.centralizer ({a} : Set G) :=
    (le_inf hZc hZd).trans (inf_centralizer_le_centralizer hwcB)
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator
      (Late.le_normalizer_inf (hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
        (hZa.trans Subgroup.le_normalizer))
      (hZd.trans (centralizer_singleton_le_normalizer_zpowers d))
  set XB := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hXBdef
  have hZX : Z ≤ XB := zHJ_le_residual_inf L Y d
  have hXBLw : XB ≤ Lw := hXB ▸ Item148HJ.residual_le Lw d'
  have hZLw : Z ≤ Lw := hZX.trans hXBLw
  set θw := aschbacherSolvableCore 3 ↥Lw with hθw
  set πw := QuotientGroup.mk' θw with hπw
  set Cw := Subgroup.centralizer ({πw ⟨d', hd'L'⟩} : Set (↥Lw ⧸ θw)) with hCw
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (by
    have h2 : w * d * w⁻¹ = 1 := h1
    have h3 : d = w⁻¹ * (w * d * w⁻¹) * w := by group
    rw [h3, h2]
    group)
  have hd'3 : d' ^ 3 = 1 := by rw [hd', conj_pow, hd3, mul_one, mul_inv_cancel]
  have hzw1 : πw ⟨d', hd'L'⟩ ≠ 1 := by
    intro h1
    rw [hπw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd'1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd'3))))
  have hθ2 : IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) L) :=
    (Proof152Gen.isPGroup_theta_of_j2 h.sec15R.toSec14Std h.j2).map L.subtype
  set XBw := inSubgroup perfectResidual (Lw ⊓ Subgroup.centralizer ({d'} : Set G)) with hXBw
  have hXBwLw : XBw ≤ Lw := Item148HJ.residual_le Lw d'
  have hXBwL : XBw ≤ L := hXB.symm ▸ Item148HJ.residual_le L d
  have hd'N : d' ∈ Subgroup.normalizer (Lw : Set G) := Subgroup.le_normalizer hd'L'
  have hXBwmap : (XBw.subgroupOf Lw).map πw = Cw := by
    have htop : perfectResidual ↥Cw = ⊤ :=
      KFacts.KS14.Native.j2_perfectResidual_centralizer_eq_top hJa hzw1 hzwc
    have hcop := map_inf_centralizer_eq_inf (X := Lw) (W := Lw) le_rfl hd'N hd'L' hd'3
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective θw), top_inf_eq] at hcop
    rw [hXBw, map_inSubgroup_perfectResidual_subgroupOf inf_le_left, hcop, inSubgroup, htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmemw : ∀ x : ↥XBw, (πw.comp (Subgroup.inclusion hXBwLw)) x ∈ Cw := fun x => by
    rw [← hXBwmap]
    exact ⟨Subgroup.inclusion hXBwLw x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set ρ' : ↥XBw →* ↥Cw := (πw.comp (Subgroup.inclusion hXBwLw)).codRestrict Cw hmemw with hρ'
  have hρ's : Function.Surjective ρ' := by
    rintro ⟨q, hq⟩
    rw [← hXBwmap] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hθθ : ∀ x ∈ XBw, x ∈ inSubgroup (aschbacherSolvableCore 3) L →
      x ∈ inSubgroup (aschbacherSolvableCore 3) Lw := by
    set T := (inSubgroup (aschbacherSolvableCore 3) L).subgroupOf XBw with hT
    have hTn : T.Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
        (Late.le_normalizer_inf (hXBwL.trans (Sec6.le_normalizer_theta L)) Subgroup.le_normalizer)
    have hT2 : IsPGroup 2 T := hθ2.comap_of_injective _ XBw.subtype_injective
    have hO2 : CFSG.pCore 2 ↥Cw = ⊥ :=
      KFacts.KS14.Native.j2_pCore_two_centralizer_eq_bot hJa hzw1 hzwc
    have hTmap : T.map ρ' ≤ CFSG.pCore 2 ↥Cw := le_sSup ⟨hTn.map ρ' hρ's, hT2.map ρ'⟩
    rw [hO2] at hTmap
    intro x hxX hxθ
    have h1 : ρ' ⟨x, hxX⟩ ∈ T.map ρ' := ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.mpr hxθ, rfl⟩
    have h1' := hTmap h1
    rw [Subgroup.mem_bot] at h1'
    have h2 : πw (Subgroup.inclusion hXBwLw ⟨x, hxX⟩) = 1 := congrArg Subtype.val h1'
    rw [hπw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have hmapw : (Z.subgroupOf Lw).map πw = Cw := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzd' : (z : G) ∈ Subgroup.centralizer ({d'} : Set G) :=
        hCd ▸ hZd (Subgroup.mem_subgroupOf.mp hz)
      rw [hCw, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzd')
    · intro q hq
      rw [← hXBwmap] at hq
      obtain ⟨x, hx, rfl⟩ := hq
      have hxX : (x : G) ∈ XBw := Subgroup.mem_subgroupOf.mp hx
      have hxXB : (x : G) ∈ XB := hXB ▸ hxX
      have hxL : (x : G) ∈ L := Item148HJ.residual_le L d hxXB
      have hxd : (x : G) ∈ Subgroup.centralizer ({d} : Set G) :=
        Item148HJ.residual_le_centralizer_singleton L d hxXB
      have hπx : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨x, hxL⟩ ∈
          (Z.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
        rw [hmap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxd)
      obtain ⟨z, hz, hzx⟩ := hπx
      have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have hzθ : z⁻¹ * ⟨x, hxL⟩ ∈ aschbacherSolvableCore 3 ↥L := QuotientGroup.eq.mp hzx
      have htθ : (z : G)⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore 3) L :=
        ⟨z⁻¹ * ⟨x, hxL⟩, hzθ, by simp⟩
      have htX : (z : G)⁻¹ * x ∈ XBw := hXB.ge (XB.mul_mem (XB.inv_mem (hZX hzZ)) hxXB)
      obtain ⟨t', ht', ht't⟩ := hθθ _ htX htθ
      refine ⟨⟨z, hZLw hzZ⟩, Subgroup.mem_subgroupOf.mpr hzZ, ?_⟩
      rw [hπw, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have he : (⟨z, hZLw hzZ⟩ : ↥Lw)⁻¹ * x = t' := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact ht't.symm)
      rw [he]
      exact ht'
  set Ub := (U.subgroupOf Lw).map πw with hUb
  have hUb2 : IsPGroup 2 Ub := isPGroup_map_subgroupOf πw hULw hU2
  have hUbN : Cw ≤ Subgroup.normalizer (Ub : Set (↥Lw ⧸ θw)) := by
    rw [← hmapw]
    rintro _ ⟨z, hz, rfl⟩
    have hzU : (z : G) ∈ Subgroup.normalizer (U : Set G) := hZU (Subgroup.mem_subgroupOf.mp hz)
    have hz' : z ∈ Subgroup.normalizer ((U.subgroupOf Lw : Subgroup ↥Lw) : Set ↥Lw) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp hzU (y : G)
    exact Subgroup.le_normalizer_map πw ⟨z, hz', rfl⟩
  have hUbot : Ub = ⊥ :=
    Proof156.eq_bot_of_isPGroup_of_centralizer_le_normalizer hJa hzw1 hzwc hUb2 hUbN
  intro u hu
  have h1 : πw ⟨u, hULw hu⟩ ∈ Ub := ⟨⟨u, hULw hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [hUbot, Subgroup.mem_bot, hπw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem Conf1515HJ.le_normalizer_conj
    (h : Conf1515HJ A c L Y)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) (h155 : Item155w A (lB A))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d})
    (hU1 : ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({w * c * w⁻¹} : Set G),
      Subgroup.zpowers d⁆ ≠ ⊥) :
    L.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hRa := h.sec15R_conj hwA
  have hSa := hRa.toSec14Std
  have hJa := nonempty_j2_conj h.j2 w
  have hθU := h.le_theta_conj hdA hd1 hdZ hwA hwd hwcB
  have hXB := h.residual_eq_conj hdA hd1 hdZ hwA hwd hwcB
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  obtain ⟨eZ⟩ := h.zHJ_quot hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hCq : IsQuasisimple ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
    (Item148HJ.centralizer_facts h.j2 hz1 hzc).1
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  set a := w * c * w⁻¹ with ha
  set Lw := L.map (MulAut.conj w).toMonoidHom with hLw
  set d' := w * d * w⁻¹ with hd'
  have haA : a ∈ A := (Subgroup.mem_normalizer_iff.mp hwA c).mp hD.mem_A
  have ha1 : a ≠ 1 := fun h1 => hD.ne_one (by
    have h3 : c = w⁻¹ * (w * c * w⁻¹) * w := by group
    rw [h3, show w * c * w⁻¹ = 1 from h1]
    group)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx haA)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set U := ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers d⁆
    with hUdef
  have hUC : U ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hUdef, Subgroup.commutator_le]
    intro x hx y hy
    have hya : y ∈ Subgroup.centralizer ({a} : Set G) := hAa ((Subgroup.zpowers_le.mpr hdA) hy)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 hya) (inv_mem hx.2)) (inv_mem hya)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 Y := by
    rw [hUdef, Subgroup.commutator_le]
    intro x hx y hy
    have hyN := h.A_le_normalizer_pCoreOf ((Subgroup.zpowers_le.mpr hdA) hy)
    have h1 : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hx.1)
    rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx.1 h1
  have hU2 : IsPGroup 2 U := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hUO
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator
      (Late.le_normalizer_inf h.A_le_normalizer_pCoreOf (hAa.trans Subgroup.le_normalizer))
      (hAd.trans (centralizer_singleton_le_normalizer_zpowers d))
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hUQ : U ∈ scriptQ A (lB A) :=
    (mem_scriptQ_of_hj_point hSa hJa ⟨hUC.trans (centralizer_singleton_le_normalizer_zpowers a),
      (isPiSubgroup_piCompl_iff Nat.prime_three U).mpr hU3, hAU⟩).1
  set T := inSubgroup (aschbacherSolvableCore 3) Lw with hTdef
  have hT2 : IsPGroup 2 T := (Proof152Gen.isPGroup_theta_of_j2 hSa hJa).map Lw.subtype
  have hT1 : T ≠ ⊥ := fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hθU))
  have hLwT : Lw ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta Lw
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    hSa.toSec13Data.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta Lw)
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1)
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) := hZL.trans hD.le_centralizer
  have hZa : Z ≤ Subgroup.centralizer ({a} : Set G) :=
    (le_inf hZc hZd).trans (inf_centralizer_le_centralizer hwcB)
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator
      (Late.le_normalizer_inf (hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
        (hZa.trans Subgroup.le_normalizer))
      (hZd.trans (centralizer_singleton_le_normalizer_zpowers d))
  have hZLw : Z ≤ Lw := (zHJ_le_residual_inf L Y d).trans (hXB ▸ Item148HJ.residual_le Lw d')
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ hmap
  set Y' := Z ⊔ U with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({a} : Set G) := sup_le hZa hUC
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAU
  have hY'U : Y' ≤ Subgroup.normalizer (U : Set G) := sup_le hZU Subgroup.le_normalizer
  have hUO' : U ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'U hU2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.sec15R.toTheoremFourHyp ha1 (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta hUQ le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO'))⟩, le_antisymm hY'Δ (delta_le Y')⟩
  set Z' := oPrimeResidualOf 3 Z with hZ'def
  have hZ'Z : Z' = Z := by
    rw [hZ'def, hZdef, zHJ, Proof156Res4.oRes3_idem']
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZX' : Z ≤ X' := hZ'Z ▸ oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ U) := Proof155w.le_sup_inf_of_le hZU hZX' hX'Y'
  have hX'U : X' ≤ Subgroup.normalizer ((X' ⊓ U : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'U)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZX' hX'le (hZX'.trans hX'U) hX'U
    (hU2.to_le inf_le_right)
  set e : ↥X' ⧸ CFSG.pCore 2 ↥X' ≃* _ := e₁.symm.trans eZ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZX'))
      (le_delta (mem_scriptQ_of_le hUQ inf_le_right
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAU)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZX'.trans le_sup_left) (hUO'.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hY'Y : Y' ≤ Y := sup_le hZY (hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨h.mem_scriptY0Star, hX'Y'.trans hY'Y, hY'Y.trans Subgroup.le_normalizer⟩
  have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
    rw [Nat.card_congr e.toEquiv, hC1080]
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
      not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
    have h60 := Nat.card_congr e5.toEquiv
    rw [hX'1080, card_alternatingGroup_five] at h60
    norm_num at h60
  have hM'm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAT (sup_le (hZLw.trans hLwT)
      (hθU.trans Subgroup.le_normalizer)) hx)⟩
  have hΔM := (h155 Y' hY'3 hX'4 hY'eq).2 Y hΓ hhyp M hM'm
  have hLwΔ : Lw ≤ delta A (lB A) M := Proof155w.le_delta_of_le_of_j2 hSa hJa (hLwT.trans hle)
  exact le_normalizer_of_isPerfect_of_le_n155 hS h152 h153 h.mem_scriptY0Star
    (Sec6.isPerfect_of_mem_thetaComponentsAt hSa.toSec13Data.mem_thetaComponentsAt)
    (hLwΔ.trans hΔM)

theorem Conf1515HJ.card_quot_pCore_two (h : Conf1515HJ A c L Y) :
    Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 604800 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  have hR := h.sec15R
  have hLc := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (hR.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) h.j2
  have hYle : Y ≤ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
    rw [inf_comm]
    exact h.eq_Y.le
  obtain ⟨eY⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := Y) inf_le_right hYle
    (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  obtain ⟨eL⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := L) inf_le_left h.eq_L.le
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  rw [Nat.card_congr ((eY.symm.trans eL).trans eJ).toEquiv, KFacts.KS14.card_nativeJ2]

theorem not_isPGroup_two_of_three_dvd {K : Type*} [Group K] [Finite K]
    (h3 : 3 ∣ Nat.card K) : ¬ IsPGroup 2 K := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rw [hn] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem Conf1515HJ.false_of_le_normalizer_conj
    (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwd : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d}) (hwcn : w * c * w⁻¹ ∉ Subgroup.zpowers c)
    (hLwY : L.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (Y : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hRa := h.sec15R_conj hwA
  have hSa := hRa.toSec14Std
  have hJa := nonempty_j2_conj h.j2 w
  have hXB := h.residual_eq_conj hdA hd1 hdZ hwA hwd hwcB
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  have hYcard := h.card_quot_pCore_two
  have hθw2 := Proof152Gen.isPGroup_theta_of_j2 hSa hJa
  obtain ⟨eJ⟩ := hJa
  set a := w * c * w⁻¹ with ha
  set Lw := L.map (MulAut.conj w).toMonoidHom with hLw
  set d' := w * d * w⁻¹ with hd'
  set θw := aschbacherSolvableCore 3 ↥Lw with hθw
  set πw := QuotientGroup.mk' θw with hπw
  have hπws : Function.Surjective πw := QuotientGroup.mk'_surjective θw
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimp : IsSimpleGroup (↥Lw ⧸ θw) := eJ.isSimpleGroup
  have hQcard : Nat.card (↥Lw ⧸ θw) = 604800 := by
    rw [Nat.card_congr eJ.toEquiv, KFacts.KS14.card_nativeJ2]
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZLw : Z ≤ Lw := (zHJ_le_residual_inf L Y d).trans (hXB ▸ Item148HJ.residual_le Lw d')
  set K' := Lw ⊓ Y with hK'
  have hK'n : (K'.subgroupOf Lw).Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
      (Late.le_normalizer_inf (Late.le_normalizer_inf Subgroup.le_normalizer hLwY)
        Subgroup.le_normalizer)
  have : ((K'.subgroupOf Lw).map πw).Normal := hK'n.map πw hπws
  rcases hsimp.eq_bot_or_eq_top_of_normal ((K'.subgroupOf Lw).map πw) with hbot | htop
  ·
    have hZθ : Z ≤ inSubgroup (aschbacherSolvableCore 3) Lw := by
      intro z hz
      have h1 : πw ⟨z, hZLw hz⟩ ∈ (K'.subgroupOf Lw).map πw :=
        ⟨⟨z, hZLw hz⟩, Subgroup.mem_subgroupOf.mpr ⟨hZLw hz, hZY hz⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have hZ2 : IsPGroup 2 Z := (hθw2.map Lw.subtype).to_le hZθ
    have hC2 := isPGroup_map_subgroupOf (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) hZL hZ2
    rw [hmap] at hC2
    exact not_isPGroup_two_of_three_dvd (by rw [hC1080]; norm_num) hC2
  ·
    have hK'Lw : K' ≤ Lw := inf_le_left
    have hK'Y : K' ≤ Y := inf_le_right
    set ψ : ↥K' →* ↥Lw ⧸ θw := πw.comp (Subgroup.inclusion hK'Lw) with hψ
    have hψs : Function.Surjective ψ := by
      intro q
      have hq : q ∈ (K'.subgroupOf Lw).map πw := htop ▸ Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    have hO2w : CFSG.pCore 2 (↥Lw ⧸ θw) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (↥Lw ⧸ θw)) with h0 | h0
      · exact h0
      · exfalso
        have h2 : IsPGroup 2 (↥Lw ⧸ θw) :=
          (CFSG.pCore_isPGroup (p := 2) (G := ↥Lw ⧸ θw)).of_surjective
            ((MulEquiv.subgroupCongr h0).trans Subgroup.topEquiv).toMonoidHom
            (MulEquiv.surjective _)
        exact not_isPGroup_two_of_three_dvd (by rw [hQcard]; norm_num) h2
    set ρY : ↥K' →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hK'Y) with hρY
    have hker : ρY.ker ≤ ψ.ker := by
      set T := ρY.ker with hT
      have hT2 : IsPGroup 2 T := by
        have hTc : T = (CFSG.pCore 2 ↥Y).comap (Subgroup.inclusion hK'Y) := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_comap, hρY, MonoidHom.comp_apply,
            QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rw [hTc]
        exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hK'Y)
      have hTmap : T.map ψ ≤ CFSG.pCore 2 (↥Lw ⧸ θw) :=
        le_sSup ⟨(MonoidHom.normal_ker ρY).map ψ hψs, hT2.map ψ⟩
      rw [hO2w] at hTmap
      intro x hx
      have h1 := hTmap ⟨x, hx, rfl⟩
      rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at h1
    have hle : Nat.card (↥Lw ⧸ θw) ≤ Nat.card ρY.range :=
      (Nat.card_le_card_of_surjective _ ((QuotientGroup.lift_surjective_of_surjective _ ψ hψs
        hker))).trans (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρY).toEquiv).le
    have hrange : ρY.range = ⊤ :=
      Subgroup.eq_top_of_le_card _ (by rw [hYcard, ← hQcard]; exact hle)
    have hYK : Y ≤ K' ⊔ CFSG.Open.pCoreOf 2 Y := by
      intro y hy
      obtain ⟨k, hk⟩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩) ∈ ρY.range :=
        hrange ▸ Subgroup.mem_top _
      have hk' : (Subgroup.inclusion hK'Y k)⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y := by
        rw [← QuotientGroup.eq]
        exact hk
      have hkO : (k : G)⁻¹ * y ∈ CFSG.Open.pCoreOf 2 Y := by
        rw [CFSG.Open.pCoreOf]
        exact ⟨_, hk', by simp⟩
      have he : y = (k : G) * ((k : G)⁻¹ * y) := by group
      rw [he]
      exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hkO)
    have haA : a ∈ A := (Subgroup.mem_normalizer_iff.mp hwA c).mp hD.mem_A
    have hLwa : Lw ≤ Subgroup.centralizer ({a} : Set G) := hSa.toSec13Data.le_centralizer
    apply hwcn
    refine h.mem_zpowers_of_mem_sectionCentralizer ⟨haA, fun y hy => ?_⟩
    have hK'O : K' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      hK'Y.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    obtain ⟨m, hm, o, ho, rfl⟩ := exists_mul_of_mem_sup hK'O (hYK hy)
    have ham : a * m = m * a :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLwa hm.1)).symm
    rw [conj_mul_eq ham]
    have hao : a * o * a⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp (h.A_le_normalizer_pCoreOf haA) o).mp ho
    exact (Subgroup.mem_normalizer_iff.mp (hK'O hm) _).mp
      (mul_mem hao (inv_mem ho))

end Certificates

theorem step1515HJConj_of
    (h152 : Item152R) (h153 : Item153MainR) (h155 : Item155wR) : Step1515HJConj := by
  intro G _ _ A c L Y h d hdA hd1 hdZ w hwA hwd hwcB hwcn hU
  have hR := h.sec15R
  exact (h.false_of_le_normalizer_conj hdA hd1 hdZ hwA hwd hwcB hwcn
    (h.le_normalizer_conj (h152 G A c L hR) (h153 G A c L hR) (h155 G A c L hR) hdA hd1 hdZ
      hwA hwd hwcB hU)).elim

end CFSG.RankThree.PartTwo.Sec15
