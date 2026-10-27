module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofUnique
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofRank
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofO2
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.RankThree.PartOne.S12.PerfectOddPrime
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement Pointwise

namespace Res7

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_pCoreOf_of_mem_oTwoP {M J : Subgroup G} (hJ : J ∈ oTwoComponentsIn M) {b j : G}
    (hb : b ∈ (Sec4.oTwoP 3 ↥M).map M.subtype) (hj : j ∈ J) :
    b * j * b⁻¹ * j⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJM, hJ'⟩ := mem_oTwoComponentsIn_iff.mp hJ
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  obtain ⟨b', hb', rfl⟩ := hb
  have hcomp := Sec19.Step1910Proof.isComponent_map_of_mem_oTwoComponents hJ'
  have hRs : Group.IsSolvable (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have := (CFSG.pCore_isPGroup (p := 3) (G := ↥M ⧸ CFSG.pCore 2 ↥M)).isNilpotent
    infer_instance
  have hRn : (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)).IsSubnormal :=
    (CFSG.pCore_normal (p := 3) (G := ↥M ⧸ CFSG.pCore 2 ↥M)).isSubnormal
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRs hRn).1 _ hcomp
  have h1 : ⁅π ⟨j, hJM hj⟩, π b'⁆ = 1 := by
    have hmem : ⁅π ⟨j, hJM hj⟩, π b'⁆ ∈ ⁅(J.subgroupOf M).map π,
        CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)⁆ :=
      Subgroup.commutator_mem_commutator ⟨⟨j, hJM hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩ hb'
    rw [hcomm, Subgroup.mem_bot] at hmem
    exact hmem
  rw [← map_commutatorElement, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Sec18.mem_pCore_iff_mem_pCoreOf] at h1
  have h2 := CFSG.Open.pCoreOf 2 M |>.inv_mem h1
  convert h2 using 1
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv,
    Subgroup.coe_subtype]
  group

theorem mul_comm_of_comm_eq_one {X : Type*} [Group X] {a b : X} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    a * b = b * a :=
  commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h)

end Res7

theorem step202CMem_of
    (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (h185 : Sec18.Item185)
    (h189 : Sec18.Item189) : Step202CMem := by
  intro G _ _ A M L N c h K₀ hK₀ h3
  by_contra hcK₀
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH18, hH187, hL, -⟩ := exists_sec18H_of_hyp201One h
  set K := normalClosureIn M c with hKdef
  obtain ⟨⟨hKC, -⟩, -, htype⟩ := h189 G A M H c hH18 hH187
  have hKperf : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hKC
  have hKsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases htype with ⟨n, -, ⟨e⟩, -⟩ | ⟨n, hn, hn0, ⟨e⟩, -⟩
    · have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
          (GaloisField 2 n)) :=
        CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
      exact (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
    · have : IsSimpleGroup ↥(projSL 2 (GaloisField 2 n)) :=
        Sec11.LSSolvableProof.isSimpleGroup_projSL (by obtain ⟨k, hk⟩ := hn; omega)
      exact e.isSimpleGroup
  have hKqperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hc3 : orderOf c = 3 := Res6.orderOf_c_of_hyp201One h184 h
  have hne : K ≠ K₀ := fun heq => hcK₀ (heq ▸ hcK)
  have hA := isE27_of_mem_partTwoE h.1.mem_partTwoE
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_of_hyp201One h1812 h184 h
  have hB23 : A ⊓ L ≤ (Sec4.oTwoP 3 ↥M).map M.subtype := by
    rw [hL]
    exact h185 G A M H c hH18
  set B := A ⊓ L with hBdef
  have hB3 : IsPGroup 3 B := hA.isPGroup.to_le inf_le_left
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨b, hb.1⟩ : A) ⟨b', hb'.1⟩)
  have hBM : B ≤ M := hB23.trans (Subgroup.map_subtype_le _)
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ1 : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal h.1.mem_scriptM.1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hπ1 : ∀ x : M, π x = 1 ↔ (x : G) ∈ Q := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Sec18.mem_pCore_iff_mem_pCoreOf]
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hKC
  have hK₀M : K₀ ≤ M := le_of_mem_oTwoComponentsIn hK₀
  set Fs := (B.subgroupOf M).map π with hFs
  set Js := (K.subgroupOf M).map π with hJs
  set J₂s := (K₀.subgroupOf M).map π with hJ₂s
  have hcommB : ∀ {J : Subgroup G}, J ∈ oTwoComponentsIn M →
      ∀ y ∈ Fs, ∀ z ∈ (J.subgroupOf M).map π, y * z = z * y := by
    intro J hJ
    rintro _ ⟨b, hb, rfl⟩ _ ⟨k, hk, rfl⟩
    have h1 := Res7.comm_mem_pCoreOf_of_mem_oTwoP hJ (hB23 (Subgroup.mem_subgroupOf.mp hb))
      (Subgroup.mem_subgroupOf.mp hk)
    have h2 : π (b * k * b⁻¹ * k⁻¹) = 1 := (hπ1 _).mpr (by simpa using h1)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact Res7.mul_comm_of_comm_eq_one h2
  have hcommFJ := hcommB hKC
  have hcommFJ₂ := hcommB hK₀
  have hcommJJ₂ : ∀ y ∈ Js, ∀ z ∈ J₂s, y * z = z * y := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    exact Sec19.Step1910Proof.mk_mul_comm_of_ne hKC hK₀ hne (Subgroup.mem_subgroupOf.mp hk)
      (Subgroup.mem_subgroupOf.mp hk')
  set xs := π ⟨c, hKM hcK⟩ with hxs
  have hxsJ : xs ∈ Js := ⟨⟨c, hKM hcK⟩, Subgroup.mem_subgroupOf.mpr hcK, rfl⟩
  have hxsnc : ∃ z ∈ Js, xs * z ≠ z * xs := by
    by_contra hcon
    push Not at hcon
    have hcO : c ∈ CFSG.Open.pCoreOf 2 K := by
      refine Res7.mem_pCoreOf_of_forall_comm_of_simple hKsimple hKqperf hcK (fun k hk => ?_)
      have h1 := hcon (π ⟨k, hKM hk⟩) ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have h2 : π (⟨c, hKM hcK⟩ * ⟨k, hKM hk⟩ * (⟨c, hKM hcK⟩ : M)⁻¹ *
          (⟨k, hKM hk⟩ : M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxs, h1]
        group
      have h3 := (hπ1 _).mp h2
      refine Sec19.Step1910Proof.inf_pCoreOf_le hKC ⟨?_, by simpa using h3⟩
      exact K.mul_mem (K.mul_mem (K.mul_mem hcK hk) (K.inv_mem hcK)) (K.inv_mem hk)
    exact Res6.not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hc3 hcO
  have hK₀perf : Group.IsPerfect K₀ := isPerfect_of_mem_oTwoComponentsIn hK₀
  have hZperf : Group.IsPerfect (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZ3 : 3 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K₀)
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₀)).exists_card_eq
    rw [hb] at h1
    rw [h1] at h3
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right b (by norm_num)) h3
  obtain ⟨ē, he3, hec⟩ := CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect
    (p := 3) (by norm_num) hZperf hZ3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₀) ē
  set x₂s := π ⟨(x : G), hK₀M x.2⟩ with hx₂s
  have hx₂sJ : x₂s ∈ J₂s := ⟨_, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hx3 : (x : G) ^ 3 ∈ Q := by
    have h1 : x ^ 3 ∈ CFSG.pCore 2 ↥K₀ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact he3
    have h2 := (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
    exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK₀ (by simpa using h2)
  have hx₂snc : ∃ z ∈ J₂s, x₂s * z ≠ z * x₂s := by
    rw [Subgroup.mem_center_iff] at hec
    push Not at hec
    obtain ⟨w, hw⟩ := hec
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₀) w
    refine ⟨π ⟨(j : G), hK₀M j.2⟩, ⟨_, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩, fun hjx => hw ?_⟩
    have h2 : π (⟨(x : G), hK₀M x.2⟩ * ⟨(j : G), hK₀M j.2⟩ * (⟨(x : G), hK₀M x.2⟩ : M)⁻¹ *
        (⟨(j : G), hK₀M j.2⟩ : M)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hx₂s, hjx]
      group
    have h3 := (hπ1 _).mp h2
    have h4 : ((x * j * x⁻¹ * j⁻¹ : ↥K₀) : G) ∈ CFSG.Open.pCoreOf 2 K₀ :=
      Sec19.Step1910Proof.inf_pCoreOf_le hK₀ ⟨(x * j * x⁻¹ * j⁻¹ : ↥K₀).2, by simpa using h3⟩
    have h5 : x * j * x⁻¹ * j⁻¹ ∈ CFSG.pCore 2 ↥K₀ := (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr h4
    have h6 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K₀)) (x * j * x⁻¹ * j⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h5
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h6
    exact (Res7.mul_comm_of_comm_eq_one h6).symm
  have hx₂sF : x₂s ∉ Fs := by
    intro hF
    obtain ⟨z, hz, hzx⟩ := hx₂snc
    exact hzx (hcommFJ₂ _ hF z hz)
  set V₁ := Fs ⊔ Subgroup.zpowers x₂s with hV₁
  have hV₁C : V₁ ≤ Subgroup.centralizer (Js : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (hcommFJ y hy z hz).symm) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => hcommJJ₂ z hz x₂s hx₂sJ
  have hxsV₁ : xs ∉ V₁ := by
    intro hV
    obtain ⟨z, hz, hzx⟩ := hxsnc
    exact hzx (Subgroup.mem_centralizer_iff.mp (hV₁C hV) z hz).symm
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxs, ← map_pow]
    refine (hπ1 _).mpr ?_
    rw [show ((⟨c, hKM hcK⟩ ^ 3 : M) : G) = c ^ 3 from rfl, ← hc3, pow_orderOf_eq_one]
    exact Q.one_mem
  have hx₂s3 : x₂s ^ 3 = 1 := by
    rw [hx₂s, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hx3)
  have hxso : orderOf xs = 3 := orderOf_eq_prime hxs3 (fun h => hxsV₁ (h ▸ V₁.one_mem))
  have hx₂so : orderOf x₂s = 3 := orderOf_eq_prime hx₂s3 (fun h => hx₂sF (h ▸ Fs.one_mem))
  have hFscard : Nat.card Fs = 9 := by
    have h1 := card_eq_card_map_mul_inf_ker π (B.subgroupOf M)
    have h2 : Nat.card ↥(B.subgroupOf M ⊓ π.ker) = 1 := by
      refine card_inf_eq_one_of_isPGroup hB3.comap_subtype ?_
      rw [hπ, QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup
    rw [h2, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hB9] at h1
    exact h1.symm
  have hV₁card : Nat.card V₁ = 27 := by
    rw [hV₁, Res7.card_sup_zpowers Fs hx₂so hx₂sF (fun z hz => hcommFJ₂ z hz x₂s hx₂sJ),
      hFscard]
  set V := V₁ ⊔ Subgroup.zpowers xs with hV
  have hV₁x : ∀ z ∈ V₁, z * xs = xs * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hV₁C hz) xs hxsJ).symm
  have hVcard : Nat.card V = 81 := by
    rw [hV, Res7.card_sup_zpowers V₁ hxso hxsV₁ hV₁x, hV₁card]
  have hT : ∀ a ∈ ((Fs : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∪ {x₂s, xs}),
      ∀ b ∈ ((Fs : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∪ {x₂s, xs}), a * b = b * a := by
    have hFF : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hf) _
        (Subgroup.mem_subgroupOf.mp hf'))
    have hxx : x₂s * xs = xs * x₂s := (hcommJJ₂ xs hxsJ x₂s hx₂sJ).symm
    intro a ha b hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
    · exact hFF a ha b hb
    · rw [Set.mem_singleton_iff.mp hb]; exact hcommFJ₂ a ha _ hx₂sJ
    · rw [Set.mem_singleton_iff.mp hb]; exact hcommFJ a ha _ hxsJ
    · rw [ha]; exact (hcommFJ₂ b hb _ hx₂sJ).symm
    · rw [ha, Set.mem_singleton_iff.mp hb]
    · rw [ha, Set.mem_singleton_iff.mp hb]; exact hxx
    · rw [Set.mem_singleton_iff.mp ha]; exact (hcommFJ b hb _ hxsJ).symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]; exact hxx.symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  have hVcl : V = Subgroup.closure ((Fs : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∪ {x₂s, xs}) := by
    rw [hV, hV₁, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_eq Fs, ← Subgroup.closure_union, ← Subgroup.closure_union,
      Subgroup.closure_eq Fs, Set.union_assoc, Set.insert_eq]
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    rw [hVcl] at ha hb
    exact KFacts.KS14.commute_of_mem_closure hT ha hb
  have hVe : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    have hv' := hv
    rw [hVcl] at hv'
    induction hv' using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨f, hf, rfl⟩ | ha | ha
      · rw [← map_pow]
        refine (hπ1 _).mpr ?_
        rw [show ((f ^ 3 : M) : G) = (f : G) ^ 3 from rfl,
          hA.1.2 _ (Subgroup.mem_subgroupOf.mp hf).1]
        exact Q.one_mem
      · rw [Set.mem_singleton_iff.mp ha]; exact hx₂s3
      · rw [Set.mem_singleton_iff.mp ha]; exact hxs3
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hVcomm a (hVcl ▸ ha) b (hVcl ▸ hb)) 3), iha (hVcl ▸ ha),
        ihb (hVcl ▸ hb), one_mul]
    | inv a ha iha => rw [inv_pow, iha (hVcl ▸ ha), inv_one]
  have h4 := Res7.four_le_localRank_of_quotient hQ1 V hVcomm hVe hVcard.ge
  rw [h.1.toTheoremFourHyp.localRank_three] at h4
  omega

end CFSG.RankThree.PartTwo.Sec20
