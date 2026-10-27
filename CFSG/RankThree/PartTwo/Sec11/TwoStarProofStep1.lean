module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofComponent
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.LocalRank.ThetaCoreQuotients
public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.Theta.TwoPlaneAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace TwoStarProof

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev autHom (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)

theorem autHom_of_mem {L : Subgroup G} {z : G} (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (hzL : z ∈ L) :
    autHom L ⟨z, hzN⟩ = MulAut.conj ((⟨z, hzL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H w =>
    rw [MulAut.conj_apply]
    change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨z, hzN⟩)
      (w : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem commutator_mem_theta_of_autHom_eq_one {L : Subgroup G} {q : G}
    (hqN : q ∈ Subgroup.normalizer (L : Set G)) (hq : autHom L ⟨q, hqN⟩ = 1) {l : G}
    (hl : l ∈ L) : q * l * q⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have := Sec4.aschbacherSolvableCore_characteristic L
  have h1 := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
    φ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) hq
  change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨q, hqN⟩)
    ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) at h1
  rw [Sec4.thetaQuotMulAut_mk, QuotientGroup.eq] at h1
  set x : L := Sec4.compAction L ⟨q, hqN⟩ ⟨l, hl⟩ with hx
  have hxv : (x : G) = q * l * q⁻¹ := rfl
  have h2 : x * (⟨l, hl⟩ : L)⁻¹ ∈ aschbacherSolvableCore 3 L := by
    have h3 := (inferInstance : (aschbacherSolvableCore 3 L).Normal).conj_mem _ h1 x
    have e : x * (x⁻¹ * ⟨l, hl⟩) * x⁻¹ = ⟨l, hl⟩ * x⁻¹ := by group
    rw [e] at h3
    have h4 := Subgroup.inv_mem _ h3
    rwa [mul_inv_rev, inv_inv] at h4
  refine ⟨_, h2, ?_⟩
  simp [hxv]

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

theorem autHom_eq_one_of_component {L : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 (3 * m)))
    {y : G} (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : y ^ 3 = 1)
    (hy1 : autHom L ⟨y, hyN⟩ ≠ 1) {Q : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G)) (hQy : Q ≤ Subgroup.centralizer ({y} : Set G))
    (hLQ : ∀ z ∈ L, y * z = z * y → z ∈ Subgroup.normalizer (Q : Set G))
    {q : G} (hq : q ∈ Q) : autHom L ⟨q, hQN hq⟩ = 1 := by
  set N := Subgroup.normalizer (L : Set G) with hN
  set ψ := autHom L with hψ
  set Qh : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := (Q.subgroupOf N).map ψ with hQh
  have hQh2 : IsPGroup 2 Qh :=
    (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm).map ψ
  have hy3' : ψ ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hQy' : ∀ φ ∈ Qh, φ * ψ ⟨y, hyN⟩ = ψ ⟨y, hyN⟩ * φ := by
    rintro _ ⟨q', hq', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQy hq'))
  have hQn' : ∀ x : L ⧸ aschbacherSolvableCore 3 L, ψ ⟨y, hyN⟩ x = x →
      ∀ φ ∈ Qh, MulAut.conj x * φ * (MulAut.conj x)⁻¹ ∈ Qh := by
    intro x hx φ hφ
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, hzw, hzy⟩ := exists_lift_of_fixed hyN hy3 w hx
    have hzN : (z : G) ∈ N := Subgroup.le_normalizer z.2
    have hconj : MulAut.conj (w : L ⧸ aschbacherSolvableCore 3 L) = ψ ⟨z, hzN⟩ := by
      rw [hψ, autHom_of_mem hzN z.2]
      exact congrArg MulAut.conj hzw.symm
    obtain ⟨q', hq', rfl⟩ := hφ
    rw [hconj]
    have hmemQ : (⟨z, hzN⟩ * q' * ⟨z, hzN⟩⁻¹ : N) ∈ Q.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have hq'Q : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq'
      have h1 := (Subgroup.mem_normalizer_iff.mp (hLQ z z.2 hzy) (q' : G)).mp hq'Q
      simpa using h1
    have h2 := Subgroup.mem_map_of_mem ψ hmemQ
    rwa [map_mul, map_mul, map_inv] at h2
  have hbot := twoStar_component_L2Field hm e hy3' hy1 hQh2 hQy' hQn'
  have hmem : ψ ⟨q, hQN hq⟩ ∈ Qh := ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem le_theta_of_commutator_mem {C L Q : Subgroup G} (hLC : L ≤ C)
    (hCL : C ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ C ⊓ Subgroup.centralizer ({d} : Set G))
    (hNQ : C ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) C) :
    Q ≤ inSubgroup (aschbacherSolvableCore 3) C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, -, -, -, hθr⟩ :=
    solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  set θ := aschbacherSolvableCore 3 C with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hQC' : Q ≤ C := hQC.trans inf_le_left
  have hL'n : (L.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hCL
  set Lb := (L.subgroupOf C).map π with hLb
  have hLbn : Lb.Normal := hL'n.map π hπs
  set W := Subgroup.centralizer (Lb : Set (C ⧸ θ)) with hW
  set Qb := (Q.subgroupOf C).map π with hQb
  have hQb2 : IsPGroup 2 Qb := (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC').symm).map π
  have hO : CFSG.pCore 2 (C ⧸ θ) = ⊥ := by
    have h1 := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_quotient_centralizers
      Nat.prime_three θ hθs hθ3).2.2.1
    have h2 := (solvable_prime_complement_core_characterization (H := C ⧸ θ)
      Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
    rw [h1] at h2
    exact le_bot_iff.mp h2
  have hQbW : Qb ≤ W := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hW, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hQL q (Subgroup.mem_subgroupOf.mp hq) l (Subgroup.mem_subgroupOf.mp hl)
    obtain ⟨z, hz, hzv⟩ := h1
    have hz' : z = q * l * q⁻¹ * l⁻¹ := Subtype.ext (by simpa using hzv)
    have h2 : π (q * l * q⁻¹ * l⁻¹) = 1 := by
      rw [← hz', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    simp only [map_mul, map_inv] at h2
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm
  set d' : C := ⟨d, hLC hdL⟩ with hd'
  have hd'3 : IsPGroup 3 (Subgroup.zpowers d') := by
    have hdvd : orderOf d' ∣ 3 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hd3))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hWN : W ≤ Subgroup.normalizer (Qb : Set (C ⧸ θ)) := by
    intro w hw
    have hdb : π d' ∈ Lb := ⟨d', Subgroup.mem_subgroupOf.mpr hdL, rfl⟩
    have hw' : w ∈ Subgroup.centralizer (((Subgroup.zpowers d').map π) : Set (C ⧸ θ)) := by
      rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute (π d') w := Subgroup.mem_centralizer_iff.mp hw _ hdb
      exact (hc.zpow_left k).eq
    have hker : ¬ 3 ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hθ3
    obtain ⟨w₀, hw₀, rfl⟩ :=
      exists_centralizer_preimage_of_pGroup_prime_complement_kernel
        3 Nat.prime_three π hπs hker _ hd'3 w hw'
    have hw₀d : (w₀ : G) ∈ C ⊓ Subgroup.centralizer ({d} : Set G) := by
      refine ⟨w₀.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hw₀ d' (Subgroup.mem_zpowers d')
      exact (congrArg Subtype.val this).symm
    have hw₀N : w₀ ∈ Subgroup.normalizer ((Q.subgroupOf C) : Set C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using (Subgroup.mem_normalizer_iff.mp (hNQ hw₀d) x)
    exact Subgroup.le_normalizer_map π ⟨w₀, hw₀N, rfl⟩
  have hQbO : Qb ≤ CFSG.pCore 2 (C ⧸ θ) := by
    have h1 : Qb ≤ inSubgroup (CFSG.pCore 2) W :=
      SteinbergBY.le_inSubgroup_pCore hQb2 hQbW hWN
    refine h1.trans (le_sSup ⟨⟨fun n hn g => ?_⟩, SteinbergBY.isPGroup_inSubgroup_pCore 2 W⟩)
    have hWn : W.Normal := by
      have := hLbn
      exact Subgroup.normal_centralizer
    have hg : g ∈ Subgroup.normalizer (W : Set (C ⧸ θ)) :=
      Subgroup.mem_normalizer_iff.mpr fun n =>
        ⟨fun hn => hWn.conj_mem n hn g, fun hn => by
          have h1 := hWn.conj_mem _ hn g⁻¹
          rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at h1⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 W hg) n).mp hn
  rw [hO] at hQbO
  intro q hq
  have h1 : π ⟨q, hQC' hq⟩ = 1 := by
    have := hQbO ⟨⟨q, hQC' hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rwa [Subgroup.mem_bot] at this
  have h2 : (⟨q, hQC' hq⟩ : C) ∈ θ := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  exact ⟨_, h2, rfl⟩

end TwoStarProof

end CFSG.RankThree.PartTwo.Sec11
