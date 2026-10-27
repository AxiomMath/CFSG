module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Sec12Fus

theorem exists_mem_of_range_pGroup {H M : Type*} [Group H] [Finite H] [Group M] {p : ℕ}
    (hp : p.Prime) (f : H →* M) (hf : IsPGroup p f.range) {S : Subgroup H} (hS : ¬ p ∣ S.index)
    {m : M} (hm : m ∈ f.range) : ∃ s ∈ S, f s = m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hf' : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective _ hf'
  have hdvd : (S.map f.rangeRestrict).index ∣ S.index := Subgroup.index_map_dvd S hf'
  obtain ⟨n, hn⟩ := hf.exists_card_eq
  have h1 : (S.map f.rangeRestrict).index ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hj0 : j = 0 := by
    by_contra hj0
    apply hS
    have : p ∣ (S.map f.rangeRestrict).index := by
      rw [hj]
      exact dvd_pow_self p hj0
    exact this.trans hdvd
  rw [hj0, pow_zero] at hj
  have htop : S.map f.rangeRestrict = ⊤ := Subgroup.index_eq_one.1 hj
  have hmem : (⟨m, hm⟩ : f.range) ∈ S.map f.rangeRestrict := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsm⟩ := hmem
  exact ⟨s, hs, congrArg Subtype.val hsm⟩

theorem exists_mem_of_mem_pCore [Finite G] {p : ℕ} (hp : p.Prime) {E X : Subgroup G}
    (hX : IsSylowOf p X (xPreimage p E)) (φ : ↥(CFSG.pCore p ↥(torusWeyl E))) :
    ∃ (x : G) (hx : x ∈ Subgroup.normalizer (E : Set G)), x ∈ X ∧
      E.normalizerMonoidHom ⟨x, hx⟩ = ((φ : ↥(torusWeyl E)) : MulAut E) := by
  classical
  have hYN : xPreimage p E ≤ Subgroup.normalizer (E : Set G) := Subgroup.map_subtype_le _
  let f : ↥(xPreimage p E) →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hrange : IsPGroup p f.range := by
    have hXp : IsPGroup p ((CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype) :=
      CFSG.pCore_isPGroup.map _
    refine hXp.to_le ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨hw, hmem⟩ := mem_xPreimage_iff.1 y.2
    exact hmem
  have hφW : ((φ : ↥(torusWeyl E)) : MulAut E) ∈ E.normalizerMonoidHom.range :=
    (φ : ↥(torusWeyl E)).2
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hφW
  have hwY : (w : G) ∈ xPreimage p E := by
    rw [mem_xPreimage_iff]
    refine ⟨w.2, ?_⟩
    have : E.normalizerMonoidHom ⟨(w : G), w.2⟩ = ((φ : ↥(torusWeyl E)) : MulAut E) := hw
    rw [this]
    exact ⟨φ, φ.2, rfl⟩
  have hmem : ((φ : ↥(torusWeyl E)) : MulAut E) ∈ f.range := ⟨⟨w, hwY⟩, hw⟩
  obtain ⟨s, hs, hsφ⟩ := exists_mem_of_range_pGroup hp f hrange
    (S := X.subgroupOf (xPreimage p E)) hX.2.2 hmem
  exact ⟨(s : G), hYN s.2, Subgroup.mem_subgroupOf.1 hs, hsφ⟩

theorem not_le_theta_of_isQuasisimple [Finite G] {p : ℕ} (hp : p.Prime) {I K : Subgroup G}
    (hK : CFSG.IsQuasisimple ↥K) (hKθ : K ≤ inSubgroup (aschbacherSolvableCore p) I) : False := by
  have hθsol := (theta_solvable_and_not_dvd hp I).1
  have hsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKθ)
      (Subgroup.inclusion_injective hKθ)
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 (Sec125.ne_bot_of_isQuasisimple hK)
  have := hK.1
  exact Group.IsPerfect.not_isSolvable ↥K hsol

theorem commutator_eq_bot_of_le_theta [Finite G] {p : ℕ} (hp : p.Prime) {I K X : Subgroup G}
    (hK : CFSG.IsQuasisimple ↥K) (hX : X ≤ Subgroup.normalizer (K : Set G))
    (hθ : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I) :
    ⁅K, X⁆ = ⊥ := by
  by_contra hne
  have hKfull := Sec125.commutator_eq_of_ne_bot hK hX hne
  refine not_le_theta_of_isQuasisimple hp hK (I := I) ?_
  calc K = ⁅K, X⁆ := hKfull.symm
    _ ≤ inSubgroup (aschbacherSolvableCore p) I := by
      rw [Subgroup.commutator_le]
      intro k hk x hx
      have e : ⁅k, x⁆ = (x * k * x⁻¹ * k⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.inv_mem _ (hθ x hx k hk)

theorem commutator_eq_or_trivial [Finite G] {p : ℕ} (hp : p.Prime) {b : G} {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p b) {a : G} (ha : a ∈ Subgroup.normalizer (I : Set G)) :
    ⁅I, Subgroup.zpowers a⁆ = I ∨
      ∀ i ∈ I, a * i * a⁻¹ * i⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I := by
  classical
  have hX : Subgroup.zpowers a ≤ Subgroup.normalizer (I : Set G) := Subgroup.zpowers_le.2 ha
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  have hperf : Group.IsPerfect ↥I := isPerfect_of_mem_thetaComponentsAt hI
  have hle : ⁅I, Subgroup.zpowers a⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro k hk x hx
    have h1 := I.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hX hx) k⁻¹).mp (I.inv_mem hk))
    simpa [commutatorElement_def, mul_assoc] using h1
  have hnorm : (⁅I, Subgroup.zpowers a⁆.subgroupOf I).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.commutator_le_sup I (Subgroup.zpowers a))).mp
      (CFSG.commutator_normal_in_sup I (Subgroup.zpowers a))
    exact le_sup_left.trans h1
  have hRq : ((⁅I, Subgroup.zpowers a⁆.subgroupOf I).map
      (QuotientGroup.mk' (aschbacherSolvableCore p ↥I))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hRq with htop | hcen
  · left
    refine le_antisymm hle ?_
    have hR'top : ⁅I, Subgroup.zpowers a⁆.subgroupOf I = ⊤ := by
      have : (⁅I, Subgroup.zpowers a⁆.subgroupOf I).Normal := hnorm
      have : Group.IsPerfect ↥I := hperf
      have hsolv : Group.IsSolvable (aschbacherSolvableCore p ↥I) :=
        (solvable_prime_complement_core_characterization (H := ↥I) hp).1
      have hdec : ∀ x : ↥I, ∃ r ∈ ⁅I, Subgroup.zpowers a⁆.subgroupOf I,
          ∃ n ∈ aschbacherSolvableCore p ↥I, x = r * n := by
        intro x
        have hx : QuotientGroup.mk' (aschbacherSolvableCore p ↥I) x ∈
            (⁅I, Subgroup.zpowers a⁆.subgroupOf I).map
              (QuotientGroup.mk' (aschbacherSolvableCore p ↥I)) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨r, hr, hrx⟩ := hx
        refine ⟨r, hr, r⁻¹ * x, ?_, by group⟩
        exact QuotientGroup.eq.1 hrx
      let g : aschbacherSolvableCore p ↥I →* ↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I :=
        (QuotientGroup.mk' _).comp (aschbacherSolvableCore p ↥I).subtype
      have hg : Function.Surjective g := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨r, hr, n, hn, rfl⟩ := hdec x
        refine ⟨⟨n, hn⟩, ?_⟩
        show ((n : ↥I) : ↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) =
          ((r * n : ↥I) : ↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I)
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff r).2 hr, one_mul]
      have : Group.IsSolvable (↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) :=
        Group.isSolvable_of_surjective hg
      have : Group.IsPerfect (↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      have hsub : Subsingleton (↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) := by
        by_contra hns
        have : Nontrivial (↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) :=
          not_subsingleton_iff_nontrivial.1 hns
        exact Group.IsPerfect.not_isSolvable (↥I ⧸ ⁅I, Subgroup.zpowers a⁆.subgroupOf I) inferInstance
      exact eq_top_iff.2 fun x _ => (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
    exact Subgroup.subgroupOf_eq_top.mp hR'top
  · right
    have : Group.IsPerfect (↥I ⧸ aschbacherSolvableCore p ↥I) := hq.1
    have hα : thetaQuotientConj p I ⟨a, ha⟩ = 1 := by
      refine CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center _ ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H k =>
        rw [thetaQuotientConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        apply hcen
        refine ⟨k⁻¹ * I.normalizerMonoidHom ⟨a, ha⟩ k, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
        have h1 : ((k⁻¹ * I.normalizerMonoidHom ⟨a, ha⟩ k : ↥I) : G) = ⁅(k : G)⁻¹, a⁆ := by
          rw [commutatorElement_def]
          simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
          group
        rw [h1]
        exact Subgroup.commutator_mem_commutator (I.inv_mem k.2) (Subgroup.mem_zpowers a)
    exact fun i hi => (thetaQuotientConj_eq_one_iff p I ⟨a, ha⟩).1 hα i hi

end Sec12Fus

theorem node1213Move_of_inputs : Node1213Move := by
  classical
  intro G _ _ p A c L E ctx b K I X P Q hL hC
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcA : c ∈ A := h.c_mem
  have hcE : c ∈ E := h.A_le_E hcA
  have hcL : c ∉ L := ctx.c_not_mem
  have hcp : c ^ p = 1 := hApow c hcA
  have hKL : K ≤ L := by
    rw [hL.K_eq]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hKne : K ≠ ⊥ := Sec125.ne_bot_of_isQuasisimple hL.K_qs
  obtain ⟨d, hdAK, hd1⟩ : ∃ d ∈ A ⊓ K, d ≠ 1 := by
    have hne : A ⊓ K ≠ ⊥ := by
      intro hbot
      have h1 := hL.A_K
      rw [hbot, Subgroup.card_bot] at h1
      exact hp.one_lt.ne h1
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩
  have hdA : d ∈ A := hdAK.1
  have hdK : d ∈ K := hdAK.2
  have hdp : d ^ p = 1 := hApow d hdA
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hcdc : c * d = d * c := hAcomm c hcA d hdA
  have hcdE : c * d ∈ E := E.mul_mem hcE (h.A_le_E hdA)
  have hcdL : c * d ∉ L := fun hm => hcL (by
    have := L.mul_mem hm (L.inv_mem (hKL hdK))
    simpa using this)
  obtain ⟨φ, ⟨k, hk⟩, -⟩ := ctx.eleven.2.1 ⟨c, hcE⟩ ⟨c * d, hcdE⟩ hcL hcdL
  obtain ⟨x, hxN, hxX, hxφ⟩ := Sec12Fus.exists_mem_of_mem_pCore hp hC.X_sylow.1 φ
  have hxc : x * c * x⁻¹ = c ^ k * d ^ k := by
    have h1 := Equivariance.coe_conjAut hxN ⟨c, hcE⟩
    have h2 : (conjAut E x hxN) ⟨c, hcE⟩ = (⟨c * d, hcdE⟩ : E) ^ k := by
      show (E.normalizerMonoidHom ⟨x, hxN⟩) ⟨c, hcE⟩ = _
      rw [hxφ]
      exact hk
    rw [h2] at h1
    rw [← Commute.mul_zpow (show Commute c d from hcdc) k]
    have h3 := h1.symm
    simpa using h3
  have hXP : X ≤ P := hC.P_sylow.2
  have hEX : E ≤ X := hC.X_sylow.2
  have hxI : x ∈ Subgroup.normalizer (I : Set G) := hC.P_norm (hXP hxX)
  have hcI : c ∈ Subgroup.normalizer (I : Set G) := hC.P_norm (hXP (hEX hcE))
  have hdI : d ∈ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer (hL.K_le hdK)
  have hcomm : ⁅I, Subgroup.zpowers c⁆ = I := by
    rcases Sec12Fus.commutator_eq_or_trivial hp hL.I_mem hcI with h1 | h1
    · exact h1
    · exfalso
      have hgc : thetaQuotientConj p I ⟨c, hcI⟩ = 1 :=
        (thetaQuotientConj_eq_one_iff p I ⟨c, hcI⟩).2 h1
      have hgd : (⟨d, hdI⟩ : Subgroup.normalizer (I : Set G)) ^ k =
          (⟨c, hcI⟩ : Subgroup.normalizer (I : Set G)) ^ (-k) *
            ((⟨x, hxI⟩ : Subgroup.normalizer (I : Set G)) * ⟨c, hcI⟩ * ⟨x, hxI⟩⁻¹) := by
        apply Subtype.ext
        show d ^ k = c ^ (-k) * (x * c * x⁻¹)
        rw [hxc]
        group
      have hφz : thetaQuotientConj p I ((⟨d, hdI⟩ : Subgroup.normalizer (I : Set G)) ^ k) = 1 := by
        rw [hgd]
        simp only [map_mul, map_zpow, map_inv, hgc, one_zpow, mul_one, mul_inv_cancel]
      have hdk : ∀ j : ℤ, ∀ i ∈ I, (d ^ k) ^ j * i * ((d ^ k) ^ j)⁻¹ * i⁻¹ ∈
          inSubgroup (aschbacherSolvableCore p) I := by
        intro j i hi
        have hmem : thetaQuotientConj p I
            (((⟨d, hdI⟩ : Subgroup.normalizer (I : Set G)) ^ k) ^ j) = 1 := by
          rw [map_zpow, hφz, one_zpow]
        exact (thetaQuotientConj_eq_one_iff p I _).1 hmem i hi
      have hzK : d ^ k ∈ K := Subgroup.zpow_mem K hdK k
      have hKz : ⁅K, Subgroup.zpowers (d ^ k)⁆ = ⊥ := by
        refine Sec12Fus.commutator_eq_bot_of_le_theta hp hL.K_qs (I := I)
          ((Subgroup.zpowers_le.2 hzK).trans Subgroup.le_normalizer) ?_
        intro y hy k' hk'
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact hdk j k' (hL.K_le hk')
      have hzc : (⟨d ^ k, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        have h2 : ⁅(w : G), d ^ k⁆ ∈ ⁅K, Subgroup.zpowers (d ^ k)⁆ :=
          Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers _)
        rw [hKz, Subgroup.mem_bot] at h2
        exact commutatorElement_eq_one_iff_mul_comm.1 h2
      have hd1k : d ^ k = 1 := by
        have hzp : (d ^ k) ^ p = 1 := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
        have hγ : (⟨(⟨d ^ k, hzK⟩ : ↥K), hzc⟩ : ↥(Subgroup.center ↥K)) ^ (p ^ 1) = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa using hzp
        have h4 := Sec12Fus.eq_one_of_pow_eq_one_of_not_dvd hp hL.K_center hγ
        exact congrArg (fun y : ↥(Subgroup.center ↥K) => (((y : ↥K) : G))) h4
      have hpk : (p : ℤ) ∣ k := by
        have h4 := (orderOf_dvd_iff_zpow_eq_one).2 hd1k
        rwa [hdord] at h4
      have hck : c ^ k = 1 := by
        obtain ⟨m, rfl⟩ := hpk
        rw [zpow_mul, zpow_natCast, hcp, one_zpow]
      have h3 : x * c * x⁻¹ = 1 := by rw [hxc, hck, hd1k, one_mul]
      have hc1 : c = 1 := by
        have h5 : c = x⁻¹ * (x * c * x⁻¹) * x := by group
        rw [h5, h3]
        group
      exact h.c_ne_one hc1
  have hne : K ≠ I := by
    intro hKI
    have hKc : ⁅K, Subgroup.zpowers c⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro y hy z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hLc (hKL hy))
      rw [Subgroup.mem_bot]
      exact Commute.commutator_eq (Commute.zpow_right (show Commute y c from hyc) i)
    apply hKne
    have hI0 : I = ⊥ := by
      rw [← hcomm, ← hKI]
      exact hKc
    rw [hKI]
    exact hI0
  exact ⟨hne, hcomm⟩

end CFSG.RankThree.PartOne
