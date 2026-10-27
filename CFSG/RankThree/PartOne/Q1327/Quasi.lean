module

public import CFSG.RankThree.PartOne.Q1327.Comp
public import CFSG.RankThree.PartOne.Q1327.QuasiAbs
import CFSG.RankThree.PartOne.S10.LocalThetaComponentEmbeddingFrontier
public import CFSG.RankThree.PartOne.N143.SectionReduce

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Torsion37
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem Jof_le_normalizer (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) : Jof p R ≤ Subgroup.normalizer (Jc : Set G) := by
  have h := H.h12
  have hp := h.prime
  have he : CFSG.Assembly.evenRank ↥(Subgroup.centralizer (R : Set G)) ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  rw [Jof_def]
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxM, k, hk⟩
  have hx' : ∃ k : ℕ, orderOf (⟨x, hxM⟩ : ↥(Subgroup.centralizer (R : Set G))) = p ^ k :=
    ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩
  have hmem := selected_prime_elements_normalize_theta_components.1
    ↥(Subgroup.centralizer (R : Set G)) he p hp h.three_lt _ hx' _ hJ.mem
  have h1 := Subgroup.mem_normalizer_iff.mp hmem
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have := (h1 ⟨g, hJ.le_M hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hg
    have hgM : g ∈ Subgroup.centralizer (R : Set G) := by
      have : x⁻¹ * (x * g * x⁻¹) * x ∈ Subgroup.centralizer (R : Set G) :=
        mul_mem (mul_mem (inv_mem hxM) (hJ.le_M hg)) hxM
      simpa [mul_assoc] using this
    have := (h1 ⟨g, hgM⟩).mpr (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp this

theorem Jc_perfect_quasi (hp : p.Prime) {Jc : Subgroup G} (hJ : JcData p E c R s Jc) :
    Group.IsPerfect ↥Jc ∧
      CFSG.IsQuasisimple (↥Jc ⧸ aschbacherSolvableCore p ↥Jc) := by
  have e := Subgroup.subgroupOfEquivOfLe hJ.le_M
  have hm := hJ.mem
  refine ⟨?_, ?_⟩
  · have := hm.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)) hm.2.2

omit [Finite G] in
theorem subgroupOf_simple_perfect {Jc K : Subgroup G} (hKJ : K ≤ Jc) (hKq : CFSG.IsQuasisimple ↥K)
    (hKz : Subgroup.center ↥K = ⊥) :
    IsSimpleGroup ↥(K.subgroupOf Jc) ∧ Group.IsPerfect ↥(K.subgroupOf Jc) := by
  obtain ⟨-, hsimple, -⟩ := N143.simple_of_quasisimple_center_bot hKq hKz
  have e := Subgroup.subgroupOfEquivOfLe hKJ
  refine ⟨e.isSimpleGroup, ?_⟩
  have := hKq.1
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem p_dvd_card_simple (hp : p.Prime) {Jc K : Subgroup G} (hKJ : K ≤ Jc)
    (hKq : CFSG.IsQuasisimple ↥K) (hKz : Subgroup.center ↥K = ⊥) {x : G} (hxK : x ∈ K)
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    p ∣ Nat.card ((↥Jc ⧸ aschbacherSolvableCore p ↥Jc) ⧸
      Subgroup.center (↥Jc ⧸ aschbacherSolvableCore p ↥Jc)) := by
  by_contra hnd
  set ψ := (QuotientGroup.mk' (Subgroup.center (↥Jc ⧸ aschbacherSolvableCore p ↥Jc))).comp
    (QuotientGroup.mk' (aschbacherSolvableCore p ↥Jc)) with hψ
  have hWs : Group.IsSolvable ψ.ker := LocalEmbeddingFrontier.isSolvable_ker_central_quotient hp
  obtain ⟨hsimple', hperf'⟩ := subgroupOf_simple_perfect hKJ hKq hKz
  have hinf := inf_solvable_normal_eq_bot hperf' inferInstance hsimple'
    (inferInstance : ψ.ker.Normal) hWs
  have hx'K : (⟨x, hKJ hxK⟩ : ↥Jc) ∈ K.subgroupOf Jc := Subgroup.mem_subgroupOf.mpr hxK
  have hord1 : orderOf (ψ ⟨x, hKJ hxK⟩) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨x, hKJ hxK⟩ : ↥Jc) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, map_one]
  have hord2 := orderOf_dvd_natCard (ψ ⟨x, hKJ hxK⟩)
  have hcop : Nat.Coprime p (Nat.card ((↥Jc ⧸ aschbacherSolvableCore p ↥Jc) ⧸
      Subgroup.center (↥Jc ⧸ aschbacherSolvableCore p ↥Jc))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hord : orderOf (ψ ⟨x, hKJ hxK⟩) = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hord1 hord2)
  have hker : (⟨x, hKJ hxK⟩ : ↥Jc) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp hord
  have hmem : (⟨x, hKJ hxK⟩ : ↥Jc) ∈ K.subgroupOf Jc ⊓ ψ.ker := ⟨hx'K, hker⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact hx1 (congrArg Subtype.val hmem)

theorem Jc_le_Jof (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) : Jc ≤ Jof p R := by
  have h := H.h12
  have hp := h.prime
  obtain ⟨hperf, hq⟩ := Jc_perfect_quasi hp hJ
  obtain ⟨-, hKsF, -, -⟩ := class_facts H (Or.inl rfl) (mem_clsOf_self p E s)
  have hLift := KFAt.toLiftAt hKsF
  have hKJ : kZero p E s ≤ Jc := hJ.K_le s (mem_clsOf_self p E s)
  have hne : autMoved E s ≠ ⊥ := by
    intro h0
    have := H.hs.1.2
    rw [h0, Subgroup.card_bot] at this
    exact hp.one_lt.ne this
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxl : (m : G) ∈ autMovedInG E s := ⟨m, hm, rfl⟩
  have hx1 : (m : G) ≠ 1 := fun h1 => hm1 (Subtype.ext (Subtype.ext h1))
  have hxK : (m : G) ∈ kZero p E s := hKsF.2.2.2.1 hxl
  have hxp : (m : G) ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h m.2
  have hdiv := p_dvd_card_simple hp hKJ hLift.1 hLift.2.1 hxK hx1 hxp
  have htop := LocalEmbeddingFrontier.eq_top_of_pElements_le hp hperf hq hdiv
    (Sub := (Jof p R).subgroupOf Jc) (fun y ⟨k, hk⟩ => by
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [Jof_def]
      exact Subgroup.subset_closure ⟨hJ.le_M y.2, k, (Subgroup.orderOf_coe y).trans hk⟩)
  intro x hx
  have : (⟨x, hx⟩ : ↥Jc) ∈ (Jof p R).subgroupOf Jc := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem Vof_Jc_le (hp : p.Prime) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) : Vof p Jc ≤ Vof p (Jof p R) := by
  have hJle := Jc_le_Jof H hJ
  have hnorm := Jof_le_normalizer H hJ
  obtain ⟨hs, hpn⟩ := theta_solvable_and_not_dvd hp Jc
  unfold Vof
  refine le_theta_of_normal hp ((Subgroup.map_subtype_le _).trans hJle) ?_ hs hpn
  intro x hx v hv
  have h1 : conjBy x Jc = Jc := Equivariance.conjBy_eq_of_mem_normalizer (hnorm hx)
  have h2 := inSubgroup_theta_conjBy hp x Jc
  rw [h1] at h2
  have hmem : x * v * x⁻¹ ∈ conjBy x (inSubgroup (aschbacherSolvableCore p) Jc) :=
    Equivariance.mem_conjBy.2 (by
      have e : x⁻¹ * (x * v * x⁻¹) * x = v := by group
      rw [e]
      exact hv)
  rwa [← h2] at hmem

theorem theta_Jc_le_center
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) : aschbacherSolvableCore p ↥Jc ≤ Subgroup.center ↥Jc := by
  have h := H.h12
  have hp := h.prime
  obtain ⟨hperf, hq⟩ := Jc_perfect_quasi hp hJ
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hcJ : c ∈ Jc := hJ.E_le hcE
  have hVJ := Vof_Jc_le hp H hJ
  have hcomm := theta_commute hGA hS hRe hTwo hFull H
  refine theta_le_center_of_commute hp hperf hq (c' := ⟨c, hcJ⟩) ?_ ?_
  · intro v hv
    have hvV : (v : G) ∈ Vof p Jc := ⟨v, hv, rfl⟩
    exact Subtype.ext (hcomm _ (hVJ hvV)).eq
  · by_contra hall
    push Not at hall
    obtain ⟨t₁, ht₁, hct₁⟩ := hJ.moves
    obtain ⟨-, hKt, -, -⟩ := class_facts H (Or.inl rfl) ht₁
    have hLift := KFAt.toLiftAt hKt
    have hKJ : kZero p E t₁ ≤ Jc := hJ.K_le t₁ ht₁
    obtain ⟨k, hkK, hkc⟩ : ∃ k ∈ kZero p E t₁, c * k ≠ k * c := by
      by_contra hno
      push Not at hno
      apply hct₁
      have hmem : c ∈ E ⊓ Subgroup.centralizer (kZero p E t₁ : Set G) :=
        ⟨hcE, Subgroup.mem_centralizer_iff.mpr fun k hk => (hno k hk).symm⟩
      rw [hKt.2.2.1] at hmem
      exact hmem
    have hcN : c ∈ Subgroup.normalizer (kZero p E t₁ : Set G) :=
      mem_normalizer_kZero t₁ fun e he => congrArg Subtype.val
        (h.E_elem.is_comm.comm (⟨c, hcE⟩ : ↥E) ⟨e, he⟩)
    obtain ⟨hsimple, hperfK⟩ := subgroupOf_simple_perfect hKJ hLift.1 hLift.2.1
    have hθs : Group.IsSolvable ↥(aschbacherSolvableCore p ↥Jc) :=
      (solvable_prime_complement_core_characterization hp).1
    have hinf := inf_solvable_normal_eq_bot hperfK inferInstance hsimple
      (inferInstance : (aschbacherSolvableCore p ↥Jc).Normal) hθs
    have hj := hall ⟨k, hKJ hkK⟩
    have hmemK : (⟨c, hcJ⟩ * ⟨k, hKJ hkK⟩ * ⟨c, hcJ⟩⁻¹ * ⟨k, hKJ hkK⟩⁻¹ : ↥Jc) ∈
        (kZero p E t₁).subgroupOf Jc := by
      show c * k * c⁻¹ * k⁻¹ ∈ kZero p E t₁
      have h1 : c * k * c⁻¹ ∈ kZero p E t₁ := (Subgroup.mem_normalizer_iff.mp hcN k).mp hkK
      exact mul_mem h1 (inv_mem hkK)
    have hboth : (⟨c, hcJ⟩ * ⟨k, hKJ hkK⟩ * ⟨c, hcJ⟩⁻¹ * ⟨k, hKJ hkK⟩⁻¹ : ↥Jc) ∈
        (kZero p E t₁).subgroupOf Jc ⊓ aschbacherSolvableCore p ↥Jc := ⟨hmemK, hj⟩
    rw [hinf, Subgroup.mem_bot] at hboth
    apply hkc
    have := congrArg Subtype.val hboth
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc c * k = (c * k * c⁻¹ * k⁻¹) * (k * c) := by group
      _ = k * c := by rw [this, one_mul]

theorem eq_one_of_pow_commute (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {z : G} (hzc : ∀ j ∈ Jc, z * j = j * z) (hzp : z ^ p = 1) :
    z = 1 := by
  have h := H.h12
  by_contra hz1
  have hEJ : E ≤ Jc := hJ.E_le
  have hFel : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers z) :=
    isElementaryAbelian_sup_of_commute h.E_elem (IsElementaryAbelian.zpowers_of_pow_eq_one hzp)
      (fun e he y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_right (show Commute e z from (hzc e (hEJ he)).symm) i)).eq)
  have hFle : E ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (A : Set G) := by
    refine sup_le h.E_le (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hzc a (hEJ (h.A_le_E ha))).symm
  have hFE := h.E_max _ hFel hFle le_sup_left
  have hzE : z ∈ E := by
    rw [← hFE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine hz1 (hJ.fixed_trivial z hzE fun t ht => ?_)
  obtain ⟨-, hKt, -, -⟩ := class_facts H (Or.inl rfl) ht
  have hmem : z ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) :=
    ⟨hzE, Subgroup.mem_centralizer_iff.mpr fun k hk => (hzc k (hJ.K_le t ht hk)).symm⟩
  rw [hKt.2.2.1] at hmem
  exact hmem

theorem center_Jc_pPrime (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) : ¬ p ∣ Nat.card (Subgroup.center ↥Jc) := by
  intro hdvd
  have h := H.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set zG : G := ((z : ↥Jc) : G) with hzG
  have hzc : ∀ j ∈ Jc, zG * j = j * zG := fun j hj =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2 ⟨j, hj⟩).symm)
  have hzo : orderOf zG = p := by rw [hzG, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
  have hzp : zG ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one zG
  have hz1 : zG ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  exact hz1 (eq_one_of_pow_commute H hJ hzc hzp)

theorem Jc_isQuasisimple
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) :
    CFSG.IsQuasisimple ↥Jc ∧ aschbacherSolvableCore p ↥Jc = Subgroup.center ↥Jc := by
  have h := H.h12
  have hp := h.prime
  obtain ⟨hperf, hq⟩ := Jc_perfect_quasi hp hJ
  have hle := theta_Jc_le_center hGA hS hRe hTwo hFull H hJ
  have hpn := center_Jc_pPrime H hJ
  have hge : Subgroup.center ↥Jc ≤ aschbacherSolvableCore p ↥Jc := by
    refine (solvable_prime_complement_core_characterization hp).2.2.2.1 _ inferInstance ?_ hpn
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp b.2 (a : ↥Jc)))
  have heq : aschbacherSolvableCore p ↥Jc = Subgroup.center ↥Jc := le_antisymm hle hge
  refine ⟨?_, heq⟩
  have hq' : CFSG.IsQuasisimple (↥Jc ⧸ Subgroup.center ↥Jc) :=
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq) hq
  have hZ := center_quot_center_eq_bot hperf
  obtain ⟨-, hsimple, -⟩ := N143.simple_of_quasisimple_center_bot hq' hZ
  exact S11d.isQuasisimple_of_perfect_of_simple hperf hsimple

end CFSG.RankThree.PartOne.Q1327
