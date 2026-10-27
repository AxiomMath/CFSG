module

public import CFSG.Timmesfeld.Bridge.OddLocalQd
public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import CFSG.Timmesfeld.Bridge.Asc72Unitary
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement MatrixGroups

namespace OddLocal

section General

variable {K : Type*} [Group K]

theorem mul_self_eq_one_of_mem_closure {S : Set K} (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hS2 : ∀ a ∈ S, a * a = 1) {g : K} (hg : g ∈ Subgroup.closure S) : g * g = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem a ha => exact hS2 a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab := commute_of_mem_closure_pairwise hS ha hb
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab.eq]
          group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

theorem isPGroup_two_of_mul_self {H : Subgroup K} (h : ∀ g ∈ H, g * g = 1) : IsPGroup 2 H := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using h g g.2

theorem eq_one_of_mem_center (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) {z : K}
    (hz : z ∈ Subgroup.center K) (hz2 : z * z = 1) : z = 1 := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center K := Subgroup.zpowers_le.mpr hz
  have hN : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hle
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    refine isPGroup_two_of_mul_self fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
  have h := hO2 _ hN hP
  have hzz : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [h, Subgroup.mem_bot] at hzz
  exact hzz

theorem mem_center_of_commute_gen {S : Set K} (hS : Subgroup.closure S = ⊤) {g : K}
    (h : ∀ s ∈ S, Commute g s) : g ∈ Subgroup.center K := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {g} := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h s hs).eq.symm
  rw [hS] at hle
  exact Subgroup.mem_center_iff.mpr fun k =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top k))

theorem zStar_eq_center (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    zStar K = Subgroup.center K := by
  have hP : CFSG.pCore 2 K = ⊥ := hO2 _ (CFSG.BaerSuzuki.Helpers.pCore_normal 2)
    (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2)
  ext g
  simp only [zStar, Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro h k
    have h1 := h (QuotientGroup.mk' _ k)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hP, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  · intro h k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ k
    rw [← map_mul, ← map_mul, h k]

theorem odd_card_center [Finite K] (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2
    (even_iff_two_dvd.mp h)
  have hzK : orderOf (z : K) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hz2 : (z : K) * z = 1 := by
    rw [← pow_two, ← hzK, pow_orderOf_eq_one]
  have hz1 : (z : K) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzK
    exact absurd hzK (by norm_num)
  exact hz1 (eq_one_of_mem_center hO2 z.2 hz2)

theorem isBenderGroup_of_mulEquiv' {K' : Type*} [Group K'] (e : K ≃* K')
    (h : CFSG.BenderSuzuki.IsBenderGroup K) : CFSG.BenderSuzuki.IsBenderGroup K' := by
  cases h with
  | isPSL2 n hn f => exact .isPSL2 n hn (e.symm.trans f)
  | isSuzuki n hn f => exact .isSuzuki n hn (e.symm.trans f)
  | isPSU3 n hn f => exact .isPSU3 n hn (e.symm.trans f)

theorem center_eq_bot_of_psl2 [Finite K] (hperf : commutator K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center K))) {n : ℕ}
    (e : K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.PSL2Model n) : Subgroup.center K = ⊥ := by
  have : Group.IsPerfect K := ⟨hperf⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : K ⧸ Subgroup.center K ≃* SL(2, GaloisField 2 n) :=
    e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  let π' : K →* SL(2, GaloisField 2 n) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hker : π'.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective, QuotientGroup.ker_mk']
  have hπ' : Function.Surjective π' := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcen' : π'.ker ≤ Subgroup.center K := hker.le
  have hodd' : ¬ 2 ∣ Nat.card π'.ker := by
    rw [hker]
    intro h
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.SectionRank.EvenCover.sl2_existsUnique_section (p := 2) hπ' hcen' hodd'
  have hsup : σ.range ⊔ Subgroup.center K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hz : (σ (π' x))⁻¹ * x ∈ Subgroup.center K := by
      apply hcen'
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have hmem : σ (π' x) ∈ σ.range := ⟨π' x, rfl⟩
    have := Subgroup.mul_mem_sup hmem hz
    rwa [mul_inv_cancel_left] at this
  have hrange : σ.range = ⊤ :=
    (CFSG.SectionRank.perfect_central_supplement inferInstance).1 _ hsup
  rw [eq_bot_iff]
  intro x hx
  rw [← hker] at hx
  have hxr : x ∈ σ.range := by
    rw [hrange]
    exact Subgroup.mem_top x
  obtain ⟨g, rfl⟩ := hxr
  have hg : g = 1 := by
    rw [← hσ g]
    exact hx
  rw [hg, map_one]
  exact Subgroup.one_mem _

theorem center_eq_bot_of_sz [Finite K] (hperf : commutator K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center K))) {n : ℕ}
    (e : K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.SzModel n) : Subgroup.center K = ⊥ := by
  have : Group.IsPerfect K := ⟨hperf⟩
  let f := QuotientGroup.mk' (Subgroup.center K)
  have hker : f.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  by_contra hne
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  rw [← hker] at hrd
  obtain ⟨C⟩ := (inferInstance : Nonempty (Sylow r f.ker))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r (K ⧸ Subgroup.center K)))
  have hcyc := CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv
    (e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n))) r hr2 Q
  exact Sylow.ne_bot_of_dvd_card C hrd
    (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f
      (QuotientGroup.mk'_surjective _) hker.le C Q hcyc)

noncomputable def mulEquivOfCenterEqBot (hc : Subgroup.center K = ⊥) :
    K ≃* K ⧸ Subgroup.center K :=
  (QuotientGroup.quotientBot (G := K)).symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)

end General

section Core

variable {K : Type} [Group K] {D : Set K}

theorem mul_self_eq_one_of_mem_closure_rootSet (hD : IsOddTransp D) {d : K} (hd : d ∈ D) {g : K}
    (hg : g ∈ Subgroup.closure (rootSet D d)) : g * g = 1 :=
  mul_self_eq_one_of_mem_closure (fun _ ha _ hb => commute_of_mem_rootSet hd ha hb)
    (fun _ ha => hD.mul_self_eq_one ha.1) hg

theorem false_of_psu3 [Finite K] (hD : IsOddTransp D) {d x : K} (hd : d ∈ D) (hdx : ¬ Commute d x)
    (hx : x ∈ D) (hgen : rootGen D d x = ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.PSU3Model n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk := QuotientGroup.mk' (Subgroup.center K)
  have hB : CFSG.BenderSuzuki.IsBenderGroup (K ⧸ Subgroup.center K) := .isPSU3 n hn e
  have hAp : IsPGroup 2 ((Subgroup.closure (rootSet D d)).map mk) :=
    (isPGroup_two_of_mul_self fun g hg => mul_self_eq_one_of_mem_closure_rootSet hD hd hg).map mk
  obtain ⟨Q, hQ⟩ := hAp.exists_le_sylow
  have hEZ : ∀ a ∈ rootSet D d,
      mk a ∈ ((Subgroup.center (Q : Subgroup (K ⧸ Subgroup.center K))).map
        (Q : Subgroup (K ⧸ Subgroup.center K)).subtype) := by
    intro a ha
    have haQ : mk a ∈ Q := hQ ⟨a, Subgroup.subset_closure ha, rfl⟩
    have ha2 : mk a * mk a = 1 := by rw [← map_mul, hD.mul_self_eq_one ha.1, map_one]
    have hc := Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB Q haQ ha2
    refine ⟨⟨mk a, haQ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).eq.symm
  have hxt : orderOf (mk x) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hD.mul_self_eq_one hx, map_one]) ?_
    intro h1
    have hxc : x ∈ Subgroup.center K := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center K)]
      exact h1
    exact hdx (Subgroup.mem_center_iff.mp hxc d)
  apply Asc72.closure_insert_center_ne_top_of_psu3 hn e Q hxt
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) g
  have hk : k ∈ rootGen D d x := hgen ▸ Subgroup.mem_top k
  have hle : rootGen D d x ≤ (Subgroup.closure (insert (mk x)
      ((Subgroup.center (Q : Subgroup (K ⧸ Subgroup.center K))).map
        (Q : Subgroup (K ⧸ Subgroup.center K)).subtype : Set (K ⧸ Subgroup.center K)))).comap
      mk := by
    rw [rootGen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hEZ y hy))
  exact hle hk

theorem mem_center_of_commute_rootGen {d x : K} (hgen : rootGen D d x = ⊤) {f : K} (hf : f ∈ D)
    (hfd : Commute f d) (hfx : Commute f x) : f ∈ Subgroup.center K := by
  refine mem_center_of_commute_gen hgen ?_
  rintro s (rfl | hs)
  · exact hfx
  · exact ((hs.2 f hf).mpr hfd.symm).symm

theorem not_thirdKind (hS : Setup K D) (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥)
    {d x : K} (hd : d ∈ D) (hgen : rootGen D d x = ⊤) {a b : K} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (htri : IsTriangle D a x b) : ¬ IsThirdKind a x b := by
  rintro ⟨n, hn, -, hord⟩
  obtain ⟨hzz, hz1, hza, hzb, hzx, hw⟩ := htri.third_kind hS.oddT hS.normal hn hord
  set z := (a * b * x) ^ n with hz
  have hab : Commute a b := htri.2.2.2.2.1
  have hwa : Commute (a * b * z) a := ((Commute.refl a).mul_left hab.symm).mul_left hza
  have hwe : ∀ e ∈ rootSet D d, Commute e (a * b * z) := fun e he =>
    (he.2 _ hw).mpr ((ha.2 _ hw).mp hwa.symm)
  have hab2 : a * b * (a * b) = 1 := htri.uv_mul_self hS.oddT
  have hzeq : z = a * b * (a * b * z) := by
    rw [← mul_assoc, hab2, one_mul]
  have hzc : z ∈ Subgroup.center K := by
    refine mem_center_of_commute_gen hgen ?_
    rintro s (rfl | hs)
    · exact hzx
    · rw [hzeq]
      have h1 : Commute (a * b) s :=
        (commute_of_mem_rootSet hd ha hs).mul_left (commute_of_mem_rootSet hd hb hs)
      exact h1.mul_left (hwe s hs).symm
  exact hz1 (eq_one_of_mem_center hO2 hzc hzz)

theorem mul_mem_of_mem_rootSet [Finite K] (hS : Setup K D)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) {d x : K} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) (hgen : rootGen D d x = ⊤) {a b : K}
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) : a * b ∈ D := by
  have hD := hS.oddT
  have hno : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, IsTriangle D a x b → ¬ IsThirdKind a x b :=
    fun a ha b hb htri => not_thirdKind hS hO2 hd hgen ha hb htri
  obtain ⟨⟨-, hZc⟩, -, -, hcomm, hnorm, -, -⟩ := qd_lemma hD hS.normal hd hx hdx hno
  set Q := qd D d
  set Qx := Q.map (MulAut.conj x).toMonoidHom
  have hQ2 : ∀ g ∈ Q, g * g = 1 := fun g hg =>
    mul_self_eq_one_of_mem_closure_rootSet hD hd (qd_le_closure hg)
  have hpairx : ∀ u ∈ (fun e => x * e * x⁻¹) '' rootSet D d,
      ∀ v ∈ (fun e => x * e * x⁻¹) '' rootSet D d, Commute u v := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (commute_of_mem_rootSet hd hu hv).conj x
  have hQx2 : ∀ g ∈ Qx, g * g = 1 := by
    intro g hg
    refine mul_self_eq_one_of_mem_closure hpairx ?_ (qdx_le_closure_conj d x hg)
    rintro _ ⟨u, hu, rfl⟩
    rw [show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group,
      hD.mul_self_eq_one hu.1, mul_one, mul_inv_cancel]
  have hZbot : Q ⊓ Qx = ⊥ := by
    have hle : Q ⊓ Qx ≤ Subgroup.center K := fun z hz =>
      Subgroup.mem_center_iff.mpr fun g => (hZc z hz g (hgen ▸ Subgroup.mem_top g)).eq.symm
    exact hO2 _ (Subgroup.normal_of_le_center hle)
      (isPGroup_two_of_mul_self fun g hg => hQ2 g hg.1)
  have hQQx : ∀ q ∈ Q, ∀ q' ∈ Qx, Commute q q' := by
    intro q hq q' hq'
    have h1 := hcomm (Subgroup.commutator_mem_commutator hq hq')
    rw [hZbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h1
    exact h1
  have hsup2 : ∀ g ∈ Q ⊔ Qx, g * g = 1 := by
    intro g hg
    rw [← Subgroup.closure_eq Q, ← Subgroup.closure_eq Qx, ← Subgroup.closure_union] at hg
    refine mul_self_eq_one_of_mem_closure ?_ ?_ hg
    · rintro u (hu | hu) v (hv | hv)
      · exact commute_of_mem_closure_rootSet hd (qd_le_closure hu) (qd_le_closure hv)
      · exact hQQx u hu v hv
      · exact (hQQx v hv u hu).symm
      · exact commute_of_mem_closure_pairwise hpairx (qdx_le_closure_conj d x hu)
          (qdx_le_closure_conj d x hv)
    · rintro u (hu | hu)
      · exact hQ2 u hu
      · exact hQx2 u hu
  have hsupN : (Q ⊔ Qx).Normal :=
    ⟨fun n hn g => hnorm g (hgen ▸ Subgroup.mem_top g) n hn⟩
  have hsupbot := hO2 _ hsupN (isPGroup_two_of_mul_self hsup2)
  have hQbot : Q = ⊥ := le_bot_iff.mp (le_sup_left.trans hsupbot.le)
  by_contra habD
  have hmem : a * b ∈ Q := Subgroup.subset_closure ⟨a, ha, b, hb, habD, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at hmem
  have hbi : b⁻¹ = b := hD.inv_eq hb.1
  exact hab (by rw [← hbi]; exact eq_inv_of_mul_eq_one_left hmem)

theorem commutator_eq_top_of_mul_mem (hS : Setup K D) {u v : K} (hu : u ∈ D) (hv : v ∈ D)
    (huv : u * v ∈ D) : commutator K = ⊤ := by
  have h1 : Abelianization.of u = 1 := by
    have e1 := hS.abelianization_eq huv hu
    have e2 := hS.abelianization_eq hv hu
    rw [map_mul, e2] at e1
    have := congrArg (fun t => t * (Abelianization.of u)⁻¹) e1
    simpa using this
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  intro y hy
  rw [SetLike.mem_coe, ← Abelianization.ker_of, MonoidHom.mem_ker, hS.abelianization_eq hy hu, h1]

end Core

end OddLocal

open OddLocal in
theorem rootGen_core (h16 : OddTranspZStar) (h18 : CommonNeighbourStmt) {K : Type} [Group K]
    [Finite K] {D : Set K} (hS : Setup K D)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) {d x : K} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) (hgen : rootGen D d x = ⊤) :
    (∃ n, 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n)) ∨
      (∃ n, 1 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.SzModel n)) ∨ rootSet D d = {d} := by
  have hD := hS.oddT
  by_cases hE1 : rootSet D d = {d}
  · exact Or.inr (Or.inr hE1)
  obtain ⟨e, he, hed⟩ : ∃ e ∈ rootSet D d, e ≠ d := by
    by_contra h
    push Not at h
    apply hE1
    ext y
    constructor
    · exact fun hy => h y hy
    · rintro rfl
      exact mem_rootSet_self hd
  have hde : d * e ∈ D :=
    mul_mem_of_mem_rootSet hS hO2 hd hx hdx hgen (mem_rootSet_self hd) he hed.symm
  have hD2 : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D :=
    ⟨d, hd, e, he.1, hed.symm, commute_of_mem_rootSet hd (mem_rootSet_self hd) he, hde⟩
  have hperf : commutator K = ⊤ := commutator_eq_top_of_mul_mem hS hd he.1 hde
  by_cases hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b
  ·
    exfalso
    obtain ⟨f, hf, hfd, hfx⟩ := h18 K D hS hconn hD2 d hd x hx hdx
    exact hD.ne_one hf (eq_one_of_mem_center hO2 (mem_center_of_commute_rootGen hgen hf hfd hfx)
      (hD.mul_self_eq_one hf))
  ·
    have hdisc : Disconnected D := by
      push Not at hconn
      obtain ⟨a, ha, b, hb, h⟩ := hconn
      exact ⟨a, ha, b, hb, h⟩
    have hB := isBenderGroup_of_mulEquiv'
      (QuotientGroup.quotientMulEquivOfEq (zStar_eq_center hO2))
      (h16 K D hD hS.normal hS.gen hD2 hdisc)
    have hodd := odd_card_center hO2
    rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
    · exact Or.inl ⟨n, hn, ⟨(mulEquivOfCenterEqBot (center_eq_bot_of_psl2 hperf hodd e)).trans e⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn,
        ⟨(mulEquivOfCenterEqBot (center_eq_bot_of_sz hperf hodd e)).trans e⟩⟩)
    · exact (false_of_psu3 hD hd hdx hx hgen hn e).elim

end CFSG.Timmesfeld.Bridge
