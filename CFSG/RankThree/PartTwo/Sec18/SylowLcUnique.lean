module

public import CFSG.RankThree.PartTwo.Sec18.SylowLcExists
import CFSG.GroupTheory.QuasiDihedralFusion.Basic
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
import CFSG.RankThree.PartTwo.Sec18.SylowFusion

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace SylowLc

section Generic

variable {X : Type} [Group X] [Finite X]

theorem commutator_mem_of_mem_thetaComponents {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ thetaComponents 3 X) (h₂ : K₂ ∈ thetaComponents 3 X) (hne : K₁ ≠ K₂)
    {x y : X} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    x * y * x⁻¹ * y⁻¹ ∈ aschbacherSolvableCore 3 X := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hπ
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := X) Nat.prime_three
  have hKne : K₁.map π ≠ K₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three h₁)
    (isComponent_map_of_mem_thetaComponents Nat.prime_three h₂)).resolve_left hKne
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx)
    (Subgroup.mem_map_of_mem π hy)
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, commutatorElement_def, hπ,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact h

theorem le_normalizer_of_mem_thetaComponents {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ thetaComponents 3 X) (h₂ : K₂ ∈ thetaComponents 3 X) (hne : K₁ ≠ K₂) :
    K₂ ≤ Subgroup.normalizer (K₁ : Set X) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hπ
  intro y hy
  have hyc : π y ∈ Subgroup.centralizer
      ((K₁.map π : Subgroup (X ⧸ aschbacherSolvableCore 3 X)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact commutator_mem_of_mem_thetaComponents h₁ h₂ hne hx hy
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hyN : y ∈ Subgroup.normalizer (((K₁.map π).comap π : Subgroup X) : Set X) :=
    Subgroup.le_normalizer_comap π (Subgroup.centralizer_le_normalizer _ hyc)
  have h := CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
    _ hyN
  rwa [hπ, perfectResidual_comap_map_of_mem_thetaComponents Nat.prime_three h₁] at h

theorem exists_isSylowOf_le_normalizer {p : ℕ} [Fact p.Prime] {K B : Subgroup X}
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hB : IsPGroup p B) :
    ∃ Q, CFSG.ABGLocalTools.IsSylowOf p Q K ∧ B ≤ Subgroup.normalizer (Q : Set X) := by
  set Y := K ⊔ B with hY
  have hKY : K ≤ Y := le_sup_left
  have hBY : B ≤ Y := le_sup_right
  have hYK : Y ≤ Subgroup.normalizer (K : Set X) := sup_le Subgroup.le_normalizer hBK
  haveI : (K.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  obtain ⟨S, hBS⟩ := (hB.comap_subtype (K := Y)).exists_le_sylow
  set S' := (S : Subgroup Y).map Y.subtype with hS'
  have hBS' : B ≤ S' := fun b hb => ⟨⟨b, hBY hb⟩, hBS (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  refine ⟨S' ⊓ K, ?_, fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (hBS' hb), hBK hb⟩⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨inf_le_right, (S.isPGroup'.map Y.subtype).to_le inf_le_left, ?_⟩
  have hSS : S'.subgroupOf Y = S := Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_subgroupOf hKY, hSS]
  exact fun hdvd => S.not_dvd_index
    (hdvd.trans (CFSG.QuasiDihedralFusion.relIndex_dvd_index_of_normal_right _ _))

theorem le_pCoreOf_of_isSolvable {K N : Subgroup X} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set X)) (hsol : Group.IsSolvable N)
    (hKp : ⁅K, K⁆ = K) [IsSimpleGroup (K ⧸ CFSG.pCore 2 K)] :
    N ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  haveI : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI : Group.IsSolvable (N.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNK).injective
  rcases ((inferInstance : (N.subgroupOf K).Normal).map π
      (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with hbot | htop
  · intro n hn
    have h1 : π ⟨n, hNK hn⟩ ∈ (N.subgroupOf K).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hn)
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf] at h1
    exact h1
  · exfalso
    haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKp
    haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) :=
      Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective _)
    have hsurj : Function.Surjective (π.comp (N.subgroupOf K).subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, htop]
    haveI : Group.IsSolvable (K ⧸ CFSG.pCore 2 K) := Group.isSolvable_of_surjective hsurj
    exact Group.IsPerfect.not_isSolvable (K ⧸ CFSG.pCore 2 K) inferInstance

theorem false_of_isSylowOf {K Q Z : Subgroup X} (hKp : Group.IsPerfect K)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (h3 : 3 ∣ Nat.card K)
    (hZ : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    (hQZ : ∀ x ∈ Q, x ^ 3 = 1 → x ∈ Z) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, rfl⟩ := hQ
  haveI : Fact (IsPGroup 3 (P : Subgroup K)) := ⟨P.isPGroup'⟩
  have hmem : ∀ x : (P : Subgroup K), ((x : K) : X) ∈ (P : Subgroup K).map K.subtype :=
    fun x => ⟨x, x.2, rfl⟩
  have hcyc : IsCyclic (P : Subgroup K) := by
    by_contra hnc
    obtain ⟨S, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    haveI := hel
    let f : (P : Subgroup K) →* X := K.subtype.comp (P : Subgroup K).subtype
    have hf : Function.Injective f := K.subtype_injective.comp (Subgroup.subtype_injective _)
    have hle : S.map f ≤ Z := by
      rintro _ ⟨s, hs, rfl⟩
      refine hQZ _ (hmem s) ?_
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian s hs, map_one]
    have hc := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hf, hcard, hZ3] at hc
    norm_num at hc
  haveI := hcyc
  haveI := hKp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (P.dvd_card_of_dvd_card h3)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hxZ : ((x : K) : X) ∈ Z := by
    refine hQZ _ (hmem x) ?_
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hx3, Subgroup.coe_one, Subgroup.coe_one]
  have hxc : (x : K) ∈ (P : Subgroup K) ⊓ Subgroup.center K := by
    refine ⟨x.2, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_⟩
    exact Subgroup.mem_center_iff.mp (hZ hxZ) g
  rw [CFSG.Quasithin.SBd19F.sylow_inf_center_eq_bot P, Subgroup.mem_bot] at hxc
  have hx1 : x = 1 := Subtype.ext hxc
  rw [hx1, orderOf_one] at hx
  norm_num at hx

end Generic

variable {G : Type} [Group G] [Finite G]

variable {A M H : Subgroup G} {c : G}

theorem commutator_mem_of_mem_thetaComponentsAt {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 c) (h₂ : K₂ ∈ thetaComponentsAt 3 c) (hne : K₁ ≠ K₂)
    {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    x * y * x⁻¹ * y⁻¹ ∈ (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).map
      (Subgroup.centralizer ({c} : Set G)).subtype := by
  obtain ⟨K₁', hK₁', rfl⟩ := h₁
  obtain ⟨K₂', hK₂', rfl⟩ := h₂
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨_, commutator_mem_of_mem_thetaComponents hK₁' hK₂' (fun h => hne (by rw [h])) hx' hy',
    rfl⟩

theorem le_normalizer_lc (hH : Sec18H G A M H c) :
    A ≤ Subgroup.normalizer (lc H c : Set G) := by
  have h := hH.toSec18Std
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAH := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH.mem_scriptH).1
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  set L := inSubgroup perfectResidual H with hL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set R := CFSG.Open.pCoreOf 2 C with hR
  intro a ha
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  apply CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
  apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
  intro z hz
  have hle : L ⊓ C ⊔ R ≤ (L ⊓ C ⊔ R).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · show a * y * a⁻¹ ∈ L ⊓ C ⊔ R
      exact Subgroup.mem_sup_left ⟨(Subgroup.mem_normalizer_iff.mp
        (le_normalizer_inSubgroup_perfectResidual H (hAH ha)) y).mp hy.1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haC) y).mp hy.2⟩
    · show a * y * a⁻¹ ∈ L ⊓ C ⊔ R
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C haC) y).mp hy)
  exact hle hz


theorem lc_mem_thetaComponentsAt (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C)
    (hH : Sec18H G A M H c) : lc H c ∈ thetaComponentsAt 3 c := by
  rw [thetaComponentsAt_eq_thetaComponentsIn]
  exact Claim184LcProof.mem_thetaComponentsIn_of_mem_oTwoComponentsIn
    (lc_mem_oTwoComponentsIn h1812 h184 h182 hH).1

theorem three_dvd_card_lc (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c) :
    3 ∣ Nat.card (lc H c) := by
  have hd := Subgroup.card_dvd_of_le (SylowFusion.isSylowOf_lc h1812 h184 hH).le
  rw [card_inf_of_sec18H h1812 h184 hH] at hd
  exact dvd_trans (by norm_num) hd

theorem mem_zpowers_of_mem_inf (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C)
    (hH : Sec18H G A M H c) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hne : K ≠ lc H c) {x : G} (hxA : x ∈ A) (hxK : x ∈ K) : x ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hH.toSec18Std
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hBlc : A ⊓ inSubgroup perfectResidual H ≤ lc H c :=
    (SylowFusion.isSylowOf_lc h1812 h184 hH).le
  have hLcθ := lc_mem_thetaComponentsAt h1812 h184 h182 hH
  have hBz : A ⊓ inSubgroup perfectResidual H ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro b hb
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbc : Commute b c := Subgroup.mem_centralizer_singleton_iff.mp (hAC hb.1)
    rw [(hbc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  have hxA' := hxA
  rw [eq_zpowers_sup_of_sec18H h1812 h184 hH, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBz] at hxA'
  obtain ⟨b, hb, z, hz, rfl⟩ := Set.mem_mul.mp hxA'
  set Lc := lc H c with hLcdef
  have hbLc : b ∈ Lc := hBlc hb
  obtain ⟨e⟩ := SylowFusion.nonempty_quotient_lc h184 hH
  haveI := Item18ResProof.isSimpleGroup_projSL_three_four
  haveI : Nontrivial (Lc ⧸ CFSG.pCore 2 Lc) := e.toEquiv.nontrivial
  haveI : IsSimpleGroup (Lc ⧸ CFSG.pCore 2 Lc) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  set θ := (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).map
    (Subgroup.centralizer ({c} : Set G)).subtype with hθ
  have hθO : θ ⊓ Lc ≤ CFSG.Open.pCoreOf 2 Lc := by
    have hΘ := solvable_prime_complement_core_characterization
      (H := Subgroup.centralizer ({c} : Set G)) Nat.prime_three
    haveI : (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).Characteristic :=
      hΘ.2.1
    haveI : Group.IsSolvable (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))) :=
      hΘ.1
    haveI : Group.IsSolvable θ := Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective
      _ _ (Subgroup.centralizer ({c} : Set G)).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    refine le_pCoreOf_of_isSolvable inf_le_right ?_
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left))
      (commutator_inSubgroup_perfectResidual _)
    intro y hy
    have hyC : y ∈ Subgroup.centralizer ({c} : Set G) := SylowFusion.lc_le_centralizer H c hy
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hy⟩
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨y, hyC⟩ * t * ⟨y, hyC⟩⁻¹,
      (inferInstance : (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).Normal).conj_mem
        t ht ⟨y, hyC⟩, rfl⟩
  have hcomm : ∀ y ∈ Lc, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Lc := by
    intro y hy
    have hzy : z * y = y * z := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hyc : Commute y c :=
        Subgroup.mem_centralizer_singleton_iff.mp (SylowFusion.lc_le_centralizer H c hy)
      exact (hyc.zpow_right k).eq.symm
    have heq : b * z * y * (b * z)⁻¹ * y⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      calc b * z * y * (b * z)⁻¹ * y⁻¹ = b * (z * y) * z⁻¹ * b⁻¹ * y⁻¹ := by group
        _ = b * (y * z) * z⁻¹ * b⁻¹ * y⁻¹ := by rw [hzy]
        _ = b * y * b⁻¹ * y⁻¹ := by group
    rw [← heq]
    refine hθO ⟨commutator_mem_of_mem_thetaComponentsAt hK hLcθ hne hxK hy, ?_⟩
    exact Lc.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_lc hH hxA) y).mp hy)
      (Lc.inv_mem hy)
  have hbZ : (QuotientGroup.mk' (CFSG.pCore 2 Lc) ⟨b, hbLc⟩) ∈
      Subgroup.center (Lc ⧸ CFSG.pCore 2 Lc) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Lc) g
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 Lc) (⟨b, hbLc⟩ * y * ⟨b, hbLc⟩⁻¹ * y⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hcomm y y.2
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [SylowFusion.center_quotient_lc_eq_bot h184 hH, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hbZ
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lc ⟨b, hbZ⟩
  have hb3 : b ^ 3 = 1 := hA.1.2 b hb.1
  have hb2 : b ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hord : orderOf b = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hb3
    have h2 := orderOf_dvd_of_pow_eq_one hb2
    have hco : Nat.Coprime (orderOf b) 3 :=
      Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k (by norm_num))
    exact Nat.Coprime.eq_one_of_dvd hco h1
  rw [orderOf_eq_one_iff] at hord
  rw [hord, one_mul]
  exact hz

theorem eq_lc_of_mem_thetaComponentsAt (h1812 : Item181_2) (h184 : Item184_1)
    (h182 : Item182Alt1C) (hH : Sec18H G A M H c) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 c) (h3 : 3 ∣ Nat.card K) : K = lc H c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  by_contra hne
  have h := hH.toSec18Std
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hc3 := orderOf_eq_three_of_sec18H h184 hH
  have hAC : A ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hcC : c ∈ C := hAC hcA
  have hBlc : A ⊓ inSubgroup perfectResidual H ≤ lc H c :=
    (SylowFusion.isSylowOf_lc h1812 h184 hH).le
  have hKA : ∀ x ∈ A, x ∈ K → x ∈ Subgroup.zpowers c := fun x hx hxK =>
    mem_zpowers_of_mem_inf h1812 h184 h182 hH hK hne hx hxK
  obtain ⟨Lc', hLc', hLceq⟩ := lc_mem_thetaComponentsAt h1812 h184 h182 hH
  obtain ⟨K', hK', rfl⟩ := hK
  have hne' : K' ≠ Lc' := by
    rintro rfl
    exact hne hLceq
  set B' := (A ⊓ inSubgroup perfectResidual H).subgroupOf C with hB'
  have hB'Lc : B' ≤ Lc' := by
    intro b hb
    have hb' : (b : G) ∈ lc H c := hBlc (Subgroup.mem_subgroupOf.mp hb)
    rw [← hLceq] at hb'
    obtain ⟨b', hb'', hbb⟩ := hb'
    rwa [Subtype.ext hbb] at hb''
  have hB'K : B' ≤ Subgroup.normalizer (K' : Set C) :=
    hB'Lc.trans (le_normalizer_of_mem_thetaComponents hK' hLc' hne')
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2)⟩
  have hB'3 : IsPGroup 3 B' := (hA3.to_le inf_le_left).comap_subtype
  obtain ⟨Q, hQ, hBQ⟩ := exists_isSylowOf_le_normalizer hB'K hB'3
  have hΘ := solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  have hQΘ : Q ⊓ aschbacherSolvableCore 3 C = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ.isPGroup
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ.2.2.1)
  have hcomm : ∀ b ∈ B', ∀ x ∈ Q, b * x = x * b := by
    intro b hb x hx
    have hxK : x ∈ K' := hQ.le hx
    have h1 : b * x * b⁻¹ * x⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hx) (Q.inv_mem hx)
    have h2 : b * x * b⁻¹ * x⁻¹ ∈ aschbacherSolvableCore 3 C := by
      have h' := (aschbacherSolvableCore 3 C).inv_mem
        (commutator_mem_of_mem_thetaComponents hK' hLc' hne' hxK (hB'Lc hb))
      rwa [show (x * b * x⁻¹ * b⁻¹)⁻¹ = b * x * b⁻¹ * x⁻¹ by group] at h'
    have h4 : b * x * b⁻¹ * x⁻¹ ∈ Q ⊓ aschbacherSolvableCore 3 C := ⟨h1, h2⟩
    rw [hQΘ, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  refine false_of_isSylowOf (Z := (Subgroup.zpowers c).subgroupOf C) hK'.1 hQ ?_ ?_ ?_ ?_
  · rwa [Subgroup.card_map_of_injective C.subtype_injective] at h3
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
    apply Subtype.ext
    have hgc : Commute (g : G) c := Subgroup.mem_centralizer_singleton_iff.mp g.2
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (hgc.zpow_right k).eq
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcC)).toEquiv,
      Nat.card_zpowers, hc3]
  · intro x hx hx3
    rw [Subgroup.mem_subgroupOf]
    have hxK : x ∈ K' := hQ.le hx
    have hle : A ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [eq_zpowers_sup_of_sec18H h1812 h184 hH]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hcomm ⟨b, hAC hb.1⟩ (Subgroup.mem_subgroupOf.mpr hb) x hx)
    have hxA : (x : G) ∈ A := by
      refine Item183NMProof.mem_of_commute_of_sec18Std h ?_ fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
      rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
    exact hKA _ hxA ⟨x, hxK, rfl⟩

end SylowLc

theorem item184_2_of
    (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C) : Item184_2 := by
  intro G _ _ A M H c hH
  exact ⟨SylowLc.lc_mem_thetaComponentsAt h1812 h184 h182 hH,
    SylowLc.three_dvd_card_lc h1812 h184 hH,
    fun K hK h3 => SylowLc.eq_lc_of_mem_thetaComponentsAt h1812 h184 h182 hH hK h3⟩

end CFSG.RankThree.PartTwo.Sec18
