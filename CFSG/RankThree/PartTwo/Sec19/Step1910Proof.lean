module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.RankThree.PartTwo.Sec19.Step1910KFact
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

namespace Step1910Proof

section Components

variable {G : Type} [Group G] [Finite G]

theorem isComponent_map_of_mem_oTwoComponents {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : L ∈ oTwoComponents Y) :
    IsComponent (L.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hsn, hq⟩ := hL
  set π := QuotientGroup.mk' (CFSG.pCore 2 Y) with hπ
  set f : L →* Y ⧸ CFSG.pCore 2 Y := π.comp L.subtype with hf
  have hker : f.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · have h2 : IsPGroup 2 f.ker := by
        intro x
        have hx : ((x : L) : Y) ∈ CFSG.pCore 2 Y := by
          have : π ((x : L) : Y) = 1 := MonoidHom.mem_ker.mp x.2
          rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨_, hx⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      exact le_sSup ⟨inferInstance, h2⟩
    · intro x hx
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hsn
      refine h1 ⟨x, ?_, rfl⟩
      exact hx
  have hrange : f.range = L.map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    (((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)) hq,
    hsn.map (QuotientGroup.mk'_surjective _)⟩

theorem commutator_mem_pCoreOf {X J K : Subgroup G} (hJ : J ∈ oTwoComponentsIn X)
    (hK : K ∈ oTwoComponentsIn X) (hne : J ≠ K) {j k : G} (hj : j ∈ J) (hk : k ∈ K) :
    j * k * j⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨hJX, hJ'⟩ := mem_oTwoComponentsIn_iff.mp hJ
  obtain ⟨hKX, hK'⟩ := mem_oTwoComponentsIn_iff.mp hK
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hQ : (CFSG.pCore 2 X).map X.subtype = CFSG.Open.pCoreOf 2 X := by
    rfl
  rcases LocalCores.distinct_components_commute (isComponent_map_of_mem_oTwoComponents hJ')
    (isComponent_map_of_mem_oTwoComponents hK') with heq | hcomm
  · exfalso
    apply hne
    refine Sec18.eq_of_sup_pCoreOf_eq hJ hK ?_
    have h1 := congrArg (Subgroup.comap π) heq
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h1
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJX,
      Subgroup.map_subgroupOf_eq_of_le hKX, hQ] at h2
  · have h1 : ⁅π ⟨j, hJX hj⟩, π ⟨k, hKX hk⟩⁆ ∈
        ⁅(J.subgroupOf X).map π, (K.subgroupOf X).map π⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr hj)) (Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr hk))
    rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    rw [← hQ]
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def]

end Components

section List194

open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open Matrix

theorem three_dvd_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

theorem three_dvd_card_of_isList194
    {X : Type} [Group X]
    (hX : IsList194 X) : 3 ∣ Nat.card X := by
  rcases hX with ⟨n, hn, h | h | h | hG2⟩ | h | h | h | h | h | h | h | h | ⟨b, c, hbc, h⟩ | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_SL3 hn]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _) _
  · obtain ⟨e⟩ := h
    exact KFacts.three_dvd_card_of_mulEquiv_projSL e
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSp_two hn]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _) _
  · rw [Step1911Proof.card_isoGTwoEven hG2, Timmesfeld.Orders.ordG2_eq]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (three_dvd_sq_sub_one n) _) _
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSU_four le_rfl]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSU_four (by norm_num)]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) (by norm_num)]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSp 3 le_rfl]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projOmegaMinus hbc]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

@[expose] def slCyc (F : Type) [Field F] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [det_fin_three]⟩

theorem slCyc_pow_three (F : Type) [Field F] : slCyc F ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem slCyc_not_mem_center (F : Type) [Field F] :
    slCyc F ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h10 := congrFun (congrFun hr 1) 0
  simp [slCyc] at h10

theorem exists_noncentral_of_isList194
    {X : Type} [Group X] [Finite X] (hX : IsList194 X) (hperf : Group.IsPerfect X) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hz : ∃ z ∈ Subgroup.center X, z ≠ 1
  · obtain ⟨z, hzc, hz1⟩ := hz
    obtain ⟨n, -, ⟨e⟩⟩ := Step1911EndProof.exists_mulEquiv_SL_of_isList194 hX hperf hzc hz1
    refine ⟨e.symm (slCyc _), by rw [← map_pow, slCyc_pow_three, map_one], fun h => ?_⟩
    apply slCyc_not_mem_center (GaloisField 2 n)
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h (e.symm g)
  · push Not at hz
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_of_isList194 hX)
    refine ⟨x, by rw [← hx]; exact pow_orderOf_eq_one x, fun h => ?_⟩
    rw [hz x h, orderOf_one] at hx
    norm_num at hx

theorem three_dvd_card_of_isSmall194 {X : Type} [Group X] (hX : IsSmall194 X) :
    3 ∣ Nat.card X := by
  rcases Step1911Proof.card_of_isSmall194 hX with h | h <;> rw [h] <;> norm_num

theorem exists_noncentral_of_isList194_wide
    {X : Type} [Group X] [Finite X] (hX : IsList194 X ∨ IsSmall194 X)
    (hperf : Group.IsPerfect X) : ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X := by
  rcases hX with hX | hX
  · exact exists_noncentral_of_isList194 hX hperf
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_of_isSmall194 hX)
    refine ⟨x, by rw [← hx]; exact pow_orderOf_eq_one x, fun h => ?_⟩
    rw [Step1911EndProof.center_eq_bot_of_isSmall194 hX hperf, Subgroup.mem_bot] at h
    rw [h, orderOf_one] at hx
    norm_num at hx

end List194

section Rank

variable {G : Type} [Group G] [Finite G]

theorem mk_mul_comm_of_ne {M J K : Subgroup G} (hJ : J ∈ oTwoComponentsIn M)
    (hK : K ∈ oTwoComponentsIn M) (hne : J ≠ K) {g h : M} (hg : (g : G) ∈ J)
    (hh : (h : G) ∈ K) :
    QuotientGroup.mk' (CFSG.pCore 2 M) g * QuotientGroup.mk' (CFSG.pCore 2 M) h =
      QuotientGroup.mk' (CFSG.pCore 2 M) h * QuotientGroup.mk' (CFSG.pCore 2 M) g := by
  have h1 := commutator_mem_pCoreOf hJ hK hne hg hh
  have h2 : g * h * g⁻¹ * h⁻¹ ∈ CFSG.pCore 2 M := by
    rw [Step1911EndProof.mem_pCore_iff]
    exact h1
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 M) (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  exact Step1910O2Proof.mul_comm_of_commutator_eq_one h3

theorem four_le_localRank {M K J J₂ F : Subgroup G} (hQ : CFSG.Open.pCoreOf 2 M ≠ ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hJ : J ∈ oTwoComponentsIn M)
    (hJ₂ : J₂ ∈ oTwoComponentsIn M) (hJK : J ≠ K) (hJ₂K : J₂ ≠ K) (hJJ₂ : J ≠ J₂)
    (hFK : F ≤ K) (hFe : ∀ f ∈ F, f ^ 3 = 1) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f)
    (hF9 : 9 ≤ Nat.card F) {x x₂ : G} (hx : x ∈ J) (hx₂ : x₂ ∈ J₂)
    (hx3 : x ^ 3 ∈ CFSG.Open.pCoreOf 2 M) (hx₂3 : x₂ ^ 3 ∈ CFSG.Open.pCoreOf 2 M)
    (hxnc : ∃ j ∈ J, x * j * x⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hx₂nc : ∃ j ∈ J₂, x₂ * j * x₂⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM := le_of_mem_oTwoComponentsIn hK
  have hJM := le_of_mem_oTwoComponentsIn hJ
  have hJ₂M := le_of_mem_oTwoComponentsIn hJ₂
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set N := CFSG.pCore 2 M with hN
  set π := QuotientGroup.mk' N with hπ
  have hmemN : ∀ m : M, m ∈ N ↔ (m : G) ∈ Q := fun m => Step1911EndProof.mem_pCore_iff m
  have hπ1 : ∀ m : M, π m = 1 ↔ (m : G) ∈ Q := fun m => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemN]
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  set xs := π ⟨x, hJM hx⟩ with hxs
  set x₂s := π ⟨x₂, hJ₂M hx₂⟩ with hx₂s
  set Fs := (F.subgroupOf M).map π with hFs
  set Js := (J.subgroupOf M).map π with hJs
  set J₂s := (J₂.subgroupOf M).map π with hJ₂s
  have hcommKJ : ∀ y ∈ Fs, ∀ z ∈ Js, y * z = z * y := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨j, hj, rfl⟩
    exact (mk_mul_comm_of_ne hJ hK hJK (Subgroup.mem_subgroupOf.mp hj)
      (hFK (Subgroup.mem_subgroupOf.mp hf))).symm
  have hcommKJ₂ : ∀ y ∈ Fs, ∀ z ∈ J₂s, y * z = z * y := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨j, hj, rfl⟩
    exact (mk_mul_comm_of_ne hJ₂ hK hJ₂K (Subgroup.mem_subgroupOf.mp hj)
      (hFK (Subgroup.mem_subgroupOf.mp hf))).symm
  have hcommJJ₂ : ∀ y ∈ Js, ∀ z ∈ J₂s, y * z = z * y := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨j', hj', rfl⟩
    exact mk_mul_comm_of_ne hJ hJ₂ hJJ₂ (Subgroup.mem_subgroupOf.mp hj)
      (Subgroup.mem_subgroupOf.mp hj')
  have hxsJ : xs ∈ Js := ⟨⟨x, hJM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hx₂sJ : x₂s ∈ J₂s := ⟨⟨x₂, hJ₂M hx₂⟩, Subgroup.mem_subgroupOf.mpr hx₂, rfl⟩
  have hxsnc : ∃ z ∈ Js, xs * z ≠ z * xs := by
    obtain ⟨j, hj, hjx⟩ := hxnc
    refine ⟨π ⟨j, hJM hj⟩, ⟨⟨j, hJM hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩, fun h => hjx ?_⟩
    have h1 : π (⟨x, hJM hx⟩ * ⟨j, hJM hj⟩ * (⟨x, hJM hx⟩ : M)⁻¹ * (⟨j, hJM hj⟩ : M)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxs, h]
      group
    exact (hπ1 _).mp h1
  have hx₂snc : ∃ z ∈ J₂s, x₂s * z ≠ z * x₂s := by
    obtain ⟨j, hj, hjx⟩ := hx₂nc
    refine ⟨π ⟨j, hJ₂M hj⟩, ⟨⟨j, hJ₂M hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩,
      fun h => hjx ?_⟩
    have h1 : π (⟨x₂, hJ₂M hx₂⟩ * ⟨j, hJ₂M hj⟩ * (⟨x₂, hJ₂M hx₂⟩ : M)⁻¹ *
        (⟨j, hJ₂M hj⟩ : M)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hx₂s, h]
      group
    exact (hπ1 _).mp h1
  have hx₂sF : x₂s ∉ Fs := by
    intro h
    obtain ⟨z, hz, hzx⟩ := hx₂snc
    exact hzx (hcommKJ₂ _ h z hz)
  set V₁ := Fs ⊔ Subgroup.zpowers x₂s with hV₁
  have hV₁C : V₁ ≤ Subgroup.centralizer (Js : Set (M ⧸ N)) := by
    refine sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (hcommKJ y hy z hz).symm) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => hcommJJ₂ z hz x₂s hx₂sJ
  have hxsV₁ : xs ∉ V₁ := by
    intro h
    obtain ⟨z, hz, hzx⟩ := hxsnc
    exact hzx (Subgroup.mem_centralizer_iff.mp (hV₁C h) z hz).symm
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxs, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hx3)
  have hx₂s3 : x₂s ^ 3 = 1 := by
    rw [hx₂s, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hx₂3)
  have hxso : orderOf xs = 3 :=
    orderOf_eq_prime hxs3 (fun h => hxsV₁ (h ▸ V₁.one_mem))
  have hx₂so : orderOf x₂s = 3 :=
    orderOf_eq_prime hx₂s3 (fun h => hx₂sF (h ▸ Fs.one_mem))
  have hFM : F ≤ M := hFK.trans hKM
  have hF3 : IsPGroup 3 (F.subgroupOf M) := by
    refine IsPGroup.comap_subtype ?_
    exact fun f => ⟨1, Subtype.ext (by simpa using hFe f f.2)⟩
  have hFscard : Nat.card Fs = Nat.card F := by
    rw [hFs, Step198DProof.card_map_of_injOn π (Sec12.injOn_mk_of_coprime N hN3 hF3),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv]
  have hcard_sup : ∀ (Y : Subgroup (M ⧸ N)) (y : M ⧸ N), orderOf y = 3 → y ∉ Y →
      (∀ z ∈ Y, z * y = y * z) → Nat.card (Y ⊔ Subgroup.zpowers y : Subgroup (M ⧸ N)) =
        Nat.card Y * 3 := by
    intro Y y hy hyY hcomm
    have hYN : Y ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (M ⧸ N)) := fun z hz =>
      Sec12.mem_normalizer_zpowers_of_commute (hcomm z hz)
    have h1 := Sec6.card_sup_mul_card_inf hYN
    have hinf : Y ⊓ Subgroup.zpowers y = ⊥ := by
      have hdvd : Nat.card (Y ⊓ Subgroup.zpowers y : Subgroup (M ⧸ N)) ∣ 3 := by
        rw [← hy, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.card_eq_one.mp h
      · exfalso
        have heq : Y ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hy])
        have hy' : y ∈ Y ⊓ Subgroup.zpowers y := by
          rw [heq]
          exact Subgroup.mem_zpowers y
        exact hyY hy'.1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy] at h1
    exact h1
  have hV₁card : Nat.card V₁ = Nat.card F * 3 := by
    rw [hV₁, hcard_sup Fs x₂s hx₂so hx₂sF (fun z hz => hcommKJ₂ z hz x₂s hx₂sJ), hFscard]
  set V := V₁ ⊔ Subgroup.zpowers xs with hV
  have hV₁x : ∀ z ∈ V₁, z * xs = xs * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hV₁C hz) xs hxsJ).symm
  have hVcard : Nat.card V = Nat.card F * 3 * 3 := by
    rw [hV, hcard_sup V₁ xs hxso hxsV₁ hV₁x, hV₁card]
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    have hT : ∀ a ∈ ((Fs : Set (M ⧸ N)) ∪ {x₂s, xs}), ∀ b ∈ ((Fs : Set (M ⧸ N)) ∪ {x₂s, xs}),
        a * b = b * a := by
      have hFF : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hFc _ (Subgroup.mem_subgroupOf.mp hf) _
          (Subgroup.mem_subgroupOf.mp hf'))
      have hxx : x₂s * xs = xs * x₂s := (hcommJJ₂ xs hxsJ x₂s hx₂sJ).symm
      intro a ha b hb
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
      · exact hFF a ha b hb
      · rw [Set.mem_singleton_iff.mp hb]; exact hcommKJ₂ a ha _ hx₂sJ
      · rw [Set.mem_singleton_iff.mp hb]; exact hcommKJ a ha _ hxsJ
      · rw [ha]; exact (hcommKJ₂ b hb _ hx₂sJ).symm
      · rw [ha, Set.mem_singleton_iff.mp hb]
      · rw [ha, Set.mem_singleton_iff.mp hb]; exact hxx
      · rw [Set.mem_singleton_iff.mp ha]; exact (hcommKJ b hb _ hxsJ).symm
      · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]; exact hxx.symm
      · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
    have hVcl : V = Subgroup.closure ((Fs : Set (M ⧸ N)) ∪ {x₂s, xs}) := by
      rw [hV, hV₁, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_eq Fs, ← Subgroup.closure_union, ← Subgroup.closure_union,
        Subgroup.closure_eq Fs, Set.union_assoc, Set.insert_eq]
    intro a ha b hb
    rw [hVcl] at ha hb
    exact KFacts.KS14.commute_of_mem_closure hT ha hb
  have hVe : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    have hVcl : V = Subgroup.closure ((Fs : Set (M ⧸ N)) ∪ {x₂s, xs}) := by
      rw [hV, hV₁, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_eq Fs, ← Subgroup.closure_union, ← Subgroup.closure_union,
        Subgroup.closure_eq Fs, Set.union_assoc, Set.insert_eq]
    have hv' := hv
    rw [hVcl] at hv'
    induction hv' using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨f, hf, rfl⟩ | ha | ha
      · rw [← map_pow]
        exact (hπ1 _).mpr (by
          have := hFe _ (Subgroup.mem_subgroupOf.mp hf)
          rw [show ((f ^ 3 : M) : G) = (f : G) ^ 3 from rfl, this]
          exact Q.one_mem)
      · rw [Set.mem_singleton_iff.mp ha]; exact hx₂s3
      · rw [Set.mem_singleton_iff.mp ha]; exact hxs3
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hVcomm a (hVcl ▸ ha) b (hVcl ▸ hb)) 3), iha (hVcl ▸ ha),
        ihb (hVcl ▸ hb), one_mul]
    | inv a ha iha => rw [inv_pow, iha (hVcl ▸ ha), inv_one]
  have hV3 : IsPGroup 3 V := fun v => ⟨1, Subtype.ext (by simpa using hVe v v.2)⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  obtain ⟨R, hR3, ⟨eR⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π (QuotientGroup.mk'_surjective N) hker V hV3
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (hVcomm _ (eR a).2 _ (eR b).2))
  have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hVe _ (eR a).2))
  obtain ⟨r, hr⟩ := hR3.exists_card_eq
  have hr4 : 4 ≤ r := by
    have h81 : 81 ≤ 3 ^ r := by
      rw [← hr, Nat.card_congr eR.toEquiv, hVcard]
      omega
    by_contra h
    push Not at h
    interval_cases r <;> norm_num at h81
  obtain ⟨R₄, hR₄⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (G := R)
    (by rw [hr]; exact pow_dvd_pow 3 hr4)
  set X₄ := (R₄.map R.subtype).map M.subtype with hX₄
  have hX₄card : Nat.card X₄ = 3 ^ 4 := by
    rw [hX₄, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective R.subtype_injective, hR₄]
  have hX₄mem : ∀ a ∈ X₄, ∃ a' : R, (((a' : M) : G)) = a := by
    rintro _ ⟨_, ⟨a', -, rfl⟩, rfl⟩
    exact ⟨a', rfl⟩
  have hX₄c : IsMulCommutative X₄ := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha'⟩ := hX₄mem a a.2
    obtain ⟨b', hb'⟩ := hX₄mem b b.2
    change (a : G) * b = b * a
    rw [← ha', ← hb']
    exact congrArg (fun z : R => ((z : M) : G)) (hRcomm a' b'))⟩⟩
  have hX₄e : ∀ a ∈ X₄, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨a', ha'⟩ := hX₄mem a ha
    rw [← ha']
    exact congrArg (fun z : R => ((z : M) : G)) (hRe a')
  have hX₄N : X₄ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.map_subtype_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact Theta.le_localRank_of_le_normalizer (by norm_num) hQ
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hX₄c hX₄e hX₄card hX₄N

end Rank

section Action

open scoped Pointwise
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_of_le_normalizer {J A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (h3 : 3 ∣ Nat.card J) :
    ∃ y ∈ J, y ≠ 1 ∧ y ^ 3 = 1 ∧ ∀ a ∈ A, a * y = y * a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : A →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hAJ) with hρ
  let act : MulAction A (Sylow 3 J) := MulAction.compHom _ ρ
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 J) := by
    intro h
    have h1 : Nat.card (Sylow 3 J) % 3 = 1 % 3 := card_sylow_modEq_one 3 J
    have h2 := (Nat.dvd_iff_mod_eq_zero).mp h
    omega
  obtain ⟨R, hR⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 J) hnd
  set RG := (R : Subgroup J).map J.subtype with hRG
  have hRG3 : IsPGroup 3 RG := R.isPGroup'.map _
  have hRGJ : RG ≤ J := Subgroup.map_subtype_le _
  have hAR : A ≤ Subgroup.normalizer (RG : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    obtain ⟨r', hr', rfl⟩ := hr
    have hfix : (⟨a, ha⟩ : A) • R = R := hR ⟨a, ha⟩
    have h1 : ρ ⟨a, ha⟩ • r' ∈ ρ ⟨a, ha⟩ • (R : Subgroup J) :=
      Subgroup.smul_mem_pointwise_smul r' _ _ hr'
    rw [← Sylow.pointwise_smul_def] at h1
    change ρ ⟨a, ha⟩ r' ∈ (((⟨a, ha⟩ : A) • R : Sylow 3 J) : Subgroup J) at h1
    rw [hfix] at h1
    exact ⟨_, h1, rfl⟩
  have hRne : RG ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card RG = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hRG, Subgroup.card_map_of_injective J.subtype_injective, Sylow.card_eq_multiplicity]
      at h1
    have h2 := Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' h3
    have h3' : 3 ^ 1 ≤ 3 ^ (Nat.card J).factorization 3 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  set Z := A ⊔ RG with hZ
  have hZ3 : IsPGroup 3 Z := hA3.to_sup_of_normal_right' hRG3 hAR
  have hZN : Z ≤ Subgroup.normalizer (RG : Set G) := sup_le hAR Subgroup.le_normalizer
  have hRZn : (RG.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hZN
  have hRZne : RG.subgroupOf Z ≠ ⊥ := by
    intro h
    apply hRne
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, Subgroup.mem_sup_right hr⟩ : Z) ∈ RG.subgroupOf Z :=
      Subgroup.mem_subgroupOf.mpr hr
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent Z := hZ3.isNilpotent
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hRZne)
  have hzR : ((z : Z) : G) ∈ RG := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
  have hzC : ∀ a ∈ A, a * (z : Z) = ((z : Z) : G) * a := by
    intro a ha
    have h1 := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2
      ⟨a, Subgroup.mem_sup_left ha⟩
    exact congrArg Subtype.val h1
  set z' : G := ((z : Z) : G) with hz'
  have hz'1 : z' ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := hRG3 ⟨z', hzR⟩
  have hz'k : z' ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz'k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hz'1 hj
  have h3z : 3 ∣ Nat.card (Subgroup.zpowers z') := by
    rw [Nat.card_zpowers, hj]
    exact dvd_pow_self 3 hj0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers z') 3 h3z
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
  have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨y, hRGJ (by rw [← hm]; exact RG.zpow_mem hzR m), fun h => ?_, ?_, fun a ha => ?_⟩
  · rw [h, orderOf_one] at hyo
    norm_num at hyo
  · rw [← hyo]
    exact pow_orderOf_eq_one _
  · rw [← hm]
    exact ((Commute.zpow_right (hzC a ha) m))

theorem map_pCore_two {H : Type*} [Group H] (σ : MulAut H) :
    (CFSG.pCore 2 H).map (σ : H →* H) = CFSG.pCore 2 H :=
  (Subgroup.characteristic_iff_map_eq.mp CFSG.pCore_characteristic) σ

@[expose] noncomputable def pCoreQuotMulAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ CFSG.pCore 2 H) where
  toFun σ := QuotientGroup.congr _ _ σ (map_pCore_two σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def quotAct {J A : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    A →* MulAut (J ⧸ CFSG.pCore 2 J) :=
  (pCoreQuotMulAut J).comp (J.normalizerMonoidHom.comp (Subgroup.inclusion hAJ))

omit [Finite G] in
theorem quotAct_mk {J A : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (a : A)
    (j : J) : ∃ j' : J, (j' : G) = a * j * (a : G)⁻¹ ∧
      quotAct hAJ a (j : J ⧸ CFSG.pCore 2 J) = (j' : J ⧸ CFSG.pCore 2 J) :=
  ⟨J.normalizerMonoidHom ⟨a, hAJ a.2⟩ j, rfl, rfl⟩

theorem exists_lift_of_fixed {J A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {x : J ⧸ CFSG.pCore 2 J}
    (hfix : ∀ a : A, quotAct hAJ a x = x) (hx3 : x ^ 3 = 1)
    (hxc : x ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J)) :
    ∃ y : J, (y : G) ^ 3 = 1 ∧ (∀ a ∈ A, a * y = (y : G) * a) ∧
      (y : J ⧸ CFSG.pCore 2 J) ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j₀, rfl⟩ := QuotientGroup.mk_surjective x
  set O := CFSG.Open.pCoreOf 2 J with hO
  have hOJ : O ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  set Y := J ⊔ A with hY
  have hJY : J ≤ Y := le_sup_left
  have hAY : A ≤ Y := le_sup_right
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
      (hAJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
  set NY := O.subgroupOf Y with hNY
  have hNYn : NY.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hOJ.trans hJY)).mpr hYO
  set πY := QuotientGroup.mk' NY with hπY
  have hker : ¬ 3 ∣ Nat.card πY.ker := by
    rw [hπY, QuotientGroup.ker_mk', hNY,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOJ.trans hJY)).toEquiv]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hmemO : ∀ k : J, k ∈ CFSG.pCore 2 J ↔ (k : G) ∈ O := fun k =>
    Step1911EndProof.mem_pCore_iff k
  have htarget : πY ⟨j₀, hJY j₀.2⟩ ∈
      Subgroup.centralizer ((A.subgroupOf Y).map πY : Set (Y ⧸ NY)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨j', hj', hfix'⟩ := quotAct_mk hAJ ⟨a, haA⟩ j₀
    have h1 := hfix ⟨a, haA⟩
    rw [hfix'] at h1
    have h2 : (j'⁻¹ * j₀ : J) ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp h1
    rw [hmemO] at h2
    have h3 : (a : G) * j₀ * (a : G)⁻¹ * (j₀ : G)⁻¹ ∈ O := by
      have e : (a : G) * j₀ * (a : G)⁻¹ * (j₀ : G)⁻¹ =
          (j₀ : G) * ((j'⁻¹ * j₀ : J) : G)⁻¹ * (j₀ : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hj']
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
        j₀.2) _).mp (O.inv_mem h2)
    have h4 : πY (a * ⟨j₀, hJY j₀.2⟩ * a⁻¹ * (⟨j₀, hJY j₀.2⟩ : Y)⁻¹) = 1 := by
      rw [hπY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNY, Subgroup.mem_subgroupOf]
      exact h3
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h4
    exact Step1910O2Proof.mul_comm_of_commutator_eq_one h4
  obtain ⟨e, he, hee⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel
    3 Nat.prime_three πY (QuotientGroup.mk'_surjective _) hker (A.subgroupOf Y)
    hA3.comap_subtype _ htarget
  rw [hπY, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hee
  have hv : ((⟨j₀, hJY j₀.2⟩ : Y)⁻¹ * e : Y) ∈ NY := QuotientGroup.eq.mp hee.symm
  rw [hNY, Subgroup.mem_subgroupOf] at hv
  have heJ : (e : G) ∈ J := by
    have e1 : (e : G) = j₀ * (((⟨j₀, hJY j₀.2⟩ : Y)⁻¹ * e : Y) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact J.mul_mem j₀.2 (hOJ hv)
  set e' : J := ⟨e, heJ⟩ with he'
  have hmk : (e' : J ⧸ CFSG.pCore 2 J) = (j₀ : J ⧸ CFSG.pCore 2 J) := by
    apply QuotientGroup.eq.mpr
    rw [hmemO]
    have e1 : ((e'⁻¹ * j₀ : J) : G) = ((((⟨j₀, hJY j₀.2⟩ : Y)⁻¹ * e : Y) : G))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, he']
      group
    rw [e1]
    exact O.inv_mem hv
  have heA : ∀ a ∈ A, a * (e' : G) = (e' : G) * a := by
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp he ⟨a, hAY ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  set n := Nat.card (CFSG.pCore 2 J) with hn
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)).exists_card_eq
  have he'3 : e' ^ 3 ∈ CFSG.pCore 2 J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk]
    exact hx3
  refine ⟨e' ^ n, ?_, fun a ha => ?_, fun hc => hxc ?_⟩
  · have h1 : (⟨e' ^ 3, he'3⟩ : CFSG.pCore 2 J) ^ n = 1 := pow_card_eq_one'
    have h2 : (e' ^ 3) ^ n = 1 := by simpa using congrArg Subtype.val h1
    rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul]
    simpa using congrArg Subtype.val h2
  · rw [Subgroup.coe_pow]
    exact (Commute.pow_right (heA a ha) n)
  · rw [QuotientGroup.mk_pow, hmk] at hc
    have hnn : (n * n) % 3 = 1 := by
      rw [hn, hk, ← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    have hpow : (j₀ : J ⧸ CFSG.pCore 2 J) = ((j₀ : J ⧸ CFSG.pCore 2 J) ^ n) ^ n := by
      rw [← pow_mul, ← Nat.div_add_mod (n * n) 3, hnn, pow_add, pow_mul, hx3, one_pow, one_mul,
        pow_one]
    rw [hpow]
    exact Subgroup.pow_mem _ hc n

theorem isProperParabolic_map {X Y : Type*} [Group X] [Finite X] [Group Y] (e : X ≃* Y)
    {P : Subgroup X} (hP : IsProperParabolic P) : IsProperParabolic (P.map e.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hP
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨fun h => hPtop ?_, T.mapSurjective hes, ?_⟩
  · rw [eq_top_iff]
    intro p _
    have hp : e.toMonoidHom p ∈ P.map e.toMonoidHom := h ▸ Subgroup.mem_top _
    obtain ⟨p', hp', hpp'⟩ := hp
    rwa [e.injective hpp'] at hp'
  · rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hT

theorem exists_fixed_of_mulEquiv_SL {J A H : Subgroup G}
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAH : A ≤ H) (hAe : ∀ a ∈ A, a ^ 3 = 1)
    {F : Type} [Field F] [Finite F] [CharP F 2] {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (ψ : J ⧸ CFSG.pCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hpar : IsProperParabolic (starIm J H)) :
    ∃ x : J ⧸ CFSG.pCore 2 J, x ^ 3 = 1 ∧ x ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) ∧
      ∀ a : A, quotAct hAJ a x = x := by
  classical
  set ρ := (MulAut.congr ψ).toMonoidHom.comp (quotAct hAJ) with hρ
  set W := ρ.range with hW
  have hW3 : ∀ w ∈ W, w ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ 3 = 1 := Subtype.ext (by simpa using hAe a a.2)
    rw [← map_pow, ha, map_one]
  set P' := (starIm J H).map ψ.toMonoidHom with hP'
  have hP'par : IsProperParabolic P' := isProperParabolic_map ψ hpar
  have hWP : ∀ w ∈ W, ∀ p ∈ P', w p ∈ P' := by
    rintro _ ⟨a, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨j, hjH, rfl⟩ := hq
    obtain ⟨j', hj', hact⟩ := quotAct_mk hAJ a j
    refine ⟨_, ⟨j', Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
    · rw [hj']
      exact H.mul_mem (H.mul_mem (hAH a.2) (Subgroup.mem_subgroupOf.mp hjH))
        (H.inv_mem (hAH a.2))
    · simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      change ψ (j' : J ⧸ CFSG.pCore 2 J) = ψ ((quotAct hAJ a) (j : J ⧸ CFSG.pCore 2 J))
      rw [hact]
  obtain ⟨x', hx'3, hx'c, hx'f⟩ := slThreeFixedOfParabolic F ω hω1 hω3 W hW3 P' hP'par hWP
  refine ⟨ψ.symm x', by rw [← map_pow, hx'3, map_one], fun hc => hx'c ?_, fun a => ?_⟩
  · rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply ψ.symm.injective
    rw [map_mul, map_mul]
    exact hc (ψ.symm g)
  · have h1 := hx'f (ρ a) ⟨a, rfl⟩
    simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply] at h1
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1

end Action

section Cores

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le {M J : Subgroup G} (hJ : J ∈ oTwoComponentsIn M) :
    J ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 J :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (le_of_mem_oTwoComponentsIn hJ hj)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)

theorem inf_pCoreOf_le_theta {M L : Subgroup G} (hLM : L ≤ M) :
    L ⊓ CFSG.Open.pCoreOf 2 M ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
  have h1 : L ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hLM hl)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  refine h1.trans ?_
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have h2 := hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  rw [← Sec18.inSubgroup_pCore_eq_pCoreOf, CFSG.inSubgroup]
  exact Subgroup.map_mono h2

theorem mk_ne_one_of_orderOf {J : Subgroup G} {c : J} (hc : orderOf (c : G) = 3) :
    (c : J ⧸ CFSG.pCore 2 J) ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  rw [QuotientGroup.eq_one_iff, Step1911EndProof.mem_pCore_iff] at h
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J ⟨_, h⟩
  have hck : (c : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd := orderOf_dvd_of_pow_eq_one hck
  rw [hc] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

end Cores

end Step1910Proof

end CFSG.RankThree.PartTwo.Sec19
