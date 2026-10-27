module

public import CFSG.RankThree.PartTwo.Sec21.Item222KLeProof
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem oPrimeResidual_three_normal (X : Type*) [Group X] :
    (CFSG.GH74.GLS.oPrimeResidual 3 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold CFSG.GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    exact Subgroup.subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem oPrimeResidual_three_eq_top {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) : CFSG.GH74.GLS.oPrimeResidual 3 X = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := oPrimeResidual_three_normal X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.GH74.GLS.oPrimeResidual 3 X) with
    hb | ht
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hmem : x ∈ CFSG.GH74.GLS.oPrimeResidual 3 X :=
      Subgroup.subset_closure ⟨1, by rw [pow_one, ← hx, pow_orderOf_eq_one]⟩
    rw [hb, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hx
    norm_num at hx
  · exact ht

theorem kZero_le_perfectResidual [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G) {c : G}
    (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L)
    (hφ2 : orderOf φ = 2) :
    kZero A φ ≤
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  have hφt : ∀ a : A, ((φ a : A) : G) = (t : G) * a * (t : G)⁻¹ := fun a => by
    rw [← htφ]
    rfl
  obtain ⟨hLC, hLth⟩ :=
    (mem_thetaComponentsIn_iff (H := Subgroup.centralizer ({c} : Set G))).mp hLc
  set B := fixedInG A φ with hBdef
  set X := Subgroup.centralizer (B : Set G) with hXdef
  have hcB : c ∈ B := by
    refine ⟨⟨c, hcA⟩, (mem_fixedSubgroupOf φ _).mpr ?_, rfl⟩
    apply Subtype.ext
    rw [hφt]
    have htc : (t : G) * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hLC htL')
    change (t : G) * c * (t : G)⁻¹ = c
    rw [htc, mul_inv_cancel_right]
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  have hAX : A ≤ X := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (hAc b ⟨a, ha⟩)
  set Y : Subgroup X := (L ⊓ X).subgroupOf X with hYdef
  have hY : Y.IsSubnormal := by
    have h1 := hLth.2.1.comap (Subgroup.inclusion hXc)
    convert h1 using 1
    ext x
    simp only [hYdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.coe_inclusion]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hYmap : Y.map X.subtype = L ⊓ X := by
    rw [hYdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hWL : ∀ a : A, ((a⁻¹ * φ a : A) : G) ∈ L ⊓ X := by
    intro a
    refine ⟨?_, hAX (a⁻¹ * φ a).2⟩
    have hφw : φ (a⁻¹ * φ a) = (a⁻¹ * φ a)⁻¹ := by
      rw [map_mul, map_inv, apply_apply_of_orderOf_eq_two hφ2]
      group
    refine mem_of_conj_eq_inv_of_mem_thetaComponentsAt hLc htL'
      (congrArg Subtype.val (hAc (a⁻¹ * φ a) ⟨c, hcA⟩)) (hAe.2 _ (a⁻¹ * φ a).2) ?_
    rw [← hφt (a⁻¹ * φ a), hφw]
    rfl
  set S : Set (Subgroup G) :=
    {M | ∃ K : Subgroup X, IsComponent K ∧ ⁅K, Y⁆ = ⊥ ∧ K.map X.subtype = M} with hSdef
  set T : Subgroup G := sSup S with hTdef
  have hSC : ∀ M ∈ S, M ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := by
    rintro M ⟨K, -, hKY, rfl⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hYmap, ← Subgroup.map_commutator,
      hKY, Subgroup.map_bot]
  have hSA : ∀ M ∈ S, M ≤ Subgroup.centralizer (A : Set G) := by
    intro M hM g hg
    have hgX : g ∈ X := by
      obtain ⟨K, -, -, rfl⟩ := hM
      exact Subgroup.map_subtype_le K hg
    have hgL := hSC M hM hg
    rw [Subgroup.mem_centralizer_iff]
    exact commute_of_commute_fixed_of_commute_commOf hAe hφ2
      (fun b hb => Subgroup.mem_centralizer_iff.mp hgX b hb)
      (fun a => Subgroup.mem_centralizer_iff.mp hgL _ (hWL a))
  have hSp : ∀ M ∈ S, Group.IsPerfect M := by
    rintro M ⟨K, hK, -, rfl⟩
    exact isPerfect_map_subtype hK.1.1
  have hTC : T ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := sSup_le hSC
  have hTA : T ≤ Subgroup.centralizer (A : Set G) := sSup_le hSA
  have hTp : Group.IsPerfect T := isPerfect_sSup_of_forall_isPerfect hSp
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h3
    obtain ⟨e, heT, he3, heA⟩ := Sec6.exists_pow_three_eq_one_not_mem hTp h3
      (Subgroup.le_centralizer_iff.mp hTA)
    exact heA (Sec4.mem_of_maximal_of_commute hAmax he3 fun a ha =>
      Subgroup.mem_centralizer_iff.mp (hTA heT) a ha)
  have hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) 3 := by
    intro v hv
    have hdvd : orderOf v ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk v hv]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3).symm
  set R := inSubgroup perfectResidual (L ⊓ X) with hRdef
  have hRle : R ≤ L ⊓ X := Subgroup.map_subtype_le _
  have hE : inSubgroup CFSG.layer X ≤ R ⊔ T := by
    rw [inSubgroup, Subgroup.map_le_iff_le_comap, CFSG.layer]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    rcases CFSG.LocalCores.component_subnormal_subgroup hK hY with hKY | hKY
    · have hKp : ⁅K.map X.subtype, K.map X.subtype⁆ = K.map X.subtype :=
        Subgroup.isPerfect_iff.mp (isPerfect_map_subtype hK.1.1)
      exact (Sec18.le_inSubgroup_perfectResidual hKp
        ((Subgroup.map_mono hKY).trans hYmap.le)).trans le_sup_left
    · exact (le_sSup ⟨K, hK, hKY, rfl⟩ : K.map X.subtype ≤ T).trans le_sup_right
  have hTR : T ≤ Subgroup.centralizer (R : Set G) := hTC.trans (Subgroup.centralizer_le hRle)
  show CFSG.GH74.GLS.oPrimeResidualOf 3 (inSubgroup CFSG.layer X) ≤ R
  rw [CFSG.GH74.GLS.oPrimeResidualOf, CFSG.GH74.GLS.oPrimeResidual, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
  have hyk : (y : G) ^ (3 ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  exact mem_of_pow_eq_one_of_mem_sup_centralizer hTR hcop (hE y.2) hyk

theorem isSubnormal_inf_centralizer [Finite G] {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L) :
    ((L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)).subgroupOf
      (Subgroup.centralizer (fixedInG A φ : Set G))).IsSubnormal := by
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  obtain ⟨hLC, hLth⟩ :=
    (mem_thetaComponentsIn_iff (H := Subgroup.centralizer ({c} : Set G))).mp hLc
  have hcB : c ∈ fixedInG A φ := by
    refine ⟨⟨c, hcA⟩, (mem_fixedSubgroupOf φ _).mpr ?_, rfl⟩
    apply Subtype.ext
    rw [← htφ]
    have htc : (t : G) * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hLC htL')
    change (t : G) * c * (t : G)⁻¹ = c
    rw [htc, mul_inv_cancel_right]
  have hXc : Subgroup.centralizer (fixedInG A φ : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  have h1 := hLth.2.1.comap (Subgroup.inclusion hXc)
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.coe_inclusion]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩

theorem perfectResidual_le_kZero [Finite G] {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L)
    (hS : IsQuasisimple
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G))))
    (h3 : CFSG.GH74.GLS.oPrimeResidual 3
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G))) = ⊤) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≤
      kZero A φ := by
  set X := Subgroup.centralizer (fixedInG A φ : Set G) with hXdef
  set Y : Subgroup X := (L ⊓ X).subgroupOf X with hYdef
  set R := inSubgroup perfectResidual (L ⊓ X) with hRdef
  have hY : Y.IsSubnormal := isSubnormal_inf_centralizer hcA hLc hφL
  have hRLX : R ≤ L ⊓ X := Subgroup.map_subtype_le _
  have hRX : R ≤ X := hRLX.trans inf_le_right
  set R' : Subgroup X := R.subgroupOf X with hR'def
  have hR'Y : R' ≤ Y := fun x hx => Subgroup.mem_subgroupOf.mpr (hRLX hx)
  have hRn : ∀ y ∈ L ⊓ X, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨r', hr', rfl⟩ := hr
    have hn : (perfectResidual ↥(L ⊓ X)).Normal := inferInstance
    exact ⟨⟨y, hy⟩ * r' * ⟨y, hy⟩⁻¹, hn.conj_mem r' hr' ⟨y, hy⟩, rfl⟩
  have hR'n : (R'.subgroupOf Y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx ⊢
    have hgY : ((g : X) : G) ∈ L ⊓ X := Subgroup.mem_subgroupOf.mp g.2
    exact hRn _ hgY _ hx
  have hR'sn : R'.IsSubnormal := Subgroup.IsSubnormal.trans hR'Y hR'n.isSubnormal hY
  have hR'q : IsQuasisimple R' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRX).symm hS
  have hR'E : R' ≤ CFSG.layer X := le_sSup ⟨hR'q, hR'sn⟩
  have hRE : R ≤ inSubgroup CFSG.layer X := by
    intro r hr
    exact ⟨⟨r, hRX hr⟩, hR'E (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  intro r hr
  have hr' : (⟨r, hr⟩ : R) ∈ CFSG.GH74.GLS.oPrimeResidual 3 R := by rw [h3]; trivial
  have hmap : (CFSG.GH74.GLS.oPrimeResidual 3 R).map (Subgroup.inclusion hRE) ≤
      CFSG.GH74.GLS.oPrimeResidual 3 (inSubgroup CFSG.layer X) := by
    unfold CFSG.GH74.GLS.oPrimeResidual
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  exact ⟨Subgroup.inclusion hRE ⟨r, hr⟩, hmap ⟨_, hr', rfl⟩, rfl⟩

theorem kZero_eq_perfectResidual [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G) {c : G}
    (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L)
    (hφ2 : orderOf φ = 2)
    (hS : IsSimpleGroup
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G))))
    (hnab : ∃ x y : inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)), x * y ≠ y * x)
    (h3 : 3 ∣ Nat.card
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)))) :
    kZero A φ = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) := by
  have := hS
  exact le_antisymm (kZero_le_perfectResidual hA hcA hLc hφL hφ2)
    (perfectResidual_le_kZero hcA hLc hφL
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1 (oPrimeResidual_three_eq_top h3))

theorem not_statedClassicalModel_U34_of_mulEquiv {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (e : X ≃* projSL 2 (GaloisField 2 m)) : ¬ StatedClassicalModel X .PSU 3 2 2 := by
  intro hU
  have h1 : Nat.card X = 62400 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl]
    decide
  rw [Nat.card_congr e.toEquiv, card_projSL_two m hm] at h1
  have hm6 : m ≤ 6 := by
    by_contra h
    have h7 : 2 ^ 7 ∣ 62400 :=
      (pow_dvd_pow 2 (by omega : 7 ≤ m)).trans (h1 ▸ dvd_mul_right _ _)
    norm_num at h7
  interval_cases m <;> norm_num at h1

theorem nonempty_kOf_mulEquiv_projSL [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G)
    {c : G} (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A}
    (hφL : φ ∈ starOf A L) (hφ2 : orderOf φ = 2) {m : ℕ} (hm : 2 ≤ m)
    (e : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
      projSL 2 (GaloisField 2 m)) :
    Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) := by
  have := isSimpleGroup_projSL_two hm
  have hK := kZero_eq_perfectResidual hA hcA hLc hφL hφ2 e.isSimpleGroup
    (exists_not_commute_of_mulEquiv_projSL e) (three_dvd_card_of_mulEquiv_projSL e)
  have hU : ¬ StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    rw [hK]
    exact not_statedClassicalModel_U34_of_mulEquiv (by omega) e
  rw [kOf_eq_kZero hU, hK]
  exact ⟨e⟩

theorem nonempty_mulEquiv_projSL_of_statedClassicalModel {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 2 2) :
    Nonempty (X ≃* projSL 2 (GaloisField 2 2)) :=
  CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h

theorem exists_not_commute_of_isSimpleGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (h3 : 3 ∣ Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hn : (Subgroup.zpowers x).Normal :=
    ⟨fun a ha g => by rw [hc g a, mul_inv_cancel_right]; exact ha⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with hb | ht
  · rw [Subgroup.zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hx
    norm_num at hx
  · have hcard : Nat.card X = 2 := by
      rw [← Subgroup.card_top (G := X), ← ht, Nat.card_zpowers, hx]
    have := orderOf_dvd_natCard y
    rw [hy, hcard] at this
    norm_num at this

theorem nonempty_kOf_mulEquiv_of_U34 [Finite G] {A L : Subgroup G} (hA : A ∈ partTwoF G)
    (hKW : KOfWellDefined A) {c : G} (hcA : c ∈ A) (hLc : L ∈ thetaComponentsAt 3 c)
    {φ : MulAut A} (hφL : φ ∈ starOf A L) (hφD : φ ∈ dStar A)
    (hU : StatedClassicalModel
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G))) .PSU 3 2 2) :
    Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 2)) := by
  have hS := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 2 hU).2
  have hcard : Nat.card
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G))) = 62400 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl]
    decide
  have hK := kZero_eq_perfectResidual hA hcA hLc hφL hφD.1.1 hS
    (exists_not_commute_of_isSimpleGroup (by rw [hcard]; norm_num) (by rw [hcard]; norm_num))
    (by rw [hcard]; norm_num)
  have hU' : StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
    rw [hK]
    exact hU
  obtain ⟨K, hKp, -⟩ := hKW φ hφD hU'
  exact nonempty_mulEquiv_projSL_of_statedClassicalModel (kOf_spec hU' ⟨K, hKp⟩).2.1

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
