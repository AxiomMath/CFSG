module

public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartTwo.Notation
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.Quasithin.SteinbergCFFullLocalSylowIntermediates
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GH74.GLS.Basic
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153

open CFSG CFSG.Quasithin CFSG.RankThree.PartTwo

section Thompson

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonJ_le_self (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup₂_le fun _ hA => hA.1

theorem le_normalizer_thompsonJ_of_le {R S K : Subgroup G} (hJR : thompsonJ S ≤ R)
    (hRS : R ≤ S) (hK : K ≤ Subgroup.normalizer (R : Set G)) :
    K ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  rw [← CFSG.QuasithinUnique.GammaExtra.thompsonJ_eq_of_le hJR hRS]
  exact hK.trans (CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ R)

end Thompson

section Group

variable {X : Type} [Group X] [Finite X]

theorem exists_char_normal_of_thompsonJ_le {S : Subgroup X} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hOS : CFSG.pCore 2 X ≤ S) (hJ : thompsonJ S ≤ CFSG.pCore 2 X) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal := by
  refine ⟨thompsonJ S, CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS2 hS1,
    thompsonJ_le_self S, CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S, ?_⟩
  have hON : Subgroup.normalizer (CFSG.pCore 2 X : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal
  have h := le_normalizer_thompsonJ_of_le (K := ⊤) hJ hOS hON.ge
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem pCore_le_of_mem_maxInvariant {A S : Subgroup X}
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) : CFSG.pCore 2 X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hO2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hON : Subgroup.normalizer (CFSG.pCore 2 X : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal
  have hmem : S ⊔ CFSG.pCore 2 X ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
        (IsPGroup.to_sup_of_normal_right' hS2 hO2 (hON ▸ le_top)),
      Sec14.le_normalizer_sup hS.prop.2.2 (hON ▸ le_top)⟩
  exact le_sup_right.trans (hS.2 hmem le_sup_left)

theorem pCore_ne_bot_of_nontrivial [Nontrivial X] (hF : generalizedFitting X = CFSG.pCore 2 X) :
    CFSG.pCore 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  have hchar : IsCharacteristicP 2 X :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hxc : x ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [h0] at hh
    rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
  have hxO : x ∈ CFSG.pCore 2 X := hchar hxc
  rw [h0] at hxO
  exact hx (Subgroup.mem_bot.mp hxO)

end Group

section CharTwo

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_two_mem_of_sup {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hx : x ∈ Y ⊔ S) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ Y := by
  have hx' : x ∈ ((S ⊔ Y : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S Y hSY] at hx'
  obtain ⟨s, hs, y, hy, rfl⟩ := hx'
  obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
  have ha' : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hm : ∀ m : ℕ, ∃ y' ∈ Y, (s * y) ^ m = s ^ m * y' := by
    intro m
    induction m with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨y', hy', he⟩ := ih
      have hyc : s⁻¹ * y' * s⁻¹⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y').mp hy'
      refine ⟨(s⁻¹ * y' * s⁻¹⁻¹) * y, Y.mul_mem hyc hy, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨y', hy', he⟩ := hm (2 ^ a)
  exact ⟨a, by rw [he, ha', one_mul]; exact hy'⟩

theorem charTwo_sup_of_isPGroup {Y S : Subgroup G} (hY : CFSG.QuasithinUnique.CharTwo Y)
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.QuasithinUnique.CharTwo (Y ⊔ S) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hY hS2 hSY

theorem generalizedFitting_sup_eq {Y S : Subgroup G}
    (hY : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    generalizedFitting ↥(Y ⊔ S) = CFSG.pCore 2 ↥(Y ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYc : CFSG.QuasithinUnique.CharTwo Y :=
    CFSG.Quasithin.SteinbergCF.charTwo_iff_isCharacteristicP.mpr
      ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mpr hY)
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥(Y ⊔ S) 2).mp
    (CFSG.Quasithin.SteinbergCF.charTwo_iff_isCharacteristicP.mp
      (charTwo_sup_of_isPGroup hYc hS2 hSY))

end CharTwo

section Residual

open CFSG.GH74.GLS

theorem oResidual_eq_of_pow {Q : Type*} [Group Q] [Finite Q] {J : Subgroup Q}
    (hJ : J ≤ oResidual 2 Q) (hpow : ∀ y : Q, ∃ a : ℕ, y ^ 2 ^ a ∈ J) : oResidual 2 Q = J := by
  refine le_antisymm ?_ hJ
  rw [oResidual, Subgroup.closure_le]
  intro y hy
  obtain ⟨a, ha⟩ := hpow y
  have hcop : Nat.Coprime (2 ^ a) (orderOf y) := (Nat.Coprime.pow_right a hy).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [SetLike.mem_coe, ← hm]
  exact Subgroup.pow_mem _ ha m

theorem map_oResidual_le {Q Q' : Type*} [Group Q] [Group Q'] [Finite Q] (f : Q →* Q') :
    (oResidual 2 Q).map f ≤ oResidual 2 Q' := by
  rw [oResidual, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  refine Subgroup.subset_closure ?_
  exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f y) hy

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_sup_eq {Y S : Subgroup G} (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    Y ⊓ CFSG.Open.pCoreOf 2 (Y ⊔ S) = CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXY : Y ⊔ S ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (CFSG.RankThree.PartTwo.Late.le_normalizer_inf Subgroup.le_normalizer
        ((le_sup_left : Y ≤ Y ⊔ S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_left)
      (hXY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf {p : ℕ} {K : Subgroup G} (x : K) :
    x ∈ CFSG.pCore p K ↔ (x : G) ∈ CFSG.Open.pCoreOf p K := (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite G] in
theorem subgroupOf_le_oResidual {Y H : Subgroup G} (hYH : Y ≤ H)
    (hY3 : Y = oPrimeResidualOf 3 Y) : Y.subgroupOf H ≤ oResidual 2 ↥H := by
  let ι : ↥Y →* ↥H := Subgroup.inclusion hYH
  have hrange : (oPrimeResidual 3 ↥Y).map ι ≤ oResidual 2 ↥H := by
    rw [oPrimeResidual, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    refine Subgroup.subset_closure ?_
    change Nat.Coprime (orderOf (ι x)) 2
    have hd : orderOf (ι x) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ (by norm_num))
  intro z hz
  have hzY : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hz
  have hz3 : (z : G) ∈ oPrimeResidualOf 3 Y := by rw [← hY3]; exact hzY
  obtain ⟨y', hy', hyz⟩ := Subgroup.mem_map.mp hz3
  have hzι : z = ι y' := Subtype.ext (by rw [← hyz]; rfl)
  rw [hzι]
  exact hrange ⟨y', hy', rfl⟩

theorem oResidual_sup_eq {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hY3 : Y = oPrimeResidualOf 3 Y) :
    oResidual 2 ↥(Y ⊔ S) = Y.subgroupOf (Y ⊔ S) := by
  refine oResidual_eq_of_pow (subgroupOf_le_oResidual le_sup_left hY3) fun y => ?_
  obtain ⟨a, ha⟩ := exists_pow_two_mem_of_sup hS2 hSY y.2
  exact ⟨a, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact ha⟩

theorem nonempty_oResidual_quotient_equiv {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hY3 : Y = oPrimeResidualOf 3 Y) :
    Nonempty (oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S)) ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set H := Y ⊔ S with hH
  set J := Y.subgroupOf H with hJ
  have hres : oResidual 2 ↥H = J := oResidual_sup_eq hS2 hSY hY3
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hJpow : ∀ y : ↥H, ∃ a : ℕ, y ^ 2 ^ a ∈ J := by
    intro y
    obtain ⟨a, ha⟩ := exists_pow_two_mem_of_sup hS2 hSY y.2
    exact ⟨a, by rw [hJ, Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact ha⟩
  have hresQ : oResidual 2 (↥H ⧸ CFSG.pCore 2 ↥H) = J.map π := by
    refine oResidual_eq_of_pow ?_ ?_
    · rw [← hres]
      exact map_oResidual_le π
    · intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) z
      obtain ⟨a, ha⟩ := hJpow y
      exact ⟨a, by rw [← map_pow]; exact ⟨_, ha, rfl⟩⟩
  set φ : ↥Y →* ↥H ⧸ CFSG.pCore 2 ↥H := π.comp (Subgroup.inclusion le_sup_left) with hφ
  have hrange : φ.range = J.map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥Y := by
    ext k
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf, mem_pCore_iff_mem_pCoreOf,
      ← inf_pCoreOf_sup_eq hSY]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  exact ⟨(MulEquiv.subgroupCongr (hresQ.trans hrange.symm)).trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))⟩

end Residual

theorem isSubnormal_subgroupOf_trans {G : Type*} [Group G] {E Y X : Subgroup G} (hEY : E ≤ Y)
    (hYX : Y ≤ X) (hE : (E.subgroupOf Y).IsSubnormal) (hY : (Y.subgroupOf X).IsSubnormal) :
    (E.subgroupOf X).IsSubnormal := by
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (E.subgroupOf Y).comap ι = (E.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((E.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hE.comap ι
  exact Subgroup.IsSubnormal.trans (fun x hx => hEY hx) h1 hY

theorem isSubnormal_subgroupOf_normalizer {G : Type*} [Group G] {Y X : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    (Y.subgroupOf (Subgroup.normalizer (X : Set G))).IsSubnormal := by
  have h1 : (Y.subgroupOf X).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY).isSubnormal
  have h2 : (X.subgroupOf (Subgroup.normalizer (X : Set G))).IsSubnormal :=
    (Subgroup.normal_in_normalizer).isSubnormal
  exact isSubnormal_subgroupOf_trans hYX Subgroup.le_normalizer h1 h2

end CFSG.RankThree.PartTwo.Sec15.Push153
