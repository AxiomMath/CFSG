module

public import CFSG.Walter.Bender1970.S2.Layer
public import CFSG.Walter.Bender1970.S2.PGroup
public import CFSG.Walter.Bender1970.S2.Transport
public import CFSG.GroupTheory.SubnormalJoin
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.InvolutionCentralizesNormalizedTwoSubgroup
import CFSG.GroupTheory.LocalCores.Components
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem mem_normalizer_sSup {𝒦 : Set (Subgroup G)} {g : G}
    (h : ∀ K ∈ 𝒦, g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((sSup 𝒦 : Subgroup G) : Set G) := by
  have key : ∀ g : G, (∀ K ∈ 𝒦, g ∈ Subgroup.normalizer (K : Set G)) →
      (sSup 𝒦).map (MulAut.conj g).toMonoidHom ≤ sSup 𝒦 := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_trans ?_ (le_sSup hK)
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hg K hK) k).mp hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g h ⟨x, hx, rfl⟩, fun hx => ?_⟩
  have h1 := key g⁻¹ (fun K hK => Subgroup.inv_mem _ (h K hK)) ⟨_, hx, rfl⟩
  simpa [mul_assoc] using h1

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← sSup_pair]
  refine mem_normalizer_sSup fun K hK => ?_
  rcases hK with rfl | rfl
  · exact hA
  · exact hB

theorem isSubnormal_subgroupOf_trans {A B C : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).IsSubnormal) (hB : (B.subgroupOf C).IsSubnormal) :
    (A.subgroupOf C).IsSubnormal := by
  let ψ : (B.subgroupOf C) →* B :=
    { toFun := fun x => ⟨((x : C) : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hA' : ((A.subgroupOf C).subgroupOf (B.subgroupOf C)).IsSubnormal := by
    convert hA.comap ψ using 1
    ext x
    exact Iff.rfl
  exact Subgroup.IsSubnormal.trans (fun x hx => hAB hx) hA' hB

theorem isSubnormal_subgroupOf_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : (A.subgroupOf B).IsSubnormal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mpr hBA).isSubnormal

theorem mem_normalizer_sSup_of_map_mem {𝒦 : Set (Subgroup G)} {g : G}
    (h : ∀ K ∈ 𝒦, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦)
    (h' : ∀ K ∈ 𝒦, K.map (MulAut.conj g⁻¹).toMonoidHom ∈ 𝒦) :
    g ∈ Subgroup.normalizer ((sSup 𝒦 : Subgroup G) : Set G) := by
  have key : ∀ g : G, (∀ K ∈ 𝒦, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦) →
      (sSup 𝒦).map (MulAut.conj g).toMonoidHom ≤ sSup 𝒦 := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hg K hK)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g h ⟨x, hx, rfl⟩, fun hx => ?_⟩
  have h1 := key g⁻¹ h' ⟨_, hx, rfl⟩
  simpa [mul_assoc] using h1

variable [Finite G]

theorem isComponentOf_le_or_commutator_eq_bot {K A N : Subgroup G} (hK : IsComponentOf K A)
    (hNA : N ≤ A) (hAN : A ≤ Subgroup.normalizer (N : Set G)) : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  have hNn : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  rcases CFSG.LocalCores.component_normal_subgroup (isComponent_subgroupOf_of_isComponentOf hK)
      hNn with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hNA] at h1

end Helpers

theorem bender1970_2_4
    {X : Type} [Group X] [Finite X] (hX : IsAStar X) {t : X}
    (ht : orderOf t = 2) {U : Subgroup X}
    (hUt : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (U : Set X))
    (hUF : generalizedFittingSubgroupOf U = U) :
    ⁅U, Subgroup.zpowers t⁆ ≤ generalizedFittingSubgroupOf (⊤ : Subgroup X) ∧
      (⁅U, Subgroup.zpowers t⁆.subgroupOf (generalizedFittingSubgroupOf ⊤)).IsSubnormal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := hX.1
  set Fst := generalizedFittingSubgroupOf (⊤ : Subgroup X) with hFst
  set F := CFSG.fittingSubgroup X with hF
  set FU := CFSG.fittingSubgroupOf U with hFU
  set EU := componentLayerOf U with hEU
  have htC : t ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htU : t ∈ Subgroup.normalizer (U : Set X) := hUt htC
  have htinv : BenderSuzuki.PFAppendixIII.IsInvolution t := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at ht
      omega
    · have h := pow_orderOf_eq_one t
      rwa [ht] at h
  have hcharN : ∀ (D : Subgroup U) [D.Characteristic], Subgroup.normalizer (U : Set X) ≤
      Subgroup.normalizer ((D.map U.subtype : Subgroup X) : Set X) := by
    intro D _ g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_map_of_characteristic hg hx, fun hx => ?_⟩
    have h1 := conj_mem_map_of_characteristic (Subgroup.inv_mem _ hg) hx
    simpa [mul_assoc] using h1
  have hFUU : FU ≤ U := Subgroup.map_subtype_le _
  have hFUN : Subgroup.normalizer (U : Set X) ≤ Subgroup.normalizer (FU : Set X) :=
    hcharN (CFSG.fittingSubgroup U)
  have hFUsolv : Group.IsSolvable FU := by
    have := CFSG.fittingSubgroupOf_isNilpotent U
    infer_instance
  have hEUFU : EU ≤ Subgroup.centralizer (FU : Set X) := by
    refine sSup_le fun K hK => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (isComponentOf_commutator_eq_bot_of_isSolvable hK hFUsolv hFUU
        (fun u hu => hFUN (Subgroup.le_normalizer hu)))
  have hFn : F.Normal := CFSG.fittingSubgroup_normal
  have hFUt : ⁅FU, Subgroup.zpowers t⁆ ≤ F := by
    rw [hFU, show _root_.CFSG.fittingSubgroupOf U = CFSG.GorensteinWalter.fittingSubgroupOf U from rfl,
      fittingSubgroupOf_eq_iSup_qCoreOf U, ← sSup_range]
    refine commutator_sSup_le _ _ _ (fun A hA => ?_)
      (fun A _ => (Subgroup.normalizer_eq_top_iff.mpr hFn).symm ▸ le_top)
    obtain ⟨q, rfl⟩ := hA
    set p : ℕ := (q : ℕ) with hpdef
    have hp : p.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have : Fact p.Prime := ⟨hp⟩
    have hAp : IsPGroup p (qCoreOf U p) := qCoreOf_isPGroup U p
    have hAN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (qCoreOf U p : Set X) :=
      hUt.trans (hcharN (pCore p U))
    by_cases hp2 : p = 2
    ·
      have hAC : qCoreOf U p ≤ Subgroup.centralizer ({t} : Set X) := by
        rw [hp2] at hAp hAN ⊢
        exact twoSubgroup_le_centralizer_involution_of_hasAbelianSylow _ hY hAp htinv (hAN htC)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      · exact bot_le
      · rw [centralizer_zpowers_eq']
        exact hAC
    · refine (bender1970_2_4_pGroup hX ht hp hp2 hAp hAN).trans ?_
      exact CFSG.LocalCores.fitting_characteristic.2.2 _ inferInstance
        (pCore_isPGroup (p := p) (G := X)).isNilpotent
  set 𝒦 := {K : Subgroup X | IsComponentOf K U ∧ ¬ K ≤ Subgroup.centralizer ({t} : Set X)}
    with h𝒦
  set W := sSup 𝒦 with hW
  have hWU : W ≤ U := sSup_le fun K hK => hK.1.1
  have hKW : ∀ K ∈ 𝒦, IsComponentOf K W := by
    intro K hK
    refine ⟨le_sSup hK, ?_, hK.1.2.2⟩
    convert hK.1.2.1.comap (Subgroup.inclusion hWU) using 1
    ext x
    exact Iff.rfl
  have hWE : componentLayerOf W = W :=
    le_antisymm (sSup_le fun K hK => hK.1) (sSup_le fun K hK => le_sSup (hKW K hK))
  have hconj𝒦 : ∀ c ∈ Subgroup.centralizer ({t} : Set X), ∀ K ∈ 𝒦,
      K.map (MulAut.conj c).toMonoidHom ∈ 𝒦 := by
    intro c hc K hK
    refine ⟨isComponentOf_map_conj hK.1 (hUt hc), fun h => hK.2 fun k hk => ?_⟩
    have h1 := h ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have hct' : c⁻¹ * t * c = t := by
      rw [mul_assoc, ← hct, ← mul_assoc, inv_mul_cancel, one_mul]
    calc k * t = k * (c⁻¹ * t * c) := by rw [hct']
      _ = c⁻¹ * ((c * k * c⁻¹) * t) * c := by group
      _ = c⁻¹ * (t * (c * k * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * t * c) * k := by group
      _ = t * k := by rw [hct']
  have hWt : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (W : Set X) :=
    fun c hc => mem_normalizer_sSup_of_map_mem (hconj𝒦 c hc)
      (hconj𝒦 c⁻¹ (Subgroup.inv_mem _ hc))
  have hWcomm : ⁅W, Subgroup.zpowers t⁆ = W := by
    refine le_antisymm (commutator_zpowers_le_of_mem_normalizer (hWt htC)) ?_
    refine sSup_le fun K hK => ?_
    have hVW : ⁅W, Subgroup.zpowers t⁆ ≤ W := commutator_zpowers_le_of_mem_normalizer (hWt htC)
    rcases isComponentOf_le_or_commutator_eq_bot (hKW K hK) hVW
        (Subgroup.normalizer_commutator_ge_left W _) with h | h
    · exact h
    · exfalso
      apply hK.2
      rw [← centralizer_zpowers_eq', ← Subgroup.commutator_eq_bot_iff_le_centralizer]
      apply CFSG.LocalCores.perfect_double_commutator (Group.isPerfect_def.mpr hK.1.2.2.2.1)
      rw [← le_bot_iff, Subgroup.commutator_comm]
      calc ⁅K, ⁅K, Subgroup.zpowers t⁆⁆ ≤ ⁅K, ⁅W, Subgroup.zpowers t⁆⁆ :=
            Subgroup.commutator_mono le_rfl (Subgroup.commutator_mono (le_sSup hK) le_rfl)
        _ = ⊥ := h
  obtain ⟨hWX, hcomp⟩ := bender1970_2_4_layer hX ht hWt hWE hWcomm
  set J := ⁅FU, Subgroup.zpowers t⁆ ⊔ W with hJ
  have hUeq : FU ⊔ EU = U := hUF
  have hFUtFU : ⁅FU, Subgroup.zpowers t⁆ ≤ FU := commutator_zpowers_le_of_mem_normalizer (hFUN htU)
  have hEUW : EU ≤ Subgroup.normalizer (W : Set X) := fun e he =>
    mem_normalizer_sSup fun K hK => componentLayerOf_le_normalizer_of_isComponentOf hK.1 he
  have hFUW : FU ≤ Subgroup.normalizer (W : Set X) := by
    intro f hf
    apply mem_normalizer_of_mem_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwE : w ∈ EU := (sSup_le fun K hK => le_sSup hK.1 : W ≤ EU) hw
    exact (Subgroup.mem_centralizer_iff.mp (hEUFU hwE) f hf).symm
  have hUJ : U ≤ Subgroup.normalizer (J : Set X) := by
    rw [← hUeq]
    refine sup_le (fun f hf => mem_normalizer_sup ?_ (hFUW hf))
      (fun e he => mem_normalizer_sup ?_ (hEUW he))
    · exact Subgroup.normalizer_commutator_ge_left FU _ hf
    · apply mem_normalizer_of_mem_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (hEUFU he) x (hFUtFU hx)
  have hFUJ : FU ≤ Subgroup.normalizer (J : Set X) := hFUU.trans hUJ
  have hEUU : EU ≤ U := (componentLayerOf_isNormalIn U).1
  have hEUJ : EU ≤ Subgroup.normalizer (J : Set X) := hEUU.trans hUJ
  have hUtJ : ⁅U, Subgroup.zpowers t⁆ ≤ J := by
    rw [← hUeq]
    refine commutator_sup_le_of_commutator_le_and_normalize FU EU _ J le_sup_left ?_ hFUJ hEUJ
    · refine commutator_sSup_le _ _ _ (fun K hK => ?_) (fun K hK => hK.1.trans hUJ)
      by_cases hKt : K ≤ Subgroup.centralizer ({t} : Set X)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
        · exact bot_le
        · rw [centralizer_zpowers_eq']
          exact hKt
      · calc ⁅K, Subgroup.zpowers t⁆ ≤ ⁅W, Subgroup.zpowers t⁆ :=
            Subgroup.commutator_mono (le_sSup ⟨hK, hKt⟩) le_rfl
          _ = W := hWcomm
          _ ≤ J := le_sup_right
  have hFit : CFSG.fittingSubgroupOf (⊤ : Subgroup X) = F :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations X
  have hFFst : F ≤ Fst := hFit ▸ le_sup_left
  have hEFst : componentLayerOf (⊤ : Subgroup X) ≤ Fst := le_sup_right
  have hEn : (componentLayerOf (⊤ : Subgroup X)).Normal :=
    normal_of_isNormalIn_top' (componentLayerOf_isNormalIn ⊤)
  have hA1 : ⁅FU, Subgroup.zpowers t⁆ ≤ Fst := hFUt.trans hFFst
  have hW1 : W ≤ Fst := hWX.trans hEFst
  have hJF : J ≤ Fst := sup_le hA1 hW1
  have hAsn : (⁅FU, Subgroup.zpowers t⁆.subgroupOf Fst).IsSubnormal :=
    isSubnormal_subgroupOf_trans hFUt
      (isSubnormal_of_nilpotent CFSG.fittingSubgroup_nilpotent _ hFUt)
      (inferInstance : (F.subgroupOf Fst).Normal).isSubnormal
  have hWsn : (W.subgroupOf Fst).IsSubnormal := by
    refine isSubnormal_subgroupOf_trans hWX ?_
      (inferInstance : ((componentLayerOf (⊤ : Subgroup X)).subgroupOf Fst).Normal).isSubnormal
    refine isSubnormal_subgroupOf_of_le_normalizer hWX fun e he => ?_
    exact mem_normalizer_sSup fun K hK =>
      componentLayerOf_top_le_normalizer (hcomp K (hKW K hK)) he
  have hJsn : (J.subgroupOf Fst).IsSubnormal := by
    rw [hJ, Subgroup.subgroupOf_sup hA1 hW1]
    exact CFSG.GroupTheory.isSubnormal_sup hAsn hWsn
  have hJU : J ≤ U := sup_le (hFUtFU.trans hFUU) hWU
  refine ⟨hUtJ.trans hJF, isSubnormal_subgroupOf_trans hUtJ ?_ hJsn⟩
  exact isSubnormal_subgroupOf_of_le_normalizer hUtJ
    (hJU.trans (Subgroup.normalizer_commutator_ge_left U _))

theorem bender1970_2_4_subgroup
    {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {t : G} (htH : t ∈ H) (ht : orderOf t = 2) {U : Subgroup G}
    (hUH : U ≤ H)
    (hUt : H ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hUF : generalizedFittingSubgroupOf U = U) :
    ⁅U, Subgroup.zpowers t⁆ ≤ generalizedFittingSubgroupOf H ∧
      (⁅U, Subgroup.zpowers t⁆.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal := by
  set t' : H := ⟨t, htH⟩ with ht'
  set U' := U.subgroupOf H with hU'
  have hU'F := generalizedFittingSubgroupOf_subgroupOf_eq_self hUH hUF
  have hU't : Subgroup.centralizer ({t'} : Set H) ≤ Subgroup.normalizer (U' : Set H) := by
    intro x hx
    rw [hU', ← Subgroup.subgroupOf_normalizer_eq hUH, Subgroup.mem_subgroupOf]
    apply hUt
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  obtain ⟨h1, h2⟩ := bender1970_2_4 hH (t := t') (by rw [Subgroup.orderOf_mk]; exact ht) hU't hU'F
  set V' := ⁅U', Subgroup.zpowers t'⁆ with hV'
  set FH' := generalizedFittingSubgroupOf (⊤ : Subgroup H) with hFH'
  have hVmap : V'.map H.subtype = ⁅U, Subgroup.zpowers t⁆ := by
    rw [hV', Subgroup.map_commutator, MonoidHom.map_zpowers, hU', Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hUH]
    rfl
  have hFmap : FH'.map H.subtype = generalizedFittingSubgroupOf H :=
    generalizedFittingSubgroupOf_subgroup_top_eq H
  refine ⟨?_, ?_⟩
  · rw [← hVmap, ← hFmap]
    exact Subgroup.map_mono h1
  · let e : FH' ≃* generalizedFittingSubgroupOf H :=
      (FH'.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hFmap)
    have h3 := h2.map (f := e.toMonoidHom) e.surjective
    convert h3 using 1
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hxV
      rw [← hVmap] at hxV
      obtain ⟨y, hyV, rfl⟩ := hxV
      exact ⟨⟨y, h1 hyV⟩, hyV, rfl⟩
    · rintro ⟨⟨y, hyF⟩, hyV, hyx⟩
      have hyx' : (y : G) = x := congrArg Subtype.val hyx
      show x ∈ ⁅U, Subgroup.zpowers t⁆
      rw [← hVmap, ← hyx']
      exact ⟨y, hyV, rfl⟩

end CFSG.Walter
