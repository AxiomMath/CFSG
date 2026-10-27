module

public import CFSG.RankThree.GF2n.Tim81.Basic
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.MS93.Sec2Gen
public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

namespace Hyp

private theorem eq_one_of_mem_two_and_coprime {P N : Subgroup G} (hP : IsPGroup 2 P)
    (hN : Nat.Coprime 2 (Nat.card N)) {x : G} (hxP : x ∈ P) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨x, hxP⟩
  have h1 : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left j hN) h2 h3)

private theorem not_isCyclic_of_mul_self {P : Subgroup G} (hexp : ∀ a ∈ P, a * a = 1)
    (h4 : 4 ≤ Nat.card P) : ¬ IsCyclic P := by
  intro hcyc
  have h := Monoid.exponent_dvd_of_forall_pow_eq_one (G := P) (n := 2) fun a =>
    Subtype.ext (by simpa [pow_two] using hexp a a.2)
  rw [IsCyclic.exponent_eq_card] at h
  have hle : Nat.card P ≤ 2 := Nat.le_of_dvd two_pos h
  exact (not_le_of_gt (Nat.lt_of_le_of_lt hle (by norm_num))) h4

theorem pPrimeCore_le_M (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    pPrimeCore 2 G ≤ M := by
  let O := pPrimeCore 2 G
  have hOcop : Nat.Coprime 2 (Nat.card O) :=
    pPrimeCore_coprime_card (p := 2) (G := G)
  have hVp : IsPGroup 2 V := h.isPGroup_V
  let _ : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => h.maxAb.prop.2.2.is_comm.comm a b }
  let _ : Fact (IsPGroup 2 V) := ⟨h.isPGroup_V⟩
  have hVcyc : ¬ IsCyclic V :=
    not_isCyclic_of_mul_self (P := V) (fun a ha => by simpa [pow_two] using h.elem.2 a ha) hV
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (pPrimeCore_normal (p := 2) (G := G))]
    exact le_top
  let _ : MulDistribMulAction V O :=
    MulDistribMulAction.compHom O (O.normalizerMonoidHom.comp (Subgroup.inclusion hVO))
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := O) (A := V) 2 hOcop hVcyc
  have hle : (⨆ (a : V) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) O) ≤ M.comap O.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hx' := hx
    rw [FixedPoints.mem_subgroup] at hx'
    have h2 : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) :=
      congrArg Subtype.val (hx' ⟨a, Subgroup.mem_zpowers a⟩)
    have hcomm : (x : G) * (a : G) = (a : G) * (x : G) := by
      calc (x : G) * (a : G)
          = ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by rw [h2]
        _ = (a : G) * (x : G) := by group
    have hxcent : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    exact h.centralizer_le_M a.2 (fun ha1 => ha (Subtype.ext ha1)) hxcent
  intro x hx
  have hx' : (⟨x, hx⟩ : O) ∈ (⨆ (a : V) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) O) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hle hx'

private theorem pPrimeCore_le_centralizer_pCore (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    pPrimeCore 2 G ≤ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) := by
  let O := pPrimeCore 2 G
  have hOM : O ≤ M := h.pPrimeCore_le_M hV
  have hOcop : Nat.Coprime 2 (Nat.card O) :=
    pPrimeCore_coprime_card (p := 2) (G := G)
  have hOsub : O.subgroupOf M ≤ pPrimeCore 2 M := by
    refine le_sSup ⟨?_, ?_⟩
    · exact (pPrimeCore_normal (p := 2) (G := G)).subgroupOf M
    · rw [show Nat.card (O.subgroupOf M) = Nat.card O from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv]
      exact hOcop
  have hInf : pPrimeCore 2 M ⊓ pCore 2 M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact eq_one_of_mem_two_and_coprime (pCore_isPGroup (p := 2) (G := M))
      (pPrimeCore_coprime_card (p := 2) (G := M)) hx.2 hx.1
  have hMcomm : ⁅pPrimeCore 2 M, pCore 2 M⁆ = ⊥ :=
    le_bot_iff.mp (hInf ▸ Subgroup.commutator_le_inf _ _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have hxP : (⟨x, hOM hx⟩ : M) ∈ pPrimeCore 2 M :=
    hOsub (Subgroup.mem_subgroupOf.mpr hx)
  have hxy'M : y' * ⟨x, hOM hx⟩ = ⟨x, hOM hx⟩ * y' :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMcomm hxP) y' hy'
  have hxy' : (y' : G) * x = x * (y' : G) := congrArg Subtype.val hxy'M
  simpa using hxy'

private theorem pPrimeCore_le_inSubgroup_pCore (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    pPrimeCore 2 G ≤ inSubgroup (pCore 2) M := by
  intro x hx
  have hxM : x ∈ M := h.pPrimeCore_le_M hV hx
  have hxcentM : (⟨x, hxM⟩ : M) ∈ Subgroup.centralizer (pCore 2 M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : (y : G) ∈ inSubgroup (pCore 2) M :=
      Subgroup.mem_map_of_mem M.subtype hy
    have hc := Subgroup.mem_centralizer_iff.mp
      (pPrimeCore_le_centralizer_pCore h hV hx) (y : G) hyG
    exact Subtype.ext (by simpa using hc)
  have hxcentG : (⟨x, hxM⟩ : M) ∈
      Subgroup.centralizer (generalizedFitting M : Set M) := by
    rw [h.fitting]
    exact hxcentM
  have hxfit : (⟨x, hxM⟩ : M) ∈ generalizedFitting M :=
    CFSG.centralizer_generalizedFitting_le M hxcentG
  have hxfit' : (⟨x, hxM⟩ : M) ∈ pCore 2 M := by
    rwa [← h.fitting]
  exact Subgroup.mem_map_of_mem M.subtype hxfit'

theorem pPrimeCore_eq_bot (h : Hyp M V) (hV : 4 ≤ Nat.card V) :
    pPrimeCore 2 G = ⊥ := by
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) :=
    pPrimeCore_coprime_card (p := 2) (G := G)
  rw [eq_bot_iff]
  intro x hx
  exact eq_one_of_mem_two_and_coprime ((inSubgroup_pCore_two M).1) hOcop
    (pPrimeCore_le_inSubgroup_pCore h hV hx) hx


end Hyp

end CFSG.RankThree.GF2n.Tim81

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem center_component_eq_bot {K : Subgroup G} (hF : fittingSubgroup G = ⊥)
    (hK : IsComponent K) : Subgroup.center K = ⊥ := by
  have h1 := (CFSG.LocalCores.center_component_le_center_layer hK).trans
    (CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := G))
  rw [hF, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  rw [Subgroup.ker_subtype] at h1
  exact le_bot_iff.mp h1

theorem component_isSimple {K : Subgroup G} (hF : fittingSubgroup G = ⊥)
    (hK : IsComponent K) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  have hc := center_component_eq_bot hF hK
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨(e.isSimpleGroup_congr).1 hs, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem components_commute_inf {K L : Subgroup G} (hF : fittingSubgroup G = ⊥)
    (hK : IsComponent K) (hL : IsComponent L) (hne : K ≠ L) :
    (∀ a ∈ K, ∀ b ∈ L, a * b = b * a) ∧ K ⊓ L = ⊥ := by
  have hcomm : ⁅K, L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hne
  have h1 : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  refine ⟨h1, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 g g.2 x hx.2)
  rw [center_component_eq_bot hF hK, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxZ)

theorem generalizedFitting_eq_layer_of_fittingSubgroup_eq_bot
    (hF : fittingSubgroup G = ⊥) : generalizedFitting G = layer G := by
  rw [generalizedFitting, hF, bot_sup_eq]

theorem generalizedFitting_simple_of_unique (hF : fittingSubgroup G = ⊥) {K : Subgroup G}
    (hK : IsComponent K) (huniq : ∀ L : Subgroup G, IsComponent L → L = K) :
    IsSimpleGroup (generalizedFitting G) ∧
      ∃ a b : generalizedFitting G, a * b ≠ b * a := by
  have hlayer : generalizedFitting G = K := by
    rw [generalizedFitting_eq_layer_of_fittingSubgroup_eq_bot hF]
    refine le_antisymm (sSup_le fun L hL => (huniq L hL).le)
      (CFSG.LocalCores.component_le_layer hK)
  obtain ⟨hs, hnab⟩ := component_isSimple hF hK
  rw [hlayer]
  exact ⟨hs, hnab⟩

theorem isComponent_conjSubgroup {K : Subgroup G} (hK : IsComponent K) (g : G) :
    IsComponent (conjSubgroup g K) := by
  simpa [conjSubgroup] using
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

end CFSG.RankThree.GF2n.Tim81


namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

private theorem map_conj_subgroupOf_eq_conjSubgroup {K M : Subgroup G} (hKM : K ≤ M) (m : M) :
    ((K.subgroupOf M).map (MulAut.conj m).toMonoidHom).map M.subtype =
      conjSubgroup (m : G) K := by
  rw [Subgroup.map_map]
  have hcomp : M.subtype.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (m : G)).toMonoidHom.comp M.subtype := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKM]
  rfl

private theorem conjugate_subgroupOf_le_normalizer {K M : Subgroup G} (hK : IsComponent K)
    (hKM : K ≤ M) (hF : fittingSubgroup G = ⊥) (g : M) :
    (K.subgroupOf M).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (K.subgroupOf M : Set M) := by
  let HM : Subgroup M := K.subgroupOf M
  change HM.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (HM : Set M)
  by_cases heq : conjSubgroup (g : G) K = K
  · have heqM : HM.map (MulAut.conj g).toMonoidHom = HM := by
      apply Subgroup.map_injective M.subtype_injective
      rw [map_conj_subgroupOf_eq_conjSubgroup hKM g, heq,
        Subgroup.map_subgroupOf_eq_of_le hKM]
    rw [heqM]
    exact Subgroup.le_normalizer
  · have hcommG := (components_commute_inf hF
      (isComponent_conjSubgroup hK (g : G)) hK heq).1
    have hcommM : ∀ a ∈ HM.map (MulAut.conj g).toMonoidHom, ∀ b ∈ HM,
        a * b = b * a := by
      intro a ha b hb
      have haG : (a : G) ∈ conjSubgroup (g : G) K := by
        rw [← map_conj_subgroupOf_eq_conjSubgroup hKM g]
        exact Subgroup.mem_map_of_mem M.subtype ha
      have hbG : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
      exact Subtype.ext (hcommG (a : G) haG (b : G) hbG)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hxy : x * y = y * x := hcommM x hx y hy
      have hval : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
          _ = y := by group
      rw [hval]
      exact hy
    · intro hy
      have hval : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      have hcomm_inv : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ :=
        hcommM x⁻¹ (Subgroup.inv_mem _ hx) (x * y * x⁻¹) hy
      have hmem : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        calc x⁻¹ * (x * y * x⁻¹) * x = (x * y * x⁻¹) * x⁻¹ * x := by rw [hcomm_inv]
          _ = x * y * x⁻¹ := by group
      rw [hval] at hmem
      rw [hmem]
      exact hy

theorem component_le_layer_of_le {K M : Subgroup G} (hK : IsComponent K) (hKM : K ≤ M)
    (hF : fittingSubgroup G = ⊥) :
    K ≤ (layer M).map M.subtype := by
  let HM : Subgroup M := K.subgroupOf M
  have hHMq : IsQuasisimple HM := by
    change IsQuasisimple (K.subgroupOf M)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKM).symm hK.1
  let L : Subgroup M := Subgroup.normalClosure (HM : Set M)
  have hHML : HM ≤ L := Subgroup.subset_normalClosure
  have hLnormal : L.Normal := inferInstance
  have hgen : ∀ m : M, HM.map (MulAut.conj m).toMonoidHom ≤
      Subgroup.normalizer (HM : Set M) := fun m =>
    conjugate_subgroupOf_le_normalizer hK hKM hF m
  have hHMnormal : (HM.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHML]
    change Subgroup.normalClosure (HM : Set M) ≤ Subgroup.normalizer (HM : Set M)
    rw [Quasithin.MS93.normalClosure_eq_iSup_map_conj]
    exact iSup_le hgen
  have hHMsub : HM.IsSubnormal :=
    Subgroup.IsSubnormal.trans hHML hHMnormal.isSubnormal hLnormal.isSubnormal
  have hHMcomp : IsComponent HM := ⟨hHMq, hHMsub⟩
  calc K = HM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hKM).symm
    _ ≤ (layer M).map M.subtype :=
        Subgroup.map_mono (CFSG.LocalCores.component_le_layer hHMcomp)

theorem false_of_isComponent_le_of_fitting_eq_pCore {K M : Subgroup G}
    (hFG : fittingSubgroup G = ⊥)
    (hF : generalizedFitting M = pCore 2 M) (hK : IsComponent K) (hKM : K ≤ M) : False := by
  have hKle : K ≤ (layer M).map M.subtype := component_le_layer_of_le hK hKM hFG
  have hlayer_le : layer M ≤ generalizedFitting M := le_sup_right
  have hKQ : K ≤ inSubgroup (pCore 2) M := by
    refine hKle.trans (Subgroup.map_mono ?_)
    rw [← hF]
    exact hlayer_le
  have hK2 : IsPGroup 2 K := (inSubgroup_pCore_two M).1.to_le hKQ
  let : Group.IsPerfect K := hK.1.1
  let : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  let : Group.IsSolvable K := @IsNilpotent.to_isSolvable _ _ hK2.isNilpotent
  exact (Group.IsPerfect.not_isSolvable K) inferInstance

private theorem mem_sup_iff_of_le_normalizer' {G : Type} [Group G] {K E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ K ⊔ E ↔ ∃ k ∈ K, ∃ e ∈ E, k * e = x := by
  let M : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ e ∈ E, k * e = x}
      one_mem' := ⟨1, K.one_mem, 1, E.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, e₁, he₁, rfl⟩ ⟨k₂, hk₂, e₂, he₂, rfl⟩
        refine ⟨k₁ * (e₁ * k₂ * e₁⁻¹), K.mul_mem hk₁
          ((Subgroup.mem_normalizer_iff.mp (hE he₁) k₂).mp hk₂), e₁ * e₂,
          E.mul_mem he₁ he₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨k, hk, e, he, rfl⟩
        refine ⟨e⁻¹ * k⁻¹ * e⁻¹⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hE (E.inv_mem he)) k⁻¹).mp (K.inv_mem hk),
          e⁻¹, E.inv_mem he, ?_⟩
        group }
  constructor
  · intro hx
    have hle : K ⊔ E ≤ M :=
      sup_le (fun k hk => ⟨k, hk, 1, E.one_mem, mul_one k⟩)
        (fun e he => ⟨1, K.one_mem, e, he, one_mul e⟩)
    exact hle hx
  · rintro ⟨k, hk, e, he, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he)

namespace Hyp

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem isMulCommutative_sup_of_le_centralizer {A B : Subgroup G}
    (hA : IsMulCommutative A) (hB : IsMulCommutative B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative ((A ⊔ B : Subgroup G)) := by
  have hAA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hAB' a ha b hb)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨a₁, ha₁, b₁, hb₁, hx⟩ := (mem_sup_iff_of_le_normalizer' hBN).mp x.2
  obtain ⟨a₂, ha₂, b₂, hb₂, hy⟩ := (mem_sup_iff_of_le_normalizer' hBN).mp y.2
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy]
  have hb₁a₂ : b₁ * a₂ = a₂ * b₁ := (hAB' a₂ ha₂ b₁ hb₁).symm
  have ha₁b₂ : a₁ * b₂ = b₂ * a₁ := hAB' a₁ ha₁ b₂ hb₂
  calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
    _ = a₁ * (a₂ * b₁) * b₂ := by rw [hb₁a₂]
    _ = (a₁ * a₂) * (b₁ * b₂) := by group
    _ = (a₂ * a₁) * (b₁ * b₂) := by rw [hAA a₁ ha₁ a₂ ha₂]
    _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hBB b₁ hb₁ b₂ hb₂]
    _ = a₂ * (a₁ * b₂) * b₁ := by group
    _ = a₂ * (b₂ * a₁) * b₁ := by rw [ha₁b₂]
    _ = a₂ * b₂ * (a₁ * b₁) := by group

theorem inf_V_eq_bot_of_ne (h : Hyp M V)
    (hFG : fittingSubgroup G = ⊥) {X Y : Subgroup G}
    (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    V ⊓ X = ⊥ := by
  by_contra hne
  haveI : Nontrivial ↥(V ⊓ X) := (Subgroup.nontrivial_iff_ne_bot (V ⊓ X)).mpr hne
  obtain ⟨x0, hx0⟩ := exists_ne (1 : ↥(V ⊓ X))
  set u : G := (x0 : G)
  have hu : u ∈ V ⊓ X := x0.2
  have hu1 : u ≠ 1 := fun h1 => hx0 (Subtype.ext h1)
  have huV : u ∈ V := (Subgroup.mem_inf.mp hu).1
  have huX : u ∈ X := (Subgroup.mem_inf.mp hu).2
  have hYv : Y ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ((components_commute_inf hFG hY hX (Ne.symm hXY)).1 y hy u huX).symm
  exact false_of_isComponent_le_of_fitting_eq_pCore hFG h.fitting hY
    (hYv.trans (h.centralizer_le_M huV hu1))

private theorem inter_isMulCommutative_of_inf_eq_bot (h : Hyp M V) {Z : Subgroup G}
    (hVZ : V ⊓ Z = ⊥) : IsMulCommutative ↥(Pc M V ⊓ Z) := by
  let PZ : Subgroup G := Pc M V ⊓ Z
  change IsMulCommutative (↥PZ)
  have hsq : ∀ x ∈ PZ, x * x = 1 := by
    intro x hx
    obtain ⟨hxP, hxZ⟩ := Subgroup.mem_inf.mp hx
    let xP : Pc M V := ⟨x, hxP⟩
    let _ : Fact (IsPGroup 2 (Pc M V)) := ⟨(inSubgroup_pCore_two M).1.to_le inf_le_left⟩
    have hfr : (xP : Pc M V) ^ 2 ∈ frattini (Pc M V) :=
      CFSG.pth_power_mem_frattini_of_isPGroup (R := Pc M V) (p := 2) xP
    have hfrG : x * x ∈ inSubgroup frattini (Pc M V) := by
      have hval : ((xP ^ 2 : Pc M V) : G) = x * x := by
        rw [SubgroupClass.coe_pow, pow_two]
      rw [← hval]
      exact Subgroup.mem_map_of_mem (Pc M V).subtype hfr
    have hxV : x * x ∈ V := h.frattini_Pc_le hfrG
    have hxZ' : x * x ∈ Z := Z.mul_mem hxZ hxZ
    have hbot : x * x ∈ V ⊓ Z := ⟨hxV, hxZ'⟩
    rw [hVZ] at hbot
    exact Subgroup.mem_bot.mp hbot
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha2 : (a : G) * (a : G) = 1 := hsq a a.2
  have hb2 : (b : G) * (b : G) = 1 := hsq b b.2
  have hab2 : ((a * b : PZ) : G) * ((a * b : PZ) : G) = 1 :=
    hsq (a * b) (mul_mem a.2 b.2)
  have hai : (a : G)⁻¹ = (a : G) := inv_eq_of_mul_eq_one_right ha2
  have hbi : (b : G)⁻¹ = (b : G) := inv_eq_of_mul_eq_one_right hb2
  calc (a : G) * (b : G) = ((a * b : PZ) : G) := rfl
    _ = (((a * b : PZ) : G))⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev (a : G) (b : G)
    _ = (b : G) * (a : G) := by rw [hai, hbi]

private theorem closure_orbit_isMulCommutative (h : Hyp M V)
    (hF : fittingSubgroup G = ⊥) {X Y : Subgroup G} (hX : IsComponent X)
    (hY : IsComponent Y) (hXY : X ≠ Y) :
    IsMulCommutative (Subgroup.closure {x : G | ∃ Z : Subgroup G,
      (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z}) := by
  let S : Set G := {x : G | ∃ Z : Subgroup G,
    (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z}
  change IsMulCommutative (Subgroup.closure S)
  have hVZ : ∀ Z : Subgroup G, IsComponent Z → V ⊓ Z = ⊥ := by
    intro Z hZ
    by_cases hZX : Z = X
    · subst hZX
      exact inf_V_eq_bot_of_ne h hF hX hY hXY
    · exact inf_V_eq_bot_of_ne h hF hZ hX hZX
  have hpair : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb
    obtain ⟨Za, ⟨hZa, _⟩, haZa⟩ := ha
    obtain ⟨Zb, ⟨hZb, _⟩, hbZb⟩ := hb
    by_cases hZab : Za = Zb
    · subst hZab
      exact congrArg Subtype.val
        ((inter_isMulCommutative_of_inf_eq_bot h (hVZ Za hZa)).is_comm.comm
          ⟨a, haZa⟩ ⟨b, hbZb⟩)
    · exact (components_commute_inf hF hZa hZb hZab).1 a
        (Subgroup.mem_inf.mp haZa).2 b (Subgroup.mem_inf.mp hbZb).2
  have hpair' : S.Pairwise (fun a b => Commute a b) := by
    intro a ha b hb _
    exact hpair a ha b hb
  exact Subgroup.isMulCommutative_closure hpair'

private theorem closure_orbit_le_Pc {X : Subgroup G} :
    Subgroup.closure {x : G | ∃ Z : Subgroup G,
      (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z} ≤
      Pc M V := by
  let S : Set G := {x : G | ∃ Z : Subgroup G,
    (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z}
  change Subgroup.closure S ≤ Pc M V
  refine (Subgroup.closure_le (K := Pc M V)).2 ?_
  intro x hx
  simp only [S, Set.mem_setOf_eq] at hx
  obtain ⟨Z, ⟨_, _⟩, hxZ⟩ := hx
  exact (Subgroup.mem_inf.mp hxZ).1

private theorem le_normalizer_closure_orbit (h : Hyp M V) {X : Subgroup G} :
    M ≤ Subgroup.normalizer (Subgroup.closure {x : G | ∃ Z : Subgroup G,
      (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z} : Set G) := by
  let S : Set G := {x : G | ∃ Z : Subgroup G,
    (IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X) ∧ x ∈ Pc M V ⊓ Z}
  change M ≤ Subgroup.normalizer (Subgroup.closure S : Set G)
  refine Quasithin.MS93.le_normalizer_of_map_conj_le fun m hm => ?_
  change (Subgroup.closure S).map (MulAut.conj m).toMonoidHom ≤ Subgroup.closure S
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := Subgroup.closure S)).2 ?_
  rintro x ⟨y, hy, rfl⟩
  have hmemS : (MulAut.conj m).toMonoidHom y ∈ S := by
    simp only [S, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨Z, hZ, hyZ⟩ := hy
    refine ⟨conjSubgroup (m : G) Z, ?_, ?_⟩
    · obtain ⟨hZcomp, k, hk⟩ := hZ
      refine ⟨isComponent_conjSubgroup hZcomp (m : G), ?_⟩
      refine ⟨⟨m, hm⟩ * k, ?_⟩
      rw [hk, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      congr 1
    · constructor
      · have hxin : (MulAut.conj m) y ∈ conjSubgroup (m : G) (Pc M V) :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp hyZ).1
        have hPeq : conjSubgroup (m : G) (Pc M V) = Pc M V := by
          simpa [conjSubgroup] using
            Quasithin.MS93.map_conj_eq_of_mem_normalizer (h.le_normalizer_Pc hm)
        rwa [hPeq] at hxin
      · exact Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom
          (Subgroup.mem_inf.mp hyZ).2
  exact Subgroup.subset_closure hmemS

private theorem sup_isMulCommutative_normal_of_le_Pc (h : Hyp M V) {W : Subgroup G}
    (hWab : IsMulCommutative W) (hWleP : W ≤ Pc M V)
    (hWnormal : M ≤ Subgroup.normalizer (W : Set G)) :
    V ⊔ W ≤ M ∧ M ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ∧
      IsMulCommutative ↥(V ⊔ W) := by
  have hVcentralW : V ≤ Subgroup.centralizer (W : Set G) := by
    rw [← h.centralizer_Pc]
    exact Subgroup.centralizer_le (show (W : Set G) ⊆ (Pc M V : Set G) from hWleP)
  have hVWab : IsMulCommutative ((V ⊔ W : Subgroup G)) :=
    isMulCommutative_sup_of_le_centralizer h.maxAb.prop.2.2 hWab hVcentralW
  have hVWleM : V ⊔ W ≤ M := by
    refine sup_le h.le_M ?_
    exact hWleP.trans h.Pc_le_M
  have hVWnormal : M ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    change Subgroup.map (MulAut.conj m).toMonoidHom V ⊔
      Subgroup.map (MulAut.conj m).toMonoidHom W = V ⊔ W
    have hVmap : Subgroup.map (MulAut.conj m).toMonoidHom V = V :=
      Quasithin.MS93.map_conj_eq_of_mem_normalizer (by simpa [h.normalizer_eq] using hm)
    have hWmap : Subgroup.map (MulAut.conj m).toMonoidHom W = W :=
      Quasithin.MS93.map_conj_eq_of_mem_normalizer (hWnormal hm)
    rw [hVmap, hWmap]
  exact ⟨hVWleM, hVWnormal, hVWab⟩

theorem inf_Pc_eq_bot_of_ne (h : Hyp M V)
    (hFG : fittingSubgroup G = ⊥) {X Y : Subgroup G}
    (hX : IsComponent X) (hY : IsComponent Y) (hXY : X ≠ Y) :
    Pc M V ⊓ X = ⊥ := by
  let P : Subgroup G := Pc M V
  let Orbit : Set (Subgroup G) :=
    {Z : Subgroup G | IsComponent Z ∧ ∃ m : M, Z = conjSubgroup (m : G) X}
  let S : Set G := {x : G | ∃ Z : Subgroup G, Z ∈ Orbit ∧
    x ∈ (((P : Subgroup G) ⊓ Z) : Set G)}
  let W : Subgroup G := Subgroup.closure S
  have hXorbit : X ∈ Orbit := ⟨hX, ⟨1, by simp [conjSubgroup_one]⟩⟩
  have hVZ : ∀ Z ∈ Orbit, V ⊓ Z = ⊥ := by
    intro Z hZ
    by_cases hZX : Z = X
    · subst hZX
      exact inf_V_eq_bot_of_ne h hFG hX hY hXY
    · exact inf_V_eq_bot_of_ne h hFG hZ.1 hX hZX
  have hWab : IsMulCommutative W :=
    closure_orbit_isMulCommutative h hFG hX hY hXY
  have hWleP : W ≤ P := closure_orbit_le_Pc
  have hWnormal : M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_closure_orbit h
  have hsup := sup_isMulCommutative_normal_of_le_Pc h hWab hWleP hWnormal
  have hle : V ⊔ W ≤ V := h.maxAb.le_of_ge hsup le_sup_left
  have hWleV : W ≤ V := le_sup_right.trans hle
  have hPX : ((P : Subgroup G) ⊓ X) ≤ V := by
    have h1 : ((P : Subgroup G) ⊓ X) ≤ W := by
      change ((P : Subgroup G) ⊓ X) ≤ Subgroup.closure S
      intro x hx
      apply Subgroup.subset_closure
      simp only [S, Set.mem_setOf_eq]
      exact ⟨X, hXorbit, hx⟩
    exact h1.trans hWleV
  rw [eq_bot_iff]
  exact (le_inf hPX inf_le_right).trans_eq (hVZ X hXorbit)

end Hyp

end CFSG.RankThree.GF2n.Tim81

