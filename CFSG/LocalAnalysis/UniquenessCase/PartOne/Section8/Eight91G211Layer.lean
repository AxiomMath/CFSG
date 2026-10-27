module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

private theorem g211_isComponentOf_top_of_isComponent {J0 : Type} [Group J0] {K : Subgroup J0}
    (hK : CFSG.IsComponent K) : IsComponentOf K ⊤ :=
  ⟨le_top, CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hK.2,
    hK.1.1.commutator_eq_top, hK.1.2.1⟩

private theorem g211_isComponent_of_isComponentOf_top {G : Type*} [Group G] {L : Subgroup G}
    (h : IsComponentOf L ⊤) : CFSG.IsComponent L :=
  ⟨⟨⟨h.2.2.1⟩, h.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L h.2.2⟩,
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h.2.1
      Subgroup.IsSubnormal.top⟩

private theorem mem_centralizer_layer_of_forall_component {J0 : Type} [Group J0]
    {x : J0} (hx : ∀ K : Subgroup J0, IsComponentOf K ⊤ → x ∈ centralizer (K : Set J0)) :
    x ∈ centralizer (CFSG.layer J0 : Set J0) := by
  rw [CFSG.layer.eq_sSup]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hle : sSup {K : Subgroup J0 | CFSG.IsComponent K} ≤ centralizer ({x} : Set J0) := by
    refine sSup_le fun K hK => ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hx K (g211_isComponentOf_top_of_isComponent hK)) z hz
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

private theorem le_centralizer_of_component_le_of_solvable {J0 : Type} [Group J0] [Finite J0]
    {M0 X0 J : Subgroup J0} (hXM : X0 ≤ M0) (hXn : (X0.subgroupOf M0).Normal)
    (hXs : IsSolvable ↥X0) (hJ : IsComponentOf J ⊤) (hJM : J ≤ M0) :
    X0 ≤ centralizer (J : Set J0) := by
  have hcomp : IsComponentOf (J.subgroupOf M0) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hJ hJM
  have : Group.IsSolvable ↥(X0.subgroupOf M0) := by
    have : Group.IsSolvable ↥X0 := hXs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXM).injective
  have : (X0.subgroupOf M0).Normal := hXn
  have hsub : IsSubnormal (X0.subgroupOf M0) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hXn.isSubnormal
  have hcomm : ⁅J.subgroupOf M0, X0.subgroupOf M0⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
      (J.subgroupOf M0) (X0.subgroupOf M0) hcomp hsub
  have hmap := congrArg (Subgroup.map M0.subtype) hcomm
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJM,
    Subgroup.map_subgroupOf_eq_of_le hXM, Subgroup.map_bot] at hmap
  rw [Subgroup.commutator_comm] at hmap
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmap

private theorem mul_mem_of_inverted {G : Type*} [Group G] {N F : Subgroup G} {t f k : G}
    (hf : f ∈ F) (hk : k ∈ N) (hFN : ∀ a ∈ F, ∀ b ∈ N, a * b = b * a)
    (htF : ∀ a ∈ F, t * a = a * t) (htN : ∀ b ∈ N, t * b * t⁻¹ ∈ N)
    (h3 : (f * k) ^ 3 = 1) (hinv : t * (f * k) * t⁻¹ = (f * k)⁻¹) : f * k ∈ N := by
  let e : G := f * k
  have h3e : e ^ 3 = 1 := h3
  have hinve : t * e * t⁻¹ = e⁻¹ := hinv
  have h4 : e ^ 4 = e := by
    calc e ^ 4 = e ^ 3 * e := by group
      _ = e := by rw [h3e, one_mul]
  have hA : t * e ^ 2 * t⁻¹ = (e ^ 2)⁻¹ := by
    calc t * e ^ 2 * t⁻¹ = (t * e * t⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
      _ = (e⁻¹) ^ 2 := by rw [hinve]
      _ = (e ^ 2)⁻¹ := by rw [inv_pow]
  have hB : t * (e ^ 2)⁻¹ * t⁻¹ = e ^ 2 := by
    simpa [mul_inv_rev, mul_assoc] using congrArg Inv.inv hA
  have he2 : e ^ 2 = f ^ 2 * k ^ 2 := by
    rw [show e = f * k from rfl]
    calc (f * k) ^ 2 = f * (k * f) * k := by rw [pow_two]; group
      _ = f * (f * k) * k := by rw [← hFN f hf k hk]
      _ = f ^ 2 * k ^ 2 := by rw [pow_two, pow_two]; group
  have he2inv : (e ^ 2)⁻¹ = (k ^ 2)⁻¹ * (f ^ 2)⁻¹ := by
    rw [he2]
    group
  have htf2 : t * (f ^ 2)⁻¹ = (f ^ 2)⁻¹ * t := by
    have htf : Commute t f := htF f hf
    exact (htf.pow_right 2).inv_right.eq
  have htinv : t * (e ^ 2)⁻¹ * t⁻¹ = (t * (k ^ 2)⁻¹ * t⁻¹) * (f ^ 2)⁻¹ := by
    rw [he2inv]
    calc t * ((k ^ 2)⁻¹ * (f ^ 2)⁻¹) * t⁻¹
        = (t * (k ^ 2)⁻¹ * t⁻¹) * (t * (f ^ 2)⁻¹ * t⁻¹) := by group
      _ = (t * (k ^ 2)⁻¹ * t⁻¹) * (f ^ 2)⁻¹ := by rw [htf2]; group
  have hC : e = e ^ 2 * (t * (e ^ 2)⁻¹ * t⁻¹) := by
    rw [hB]
    calc e = e ^ 4 := h4.symm
      _ = e ^ 2 * e ^ 2 := by group
  have hu : t * (k ^ 2)⁻¹ * t⁻¹ ∈ N := htN _ (N.inv_mem (N.pow_mem hk 2))
  have hv : k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹) ∈ N := N.mul_mem (N.pow_mem hk 2) hu
  have hcommf : f ^ 2 * (k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹)) =
      (k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹)) * f ^ 2 :=
    hFN _ (F.pow_mem hf 2) _ hv
  have hkey : e = k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹) := by
    calc e = e ^ 2 * (t * (e ^ 2)⁻¹ * t⁻¹) := hC
      _ = (f ^ 2 * k ^ 2) * ((t * (k ^ 2)⁻¹ * t⁻¹) * (f ^ 2)⁻¹) := by
          rw [htinv, he2]
      _ = (f ^ 2 * (k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹))) * (f ^ 2)⁻¹ := by group
      _ = ((k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹)) * f ^ 2) * (f ^ 2)⁻¹ := by rw [hcommf]
      _ = k ^ 2 * (t * (k ^ 2)⁻¹ * t⁻¹) := by group
  change e ∈ N
  rw [hkey]
  exact hv

private theorem not_le_centralizer_map_conj_of_mem_normalizer {J0 : Type} [Group J0]
    {E J : Subgroup J0} {g : J0}
    (hg : g ∈ normalizer (E : Set J0)) (h : ¬ E ≤ centralizer (J : Set J0)) :
    ¬ E ≤ centralizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup J0) : Set J0) := by
  intro hconj
  apply h
  intro e he
  have hge : g * e * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg e).mp he
  have hx : g * e * g⁻¹ ∈
      centralizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup J0) : Set J0) := hconj hge
  rw [Subgroup.mem_centralizer_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hmem : (MulAut.conj g) j ∈ J.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hj
  have hy := hx ((MulAut.conj g) j) hmem
  rw [MulAut.conj_apply] at hy
  have hy' : g * (j * e) * g⁻¹ = g * (e * j) * g⁻¹ := by
    calc g * (j * e) * g⁻¹ = (g * j * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (g * e * g⁻¹) * (g * j * g⁻¹) := hy
      _ = g * (e * j) * g⁻¹ := by group
  calc j * e = g⁻¹ * (g * (j * e) * g⁻¹) * g := by group
    _ = g⁻¹ * (g * (e * j) * g⁻¹) * g := by rw [hy']
    _ = e * j := by group

private theorem g211_pCore_le_of_isSylowOf {J0 : Type} [Group J0] [Finite J0]
    {P : Subgroup J0} (hP : IsSylowOf 3 P ⊤) : CFSG.pCore 3 J0 ≤ P := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have : (CFSG.pCore 3 J0).Normal := CFSG.pCore_normal
  have hP3 : IsPGroup 3 ↥(P ⊔ CFSG.pCore 3 J0) :=
    IsPGroup.to_sup_of_normal_right (H := P) (K := CFSG.pCore 3 J0)
      hP.isPGroup CFSG.pCore_isPGroup
  exact le_sup_right.trans (hP.eq_of_le le_sup_left le_top hP3).le

theorem centralizes_pCore_of_inf_eq_bot {J0 : Type} [Group J0] [Finite J0]
    {P M0 X0 E : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0)
    (hEF : E ⊓ CFSG.pCore 3 J0 = ⊥) :
    X0 ≤ centralizer (CFSG.pCore 3 J0 : Set J0) := by
  have : (CFSG.pCore 3 J0).Normal := CFSG.pCore_normal
  have hFP : CFSG.pCore 3 J0 ≤ P := g211_pCore_le_of_isSylowOf hP
  have hFM : CFSG.pCore 3 J0 ≤ M0 := hFP.trans hPM
  have h1 : ⁅X0, CFSG.pCore 3 J0⁆ ≤ CFSG.pCore 3 J0 :=
    Subgroup.commutator_le_right _ _
  have : (X0.subgroupOf M0).Normal := hXn
  have h2 : ⁅X0, CFSG.pCore 3 J0⁆ ≤ X0 := by
    have hcomm : ⁅X0.subgroupOf M0, (CFSG.pCore 3 J0).subgroupOf M0⁆ ≤
        X0.subgroupOf M0 := Subgroup.commutator_le_left _ _
    have hmap := Subgroup.map_mono hcomm (f := M0.subtype)
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXM,
      Subgroup.map_subgroupOf_eq_of_le hFM] at hmap
    exact hmap
  have hbot : ⁅X0, CFSG.pCore 3 J0⁆ = ⊥ := by
    refine le_antisymm ?_ bot_le
    have hleE : X0 ⊓ CFSG.pCore 3 J0 ≤ E := by
      rw [hE]
      exact le_inf (inf_le_right.trans hFP) inf_le_left
    calc ⁅X0, CFSG.pCore 3 J0⁆ ≤ X0 ⊓ CFSG.pCore 3 J0 := le_inf h2 h1
      _ ≤ E ⊓ CFSG.pCore 3 J0 := le_inf hleE inf_le_right
      _ = ⊥ := hEF
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

private theorem layer_eq_sup_inf_centralizer {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hJ : CFSG.IsComponent J) :
    CFSG.layer G = J ⊔ (CFSG.layer G ⊓ Subgroup.centralizer (J : Set G)) := by
  have hothers : sSup {T : Subgroup G | CFSG.IsComponent T ∧ T ≠ J} ≤
      CFSG.layer G ⊓ Subgroup.centralizer (J : Set G) := by
    refine le_inf (sSup_le ?_) (CFSG.WholeGroup.layer_eq_sup_others hJ).1
    exact fun T hT => CFSG.LocalCores.component_le_layer hT.1
  refine le_antisymm ?_ (sup_le (CFSG.LocalCores.component_le_layer hJ) inf_le_left)
  calc CFSG.layer G = J ⊔ sSup {T : Subgroup G | CFSG.IsComponent T ∧ T ≠ J} :=
        (CFSG.WholeGroup.layer_eq_sup_others hJ).2
    _ ≤ J ⊔ (CFSG.layer G ⊓ Subgroup.centralizer (J : Set G)) := sup_le_sup_left hothers J

private theorem layer_le_normalizer_inf_centralizer {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hJ : CFSG.IsComponent J) :
    CFSG.layer G ≤ Subgroup.normalizer
      (CFSG.layer G ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) := by
  have hJK : J ≤ CFSG.layer G := (CFSG.LocalCores.components_normal_in_layer hJ).1
  have hJnorm : CFSG.layer G ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mp
      (CFSG.LocalCores.components_normal_in_layer hJ).2
  have hCJ : CFSG.layer G ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set G)) := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (J : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (J : Set G))
    exact hJnorm.trans h
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, hCJ hx⟩

private theorem map_prod_sylow_eq_sup {G : Type*} [Group G]
    {p : ℕ} {J C : Subgroup G}
    (hcomm : ∀ a ∈ J, ∀ b ∈ C, a * b = b * a)
    (SJ : Sylow p J) (SC : Sylow p C) :
    (((SJ : Subgroup J).prod (SC : Subgroup C)).map
        ((J.subtype.codRestrict (J ⊔ C) (fun x => Subgroup.mem_sup_left x.2)).noncommCoprod
          (C.subtype.codRestrict (J ⊔ C) (fun x => Subgroup.mem_sup_right x.2))
          (fun a b => by
            apply Subtype.ext
            exact hcomm a a.2 b b.2))).map (J ⊔ C).subtype
      = (SJ : Subgroup J).map J.subtype ⊔ (SC : Subgroup C).map C.subtype := by
  let fJ : J →* (J ⊔ C : Subgroup G) :=
    J.subtype.codRestrict (J ⊔ C) fun x => Subgroup.mem_sup_left x.2
  let fC : C →* (J ⊔ C : Subgroup G) :=
    C.subtype.codRestrict (J ⊔ C) fun x => Subgroup.mem_sup_right x.2
  have hcomm_hom : ∀ a : J, ∀ b : C, fJ a * fC b = fC b * fJ a := by
    intro a b
    apply Subtype.ext
    exact hcomm a a.2 b b.2
  let π : J × C →* (J ⊔ C : Subgroup G) := fJ.noncommCoprod fC hcomm_hom
  change (((SJ : Subgroup J).prod (SC : Subgroup C)).map π).map (J ⊔ C).subtype =
    (SJ : Subgroup J).map J.subtype ⊔ (SC : Subgroup C).map C.subtype
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨a, b⟩ := s
    have ha : a ∈ SJ := (Subgroup.mem_prod.mp hs).1
    have hb : b ∈ SC := (Subgroup.mem_prod.mp hs).2
    change (a : G) * (b : G) ∈ (SJ : Subgroup J).map J.subtype ⊔ (SC : Subgroup C).map C.subtype
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem J.subtype ha)
      (Subgroup.mem_map_of_mem C.subtype hb)
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨π (a, 1), Subgroup.mem_map.mpr ?_, ?_⟩
      · exact ⟨(a, 1), Subgroup.mem_prod.mpr ⟨ha, (SC : Subgroup C).one_mem⟩, rfl⟩
      · change (a : G) * 1 = (a : G)
        exact mul_one (a : G)
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨π (1, b), Subgroup.mem_map.mpr ?_, ?_⟩
      · exact ⟨(1, b), Subgroup.mem_prod.mpr ⟨(SJ : Subgroup J).one_mem, hb⟩, rfl⟩
      · change (1 : G) * (b : G) = (b : G)
        exact one_mul (b : G)

private theorem isSylowOf_sup_of_isSylowOf_of_commute {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {J C A B : Subgroup G}
    (hcomm : ∀ a ∈ J, ∀ b ∈ C, a * b = b * a)
    (hA : IsSylowOf p A J) (hB : IsSylowOf p B C) :
    IsSylowOf p (A ⊔ B) (J ⊔ C) := by
  classical
  obtain ⟨SJ, hSJ⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨SC, hSC⟩ := hB.exists_sylow_eq_subgroupOf
  have hS_pgroup : IsPGroup p ((SJ : Subgroup J).prod (SC : Subgroup C)) := by
    have hcard : Nat.card ((SJ : Subgroup J).prod (SC : Subgroup C)) =
        Nat.card (SJ : Subgroup J) * Nat.card (SC : Subgroup C) := by
      calc Nat.card ((SJ : Subgroup J).prod (SC : Subgroup C))
          = Nat.card (↥(SJ : Subgroup J) × ↥(SC : Subgroup C)) :=
            Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
        _ = Nat.card (SJ : Subgroup J) * Nat.card (SC : Subgroup C) := Nat.card_prod _ _
    obtain ⟨m, hm⟩ := SJ.isPGroup'.exists_card_eq
    obtain ⟨n, hn⟩ := SC.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := m + n) ?_
    rw [hcard, hm, hn, pow_add]
  have hS_index : ¬ p ∣ ((SJ : Subgroup J).prod (SC : Subgroup C)).index := by
    rw [Subgroup.index_prod]
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h' | h'
    · exact SJ.not_dvd_index h'
    · exact SC.not_dvd_index h'
  let Ssyl : Sylow p (J × C) := hS_pgroup.toSylow hS_index
  let fJ : J →* (J ⊔ C : Subgroup G) :=
    J.subtype.codRestrict (J ⊔ C) fun x => Subgroup.mem_sup_left x.2
  let fC : C →* (J ⊔ C : Subgroup G) :=
    C.subtype.codRestrict (J ⊔ C) fun x => Subgroup.mem_sup_right x.2
  have hcomm_hom : ∀ a : J, ∀ b : C, fJ a * fC b = fC b * fJ a := by
    intro a b
    apply Subtype.ext
    exact hcomm a a.2 b b.2
  let π : J × C →* (J ⊔ C : Subgroup G) := fJ.noncommCoprod fC hcomm_hom
  have hπ_surj : Function.Surjective π := by
    intro y
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm y.2
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    simp only [π, fJ, fC]
    exact hab
  have hcoe : ((Ssyl.mapSurjective hπ_surj : Sylow p (J ⊔ C : Subgroup G)) :
      Subgroup (J ⊔ C : Subgroup G)) =
      ((SJ : Subgroup J).prod (SC : Subgroup C)).map π := by
    rw [Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  refine ⟨Ssyl.mapSurjective hπ_surj, ?_⟩
  rw [hcoe, map_prod_sylow_eq_sup hcomm SJ SC, hSJ, hSC,
    Subgroup.map_subgroupOf_eq_of_le hA.le, Subgroup.map_subgroupOf_eq_of_le hB.le]

theorem layer_decomp_of_isSylow {J0 : Type} [Group J0] [Finite J0] {P J : Subgroup J0}
    (hP : IsSylowOf 3 P ⊤) (hJ : IsComponentOf J ⊤) {e : J0}
    (he : e ∈ P ⊓ CFSG.layer J0) :
    ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)), e = q * r := by
  classical
  let K : Subgroup J0 := CFSG.layer J0
  let C : Subgroup J0 := K ⊓ Subgroup.centralizer (J : Set J0)
  have hJc : CFSG.IsComponent J := g211_isComponent_of_isComponentOf_top hJ
  have hJK : J ≤ K := (CFSG.LocalCores.components_normal_in_layer hJc).1
  have hJnorm : K ≤ Subgroup.normalizer (J : Set J0) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mp
      (CFSG.LocalCores.components_normal_in_layer hJc).2
  have hKn : K.Normal := by
    have h : K.Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hCnorm : K ≤ Subgroup.normalizer (C : Set J0) :=
    layer_le_normalizer_inf_centralizer hJc
  have hPK : IsSylowOf 3 (P ⊓ K) K :=
    hP.inf_of_le_normalizer (K := ⊤) (N := K) le_top Subgroup.le_normalizer_of_normal
  have hA : IsSylowOf 3 (P ⊓ J) J := by
    have h := hPK.inf_of_le_normalizer hJK hJnorm
    simpa [inf_assoc, inf_eq_right.mpr hJK] using h
  have hB : IsSylowOf 3 (P ⊓ C) C := by
    have h := hPK.inf_of_le_normalizer (show C ≤ K from inf_le_left) hCnorm
    simpa [C, inf_assoc] using h
  have hK_eq : K = J ⊔ C := layer_eq_sup_inf_centralizer hJc
  have hcomm : ∀ a ∈ J, ∀ b ∈ C, a * b = b * a := by
    rintro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 a ha
  have hSyl : IsSylowOf 3 ((P ⊓ J) ⊔ (P ⊓ C)) (J ⊔ C) :=
    isSylowOf_sup_of_isSylowOf_of_commute hcomm hA hB
  have hSyl' : IsSylowOf 3 ((P ⊓ J) ⊔ (P ⊓ C)) K := hK_eq ▸ hSyl
  have hABle : (P ⊓ J) ⊔ (P ⊓ C) ≤ P ⊓ K :=
    sup_le (le_inf inf_le_left (inf_le_right.trans hJK))
      (le_inf inf_le_left (inf_le_right.trans inf_le_left))
  have hKeq : P ⊓ K = (P ⊓ J) ⊔ (P ⊓ C) :=
    hSyl'.eq_of_le hABle inf_le_right hPK.isPGroup
  have he' : e ∈ (P ⊓ J) ⊔ (P ⊓ C) := by
    rw [← hKeq]
    exact he
  obtain ⟨q, hq, r, hr, hqr⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (show ∀ a ∈ P ⊓ J, ∀ b ∈ P ⊓ C, a * b = b * a from fun a ha b hb =>
        Subgroup.mem_centralizer_iff.mp hb.2.2 a ha.2) he'
  exact ⟨q, hq, r, ⟨hr.1, hr.2.1, hr.2.2⟩, hqr.symm⟩

theorem component_alt_of_solvable_normal {J0 : Type} [Group J0] [Finite J0]
    {M0 X0 E J : Subgroup J0} (hXM : X0 ≤ M0) (hXn : (X0.subgroupOf M0).Normal)
    (hXs : IsSolvable ↥X0) (hEX : E ≤ X0)
    (hC : ∀ a ∈ E, a ≠ 1 → centralizer ({a} : Set J0) ≤ M0) (hJ : IsComponentOf J ⊤) :
    E ≤ centralizer (J : Set J0) ∨ E ⊓ centralizer (J : Set J0) = ⊥ := by
  by_cases hbot : E ⊓ centralizer (J : Set J0) = ⊥
  · exact Or.inr hbot
  · left
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have haE : (a : J0) ∈ E := (Subgroup.mem_inf.mp a.2).1
    have haC : (a : J0) ∈ centralizer (J : Set J0) := (Subgroup.mem_inf.mp a.2).2
    have ha1 : (a : J0) ≠ 1 := fun h => ha (Subtype.ext h)
    have hJM : J ≤ M0 := by
      refine (le_trans ?_ (hC (a : J0) haE ha1))
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp haC x hx
    exact hEX.trans (le_centralizer_of_component_le_of_solvable hXM hXn hXs hJ hJM)

private theorem le_generalizedFitting_of_irreducible {J0 : Type} [Group J0]
    {P M0 X0 E T : Subgroup J0} (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hTN : T ≤ normalizer (E : Set J0))
    (hIrr : ∀ W : Subgroup J0, W ≤ E → T ≤ normalizer (W : Set J0) → W = ⊥ ∨ W = E)
    (hGrossC : ∀ c ∈ P, c ^ 3 = 1 → (∀ u ∈ P ⊓ CFSG.generalizedFitting J0, c * u = u * c) →
      c ∈ CFSG.generalizedFitting J0) :
    E ≤ CFSG.generalizedFitting J0 := by
  have hFchar : (CFSG.generalizedFitting J0).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := J0)).1
  have hFnorm : (CFSG.generalizedFitting J0).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := J0)).2
  have hTF : T ≤ normalizer (CFSG.generalizedFitting J0 : Set J0) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.characteristic_iff_map_eq.mp hFchar (MulAut.conj t)
  have hTW : T ≤ normalizer ((E ⊓ CFSG.generalizedFitting J0 : Subgroup J0) : Set J0) := by
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTN ht, hTF ht⟩
  rcases hIrr (E ⊓ CFSG.generalizedFitting J0) inf_le_left hTW with hW | hW
  · intro e he
    have he3 := hE3 e he
    rw [hE] at he
    obtain ⟨heP, heX0⟩ := Subgroup.mem_inf.mp he
    refine hGrossC e heP he3 fun u hu => ?_
    obtain ⟨huP, huF⟩ := Subgroup.mem_inf.mp hu
    have hMnorm : M0 ≤ normalizer (X0 : Set J0) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXn
    have hconj : u * e⁻¹ * u⁻¹ ∈ X0 :=
      (Subgroup.mem_normalizer_iff.mp (hMnorm (hPM huP)) e⁻¹).mp (X0.inv_mem heX0)
    have hmemW : e * u * e⁻¹ * u⁻¹ ∈ E ⊓ CFSG.generalizedFitting J0 := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hE]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact P.mul_mem (P.mul_mem (P.mul_mem heP huP) (P.inv_mem heP)) (P.inv_mem huP)
        · rw [show e * u * e⁻¹ * u⁻¹ = e * (u * e⁻¹ * u⁻¹) by group]
          exact X0.mul_mem heX0 hconj
      · exact (CFSG.generalizedFitting J0).mul_mem (hFnorm.conj_mem u huF e)
          ((CFSG.generalizedFitting J0).inv_mem huF)
    rw [hW] at hmemW
    have h1 : e * u * e⁻¹ * u⁻¹ = 1 := Subgroup.mem_bot.mp hmemW
    calc e * u = (e * u * e⁻¹ * u⁻¹) * (u * e) := by group
      _ = 1 * (u * e) := by rw [h1]
      _ = u * e := by group
  · have h := inf_le_right (a := E) (b := CFSG.generalizedFitting J0)
    rwa [hW] at h

theorem le_layer_of_irreducible_inverted {J0 : Type} [Group J0] [Finite J0]
    {P M0 X0 E T : Subgroup J0} (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hO : CFSG.pPrimeCore 3 J0 = ⊥) (hTX : T ≤ X0)
    (hTN : T ≤ normalizer (E : Set J0))
    (hIrr : ∀ W : Subgroup J0, W ≤ E → T ≤ normalizer (W : Set J0) → W = ⊥ ∨ W = E)
    (hInv : ∃ t ∈ ⁅T, T⁆, ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hXF : X0 ≤ centralizer (CFSG.pCore 3 J0 : Set J0))
    (hGrossC : ∀ c ∈ P, c ^ 3 = 1 → (∀ u ∈ P ⊓ CFSG.generalizedFitting J0, c * u = u * c) →
      c ∈ CFSG.generalizedFitting J0) :
    E ≤ CFSG.layer J0 := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have : (CFSG.pCore 3 J0).Normal := CFSG.pCore_normal
  have hE_F : E ≤ CFSG.generalizedFitting J0 :=
    le_generalizedFitting_of_irreducible hPM hXM hXn hE hE3 hTN hIrr hGrossC
  have hF_eq : CFSG.generalizedFitting J0 = CFSG.pCore 3 J0 ⊔ CFSG.layer J0 := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore J0 3 hO]
  obtain ⟨t, htTT, htInv⟩ := hInv
  have htT : t ∈ T := Subgroup.commutator_le_self T htTT
  have htF : ∀ a ∈ CFSG.pCore 3 J0, t * a = a * t := by
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hXF (hTX htT)) a ha).symm
  have hFN : ∀ a ∈ CFSG.pCore 3 J0, ∀ b ∈ CFSG.layer J0, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.WholeGroup.pCore_le_centralizer_layer (p := 3) ha) b hb).symm
  have htN : ∀ b ∈ CFSG.layer J0, t * b * t⁻¹ ∈ CFSG.layer J0 := by
    intro b hb
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.LocalCores.layer_characteristic (G := J0)) (MulAut.conj t)
    have hmem : (MulAut.conj t) b ∈ CFSG.layer J0 := by
      have h' : (MulAut.conj t) b ∈ (CFSG.layer J0).map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hb
      rwa [hmap] at h'
    rwa [MulAut.conj_apply] at hmem
  intro e he
  have heF : e ∈ CFSG.generalizedFitting J0 := hE_F he
  rw [hF_eq, Subgroup.mem_sup_of_normal_left] at heF
  obtain ⟨f, hf, k, hk, hfk⟩ := heF
  have hmem := mul_mem_of_inverted (N := CFSG.layer J0) (F := CFSG.pCore 3 J0)
    (t := t) hf hk hFN htF htN (by rw [hfk]; exact hE3 e he)
    (by rw [hfk]; exact htInv e he)
  rwa [hfk] at hmem

private theorem g211_mem_pCore_of_mem_component_of_centralizes {J0 : Type} [Group J0] [Finite J0]
    {J : Subgroup J0} (hJ : IsComponentOf J ⊤) {z : J0} (hz : z ∈ J)
    (hc : z ∈ centralizer (J : Set J0)) (hO : CFSG.pPrimeCore 3 J0 = ⊥) :
    z ∈ CFSG.pCore 3 J0 := by
  have hJc : CFSG.IsComponent J := g211_isComponent_of_isComponentOf_top hJ
  have hzcenter : (⟨z, hz⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hc) w w.2
  have hzC : z ∈ centralizer (CFSG.layer J0 : Set J0) :=
    CFSG.LocalCores.center_component_le_centralizer_layer hJc
      ⟨⟨z, hz⟩, hzcenter, rfl⟩
  have hzlayer : z ∈ CFSG.layer J0 := CFSG.LocalCores.component_le_layer hJc hz
  have hzcenterlayer :
      (⟨z, hzlayer⟩ : CFSG.layer J0) ∈ Subgroup.center (CFSG.layer J0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hzC) w w.2
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot (G := J0) 3 hO
    ⟨⟨z, hzlayer⟩, hzcenterlayer, rfl⟩

private theorem g211_no_active_implies_bot {J0 : Type} [Group J0] [Finite J0]
    {E : Subgroup J0} (hO : CFSG.pPrimeCore 3 J0 = ⊥)
    (hEF : E ⊓ CFSG.pCore 3 J0 = ⊥) (hEK : E ≤ CFSG.layer J0)
    (hcent : ∀ e ∈ E, e ∈ centralizer (CFSG.layer J0 : Set J0)) : E = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  have hK : e ∈ CFSG.layer J0 := hEK he
  have hC : e ∈ centralizer (CFSG.layer J0 : Set J0) := hcent e he
  have hcenter : (⟨e, hK⟩ : CFSG.layer J0) ∈ Subgroup.center (CFSG.layer J0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hC) w w.2
  have hep : e ∈ CFSG.pCore 3 J0 :=
    CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot (G := J0) 3 hO
      ⟨⟨e, hK⟩, hcenter, rfl⟩
  have hmem : e ∈ E ⊓ CFSG.pCore 3 J0 := ⟨he, hep⟩
  rwa [hEF] at hmem

private theorem g211_exists_q_noncentral {J0 : Type} [Group J0]
    {P E J : Subgroup J0} (hJ : IsComponentOf J ⊤)
    (hdec : ∀ K : Subgroup J0, IsComponentOf K ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ K, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (K : Set J0)), e = q * r)
    {e : J0} (he : e ∈ E) (hae : e ∉ centralizer (J : Set J0)) :
    ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)),
      e = q * r ∧ ¬ ∀ w ∈ J, w * q = q * w := by
  obtain ⟨q, hq, r, hr, heqr⟩ := hdec J hJ e he
  refine ⟨q, hq, r, hr, heqr, ?_⟩
  intro hqcen
  apply hae
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hrC : r ∈ centralizer (J : Set J0) := hr.2.2
  have hrw := (Subgroup.mem_centralizer_iff.mp hrC) w hw
  calc w * e = w * (q * r) := by rw [heqr]
    _ = (w * q) * r := by group
    _ = (q * w) * r := by rw [hqcen w hw]
    _ = q * (w * r) := by group
    _ = q * (r * w) := by rw [hrw]
    _ = (q * r) * w := by group
    _ = e * w := by rw [heqr]

private theorem g211_exists_key_z {J0 : Type} [Group J0]
    {P E J : Subgroup J0} (hdec : ∀ K : Subgroup J0, IsComponentOf K ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ K, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (K : Set J0)), e = q * r)
    (hJ : IsComponentOf J ⊤) {e q r : J0} (he : e ∈ E) (heqr : e = q * r)
    {t : J0} (htinv : ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hq : q ∈ P ⊓ J) (hr : r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0))) :
    ∃ q₂ r₂ z : J0,
      q₂ ∈ P ⊓ (J.map (MulAut.conj t).toMonoidHom) ∧
      r₂ ∈ P ⊓ (CFSG.layer J0 ⊓
        centralizer ((J.map (MulAut.conj t).toMonoidHom : Subgroup J0) : Set J0)) ∧
      z = q₂ * (t * q * t⁻¹) ∧ z ∈ J.map (MulAut.conj t).toMonoidHom ∧
      z ∈ centralizer ((J.map (MulAut.conj t).toMonoidHom : Subgroup J0) : Set J0) ∧
      e = q₂ * r₂ := by
  let J' : Subgroup J0 := J.map (MulAut.conj t).toMonoidHom
  have hJ' : IsComponentOf J' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) J).mpr hJ
  obtain ⟨q₂, hq₂, r₂, hr₂, heqr₂⟩ := hdec J' hJ' e he
  have hq₂r₂ : q₂ * r₂ = r₂ * q₂ :=
    (Subgroup.mem_centralizer_iff.mp hr₂.2.2) q₂ hq₂.2
  have hte : (t * q * t⁻¹) * (t * r * t⁻¹) = e⁻¹ := by
    rw [← htinv e he, heqr]
    group
  have hee : e⁻¹ = q₂⁻¹ * r₂⁻¹ := by
    rw [heqr₂]
    calc (q₂ * r₂)⁻¹ = r₂⁻¹ * q₂⁻¹ := mul_inv_rev _ _
      _ = q₂⁻¹ * r₂⁻¹ := by
        rw [← mul_inv_rev, hq₂r₂, mul_inv_rev]
  have hzEq : q₂ * (t * q * t⁻¹) = r₂⁻¹ * (t * r * t⁻¹)⁻¹ := by
    have h := hte
    rw [hee] at h
    calc q₂ * (t * q * t⁻¹) = q₂ * ((t * q * t⁻¹) * (t * r * t⁻¹)) *
          (t * r * t⁻¹)⁻¹ := by group
      _ = q₂ * (q₂⁻¹ * r₂⁻¹) * (t * r * t⁻¹)⁻¹ := by rw [h]
      _ = r₂⁻¹ * (t * r * t⁻¹)⁻¹ := by group
  have hqtJ' : t * q * t⁻¹ ∈ J' := by
    simpa [J', MulAut.conj_apply] using
      (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hq.2)
  have hzJ' : q₂ * (t * q * t⁻¹) ∈ J' := J'.mul_mem hq₂.2 hqtJ'
  have htrC : t * r * t⁻¹ ∈ centralizer (J' : Set J0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    have hrw := (Subgroup.mem_centralizer_iff.mp hr.2.2) w0 hw0
    change t * w0 * t⁻¹ * (t * r * t⁻¹) = t * r * t⁻¹ * (t * w0 * t⁻¹)
    calc t * w0 * t⁻¹ * (t * r * t⁻¹) = t * (w0 * r) * t⁻¹ := by group
      _ = t * (r * w0) * t⁻¹ := by rw [hrw]
      _ = t * r * t⁻¹ * (t * w0 * t⁻¹) := by group
  have hzC : q₂ * (t * q * t⁻¹) ∈ centralizer (J' : Set J0) := by
    rw [hzEq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hr₂.2.2) (Subgroup.inv_mem _ htrC)
  exact ⟨q₂, r₂, q₂ * (t * q * t⁻¹), hq₂, hr₂, rfl, hzJ', hzC, heqr₂⟩

private theorem g211_key_conjP {J0 : Type} [Group J0] [Finite J0]
    {P E J : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hO : CFSG.pPrimeCore 3 J0 = ⊥)
    (hdec : ∀ K : Subgroup J0, IsComponentOf K ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ K, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (K : Set J0)), e = q * r)
    (hJ : IsComponentOf J ⊤) {e q r : J0} (he : e ∈ E) (heqr : e = q * r)
    {t : J0} (htinv : ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hq : q ∈ P ⊓ J) (hr : r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0))) :
    t * q * t⁻¹ ∈ P := by
  obtain ⟨q₂, r₂, z, hq₂, -, hzdef, hzJ', hzC, -⟩ :=
    g211_exists_key_z hdec hJ he heqr htinv hq hr
  have hJ' : IsComponentOf (J.map (MulAut.conj t).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) J).mpr hJ
  have hzP : z ∈ P :=
    (g211_pCore_le_of_isSylowOf hP)
      (g211_mem_pCore_of_mem_component_of_centralizes hJ' hzJ' hzC hO)
  have hconj : t * q * t⁻¹ = q₂⁻¹ * z := by
    rw [hzdef]
    group
  rw [hconj]
  exact P.mul_mem (P.inv_mem hq₂.1) hzP

private theorem g211_key_mem_E {J0 : Type} [Group J0]
    {P M0 X0 E : Subgroup J0} (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0)
    {q t : J0} (hq : q ∈ P) (htP : t * q * t⁻¹ ∈ P) (htX : t ∈ X0) :
    q * t * q⁻¹ * t⁻¹ ∈ E := by
  have hMnorm : M0 ≤ normalizer (X0 : Set J0) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXn
  have hqnorm : q ∈ normalizer (X0 : Set J0) := hMnorm (hPM hq)
  have hqtX : q * t * q⁻¹ ∈ X0 :=
    (Subgroup.mem_normalizer_iff.mp hqnorm t).mp htX
  have hcX : q * t * q⁻¹ * t⁻¹ ∈ X0 := X0.mul_mem hqtX (X0.inv_mem htX)
  have hcP : q * t * q⁻¹ * t⁻¹ ∈ P := by
    have hc : q * t * q⁻¹ * t⁻¹ = q * (t * q * t⁻¹)⁻¹ := by group
    rw [hc]
    exact P.mul_mem hq (P.inv_mem htP)
  rw [hE]
  exact ⟨hcP, hcX⟩

private theorem g211_key_ne_one_of_ne {J0 : Type} [Group J0] [Finite J0]
    {J J' : Subgroup J0} (hJ : IsComponentOf J ⊤) (hJ' : IsComponentOf J' ⊤)
    (hne : J' ≠ J) {q : J0} (hqJ' : q ∈ J')
    (hq_noncentral : ¬ ∀ w ∈ J, w * q = q * w) : False := by
  apply hq_noncentral
  intro w hw
  have hcommle : J ≤ centralizer (J' : Set J0) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J J' hJ hJ'
        (fun h => hne h.symm))
  exact ((Subgroup.mem_centralizer_iff.mp (hcommle hw)) q hqJ').symm

private theorem g211_key_sq_central {J0 : Type} [Group J0]
    {P J J' : Subgroup J0} (hP : IsSylowOf 3 P ⊤)
    (hEq : J' = J) {q q₂ r r₂ z z₁ e t : J0}
    (hq : q ∈ P ⊓ J) (hq₂J : q₂ ∈ J)
    (hrC : r ∈ centralizer (J : Set J0))
    (hr₂C : r₂ ∈ centralizer (J' : Set J0))
    (hzC : z ∈ centralizer (J' : Set J0))
    (hzdef : z = q₂ * (t * q * t⁻¹)) (hfix : t * q * t⁻¹ = q)
    (heqr : e = q * r) (heqr₂ : e = q₂ * r₂)
    (hz₁def : z₁ = q⁻¹ * q₂) :
    (⟨q, hq.2⟩ : J) ∈ Subgroup.center J := by
  subst J'
  have hzJ : z ∈ J := by rw [hzdef, hfix]; exact J.mul_mem hq₂J hq.2
  have hz₁eq : q⁻¹ * q₂ = r * r₂⁻¹ := by
    have h : q * r = q₂ * r₂ := heqr.symm.trans heqr₂
    calc q⁻¹ * q₂ = q⁻¹ * (q₂ * r₂) * r₂⁻¹ := by group
      _ = q⁻¹ * (q * r) * r₂⁻¹ := by rw [← h]
      _ = r * r₂⁻¹ := by group
  have hz₁J : z₁ ∈ J := by
    rw [hz₁def]
    exact J.mul_mem (J.inv_mem hq.2) hq₂J
  have hz₁C : z₁ ∈ centralizer (J : Set J0) := by
    rw [hz₁def, hz₁eq]
    exact Subgroup.mul_mem _ hrC (Subgroup.inv_mem _ hr₂C)
  have hqz₁ : q * z₁ = z₁ * q :=
    (Subgroup.mem_centralizer_iff.mp hz₁C) q hq.2
  have hq₂eq : q₂ = q * z₁ := by
    rw [hz₁def]
    group
  have hzeq : z = q₂ * q := by
    rw [hzdef, hfix]
  have hzq : z = q ^ 2 * z₁ := by
    rw [hzeq, hq₂eq]
    calc (q * z₁) * q = q * (z₁ * q) := by group
      _ = q * (q * z₁) := by rw [← hqz₁]
      _ = q ^ 2 * z₁ := by rw [pow_two]; group
  have hq2 : q ^ 2 = z * z₁⁻¹ := by
    rw [hzq]
    group
  have hq2C : q ^ 2 ∈ centralizer (J : Set J0) := by
    rw [hq2]
    exact Subgroup.mul_mem _ hzC (Subgroup.inv_mem _ hz₁C)
  have hq2J : q ^ 2 ∈ J := J.pow_mem hq.2 2
  have hq2center : (⟨q ^ 2, hq2J⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hq2C) w w.2
  obtain ⟨k, hkP⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) ⟨q, hq.1⟩
  have hk : orderOf q = 3 ^ k := by
    rw [Subgroup.orderOf_coe (⟨q, hq.1⟩ : P)]
    exact hkP
  have hodd : Odd (orderOf q) := by
    rw [hk]
    exact Odd.pow (by decide : Odd 3)
  have hcop : Nat.Coprime 2 (orderOf q) := Nat.coprime_two_left.mpr hodd
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := q) (n := 2) hcop
  have hsub : (⟨q ^ 2, hq2J⟩ : J) ^ m = ⟨q, hq.2⟩ := Subtype.ext hm
  rw [← hsub]
  exact Subgroup.pow_mem _ hq2center m

private theorem g211_key_ne_one_of_eq {J0 : Type} [Group J0]
    {P J J' : Subgroup J0} (hP : IsSylowOf 3 P ⊤)
    (hEq : J' = J) {q q₂ r r₂ z z₁ e t : J0}
    (hq : q ∈ P ⊓ J) (hq₂J : q₂ ∈ J)
    (hrC : r ∈ centralizer (J : Set J0))
    (hr₂C : r₂ ∈ centralizer (J' : Set J0))
    (hzC : z ∈ centralizer (J' : Set J0))
    (hzdef : z = q₂ * (t * q * t⁻¹)) (hfix : t * q * t⁻¹ = q)
    (heqr : e = q * r) (heqr₂ : e = q₂ * r₂)
    (hz₁def : z₁ = q⁻¹ * q₂)
    (hq_noncentral : ¬ ∀ w ∈ J, w * q = q * w) : False := by
  have hqcenter := g211_key_sq_central hP hEq hq hq₂J hrC hr₂C hzC hzdef hfix
    heqr heqr₂ hz₁def
  apply hq_noncentral
  intro w hw
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hqcenter) ⟨w, hw⟩)

private theorem g211_key_ne_one {J0 : Type} [Group J0] [Finite J0]
    {P E J : Subgroup J0} (hP : IsSylowOf 3 P ⊤)
    (hdec : ∀ K : Subgroup J0, IsComponentOf K ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ K, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (K : Set J0)), e = q * r)
    (hJ : IsComponentOf J ⊤) {e q r : J0} (he : e ∈ E) (heqr : e = q * r)
    {t : J0} (htinv : ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hq : q ∈ P ⊓ J) (hr : r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)))
    (hq_noncentral : ¬ ∀ w ∈ J, w * q = q * w) :
    q * t * q⁻¹ * t⁻¹ ≠ 1 := by
  intro hc1
  have hfix : t * q * t⁻¹ = q := by
    have h1 : q * t * q⁻¹ = t := by
      have h := congrArg (fun x => x * t) hc1
      simpa [mul_assoc] using h
    have h2 : q * t = t * q := by
      have h := congrArg (fun x => x * q) h1
      simpa [mul_assoc] using h
    rw [← h2]
    group
  obtain ⟨q₂, r₂, z, hq₂, hr₂, hzdef, -, hzC, heqr₂⟩ :=
    g211_exists_key_z hdec hJ he heqr htinv hq hr
  have hJ' : IsComponentOf (J.map (MulAut.conj t).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) J).mpr hJ
  by_cases hEq : J.map (MulAut.conj t).toMonoidHom = J
  · have hq₂J : q₂ ∈ J := by
      rw [← hEq]
      exact hq₂.2
    exact g211_key_ne_one_of_eq hP hEq hq hq₂J hr.2.2 hr₂.2.2 hzC hzdef hfix
      heqr heqr₂ rfl hq_noncentral
  · have hqtJ' : t * q * t⁻¹ ∈ J.map (MulAut.conj t).toMonoidHom := by
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hq.2)
    have hqJ' : q ∈ J.map (MulAut.conj t).toMonoidHom := by
      rw [← hfix]
      exact hqtJ'
    exact g211_key_ne_one_of_ne hJ hJ' hEq hqJ' hq_noncentral

private theorem g211_key_centralizes {J0 : Type} [Group J0] [Finite J0]
    {J J' K : Subgroup J0} (hJ : IsComponentOf J ⊤) (hJ' : IsComponentOf J' ⊤)
    (hK : IsComponentOf K ⊤) (hKJ : K ≠ J) (hKJ' : K ≠ J')
    {q t : J0} (hq : q ∈ J) (hqt : t * q * t⁻¹ ∈ J') :
    q * t * q⁻¹ * t⁻¹ ∈ centralizer (K : Set J0) := by
  have hJK : J ≤ centralizer (K : Set J0) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J K hJ hK
        (fun h => hKJ h.symm))
  have hJ'K : J' ≤ centralizer (K : Set J0) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J' K hJ' hK
        (fun h => hKJ' h.symm))
  have hc : q * t * q⁻¹ * t⁻¹ = q * (t * q * t⁻¹)⁻¹ := by group
  rw [hc]
  exact Subgroup.mul_mem _ (hJK hq) (Subgroup.inv_mem _ (hJ'K hqt))

private theorem g211_active_eq_J_or_conj {J0 : Type} [Group J0] [Finite J0]
    {P M0 X0 E T : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0) (hO : CFSG.pPrimeCore 3 J0 = ⊥)
    (hTX : T ≤ X0) {t : J0}
    (htT : t ∈ ⁅T, T⁆) (htinv : ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hAlt : ∀ J : Subgroup J0, IsComponentOf J ⊤ →
      E ≤ centralizer (J : Set J0) ∨ E ⊓ centralizer (J : Set J0) = ⊥)
    (hdec : ∀ J : Subgroup J0, IsComponentOf J ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)), e = q * r)
    {J : Subgroup J0} (hJ : IsComponentOf J ⊤) (hact : ¬ E ≤ centralizer (J : Set J0)) :
    ∀ K : Subgroup J0, IsComponentOf K ⊤ → ¬ E ≤ centralizer (K : Set J0) →
      K = J ∨ K = J.map (MulAut.conj t).toMonoidHom := by
  intro K hK hactK
  by_contra hcase
  push Not at hcase
  obtain ⟨hKJ, hKJ'⟩ := hcase
  obtain ⟨e, he, hae⟩ : ∃ e : J0, e ∈ E ∧ e ∉ centralizer (J : Set J0) := by
    by_contra h
    apply hact
    intro e he
    by_contra hec
    exact h ⟨e, he, hec⟩
  obtain ⟨q, hq, r, hr, heqr, hqnc⟩ := g211_exists_q_noncentral hJ hdec he hae
  have htP : t * q * t⁻¹ ∈ P :=
    g211_key_conjP hP hO hdec hJ he heqr htinv hq hr
  have hcE : q * t * q⁻¹ * t⁻¹ ∈ E :=
    g211_key_mem_E hPM hXM hXn hE hq.1 htP (hTX (Subgroup.commutator_le_self T htT))
  have hcne : q * t * q⁻¹ * t⁻¹ ≠ 1 :=
    g211_key_ne_one hP hdec hJ he heqr htinv hq hr hqnc
  have hJ' : IsComponentOf (J.map (MulAut.conj t).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) J).mpr hJ
  have hqtJ' : t * q * t⁻¹ ∈ J.map (MulAut.conj t).toMonoidHom := by
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hq.2)
  have hcent : q * t * q⁻¹ * t⁻¹ ∈ centralizer (K : Set J0) :=
    g211_key_centralizes hJ hJ' hK hKJ hKJ' hq.2 hqtJ'
  rcases hAlt K hK with hle | hbot
  · exact hactK hle
  · apply hcne
    have hmem : q * t * q⁻¹ * t⁻¹ ∈ E ⊓ centralizer (K : Set J0) := ⟨hcE, hcent⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem

private theorem g211_map_conj_mul_eq {G : Type*} [Group G] (A : Subgroup G) (x y : G) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

private theorem g211_map_conj_pair_actions {G : Type*} [Group G]
    {T A B : Subgroup G} (hAB : A ≠ B)
    (hB : ∀ s ∈ T, B.map (MulAut.conj s).toMonoidHom = A ∨
      B.map (MulAut.conj s).toMonoidHom = B) :
    (∀ x ∈ T, A.map (MulAut.conj x).toMonoidHom = A →
      B.map (MulAut.conj x).toMonoidHom = B) ∧
    (∀ x ∈ T, A.map (MulAut.conj x).toMonoidHom = B →
      B.map (MulAut.conj x).toMonoidHom = A) ∧
    (∀ x ∈ T, A.map (MulAut.conj x).toMonoidHom = A →
      A.map (MulAut.conj x⁻¹).toMonoidHom = A) ∧
    (∀ x ∈ T, A.map (MulAut.conj x).toMonoidHom = B →
      A.map (MulAut.conj x⁻¹).toMonoidHom = B) := by
  have hmapinj : ∀ x : G, Function.Injective (Subgroup.map (MulAut.conj x).toMonoidHom) :=
    fun x => Subgroup.map_injective (MulAut.conj x).injective
  have hone : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyz' : y = z := by simpa [MulAut.conj_apply] using hyz
      simpa [hyz'] using hy
    · intro hz
      exact ⟨z, hz, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxa
    rcases hB x hx with hbA | hbB
    · exact absurd (hmapinj x (hxa.trans hbA.symm)) hAB
    · exact hbB
  · intro x hx hxa
    rcases hB x hx with hbA | hbB
    · exact hbA
    · exact absurd (hmapinj x (hxa.trans hbB.symm)) hAB
  · intro x hx hxa
    have h := g211_map_conj_mul_eq A x x⁻¹
    rw [mul_inv_cancel] at h
    have hleft : (A.map (MulAut.conj x⁻¹).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = A.map (MulAut.conj x).toMonoidHom := by
      rw [hxa]
      calc (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom
          = A.map (MulAut.conj (1 : G)).toMonoidHom := h.symm
        _ = A := hone
    exact Subgroup.map_injective (MulAut.conj x).injective hleft
  · intro x hx hxa
    have h := g211_map_conj_mul_eq A x x⁻¹
    rw [mul_inv_cancel] at h
    have hleft : (A.map (MulAut.conj x⁻¹).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = A := by
      calc (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom
          = A.map (MulAut.conj (1 : G)).toMonoidHom := h.symm
        _ = A := hone
    have hBx : B.map (MulAut.conj x).toMonoidHom = A := by
      rcases hB x hx with hbA | hbB
      · exact hbA
      · exact absurd (hmapinj x (hxa.trans hbB.symm)) hAB
    exact Subgroup.map_injective (MulAut.conj x).injective (hleft.trans hBx.symm)

private theorem map_conj_eq_of_mem_commutator_of_pair {G : Type*} [Group G]
    {T A B : Subgroup G} (hAB : A ≠ B)
    (hA : ∀ s ∈ T, A.map (MulAut.conj s).toMonoidHom = A ∨
      A.map (MulAut.conj s).toMonoidHom = B)
    (hB : ∀ s ∈ T, B.map (MulAut.conj s).toMonoidHom = A ∨
      B.map (MulAut.conj s).toMonoidHom = B)
    {s : G} (hs : s ∈ ⁅T, T⁆) : A.map (MulAut.conj s).toMonoidHom = A := by
  have hactions := g211_map_conj_pair_actions hAB hB
  obtain ⟨hB_of_A, hB_of_A_swap, hinv_fix, hinv_swap⟩ := hactions
  change A.map (MulAut.conj s) = A
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : ⁅T, T⁆ ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, Subgroup.mem_normalizer_iff_map_conj_eq]
    have htelescope :
        A.map (MulAut.conj (a * b * a⁻¹ * b⁻¹)).toMonoidHom =
          ((((A.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom).map
            (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom) := by
      rw [g211_map_conj_mul_eq A (a * b * a⁻¹) b⁻¹,
        g211_map_conj_mul_eq (A.map (MulAut.conj b⁻¹).toMonoidHom) (a * b) a⁻¹,
        g211_map_conj_mul_eq ((A.map (MulAut.conj b⁻¹).toMonoidHom).map
          (MulAut.conj a⁻¹).toMonoidHom) a b]
    change A.map (MulAut.conj (a * b * a⁻¹ * b⁻¹)).toMonoidHom = A
    rw [htelescope]
    rcases hA a ha with hafix | haswap
    · rcases hA b hb with hbfix | hbswap
      · rw [hinv_fix b hb hbfix, hinv_fix a ha hafix, hbfix, hafix]
      · rw [hinv_swap b hb hbswap, hB_of_A a⁻¹ (T.inv_mem ha) (hinv_fix a ha hafix),
          hB_of_A_swap b hb hbswap, hafix]
    · rcases hA b hb with hbfix | hbswap
      · rw [hinv_fix b hb hbfix, hinv_swap a ha haswap, hB_of_A b hb hbfix,
          hB_of_A_swap a ha haswap]
      · rw [hinv_swap b hb hbswap,
          hB_of_A_swap a⁻¹ (T.inv_mem ha) (hinv_swap a ha haswap), hbswap,
          hB_of_A_swap a ha haswap]
  exact hle hs

theorem unique_active_component {J0 : Type} [Group J0] [Finite J0]
    {P M0 X0 E T : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hPM : P ≤ M0) (hXM : X0 ≤ M0)
    (hXn : (X0.subgroupOf M0).Normal) (hE : E = P ⊓ X0) (hE1 : E ≠ ⊥)
    (hO : CFSG.pPrimeCore 3 J0 = ⊥) (hEF : E ⊓ CFSG.pCore 3 J0 = ⊥)
    (hEK : E ≤ CFSG.layer J0) (hTX : T ≤ X0) (hTN : T ≤ normalizer (E : Set J0))
    (hInv : ∃ t ∈ ⁅T, T⁆, ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hAlt : ∀ J : Subgroup J0, IsComponentOf J ⊤ →
      E ≤ centralizer (J : Set J0) ∨ E ⊓ centralizer (J : Set J0) = ⊥)
    (hdec : ∀ J : Subgroup J0, IsComponentOf J ⊤ → ∀ e ∈ E,
      ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)), e = q * r) :
    ∃ J : Subgroup J0, IsComponentOf J ⊤ ∧ ¬ E ≤ centralizer (J : Set J0) ∧
      ∀ J' : Subgroup J0, IsComponentOf J' ⊤ → ¬ E ≤ centralizer (J' : Set J0) → J' = J := by
  have hactive : ∃ J : Subgroup J0, IsComponentOf J ⊤ ∧ ¬ E ≤ centralizer (J : Set J0) := by
    by_contra hnone
    push Not at hnone
    have hcent : ∀ e ∈ E, e ∈ centralizer (CFSG.layer J0 : Set J0) := by
      intro e he
      exact mem_centralizer_layer_of_forall_component (fun K hK => hnone K hK he)
    exact hE1 (g211_no_active_implies_bot hO hEF hEK hcent)
  obtain ⟨J, hJ, hact⟩ := hactive
  obtain ⟨t, htT, htinv⟩ := hInv
  have hpair : ∀ K : Subgroup J0, IsComponentOf K ⊤ →
      ¬ E ≤ centralizer (K : Set J0) → K = J ∨ K = J.map (MulAut.conj t).toMonoidHom :=
    g211_active_eq_J_or_conj hP hPM hXM hXn hE hO hTX htT htinv hAlt hdec hJ hact
  by_cases hEq : J.map (MulAut.conj t).toMonoidHom = J
  · refine ⟨J, hJ, hact, fun K hK hactK => ?_⟩
    rcases hpair K hK hactK with h | h
    · exact h
    · rw [h, hEq]
  · exfalso
    have htN : t ∈ normalizer (E : Set J0) := hTN (Subgroup.commutator_le_self T htT)
    have hJ' : IsComponentOf (J.map (MulAut.conj t).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) _).mpr hJ
    have hact' : ¬ E ≤ centralizer
        ((J.map (MulAut.conj t).toMonoidHom : Subgroup J0) : Set J0) :=
      not_le_centralizer_map_conj_of_mem_normalizer htN hact
    have hA : ∀ s ∈ T, J.map (MulAut.conj s).toMonoidHom = J ∨
        J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj t).toMonoidHom := by
      intro s hs
      have hJs : IsComponentOf (J.map (MulAut.conj s).toMonoidHom) ⊤ :=
        (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) _).mpr hJ
      exact hpair _ hJs (not_le_centralizer_map_conj_of_mem_normalizer (hTN hs) hact)
    have hB : ∀ s ∈ T,
        (J.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom = J ∨
        (J.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
          J.map (MulAut.conj t).toMonoidHom := by
      intro s hs
      have hJ's : IsComponentOf
          ((J.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom) ⊤ :=
        (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) _).mpr hJ'
      exact hpair _ hJ's (not_le_centralizer_map_conj_of_mem_normalizer (hTN hs) hact')
    have hAB : J ≠ J.map (MulAut.conj t).toMonoidHom := fun h => hEq h.symm
    exact hEq (map_conj_eq_of_mem_commutator_of_pair hAB hA hB htT)

private theorem mem_pCore_of_unique_active {J0 : Type} [Group J0] [Finite J0]
    {E J : Subgroup J0} (hO : CFSG.pPrimeCore 3 J0 = ⊥) (hJ : IsComponentOf J ⊤)
    (huniq : ∀ J' : Subgroup J0, IsComponentOf J' ⊤ → ¬ E ≤ centralizer (J' : Set J0) → J' = J)
    {e q r : J0} (he : e ∈ E) (hqJ : q ∈ J)
    (hr : r ∈ CFSG.layer J0 ⊓ centralizer (J : Set J0)) (heqr : e = q * r) :
    r ∈ CFSG.pCore 3 J0 := by
  have hrcomp : ∀ J' : Subgroup J0, IsComponentOf J' ⊤ → r ∈ centralizer (J' : Set J0) := by
    intro J' hJ'
    by_cases hJJ' : J' = J
    · rw [hJJ']
      exact (Subgroup.mem_inf.mp hr).2
    · have hE' : E ≤ centralizer (J' : Set J0) := by
        by_contra hnot
        exact hJJ' (huniq J' hJ' hnot)
      have hr_eq : r = q⁻¹ * e := by
        rw [heqr]
        group
      rw [hr_eq]
      have hJle : J ≤ centralizer (J' : Set J0) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne J J' hJ hJ' (Ne.symm hJJ'))
      exact Subgroup.mul_mem _ (hJle (J.inv_mem hqJ)) (hE' he)
  have hrC : r ∈ centralizer (CFSG.layer J0 : Set J0) :=
    mem_centralizer_layer_of_forall_component hrcomp
  have hr_center : r ∈ (Subgroup.center (CFSG.layer J0)).map (CFSG.layer J0).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨r, (Subgroup.mem_inf.mp hr).1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hrC (y : J0) y.2
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot (p := 3) hO hr_center

theorem le_component_of_unique_active {J0 : Type} [Group J0] [Finite J0]
    {P M0 X0 E T J : Subgroup J0} (hXM : X0 ≤ M0) (hXn : (X0.subgroupOf M0).Normal)
    (hXs : IsSolvable ↥X0) (hEX : E ≤ X0) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hO : CFSG.pPrimeCore 3 J0 = ⊥) (hTX : T ≤ X0) (hTN : T ≤ normalizer (E : Set J0))
    (hInv : ∃ t ∈ ⁅T, T⁆, ∀ e ∈ E, t * e * t⁻¹ = e⁻¹)
    (hXF : X0 ≤ centralizer (CFSG.pCore 3 J0 : Set J0))
    (hJ : IsComponentOf J ⊤) (hact : ¬ E ≤ centralizer (J : Set J0))
    (huniq : ∀ J' : Subgroup J0, IsComponentOf J' ⊤ → ¬ E ≤ centralizer (J' : Set J0) → J' = J)
    (hdec : ∀ e ∈ E,
      ∃ q ∈ P ⊓ J, ∃ r ∈ P ⊓ (CFSG.layer J0 ⊓ centralizer (J : Set J0)), e = q * r) :
    E ≤ J ∧ ¬ J ≤ M0 := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have : (CFSG.pCore 3 J0).Normal := CFSG.pCore_normal
  constructor
  · intro e he
    obtain ⟨q, hqPJ, r, hrP, heqr⟩ := hdec e he
    have hqJ : q ∈ J := (Subgroup.mem_inf.mp hqPJ).2
    have hrCJ : r ∈ centralizer (J : Set J0) := (Subgroup.mem_inf.mp hrP).2 |>.2
    have hr_pcore : r ∈ CFSG.pCore 3 J0 :=
      mem_pCore_of_unique_active hO hJ huniq he hqJ (Subgroup.mem_inf.mp hrP).2 heqr
    obtain ⟨t, htTT, htInv⟩ := hInv
    have htT : t ∈ T := Subgroup.commutator_le_self T htTT
    have hnotact : ¬ E ≤
        centralizer ((J.map (MulAut.conj t).toMonoidHom : Subgroup J0) : Set J0) :=
      not_le_centralizer_map_conj_of_mem_normalizer (hTN htT) hact
    have hJt : IsComponentOf (J.map (MulAut.conj t).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) _).mpr hJ
    have hJmap : J.map (MulAut.conj t).toMonoidHom = J := huniq _ hJt hnotact
    have htF : ∀ a ∈ CFSG.pCore 3 J0, t * a = a * t := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hXF (hTX htT)) a ha).symm
    have hFN : ∀ a ∈ CFSG.pCore 3 J0, ∀ b ∈ J, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (CFSG.WholeGroup.pCore_le_centralizer_layer (p := 3) ha) b
        (CFSG.LocalCores.component_le_layer (g211_isComponent_of_isComponentOf_top hJ) hb)).symm
    have htN : ∀ b ∈ J, t * b * t⁻¹ ∈ J := by
      intro b hb
      have hb' : (MulAut.conj t) b ∈ J.map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hb
      rw [hJmap] at hb'
      rwa [MulAut.conj_apply] at hb'
    have hqr : r * q = e := by
      rw [heqr]
      have hcomm : q * r = r * q := Subgroup.mem_centralizer_iff.mp hrCJ q hqJ
      rw [hcomm]
    have hmem := mul_mem_of_inverted (N := J) (F := CFSG.pCore 3 J0) (t := t)
      hr_pcore hqJ hFN htF htN (by rw [hqr]; exact hE3 e he)
      (by rw [hqr]; exact htInv e he)
    rwa [hqr] at hmem
  · intro hJM
    have hX0 := le_centralizer_of_component_le_of_solvable hXM hXn hXs hJ hJM
    exact hact (hEX.trans hX0)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
