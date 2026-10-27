module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.SmallIndex
public import CFSG.Quasithin.Vol2.Ch10SecQ3CI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_SU3EightBorelNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 3 → 3 ∣ Nat.card (Subgroup.center X) →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      ∃ x : X, x ∈ Subgroup.normalizer (S : Set X) ∧ orderOf x = 9 ∧
        orderOf (x ^ 3) = 3 ∧ x ^ 3 ∈ Subgroup.center X

theorem exists_permuting_E9_of_two_conj
    (D : Data G) (V₀ V L : Subgroup G)
    (hK : K_SU3EightBorelNine)
    (hCen : UCK.U3Center)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    (c : Ctx17_33 D V₀ V L 3) (hZ : 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ conjSetOf D.M L) (hK₂ : K₂ ∈ conjSetOf D.M L)
    (h₁₂ : K₁ ≠ K₂) :
    ∃ E : Subgroup G, E ≤ conjClosure D.M L ∧ IsElemAbelian 3 E ∧
      Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank 3 E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : L ∈ calC D.M := c.mem_calC
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) = 3 :=
    Nat.dvd_antisymm (hCen (Bar2 L) 3 c.shape) hZ
  let X : Subgroup G := conjClosure D.M L
  have hX : X = conjClosure D.M L := rfl
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  let S : Subgroup G := D.T ⊓ X
  have hSylX : IsSylowTwoOf S X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hXM hMX)
  let Sbar : Subgroup (Bar2 X) := barImage X S
  have hSylBar : IsSylowTwoOf Sbar ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylX)
  have hlayer : CFSG.layer (Bar2 X) = ⊤ := layer_bar2_eq_top_of_calC hL hX
  have hO2 : CFSG.pCore 2 (Bar2 X) = ⊥ := s13_pCore_bar_eq_bot X
  have hK₁C : K₁ ∈ calC X := mem_calC_of_mem_conjSetOf_of_calC hL hX hK₁
  have hK₂C : K₂ ∈ calC X := mem_calC_of_mem_conjSetOf_of_calC hL hX hK₂
  let C₁ : Subgroup (Bar2 X) := barImage X K₁
  let C₂ : Subgroup (Bar2 X) := barImage X K₂
  have hC₁comp : CFSG.IsComponent C₁ := s13_barImage_isComponent hK₁C
  have hC₂comp : CFSG.IsComponent C₂ := s13_barImage_isComponent hK₂C
  have hCne : C₁ ≠ C₂ := by
    have hc₁ : K₁ ∈ CFSG.Quasithin.cComp X := uc22p20e_cComp_of_calC hK₁C
    have hc₂ : K₂ ∈ CFSG.Quasithin.cComp X := uc22p20e_cComp_of_calC hK₂C
    intro heq
    exact h₁₂ (barImage_injOn_cComp hL hX hc₁ hc₂ heq)
  have hcommC : ∀ a ∈ C₁, ∀ b ∈ C₂, a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hK₁C hK₂C h₁₂ a ha b hb
  have hSU₁ : IsSU3 ↥C₁ 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₁C
    exact uc22p20p_isSU3_of_mulEquiv e (isSU3_bar2_of_mem_conjSet hK₁ c.shape)
  have hSU₂ : IsSU3 ↥C₂ 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₂C
    exact uc22p20p_isSU3_of_mulEquiv e (isSU3_bar2_of_mem_conjSet hK₂ c.shape)
  have hZ₁ : Nat.card (Subgroup.center ↥C₁) = 3 := by
    refine Nat.dvd_antisymm (hCen ↥C₁ 3 hSU₁) ?_
    have hcongr : Nat.card (Subgroup.center ↥C₁) =
        Nat.card (Subgroup.center (Bar2 K₁)) := by
      obtain ⟨e⟩ := s13_bar_equiv hK₁C
      exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [hcongr]
    obtain ⟨g, -, rfl⟩ := hK₁
    rw [card_center_bar2_map (MulAut.conj g) L, hZcard]
  have hZ₂ : Nat.card (Subgroup.center ↥C₂) = 3 := by
    refine Nat.dvd_antisymm (hCen ↥C₂ 3 hSU₂) ?_
    have hcongr : Nat.card (Subgroup.center ↥C₂) =
        Nat.card (Subgroup.center (Bar2 K₂)) := by
      obtain ⟨e⟩ := s13_bar_equiv hK₂C
      exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [hcongr]
    obtain ⟨g, -, rfl⟩ := hK₂
    rw [card_center_bar2_map (MulAut.conj g) L, hZcard]
  have hSyl₁ : IsSylowTwoOf (Sbar ⊓ C₁) C₁ :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hSylBar le_top
      hC₁comp.2.subgroupOf
  have hSyl₂ : IsSylowTwoOf (Sbar ⊓ C₂) C₂ :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hSylBar le_top
      hC₂comp.2.subgroupOf
  have hSyl₁' : IsSylowTwoOf ((Sbar ⊓ C₁).subgroupOf C₁) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSyl₁
  have hSyl₂' : IsSylowTwoOf ((Sbar ⊓ C₂).subgroupOf C₂) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSyl₂
  obtain ⟨x₁, hx₁N, hx₁ord, hx₁cube, _⟩ :=
    hK ↥C₁ hSU₁ (by rw [hZ₁]) ((Sbar ⊓ C₁).subgroupOf C₁) hSyl₁'
  obtain ⟨x₂, hx₂N, hx₂ord, hx₂cube, _⟩ :=
    hK ↥C₂ hSU₂ (by rw [hZ₂]) ((Sbar ⊓ C₂).subgroupOf C₂) hSyl₂'
  have hx₁Nbar : (x₁ : Bar2 X) ∈ Subgroup.normalizer (Sbar : Set (Bar2 X)) := by
    have hx₁Ninf : (x₁ : Bar2 X) ∈ Subgroup.normalizer
        ((Sbar ⊓ C₁ : Subgroup (Bar2 X)) : Set (Bar2 X)) :=
      CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.coe_mem_normalizer (K := C₁)
        (S := Sbar ⊓ C₁) inf_le_right hx₁N
    exact normalizer_inf_component_le_normalizer_sylow hSylBar hlayer hO2 hC₁comp
      ⟨x₁.2, hx₁Ninf⟩
  have hx₂Nbar : (x₂ : Bar2 X) ∈ Subgroup.normalizer (Sbar : Set (Bar2 X)) := by
    have hx₂Ninf : (x₂ : Bar2 X) ∈ Subgroup.normalizer
        ((Sbar ⊓ C₂ : Subgroup (Bar2 X)) : Set (Bar2 X)) :=
      CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.coe_mem_normalizer (K := C₂)
        (S := Sbar ⊓ C₂) inf_le_right hx₂N
    exact normalizer_inf_component_le_normalizer_sylow hSylBar hlayer hO2 hC₂comp
      ⟨x₂.2, hx₂Ninf⟩
  let z₁ : Bar2 X := (x₁ : Bar2 X) ^ 3
  let z₂ : Bar2 X := (x₂ : Bar2 X) ^ 3
  have hz₁ord : orderOf z₁ = 3 := by
    change orderOf ((x₁ : Bar2 X) ^ 3) = 3
    rw [← SubgroupClass.coe_pow (x₁ : ↥C₁) 3, Subgroup.orderOf_coe]
    exact hx₁cube
  have hz₂ord : orderOf z₂ = 3 := by
    change orderOf ((x₂ : Bar2 X) ^ 3) = 3
    rw [← SubgroupClass.coe_pow (x₂ : ↥C₂) 3, Subgroup.orderOf_coe]
    exact hx₂cube
  have hz₁pow : z₁ ^ 3 = 1 := by rw [← hz₁ord]; exact pow_orderOf_eq_one z₁
  have hz₂pow : z₂ ^ 3 = 1 := by rw [← hz₂ord]; exact pow_orderOf_eq_one z₂
  have hz₁N : z₁ ∈ Subgroup.normalizer (Sbar : Set (Bar2 X)) :=
    Subgroup.pow_mem (Subgroup.normalizer (Sbar : Set (Bar2 X))) hx₁Nbar 3
  have hz₂N : z₂ ∈ Subgroup.normalizer (Sbar : Set (Bar2 X)) :=
    Subgroup.pow_mem (Subgroup.normalizer (Sbar : Set (Bar2 X))) hx₂Nbar 3
  have hz₁C : z₁ ∈ C₁ := by
    change (x₁ : Bar2 X) ^ 3 ∈ C₁
    exact C₁.pow_mem x₁.2 3
  have hz₂C : z₂ ∈ C₂ := by
    change (x₂ : Bar2 X) ^ 3 ∈ C₂
    exact C₂.pow_mem x₂.2 3
  have hx₁x₂comm : Commute (x₁ : Bar2 X) (x₂ : Bar2 X) := hcommC _ x₁.2 _ x₂.2
  have hz₁z₂comm : Commute z₁ z₂ := (hx₁x₂comm.pow_left 3).pow_right 3
  have hC₁normal : C₁.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hC₁comp
  have hC₂normal : C₂.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hC₂comp
  have hCinfCent : C₁ ⊓ C₂ ≤ (Subgroup.center ↥C₁).map C₁.subtype := by
    have hntriv : ⁅C₁, C₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hC₁comp hC₂comp).resolve_left hCne
    have hC₁N₂ : C₁ ≤ Subgroup.normalizer (C₂ : Set (Bar2 X)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hntriv).trans
        (Subgroup.centralizer_le_normalizer _)
    have hC₁Ninf : C₁ ≤ Subgroup.normalizer ((C₁ ⊓ C₂ : Subgroup (Bar2 X)) : Set (Bar2 X)) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · rintro ⟨hw₁, hw₂⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) w).mp hw₁,
          (Subgroup.mem_normalizer_iff.mp (hC₁N₂ hy) w).mp hw₂⟩
      · rintro ⟨hw₁, hw₂⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) w).mpr hw₁,
          (Subgroup.mem_normalizer_iff.mp (hC₁N₂ hy) w).mpr hw₂⟩
    have hN : ((C₁ ⊓ C₂).subgroupOf C₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hC₁Ninf
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC₁comp.1 hN with htop | hcenter
    · exfalso
      have hle : C₁ ≤ C₂ := by
        intro y hy
        have hmem : (⟨y, hy⟩ : ↥C₁) ∈ (C₁ ⊓ C₂).subgroupOf C₁ := by
          rw [htop]; exact Subgroup.mem_top _
        have hmemC2 : (⟨y, hy⟩ : ↥C₁) ∈ C₂.subgroupOf C₁ :=
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
        exact Subgroup.mem_subgroupOf.mp hmemC2
      have h1 : CFSG.Open.IsComponentOf C₁ ⊤ :=
        ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hC₁normal),
          Iff.mp CFSG.Quasithin.A3.isQuasisimple_iff_open hC₁comp.1⟩
      have h2 : CFSG.Open.IsComponentOf C₂ ⊤ :=
        ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hC₂normal),
          Iff.mp CFSG.Quasithin.A3.isQuasisimple_iff_open hC₂comp.1⟩
      exact hCne (CFSG.ComponentClassification.LocalComponents.eq_of_le C₁ C₂ h1 h2 hle)
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      have hsub : (⟨y, hy.1⟩ : ↥C₁) ∈ (C₁ ⊓ C₂).subgroupOf C₁ :=
        Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hcenter hsub, rfl⟩
  let Nbar : Subgroup (Bar2 X) := Subgroup.normalizer (Sbar : Set (Bar2 X))
  have hcenter_dvd : ∀ {y : C₁}, y ∈ Subgroup.center ↥C₁ →
      orderOf (y : Bar2 X) ∣ 3 := by
    intro y hy
    have h1 : orderOf y ∣ Nat.card ↥(Subgroup.center ↥C₁) :=
      Subgroup.orderOf_dvd_natCard _ hy
    rw [hZ₁] at h1
    have h2 : orderOf (y : Bar2 X) = orderOf y := Subgroup.orderOf_coe y
    rwa [h2]
  have hx₁ord' : orderOf (x₁ : Bar2 X) = 9 := by
    rw [Subgroup.orderOf_coe, hx₁ord]
  have hx₂ord' : orderOf (x₂ : Bar2 X) = 9 := by
    rw [Subgroup.orderOf_coe, hx₂ord]
  have hE9 : ∃ F : Subgroup (Bar2 X), F ≤ Nbar ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
    by_cases hind : z₂ ∈ Subgroup.zpowers z₁
    ·
      have hcases := CFSG.SignalizerFunctorTheorem.NonLocalExc.eq_one_or_eq_or_eq_inv_of_mem_zpowers
        (a := z₁) (b := z₂) hz₁pow hind
      have hz₂ne1 : z₂ ≠ 1 := by
        intro h; rw [h, orderOf_one] at hz₂ord; omega
      have hz₁C₂ : z₁ ∈ C₂ := by
        rcases hcases with h | h | h
        · exact absurd h hz₂ne1
        · rw [← h]; exact hz₂C
        · have hz₁eq : z₁ = z₂⁻¹ := by rw [h]; group
          rw [hz₁eq]; exact C₂.inv_mem hz₂C
      have key : ∀ (y : Bar2 X), y ∈ Nbar → y ^ 3 = 1 → y ∉ Subgroup.zpowers z₁ →
          (∀ e ∈ Subgroup.zpowers z₁, Commute y e) →
          ∃ F : Subgroup (Bar2 X), F ≤ Nbar ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
        intro y hyN hy3 hyNot hyComm
        obtain ⟨F, hFel, hFcard, hFN⟩ :=
          CFSG.SectionRank.QTK.CoverB.exists_elemAbelian_sup (r := 3) (k := 1)
            Nat.prime_three (E := Subgroup.zpowers z₁) (x := y) (K := Nbar)
            (CFSG.SectionRank.QTK.CoverB.isElemAbelian_zpowers_of_pow hz₁pow)
            (by rw [Nat.card_zpowers, hz₁ord]; norm_num) hy3 hyComm hyNot hyN
            (Subgroup.zpowers_le.mpr hz₁N)
        exact ⟨F, hFN, hFel, by simpa using hFcard⟩
      by_cases hzeq : z₂ = z₁
      ·
        let y : Bar2 X := (x₁ : Bar2 X) * (x₂ : Bar2 X)⁻¹
        have hy3 : y ^ 3 = 1 := by
          change ((x₁ : Bar2 X) * (x₂ : Bar2 X)⁻¹) ^ 3 = 1
          rw [(hx₁x₂comm.inv_right).mul_pow, inv_pow]
          change z₁ * z₂⁻¹ = 1
          rw [hzeq, mul_inv_cancel]
        have hyN : y ∈ Nbar :=
          Nbar.mul_mem hx₁Nbar (Nbar.inv_mem hx₂Nbar)
        have hyNot : y ∉ Subgroup.zpowers z₁ := by
          intro hy
          have hyC₂ : y ∈ C₂ := Subgroup.zpowers_le.mpr hz₁C₂ hy
          have hx₁C₂ : (x₁ : Bar2 X) ∈ C₂ := by
            have hx₁eq : (x₁ : Bar2 X) = y * (x₂ : Bar2 X) := by
              change (x₁ : Bar2 X) =
                ((x₁ : Bar2 X) * (x₂ : Bar2 X)⁻¹) * (x₂ : Bar2 X)
              group
            rw [hx₁eq]
            exact C₂.mul_mem hyC₂ x₂.2
          have hx₁cent : (⟨(x₁ : Bar2 X), x₁.2⟩ : C₁) ∈ Subgroup.center ↥C₁ := by
            obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (hCinfCent ⟨x₁.2, hx₁C₂⟩)
            have : a = ⟨(x₁ : Bar2 X), x₁.2⟩ := Subtype.ext hax
            rwa [this] at ha
          have hdvd := hcenter_dvd hx₁cent
          have hle : orderOf (x₁ : Bar2 X) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
          omega
        have hyComm : ∀ e ∈ Subgroup.zpowers z₁, Commute y e := by
          have hz₁x₁ : Commute z₁ (x₁ : Bar2 X) := by
            change Commute ((x₁ : Bar2 X) ^ 3) (x₁ : Bar2 X)
            exact (Commute.refl (x₁ : Bar2 X)).pow_left 3
          have hz₁x₂ : Commute z₁ (x₂ : Bar2 X) := hcommC _ hz₁C _ x₂.2
          have hz₁y : Commute z₁ y := hz₁x₁.mul_right hz₁x₂.inv_right
          intro e he
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
          exact hz₁y.symm.zpow_right k
        exact key y hyN hy3 hyNot hyComm
      ·
        have hz₂eq : z₂ = z₁⁻¹ := by
          rcases hcases with h | h | h
          · exact absurd h hz₂ne1
          · exact absurd h hzeq
          · exact h
        let y : Bar2 X := (x₁ : Bar2 X) * (x₂ : Bar2 X)
        have hy3 : y ^ 3 = 1 := by
          change ((x₁ : Bar2 X) * (x₂ : Bar2 X)) ^ 3 = 1
          rw [hx₁x₂comm.mul_pow]
          change z₁ * z₂ = 1
          rw [hz₂eq, mul_inv_cancel]
        have hyN : y ∈ Nbar := Nbar.mul_mem hx₁Nbar hx₂Nbar
        have hyNot : y ∉ Subgroup.zpowers z₁ := by
          intro hy
          have hyC₂ : y ∈ C₂ := Subgroup.zpowers_le.mpr hz₁C₂ hy
          have hx₁C₂ : (x₁ : Bar2 X) ∈ C₂ := by
            have hx₁eq : (x₁ : Bar2 X) = y * (x₂ : Bar2 X)⁻¹ := by
              change (x₁ : Bar2 X) =
                ((x₁ : Bar2 X) * (x₂ : Bar2 X)) * (x₂ : Bar2 X)⁻¹
              group
            rw [hx₁eq]
            exact C₂.mul_mem hyC₂ (C₂.inv_mem x₂.2)
          have hx₁cent : (⟨(x₁ : Bar2 X), x₁.2⟩ : C₁) ∈ Subgroup.center ↥C₁ := by
            obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (hCinfCent ⟨x₁.2, hx₁C₂⟩)
            have : a = ⟨(x₁ : Bar2 X), x₁.2⟩ := Subtype.ext hax
            rwa [this] at ha
          have hdvd := hcenter_dvd hx₁cent
          have hle : orderOf (x₁ : Bar2 X) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
          omega
        have hyComm : ∀ e ∈ Subgroup.zpowers z₁, Commute y e := by
          have hz₁x₁ : Commute z₁ (x₁ : Bar2 X) := by
            change Commute ((x₁ : Bar2 X) ^ 3) (x₁ : Bar2 X)
            exact (Commute.refl (x₁ : Bar2 X)).pow_left 3
          have hz₁x₂ : Commute z₁ (x₂ : Bar2 X) := hcommC _ hz₁C _ x₂.2
          have hz₁y : Commute z₁ y := hz₁x₁.mul_right hz₁x₂
          intro e he
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
          exact hz₁y.symm.zpow_right k
        exact key y hyN hy3 hyNot hyComm
    ·
      obtain ⟨F, hFel, hFcard, hFN⟩ :=
        CFSG.SectionRank.QTK.CoverB.exists_elemAbelian_sup (r := 3) (k := 1)
          Nat.prime_three (E := Subgroup.zpowers z₁) (x := z₂) (K := Nbar)
          (CFSG.SectionRank.QTK.CoverB.isElemAbelian_zpowers_of_pow hz₁pow)
          (by rw [Nat.card_zpowers, hz₁ord]; norm_num) hz₂pow
          (fun e he => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
            exact hz₁z₂comm.symm.zpow_right k) hind hz₂N
          (Subgroup.zpowers_le.mpr hz₁N)
      exact ⟨F, hFN, hFel, by simpa using hFcard⟩
  have h2Nbar : 2 ≤ CFSG.Open.pRank 3 Nbar := by
    obtain ⟨F, hFN, hFel, hFcard⟩ := hE9
    have h := CFSG.SectionRank.le_pRank (p := 3) (k := 2) (by norm_num) (H := Nbar) (E := F)
      hFN hFel (by rw [hFcard]; norm_num)
    simpa using h
  let B : Subgroup G := X ⊓ Subgroup.normalizer (S : Set G)
  have hBrank : 2 ≤ CFSG.Open.pRank 3 B := by
    let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
    let SX : Subgroup ↥X := S.subgroupOf X
    have hSXbar : SX.map π = Sbar := rfl
    have hQleS : CFSG.pCore 2 ↥X ≤ SX :=
      CFSG.Quasithin.pCore_two_le_subgroupOf hSylX
    have hcomap : Sbar.comap π = SX := by
      rw [show Sbar = SX.map π from rfl]
      exact Subgroup.comap_map_eq_self (by
        rw [show π.ker = CFSG.pCore 2 ↥X from QuotientGroup.ker_mk' _]
        exact hQleS)
    have hBsub : B.subgroupOf X = Subgroup.normalizer (SX : Set ↥X) := by
      ext x
      constructor
      · intro hx
        have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
        have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.mp hxB).2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hxN (y : G)
      · intro hxN
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hyX : y ∈ X := hy.2
          have h := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyX⟩).mp
            (Subgroup.mem_subgroupOf.mpr hy)
          rwa [Subgroup.mem_subgroupOf] at h
        · intro hy
          have hyX : y ∈ X := by
            have h1 : y = (x : G)⁻¹ * (x * y * (x : G)⁻¹) * x := by group
            rw [h1]
            exact X.mul_mem (X.mul_mem (X.inv_mem x.2) hy.2) x.2
          have h := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyX⟩).mpr
            (Subgroup.mem_subgroupOf.mpr hy)
          rwa [Subgroup.mem_subgroupOf] at h
    have hmapnorm : (Subgroup.normalizer (SX : Set ↥X)).map π = Nbar := by
      have h1 : Nbar.comap π = Subgroup.normalizer (SX : Set ↥X) := by
        rw [← hcomap]
        exact Subgroup.comap_normalizer_eq_of_surjective Sbar
          (QuotientGroup.mk'_surjective _)
      rw [← h1]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hBmap : (B.subgroupOf X).map π = Nbar := by
      rw [hBsub, hmapnorm]
    have hcop : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥X) :=
      CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three (by norm_num)
    calc 2 ≤ CFSG.Open.pRank 3 Nbar := h2Nbar
      _ = CFSG.Open.pRank 3 ((B.subgroupOf X).map π) := by rw [hBmap]
      _ = CFSG.Open.pRank 3 (B.subgroupOf X) :=
          CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
            (source := ↥X) 3 Nat.prime_three (CFSG.pCore 2 ↥X) hcop (B.subgroupOf X)
      _ = CFSG.Open.pRank 3 B :=
          CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3
            (show B ≤ X from inf_le_left)
  have hchev : CIsChevOver (BarInf L) 3 := by
    obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv_of_calC hL
    have hLie : CFSG.Blueprint.LieModel (BarInf L) .PSU 3 2 3 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm c.shape.2
    exact ⟨.PSU, 3, hLie.admissible, hLie⟩
  obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
    exists_permuting_elemAbelian_of_calC (D := D) (L := L) (X := X) (n := 3)
      hL hX hchev hK3 Nat.prime_three (by norm_num)
  refine ⟨E, ?_, hEel, hperm, hBrank.trans hErank⟩
  exact hEB.trans inf_le_left

theorem gap17_36a_n3_three_torus_of_inputs
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ)
    (hK : K_SU3EightBorelNine)
    (hCen : UCK.U3Center)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian) :
    Gap17_36a_n3_three_torus D V₀ V L n := by
  intro c _ hn hZ hcard
  subst hn
  obtain ⟨K₁, K₂, _, hK₁, hK₂, _, h₁₂, _, _⟩ := exists_three_mem_conjSetOf hcard
  exact exists_permuting_E9_of_two_conj D V₀ V L hK hCen hK3 c hZ hK₁ hK₂ h₁₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
