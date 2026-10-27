module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigTools
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof153Twin3

variable {G : Type} [Group G] [Finite G]

theorem generalizedFitting_sup_pCoreOf_eq_pCore_and_mem_scriptY2 {A Y K : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hY2 : Y ∈ scriptY2 A) (hYc : IsCharacteristicP 2 ↥Y)
    (hK4 : K ∈ scriptY4 A LB) (hKY : K ≤ Y) :
    generalizedFitting ↥(K ⊔ CFSG.Open.pCoreOf 2 Y) =
        CFSG.pCore 2 ↥(K ⊔ CFSG.Open.pCoreOf 2 Y) ∧
      K ⊔ CFSG.Open.pCoreOf 2 Y ∈ scriptY2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemP : ∀ u : ↥Y, (u : G) ∈ CFSG.Open.pCoreOf 2 Y ↔ u ∈ CFSG.pCore 2 ↥Y :=
    fun _ => Subgroup.mem_map_iff_mem Y.subtype_injective
  have hPY : CFSG.Open.pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hP2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  have hAP : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK4.1.2
  have hKhY : K ⊔ CFSG.Open.pCoreOf 2 Y ≤ Y := sup_le hKY hPY
  have hKhP : K ⊔ CFSG.Open.pCoreOf 2 Y ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) := hKhY.trans hYP
  have hCP : ∀ x ∈ Y, x ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) →
      x ∈ CFSG.Open.pCoreOf 2 Y := by
    intro x hx hxc
    have h1 : (⟨x, hx⟩ : ↥Y) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥Y : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxc u ((hmemP u).mpr hu)
    exact (hmemP ⟨x, hx⟩).mpr (hYc h1)
  have hPKh : CFSG.Open.pCoreOf 2 Y ≤
      CFSG.Open.pCoreOf 2 (K ⊔ CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hKhP hP2
  have hKh2 : K ⊔ CFSG.Open.pCoreOf 2 Y ∈ scriptY2 A :=
    ⟨⟨fun htop => hY2.1.1 (top_le_iff.mp (htop ▸ hKhY)),
        Sec14.le_normalizer_sup hAK hAP⟩,
      fun h0 => hY2.2 (le_bot_iff.mp (h0 ▸ hPKh))⟩
  refine ⟨(isCharacteristicP_iff_generalizedFitting_eq_pCore
    ↥(K ⊔ CFSG.Open.pCoreOf 2 Y) 2).mp ?_, hKh2⟩
  refine Proof153Twin3.isCharacteristicP_of_le_normalizer' le_sup_right hP2 hKhP
    fun x hx hxc => ?_
  obtain ⟨k, hk⟩ := hP2 ⟨x, hCP x (hKhY hx) hxc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem exists_mul_mem_of_le_sup_pCoreOf {Y K X₁ : Subgroup G} (hKY : K ≤ Y)
    (hX₁ : X₁ ≤ K ⊔ CFSG.Open.pCoreOf 2 Y) :
    ∀ x ∈ X₁, ∃ k ∈ K, ∃ u ∈ CFSG.Open.pCoreOf 2 Y, x = k * u := by
  intro x hx
  have hxKh : x ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := hX₁ hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K (CFSG.Open.pCoreOf 2 Y)
    (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hxKh
  obtain ⟨k, hk, u, hu, hxku⟩ := hxKh
  exact ⟨k, hk, u, hu, hxku.symm⟩

theorem isTripleCover_quot_pCoreOf_of_le_sup {Y K X₁ : Subgroup G}
    (hKY : K ≤ Y) (hX₁Y : X₁ ≤ Y) (hKX₁ : K ≤ X₁)
    (hKP : ∀ x ∈ X₁, ∃ k ∈ K, ∃ u ∈ CFSG.Open.pCoreOf 2 Y, x = k * u)
    (hKbar : Sec4.IsTripleCover ↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))
      (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) := by
  have hmemP : ∀ u : ↥Y, (u : G) ∈ CFSG.Open.pCoreOf 2 Y ↔ u ∈ CFSG.pCore 2 ↥Y :=
    fun _ => Subgroup.mem_map_iff_mem Y.subtype_injective
  have hPY : CFSG.Open.pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hP2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  set f : ↥X₁ →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hX₁Y) with hf
  set Kb := (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) with hKb
  have hrange : f.range = Kb := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨k, hk, u, hu, hxku⟩ := hKP x x.2
      refine ⟨⟨k, hKY hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
      have hu' : (⟨u, hPY hu⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := (hmemP ⟨u, hPY hu⟩).mp hu
      have hxe : Subgroup.inclusion hX₁Y x = ⟨k, hKY hk⟩ * ⟨u, hPY hu⟩ := Subtype.ext hxku
      have hu1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨u, hPY hu⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hu'
      rw [hf, MonoidHom.comp_apply, hxe, map_mul, hu1, mul_one]
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, hKX₁ (Subgroup.mem_subgroupOf.mp hk)⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥X₁ := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, fun x => ?_⟩
      have hxP : ((x : ↥X₁) : G) ∈ CFSG.Open.pCoreOf 2 Y := by
        have h1 : f x = 1 := x.2
        have h2 : (Subgroup.inclusion hX₁Y (x : ↥X₁) : ↥Y) ∈ CFSG.pCore 2 ↥Y :=
          (QuotientGroup.eq_one_iff _).mp h1
        exact (hmemP _).mpr h2
      obtain ⟨k, hk⟩ := hP2 ⟨_, hxP⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    · have hKb' : Sec4.IsTripleCover ↥f.range (alternatingGroup (Fin 6)) :=
        Proof1515.isTripleCover_congr (MulEquiv.subgroupCongr hrange.symm) hKbar
      have hn : ((CFSG.pCore 2 ↥X₁).map f.rangeRestrict).Normal :=
        Subgroup.Normal.map inferInstance _ f.rangeRestrict_surjective
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥X₁).map f.rangeRestrict) :=
        CFSG.pCore_isPGroup.map _
      have hbot := Proof153Twin3.eq_bot_of_isTripleCover hKb' h2
      intro x hx
      have h1 : f.rangeRestrict x = 1 := by
        have : f.rangeRestrict x ∈ (CFSG.pCore 2 ↥X₁).map f.rangeRestrict :=
          Subgroup.mem_map_of_mem _ hx
        rwa [hbot, Subgroup.mem_bot] at this
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
  have e : ↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  exact Proof1515.isTripleCover_congr e.symm hKbar

omit [Finite G] in
theorem mem_sectionCentralizer_of_le_sup_pCoreOf {A Y K X₁ : Subgroup G} {c₀ : G}
    (hc₀A : c₀ ∈ A) (hKc : K ≤ Subgroup.centralizer ({c₀} : Set G)) (hKY : K ≤ Y)
    (hAP : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
    (hAX₁ : A ≤ Subgroup.normalizer (X₁ : Set G))
    (hKP : ∀ x ∈ X₁, ∃ k ∈ K, ∃ u ∈ CFSG.Open.pCoreOf 2 Y, x = k * u)
    (hNX₁ : X₁ ⊓ CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X₁) :
    c₀ ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  refine ⟨hc₀A, fun x hx => hNX₁ ⟨?_, ?_⟩⟩
  · exact X₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAX₁ hc₀A) x).mp hx) (X₁.inv_mem hx)
  · obtain ⟨k, hk, u, hu, rfl⟩ := hKP x hx
    have hck : c₀ * k = k * c₀ :=
      Subgroup.mem_centralizer_iff.mp (hKc hk) c₀ (Set.mem_singleton c₀)
    have hcu : c₀ * u * c₀⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp (hAP hc₀A) u).mp hu
    have hcomm : c₀ * u * c₀⁻¹ * u⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (CFSG.Open.pCoreOf 2 Y).mul_mem hcu ((CFSG.Open.pCoreOf 2 Y).inv_mem hu)
    have e1 : c₀ * (k * u) * c₀⁻¹ * (k * u)⁻¹ =
        k * (c₀ * u * c₀⁻¹ * u⁻¹) * k⁻¹ := by
      calc c₀ * (k * u) * c₀⁻¹ * (k * u)⁻¹ = (c₀ * k) * u * c₀⁻¹ * u⁻¹ * k⁻¹ := by group
        _ = (k * c₀) * u * c₀⁻¹ * u⁻¹ * k⁻¹ := by rw [hck]
        _ = k * (c₀ * u * c₀⁻¹ * u⁻¹) * k⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (hYP (hKY hk)) _).mp hcomm

theorem exists_mem_scriptY0_of_le_centralizer {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y K : Subgroup G} {c₀ : G} (hY : Y ∈ scriptY0 A LB) (hYc : IsCharacteristicP 2 ↥Y)
    (hc₀ : c₀ ∈ A) (hK4 : K ∈ scriptY4 A LB)
    (hKYc : K ≤ Y ⊓ Subgroup.centralizer ({c₀} : Set G))
    (hKbar : Sec4.IsTripleCover ↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))
      (alternatingGroup (Fin 6)))
    (h152 : ∀ M ∈ scriptY2 A, K ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∃ X ∈ thetaComponentsIn M, K ≤ X ∧ X ∈ scriptY0 A LB) :
    ∃ X₁ : Subgroup G, X₁ ∈ scriptY0 A LB ∧ X₁ ≤ Y ∧
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) ∧
      c₀ ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
  have hKY : K ≤ Y := hKYc.trans inf_le_left
  have hKc : K ≤ Subgroup.centralizer ({c₀} : Set G) := hKYc.trans inf_le_right
  have hPY : CFSG.Open.pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hP2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.2
  have hAP : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  obtain ⟨hKhF, hKh2⟩ :=
    generalizedFitting_sup_pCoreOf_eq_pCore_and_mem_scriptY2 hY.2 hYc hK4 hKY
  obtain ⟨X₁, hX₁θ, hKX₁, hX₁0⟩ :=
    h152 (K ⊔ CFSG.Open.pCoreOf 2 Y) hKh2 le_sup_left hKhF
  have hX₁Kh : X₁ ≤ K ⊔ CFSG.Open.pCoreOf 2 Y := le_of_mem_thetaComponentsIn hX₁θ
  have hX₁Y : X₁ ≤ Y := hX₁Kh.trans (sup_le hKY hPY)
  have hKP : ∀ x ∈ X₁, ∃ k ∈ K, ∃ u ∈ CFSG.Open.pCoreOf 2 Y, x = k * u :=
    exists_mul_mem_of_le_sup_pCoreOf hKY hX₁Kh
  have hNX₁ : X₁ ⊓ CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hX₁Y.trans hYP)) (hP2.to_le inf_le_right)
  refine ⟨X₁, hX₁0, hX₁Y, isTripleCover_quot_pCoreOf_of_le_sup hKY hX₁Y hKX₁ hKP hKbar, ?_⟩
  exact mem_sectionCentralizer_of_le_sup_pCoreOf hc₀ hKc hKY hAP hX₁0.1.1.2 hKP hNX₁

theorem step156ONXK_of_onk_big {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (h152 : Item152Big A (lB A))
    (hK : Step156ONK A (lB A)) : Step156ONXK A (lB A) := by
  intro Y hY hON
  obtain ⟨c₀, K, hc₀, hK4, hKYc, hKbar⟩ := hK Y hY hON
  have hYb : Big152 Y := big152_of_isTripleCover_on hON
  obtain ⟨M, hM⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  obtain ⟨-, -, -, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hYc : IsCharacteristicP 2 ↥Y :=
    isCharacteristicP_of_mem_thetaComponentsIn hF
      (Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM)
  have hKb : Big152 K := big152_of_map_isTripleCover_alt6 (hKYc.trans inf_le_left) hKbar
  obtain ⟨X₁, hX₁0, hX₁Y, hX₁bar, hc₀X⟩ :=
    exists_mem_scriptY0_of_le_centralizer hY.prop hYc (zpowers_mem_omegaA_iff.mp hc₀).1 hK4 hKYc
      hKbar (fun M hM hKM hF => h152 K hK4 hKb M hM hKM hF)
  exact ⟨c₀, X₁, hc₀, hX₁0, hX₁Y, hX₁bar, hc₀X⟩

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
