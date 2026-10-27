module

public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lA zpowers_mem_omegaA_iff)

section Components

@[expose] noncomputable def lA422 {G : Type*} [Group G] [Finite G] (A : Subgroup G) (a : G) :
    Set (Subgroup G) :=
  {K | K ∈ thetaComponentsAt 3 a ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
    Late.sectionCentralizer A K ((aschbacherSolvableCore 3 K).map K.subtype) =
      (Subgroup.zpowers a : Set G) ∧
    thetaAlpha 3 ((Sec4.autThetaQuot A K).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({a} : Set G)) K)) ≠ ⊥}

theorem mem_lA422_iff {G : Type*} [Group G] [Finite G] {A K : Subgroup G} {a : G} :
    K ∈ lA422 A a ↔ K ∈ thetaComponentsAt 3 a ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      Late.sectionCentralizer A K ((aschbacherSolvableCore 3 K).map K.subtype) =
        (Subgroup.zpowers a : Set G) ∧
      thetaAlpha 3 ((Sec4.autThetaQuot A K).subgroupOf
        (Sec4.autThetaQuot (Subgroup.centralizer ({a} : Set G)) K)) ≠ ⊥ :=
  Iff.rfl

theorem mem_lA_of_mem_lA422 {G : Type} [Group G] [Finite G] {A K : Subgroup G} {a : G}
    (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) (hK : K ∈ lA422 A a) : K ∈ lA A a :=
  ⟨hK.1, hK.2.1, hK.2.2.1, Sec13.thetaAlpha_ne_bot_of_le (Sec13.autThetaQuot_mono hAa K)
    (Sec13.autThetaQuot_mono (Sec13.centralizer_le_normalizer_zpowers a) K)
    (Sec13.autThetaQuot_centralizer_normal a K) hK.2.2.2⟩

theorem exists_mem_lA422 (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) {G : Type} [Group G]
    [Finite G] (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (h27 : Nat.card A = 27) {c : G} (hc : Subgroup.zpowers c ∈ omegaA A) :
    ∃ L : Subgroup G, L ∈ lA422 A c := by
  obtain ⟨hcA, hc3, hstar⟩ := zpowers_mem_omegaA_iff.mp hc
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    norm_num at hc3
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha c hcA)
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  have hmax : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'e, fun B hB hAB => ?_⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := x
        obtain ⟨_, y, hy, rfl⟩ := y
        apply Subtype.ext
        change (x : G) * y = y * x
        exact congrArg Subtype.val
          (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hB.2 x hx)
    have hAB' : A ≤ B.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hBA := hAF.2.1 _ hBe hAB'
    intro x hx
    have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  rcases h422 C hS4 A' hmax h27' c' hc'A hc'Z hc'1 with h1 | ⟨L', hL', h9, hα⟩
  · exact absurd h1 hstar
  set L := L'.map C.subtype with hLdef
  have hLc : L ∈ thetaComponentsAt 3 c := ⟨L', hL', rfl⟩
  have hA'N : A' ≤ Subgroup.normalizer (L' : Set C) :=
    h45 C hS4 A' (fun x => ⟨1, Subtype.ext (by simpa using hA'e.2 x x.2)⟩)
      (Or.inr ⟨hA'e, 3, le_rfl, by rw [h27']; norm_num⟩) L' hL'
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    have hmem : (⟨a, hAC ha⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr ha
    exact (Sec13.coe_mem_normalizer_map_iff C).mpr (hA'N hmem)
  have hAut : Nat.card (Sec4.autThetaQuot A L) = 9 := by
    rw [← hA'map, hLdef, ← Sec13.map_autThetaQuot_sub C A' L',
      Subgroup.card_map_of_injective (MulAut.congr (Sec13.thetaQuotEquivSub C L')).injective, h9]
  have hcT : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc
  have hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAN]
    congr 1
    have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
      have := Sec13.card_inf_mul_card_autThetaQuot hAN
      rw [hAut, h27] at this
      omega
    have hcmem : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := Subgroup.mem_inf.mpr ⟨hcA, hcT⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcmem)
      (by rw [h3, hc3])).symm
  have hαC : thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf (Sec4.autThetaQuot C L)) ≠ ⊥ := by
    have hC' : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← (Sec13.thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (Sec13.thetaQuotEquivSub C L'))
      (Sec4.autThetaQuot A' L') (Sec4.autThetaQuot ⊤ L'))] at hα
    rwa [Sec13.map_autThetaQuot_sub, Sec13.map_autThetaQuot_sub, hA'map, hC'] at hα
  exact ⟨L, hLc, hAN, hsc, hαC⟩

end Components

@[expose] def Item128BarAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    A ∈ partTwoT G ∨ ∀ a : G, Subgroup.zpowers a ∈ omegaA A →
      ((a ∈ Sec4.thetaQuotCentralizer L ∧
          Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6))) ∨
        (a ∈ L ∧ A ⊓ L = Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧
          ∃ L₀ ∈ thetaComponentsAt 3 c, L₀ ≠ L ∧
            Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6)) ∧
            c ∈ L₀ ∧ a ∈ Sec4.thetaQuotCentralizer L₀)) ∧
      ∀ K ∈ lA422 A a, Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Item1210BarS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G → partTwoS G = ∅ →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
      A ∈ partTwoT G ∨
      A ∉ partTwoS G ∧ ∃ L₀ ∈ thetaComponentsAt 3 c,
        Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6)) ∧
        ∃ a ∈ A ⊓ Sec4.thetaQuotCentralizer L₀, a ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 a,
          Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          Subgroup.zpowers a ∈ omegaA A ∧ K ∈ lA A a

section Proofs

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_one_of_card_zpowers_eq_three {a : G} (ha : Nat.card (Subgroup.zpowers a) = 3) :
    a ≠ 1 := by
  rintro rfl
  rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at ha
  exact absurd ha (by norm_num)

theorem exists_of_item128BarAt (h128 : Item128BarAt) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hAE : A ∈ partTwoE G) (hAT : A ∉ partTwoT G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) :
    ∃ L₀ ∈ thetaComponentsAt 3 c,
      Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6)) ∧
      a ∈ A ⊓ Sec4.thetaQuotCentralizer L₀ ∧ a ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 a,
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2) ∧ K ∈ lA A a := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  obtain ⟨haA, ha3, -⟩ := zpowers_mem_omegaA_iff.mp ha
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  obtain ⟨K, hK⟩ := exists_mem_lA422 h422 h45 h.toPartTwoStanding hAF hAE.2.1 ha
  obtain ⟨hcase, hHJ⟩ := (h128 G A c L h hAE hty).resolve_left hAT a ha
  have hKa : K ∈ lA A a := mem_lA_of_mem_lA422 hAa hK
  have ha1 := ne_one_of_card_zpowers_eq_three ha3
  rcases hcase with ⟨haL, hA6⟩ | ⟨-, -, L₀, hL₀, -, hA6, -, haL₀⟩
  · exact ⟨L, h.mem_thetaComponentsAt, hA6, ⟨haA, haL⟩, ha1, K, hK.1, hHJ K hK, hKa⟩
  · exact ⟨L₀, hL₀, hA6, ⟨haA, haL₀⟩, ha1, K, hK.1, hHJ K hK, hKa⟩

theorem item1210BarS_of (h128 : Item128BarAt) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) :
    Item1210BarS := by
  intro G _ _ A c L h hAE hS hty
  by_cases hAT : A ∈ partTwoT G
  · exact Or.inl hAT
  right
  refine ⟨by rw [hS]; exact Set.notMem_empty A, ?_⟩
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  obtain ⟨F, hF⟩ := Sec13.omegaA_nonempty h.toPartTwoStanding hS hAF hAT
  obtain ⟨-, -, a, rfl, -⟩ := id hF
  obtain ⟨L₀, hL₀, hA6, haL₀, ha1, K, hK, hHJ, hKa⟩ :=
    exists_of_item128BarAt h128 h422 h45 h hAE hAT hty hF
  exact ⟨L₀, hL₀, hA6, a, haL₀, ha1, K, hK, hHJ, hF, hKa⟩

theorem Sec12Std.inf_thetaQuotCentralizer_eq {A L : Subgroup G} {c : G} (h : Sec12Std G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hAL : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A ⊓ Sec4.thetaQuotCentralizer L = A ⊓ Subgroup.centralizer (L : Set G) := by
  have hle : A ⊓ Subgroup.centralizer (L : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer L := by
    refine fun x hx => ⟨hx.1, Sec6.mem_thetaQuotCentralizer_iff.mpr
      ⟨Subgroup.centralizer_le_normalizer _ hx.2, fun l hl => ?_⟩⟩
    have h1 : l * x = x * l := Subgroup.mem_centralizer_iff.mp hx.2 l hl
    rw [show l⁻¹ * (x * l * x⁻¹) = 1 by rw [← h1]; group]
    exact one_mem _
  have hA27 : Nat.card A = 27 := h.isE27.2
  have hdvd : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 9 ≤ Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    h.card_B ▸ Subgroup.card_le_of_le hle
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · rw [hk] at hge; norm_num at hge
  · rw [hk] at hge; norm_num at hge
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, h.card_B]; norm_num)).symm
  · exfalso
    have hAA : A ⊓ Sec4.thetaQuotCentralizer L = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA27]; norm_num)
    have hB3 : IsPGroup 3 (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
      ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
    have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
    rw [hAA, hAL, hZ] at h1
    norm_num at h1

theorem Sec12Std.toSec12StdBar {A L : Subgroup G} {c : G} (h : Sec12Std G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hAL : Nat.card (A ⊓ L : Subgroup G) = 9) : Sec12StdBar G A c L := by
  have heq := h.inf_thetaQuotCentralizer_eq hZ hAL
  exact
    { h.toPartTwoStanding with
      partTwoF_eq := h.partTwoF_eq
      isE27 := h.isE27
      mem_A := h.mem_A
      ne_one := h.ne_one
      mem_thetaComponentsAt := h.mem_thetaComponentsAt
      mem_L := h.mem_L
      card_B := by rw [heq]; exact h.card_B
      sup_eq := by rw [heq]; exact h.sup_eq
      exists_sylow := by rw [heq]; exact h.exists_sylow }

theorem item128_of_item128BarAt (h128 : Item128BarAt) (h122 : Item122) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) : Item128 := by
  intro G _ _ A c L h
  by_cases hAT : A ∈ partTwoT G
  · exact Or.inl hAT
  right
  have hty := h122 G A c L h.toSec12Std
  have hZ := card_center_thetaQuot_eq_three_of_item122 h122 h.toSec12Std
  have hAL := h.toSec12Std.card_inf_eq_nine h122
  have hbar := h.toSec12Std.toSec12StdBar hZ hAL
  have heq := h.toSec12Std.inf_thetaQuotCentralizer_eq hZ hAL
  have hAE := h.mem_partTwoE
  by_cases hΩ : ∃ a : G, Subgroup.zpowers a ∈ omegaA A
  · right
    obtain ⟨a, ha⟩ := hΩ
    obtain ⟨L₀, hL₀, hA6, haL₀, ha1, K, hK, hHJ, hKa⟩ :=
      exists_of_item128BarAt h128 h422 h45 hbar hAE hAT hty ha
    refine ⟨L₀, hL₀, hA6, a, ⟨haL₀.1, fun x hx => ?_⟩, ha1, K, hK, hHJ, ha, hKa⟩
    obtain ⟨-, hθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp haL₀.2
    have h1 := Sec13.conj_mem_inSubgroup_theta hx (hθ x hx)
    have e : x * (x⁻¹ * (a * x * a⁻¹)) * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by group
    rw [e] at h1
    exact h1
  · left
    push Not at hΩ
    have hAab := hAE.1
    have h27 := hAE.2.1
    have hstar : ∀ a ∈ A, a ≠ 1 → StarConditionAt A a := by
      intro a ha ha1
      by_contra hs
      exact hΩ a (zpowers_mem_omegaA_iff.mpr ⟨ha, Sec13.card_zpowers_eq_three hAab ha ha1, hs⟩)
    obtain ⟨hsolv, hindep, -⟩ :=
      CFSG.RankThree.Theta.part_two_solvable_local_quotient_alpha_criterion A hAab h27 hstar
    have hB9 := h.card_B
    have hBA : A ⊓ Subgroup.centralizer (L : Set G) ≤ A := inf_le_left
    refine ⟨fun D hDA hD9 => hindep D _ hDA hD9 hBA hB9, ?_⟩
    obtain ⟨hs, hcop⟩ := hsolv _ hBA hB9
    have hcore := solvable_prime_complement_core_characterization
      (H := thetaAlpha 3 (A ⊓ Subgroup.centralizer (L : Set G))) Nat.prime_three
    refine eq_top_iff.mpr (hcore.2.2.2.1 ⊤ Subgroup.normal_top ?_ ?_)
    · exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
        (⊤ : Subgroup (thetaAlpha 3 (A ⊓ Subgroup.centralizer (L : Set G)))) ≃* _).symm.toMonoidHom)
        (MulEquiv.surjective _)
    · rw [Subgroup.card_top]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop

end Proofs

end CFSG.RankThree.PartTwo.Sec12
