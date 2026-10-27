module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofTools
public import CFSG.RankThree.Native.ONTripleRed
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint

namespace Res417Five

open CFSG.RankThree.Native.ONTriple

theorem isElemAbelian_zpowers_of_cube {Y : Type*} [Group Y] {x : Y} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change (a : Y) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

section Model


theorem card_le_27_of_abelian_model {B : Subgroup GM} (hB : IsPGroup 3 B)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hBP⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  have hBQ : B ≤ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := hg ▸ hBP
  have h := hr.card_le_of_abelian (B.subgroupOf _) fun a ha b hb =>
    Subtype.ext (hab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv] at h


theorem exists_isE27_model : ∃ D : Subgroup GM, Late.IsE27 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : xG 0 ^ 3 = 1 := relG.vcube 0
  have hyz : xG 0 ∉ Subgroup.zpowers zG := by
    intro h
    have h0 := (relG.coord_eq_zero_iff ⟨xG 0, ThreeQRel.v_mem 0⟩).2 h
    rw [coord_xG0] at h0
    have := congrFun h0 0
    simp at this
  obtain ⟨x, hx3, hxy, hxY⟩ := Sec13.ON134.model_exists_centralizer hy3 hyz
  have hz3 : zG ^ 3 = 1 := relG.xcube
  have hzo : orderOf zG = 3 := orderOf_eq_prime hz3 relG.x1
  have hyo : orderOf (xG 0) = 3 :=
    orderOf_eq_prime hy3 fun h => hyz (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 3 :=
    orderOf_eq_prime hx3 fun h => hxY (h ▸ Subgroup.one_mem _)
  set Y := Subgroup.zpowers (xG 0) ⊔ Subgroup.zpowers zG with hY
  refine ⟨Y ⊔ Subgroup.zpowers x, ?_, ?_⟩
  · have hYe : CFSG.Assembly.IsElemAbelian 3 Y :=
      isElemAbelian_sup_zpowers_cube (isElemAbelian_zpowers_of_cube hy3) hz3
        fun a _ => (zG_central a).symm
    refine isElemAbelian_sup_zpowers_cube hYe hx3 fun a ha => ?_
    have hxC : Y ≤ Subgroup.centralizer ({x} : Set GM) := by
      refine sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm)) (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (zG_central x)))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hxC ha)
  · have hzy : zG ∉ Subgroup.zpowers (xG 0) := by
      intro h
      apply hyz
      have hle : Subgroup.zpowers zG ≤ Subgroup.zpowers (xG 0) := Subgroup.zpowers_le.mpr h
      have heq : Subgroup.zpowers zG = Subgroup.zpowers (xG 0) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hyo])
      rw [heq]
      exact Subgroup.mem_zpowers _
    have h9 : Nat.card Y = 9 := by
      rw [hY, card_sup_zpowers_eq_three_mul hzo hzy fun a _ b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_right (zG_central a).symm k).eq, Nat.card_zpowers, hyo]
    have hxYc : ∀ a ∈ Y, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hxC : Y ≤ Subgroup.centralizer ({x} : Set GM) := by
        refine sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm)) (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (zG_central x)))
      exact (Commute.zpow_right
        (Subgroup.mem_centralizer_singleton_iff.mp (hxC ha)) k).eq
    rw [card_sup_zpowers_eq_three_mul hxo hxY hxYc, h9]

theorem exists_twoGroup_model {D : Subgroup GM}
    (hD : Late.IsE27 D) :
    ∃ S : Subgroup GM, S ≠ ⊥ ∧ IsPGroup 2 S ∧ D ≤ Subgroup.normalizer (S : Set GM) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := maxInvariantPiSubgroups_nonempty (⊤ : Subgroup GM) D (piOf 2)
  have hzcard : Nat.card (Subgroup.zpowers zG) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) relG.xcube
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers zG := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers zG from hall)
    rw [hD.2] at h1
    omega
  obtain ⟨hK4, -⟩ := part_three_M hD hyD hyz hS
  obtain ⟨⟨-, hS2, hSD⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hS
  refine ⟨S, fun hb => ?_, (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2, hSD⟩
  have h4 := hK4.card_four
  rw [hb, Subgroup.card_bot] at h4
  norm_num at h4

end Model

end Res417Five

open Res417Three Res417Five

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerInConf417.exists_centralizer_not_mem (h : IsInnerInConf417 L A E c m)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (h3 : ∀ l : L, l ^ 3 ^ 2 = 1 → l ^ 3 = 1) {a : G} (haA : a ∈ A) (haL : a ∉ L) :
    ∃ w : G, w ∈ Subgroup.centralizer (L : Set G) ∧ w ^ 3 = 1 ∧ w ∉ L := by
  obtain ⟨l, hl, hal⟩ := h.inner a haA
  have ha3 : a ^ 3 = 1 := h.2.2.2.2.1.1.prop.2 a haA
  have hla : l * a = a * l := by
    have h1 := hal l hl
    calc l * a = a * l * a⁻¹ * a := by rw [h1]; group
      _ = a * l := by group
  have hwC : l⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hal x hx
    calc x * (l⁻¹ * a) = l⁻¹ * (l * x * l⁻¹) * l * l⁻¹ * a := by group
      _ = l⁻¹ * (a * x * a⁻¹) * l * l⁻¹ * a := by rw [h1]
      _ = l⁻¹ * a * x := by group
  have hl3 : l ^ 3 = 1 := by
    have hc : (⟨l ^ 3, L.pow_mem hl 3⟩ : L) ∈ Subgroup.center L := by
      refine mem_center_of_forall (L.pow_mem hl 3) fun x hx => ?_
      have h1 := conj_pow_eq hl hal 3 x hx
      rw [ha3] at h1
      simpa using h1.symm
    have h9 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨_, hc⟩)
    rw [hZ] at h9
    have h9' : (⟨l, hl⟩ : L) ^ 3 ^ 2 = 1 := by
      apply Subtype.ext
      have := congrArg (fun y : Subgroup.center L => ((y : L) : G)) h9
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← this, ← pow_mul]
      norm_num
    have := congrArg Subtype.val (h3 _ h9')
    simpa using this
  refine ⟨l⁻¹ * a, hwC, ?_, fun hw => haL ?_⟩
  · have hcomm : Commute l⁻¹ a := (Commute.inv_left hla)
    rw [hcomm.mul_pow, inv_pow, hl3, ha3, inv_one, one_mul]
  · have : a = l * (l⁻¹ * a) := by group
    rw [this]
    exact L.mul_mem hl hw

theorem item417InONRank_holds :
    Item417InONRank := by
  intro G _ _ L A E c m hconf hZ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model (X := L) this ⟨hZ, ⟨e⟩⟩
  have hm4 := hconf.2.2.2.1 A E c m hconf.2.2.2.2.1
  have hm3 := three_le_of_isQuad hconf.2.2.2.2.1
  by_contra hm
  have hm4' : m = 4 := by omega
  obtain ⟨hAmax, hcard, -⟩ := hconf.2.2.2.2.1
  have hA := hAmax.prop
  have h3 : ∀ l : L, l ^ 3 ^ 2 = 1 → l ^ 3 = 1 := fun l hl =>
    Sec13.ON134.pow_three_eq_one ψ hl
  obtain ⟨a, haA, haL⟩ : ∃ a ∈ A, a ∉ L := by
    by_contra hall
    push Not at hall
    have hAL : A ≤ L := fun a ha => hall a ha
    set B : Subgroup CFSG.RankThree.Native.ONTriple.GM := (A.subgroupOf L).map ψ.toMonoidHom with hB
    have hBcard : Nat.card B = 81 := by
      rw [hB, Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hcard, hm4']
      norm_num
    have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 4) (by rw [hBcard]; norm_num)
    have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 : (x : G) * y = y * x := congrArg Subtype.val (hA.1.is_comm.comm
        ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
      exact Subtype.ext h1
    have := card_le_27_of_abelian_model hB3 hBab
    omega
  obtain ⟨w, hwC, hw3, hwL⟩ := hconf.exists_centralizer_not_mem hZ h3 haA haL
  obtain ⟨D', hD'⟩ := exists_isE27_model
  obtain ⟨S', hS'1, hS'2, hD'S'⟩ := exists_twoGroup_model hD'
  set ι : CFSG.RankThree.Native.ONTriple.GM →* G := L.subtype.comp ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := L.subtype_injective.comp ψ.symm.injective
  have hιL : ∀ g, ι g ∈ L := fun g => (ψ.symm g).2
  have hD : Late.IsE27 (D'.map ι) := ⟨isElemAbelian_map ι hD'.1,
    by rw [Subgroup.card_map_of_injective hιinj, hD'.2]⟩
  have hS2 : IsPGroup 2 (S'.map ι) := hS'2.map ι
  have hS1 : S'.map ι ≠ ⊥ := fun hb =>
    hS'1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp hb)
  have hDS : D'.map ι ≤ Subgroup.normalizer ((S'.map ι : Subgroup G) : Set G) :=
    (Subgroup.map_mono hD'S').trans (Subgroup.le_normalizer_map ι)
  have hwD : ∀ d ∈ D'.map ι, d * w = w * d := by
    rintro _ ⟨d, -, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hwC _ (hιL d)
  have hwS : w ∈ Subgroup.normalizer ((S'.map ι : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, -, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hwC _ (hιL s)
  have hwmem := mem_of_commute_of_isE27 hconf.1 hD hS2 hS1 hDS hw3 hwD hwS
  obtain ⟨d, -, rfl⟩ := hwmem
  exact hwL (hιL d)

end Certs

end CFSG.RankThree.PartTwo.Sec4
