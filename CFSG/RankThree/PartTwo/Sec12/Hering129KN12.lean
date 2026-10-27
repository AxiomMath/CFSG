module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KN9
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN10
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN11
import CFSG.RankThree.PartTwo.Sec12.Hering129KEj
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec12.Hering129GHJ
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLE81
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofK

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering129KN12

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_zpowers_sup {n x : G} {V : Subgroup G} (hnx : n * x = x * n)
    (hnV : n ∈ Subgroup.normalizer (V : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers x ⊔ V : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hle : Subgroup.zpowers x ⊔ V ≤
      (Subgroup.zpowers x ⊔ V).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le ?_ fun v hv => ?_
    · rw [Subgroup.zpowers_le]
      show n * x * n⁻¹ ∈ Subgroup.zpowers x ⊔ V
      rw [hnx, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    · show n * v * n⁻¹ ∈ Subgroup.zpowers x ⊔ V
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hnV v).mp hv)
  exact hle hy

end Hering129KN12


theorem end_L3_of_config (hDeg : Gap129HessL3Deg)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {b a : G}
    {K S : Subgroup G} (cfg : Cfg129 G A c L b a K S)
    {q : TauCeti.PrimePower}
    (hq : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card) (hqm : ¬ PiModNine q.card)
    {x : G} (hxD : x ∈ D129 a b) (hxb : x ∉ Subgroup.zpowers b) (hxL : x ∉ L)
    {Y : Subgroup G} (hY : Core129 A c x Y) (hxY : x ∉ Y) (hcY : c ∈ Y)
    (hX : ∃ X : Subgroup G, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set G) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set G))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)))
    (hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField)
    (hty : ∃ (p e : ℕ) (_ : Fact p.Prime),
      Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e)
    (hR2 : IsPGroup 2 (aschbacherSolvableCore 3 Y))
    {Y' J : Subgroup G} (hJ : JData129 A c L Y' J) (hbJ : b ∈ J)
    {r : TauCeti.PrimePower} (hr : Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card)
    (hrm : ¬ PiModNine r.card) :
    ∃ F : Subgroup G, Late.IsE27 F ∧ c ∈ F ∧ F ≤ lcBar c L ∧
      ¬ Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hcA : c ∈ A := hstd.mem_A
  have hc1 : c ≠ 1 := hstd.ne_one
  have hL : L ∈ thetaComponentsAt 3 c := hstd.mem_thetaComponentsAt
  have hcL : c ∈ L := hstd.mem_L
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  have hcD : c ∉ D129 a b := cfg.not_mem_D
  obtain ⟨hgen, hbxc⟩ := cfg.gen_facts hxD hxb
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hAe.2 b hbA) hb1
  have hcx : c ∉ Subgroup.zpowers x := fun h => hcD ((Subgroup.zpowers_le.mpr hxD) h)
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hAle : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
  have hxc : ∀ w ∈ Y ⊔ A, x * w = w * x := fun w hw =>
    (Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hYle hAle) hw)).symm
  have hYp : Group.IsPerfect ↥Y := Sec6.isPerfect_of_mem_thetaComponentsAt hYx
  have hYq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYx
  obtain ⟨hJc, hJL, hcJ, -, hJA, -⟩ := hJ
  obtain ⟨⟨t, htY, ht2, hbt, htc⟩, hmove⟩ := exists_t_move_sub hDeg hAN hYp hYq hAe hA27 hgen
    hx1 hxc hxY hcY hbxc hAC hX hkind hty hR2
  have htx : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp (hYle htY)
  obtain ⟨i, j, hxij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hAc a haA b hbA) hxD
  have ha'A : a ^ i ∈ A := A.zpow_mem haA i
  have hb'A : b ^ j ∈ A := A.zpow_mem hbA j
  have ha'L : a ^ i ∈ L := L.zpow_mem haL i
  have hb'J : b ^ j ∈ J := J.zpow_mem hbJ j
  have ha'1 : a ^ i ≠ 1 := by
    intro h
    apply hxb
    rw [hxij, h, one_mul]
    exact Subgroup.zpow_mem_zpowers b j
  have hb'1 : b ^ j ≠ 1 := by
    intro h
    apply hxL
    rw [hxij, h, mul_one]
    exact ha'L
  have ha'c : a ^ i ∉ Subgroup.zpowers c := fun h =>
    cfg.ha_not (mem_of_mem_zpowers_of_ne_one ha3 (Subgroup.zpow_mem_zpowers a i) ha'1 h)
  have hb'c : b ^ j ∉ Subgroup.zpowers c := fun h =>
    cfg.hb_not (mem_of_mem_zpowers_of_ne_one hb3 (Subgroup.zpow_mem_zpowers b j) hb'1 h)
  have ha'B : a ^ i ∉ Sec4.thetaQuotCentralizer L := fun h =>
    haB (mem_of_mem_zpowers_of_ne_one ha3 (Subgroup.zpow_mem_zpowers a i) ha'1 h)
  have htb' : t * b ^ j = b ^ j * t := (Commute.zpow_right (show Commute t b from hbt.symm) j).eq
  have hta' : t * a ^ i = a ^ i * t := by
    have h : a ^ i = x * (b ^ j)⁻¹ := by rw [hxij, mul_inv_cancel_right]
    rw [h]
    exact ((show Commute t x from htx).mul_right (show Commute t (b ^ j) from htb').inv_right).eq
  have hbθ : b ∉ Sec4.thetaQuotCentralizer J := by
    intro h
    have h' : b ∈ A ⊓ L := by
      rw [← hJA]
      exact ⟨hbA, h⟩
    exact hbL h'.2
  have htLn : t ∈ Subgroup.normalizer (L : Set G) := conj_eq_of_comm_inv hL ha'L hta' htc ha'B
  have htJn : t ∈ Subgroup.normalizer (J : Set G) :=
    conj_eq_of_comm_inv hJc hbJ hbt.symm htc hbθ
  have htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp htLn l).mp hl
  have htJ : ∀ l ∈ J, t * l * t⁻¹ ∈ J := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp htJn l).mp hl
  have hcN : c ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_commute (hAc x hxA c hcA)
  have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Item125Diag.mem_normalizer_zpowers_of_conj_mem
      (by rw [htc]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have ha'N : a ^ i ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_commute (hAc _ ha'A c hcA)
  have hb'N : b ^ j ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_commute (hAc _ hb'A c hcA)
  have hloc := endLocalX_lBar hL hJc (Ne.symm hJL) hcL hcJ hAe hcA ha'A hb'A hc1 ha'L hb'J ha'c
    hb'c hq hqm hr hrm htL htJ hta' htb' htc ht2 (xN := ⟨x, hxN⟩) (tN := ⟨t, htN⟩)
    (cN := ⟨c, hcN⟩) hxij rfl rfl
  have hT3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3
      ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    three_not_dvd_card_aschbacherSolvableCore
  have ht2N : IsPGroup 2 (Subgroup.zpowers
      (⟨t, htN⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)))) :=
    (ht2.comap_of_injective _ (Subgroup.subtype_injective _)).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers t)))
  have hYn : ∀ m : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)),
      m * ⟨x, hxN⟩ = ⟨x, hxN⟩ * m → m * ⟨c, hcN⟩ = ⟨c, hcN⟩ * m →
      ∀ y ∈ Y.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)),
        m * y * m⁻¹ ∈ Y.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    intro m hmx hmc y hy
    have hmY := mem_normalizer_of_commute_core hcA hcY hY hcx (congrArg Subtype.val hmx)
      (congrArg Subtype.val hmc)
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp hmY y).mp hy
  obtain ⟨V, t', hVY, hVab, hV9, hcV, hVU, hVx, ht'Y, -, -, -, ht'V⟩ :=
    exists_inverted_lift _ hT3 (x := ⟨x, hxN⟩) (c := ⟨c, hcN⟩) (t := ⟨t, htN⟩)
      (Subtype.ext hx3) (Subtype.ext hc3) (fun h => hc1 (congrArg Subtype.val h))
      (Subtype.ext (hAc x hxA c hcA)) (Subtype.ext htx) (Subtype.ext htc) ht2N
      (Subgroup.mem_subgroupOf.mpr htY) hYn hloc
  set V' : Subgroup G := V.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype
    with hV'
  have hV'Y : V' ≤ Y := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hVY hv)
  have hV'ab : CFSG.Assembly.IsElemAbelian 3 V' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ V hVab
  have hV'9 : Nat.card V' = 9 := by
    rw [hV', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hV9]
  have hcV' : c ∈ V' := ⟨⟨c, hcN⟩, hcV, rfl⟩
  have hxV' : x ∉ V' := fun h => hxY (hV'Y h)
  have hV'x : ∀ v ∈ V', x * v = v * x := by
    rintro _ ⟨v, hv, rfl⟩
    exact (congrArg Subtype.val (hVx v hv)).symm
  obtain ⟨hFab, hF27⟩ :=
    Sec13.isElemAbelian_zpowers_sup_of_card_nine hx3 hxV' le_rfl hV'9 hV'ab.2 hV'x
  refine ⟨Subgroup.zpowers x ⊔ V', ⟨hFab, hF27⟩, Subgroup.mem_sup_right hcV', ?_, ?_⟩
  ·
    have hJC : lBar c J ≤ Subgroup.centralizer (lBar c L : Set _) := fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Sec13.Item131bProof.lBar_commute_of_ne hL hJc (Ne.symm hJL) hz hy
    have hmem : ∀ n : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)),
        QuotientGroup.mk' _ n ∈ lBar c L ⊔ lBar c J → (n : G) ∈ lcBar c L := fun n hn =>
      ⟨n, sup_le_sup_left hJC _ hn, rfl⟩
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      have hx' : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))) =
          ⟨a ^ i, ha'N⟩ * ⟨b ^ j, hb'N⟩ := Subtype.ext hxij
      refine hmem ⟨x, hxN⟩ ?_
      rw [hx', map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨⟨a ^ i, ha'N⟩, Subgroup.mem_subgroupOf.mpr ha'L, rfl⟩)
        (Subgroup.mem_sup_right ⟨⟨b ^ j, hb'N⟩, Subgroup.mem_subgroupOf.mpr hb'J, rfl⟩)
    · rintro _ ⟨v, hv, rfl⟩
      exact hmem v (hVU v hv)
  ·
    have hinv : ∀ v ∈ V', (t' : G) * v * (t' : G)⁻¹ = v⁻¹ := by
      rintro _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val (ht'V v hv)
    obtain ⟨n, ⟨hnY, hnV⟩, hnc⟩ :=
      hmove V' hV'Y hV'ab hV'9 hcV' ⟨t', Subgroup.mem_subgroupOf.mp ht'Y, hinv⟩
    intro hle
    have hnx : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.mp (hYle hnY)
    exact hnc ((Subgroup.mem_normalizer_iff.mp
      (hle (Hering129KN12.mem_normalizer_zpowers_sup hnx hnV)) c).mp (Subgroup.mem_zpowers c))

end CFSG.RankThree.PartTwo.Sec12
