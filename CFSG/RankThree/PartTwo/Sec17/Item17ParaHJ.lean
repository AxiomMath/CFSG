module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

section Facts

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem Sec17Std.hj_facts (h1715 : Item1715) (h415 : Sec4.Item4_15)
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    omegaA A = {Subgroup.zpowers c} ∧ c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  obtain ⟨φJ⟩ := hJ
  rcases h1715 G A c L Y₀ h with ⟨hΩ, -, ⟨φ⟩, -⟩ | ⟨-, ⟨ψ⟩, -⟩
  · have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
      center_eq_bot_of_mulEquiv φJ (KFacts.KS14.center_nativeJ2_eq_bot h415)
    have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
    have hperf : Group.IsPerfect (Sec12.lBar c L) := by
      obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_lA.1
      have := (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_lA.1).1
      exact Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective
    have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine h.toSec13Data hperf φ
    refine ⟨hΩ, hcL, h9, ?_⟩
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.c_mem) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine h.c_pow_three
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => h.isE27.1.2 b hb.1) (fun b hb => h.commute_of_mem h.c_mem hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.isE27.2, hcard])).symm
  · exact ((KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1).false (φJ.symm.trans ψ)).elim

end Facts

section Sylow

variable {L : Subgroup G}

theorem card_sylow_eq_27 (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (S : Sylow 3 ↥L) : Nat.card (S : Subgroup ↥L) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π ((S : Subgroup ↥L) : Set ↥L) :=
    injOn_mk_of_isPGroup Nat.prime_three S.isPGroup'
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 _ hJ Sb _ rfl _ rfl
  rw [← card_map_eq_of_injOn π hinj, ← hSb]
  exact hHeis.2.1

theorem isSylowOf_of_card_27 (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hTL : T ≤ L) (hT3 : IsPGroup 3 T) (h27 : Nat.card T = 27) :
    IsSylowOf 3 T L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, hTQ⟩ := Item134SylowBarProof.exists_isSylowOf_le hTL hT3
  have hQ27 : Nat.card Q = 27 := by
    obtain ⟨Q', rfl⟩ := hQ
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact card_sylow_eq_27 h415 hJ Q'
  have heq : T = Q := Subgroup.eq_of_le_of_card_ge hTQ (by rw [hQ27, h27])
  exact heq ▸ hQ

theorem isSylowOf_of_le_of_le {p : ℕ} [Fact p.Prime] {T K : Subgroup G} (hT : IsSylowOf p T L)
    (hTK : T ≤ K) (hKL : K ≤ L) : IsSylowOf p T K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT ⊢
  obtain ⟨-, hT3, hdvd⟩ := hT
  refine ⟨hTK, hT3, fun h => hdvd ?_⟩
  exact h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T K L hTK hKL))

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_conj_eq' ?_
  rw [Subgroup.map_sup, Late.map_conj_eq_of_mem_normalizer hH,
    Late.map_conj_eq_of_mem_normalizer hK]

theorem exists_mem_conj_eq_inv (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hd1 : d ≠ 1) (hd : IsThreeCentralIn L d) : ∃ t ∈ L, t * d * t⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdL, S₀, hdS₀, hS₀d⟩ := hd
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S₀.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S₀ : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨hdb1, -⟩ := bar_facts_of_central hd'1 ⟨S₀, hdS₀, hS₀d⟩
  have hdbZ : π d' ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine ⟨hSb ▸ Subgroup.mem_map_of_mem π hdS₀, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [hSb] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hS₀d hx)]
  obtain ⟨gb, hgb⟩ := Item134SylowBarProof.j2_exists_conj_eq_inv h415 hJ Sb hdb1 hdbZ
  have hD3 : IsPGroup 3 (Subgroup.zpowers d') :=
    S₀.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS₀)
  have hgbN : gb ∈ Subgroup.normalizer (((Subgroup.zpowers d').map π :
      Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, MonoidHom.map_zpowers] at hy ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hgb]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers _)) k
  rw [normalizer_map_mk_eq hD3] at hgbN
  obtain ⟨t, htN, rfl⟩ := hgbN
  have htd : t * d' * t⁻¹ ∈ Subgroup.zpowers d' :=
    (Subgroup.mem_normalizer_iff.mp htN d').mp (Subgroup.mem_zpowers d')
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hD3
  have heq : t * d' * t⁻¹ = d'⁻¹ := hinj htd (inv_mem (Subgroup.mem_zpowers d'))
    (by rw [map_inv, map_mul, map_mul, map_inv]; exact hgb)
  exact ⟨t, t.2, congrArg Subtype.val heq⟩

omit [Finite G] in
theorem inf_zpowers_eq_bot [Finite G] {H : Subgroup G} {w : G} (hw : orderOf w = 3)
    (hwH : w ∉ H) : H ⊓ Subgroup.zpowers w = ⊥ := by
  have hdvd : Nat.card (H ⊓ Subgroup.zpowers w : Subgroup G) ∣ 3 := by
    rw [← hw, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hwH
    have heq : H ⊓ Subgroup.zpowers w = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hw])
    exact (heq ▸ inf_le_left : Subgroup.zpowers w ≤ H) (Subgroup.mem_zpowers w)

theorem isSylowOf_inf_sup_zpowers (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {A : Subgroup G} (hA : IsE27 A) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (hwnA : w ∉ A)
    (hw : orderOf w = 3) :
    IsSylowOf 3 ((A ⊓ L) ⊔ Subgroup.zpowers w) L ∧
      Subgroup.zpowers w ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr hwA)
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hwL))
  have hAL3 : IsPGroup 3 ↥(A ⊓ L) := hA.isPGroup.to_le inf_le_left
  have hw3' : IsPGroup 3 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hw, pow_one])
  have hT3 : IsPGroup 3 ((A ⊓ L) ⊔ Subgroup.zpowers w : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hAL3 hw3' hwN
  have hdisj : Disjoint (A ⊓ L) (Subgroup.zpowers w) :=
    disjoint_iff.mpr (inf_zpowers_eq_bot hw (fun h => hwnA (Subgroup.mem_inf.mp h).1))
  have h27 : Nat.card ((A ⊓ L) ⊔ Subgroup.zpowers w : Subgroup G) = 27 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hwN hdisj, h9,
      Nat.card_zpowers, hw]
  exact ⟨isSylowOf_of_card_27 h415 hJ (sup_le inf_le_right (Subgroup.zpowers_le.mpr hwL)) hT3
    h27, hwN⟩

theorem exists_central_mem {T E : Subgroup G} (hT : IsSylowOf 3 T L) (hET : E ≤ T)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) (hE1 : E ≠ ⊥) :
    ∃ d ∈ E, d ≠ 1 ∧ T ≤ Subgroup.centralizer ({d} : Set G) ∧ IsThreeCentralIn L d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
  have hN : (E.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTE
  have hne : E.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hE1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hET hx⟩ : ↥T) ∈ E.subgroupOf T := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hxE, hxZ⟩ := Subgroup.mem_inf.mp x.2
  set d : G := ((x : ↥T) : G) with hd
  have hd1 : d ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
  have hTd : T ≤ Subgroup.centralizer ({d} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩)
  have hdT : d ∈ T := (x : ↥T).2
  have hTL : T ≤ L := hT.le
  refine ⟨d, hxE, hd1, hTd, hTL hdT, ?_⟩
  obtain ⟨Q, hQ⟩ := hT
  refine ⟨Q, ?_, fun q hq => ?_⟩
  · have : d ∈ (Q : Subgroup ↥L).map L.subtype := hQ ▸ hdT
    obtain ⟨q, hq, hqd⟩ := this
    have : q = ⟨d, hTL hdT⟩ := Subtype.ext hqd
    exact this ▸ hq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hqT : (q : G) ∈ T := hQ ▸ Subgroup.mem_map_of_mem L.subtype hq
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hTd hqT))

theorem exists_mem_normalizer_inverts (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hT : IsSylowOf 3 T L) {d : G} (hd1 : d ≠ 1) (hdT : d ∈ T)
    (hTd : T ≤ Subgroup.centralizer ({d} : Set G)) :
    ∃ r ∈ L, r ∈ Subgroup.normalizer (T : Set G) ∧ r * d * r⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTL : T ≤ L := hT.le
  have hd3c : IsThreeCentralIn L d := by
    obtain ⟨Q, hQ⟩ := hT
    refine ⟨hTL hdT, Q, ?_, fun q hq => ?_⟩
    · have : d ∈ (Q : Subgroup ↥L).map L.subtype := hQ ▸ hdT
      obtain ⟨q, hq, hqd⟩ := this
      have : q = ⟨d, hTL hdT⟩ := Subtype.ext hqd
      exact this ▸ hq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hqT : (q : G) ∈ T := hQ ▸ Subgroup.mem_map_of_mem L.subtype hq
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hTd hqT))
  obtain ⟨t, htL, htd⟩ := exists_mem_conj_eq_inv h415 hJ hd1 hd3c
  set K := L ⊓ Subgroup.centralizer ({d} : Set G) with hK
  have htd' : t * d⁻¹ * t⁻¹ = d := by
    have := congrArg (fun x => x⁻¹) htd
    simpa [mul_assoc] using this
  have hTK : IsSylowOf 3 T K := isSylowOf_of_le_of_le hT (le_inf hTL hTd) inf_le_left
  set T' := T.map (MulAut.conj t).toMonoidHom with hT'
  have hT'L : IsSylowOf 3 T' L := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem htL (hTL hx)) (inv_mem htL)
    · rw [hT', Subgroup.card_map_of_injective (MulAut.conj t).injective]
      exact hT.card_eq
  have hT'K : IsSylowOf 3 T' K := by
    refine isSylowOf_of_le_of_le hT'L (le_inf hT'L.le ?_) inf_le_left
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp (hTd hx)
    change t * x * t⁻¹ * d = d * (t * x * t⁻¹)
    calc t * x * t⁻¹ * d = t * x * t⁻¹ * (t * d⁻¹ * t⁻¹) := by rw [htd']
      _ = t * (x * d⁻¹) * t⁻¹ := by group
      _ = t * (d⁻¹ * x) * t⁻¹ := by
          rw [(Commute.inv_right (show Commute x d from hxd)).eq]
      _ = (t * d⁻¹ * t⁻¹) * (t * x * t⁻¹) := by group
      _ = d * (t * x * t⁻¹) := by rw [htd']
  obtain ⟨m, hmK, hm⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hTK hT'K
  have hmd : m * d = d * m := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmK).2
  refine ⟨m⁻¹ * t, mul_mem (inv_mem (Subgroup.mem_inf.mp hmK).1) htL, ?_, ?_⟩
  · refine mem_normalizer_of_map_conj_eq' ?_
    rw [map_conj_mul, ← hT', hm, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  · have hmd2 : d⁻¹ * m = m * d⁻¹ := (Commute.inv_left (show Commute m d from hmd).symm).eq
    have hmd' : m⁻¹ * d⁻¹ * m = d⁻¹ := by
      rw [mul_assoc, hmd2, inv_mul_cancel_left]
    calc m⁻¹ * t * d * (m⁻¹ * t)⁻¹ = m⁻¹ * (t * d * t⁻¹) * m := by group
      _ = d⁻¹ := by rw [htd, hmd']

end Sylow

section Data

variable {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G} {w : G}
  {Q : Subgroup G}

theorem Sec17W.exists_d_r (h1715 : Item1715) (h1721 : Item1721) (h415 : Sec4.Item4_15)
    (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    ∃ d r₀ : G, d ∈ A ⊓ L ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
      r₀ ∈ L ⊓ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) ∧
      r₀ * d * r₀⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨-, -, h9, hAeq⟩ := h.hj_facts h1715 h415 hJ
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  obtain ⟨hTsyl, hwN⟩ := isSylowOf_inf_sup_zpowers h415 hJ h.isE27 h9 hwA hwL h.w_not_mem
    h.orderOf_w
  set T := (A ⊓ L) ⊔ Subgroup.zpowers w with hTdef
  have hTE : T ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hwN
  have hE1 : A ⊓ L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h9
    omega
  obtain ⟨d, hdE, hd1, hTd, hd3c⟩ := exists_central_mem hTsyl le_sup_left hTE hE1
  obtain ⟨r₀, hr₀L, hr₀T, hr₀d⟩ := exists_mem_normalizer_inverts h415 hJ hTsyl hd1
    (le_sup_left (a := A ⊓ L) hdE) hTd
  refine ⟨d, r₀, hdE, hd1, hd3c, Subgroup.mem_inf.mpr ⟨hr₀L, ?_⟩, hr₀d⟩
  have hsup : A ⊔ Subgroup.zpowers w = Subgroup.zpowers c ⊔ T := by
    conv_lhs => rw [hAeq]
    rw [hTdef, sup_assoc]
  rw [hsup]
  have hr₀c : r₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (h.le_centralizer_c hr₀L)
  exact mem_normalizer_sup hr₀c hr₀T

end Data

end CFSG.RankThree.PartTwo.Sec17
