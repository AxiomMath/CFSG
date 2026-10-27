module

import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.Quasithin.Background.A318PC7
import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

section Theta

variable {L : Subgroup G}

theorem mem_thetaQuotCentralizer_iff {g : G} :
    g ∈ Sec4.thetaQuotCentralizer L ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G), ∀ x : ↥L,
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (L.normalizerMonoidHom ⟨g, hg⟩ x) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) x := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.2, fun x => ?_⟩
    have h1 : (Sec4.thetaQuotMulAut L) (L.normalizerMonoidHom n) = 1 := hn
    exact congrArg (fun σ : MulAut _ => σ (QuotientGroup.mk' _ x)) h1
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    change (Sec4.thetaQuotMulAut L) (L.normalizerMonoidHom ⟨g, hg⟩) = 1
    ext y
    induction y using QuotientGroup.induction_on with
    | H x => exact h x

theorem mem_thetaQuotCentralizer_of_commute {g : G} (hg : ∀ x ∈ L, g * x = x * g) :
    g ∈ Sec4.thetaQuotCentralizer L := by
  have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => by
      rw [hg x hx, mul_inv_cancel_right]
      exact hx
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hgN, fun x => ?_⟩
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hg x x.2, mul_inv_cancel_right]

theorem exists_inv_mul_mem_thetaQuotCentralizer_of_sylow
    (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {S : Subgroup G} (hS : IsSylowOf 3 S L) {ρ : G}
    (hρL : ρ ∈ Subgroup.normalizer (L : Set G)) (hρS : ρ ∈ Subgroup.normalizer (S : Set G))
    {k : ℕ} (hρ : ρ ^ 3 ^ k = 1) :
    ∃ s ∈ S, s⁻¹ * ρ ∈ Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨φJ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φJ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  obtain ⟨S', rfl⟩ := hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set ρ' : Subgroup.normalizer (L : Set G) := ⟨ρ, hρL⟩ with hρ'
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ρ') with hσ
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : ρ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hρ)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨q, hq⟩ := Item134SylowBarProof.mem_range_conj_of_pow_three_pow hJ σ hσk
  have hσapp : ∀ x : ↥L, σ (π x) = π (L.normalizerMonoidHom ρ' x) := fun x => rfl
  have hqapp : ∀ y, q * y * q⁻¹ = σ y := fun y => by rw [← hq]; rfl
  have hρS' : ∀ x ∈ (S' : Subgroup ↥L), L.normalizerMonoidHom ρ' x ∈ (S' : Subgroup ↥L) := by
    intro x hx
    have h1 : ρ * (x : G) * ρ⁻¹ ∈ (S' : Subgroup ↥L).map L.subtype :=
      (Subgroup.mem_normalizer_iff.mp hρS x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = L.normalizerMonoidHom ρ' x := Subtype.ext hyx
    exact this ▸ hy
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S' : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  have hqN : q ∈ Subgroup.normalizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
      Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hqapp]
    rw [SetLike.mem_coe, hSb] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hσapp]
    exact Subgroup.mem_map_of_mem π (hρS' x hx)
  have hq3 : q ^ 3 ^ k = 1 := by
    have hc : q ^ 3 ^ k ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : MulAut.conj (q ^ 3 ^ k) = 1 := by rw [map_pow, hq, hσk]
      have h2 := congrArg (fun φ : MulAut _ => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * q ^ 3 ^ k = q ^ 3 ^ k * y * (q ^ 3 ^ k)⁻¹ * q ^ 3 ^ k := by rw [h2]
        _ = q ^ 3 ^ k * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hqS : q ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    have hdvd : orderOf q ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hq3
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hp : IsPGroup 3 (Subgroup.zpowers q) :=
      IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
    have hsup := hp.to_sup_of_normal_right' Sb.isPGroup' (Subgroup.zpowers_le.mpr hqN)
    have heq := Sb.3 hsup le_sup_right
    exact heq ▸ (le_sup_left : Subgroup.zpowers q ≤ _) (Subgroup.mem_zpowers q)
  rw [hSb] at hqS
  obtain ⟨s₁, hs₁, hs₁q⟩ := hqS
  refine ⟨(s₁ : G), ⟨s₁, hs₁, rfl⟩, ?_⟩
  have hs₁N : (s₁ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer s₁.2
  have hmemN : (s₁ : G)⁻¹ * ρ ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hs₁N) hρL
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hmemN, fun x => ?_⟩
  have heq : L.normalizerMonoidHom ⟨(s₁ : G)⁻¹ * ρ, hmemN⟩ x =
      s₁⁻¹ * L.normalizerMonoidHom ρ' x * s₁ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    show (s₁ : G)⁻¹ * ρ * (x : G) * ((s₁ : G)⁻¹ * ρ)⁻¹ = (s₁ : G)⁻¹ * (ρ * (x : G) * ρ⁻¹) * s₁
    group
  rw [heq, map_mul, map_mul, map_inv, ← hσapp, ← hqapp, hs₁q]
  group
  rfl

end Theta

section Commutator

variable {L : Subgroup G}

theorem commutator_mem_of_hj
    (h415 : Sec4.Item4_15)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {A T : Subgroup G} {c : G} (hAF : A ∈ partTwoF G)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hc : orderOf c = 3) (hT3 : IsPGroup 3 T) (hAT : A ≤ T)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowOf 3 (T ⊓ L) L) :
    ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨φJ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φJ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Y := T ⊓ Sec4.thetaQuotCentralizer L with hYdef
  have hcA : c ∈ A := hAeq ▸ (le_sup_left : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx)).symm
  have hcY : c ∈ Y := ⟨hAT hcA, mem_thetaQuotCentralizer_of_commute hcL⟩
  set S' := (T ⊓ L).subgroupOf L with hS'
  have hS'3 : IsPGroup 3 S' := (hT3.to_le inf_le_left).comap_of_injective L.subtype
    L.subtype_injective
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hS'3
  have hYS : ∀ y ∈ Y, ∀ s ∈ T ⊓ L, y * s = s * y := by
    intro y hy s hs
    obtain ⟨hyN, hytriv⟩ := mem_thetaQuotCentralizer_iff.mp hy.2
    have hysT : y * s * y⁻¹ ∈ T := mul_mem (mul_mem hy.1 hs.1) (inv_mem hy.1)
    have hysL : y * s * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN s).mp hs.2
    have h1 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = L.normalizerMonoidHom ⟨y, hyN⟩ ⟨s, hs.2⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hyN⟩ ⟨s, hs.2⟩).symm
    have h2 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = ⟨s, hs.2⟩ := by
      refine hinj (show (⟨y * s * y⁻¹, hysL⟩ : ↥L) ∈ S' from ⟨hysT, hysL⟩)
        (show (⟨s, hs.2⟩ : ↥L) ∈ S' from hs) ?_
      rw [h1]
      exact hytriv ⟨s, hs.2⟩
    have h3 : y * s * y⁻¹ = s := congrArg Subtype.val h2
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h3]
  have hAL : A ⊓ L ≤ T ⊓ L := inf_le_inf_right L hAT
  have hY3 : ∀ z ∈ Y, z ^ 3 = 1 → z ∈ Subgroup.zpowers c := by
    intro z hz hz3
    have hAz : A ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun e he => ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hTc hz.1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hYS z hz e (hAL he)).symm
    have hzA : z ∈ A := mem_of_mem_partTwoF hAF hz3 hAz
    have hcAL : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun e he => (hcL e he.2).symm
    rw [hAeq] at hzA
    obtain ⟨k, e, he, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcAL hzA
    have heY : e ∈ Y := by
      have : e = (c ^ k)⁻¹ * (c ^ k * e) := by group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hcY k)) hz
    obtain ⟨heN, hetriv⟩ := mem_thetaQuotCentralizer_iff.mp heY.2
    have hecen : π ⟨e, he.2⟩ ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        have h1 : L.normalizerMonoidHom ⟨e, heN⟩ x = ⟨e, he.2⟩ * x * ⟨e, he.2⟩⁻¹ :=
          Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)
        have h2 := hetriv x
        rw [h1, map_mul, map_mul, map_inv] at h2
        change π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x
        calc π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x * (π ⟨e, he.2⟩)⁻¹ * π ⟨e, he.2⟩ := by
              rw [h2]
          _ = π ⟨e, he.2⟩ * π x := by group
    rw [hZ, Subgroup.mem_bot] at hecen
    have he1 : (⟨e, he.2⟩ : ↥L) = 1 :=
      hinj (show (⟨e, he.2⟩ : ↥L) ∈ S' from hAL he) (one_mem S') (by rw [hecen, map_one])
    have he1' : e = 1 := congrArg Subtype.val he1
    rw [he1', mul_one]
    exact zpow_mem (Subgroup.mem_zpowers c) k
  have hY3' : IsPGroup 3 Y := hT3.to_le inf_le_left
  have hYcyc : IsCyclic Y := by
    refine CFSG.Quasithin.A318P.isCyclic_of_unique_three hY3' (Z := Subgroup.zpowers c)
      (by rw [Nat.card_zpowers, hc]) fun r hr hr3 => hY3 r hr ?_
    rw [← hr3]
    exact pow_orderOf_eq_one r
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    Sec13.mul_comm_of_isCyclic (P := Y) ha hb
  have hdecomp : ∀ t ∈ T, ∃ s ∈ T ⊓ L, s⁻¹ * t ∈ Y := by
    intro t ht
    obtain ⟨k, hk⟩ := hT3 ⟨t, ht⟩
    have htk : t ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have htS : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      le_normalizer_inf (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer ht))
        (Subgroup.zpowers_le.mpr (hTL ht)) (Subgroup.mem_zpowers t)
    obtain ⟨s, hs, hsY⟩ :=
      exists_inv_mul_mem_thetaQuotCentralizer_of_sylow h415 hJ hS (hTL ht) htS htk
    exact ⟨s, hs, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hs).1) ht, hsY⟩⟩
  intro x hx y hy
  obtain ⟨a, ha, hb⟩ := hdecomp x hx
  obtain ⟨c', hc', hd⟩ := hdecomp y hy
  set b := a⁻¹ * x with hbdef
  set d := c'⁻¹ * y with hddef
  have hx' : x = a * b := by rw [hbdef]; group
  have hy' : y = c' * d := by rw [hddef]; group
  have hbc : b * c' = c' * b := hYS b hb c' hc'
  have hbd : b * d = d * b := hYcomm b hb d hd
  have hda : d * a = a * d := hYS d hd a ha
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (show Commute d a from hda)).eq
  have heq : x * y * x⁻¹ * y⁻¹ = a * c' * a⁻¹ * c'⁻¹ := by
    rw [hx', hy']
    calc a * b * (c' * d) * (a * b)⁻¹ * (c' * d)⁻¹
        = a * (b * c') * d * b⁻¹ * a⁻¹ * d⁻¹ * c'⁻¹ := by group
      _ = a * c' * (b * d) * b⁻¹ * a⁻¹ * d⁻¹ * c'⁻¹ := by rw [hbc]; group
      _ = a * c' * d * a⁻¹ * d⁻¹ * c'⁻¹ := by rw [hbd]; group
      _ = a * c' * (d * a⁻¹) * d⁻¹ * c'⁻¹ := by group
      _ = a * c' * a⁻¹ * c'⁻¹ := by rw [hda']; group
  rw [heq]
  exact mul_mem (mul_mem (mul_mem ha.2 hc'.2) (inv_mem ha.2)) (inv_mem hc'.2)

end Commutator

section Transfer

theorem exists_conj_eq_inv_of_weaklyClosed (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {c : G} (hc : orderOf c = 3) {T L : Subgroup G}
    (hT : IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G))) (hcT : c ∈ T)
    (hweak : ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L) (hcL : c ∉ L) :
    ∃ g : G, g * c * g⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  push Not at hno
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx
  have hNC : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G), g * c * g⁻¹ = c := by
    intro g hg
    have hmem : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hg c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h3 : ((orderOf c : ℕ) : ℤ) = 3 := by rw [hc]; norm_num
    have hk' : c ^ (k % 3) = g * c * g⁻¹ := by rw [← hk, ← h3, zpow_mod_orderOf]
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hge : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    set m := k % 3 with hm
    interval_cases m
    · exfalso
      apply hc1
      rw [zpow_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hk'
      exact hk'
    · rw [zpow_one] at hk'
      exact hk'.symm
    · exfalso
      apply hno g
      rw [← hk', show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hc3]
  have hCc : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G),
      g ∈ Subgroup.centralizer ({c} : Set G) := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hNC g hg
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h]
  have hTG : ¬ 3 ∣ T.index := by
    obtain ⟨T', hTT'⟩ := hT.isPGroup.exists_le_sylow
    have heq : T = (T' : Subgroup G) := by
      by_contra hne
      obtain ⟨x, hxT', hxT, hxN⟩ :=
        Late.exists_mem_normalizer_not_mem_of_lt T'.isPGroup' (lt_of_le_of_ne hTT' hne)
      have hle : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ≤ T := by
        rw [MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.mpr ((Subgroup.mem_normalizer_iff.mp hxN c).mp hcT)
      have hxH := hweak x (hle.trans (hT.le.trans hCN))
      have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
        hCc x (mem_normalizer_of_map_conj_eq' hxH)
      have hsup3 : IsPGroup 3 (T ⊔ Subgroup.zpowers x : Subgroup G) :=
        T'.isPGroup'.to_le (sup_le hTT' (Subgroup.zpowers_le.mpr hxT'))
      have h := hT.eq_of_le le_sup_left (sup_le hT.le (Subgroup.zpowers_le.mpr hxC)) hsup3
      exact hxT (h ▸ (le_sup_right : Subgroup.zpowers x ≤ T ⊔ Subgroup.zpowers x)
        (Subgroup.mem_zpowers x))
    rw [heq]
    exact T'.not_dvd_index
  let ϕ : ↥T →* Abelianization ↥T := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * c ^ k * g₀ ∈ T → g₀⁻¹ * c ^ k * g₀ = c ^ k := by
    intro k g₀ hk
    by_cases hck : c ^ k = 1
    · rw [hck, mul_one, inv_mul_cancel]
    · have h3k : ¬ 3 ∣ k := fun h3 => hck (by
        obtain ⟨j, rfl⟩ := h3
        rw [pow_mul, hc3, one_pow])
      have hgcd : k.gcd (orderOf c) = 1 := by
        rw [hc]
        exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3k))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_iff.mpr hgcd)
      have hconj : g₀⁻¹ * c * g₀ = (g₀⁻¹ * c ^ k * g₀) ^ j := by
        have e1 : (g₀⁻¹ * c ^ k * g₀) ^ j = g₀⁻¹ * (c ^ k) ^ j * g₀ := by
          have := conj_zpow (a := g₀⁻¹) (b := c ^ k) (i := j)
          rwa [inv_inv] at this
        rw [e1, hj]
      have hle : (Subgroup.zpowers c).map (MulAut.conj g₀⁻¹).toMonoidHom ≤ T := by
        rw [MonoidHom.map_zpowers]
        refine Subgroup.zpowers_le.mpr ?_
        change g₀⁻¹ * c * g₀⁻¹⁻¹ ∈ T
        rw [inv_inv, hconj]
        exact zpow_mem hk j
      have hx := hweak g₀⁻¹ (hle.trans (hT.le.trans hCN))
      have hg₀ := hNC g₀⁻¹ (mem_normalizer_of_map_conj_eq' hx)
      rw [inv_inv] at hg₀
      have e2 : g₀⁻¹ * c ^ k * g₀ = (g₀⁻¹ * c * g₀) ^ k := by
        have := conj_pow (a := g₀⁻¹) (b := c) (i := k)
        rw [inv_inv] at this
        exact this.symm
      rw [e2, hg₀]
  have hV := MonoidHom.transfer_eq_pow ϕ c key
  have hV1 : ϕ.transfer c = 1 := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ϕ.transfer).ker with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ϕ.transfer (a * b) = ϕ.transfer (b * a) := by rw [map_mul, map_mul, mul_comm]
      exact (MonoidHom.ker_eq_bot_iff _).mp hbot this
    · exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top c)
  rw [hV] at hV1
  have hmem : (⟨c ^ T.index, MonoidHom.transfer_eq_pow_aux c key⟩ : ↥T) ∈ commutator ↥T := by
    rw [← Abelianization.ker_of]
    exact hV1
  have hcomm' : commutator ↥T ≤ L.subgroupOf T := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    simpa using hcomm x x.2 y y.2
  have hcnL : c ^ T.index ∈ L := hcomm' hmem
  have hgcd : T.index.gcd (orderOf c) = 1 := by
    rw [hc]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hTG))
  exact hcL ((Subgroup.zpowers_le.mpr hcnL) (mem_zpowers_pow_iff.mpr hgcd))

end Transfer

end CFSG.RankThree.PartTwo.Sec17
