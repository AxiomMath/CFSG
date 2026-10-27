module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.Asc83Table (Automizer automizerCongr)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {e g : G} (h : g * e = e * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
  have hc : ∀ k : ℤ, g * e ^ k * g⁻¹ = e ^ k := fun k => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, mul_inv_cancel_right]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hc k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc e ^ k = g⁻¹ * (g * e ^ k * g⁻¹) * g := by group
      _ = g⁻¹ * e ^ k * g := by rw [hc k]
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hk]
      _ = y := by group

theorem eq_of_mk_eq {L : Subgroup G} {S : Subgroup L} (hS : IsPGroup 3 S) {s t : L}
    (hs : s ∈ S) (ht : t ∈ S)
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3 L) s =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) t) : s = t :=
  injOn_mk_of_isPGroup Nat.prime_three hS hs ht h

theorem card_map_mk {L : Subgroup G} {S : Subgroup L} (hS : IsPGroup 3 S) :
    Nat.card (S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) = Nat.card S := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp S.subtype) := fun s t hst =>
    Subtype.ext (eq_of_mk_eq hS s.2 t.2 hst)
  have hrange : ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp S.subtype).range =
      S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem isElemAbelian_of_le_of_card_eq_nine {L S : Subgroup G}
    (eL : lBar L ≃* projSL 3 (GaloisField 2 2)) (hSL : S ≤ L) (hS9 : Nat.card S = 9) :
    IsElemAbelian 3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S' := S.subgroupOf L with hS'
  have hS'9 : Nat.card S' = 9 := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hS9]
  have hS'3 : IsPGroup 3 S' := IsPGroup.of_card (n := 2) (by rw [hS'9]; norm_num)
  set e' := eL.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  set φ := e'.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) with hφ
  have hφinj : ∀ s ∈ S', ∀ t ∈ S', φ s = φ t → s = t := fun s hs t ht h =>
    eq_of_mk_eq hS'3 hs ht (e'.injective h)
  have hE9 : Nat.card (S'.map φ) = 9 := by
    rw [hφ, ← Subgroup.map_map, Subgroup.card_map_of_injective e'.injective,
      card_map_mk hS'3, hS'9]
  have hEA := KFacts.L34.isElementaryAbelian_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hE9
  have hmem : ∀ (x : G) (hx : x ∈ S), (⟨x, hSL hx⟩ : L) ∈ S' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr hx
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hu := hmem u.1 u.2
    have hv := hmem v.1 v.2
    have h := congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm
      ⟨φ _, Subgroup.mem_map_of_mem _ hu⟩ ⟨φ _, Subgroup.mem_map_of_mem _ hv⟩)
    have h' : φ (⟨u, hSL u.2⟩ * ⟨v, hSL v.2⟩) = φ (⟨v, hSL v.2⟩ * ⟨u, hSL u.2⟩) := by
      rw [map_mul, map_mul]
      exact h
    have := hφinj _ (S'.mul_mem hu hv) _ (S'.mul_mem hv hu) h'
    exact congrArg (fun z : L => (z : G)) this
  · have hx' := hmem x hx
    have h3 := @CFSG.elemPow_eq_one_of_isElementaryAbelian 3 _ _ _ hEA (φ ⟨x, hSL hx⟩)
      (Subgroup.mem_map_of_mem _ hx')
    have := hφinj _ (S'.pow_mem hx' 3) _ S'.one_mem (by rw [map_pow, h3, map_one])
    exact congrArg (fun z : L => (z : G)) this

section Automizers

variable {L S : Subgroup G} {e : G}

theorem inf_eq_of_not_mem (hSL : S ≤ L) (heL : e ∉ L) (he3 : e ^ 3 = 1)
    (heS : ∀ s ∈ S, e * s = s * e) : (S ⊔ Subgroup.zpowers e) ⊓ L = S := by
  apply le_antisymm _ (le_inf le_sup_left hSL)
  rintro x ⟨hxF, hxL⟩
  have hc : ∀ y ∈ S, ∀ z ∈ Subgroup.zpowers e, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute e y from heS y hy) k).eq).symm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S _ hc
  have hx : x ∈ ((S ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := hxF
  rw [hset] at hx
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers he3 hz
  have hzL : e ^ j ∈ L := by
    have := L.mul_mem (L.inv_mem (hSL hs)) hxL
    simpa using this
  interval_cases j
  · simpa using hs
  · exact absurd (by simpa using hzL) heL
  · exfalso
    apply heL
    have h1 := L.pow_mem hzL 2
    rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, he3, one_mul, pow_one] at h1

theorem nonempty_autIn_equiv_automizer (hSL : S ≤ L)
    (hLe : L ≤ Subgroup.centralizer ({e} : Set G)) (heL : e ∉ L) (he3 : e ^ 3 = 1) :
    Nonempty (Sec4.autIn L (S ⊔ Subgroup.zpowers e) ≃* Automizer (S.subgroupOf L)) := by
  set F := S ⊔ Subgroup.zpowers e with hF
  set S' := S.subgroupOf L with hS'
  have heS : ∀ s ∈ S, e * s = s * e := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLe (hSL hs))).symm
  have hFL : F ⊓ L = S := inf_eq_of_not_mem hSL heL he3 heS
  have hge : ∀ x ∈ L, x * e = e * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLe hx)
  have hnS : ∀ n : Subgroup.normalizer (S' : Set L),
      ((n : L) : G) ∈ Subgroup.normalizer (S : Set G) := by
    intro n
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp n.2 ⟨s, hSL hs⟩).mp (Subgroup.mem_subgroupOf.mpr hs)
    exact Subgroup.mem_subgroupOf.mp h1
  have hnF : ∀ n : Subgroup.normalizer (S' : Set L),
      ((n : L) : G) ∈ Subgroup.normalizer (F : Set G) := fun n =>
    mem_normalizer_sup (hnS n) (mem_normalizer_zpowers_of_commute (hge _ (n : L).2))
  let ι : Subgroup.normalizer (S' : Set L) →* Subgroup.normalizer (F : Set G) :=
    { toFun := fun n => ⟨((n : L) : G), hnF n⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := F.normalizerMonoidHom.comp ι
  have hrange : g.range = Sec4.autIn L F := by
    ext τ
    constructor
    · rintro ⟨n, rfl⟩
      exact Sec4.mem_autIn_iff.mpr ⟨((n : L) : G), hnF n, (n : L).2, rfl⟩
    · intro hτ
      obtain ⟨h, hN, hhL, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
      have hhS : h ∈ Subgroup.normalizer (S : Set G) := by
        rw [← hFL]
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hN, Subgroup.le_normalizer hhL⟩
      have hhS' : (⟨h, hhL⟩ : L) ∈ Subgroup.normalizer (S' : Set L) := by
        refine Subgroup.mem_normalizer_fintype fun s hs => ?_
        have hs' : (s : G) ∈ S := hs
        show ((⟨h, hhL⟩ * s * ⟨h, hhL⟩⁻¹ : L) : G) ∈ S
        exact (Subgroup.mem_normalizer_iff.mp hhS _).mp hs'
      exact ⟨⟨⟨h, hhL⟩, hhS'⟩, rfl⟩
  have hcent : ∀ k : L, k ∈ Subgroup.centralizer (S' : Set L) ↔
      (k : G) ∈ Subgroup.centralizer (F : Set G) := by
    intro k
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have hFk : F ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
        refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := h ⟨s, hSL hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
          exact congrArg Subtype.val h1
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hge _ k.2).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hFk hx)
    · intro h s hs
      exact Subtype.ext (h s (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hs)))
  have hker : g.ker = (Subgroup.centralizer (S' : Set L)).subgroupOf
      (Subgroup.normalizer (S' : Set L)) := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      hcent]
    rfl
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange g).symm).trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

end Automizers

section Bar

variable {K : Type} [Group K] [Finite K]

omit [Group G] [Finite G] [Finite K] in
theorem card_sup_mul_card_inf_of_le_normalizer' {A N : Subgroup K}
    (hAN : A ≤ Subgroup.normalizer (N : Set K)) :
    Nat.card (A ⊔ N : Subgroup K) * Nat.card (A ⊓ N : Subgroup K) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup K) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Group G] [Finite G] in
theorem nonempty_automizer_equiv_bar {S : Subgroup K} (hS3 : IsPGroup 3 S)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    Nonempty (Automizer S ≃* Automizer (S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)))) :=
    by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 K with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Sb := S.map π with hSb
  have hθ3 : ¬ 3 ∣ Nat.card θ := three_not_dvd_card_aschbacherSolvableCore
  have hinj : ∀ s ∈ S, ∀ t ∈ S, π s = π t → s = t := fun s hs t ht h =>
    injOn_mk_of_isPGroup Nat.prime_three hS3 hs ht h
  have hSbc : Sb ≤ Subgroup.centralizer (Sb : Set (K ⧸ θ)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hSc t ht s hs]
  let ι₂ : Subgroup.normalizer (S : Set K) →* Subgroup.normalizer (Sb : Set (K ⧸ θ)) :=
    { toFun := fun n => ⟨π (n : K), Subgroup.le_normalizer_map π ⟨n, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun m n => Subtype.ext (map_mul π (m : K) n) }
  let f := (QuotientGroup.mk' ((Subgroup.centralizer (Sb : Set (K ⧸ θ))).subgroupOf
    (Subgroup.normalizer (Sb : Set (K ⧸ θ))))).comp ι₂
  have hker : f.ker = (Subgroup.centralizer (S : Set K)).subgroupOf
      (Subgroup.normalizer (S : Set K)) := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change π (n : K) ∈ Subgroup.centralizer (Sb : Set (K ⧸ θ)) ↔
      (n : K) ∈ Subgroup.centralizer (S : Set K)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      have hns : (n : K) * s * (n : K)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp n.2 s).mp hs
      have h1 := h (π s) ⟨s, hs, rfl⟩
      have h2 : π ((n : K) * s * (n : K)⁻¹) = π s := by
        rw [map_mul, map_mul, map_inv, ← h1]
        group
      have h3 := hinj _ hns _ hs h2
      calc s * n = (n : K) * s * (n : K)⁻¹ * n := by rw [h3]
        _ = n * s := by group
    · rintro h _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, h s hs]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨mb, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk'_surjective θ (mb : K ⧸ θ)
    set M := S ⊔ θ with hM
    have hMπ : Sb.comap π = M := by
      rw [hSb, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
    have hT₀M : S.map (MulAut.conj m₀).toMonoidHom ≤ M := by
      rintro _ ⟨s, hs, rfl⟩
      rw [← hMπ, Subgroup.mem_comap]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      rw [hm₀]
      exact (Subgroup.mem_normalizer_iff.mp mb.2 (π s)).mp ⟨s, hs, rfl⟩
    have hθN : S ≤ Subgroup.normalizer (θ : Set K) := fun x _ =>
      Subgroup.normalizer_eq_top_iff.mpr (aschbacherSolvableCore_normal 3 K) ▸ Subgroup.mem_top x
    have hSθ : S ⊓ θ = ⊥ := by
      obtain ⟨k, hk⟩ := hS3.exists_card_eq
      refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    have hcardM : Nat.card M = Nat.card S * Nat.card θ := by
      have h1 := card_sup_mul_card_inf_of_le_normalizer' hθN
      rwa [hSθ, Subgroup.card_bot, mul_one] at h1
    obtain ⟨k, hk⟩ := hS3.exists_card_eq
    have hfac : (Nat.card M).factorization 3 = k := by
      rw [hcardM, hk]
      exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three rfl hθ3
    have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 S M :=
      CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left (by rw [hfac, hk])
    have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 (S.map (MulAut.conj m₀).toMonoidHom) M :=
      CFSG.ABGLocalTools.isSylowOf_of_card hT₀M (by
        rw [Subgroup.card_map_of_injective (MulAut.conj m₀).injective, hfac, hk])
    obtain ⟨x, hxM, hxS⟩ := Item2119End5Proof.exists_conj_of_isSylowOf hTsyl hSsyl
    have hcomp : ((S.map (MulAut.conj m₀).toMonoidHom).map (MulAut.conj x).toMonoidHom) =
        S.map (MulAut.conj (x * m₀)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [mul_assoc]
    have hn₀ : x * m₀ ∈ Subgroup.normalizer (S : Set K) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcomp.symm.trans hxS.symm)
    have hxb : π x ∈ Sb := by
      have : x ∈ Sb.comap π := by rw [hMπ]; exact hxM
      exact this
    have hxbN : π x ∈ Subgroup.normalizer (Sb : Set (K ⧸ θ)) := Subgroup.le_normalizer hxb
    refine ⟨⟨x * m₀, hn₀⟩, ?_⟩
    have hι : ι₂ ⟨x * m₀, hn₀⟩ = ⟨π x, hxbN⟩ * mb := by
      apply Subtype.ext
      change π (x * m₀) = π x * (mb : K ⧸ θ)
      rw [map_mul, ← hm₀]
    change QuotientGroup.mk' _ (ι₂ ⟨x * m₀, hn₀⟩) = _
    rw [hι, map_mul]
    have h1 : QuotientGroup.mk' ((Subgroup.centralizer (Sb : Set (K ⧸ θ))).subgroupOf
        (Subgroup.normalizer (Sb : Set (K ⧸ θ)))) ⟨π x, hxbN⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hSbc hxb
    rw [h1, one_mul]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

end Bar

theorem nonempty_autIn_sup_zpowers {L S : Subgroup G} {e : G}
    (eL : lBar L ≃* projSL 3 (GaloisField 2 2)) (hSL : S ≤ L) (hS9 : Nat.card S = 9)
    (hLe : L ≤ Subgroup.centralizer ({e} : Set G)) (heL : e ∉ L) (he3 : e ^ 3 = 1) :
    Nonempty (Sec4.autIn L (S ⊔ Subgroup.zpowers e) ≃* QuaternionGroup 2) := by
  obtain ⟨e₁⟩ := nonempty_autIn_equiv_automizer hSL hLe heL he3
  set S' := S.subgroupOf L with hS'
  have hS'9 : Nat.card S' = 9 := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hS9]
  have hS'3 : IsPGroup 3 S' := IsPGroup.of_card (n := 2) (by rw [hS'9]; norm_num)
  have hSe := isElemAbelian_of_le_of_card_eq_nine eL hSL hS9
  have hS'c : ∀ x ∈ S', ∀ y ∈ S', x * y = y * x := fun x hx y hy =>
    Subtype.ext (congrArg (fun z : S => (z : G))
      (hSe.1.is_comm.comm ⟨(x : G), hx⟩ ⟨(y : G), hy⟩))
  obtain ⟨e₂⟩ := nonempty_automizer_equiv_bar hS'3 hS'c
  set e' := eL.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have h9 : Nat.card ((S'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map
      e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e'.injective, card_map_mk hS'3, hS'9]
  obtain ⟨e₃⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two h9
  exact ⟨e₁.trans (e₂.trans ((automizerCongr e' _).trans e₃))⟩

end CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof
