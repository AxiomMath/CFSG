module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def barOf (H K : Subgroup G) : Subgroup (Bar2 H) :=
  (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

private theorem pCore_quotient_eq_bot {H : Type*} [Group H] {p : ℕ} :
    CFSG.pCore p (H ⧸ CFSG.pCore p H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore p H with hN
  set K : Subgroup H := (CFSG.pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem pCore_bar2_eq_bot (H : Subgroup G) : CFSG.pCore 2 (Bar2 H) = ⊥ := by
  exact pCore_quotient_eq_bot

theorem isSylowOf_barOf {H T : Subgroup G} (hT : IsSylowOf 2 T H) : IsSylowOf 2 (barOf H T) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hdvd⟩ := isSylowOf_iff.1 hT
  refine isSylowOf_iff.2 ⟨le_top, hT2.comap_subtype.map _, fun h => hdvd ?_⟩
  rw [relIndex_top_right] at h
  exact h.trans ((T.subgroupOf H).index_map_dvd (QuotientGroup.mk'_surjective _))

theorem barOf_sup_eq_top (X T : Subgroup G) : barOf (X ⊔ T) X ⊔ barOf (X ⊔ T) T = ⊤ := by
  rw [barOf, barOf, ← Subgroup.map_sup, codisjoint_iff.1 (codisjoint_subgroupOf_sup X T),
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem isSubnormal_barOf {X H : Subgroup G} (h : IsSubnormal X H) :
    IsSubnormal (barOf H X) ⊤ := by
  have h1 := (h.comap H.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  rw [comap_subtype, comap_subtype, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  exact h1

private theorem conj_mem_map_of_characteristic {X : Subgroup G} {D : Subgroup X}
    [hD : D.Characteristic] {g : G} (hg : g ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ D.map X.subtype) : g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem map_pCore_le_of_isSubnormal {X H : Subgroup G} (h : CFSG.Open.IsSubnormal X H) :
    (CFSG.pCore 2 ↥X).map X.subtype ≤ (CFSG.pCore 2 ↥H).map H.subtype := by
  induction h with
  | refl => exact le_rfl
  | @step X M K hXM hN _ ih =>
    refine le_trans ?_ ih
    have hMN : M ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer hXM).mp hN
    have hLM : (CFSG.pCore 2 ↥X).map X.subtype ≤ M := (map_subtype_le _).trans hXM
    have hle : ((CFSG.pCore 2 ↥X).map X.subtype).subgroupOf M ≤ CFSG.pCore 2 ↥M := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic (hMN y.2) hl
      · exact ((CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype).of_equiv
          (subgroupOfEquivOfLe hLM).symm
    calc (CFSG.pCore 2 ↥X).map X.subtype
        = (((CFSG.pCore 2 ↥X).map X.subtype).subgroupOf M).map M.subtype :=
          (map_subgroupOf_eq_of_le hLM).symm
      _ ≤ (CFSG.pCore 2 ↥M).map M.subtype := map_mono hle

theorem nonempty_barOf_mulEquiv {X H : Subgroup G} (h : IsSubnormal X H) :
    Nonempty (barOf H X ≃* Bar2 X) := by
  have hXH : X ≤ H := h.le
  set ψ : ↥X →* Bar2 H := (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (inclusion hXH) with hψ
  have hker : ψ.ker = CFSG.pCore 2 ↥X := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥H).comap (inclusion hXH)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).comap_of_injective _ (inclusion_injective hXH)
      rwa [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    · intro x hx
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1
        (map_pCore_le_of_isSubnormal h (mem_map_of_mem X.subtype hx))
      have hy' : y = inclusion hXH x := Subtype.ext hyx
      rw [← hy']
      exact hy
  have hrange : ψ.range = barOf H X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (show inclusion hXH x ∈ X.subgroupOf H from x.2)
    · intro hy
      rw [barOf] at hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨z, hz⟩, rfl⟩
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange ψ).symm).trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem barOf_eq_top_iff {X H : Subgroup G} (hXH : X ≤ H) :
    barOf H X = ⊤ ↔ H = X ⊔ pCoreOf 2 H := by
  rw [← (comap_injective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H))).eq_iff, comap_top,
    barOf, comap_map_eq, QuotientGroup.ker_mk', ← (map_injective H.subtype_injective).eq_iff,
    Subgroup.map_sup, map_subgroupOf_eq_of_le hXH, ← MonoidHom.range_eq_map, range_subtype, pCoreOf]
  exact eq_comm

theorem nonempty_bar2_mulEquiv_of_eq {X H : Subgroup G} (h : IsSubnormal X H)
    (hH : H = X ⊔ pCoreOf 2 H) : Nonempty (Bar2 H ≃* Bar2 X) := by
  obtain ⟨e⟩ := nonempty_barOf_mulEquiv h
  have htop : barOf H X = ⊤ := (barOf_eq_top_iff h.le).2 hH
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩

private theorem isElemAbelian_of_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] {p : ℕ}
    {A : Subgroup G₁} {B : Subgroup G₂} (e : A ≃* B) (hB : IsElemAbelian p B) :
    IsElemAbelian p A := by
  refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hB.1.is_comm.comm (e a) (e b)
  · have h1 : e ⟨x, hx⟩ ^ p = 1 := Subtype.ext (hB.2 _ (e ⟨x, hx⟩).2)
    rw [← map_pow, ← map_one e] at h1
    have h2 := congrArg (fun y : A => (y : G₁)) (e.injective h1)
    simpa using h2

theorem exists_lift {H T : Subgroup G} (hT : IsSylowOf 2 T H) {Q : Subgroup (Bar2 H)}
    (hQ : IsPGroup 3 Q) (hQT : Permutes Q (barOf H T)) :
    ∃ P : Subgroup G, P ≤ H ∧ Nat.card P = Nat.card Q ∧
      (IsElemAbelian 3 Q → IsElemAbelian 3 P) ∧ Permutes P T ∧
      (IrrOn (normalizer (Q : Set (Bar2 H)) ⊓ barOf H T) Q →
        IrrOn (normalizer (P : Set G) ⊓ T) P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hπ⟩ : ∃ π : ↥H →* Bar2 H, π = QuotientGroup.mk' (CFSG.pCore 2 ↥H) := ⟨_, rfl⟩
  have hπs : Function.Surjective π := by
    subst hπ
    exact QuotientGroup.mk'_surjective _
  have hker : ∀ h : ↥H, π h = 1 ↔ h ∈ CFSG.pCore 2 ↥H := fun h => by
    subst hπ
    rw [QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff h
  have hbar : ∀ K : Subgroup G, barOf H K = (K.subgroupOf H).map π := fun K => by
    subst hπ
    rfl
  have hTH : T ≤ H := hT.le
  have hOT : CFSG.pCore 2 ↥H ≤ T.subgroupOf H := by
    obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
    rw [← hS]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal S
  obtain ⟨Q₀⟩ : Nonempty (Sylow 3 ↥(Q.comap π)) := inferInstance
  set R : Subgroup ↥H := Q.comap π with hR
  set P₀ : Subgroup ↥H := (Q₀ : Subgroup ↥R).map R.subtype with hP₀
  have hP₀syl : IsSylowOf 3 P₀ R := ⟨Q₀, rfl⟩
  have hP₀3 : IsPGroup 3 P₀ := hP₀syl.isPGroup
  have hP₀Q : ∀ p ∈ P₀, π p ∈ Q := fun p hp => hP₀syl.le hp
  set f : ↥R →* ↥Q := (π.comp R.subtype).codRestrict Q (fun r => r.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨h, rfl⟩ := hπs q
    exact ⟨⟨h, hq⟩, Subtype.ext rfl⟩
  have hQtop : ((Sylow.mapSurjective hfs Q₀ : Sylow 3 ↥Q) : Subgroup ↥Q) = ⊤ :=
    ((Sylow.mapSurjective hfs Q₀).3 (hQ.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hπP₀ : ∀ q ∈ Q, ∃ p ∈ P₀, π p = q := by
    intro q hq
    have hq' : (⟨q, hq⟩ : ↥Q) ∈ ((Sylow.mapSurjective hfs Q₀ : Sylow 3 ↥Q) : Subgroup ↥Q) := by
      rw [hQtop]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at hq'
    obtain ⟨r, hr, hrq⟩ := Subgroup.mem_map.1 hq'
    rw [Subtype.ext_iff] at hrq
    exact ⟨r, mem_map_of_mem R.subtype hr, hrq⟩
  have hdisj : Disjoint P₀ (CFSG.pCore 2 ↥H) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) P₀ (CFSG.pCore 2 ↥H) hP₀3 CFSG.pCore_isPGroup
  have hinj : ∀ p₁ ∈ P₀, ∀ p₂ ∈ P₀, π p₁ = π p₂ → p₁ = p₂ := by
    intro p₁ h₁ p₂ h₂ h
    refine inv_mul_eq_one.1 (disjoint_def.1 hdisj (P₀.mul_mem (P₀.inv_mem h₁) h₂) ?_)
    rw [← hker, map_mul, map_inv, h, inv_mul_cancel]
  set g : ↥P₀ →* ↥Q := (π.comp P₀.subtype).codRestrict Q (fun p => hP₀Q p p.2) with hg
  have hgb : Function.Bijective g := by
    refine ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 ?_), fun q => ?_⟩
    · have h := congrArg Subtype.val hab
      exact h
    · obtain ⟨p, hp, hpq⟩ := hπP₀ q q.2
      exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  set e : ↥P₀ ≃* ↥Q := MulEquiv.ofBijective g hgb with he
  have hTbar : ∀ t ∈ T.subgroupOf H, π t ∈ barOf H T := fun t ht => by
    rw [hbar]
    exact mem_map_of_mem π ht
  have hQT' : (Q : Set (Bar2 H)) * (barOf H T : Set (Bar2 H)) =
      (barOf H T : Set (Bar2 H)) * (Q : Set (Bar2 H)) := hQT
  have hmem1 : ∀ h : ↥H, h ∈ (P₀ : Set ↥H) * (T.subgroupOf H : Set ↥H) ↔
      π h ∈ (Q : Set (Bar2 H)) * (barOf H T : Set (Bar2 H)) := by
    intro h
    constructor
    · intro hh
      obtain ⟨p, hp, t, ht, rfl⟩ := Set.mem_mul.1 hh
      exact Set.mem_mul.2 ⟨π p, hP₀Q p hp, π t, hTbar t ht, (map_mul π p t).symm⟩
    · intro hh
      obtain ⟨q, hq, x, hx, hqx⟩ := Set.mem_mul.1 hh
      obtain ⟨p, hp, rfl⟩ := hπP₀ q hq
      rw [hbar] at hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
      have ho : (p * t)⁻¹ * h ∈ CFSG.pCore 2 ↥H := by
        rw [← hker, map_mul, map_inv, map_mul, ← hqx, inv_mul_cancel]
      refine Set.mem_mul.2 ⟨p, hp, t * ((p * t)⁻¹ * h), (T.subgroupOf H).mul_mem ht (hOT ho), ?_⟩
      group
  have hmem2 : ∀ h : ↥H, h ∈ (T.subgroupOf H : Set ↥H) * (P₀ : Set ↥H) ↔
      π h ∈ (barOf H T : Set (Bar2 H)) * (Q : Set (Bar2 H)) := by
    intro h
    constructor
    · intro hh
      obtain ⟨t, ht, p, hp, rfl⟩ := Set.mem_mul.1 hh
      exact Set.mem_mul.2 ⟨π t, hTbar t ht, π p, hP₀Q p hp, (map_mul π t p).symm⟩
    · intro hh
      obtain ⟨x, hx, q, hq, hxq⟩ := Set.mem_mul.1 hh
      obtain ⟨p, hp, rfl⟩ := hπP₀ q hq
      rw [hbar] at hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
      have ho : h * (t * p)⁻¹ ∈ CFSG.pCore 2 ↥H := by
        rw [← hker, map_mul, map_inv, map_mul, ← hxq, mul_inv_cancel]
      refine Set.mem_mul.2 ⟨h * (t * p)⁻¹ * t, (T.subgroupOf H).mul_mem (hOT ho) ht, p, hp, ?_⟩
      group
  have hset : (P₀ : Set ↥H) * (T.subgroupOf H : Set ↥H) =
      (T.subgroupOf H : Set ↥H) * (P₀ : Set ↥H) := by
    ext h
    rw [hmem1, hmem2, hQT']
  refine ⟨P₀.map H.subtype, map_subtype_le _, ?_, fun hQe => ?_, ?_, ?_⟩
  · rw [card_map_of_injective H.subtype_injective]
    exact Nat.card_congr e.toEquiv
  · exact isElemAbelian_of_mulEquiv
      ((P₀.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e) hQe
  · show ((P₀.map H.subtype : Subgroup G) : Set G) * (T : Set G) =
      (T : Set G) * ((P₀.map H.subtype : Subgroup G) : Set G)
    rw [← map_subgroupOf_eq_of_le hTH, coe_map H.subtype P₀, coe_map H.subtype (T.subgroupOf H),
      ← Set.image_mul, ← Set.image_mul, hset]
  · intro hirr W hWP hWN
    have hWH : W ≤ H := hWP.trans (map_subtype_le _)
    have hWmap : (W.subgroupOf H).map H.subtype = W := map_subgroupOf_eq_of_le hWH
    have hW₀P₀ : W.subgroupOf H ≤ P₀ := by
      intro w hw
      obtain ⟨p, hp, hpw⟩ := Subgroup.mem_map.1 (hWP hw)
      have hpw' : p = w := Subtype.ext hpw
      rwa [← hpw']
    have hle : (W.subgroupOf H).map π ≤ Q := by
      rintro _ ⟨w, hw, rfl⟩
      exact hP₀Q w (hW₀P₀ hw)
    have hN : normalizer (Q : Set (Bar2 H)) ⊓ barOf H T ≤
        normalizer (((W.subgroupOf H).map π : Subgroup (Bar2 H)) : Set (Bar2 H)) := by
      rintro x ⟨hxQ, hxT⟩
      rw [hbar] at hxT
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hxT
      have htR : t ∈ normalizer (R : Set ↥H) := by
        refine mem_normalizer_fintype fun y hy => ?_
        show π (t * y * t⁻¹) ∈ Q
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.1 hxQ (π y)).1 hy
      obtain ⟨r, hrR, hrN⟩ := exists_inv_mul_mem_normalizer hP₀syl htR
      obtain ⟨p, hp, hpr⟩ := hπP₀ (π r) hrR
      have hs1 : p * r⁻¹ ∈ CFSG.pCore 2 ↥H := by
        rw [← hker, map_mul, map_inv, hpr, mul_inv_cancel]
      have key : ∃ s ∈ T.subgroupOf H, s ∈ normalizer (P₀ : Set ↥H) ∧ π s = π t := by
        refine ⟨p * (r⁻¹ * t), ?_, mul_mem (le_normalizer hp) hrN, ?_⟩
        · rw [← mul_assoc]
          exact (T.subgroupOf H).mul_mem (hOT hs1) ht
        · rw [map_mul, map_mul, map_inv, hpr, mul_inv_cancel_left]
      obtain ⟨s, hsT, hsN, hπst⟩ := key
      have hsG : (s : G) ∈ normalizer ((P₀.map H.subtype : Subgroup G) : Set G) ⊓ T := by
        refine ⟨mem_normalizer_fintype fun y hy => ?_, hsT⟩
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
        exact Subgroup.mem_map.2 ⟨_, (mem_normalizer_iff.1 hsN z).1 hz, rfl⟩
      have hsW := hWN hsG
      rw [← hπst]
      refine mem_normalizer_fintype fun y hy => ?_
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨s * w * s⁻¹, ?_, ?_⟩
      · exact (mem_normalizer_iff.1 hsW (w : G)).1 hw
      · rw [map_mul, map_mul, map_inv]
    rcases hirr _ hle hN with h | h
    · left
      rw [← hWmap, eq_bot_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : π w = 1 := by
        have hw' : π w ∈ (W.subgroupOf H).map π := mem_map_of_mem π hw
        rw [h] at hw'
        exact mem_bot.1 hw'
      have hw2 := hinj w (hW₀P₀ hw) 1 P₀.one_mem (by rw [hw1, map_one])
      rw [hw2, map_one]
      exact one_mem _
    · right
      rw [← hWmap]
      congr 1
      refine le_antisymm hW₀P₀ fun p hp => ?_
      have hp' : π p ∈ (W.subgroupOf H).map π := by
        rw [h]
        exact hP₀Q p hp
      obtain ⟨w, hw, hwp⟩ := Subgroup.mem_map.1 hp'
      rwa [← hinj w (hW₀P₀ hw) p hp hwp]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
