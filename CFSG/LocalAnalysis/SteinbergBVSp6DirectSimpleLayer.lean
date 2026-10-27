module

public import CFSG.LocalAnalysis.SteinbergBVSp6NonnormalLayer
public import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG.LocalCores
open scoped commutatorElement

namespace DirectSimpleLayer

open OneOrTwoLayer

variable {F : Type*} [Group F]

theorem center_eq_bot_of_simple {J : Subgroup F} [IsSimpleGroup J]
    (hJna : ∃ x y : J, x * y ≠ y * x) : center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hJna
    exact absurd (mem_center_iff.1 (h ▸ mem_top y) x) hxy

theorem injOn_of_isPGroup_two [Finite F] (R : Subgroup F) [R.Normal] (hR : Odd (Nat.card R))
    {P : Subgroup F} (hP : IsPGroup 2 P) : Set.InjOn (QuotientGroup.mk' R) (P : Set F) := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ R := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨_, h2⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : orderOf (x⁻¹ * y) ∣ Nat.card R := by
    have := orderOf_dvd_natCard (⟨_, h1⟩ : R)
    rwa [Subgroup.orderOf_mk] at this
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact Nat.not_even_iff_odd.2 hR (even_iff_two_dvd.2 ((dvd_pow_self 2 j.succ_ne_zero).trans h3))
  rw [hk0, pow_zero, orderOf_eq_one_iff, inv_mul_eq_one] at hk
  exact hk

theorem odd_core_inverted [Finite F] {J : Subgroup F} [IsSimpleGroup J]
    (hJna : ∃ x y : J, x * y ≠ y * x) (hJ4 : 4 ∣ Nat.card J) {a : F} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set F)) (hprod : zpowers a ⊔ J = centralizer ({a} : Set F)) :
    CFSG.pPrimeCore 2 F ⊓ centralizer ({a} : Set F) = ⊥ ∧
      (∀ r ∈ CFSG.pPrimeCore 2 F, a⁻¹ * r * a = r⁻¹) ∧
      IsMulCommutative (CFSG.pPrimeCore 2 F) := by
  set R := CFSG.pPrimeCore 2 F with hRdef
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hZJ := center_eq_bot_of_simple hJna
  have hRJ : ∀ x ∈ R, x ∈ J → x = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf J) with h | h
    · intro x hxR hxJ
      have : (⟨x, hxJ⟩ : J) ∈ R.subgroupOf J := hxR
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hJR : J ≤ R := fun x hx => by
        have : (⟨x, hx⟩ : J) ∈ R.subgroupOf J := h ▸ mem_top _
        exact this
      exact Nat.not_even_iff_odd.2 hRodd
        (even_iff_two_dvd.2 (((by norm_num : 2 ∣ 4).trans hJ4).trans (card_dvd_of_le hJR)))
  have haCJ : a ∈ centralizer (J : Set F) := mem_centralizer_iff.2 fun j hj =>
    mem_centralizer_singleton_iff.1 (hJa hj)
  have haJ : zpowers a ≤ normalizer (J : Set F) :=
    le_normalizer_of_le_centralizer ((zpowers_le (G := F)).2 haCJ)
  have hCaN : centralizer ({a} : Set F) ≤ normalizer (J : Set F) := by
    rw [← hprod]
    exact sup_le haJ le_normalizer
  have hRa : R ⊓ centralizer ({a} : Set F) = ⊥ := by
    refine eq_bot_iff.2 fun x ⟨hxR, hxa⟩ => ?_
    have hxJ : ∀ j ∈ J, x * j = j * x := fun j hj => by
      have h1 : x * j * x⁻¹ * j⁻¹ ∈ R := by
        have := (inferInstance : R.Normal).conj_mem _ (R.inv_mem hxR) j
        have h' := R.mul_mem hxR this
        convert h' using 1
        group
      have h2 : x * j * x⁻¹ * j⁻¹ ∈ J :=
        J.mul_mem ((mem_normalizer_iff.1 (hCaN hxa) j).1 hj) (J.inv_mem hj)
      have h3 := hRJ _ h1 h2
      calc x * j = (x * j * x⁻¹ * j⁻¹) * (j * x) := by group
        _ = j * x := by rw [h3, one_mul]
    have hxa' : x ∈ ((zpowers a ⊔ J : Subgroup F) : Set F) := by
      rw [SetLike.mem_coe, hprod]
      exact hxa
    rw [coe_mul_of_left_le_normalizer_right _ _ haJ] at hxa'
    obtain ⟨k, hk, j, hj, rfl⟩ := hxa'
    have hkJ : ∀ j' ∈ J, k * j' = j' * k := fun j' hj' => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
      exact ((Commute.zpow_left (mem_centralizer_singleton_iff.1 (hJa hj')).symm n)).eq
    have hjZ : (⟨j, hj⟩ : J) ∈ center J := mem_center_iff.2 fun g => Subtype.ext (by
      have h1 := hxJ g g.2
      have h2 := hkJ g g.2
      show (g : F) * j = j * g
      calc (g : F) * j = k⁻¹ * (k * g) * j := by group
        _ = k⁻¹ * (g * k) * j := by rw [h2]
        _ = k⁻¹ * (g * (k * j)) := by group
        _ = k⁻¹ * (k * j * g) := by rw [h1]
        _ = j * g := by group)
    rw [hZJ, mem_bot] at hjZ
    have hj1 : j = 1 := congrArg Subtype.val hjZ
    subst hj1
    simp only [mul_one] at hxR ⊢
    rcases eq_one_or_eq_of_mem_zpowers ha hk with h | h
    · exact mem_bot.2 h
    · exfalso
      rw [h] at hxR
      have h2 := orderOf_dvd_natCard (⟨a, hxR⟩ : R)
      rw [Subgroup.orderOf_mk, ha] at h2
      exact Nat.not_even_iff_odd.2 hRodd (even_iff_two_dvd.2 h2)
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  let φ : R →* R := (MulAut.conjNormal a⁻¹ : MulAut R).toMonoidHom
  have hφ : ∀ r : R, ((φ r : R) : F) = a⁻¹ * r * a := fun r => by
    show ((MulAut.conjNormal a⁻¹ r : R) : F) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hfree : MonoidHom.FixedPointFree φ := fun r hr => by
    have h1 : (r : F) ∈ R ⊓ centralizer ({a} : Set F) := by
      refine ⟨r.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h2 : a⁻¹ * r * a = r := by rw [← hφ, hr]
      calc (r : F) * a = a * (a⁻¹ * r * a) := by group
        _ = a * r := by rw [h2]
    rw [hRa, mem_bot] at h1
    exact Subtype.ext h1
  have hinvol : Function.Involutive φ := fun r => Subtype.ext (by
    rw [hφ, hφ, hainv]
    calc a * (a * (r : F) * a) * a = (a * a) * r * (a * a) := by group
      _ = r := by rw [haa, one_mul, mul_one])
  refine ⟨hRa, fun r hr => ?_, ⟨⟨fun x y => ?_⟩⟩⟩
  · have h1 := congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨r, hr⟩
    have h2 := congrArg Subtype.val h1
    rw [hφ] at h2
    exact h2
  · exact (hfree.commute_all_of_involutive hinvol x y).eq

theorem eq_top_of_card_sylow_eq_two [Finite F] (hF : CFSG.pPrimeCore 2 F = ⊥) (S : Sylow 2 F)
    (hS : Nat.card (S : Subgroup F) = 2) : (S : Subgroup F) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : ∀ s t : F, s ∈ (S : Subgroup F) → t ∈ (S : Subgroup F) → s ≠ 1 → t ≠ 1 → s = t := by
    intro s t hs ht hs1 ht1
    have hord : orderOf (⟨s, hs⟩ : (S : Subgroup F)) = 2 := by
      have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : (S : Subgroup F))
      rw [hS] at h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.1 h)) hs1
      · exact h
    have htop : zpowers (⟨s, hs⟩ : (S : Subgroup F)) = ⊤ := by
      apply eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hS]
    have ht' : (⟨t, ht⟩ : (S : Subgroup F)) ∈ zpowers (⟨s, hs⟩ : (S : Subgroup F)) :=
      htop ▸ mem_top _
    rcases eq_one_or_eq_of_mem_zpowers hord ht' with h | h
    · exact absurd (congrArg Subtype.val h) ht1
    · exact (congrArg Subtype.val h).symm
  have hP : normalizer ((S : Subgroup F) : Set F) ≤ centralizer ((S : Subgroup F) : Set F) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    · have hgs : g * s * g⁻¹ ∈ (S : Subgroup F) := (mem_normalizer_iff.1 hg s).1 hs
      have hgs1 : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
        calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group)
      have := hS2 _ _ hgs hs hgs1 hs1
      calc s * g = (g * s * g⁻¹) * g := by rw [this]
        _ = g * s := by group
  have hcompl := MonoidHom.ker_transferSylow_isComplement' S hP
  have hcard := hcompl.card_mul_card
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow S hP
  have hker : (MonoidHom.transferSylow S hP).ker = ⊥ := by
    rw [eq_bot_iff, ← hF]
    exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd⟩
  rw [hker, card_bot, one_mul] at hcard
  exact (card_eq_iff_eq_top _).1 hcard

theorem not_central_sylow_quotient [Finite F] (R : Subgroup F) [R.Normal]
    (hR : Odd (Nat.card R)) {a : F} (ha : orderOf a = 2)
    (hnc : ∀ S : Sylow 2 F, a ∈ S → ∃ s ∈ S, s * a ≠ a * s) :
    ∀ T : Sylow 2 (F ⧸ R), QuotientGroup.mk' R a ∈ T →
      ∃ t ∈ T, t * QuotientGroup.mk' R a ≠ QuotientGroup.mk' R a * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T haT
  set θ := QuotientGroup.mk' R with hθ
  set T' := (T : Subgroup (F ⧸ R)).comap θ with hT'
  have haT' : a ∈ T' := haT
  have hza : IsPGroup 2 (zpowers (⟨a, haT'⟩ : T')) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact ha)
  obtain ⟨P', hP'⟩ := hza.exists_le_sylow
  set P := (P' : Subgroup T').map T'.subtype with hPdef
  have hP2 : IsPGroup 2 P := P'.isPGroup'.map _
  have hPidx : ¬ 2 ∣ P.index := by
    have h1 := index_map_subtype (P' : Subgroup T')
    have h2 : T'.index = (T : Subgroup (F ⧸ R)).index :=
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective R)
    rw [hPdef, h1, h2]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h1 | h1
    · exact P'.not_dvd_index h1
    · exact T.not_dvd_index h1
  have haP : a ∈ P := ⟨⟨a, haT'⟩, hP' (mem_zpowers _), rfl⟩
  obtain ⟨s, hs, hsa⟩ := hnc (hP2.toSylow hPidx) (by rw [IsPGroup.mem_toSylow]; exact haP)
  rw [IsPGroup.mem_toSylow] at hs
  refine ⟨θ s, ?_, fun h => hsa ?_⟩
  · obtain ⟨s', -, rfl⟩ := hs
    exact s'.2
  · refine injOn_of_isPGroup_two R hR hP2 (P.mul_mem hs haP) (P.mul_mem haP hs) ?_
    rw [map_mul, map_mul]
    exact h

theorem isStandardSubgroup_of_assembly {L : Subgroup F} [IsSimpleGroup L]
    (_hna : ∃ x y : L, x * y ≠ y * x) (h : CFSG.Assembly.ComponentType.IsStandardSubgroup L) :
    CFSG.IsStandardSubgroup L :=
  CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.2 h

theorem preimage_le_centralizer [Finite F] (R : Subgroup F) [R.Normal] {a : F}
    (ha : orderOf a = 2) (hinv : ∀ r ∈ R, a⁻¹ * r * a = r⁻¹) (hab : IsMulCommutative R)
    (J : Subgroup F)
    (hal : OneOrTwoLayerAlternatives (J.map (QuotientGroup.mk' R))
      (normalClosure (J.map (QuotientGroup.mk' R) : Set (F ⧸ R))) (QuotientGroup.mk' R a)) :
    (normalClosure (J.map (QuotientGroup.mk' R) : Set (F ⧸ R))).comap (QuotientGroup.mk' R) ≤
      centralizer (R : Set F) := by
  set θ := QuotientGroup.mk' R with hθ
  set D := normalClosure (J.map θ : Set (F ⧸ R)) with hDdef
  set K := centralizer (R : Set F) with hKdef
  have hRK : R ≤ K := fun r hr => mem_centralizer_iff.2 fun s hs =>
    congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ ⟨r, hr⟩)
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hconjR : ∀ s ∈ R, a * s * a⁻¹ = s⁻¹ := fun s hs => by
    have := hinv s hs
    rw [hainv] at this ⊢
    exact this
  have hcommK : ∀ h : F, h * a * h⁻¹ * a⁻¹ ∈ K := by
    intro h
    rw [mem_centralizer_iff]
    intro r hr
    have hs : h⁻¹ * r⁻¹ * h ∈ R := by
      have := (inferInstance : R.Normal).conj_mem _ (R.inv_mem hr) h⁻¹
      rwa [inv_inv] at this
    have e1 : a⁻¹ * r * a = r⁻¹ := hinv r hr
    have e2 : a * (h⁻¹ * r⁻¹ * h) * a⁻¹ = (h⁻¹ * r⁻¹ * h)⁻¹ := hconjR _ hs
    have hc : (h * a * h⁻¹ * a⁻¹) * r * (h * a * h⁻¹ * a⁻¹)⁻¹ = r := by
      calc (h * a * h⁻¹ * a⁻¹) * r * (h * a * h⁻¹ * a⁻¹)⁻¹ =
            h * a * h⁻¹ * (a⁻¹ * r * a) * h * a⁻¹ * h⁻¹ := by group
        _ = h * (a * (h⁻¹ * r⁻¹ * h) * a⁻¹) * h⁻¹ := by rw [e1]; group
        _ = h * (h⁻¹ * r⁻¹ * h)⁻¹ * h⁻¹ := by rw [e2]
        _ = r := by group
    calc r * (h * a * h⁻¹ * a⁻¹) =
          (h * a * h⁻¹ * a⁻¹) * r * (h * a * h⁻¹ * a⁻¹)⁻¹ * (h * a * h⁻¹ * a⁻¹) := by rw [hc]
      _ = (h * a * h⁻¹ * a⁻¹) * r := by group
  set Kb := K.map θ with hKbdef
  have hKbn : Kb.Normal := (inferInstance : K.Normal).map θ (QuotientGroup.mk'_surjective R)
  have hcommKb : ∀ d : F ⧸ R, d * θ a * d⁻¹ * (θ a)⁻¹ ∈ Kb := by
    intro d
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective R d
    refine ⟨h * a * h⁻¹ * a⁻¹, hcommK h, ?_⟩
    simp [hθ, map_mul, map_inv]
  have hDKb : D ≤ Kb := by
    rcases hal with ⟨⟨hDs, -, -, d, hd, hda⟩, -⟩ | ⟨⟨D₁, D₂, hD₁, hD₂, hne, hs₁, hna₁, -, -,
        hsup, hinf, hcomm, hmap, -⟩, -⟩
    ·
      have hn : (Kb.subgroupOf D).Normal := Subgroup.normal_subgroupOf
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kb.subgroupOf D) with h | h
      · exfalso
        apply hda
        have hdD : d * θ a * d⁻¹ * (θ a)⁻¹ ∈ D := by
          have h1 := (normalClosure_normal (s := (J.map θ : Set (F ⧸ R)))).conj_mem _
            (D.inv_mem hd) (θ a)
          have h2 := D.mul_mem hd h1
          convert h2 using 1
          group
        have h3 : (⟨_, hdD⟩ : D) ∈ Kb.subgroupOf D := hcommKb d
        rw [h, mem_bot] at h3
        have h4 : d * θ a * d⁻¹ * (θ a)⁻¹ = 1 := congrArg Subtype.val h3
        have h5 : d * θ a = θ a * d := by
          calc d * θ a = (d * θ a * d⁻¹ * (θ a)⁻¹) * (θ a * d) := by group
            _ = θ a * d := by rw [h4, one_mul]
        calc (θ a)⁻¹ * d * θ a = (θ a)⁻¹ * (d * θ a) := by group
          _ = (θ a)⁻¹ * (θ a * d) := by rw [h5]
          _ = d := by group
      · intro x hx
        have : (⟨x, hx⟩ : D) ∈ Kb.subgroupOf D := h ▸ mem_top _
        exact this
    ·
      have hD₁Kb : D₁ ≤ Kb := by
        have hD₁D : D₁ ≤ D := hsup ▸ le_sup_left
        have hn : (Kb.subgroupOf D₁).Normal := Subgroup.normal_subgroupOf
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kb.subgroupOf D₁) with h | h
        · exfalso
          obtain ⟨x, y, hxy⟩ := hna₁
          apply hxy
          have hcomm1 : ∀ u ∈ D₁, ∀ v ∈ D₂, u * v = v * u := fun u hu v hv =>
            (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm hu) v hv).symm
          have hconj : ∀ u ∈ D₁, θ a * u⁻¹ * (θ a)⁻¹ ∈ D₂ := fun u hu => by
            rw [← hmap]
            refine ⟨u⁻¹, D₁.inv_mem hu, ?_⟩
            have hθaa : θ a * θ a = 1 := by rw [← map_mul, haa, map_one]
            have hθinv : (θ a)⁻¹ = θ a := inv_eq_of_mul_eq_one_right hθaa
            simp [MulAut.conj_apply, hθinv]
          have key : ∀ u ∈ D₁, ∀ z ∈ D₁, u * z = z * u := by
            intro u hu z hz
            set w := θ a * u⁻¹ * (θ a)⁻¹ with hw
            have hwD₂ : w ∈ D₂ := hconj u hu
            have hk : u * w ∈ Kb := by
              have := hcommKb u
              convert this using 1
              rw [hw]
              group
            have hk2 : u * z * u⁻¹ * z⁻¹ ∈ Kb := by
              have h1 := hKbn.conj_mem _ (Kb.inv_mem hk) z
              have h2 := Kb.mul_mem hk h1
              convert h2 using 1
              have hwz : w * z = z * w := (hcomm1 z hz w hwD₂).symm
              calc u * z * u⁻¹ * z⁻¹ = u * w * z * w⁻¹ * u⁻¹ * z⁻¹ := by
                    rw [show u * w * z * w⁻¹ * u⁻¹ * z⁻¹ = u * (w * z) * w⁻¹ * u⁻¹ * z⁻¹ by group,
                      hwz]
                    group
                _ = u * w * (z * (u * w)⁻¹ * z⁻¹) := by group
            have hmem : (⟨u * z * u⁻¹ * z⁻¹, D₁.mul_mem (D₁.mul_mem (D₁.mul_mem hu hz)
                (D₁.inv_mem hu)) (D₁.inv_mem hz)⟩ : D₁) ∈ Kb.subgroupOf D₁ := hk2
            rw [h, mem_bot] at hmem
            have h5 : u * z * u⁻¹ * z⁻¹ = 1 := congrArg Subtype.val hmem
            calc u * z = (u * z * u⁻¹ * z⁻¹) * (z * u) := by group
              _ = z * u := by rw [h5, one_mul]
          exact Subtype.ext (key x x.2 y y.2)
        · intro x hx
          have : (⟨x, hx⟩ : D₁) ∈ Kb.subgroupOf D₁ := h ▸ mem_top _
          exact this
      have hD₂Kb : D₂ ≤ Kb := by
        rw [← hmap]
        rintro _ ⟨x, hx, rfl⟩
        have := hKbn.conj_mem x (hD₁Kb hx) (θ a)⁻¹
        simpa [MulAut.conj_apply] using this
      rw [← hsup]
      exact sup_le hD₁Kb hD₂Kb
  intro x hx
  have hx' : θ x ∈ Kb := hDKb hx
  obtain ⟨k, hk, hkx⟩ := hx'
  have hkx' : k⁻¹ * x ∈ R := by
    rw [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
  have := K.mul_mem hk (hRK hkx')
  rwa [mul_inv_cancel_left] at this

end DirectSimpleLayer

open DirectSimpleLayer OneOrTwoLayer in
theorem direct_simple_involution_centralizer_layer_of
    (h1 : NonnormalInvolutionComponentLayerStmt) : DirectSimpleInvolutionCentralizerLayerStmt := by
  intro F _ _ hKF J hJs hJna hJ4 a ha hJa hcap hprod hnc θ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.pPrimeCore 2 F with hRdef
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hJ4' : 4 ∣ Nat.card J := by
    obtain ⟨E, hEJ, -, hE4⟩ := hJ4
    rw [← hE4]
    exact card_dvd_of_le hEJ
  obtain ⟨hRa, hinvR, hRab⟩ := odd_core_inverted hJna hJ4' ha hJa hprod
  have hZJ := center_eq_bot_of_simple hJna
  have haCJ : a ∈ centralizer (J : Set F) := mem_centralizer_iff.2 fun j hj =>
    mem_centralizer_singleton_iff.1 (hJa hj)
  have haJ : zpowers a ≤ normalizer (J : Set F) :=
    le_normalizer_of_le_centralizer ((zpowers_le (G := F)).2 haCJ)
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hCJa : centralizer (J : Set F) ⊓ centralizer ({a} : Set F) = zpowers a := by
    apply le_antisymm
    · rintro x ⟨hxJ, hxa⟩
      have hxa' : x ∈ ((zpowers a ⊔ J : Subgroup F) : Set F) := by
        rw [SetLike.mem_coe, hprod]
        exact hxa
      rw [coe_mul_of_left_le_normalizer_right _ _ haJ] at hxa'
      obtain ⟨k, hk, j, hj, hkj⟩ := hxa'
      have hkJ : ∀ j' ∈ J, k * j' = j' * k := fun j' hj' => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
        exact ((Commute.zpow_left (mem_centralizer_singleton_iff.1 (hJa hj')).symm n)).eq
      have hjZ : (⟨j, hj⟩ : J) ∈ center J := mem_center_iff.2 fun g => Subtype.ext (by
        have h1 := mem_centralizer_iff.1 hxJ g g.2
        rw [← hkj] at h1
        have h2 := hkJ g g.2
        show (g : F) * j = j * g
        calc (g : F) * j = k⁻¹ * (k * g) * j := by group
          _ = k⁻¹ * (g * k) * j := by rw [h2]
          _ = k⁻¹ * (g * (k * j)) := by group
          _ = k⁻¹ * (k * j * g) := by rw [h1]
          _ = j * g := by group)
      rw [hZJ, mem_bot] at hjZ
      have hj1 : j = 1 := congrArg Subtype.val hjZ
      subst hkj
      show k * j ∈ zpowers a
      rw [hj1, mul_one]
      exact hk
    · exact le_inf ((zpowers_le (G := F)).2 haCJ)
        ((zpowers_le (G := F)).2 (mem_centralizer_singleton_iff.2 rfl))
  have hE' : ∃ E : Subgroup F, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hEJ, hE, hE4⟩ := hJ4
    exact ⟨E, hEJ, ⟨hE.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) x hx⟩, hE4⟩
  have hCaN : centralizer ({a} : Set F) ≤ normalizer (J : Set F) := by
    rw [← hprod]
    exact sup_le haJ le_normalizer
  have hJn : (J.subgroupOf (centralizer ({a} : Set F))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJa).2 hCaN
  have hsylBK : ∃ S : Sylow 2 ↥(centralizer (J : Set F) ⊓ centralizer ({a} : Set F)),
      (S : Subgroup _).map (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).subtype =
        zpowers a := by
    have hP : IsPGroup 2 ((zpowers a).subgroupOf
        (centralizer (J : Set F) ⊓ centralizer ({a} : Set F))) :=
      hza.comap_of_injective _ (Subgroup.subtype_injective _)
    have hidx : ¬ 2 ∣ ((zpowers a).subgroupOf
        (centralizer (J : Set F) ⊓ centralizer ({a} : Set F))).index := by
      rw [Subgroup.subgroupOf_eq_top.2 hCJa.le, index_top]
      norm_num
    refine ⟨hP.toSylow hidx, ?_⟩
    rw [IsPGroup.toSylow_coe, subgroupOf_map_subtype, hCJa, inf_idem]
  obtain ⟨hinjJ, hinj2, hθa2, hJbs, hJbna, hJba, hJbn, hCaeq, -, hstd, hsylb, hconj⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hJna hE' ha hJa hJn hsylBK R hRodd
  have hinjC : Set.InjOn θ (centralizer ({a} : Set F) : Set F) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ R ⊓ centralizer ({a} : Set F) :=
      ⟨QuotientGroup.eq.mp hxy, (centralizer ({a} : Set F)).mul_mem
        ((centralizer ({a} : Set F)).inv_mem hx) hy⟩
    rw [hRa, mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hKH : CFSG.SectionRank.IsKGroupCat (F ⧸ R) := CFSG.SectionRank.IsKGroupCat.quotient hKF R
  have hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog (F ⧸ R) := by
    intro K L _ _ _ hsimple _
    exact hKH K (L.subgroupOf K) hsimple
  have hcoreH : CFSG.pPrimeCore 2 (F ⧸ R) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hncb := not_central_sylow_quotient R hRodd ha hnc
  have hcapb : zpowers (θ a) ⊓ J.map θ = ⊥ := by
    refine eq_bot_iff.2 fun x ⟨hx₁, hx₂⟩ => ?_
    rw [← MonoidHom.map_zpowers] at hx₁
    obtain ⟨y, hy, rfl⟩ := hx₁
    obtain ⟨j, hj, hjy⟩ := hx₂
    have hyC : y ∈ centralizer ({a} : Set F) := hprod ▸ mem_sup_left hy
    have hjC : j ∈ centralizer ({a} : Set F) := hJa hj
    have hyj : j = y := hinjC hjC hyC hjy
    have hy1 : y ∈ zpowers a ⊓ J := ⟨hy, hyj ▸ hj⟩
    rw [hcap, mem_bot] at hy1
    rw [hy1, map_one]
    exact one_mem _
  have hprodb : zpowers (θ a) ⊔ J.map θ = centralizer ({θ a} : Set (F ⧸ R)) := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup, hprod, hCaeq]
  have hidxb : ¬ 2 ∣ (zpowers (θ a)).relIndex (centralizer (J.map θ : Set (F ⧸ R))) := by
    obtain ⟨S, hS⟩ := hsylb
    rw [Subgroup.relIndex, ← hS]
    have hc : ((S : Subgroup _).map (centralizer (J.map θ : Set (F ⧸ R))).subtype).subgroupOf
        (centralizer (J.map θ : Set (F ⧸ R))) = S :=
      comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [hc]
    exact S.not_dvd_index
  have hJbnn : ¬ (J.map θ).Normal := by
    intro hN
    set B := centralizer (J.map θ : Set (F ⧸ R)) with hBdef
    have hcoreB : CFSG.pPrimeCore 2 B = ⊥ := by
      have hle : (CFSG.pPrimeCore 2 B).map B.subtype ≤ CFSG.pPrimeCore 2 (F ⧸ R) := by
        refine le_sSup ⟨inferInstance, ?_⟩
        rw [card_map_of_injective B.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
      rw [hcoreH, le_bot_iff, map_eq_bot_iff_of_injective _ B.subtype_injective] at hle
      exact hle
    obtain ⟨S, hS⟩ := hsylb
    have hS2 : Nat.card (S : Subgroup B) = 2 := by
      have h := congrArg (fun X : Subgroup (F ⧸ R) => Nat.card X) hS
      rwa [card_map_of_injective B.subtype_injective, Nat.card_zpowers, hθa2] at h
    have hStop := eq_top_of_card_sylow_eq_two hcoreB S hS2
    have hBeq : B = zpowers (θ a) := by
      rw [← hS, hStop, ← MonoidHom.range_eq_map, range_subtype]
    have hcent : ∀ g : F ⧸ R, g * θ a = θ a * g := by
      intro g
      have hmB : θ a ∈ B := hBeq ▸ mem_zpowers _
      have hm : g * θ a * g⁻¹ ∈ B := (inferInstance : B.Normal).conj_mem _ hmB g
      rw [hBeq] at hm
      rcases eq_one_or_eq_of_mem_zpowers hθa2 hm with h | h
      · exfalso
        have h1 : θ a = 1 := by
          calc θ a = g⁻¹ * (g * θ a * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [h1, orderOf_one] at hθa2
        exact absurd hθa2 (by norm_num)
      · calc g * θ a = g * θ a * g⁻¹ * g := by group
          _ = θ a * g := by rw [h]
    have hzb : IsPGroup 2 (zpowers (θ a)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hθa2, pow_one])
    obtain ⟨T, hT⟩ := hzb.exists_le_sylow
    obtain ⟨t, -, ht⟩ := hncb T (hT (mem_zpowers _))
    exact ht (hcent t)
  have hE4b : ∃ E : Subgroup (F ⧸ R), E ≤ J.map θ ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 4 := by
    obtain ⟨E, hEJ, hE, hE4⟩ := hJ4
    have : CFSG.IsElementaryAbelian 2 E := hE
    have hinjE : Function.Injective (θ.comp E.subtype) := fun x y hxy =>
      Subtype.ext (hinjJ (hEJ x.2) (hEJ y.2) hxy)
    refine ⟨E.map θ, map_mono hEJ, CFSG.IsElementaryAbelian.map θ, ?_⟩
    have hr : (θ.comp E.subtype).range = E.map θ := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← hE4]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv).symm
  have hCaNb : centralizer ({θ a} : Set (F ⧸ R)) ≤ normalizer (J.map θ : Set (F ⧸ R)) :=
    (normal_subgroupOf_iff_le_normalizer hJba).1 hJbn
  have hconcl := h1 (F ⧸ R) hKP hcoreH (J.map θ) hJbs hJbna hE4b (θ a) hθa2 hJba hCaNb hidxb
    hJbnn
  obtain ⟨hO2H, hFH, hJbE, hDE, hCD, halt, hfaith⟩ := hconcl
  have hlift := preimage_le_centralizer R ha hinvR hRab J halt
  set Q := normalClosure (J : Set F) with hQdef
  have hQmap : Q.map θ = normalClosure (J.map θ : Set (F ⧸ R)) := by
    rw [hQdef, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map]
  have hJQ : J ≤ Q := le_normalClosure
  have hQC : Q ≤ centralizer (R : Set F) :=
    (le_comap_map θ Q).trans (hQmap ▸ hlift)
  have hCDb : ∀ x : F, (∀ q ∈ Q, q * x = x * q) → x ∈ R := by
    intro x hx
    have h2 : θ x ∈ centralizer (normalClosure (J.map θ : Set (F ⧸ R)) : Set (F ⧸ R)) := by
      rw [mem_centralizer_iff]
      intro d hd
      rw [← hQmap] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      rw [← map_mul, ← map_mul, hx q hq]
    rw [hCD, mem_bot] at h2
    exact (QuotientGroup.eq_one_iff x).1 h2
  refine ⟨⟨hRab, hinvR, hRa⟩, ⟨hinjJ, hinjC, hinj2⟩, ⟨hKH, hKP, hcoreH⟩, ⟨hJba, hcapb, hprodb⟩,
    hncb, ⟨isStandardSubgroup_of_assembly hJbna hstd, hidxb, ?_, hJbnn⟩,
    ⟨hO2H, hFH, hJbE, hDE, hCD, halt, hfaith⟩,
    ⟨fun x hx r hr => (mem_centralizer_iff.1 (hlift hx) r hr).symm,
      commutator_eq_bot_iff_le_centralizer.2 (hJQ.trans hQC)⟩, ?_, ?_, ?_⟩
  ·
    intro t ht ht2
    obtain ⟨h, hh, hht⟩ := hconj t ht ht2
    refine ⟨h⁻¹, inv_mem hh, ?_⟩
    rw [← hht]
    show _ = QuotientGroup.mk' R a
    group
  ·
    refine ⟨normalClosure_normal, ?_, hQmap, ?_, ?_, ?_, ?_⟩
    · apply le_antisymm (commutator_le_left Q Q)
      refine normalClosure_le_normal fun j hj => ?_
      have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 (isQuasisimple_of_simple hJna).1
      exact Subgroup.commutator_mono hJQ hJQ (hJperf.symm ▸ hj : j ∈ ⁅J, J⁆)
    · rw [← hQmap, comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    · apply le_antisymm
      · intro z hz
        obtain ⟨hzQ, hzC⟩ := (mem_map_center_iff Q).1 hz
        exact ⟨hzQ, hCDb z fun q hq => mem_centralizer_iff.1 hzC q hq⟩
      · rintro z ⟨hzQ, hzR⟩
        refine (mem_map_center_iff Q).2 ⟨hzQ, mem_centralizer_iff.2 fun q hq => ?_⟩
        exact (mem_centralizer_iff.1 (hQC hq) z hzR).symm
    · apply le_antisymm
      · intro x hx
        exact hCDb x fun q hq => mem_centralizer_iff.1 hx q hq
      · intro r hr
        rw [mem_centralizer_iff]
        intro q hq
        exact (mem_centralizer_iff.1 (hQC hq) r hr).symm
    · let θQ : Q →* normalClosure (J.map θ : Set (F ⧸ R)) :=
        (θ.comp Q.subtype).codRestrict _ fun q => hQmap ▸ mem_map_of_mem θ q.2
      have hθQs : Function.Surjective θQ := by
        rintro ⟨d, hd⟩
        rw [← hQmap] at hd
        obtain ⟨q, hq, rfl⟩ := hd
        exact ⟨⟨q, hq⟩, rfl⟩
      have hker : θQ.ker = R.subgroupOf Q := by
        ext q
        rw [MonoidHom.mem_ker, mem_subgroupOf]
        constructor
        · intro h
          exact (QuotientGroup.eq_one_iff (q : F)).1 (congrArg Subtype.val h)
        · intro h
          exact Subtype.ext ((QuotientGroup.eq_one_iff (q : F)).2 h)
      refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θQ hθQs), fun q => rfl⟩
  · exact ⟨Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_right), fun r hr => hinvR r hr.2⟩
  · refine ⟨?_, ?_⟩
    ·
      have hle : (CFSG.pCore 2 F).map θ ≤ CFSG.pCore 2 (F ⧸ R) :=
        le_sSup ⟨(inferInstance : (CFSG.pCore 2 F).Normal).map θ
          (QuotientGroup.mk'_surjective R), CFSG.pCore_isPGroup.map θ⟩
      rw [hO2H, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
      refine eq_bot_iff.2 fun x hx => mem_bot.2 ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := F)) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hk
      have h3 : orderOf x ∣ Nat.card R := by
        have := orderOf_dvd_natCard (⟨x, hle hx⟩ : R)
        rwa [Subgroup.orderOf_mk] at this
      rw [hk] at h3
      have hk0 : k = 0 := by
        by_contra hk0
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        exact Nat.not_even_iff_odd.2 hRodd
          (even_iff_two_dvd.2 ((dvd_pow_self 2 j.succ_ne_zero).trans h3))
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    ·
      apply le_antisymm
      · have hFn : (CFSG.fittingSubgroup F).Normal := (fitting_characteristic (G := F)).2.1
        have hFnil : Group.IsNilpotent (CFSG.fittingSubgroup F) :=
          (fitting_nilpotent (G := F)).1
        have hmapnil : Group.IsNilpotent ((CFSG.fittingSubgroup F).map θ) :=
          Group.nilpotent_of_surjective ((θ.comp (CFSG.fittingSubgroup F).subtype).codRestrict
            _ fun x => mem_map_of_mem θ x.2) (by
              rintro ⟨y, x, hx, rfl⟩
              exact ⟨⟨x, hx⟩, rfl⟩)
        have hle := (fitting_characteristic (G := F ⧸ R)).2.2 _
          (hFn.map θ (QuotientGroup.mk'_surjective R)) hmapnil
        rw [hFH, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
        exact hle
      · let _ : CommGroup R := { (inferInstance : Group R) with mul_comm := hRab.is_comm.comm }
        have : Group.IsNilpotent R := inferInstance
        exact (fitting_characteristic (G := F)).2.2 R inferInstance this

theorem direct_simple_involution_centralizer_layer_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog) :
    DirectSimpleInvolutionCentralizerLayerStmt :=
  direct_simple_involution_centralizer_layer_of
    (nonnormal_involution_component_layer_of_schreier hS)

end CFSG.LocalAnalysis.SteinbergBV
