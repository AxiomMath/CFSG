module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4B

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_le_normalizer {T Y : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y ≤ T :=
  (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 Y) (hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y)))
    (pCoreOf_isPGroup 2 Y)).trans
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT le_sup_right))

theorem le_normalizer_conjClosure_of {Y B T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hB : Odd (Nat.card B)) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hc : ⁅Y, B⁆ ≤ pCoreOf 2 Y) : Y ≤ Subgroup.normalizer (conjClosure B T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  refine le_normalizer_conjClosure_of_mem hB (pCoreOf_isPGroup 2 Y)
    ((pCoreOf_le_of_le_normalizer hT hTY).trans (le_normalizer_conjClosure B T))
    (le_normalizer_pCoreOf 2 Y) fun y hy t ht b hb => ?_
  have hy' : t⁻¹ * y * t ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) y).mp hy
    simpa using this
  have h1 : t⁻¹ * y * t * b * (t⁻¹ * y * t)⁻¹ * b⁻¹ ∈ pCoreOf 2 Y :=
    hc (Subgroup.commutator_mem_commutator hy' hb)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hTO ht) _).mp h1
  have e : y * (t * b * t⁻¹) * y⁻¹ * (t * b * t⁻¹)⁻¹ =
      t * (t⁻¹ * y * t * b * (t⁻¹ * y * t)⁻¹ * b⁻¹) * t⁻¹ := by group
  rw [e]
  exact h2

omit [Finite G] in
theorem le_centralizer_of_simple {K X V : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hVK : V ≤ K) (hV : V ≠ ⊥)
    (hXV : X ≤ Subgroup.centralizer (V : Set G)) : K ≤ Subgroup.centralizer (X : Set G) := by
  set C := Subgroup.centralizer (X : Set G) with hC
  have hn : ((K ⊓ C).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, normalizer_le_normalizer_centralizer X (hKX hk)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ C).subgroupOf K) with h | h
  · exfalso
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have hvC : v ∈ C := Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hXV hx) v hv).symm
    have : (⟨v, hVK hv⟩ : ↥K) ∈ (K ⊓ C).subgroupOf K := ⟨hVK hv, hvC⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ C).subgroupOf K := h ▸ Subgroup.mem_top _
    exact this.2

theorem le_normalizer_of_le_centralizer {K B T : Subgroup G}
    (hcore : perfectCore (Subgroup.normalizer (B : Set G)) = K) (hKp : ⁅K, K⁆ = K)
    (hKX : K ≤ Subgroup.centralizer (conjClosure B T : Set G)) :
    T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  set φ := (MulAut.conj t⁻¹).toMonoidHom with hφ
  have hK' : K.map φ ≤ Subgroup.normalizer (B : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    have h1 := Subgroup.mem_centralizer_iff.mp (hKX hk) _ (mem_conjClosure ht hb)
    show b * (t⁻¹ * k * t⁻¹⁻¹) = t⁻¹ * k * t⁻¹⁻¹ * b
    calc b * (t⁻¹ * k * t⁻¹⁻¹) = t⁻¹ * ((t * b * t⁻¹) * k) * t := by group
      _ = t⁻¹ * (k * (t * b * t⁻¹)) * t := by rw [h1]
      _ = t⁻¹ * k * t⁻¹⁻¹ * b := by group
  have hperf : ⁅K.map φ, K.map φ⁆ = K.map φ := by rw [← Subgroup.map_commutator, hKp]
  have hle : K.map φ ≤ K := (le_perfectCore_of_perfect hK' hperf).trans hcore.le
  have heq : K.map φ = K := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective])
  have h1 : t⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  simpa using Subgroup.inv_mem _ h1

omit [Finite G] in
theorem exists_mem_center [Finite G] {V T : Subgroup G} (hT : IsPGroup 2 ↥T) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hn : (V.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨x, hxV, hxZ⟩, hx1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨x, hxV, fun h => hx1 (Subtype.ext (Subtype.ext h)), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem isSylowTwoOf_inf {T A Y : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = A ⊔ pCoreOf 2 Y) :
    IsSylowTwoOf (T ⊓ A) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 Y with hQ
  have hAY : A ≤ Y := by rw [hY]; exact le_sup_left
  have hQT : Q ≤ T := pCoreOf_le_of_le_normalizer hT hTY
  have hTH : IsSylowTwoOf T (Y ⊔ T) := isSylowTwoOf_of_le hT le_sup_right
  have hYn : (Y.subgroupOf (Y ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTY)
  have hSY := A312.isSylowTwoOf_inf_of_subnormal (A3.subnormal_of_normal le_sup_left hYn) hTH
  refine ⟨inf_le_right, hT.1.to_le inf_le_left, ?_⟩
  rw [Subgroup.inf_subgroupOf_right]
  have hQ'n : (Q.subgroupOf Y).Normal := normal_pCoreOf_subgroupOf Y
  set π := QuotientGroup.mk' (Q.subgroupOf Y) with hπ
  set ρ : ↥A →* ↥Y ⧸ Q.subgroupOf Y := π.comp (Subgroup.inclusion hAY) with hρ
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hAY.trans (le_normalizer_pCoreOf 2 Y)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Y) y
    have hy : (y : G) ∈ A ⊔ Q := hY ▸ y.2
    obtain ⟨a, ha, q, hq, e⟩ := (mem_sup_of_le_normalizer hAQ).mp hy
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show a⁻¹ * (y : G) ∈ Q
    rw [← e]
    simpa using hq
  have h1 : ((T.subgroupOf Y).map π).comap ρ = T.subgroupOf A := by
    ext a
    simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hya⟩
      rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf] at hya
      have h2 : (y : G)⁻¹ * a ∈ T := hQT hya
      have h3 : (a : G) = y * ((y : G)⁻¹ * a) := by group
      rw [h3]
      exact T.mul_mem hy h2
    · intro ha
      exact ⟨Subgroup.inclusion hAY a, ha, rfl⟩
  have h2 : ((T.subgroupOf Y).map π).comap π = T.subgroupOf Y := by
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left]
    exact fun x hx => hQT hx
  rw [← h1, Subgroup.index_comap_of_surjective _ hρs,
    ← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (Q.subgroupOf Y)), ← hπ,
    h2]
  have := hSY.2.2
  rwa [Subgroup.inf_subgroupOf_right] at this

end CFSG.Quasithin.H13.Ch4.G443J4
