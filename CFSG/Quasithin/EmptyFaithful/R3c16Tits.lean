module

public import CFSG.Quasithin.EmptyFaithful.R3c14Cfg
public import CFSG.Sporadic.Schreier.TitsQTInner
public import CFSG.Sporadic.Schreier.TitsQTStrong
public import CFSG.Quasithin.Recognition.CertTitsOvergroup

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c14
open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem exists_central_of_normal {T V : Subgroup G} (hT : IsPGroup 2 ↥T) (hVT : V ≤ T)
    (hV : V ≠ ⊥) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, t * v = v * t := by
  classical
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hVn : (V.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hV1 : V.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hV
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hVT hx⟩ : ↥T) ∈ V.subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
  obtain ⟨⟨⟨v, hvT⟩, hvmem⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  refine ⟨v, Subgroup.mem_subgroupOf.mp hvmem.1, fun h => hv1 (Subtype.ext (Subtype.ext h)),
    fun t ht => ?_⟩
  have := Subgroup.mem_center_iff.mp hvmem.2 ⟨t, ht⟩
  exact congrArg Subtype.val this

end Abstract

section Tits

theorem not_elData_titsD
    {V H : Subgroup titsD} {ζ : MulAut titsD}
    (h : ElData (titsSylow : Subgroup titsD) V H ζ) : False := by
  obtain ⟨b, hbS, hb⟩ := titsD_sylow_pointwise_inner ζ h.fixT
  have hbN : b ∈ Subgroup.normalizer ((titsSylow : Subgroup titsD) : Set titsD) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun s hs => (hbS s hs).symm
  have hbSyl : b ∈ (titsSylow : Subgroup titsD) := by
    rw [coe_titsSylow] at hbN ⊢
    exact CFSG.Quasithin.titsSD_normalizer_le hbN
  have hV0 : V ≠ ⊥ := by
    intro hb0
    have h4 := h.V4
    rw [hb0, Subgroup.card_bot] at h4
    omega
  obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal titsSylow.isPGroup' h.VT hV0 h.TV
  have hvS : v ∈ (titsSylow : Subgroup titsD) := h.VT hvV
  have hvz : v = titsZD := (titsSylow_central_eq v hvS hvc).resolve_left hv1
  rcases titsSylow_central_eq b hbSyl (fun p hp => (hbS p hp).symm) with hb1 | hbz
  ·
    apply h.ne
    ext y
    rw [hb y, hb1]
    simp
  ·
    apply hv1
    refine h.fix v hvV fun k hk => ?_
    have hk' := h.fixH k hk
    rw [hb k, hbz, ← hvz] at hk'
    calc k * v = (v * k * v⁻¹) * v := by rw [hk']
      _ = v * k := by group

theorem not_elConfig_titsD :
    ¬ ElConfig titsD := by
  intro hc
  have hsyl : IsSylowTwoOf (titsSylow : Subgroup titsD) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨titsSylow.isPGroup', titsSylow.not_dvd_index⟩
  obtain ⟨V, H, ζ, hd⟩ := ElConfig.of_sylow hsyl hc
  exact not_elData_titsD hd

theorem not_elConfig_of_tits
    {X : Type} [Group X]
    (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) : ¬ ElConfig X := by
  intro hc
  obtain ⟨e⟩ := titsModelEquiv X 2 1 h
  exact not_elConfig_titsD (ElConfig.map e hc)

theorem no_two_klein_tits
    {X : Type} [Group X] [Finite X] (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1)
    {T V₁ V₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hV₁T : V₁ ≤ T) (hV₂T : V₂ ≤ T)
    (h4₁ : Nat.card V₁ = 4) (h4₂ : Nat.card V₂ = 4)
    (hN₁ : T ≤ Subgroup.normalizer (V₁ : Set X)) (hN₂ : T ≤ Subgroup.normalizer (V₂ : Set X))
    (hinf : V₁ ⊓ V₂ = ⊥) : False := by
  obtain ⟨ψ⟩ := titsModelEquiv X 2 1 h
  have hT' : IsSylowTwoOf (T.map ψ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map ψ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective]
    exact hi
  have hsyl : IsSylowTwoOf (titsSylow : Subgroup titsD) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨titsSylow.isPGroup', titsSylow.not_dvd_index⟩
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT' hsyl
  set Φ : X ≃* titsD := ψ.trans (MulAut.conj g) with hΦ
  have hΦT : T.map Φ.toMonoidHom = (titsSylow : Subgroup titsD) := by
    rw [← hg, Subgroup.map_map]
    rfl
  have key : ∀ V : Subgroup X, V ≤ T → Nat.card V = 4 →
      T ≤ Subgroup.normalizer (V : Set X) →
        ∃ v ∈ V.map Φ.toMonoidHom, v ≠ 1 ∧ v = titsZD := by
    intro V hVT hV4 hNV
    have hV0 : V.map Φ.toMonoidHom ≠ ⊥ := by
      intro hb
      have h1 : Nat.card (V.map Φ.toMonoidHom) = 4 := by
        rw [← hV4]
        exact (Nat.card_congr (V.equivMapOfInjective Φ.toMonoidHom Φ.injective).toEquiv).symm
      rw [hb, Subgroup.card_bot] at h1
      omega
    have hVS : V.map Φ.toMonoidHom ≤ (titsSylow : Subgroup titsD) := hΦT ▸ Subgroup.map_mono hVT
    have hSV : (titsSylow : Subgroup titsD) ≤
        Subgroup.normalizer ((V.map Φ.toMonoidHom : Subgroup titsD) : Set titsD) := by
      rw [← hΦT]
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      exact (R3c11.mem_normalizer_map_equiv_iff Φ V t₀).mpr (hNV ht₀)
    obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal titsSylow.isPGroup' hVS hV0 hSV
    exact ⟨v, hvV, hv1, (titsSylow_central_eq v (hVS hvV) hvc).resolve_left hv1⟩
  obtain ⟨v₁, hv₁, hv₁1, hv₁z⟩ := key V₁ hV₁T h4₁ hN₁
  obtain ⟨v₂, hv₂, -, hv₂z⟩ := key V₂ hV₂T h4₂ hN₂
  have hz : v₁ ∈ V₁.map Φ.toMonoidHom ⊓ V₂.map Φ.toMonoidHom :=
    ⟨hv₁, by rw [hv₁z, ← hv₂z]; exact hv₂⟩
  rw [← Subgroup.map_inf _ _ _ Φ.injective, hinf, Subgroup.map_bot] at hz
  exact hv₁1 (Subgroup.mem_bot.mp hz)

end Tits

end CFSG.Quasithin.R3c16
