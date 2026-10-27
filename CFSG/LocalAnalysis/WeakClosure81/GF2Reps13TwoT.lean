module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private def w16g_Faith {W : Type*} [CommGroup W] (G : Subgroup (MulAut W))
    (U : Subgroup W) : Prop :=
  ∀ y ∈ G, (∀ u ∈ U, y u = u) → y = 1

private theorem w16g_mem_map_subtype {W : Type*} [CommGroup W] {V₀ : Subgroup W}
    {U : Subgroup ↥V₀} {u : ↥V₀} : (u : W) ∈ U.map V₀.subtype ↔ u ∈ U :=
  Subgroup.mem_map_iff_mem V₀.subtype_injective

private theorem w16g_map_inclusion_subgroupOf {W : Type} [CommGroup W]
    {G K : Subgroup (MulAut W)} (hGK : G ≤ K) {P : Subgroup (MulAut W)} (hPG : P ≤ G) :
    (P.subgroupOf G).map (Subgroup.inclusion hGK) = P.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact ⟨⟨(x : MulAut W), hPG (Subgroup.mem_subgroupOf.mp hx)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩

private theorem w16g_subgroupOf_commutator {M : Type} [Group M] {H₁ H₂ K : Subgroup M}
    (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le h₁ h₂)]

private theorem w16g_stableUnder_range {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (U : Subgroup ↥V₀) :
    StableUnder σ.range U ↔ StableUnder G (U.map V₀.subtype) := by
  constructor
  · intro hstable x hx w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    have hmem : σ ⟨x, hx⟩ u ∈ U :=
      hstable _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) u hu
    exact Subgroup.mem_map.mpr ⟨_, hmem, hσ ⟨x, hx⟩ u⟩
  · intro hstable y hy u hu
    obtain ⟨xg, rfl⟩ := MonoidHom.mem_range.mp hy
    have hmem : (xg : MulAut W) (u : W) ∈ U.map V₀.subtype :=
      hstable xg xg.2 (u : W) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    rw [← hσ xg u] at hmem
    exact w16g_mem_map_subtype.mp hmem

private theorem w16g_faith_range {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (hσinj : Function.Injective σ)
    (U : Subgroup ↥V₀) :
    w16g_Faith σ.range U ↔ w16g_Faith G (U.map V₀.subtype) := by
  constructor
  · intro h x hx hfix
    have hσ1 : σ ⟨x, hx⟩ = 1 := by
      refine h _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) ?_
      intro u hu
      apply Subtype.ext
      rw [hσ]
      simpa using hfix (u : W) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    have hG : (⟨x, hx⟩ : G) = 1 := hσinj (by rw [hσ1, map_one])
    exact congrArg Subtype.val hG
  · intro h y hy hfix
    obtain ⟨xg, rfl⟩ := MonoidHom.mem_range.mp hy
    have hxg1 : (xg : MulAut W) = 1 := by
      refine h xg xg.2 ?_
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      have := congrArg Subtype.val (hfix u hu)
      rw [hσ] at this
      exact this
    rw [show xg = 1 from Subtype.ext hxg1, map_one]

private theorem w16g_map_commSub_le {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (x : G) :
    (commSub ⊤ (Subgroup.zpowers (σ x))).map V₀.subtype ≤
      commSub V₀ (Subgroup.zpowers (x : MulAut W)) := by
  rw [commSub, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro c ⟨d, hd, rfl⟩
  obtain ⟨y, hy, v, _, hdxy⟩ := hd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  change (d : W) ∈ {c | ∃ z ∈ Subgroup.zpowers (x : MulAut W), ∃ w ∈ V₀, z w * w⁻¹ = c}
  refine ⟨(x : MulAut W) ^ n, Subgroup.zpow_mem_zpowers _ _, (v : W), v.2, ?_⟩
  have hleft : ((x : MulAut W) ^ n) (v : W) = (((σ x) ^ n) v : W) := by
    rw [← map_zpow, hσ, Subgroup.coe_zpow]
  rw [← hdxy, ← hn, Subgroup.coe_mul, Subgroup.coe_inv, hleft]

private theorem w16g_isPOnePlusTwo_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨isExtraspecial_of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_isZ3Times_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsZ3TimesPOnePlusTwo X) : IsZ3TimesPOnePlusTwo Y := by
  obtain ⟨H, hinstH, hP, ⟨f⟩⟩ := h
  letI := hinstH
  exact ⟨H, hinstH, hP, ⟨e.symm.trans f⟩⟩

private theorem w16g_isZ3WrZ3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsZ3WrZ3 X) : IsZ3WrZ3 Y := by
  obtain ⟨hcard, z, b, hz, hcomm, hb, hconj, hgen⟩ := h
  refine ⟨?_, fun i => e (z i), e b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hcard]
  · intro i; rw [← map_pow, hz i, map_one]
  · intro i j; exact (hcomm i j).map e
  · rw [← map_pow, hb, map_one]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hconj i]
  · have himg : Set.range (fun i => e (z i)) ∪ {e b} =
        (e : X →* Y) '' (Set.range z ∪ {b}) := by
      ext y
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨z i, Or.inl ⟨i, rfl⟩, rfl⟩
        · exact ⟨b, Or.inr rfl, rfl⟩
      · rintro ⟨x, hx | rfl, rfl⟩
        · obtain ⟨i, rfl⟩ := hx; exact Or.inl ⟨i, rfl⟩
        · exact Or.inr rfl
    have hmap := MonoidHom.map_closure (e : X →* Y) (Set.range z ∪ {b})
    rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    rw [← himg] at hmap
    exact hmap.symm

theorem w4Lem13_2Shape_of_minLe (n : ℕ) (h : W4Lem13_2MinLe n) : W4Lem13_2ShapeLe n := by
  intro W _ _ hW2 t ht2 htrk p P hp hPgrp hPne htP hcomm hPn
  classical
  let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hPG : P ≤ G := le_sup_left
  have ht2sq : (t : MulAut W) ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  let Faith : Subgroup W → Prop := fun U => (∀ y ∈ G, (∀ u ∈ U, y u = u) → y = 1)
  have hex : ∃ n : ℕ, ∃ U : Subgroup W, StableUnder G U ∧ Faith U ∧ Nat.card U = n :=
    ⟨Nat.card (⊤ : Subgroup W), (⊤ : Subgroup W), fun _ _ _ _ => Subgroup.mem_top _,
      fun y _ hy => by ext w; exact hy w (Subgroup.mem_top w), rfl⟩
  let V₀ : Subgroup W := Classical.choose (Nat.find_spec hex)
  have hV₀spec : StableUnder G V₀ ∧ Faith V₀ ∧ Nat.card V₀ = Nat.find hex :=
    Classical.choose_spec (Nat.find_spec hex)
  have hV₀stab : StableUnder G V₀ := hV₀spec.1
  have hV₀faith : Faith V₀ := hV₀spec.2.1
  have hV₀card : Nat.card V₀ = Nat.find hex := hV₀spec.2.2
  have hV₀min : ∀ U : Subgroup W, StableUnder G U → Faith U → Nat.card V₀ ≤ Nat.card U := by
    intro U hU1 hU2
    rw [hV₀card]
    exact Nat.find_min' hex ⟨U, hU1, hU2, rfl⟩
  have hGV : G ≤ stabSub V₀ := by
    intro x hx
    rw [mem_stabSub]
    intro v
    exact ⟨fun hv => by simpa using hV₀stab x⁻¹ (G.inv_mem hx) (x v) hv,
      fun hv => hV₀stab x hx v hv⟩
  let σ : G →* MulAut ↥V₀ := (resHom V₀).comp (Subgroup.inclusion hGV)
  have hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W) := by
    intro x u
    change (((resHom V₀) (Subgroup.inclusion hGV x)) u : W) = (x : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hcent : (x : MulAut W) ∈ centSub V₀ := by
        rw [mem_centSub]
        intro u hu
        have h1 := congrArg (fun φ : MulAut ↥V₀ => (φ ⟨u, hu⟩ : W)) hx
        rw [hσ x ⟨u, hu⟩] at h1
        simpa using h1
      exact Subtype.ext (hV₀faith x x.2 (mem_centSub.mp hcent))
    · intro hx
      rw [hx, map_one]
  let t' : MulAut ↥V₀ := σ ⟨t, htG⟩
  have hW'2 : ∀ w : ↥V₀, w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using hW2 (w : W)
  have ht'sq : t' ^ 2 = 1 := by
    change σ ⟨t, htG⟩ ^ 2 = 1
    rw [← map_pow]
    have h2 : (⟨t, htG⟩ : G) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one] using ht2sq
    rw [h2, map_one]
  have ht'ne : t' ≠ 1 := by
    intro h1
    have hσt1 : σ ⟨t, htG⟩ = 1 := h1
    have hG1 : (⟨t, htG⟩ : G) = 1 := hσinj (by rw [hσt1, map_one])
    have ht1 : (t : MulAut W) = 1 := congrArg Subtype.val hG1
    rw [ht1, orderOf_one] at ht2
    omega
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'sq ht'ne
  have hmapσ : (P.subgroupOf G).map σ = autSub P V₀ := by
    rw [show σ = (resHom V₀).comp (Subgroup.inclusion hGV) from rfl]
    rw [← Subgroup.map_map (K := P.subgroupOf G)
      (g := resHom V₀) (f := Subgroup.inclusion hGV)]
    rw [w16g_map_inclusion_subgroupOf hGV hPG]
    rfl
  have hzp : ((Subgroup.zpowers t).subgroupOf G).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G = Subgroup.zpowers (⟨t, htG⟩ : G) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]

  have hG'eq : autSub P V₀ ⊔ Subgroup.zpowers t' = σ.range := by
    have hsub : (P.subgroupOf G) ⊔ ((Subgroup.zpowers t).subgroupOf G) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPG (Subgroup.zpowers_le.mpr htG),
        show P ⊔ Subgroup.zpowers t = G from rfl, Subgroup.subgroupOf_self]
    calc autSub P V₀ ⊔ Subgroup.zpowers t'
        = (P.subgroupOf G).map σ ⊔ ((Subgroup.zpowers t).subgroupOf G).map σ := by
            rw [hmapσ, hzp]
      _ = ((P.subgroupOf G) ⊔ ((Subgroup.zpowers t).subgroupOf G)).map σ := by
            rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup G).map σ := by rw [hsub]
      _ = σ.range := (MonoidHom.range_eq_map σ).symm
  have ht'norm : ∀ x ∈ autSub P V₀, t' * x * t'⁻¹ ∈ autSub P V₀ := by
    intro x hx
    rw [← hmapσ] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨t, htG⟩ * q * ⟨t, htG⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change t * (q : MulAut W) * t⁻¹ ∈ P
      exact htP _ (Subgroup.mem_subgroupOf.mp hq)
    · rw [map_mul, map_mul, map_inv]
  have hcomm' : ⁅autSub P V₀, Subgroup.zpowers t'⁆ = autSub P V₀ := by
    have hcommG : ⁅P.subgroupOf G, (Subgroup.zpowers t).subgroupOf G⁆ = P.subgroupOf G := by
      rw [w16g_subgroupOf_commutator hPG (Subgroup.zpowers_le.mpr htG), hcomm]
    have hmap := Subgroup.map_commutator (P.subgroupOf G)
      ((Subgroup.zpowers t).subgroupOf G) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have hmin' : ∀ U : Subgroup ↥V₀, StableUnder (autSub P V₀ ⊔ Subgroup.zpowers t') U →
      (∀ y ∈ autSub P V₀ ⊔ Subgroup.zpowers t', (∀ u ∈ U, y u = u) → y = 1) → U = ⊤ := by
    intro U hU hUf
    have hU0stab : StableUnder G (U.map V₀.subtype) := by
      rw [← w16g_stableUnder_range σ hσ U, ← hG'eq]
      exact hU
    have hU0f : w16g_Faith G (U.map V₀.subtype) := by
      rw [← w16g_faith_range σ hσ hσinj U, ← hG'eq]
      exact hUf
    have hcard := hV₀min (U.map V₀.subtype) hU0stab hU0f
    have hle : U.map V₀.subtype ≤ V₀ := Subgroup.map_subtype_le _
    have heq : U.map V₀.subtype = V₀ := Subgroup.eq_of_le_of_card_ge hle hcard
    have htop : (⊤ : Subgroup ↥V₀).map V₀.subtype = V₀ := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective V₀.subtype_injective (heq.trans htop.symm)
  let ρ : P →* MulAut ↥V₀ := σ.comp (Subgroup.inclusion hPG)
  have hρrange : ρ.range = autSub P V₀ := by
    rw [show ρ = σ.comp (Subgroup.inclusion hPG) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range hPG, hmapσ]
  have hρinj : Function.Injective ρ := hσinj.comp (Subgroup.inclusion_injective hPG)
  let ePP' : ↥P ≃* ↥(autSub P V₀) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hP'grp : IsPGroup p ↥(autSub P V₀) := by
    intro y
    obtain ⟨x, rfl⟩ := ePP'.surjective y
    obtain ⟨n, hn⟩ := hPgrp x
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hP'ne : autSub P V₀ ≠ ⊥ := by
    intro hbot
    apply hPne
    have hcard : Nat.card ↥P = 1 := by
      rw [Nat.card_congr ePP'.toEquiv, hbot]
      simp
    exact (Subgroup.card_eq_one).mp hcard
  have hmaple := w16g_map_commSub_le σ hσ ⟨t, htG⟩
  have hle : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t'))
        = rk ↥((commSub ⊤ (Subgroup.zpowers t')).map V₀.subtype) := by
            unfold rk
            rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
              (f := V₀.subtype) V₀.subtype_injective]
      _ ≤ rk ↥(commSub V₀ (Subgroup.zpowers t)) := rk_mono hmaple
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono (commSub_mono le_top le_rfl)
  have htrk' : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 3 := hle.trans htrk
  have hcardle : Nat.card ↥(autSub P V₀) ≤ n := by
    rw [← Nat.card_congr ePP'.toEquiv]
    exact hPn
  have hconc := h (↥V₀) hW'2 t' ht'2 htrk' p (autSub P V₀) hp hP'grp hP'ne ht'norm hcomm'
    hcardle hmin'
  rcases hconc with ⟨hcyc, hcard⟩ | ⟨n, hn, hE⟩ | ⟨hP1, _⟩ | ⟨hZ, hrk, _⟩
  · exact Or.inl ⟨(MulEquiv.isCyclic ePP').mpr hcyc,
      by rw [Nat.card_congr ePP'.toEquiv]; exact hcard⟩
  · exact Or.inr (Or.inl ⟨n, hn, IsElemAbelianOfRank.of_mulEquiv ePP'.symm hE⟩)
  · exact Or.inr (Or.inr (Or.inl (w16g_isPOnePlusTwo_of_mulEquiv ePP'.symm hP1)))
  · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
    · rcases hZ with hZ | hZ
      · exact Or.inl (w16g_isZ3Times_of_mulEquiv ePP'.symm hZ)
      · exact Or.inr (w16g_isZ3WrZ3_of_mulEquiv ePP'.symm hZ)
    · exact le_antisymm htrk (hrk ▸ hle)

theorem w4Lem13_2Shape_of_min (h : W4Lem13_2Min) :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
        ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
          (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P →
            (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
            (∃ n : ℕ, n ≤ 3 ∧ IsElemAbelianOfRank 3 n ↥P) ∨
            IsPOnePlusTwo 3 ↥P ∨
            ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
              rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3) := by
  intro W _ _ hW t ht hrk p P hp hP hne hn hc
  exact w4Lem13_2Shape_of_minLe (Nat.card P)
    (fun W' _ _ hW' t' ht' hrk' p' P' hp' hP' hne' hn' hc' _ hmin' =>
      h W' hW' t' ht' hrk' p' P' hp' hP' hne' hn' hc' hmin') W hW t ht hrk p P hp hP hne hn hc
    le_rfl

end CFSG.LocalAnalysis.WeakClosure81
