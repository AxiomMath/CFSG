module

public import CFSG.Quasithin.Background.S1549CIn
public import CFSG.Quasithin.EmptyFaithful.S1565E
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.EmptyFaithful.S153D26

public section


namespace CFSG.Quasithin

namespace S1549D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C
open scoped commutatorElement Pointwise

section Vec

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem mem_normalizer_of_mem_conjClosure (h : HypF91 T V L V₁ Vp H) {u : G}
    (hu : u ∈ conjClosure Vp H) : u ∈ Subgroup.normalizer (V₁ : Set G) :=
  h.H_normalizes_V₁ (pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf hu))

@[expose] noncomputable def vecOf (h : HypF91 T V L V₁ Vp H) (a : G) (ha : a ∈ conjClosure Vp H) :
    ↥(tildeOf V₁ (conjClosure Vp H)) :=
  ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, mem_normalizer_of_mem_conjClosure h ha⟩,
    secMk_mem_secImg ha⟩

theorem vecOf_coe (h : HypF91 T V L V₁ Vp H) (a : G) (ha : a ∈ conjClosure Vp H) :
    ((vecOf h a ha : ↥(tildeOf V₁ (conjClosure Vp H))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, mem_normalizer_of_mem_conjClosure h ha⟩ := rfl

theorem vecOf_eq_one_iff (h : HypF91 T V L V₁ Vp H) {a : G} (ha : a ∈ conjClosure Vp H) :
    vecOf h a ha = 1 ↔ a ∈ V₁ := by
  rw [← Subtype.coe_inj, vecOf_coe, show ((1 : ↥(tildeOf V₁ (conjClosure Vp H))) :
    SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) = 1 from rfl]
  exact secMk_eq_one_iff

theorem vecOf_eq_vecOf_iff (h : HypF91 T V L V₁ Vp H) {a b : G} (ha : a ∈ conjClosure Vp H)
    (hb : b ∈ conjClosure Vp H) : vecOf h a ha = vecOf h b hb ↔ a⁻¹ * b ∈ V₁ := by
  rw [← Subtype.coe_inj, vecOf_coe, vecOf_coe]
  exact secMk_eq_secMk_iff

theorem vecOf_mul (h : HypF91 T V L V₁ Vp H) {a b : G} (ha : a ∈ conjClosure Vp H)
    (hb : b ∈ conjClosure Vp H) :
    (vecOf h (a * b) (Subgroup.mul_mem _ ha hb) : ↥(tildeOf V₁ (conjClosure Vp H))) =
      vecOf h a ha * vecOf h b hb := by
  apply Subtype.ext
  show secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a * b, _⟩ = _
  have : (⟨a * b, mem_normalizer_of_mem_conjClosure h (Subgroup.mul_mem _ ha hb)⟩ :
      ↥(Subgroup.normalizer (V₁ : Set G))) =
      ⟨a, mem_normalizer_of_mem_conjClosure h ha⟩ * ⟨b, mem_normalizer_of_mem_conjClosure h hb⟩ := rfl
  rw [this, map_mul]
  rfl

theorem starHom_vecOf (h : HypF91 T V L V₁ Vp H) (x : ↥H) {a : G} (ha : a ∈ conjClosure Vp H) :
    starHom h x (vecOf h a ha) = vecOf h (x * a * (x : G)⁻¹)
      (by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H x.2) a).mp ha
        exact this) := by
  apply Subtype.ext
  show ((conjAct (tildeOf V₁ (conjClosure Vp H)) (S1549C.tildeHom h x) (vecOf h a ha) :
    ↥(tildeOf V₁ (conjClosure Vp H))) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) = _
  rw [conjAct_apply_coe']
  have hx : (((S1549C.tildeHom h x : ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x) := rfl
  rw [hx, vecOf_coe, vecOf_coe, ← map_inv, ← map_mul, ← map_mul]
  congr 1

end Vec

section Star

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def starOfSub (h : HypF91 T V L V₁ Vp H) (K : Subgroup G) :
    Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H))) :=
  (K.subgroupOf H).map (starHom h)

omit [Finite G] in
theorem mem_starOfSub (h : HypF91 T V L V₁ Vp H) {K : Subgroup G}
    {y : MulAut ↥(tildeOf V₁ (conjClosure Vp H))} :
    y ∈ starOfSub h K ↔ ∃ x : ↥H, (x : G) ∈ K ∧ starHom h x = y := by
  simp [starOfSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem starOfSub_mono (h : HypF91 T V L V₁ Vp H) {K K' : Subgroup G} (hK : K ≤ K') :
    starOfSub h K ≤ starOfSub h K' := fun y hy => by
  obtain ⟨x, hx, rfl⟩ := (mem_starOfSub h).mp hy
  exact (mem_starOfSub h).mpr ⟨x, hK hx, rfl⟩

omit [Finite G] in
theorem starOfSub_sup (h : HypF91 T V L V₁ Vp H) {K K' : Subgroup G} (hK : K ≤ H) (hK' : K' ≤ H) :
    starOfSub h (K ⊔ K') = starOfSub h K ⊔ starOfSub h K' := by
  unfold starOfSub
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

omit [Finite G] in
theorem starOfSub_H (h : HypF91 T V L V₁ Vp H) : starOfSub h H = (starHom h).range := by
  unfold starOfSub
  rw [Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem mem_of_starHom_mem (h : HypF91 T V L V₁ Vp H) {K : Subgroup G} (hQK : pCoreOf 2 H ≤ K)
    {x : ↥H} (hx : starHom h x ∈ starOfSub h K) : (x : G) ∈ K := by
  obtain ⟨k, hk, hkx⟩ := (mem_starOfSub h).mp hx
  have h1 : starHom h (k⁻¹ * x) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
  have h2 : ((k⁻¹ * x : ↥H) : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h _).mp h1
  have h3 : (x : G) = k * ((k⁻¹ * x : ↥H) : G) := by simp
  rw [h3]
  exact K.mul_mem hk (hQK h2)

theorem starOfSub_inf_le (h : HypF91 T V L V₁ Vp H) {K K' : Subgroup G} (hQK : pCoreOf 2 H ≤ K) :
    starOfSub h K ⊓ starOfSub h K' ≤ starOfSub h (K ⊓ K') := by
  intro y ⟨hy1, hy2⟩
  obtain ⟨x, hx, rfl⟩ := (mem_starOfSub h).mp hy1
  obtain ⟨x', hx', hxx'⟩ := (mem_starOfSub h).mp hy2
  have h1 : starHom h (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxx', inv_mul_cancel]
  have h2 : ((x'⁻¹ * x : ↥H) : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h _).mp h1
  have h3 : (x' : G) = x * ((x'⁻¹ * x : ↥H) : G)⁻¹ := by simp
  have : (x' : G) ∈ K := by
    rw [h3]
    exact K.mul_mem hx (K.inv_mem (hQK h2))
  exact (mem_starOfSub h).mpr ⟨x', ⟨this, hx'⟩, hxx'⟩

theorem pCoreOf_starOfSub_H (h : HypF91 T V L V₁ Vp H) : pCoreOf 2 (starOfSub h H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [starOfSub_H]
  set R := pCoreOf 2 (starHom h).range with hR
  have hRle : R ≤ (starHom h).range := pCoreOf_le 2 _
  set R' : Subgroup ↥H := R.comap (starHom h) with hR'
  have hnorm : R'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : starHom h g ∈ Subgroup.normalizer (R : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) :=
      le_normalizer_pCoreOf 2 (starHom h).range ⟨g, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (starHom h n)).mp hn
    rw [hR', Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h1
  have hp : IsPGroup 2 ↥R' := by
    intro x
    have hx : starHom h (x : ↥H) ∈ R := x.2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (starHom h).range ⟨starHom h (x : ↥H), hx⟩
    have hk' : (starHom h) ((x : ↥H) ^ 2 ^ k) = 1 := by
      have := congrArg (fun y : ↥R => (y : MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) hk
      simpa [map_pow] using this
    have hq : (((x : ↥H) ^ 2 ^ k : ↥H) : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h _).mp hk'
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, hq⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h3 : (((x : ↥H) ^ 2 ^ k : ↥H) : G) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using h3
  have hle : R'.map H.subtype ≤ pCoreOf 2 H := by
    refine le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ (hp.map _)
    rw [map_subtype_subgroupOf']
    exact hnorm
  refine eq_bot_iff.mpr (fun r hr => ?_)
  obtain ⟨x, hx⟩ := hRle hr
  have hxR' : x ∈ R' := by
    rw [hR', Subgroup.mem_comap, hx]
    exact hr
  have h1 : ((x : ↥H) : G) ∈ pCoreOf 2 H := hle ⟨x, hxR', rfl⟩
  have h2 := (starHom_eq_one_iff h x).mpr h1
  rw [Subgroup.mem_bot, ← hx, h2]

omit [Finite G] in
theorem isPGroup_starOfSub (h : HypF91 T V L V₁ Vp H) {K : Subgroup G} (hKH : K ≤ H)
    (hK : IsPGroup 2 K) : IsPGroup 2 (starOfSub h K) :=
  (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm).map (starHom h)

theorem isSylowTwoOf_starOfSub_T (h : HypF91 T V L V₁ Vp H) :
    IsSylowTwoOf (starOfSub h T) (starHom h).range := by
  have hT := h.sylow_H
  have hTH : T ≤ H := hT.1
  refine ⟨?_, isPGroup_starOfSub h hTH hT.2.1, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp hy
    exact ⟨x, rfl⟩
  · set f := (starHom h).rangeRestrict with hf
    have hfs : Function.Surjective f := (starHom h).rangeRestrict_surjective
    set K := T.subgroupOf H with hK
    have hker : f.ker ≤ K := by
      intro x hx
      have h1 : starHom h x = 1 := by
        have := (MonoidHom.mem_ker).mp hx
        have h2 := congrArg Subtype.val this
        simpa [hf] using h2
      have hq := (starHom_eq_one_iff h x).mp h1
      exact Subgroup.mem_subgroupOf.mpr (IsSylowTwoOf.pCoreOf_le hT hq)
    have hmap : (starOfSub h T).subgroupOf (starHom h).range = K.map f := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_subgroupOf, mem_starOfSub, Subgroup.mem_map, hK, hf]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, congrArg Subtype.val hxy⟩
    rw [hmap, Subgroup.index_map_eq K hfs hker]
    exact hT.2.2

theorem starOfSub_pCoreOf_le (h : HypF91 T V L V₁ Vp H) {K : Subgroup G} (hKH : K ≤ H) :
    starOfSub h (pCoreOf 2 K) ≤ pCoreOf 2 (starOfSub h K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfwd : ∀ k : ↥H, (k : G) ∈ K → ∀ r ∈ starOfSub h (pCoreOf 2 K),
      starHom h k * r * (starHom h k)⁻¹ ∈ starOfSub h (pCoreOf 2 K) := by
    intro k hk r hr
    obtain ⟨x, hx, rfl⟩ := (mem_starOfSub h).mp hr
    refine (mem_starOfSub h).mpr ⟨k * x * k⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hkn := le_normalizer_pCoreOf 2 K hk
    have := (Subgroup.mem_normalizer_iff.mp hkn (x : G)).mp hx
    simpa using this
  refine le_pCoreOf_of_le_normalizer 2 (starOfSub_mono h (pCoreOf_le 2 K)) ?_
    (isPGroup_starOfSub h ((pCoreOf_le 2 K).trans hKH) (pCoreOf_isPGroup 2 K))
  intro y hy
  obtain ⟨k, hk, rfl⟩ := (mem_starOfSub h).mp hy
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => hfwd k hk r hr, fun hr => ?_⟩
  have hk' : ((k⁻¹ : ↥H) : G) ∈ K := by simpa using K.inv_mem hk
  have := hfwd k⁻¹ hk' _ hr
  simpa [map_inv, mul_assoc] using this

end Star

section Zvec

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_zvec (c : Ctx153 G T Mc M V₁ V₂ t) :
    ∃ a ∈ ZS153 T M V₁, a ∉ quasithinOmegaOneCenter T := by
  by_contra hcon
  push Not at hcon
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := c.hyp.lemma_15_3_2_two.2
  have hZS4 : Nat.card (ZS153 T M V₁) = 4 := Decomp153.card_ZS c.hyp c.decomp
  have hle : ZS153 T M V₁ ≤ quasithinOmegaOneCenter T := hcon
  have := Subgroup.card_le_of_le hle
  omega

theorem vecOf_ZS_cases (c : Ctx153 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (h : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {a : G} (haS : a ∈ ZS153 T M V₁) (haZ : a ∉ quasithinOmegaOneCenter T)
    {b : G} (hbS : b ∈ ZS153 T M V₁) :
    vecOf h b (le_conjClosure _ _ hbS) = 1 ∨
      vecOf h b (le_conjClosure _ _ hbS) = vecOf h a (le_conjClosure _ _ haS) := by
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := c.hyp.lemma_15_3_2_two.2
  have hZS4 : Nat.card (ZS153 T M V₁) = 4 := Decomp153.card_ZS c.hyp c.decomp
  have hZle : quasithinOmegaOneCenter T ≤ ZS153 T M V₁ := S1565.Z_le_ZS153 c
  have hidx : ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, hZ2, hZS4] at h1
    omega
  by_cases hbZ : b ∈ quasithinOmegaOneCenter T
  · left
    exact (vecOf_eq_one_iff h _).mpr hbZ
  · right
    have ha' : (⟨a⁻¹, (ZS153 T M V₁).inv_mem haS⟩ : ZS153 T M V₁) ∉
        (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) := fun hh =>
      haZ (by simpa using (quasithinOmegaOneCenter T).inv_mem (Subgroup.mem_subgroupOf.mp hh))
    have hb' : (⟨b, hbS⟩ : ZS153 T M V₁) ∉ (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) :=
      hbZ
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨a⁻¹, (ZS153 T M V₁).inv_mem haS⟩) (b := ⟨b, hbS⟩)).mpr (iff_of_false ha' hb')
    exact (vecOf_eq_vecOf_iff h _ _).mpr (by
      simpa using (quasithinOmegaOneCenter T).inv_mem (Subgroup.mem_subgroupOf.mp key))

theorem vecOf_inv {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H) {a : G}
    (ha : a ∈ conjClosure Vp H) :
    (vecOf h a⁻¹ (Subgroup.inv_mem _ ha) : ↥(tildeOf V₁ (conjClosure Vp H))) =
      (vecOf h a ha)⁻¹ := by
  apply Subtype.ext
  show secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a⁻¹, _⟩ = _
  have : (⟨a⁻¹, mem_normalizer_of_mem_conjClosure h (Subgroup.inv_mem _ ha)⟩ :
      ↥(Subgroup.normalizer (V₁ : Set G))) =
      (⟨a, mem_normalizer_of_mem_conjClosure h ha⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem starHom_T_zvec (c : Ctx153 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (h : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {a : G} (haS : a ∈ ZS153 T M V₁) {x : ↥H} (hx : (x : G) ∈ T) :
    starHom h x (vecOf h a (le_conjClosure _ _ haS)) = vecOf h a (le_conjClosure _ _ haS) := by
  rw [starHom_vecOf, vecOf_eq_vecOf_iff]
  have := S1565.commutator_T_ZS153 c ((ZS153 T M V₁).inv_mem haS) hx
  have e : ((x : G) * a * (x : G)⁻¹)⁻¹ * a = (a⁻¹ * (x : G) * a⁻¹⁻¹ * (x : G)⁻¹)⁻¹ := by group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem this

theorem closure_orbit_zvec (c : Ctx153 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (h : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {a : G} (haS : a ∈ ZS153 T M V₁) (haZ : a ∉ quasithinOmegaOneCenter T) :
    Subgroup.closure {v | ∃ g ∈ (starHom h).range,
      g (vecOf h a (le_conjClosure _ _ haS)) = v} = ⊤ := by
  set K := Subgroup.closure {v | ∃ g ∈ (starHom h).range,
      g (vecOf h a (le_conjClosure _ _ haS)) = v} with hK
  have key : ∀ u (hu : u ∈ conjClosure (ZS153 T M V₁) H), vecOf h u hu ∈ K := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h', hh', b, hb, rfl⟩ := hx
      have hb' := vecOf_ZS_cases c h haS haZ hb
      have e := starHom_vecOf h ⟨h', hh'⟩ (le_conjClosure _ _ hb)
      rcases hb' with h1 | h1
      · rw [h1, map_one] at e
        have : vecOf h (h' * b * h'⁻¹) _ = 1 := e.symm
        rw [this]
        exact K.one_mem
      · rw [h1] at e
        rw [← e]
        exact Subgroup.subset_closure ⟨_, ⟨⟨h', hh'⟩, rfl⟩, rfl⟩
    | one =>
      have : vecOf h 1 (Subgroup.one_mem _) = 1 := (vecOf_eq_one_iff h _).mpr (Subgroup.one_mem _)
      rw [this]
      exact K.one_mem
    | mul x y hx hy ihx ihy =>
      rw [vecOf_mul h hx hy]
      exact K.mul_mem ihx ihy
    | inv x hx ihx =>
      rw [vecOf_inv h hx]
      exact K.inv_mem ihx
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hv
  exact key (x : G) hx

theorem mem_M_of_fix_zvec (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂) {H : Subgroup G}
    (h : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {a : G} (haS : a ∈ ZS153 T M V₁) (haZ : a ∉ quasithinOmegaOneCenter T) {x : ↥H}
    (hx : starHom h x (vecOf h a (le_conjClosure _ _ haS)) = vecOf h a (le_conjClosure _ _ haS)) :
    (x : G) ∈ M := by
  have hZle : quasithinOmegaOneCenter T ≤ ZS153 T M V₁ := S1565.Z_le_ZS153 c
  have hfix : ∀ y : ↥H, starHom h y (vecOf h a (le_conjClosure _ _ haS)) =
      vecOf h a (le_conjClosure _ _ haS) → ∀ b ∈ ZS153 T M V₁,
      (y : G) * b * (y : G)⁻¹ ∈ ZS153 T M V₁ := by
    intro y hy b hb
    have hb' := vecOf_ZS_cases c h haS haZ hb
    have hfixb : starHom h y (vecOf h b (le_conjClosure _ _ hb)) =
        vecOf h b (le_conjClosure _ _ hb) := by
      rcases hb' with h1 | h1
      · rw [h1, map_one]
      · rw [h1]
        exact hy
    rw [starHom_vecOf] at hfixb
    have hmem := (vecOf_eq_vecOf_iff h _ _).mp hfixb
    have hw : b⁻¹ * ((y : G) * b * (y : G)⁻¹) ∈ quasithinOmegaOneCenter T := by
      have := (quasithinOmegaOneCenter T).inv_mem hmem
      simpa using this
    have e : (y : G) * b * (y : G)⁻¹ = b * (b⁻¹ * ((y : G) * b * (y : G)⁻¹)) := by group
    rw [e]
    exact (ZS153 T M V₁).mul_mem hb (hZle hw)
  have hx' : starHom h x⁻¹ (vecOf h a (le_conjClosure _ _ haS)) =
      vecOf h a (le_conjClosure _ _ haS) := by
    have h1 : starHom h x⁻¹ (starHom h x (vecOf h a (le_conjClosure _ _ haS))) =
        vecOf h a (le_conjClosure _ _ haS) := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [hx] at h1
  have hnorm : (x : G) ∈ Subgroup.normalizer (ZS153 T M V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => hfix x hx b hb, fun hb => ?_⟩
    have := hfix x⁻¹ hx' _ hb
    have e : ((x⁻¹ : ↥H) : G) * ((x : G) * b * (x : G)⁻¹) * ((x⁻¹ : ↥H) : G)⁻¹ = b := by
      simp [mul_assoc]
    rwa [e] at this
  exact r46.normalizer_ZS hnorm

end Zvec

section LFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem starOf_eq_starOfSub (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    {K : Subgroup G} (hKH : K ≤ H) :
    StarOf T M V₁ H K = starOfSub hb.hF98.toHypF91 K :=
  autOn_tilde_eq_map_starHom hb.hF98.toHypF91 hKH

theorem sqtkGroup_starOfSub (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    {K : Subgroup G} (hKH : K ≤ H) : SQTKGroup ↥(starOfSub hb.hF98.toHypF91 K) := by
  have h := hb.hF98.toHypF91
  have hSH : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot cx.c.hyp.qtfe.qtke cx.c.hyp.qtfe.simple cx.c.hyp.qtfe.nonabelian
      hb.adm.hH.1.2
  have hSK : SQTKGroup ↥K := InternalSec.sqtkGroup_mono hSH hKH
  let f : ↥K →* ↥(starOfSub h K) := ((starHom h).comp (Subgroup.inclusion hKH)).codRestrict _
    (fun x => (mem_starOfSub h).mpr ⟨Subgroup.inclusion hKH x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxK, rfl⟩ := (mem_starOfSub h).mp hy
    exact ⟨⟨x, hxK⟩, rfl⟩
  have hker : IsPGroup 2 ↥f.ker := by
    intro y
    have hy : starHom h (Subgroup.inclusion hKH (y : ↥K)) = 1 := by
      have := (MonoidHom.mem_ker).mp y.2
      have h2 := congrArg Subtype.val this
      simpa [f] using h2
    have hq : (((y : ↥K) : G)) ∈ pCoreOf 2 H := (starHom_eq_one_iff h _).mp hy
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨((y : ↥K) : G), hq⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h3 : ((y : ↥K) : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    simpa using h3
  exact InternalSec.sqtkGroup_of_surjective f hf hker hSK

theorem card_of_equiv_statedSL3 {Y : Type} [Group Y]
    (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) : Nat.card Y = 168 := by
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
  norm_num

theorem isQuasisimple_of_equiv_statedSL3 {Y : Type} [Group Y]
    (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) : CFSG.IsQuasisimple Y := by
  have hsS : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (K := ZMod 2) (by simp)
      (n := 3) (by norm_num)
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := hsS
  have hsY : IsSimpleGroup Y := e.isSimpleGroup
  let e' : Y ≃* L3.Γ :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  have hnc : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨x, -, y, -, hxy⟩ := L3.cent_nonabelian L3.x12 L3.x12_invol
    refine ⟨e'.symm x, e'.symm y, fun hcon => hxy ?_⟩
    have := congrArg e' hcon
    simpa using this
  exact isQuasisimple_of_perfect_of_isSimpleGroup (by
    have hc : (commutator Y).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h0 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact ⟨h1⟩) hsY

theorem not_starOfSub_L_le_M (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hb : InspBase cx H) {W : Subgroup G}
    {B : Subgroup (MulAut (UTil T M V₁ H))} (od : OffData hb W B) {L : Subgroup G}
    (lctx : LCtx hb od L) :
    ¬ starOfSub hb.hF98.toHypF91 L ≤ starOfSub hb.hF98.toHypF91 (M ⊓ H) := by
  intro hle
  have h := hb.hF98.toHypF91
  have hLH : L ≤ H := (le_of_mem_cComp lctx.comp).trans (preStar_le _ _)
  have hQ : pCoreOf 2 H ≤ M ⊓ H :=
    le_inf ((IsSylowTwoOf.pCoreOf_le h.sylow_H).trans cx.c.hyp.T_le) (pCoreOf_le 2 H)
  have hLMH : L ≤ M ⊓ H := fun l hl =>
    mem_of_starHom_mem h hQ (x := ⟨l, hLH hl⟩)
      (hle ((mem_starOfSub h).mpr ⟨⟨l, hLH hl⟩, hl, rfl⟩))
  have hnorm : L ≤ Subgroup.normalizer (Y0 T Mc M : Set G) := by
    rw [hb.claimB]
    exact fun x hx => S153D.normalizer_le_normalizer_thetaOf (M ⊓ H)
      (Subgroup.le_normalizer (hLMH hx))
  have hcomm : ⁅L, Y0 T Mc M⁆ ≤ Y0 T Mc M := by
    refine Subgroup.commutator_le.mpr fun l hl y hy => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm hl) y).mp hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
  have hLY0 : L ≤ Y0 T Mc M := lctx.comm ▸ hcomm
  have hsolv : Group.IsSolvable ↥L :=
    S153D.isSolvable_of_le_Y153 h113 cx.c.hyp (hLY0.trans ((Y0_le T Mc M).trans inf_le_left))
  exact not_isSolvable_of_mem_cComp lctx.comp hsolv

theorem starOfSub_le_ffJ (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    {W : Subgroup G} {B : Subgroup (MulAut (UTil T M V₁ H))} (od : OffData hb W B) {L : Subgroup G}
    (lctx : LCtx hb od L) :
    starOfSub hb.hF98.toHypF91 L ≤ @ffJ (UTil T M V₁ H) (modInst hb.hF98.toHypF91)
      (starOfSub hb.hF98.toHypF91 H) := by
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  intro y hy
  obtain ⟨x, hxL, rfl⟩ := (mem_starOfSub h).mp hy
  have hxJ : (x : G) ∈ Jgrp hb B := le_of_mem_cComp lctx.comp hxL
  have h1 : starHom h x ∈ conjClosure B (StarOf T M V₁ H H) := (starHom_mem_iff h).mp hxJ
  rw [starOf_eq_starOfSub cx hb le_rfl] at h1
  have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
    have := od.off
    rwa [starOf_eq_starOfSub cx hb le_rfl] at this
  refine conjClosure_le ?_ h1
  intro g hg b hb'
  have hbJ : b ∈ ffJ (V := UTil T M V₁ H) (starOfSub h H) := B6.le_ffJ hoff hb'
  exact (Subgroup.mem_normalizer_iff.mp
    (B6.le_normalizer_ffJ (V := UTil T M V₁ H) (starOfSub h H) hg) b).mp hbJ

end LFacts

end S1549D

end CFSG.Quasithin
