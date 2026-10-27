module

public import CFSG.Milestones.ASVolI.C48.Lin
public import CFSG.Quasithin.Background.C48AsmLineStep
public import CFSG.Milestones.ASVolI.C4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Groups

variable {G : Type} [Group G]

theorem burnsideC48_le_normalizer {P X : Subgroup G}
    (h : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) : P ≤ Subgroup.normalizer (X : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h p hp y, fun hy => ?_⟩
  have h1 := h p⁻¹ (P.inv_mem hp) _ hy
  rwa [show p⁻¹ * (p * y * p⁻¹) * p⁻¹⁻¹ = y by group] at h1

theorem burnsideC48_omegaOneCenterOf_le (X : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => (Subgroup.mem_inf.mp hx.1).1

theorem burnsideC48_natural_irred {K W X : Subgroup G} {N : Subgroup ↥K} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Open.StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (h : IsNaturalSectionWith K W ⊥ N (CFSG.Open.StatedSL 3 F) α β) (hXW : X ≤ W)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = W := by
  obtain ⟨-, hα, -, -, hβker, hβeq⟩ := h
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  rcases X.bot_or_exists_ne_one with hX | ⟨x, hxX, hx1⟩
  · exact Or.inl hX
  right
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | ∃ w : ↥W, (w : G) ∈ X ∧ Multiplicative.toAdd (β w) = y}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, X.mul_mem ha hb, by rw [map_mul]; rfl⟩
      zero_mem' := ⟨1, X.one_mem, by rw [map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, X.inv_mem ha, by rw [map_inv]; rfl⟩ }
  have hSinv : ∀ g : ↥(CFSG.Open.StatedSL 3 F), ∀ y ∈ S,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec y ∈ S := by
    rintro g _ ⟨w, hwX, rfl⟩
    obtain ⟨k, rfl⟩ := hα g
    have hk : (k : G) * w * (k : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hKX k.2) w).mp hwX
    exact ⟨⟨_, hXW hk⟩, hk, hβeq k w ⟨_, hXW hk⟩ rfl⟩
  have hβx : Multiplicative.toAdd (β ⟨x, hXW hxX⟩) ≠ 0 := by
    intro h0
    apply hx1
    have h1 : β ⟨x, hXW hxX⟩ = β 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
    exact congrArg Subtype.val (hβi h1)
  have htop := burnsideC48_eq_top_of_invariant hSinv ⟨⟨x, hXW hxX⟩, hxX, rfl⟩ hβx
  refine le_antisymm hXW fun w hw => ?_
  have hmem : Multiplicative.toAdd (β ⟨w, hw⟩) ∈ S := htop ▸ AddSubgroup.mem_top _
  obtain ⟨u, huX, hu⟩ := hmem
  have hu' : u = ⟨w, hw⟩ := hβi (Multiplicative.toAdd.injective hu)
  rw [hu'] at huX
  exact huX

theorem burnsideC48_card_line {W V : Subgroup G} {F : Type} [Field F] [Fintype F]
    {β : ↥W →* Multiplicative (Fin 3 → F)} (hβi : Function.Injective β)
    (hβs : Function.Surjective β) (hl : IsFLineVia W V β) :
    Nat.card ↥V = Fintype.card F ^ 2 := by
  classical
  obtain ⟨hVW, ℓ, hℓ, hmem⟩ := hl
  let e : ↥V → ↥ℓ := fun v =>
    ⟨Multiplicative.toAdd (β ⟨v, hVW v.2⟩), (hmem ⟨v, hVW v.2⟩).mp v.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h1 : β ⟨a, hVW a.2⟩ = β ⟨b, hVW b.2⟩ :=
        Multiplicative.toAdd.injective (congrArg Subtype.val hab)
      have h2 := congrArg (fun w : ↥W => (w : G)) (hβi h1)
      exact Subtype.ext h2
    · obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (y : Fin 3 → F))
      have huV : (u : G) ∈ V := (hmem u).mpr (by rw [hu]; exact y.2)
      refine ⟨⟨u, huV⟩, Subtype.ext ?_⟩
      show Multiplicative.toAdd (β ⟨(u : G), hVW huV⟩) = y
      rw [show (⟨(u : G), hVW huV⟩ : ↥W) = u from rfl, hu]
      rfl
  haveI : Fintype ↥ℓ := Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := ↥ℓ), hℓ]

theorem burnsideC48_le_of_stab {K W V U : Subgroup G} {N : Subgroup ↥K} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Open.StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (h : IsNaturalSectionWith K W ⊥ N (CFSG.Open.StatedSL 3 F) α β) (hl : IsFLineVia W V β)
    (hUW : U ≤ W)
    (hU : K ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hnot : ¬ U ≤ V) : V ≤ U := by
  obtain ⟨hKW, hα, -, -, hβker, hβeq⟩ := h
  obtain ⟨hVW, ℓ, -, hmem⟩ := hl
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  obtain ⟨u, huU, huV⟩ := Set.not_subset.mp hnot
  have hxℓ : Multiplicative.toAdd (β ⟨u, hUW huU⟩) ∉ ℓ := fun hx' =>
    huV ((hmem ⟨u, hUW huU⟩).mpr hx')
  obtain ⟨f, hfx, hℓf⟩ := Submodule.exists_le_ker_of_notMem hxℓ
  have hstab : ∀ w ∈ ℓ, ∃ k : ↥K, (k : G) ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ (y z : ↥W), (z : G) = k * y * k⁻¹ →
        Multiplicative.toAdd (β z) =
          Multiplicative.toAdd (β y) + f (Multiplicative.toAdd (β y)) • w := by
    intro w hw
    have hfw : f w = 0 := hℓf hw
    obtain ⟨k, hk⟩ := hα (burnsideC48_tvSL f w hfw)
    have hk' : ∀ (y z : ↥W), (z : G) = k * y * k⁻¹ →
        Multiplicative.toAdd (β z) =
          Multiplicative.toAdd (β y) + f (Multiplicative.toAdd (β y)) • w := by
      intro y z hyz
      rw [hβeq k y z hyz, hk, burnsideC48_tvSL_mulVec]
    refine ⟨k, ?_, hk'⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyW := hVW hy
      have hzW : (k : G) * y * (k : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hKW k.2) y).mp hyW
      have hyℓ : Multiplicative.toAdd (β ⟨y, hyW⟩) ∈ ℓ := (hmem ⟨y, hyW⟩).mp hy
      have h1 := hk' ⟨y, hyW⟩ ⟨_, hzW⟩ rfl
      have h2 : f (Multiplicative.toAdd (β ⟨y, hyW⟩)) = 0 := hℓf hyℓ
      rw [h2, zero_smul, add_zero] at h1
      exact (hmem ⟨_, hzW⟩).mpr (h1 ▸ hyℓ)
    · intro hz
      have hzW := hVW hz
      have hyW : y ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW k.2) y).mpr hzW
      have hzℓ : Multiplicative.toAdd (β ⟨_, hzW⟩) ∈ ℓ := (hmem ⟨_, hzW⟩).mp hz
      have h1 := hk' ⟨y, hyW⟩ ⟨_, hzW⟩ rfl
      have h2 : f (Multiplicative.toAdd (β ⟨y, hyW⟩)) = 0 := by
        have h3 : f (Multiplicative.toAdd (β ⟨_, hzW⟩)) = 0 := hℓf hzℓ
        rw [h1, map_add, map_smul, hfw, smul_zero, add_zero] at h3
        exact h3
      rw [h2, zero_smul, add_zero] at h1
      exact (hmem ⟨y, hyW⟩).mpr (h1 ▸ hzℓ)
  intro v hv
  have hvW := hVW hv
  have hyℓ : Multiplicative.toAdd (β ⟨v, hvW⟩) ∈ ℓ := (hmem ⟨v, hvW⟩).mp hv
  obtain ⟨k, hkN, hk⟩ := hstab ((f (Multiplicative.toAdd (β ⟨u, hUW huU⟩)))⁻¹ •
    Multiplicative.toAdd (β ⟨v, hvW⟩)) (ℓ.smul_mem _ hyℓ)
  have hkU : (k : G) * u * (k : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hU ⟨k.2, hkN⟩) u).mp huU
  have h1 := hk ⟨u, hUW huU⟩ ⟨_, hUW hkU⟩ rfl
  have h2 : β (⟨u, hUW huU⟩⁻¹ * ⟨_, hUW hkU⟩) = β ⟨v, hvW⟩ := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, smul_smul, mul_inv_cancel₀ hfx, one_smul]
    abel
  have h4 : u⁻¹ * ((k : G) * u * (k : G)⁻¹) = v := congrArg Subtype.val (hβi h2)
  rw [← h4]
  exact U.mul_mem (U.inv_mem huU) hkU

theorem burnsideC48_theta {K W Q : Subgroup G} {N₀ : Subgroup ↥K} {F F' : Type} [Field F]
    [Field F'] {α : ↥K →* ↥(CFSG.Open.StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (h : IsNaturalSectionWith K W ⊥ N₀ (CFSG.Open.StatedSL 3 F) α β)
    {α' : ↥K →* ↥(CFSG.Open.StatedSL 3 F')} (hα' : Function.Surjective α')
    (hQ : IsSumOfNaturalModulesVia K Q ⊥ α' false 2) (hWQ : W ≤ Q) :
    ∃ θ : ↥W →* Multiplicative (Fin 3 → F'), Function.Bijective θ ∧
      ∀ (k : ↥K) (u v : ↥W), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (θ v) =
          ((α' k : GL (Fin 3) F') : Matrix (Fin 3) (Fin 3) F').mulVec
            (Multiplicative.toAdd (θ u)) := by
  have h' := h
  obtain ⟨hKW, -, -, hβs, hβker, -⟩ := h'
  obtain ⟨-, -, βQ, -, hβQker, hβQeq⟩ := hQ
  have hβQi : Function.Injective βQ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβQker, Subgroup.bot_subgroupOf]
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  let θ : Fin 2 → (↥W →* Multiplicative (Fin 3 → F')) := fun j =>
    { toFun := fun w => Multiplicative.ofAdd (Multiplicative.toAdd (βQ ⟨w, hWQ w.2⟩) j)
      map_one' := by
        show Multiplicative.ofAdd (Multiplicative.toAdd (βQ 1) j) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (Multiplicative.toAdd
          (βQ (⟨a, hWQ a.2⟩ * ⟨b, hWQ b.2⟩)) j) = _
        rw [map_mul]
        rfl }
  have hθ : ∀ j (w : ↥W), Multiplicative.toAdd (θ j w) =
      Multiplicative.toAdd (βQ ⟨w, hWQ w.2⟩) j := fun _ _ => rfl
  have hθeq : ∀ j (k : ↥K) (u v : ↥W), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (θ j v) =
        ((α' k : GL (Fin 3) F') : Matrix (Fin 3) (Fin 3) F').mulVec
          (Multiplicative.toAdd (θ j u)) := by
    intro j k u v huv
    rw [hθ, hθ]
    exact hβQeq k ⟨u, hWQ u.2⟩ ⟨v, hWQ v.2⟩ huv j
  obtain ⟨w₀, hw₀⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hw₀1 : w₀ ≠ 1 := by
    intro h1
    rw [h1, map_one] at hw₀
    have := congrFun (congrArg Multiplicative.toAdd hw₀) 0
    simp at this
  have hX : ∀ j, (θ j).ker.map W.subtype = ⊥ ∨ (θ j).ker.map W.subtype = W := by
    intro j
    refine burnsideC48_natural_irred h (Subgroup.map_subtype_le _) ?_
    refine burnsideC48_le_normalizer fun k hk y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hy
    have hz : k * (w : G) * k⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW hk) w).mp w.2
    refine ⟨⟨_, hz⟩, ?_, rfl⟩
    change θ j w = 1 at hw
    show θ j ⟨_, hz⟩ = 1
    apply Multiplicative.toAdd.injective
    rw [hθeq j ⟨k, hk⟩ w ⟨_, hz⟩ rfl, hw]
    simp
  have hinj : ∃ j, Function.Injective (θ j) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ j, (θ j).ker.map W.subtype = W := by
      intro j
      rcases hX j with hb | ht
      · exfalso
        apply hcon j
        rw [← MonoidHom.ker_eq_bot_iff]
        exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp hb
      · exact ht
    have hw : ∀ j, θ j w₀ = 1 := by
      intro j
      have hmem : (w₀ : G) ∈ (θ j).ker.map W.subtype := (hall j).symm ▸ w₀.2
      obtain ⟨w, hw, hww⟩ := hmem
      rw [Subtype.ext hww] at hw
      exact hw
    apply hw₀1
    have hQ1 : βQ ⟨w₀, hWQ w₀.2⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      have := congrArg Multiplicative.toAdd (hw j)
      rw [hθ] at this
      rw [this]
      rfl
    have := hβQi (hQ1.trans (map_one βQ).symm)
    exact Subtype.ext (congrArg (fun q : ↥Q => (q : G)) this)
  obtain ⟨j, hj⟩ := hinj
  refine ⟨θ j, ⟨hj, ?_⟩, hθeq j⟩
  let T : AddSubgroup (Fin 3 → F') :=
    { carrier := {y | ∃ w : ↥W, Multiplicative.toAdd (θ j w) = y}
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, by rw [map_mul]; rfl⟩
      zero_mem' := ⟨1, by rw [map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a⁻¹, by rw [map_inv]; rfl⟩ }
  have hTinv : ∀ g : ↥(CFSG.Open.StatedSL 3 F'), ∀ y ∈ T,
      ((g : GL (Fin 3) F') : Matrix (Fin 3) (Fin 3) F').mulVec y ∈ T := by
    rintro g _ ⟨w, rfl⟩
    obtain ⟨k, rfl⟩ := hα' g
    have hz : (k : G) * w * (k : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hKW k.2) w).mp w.2
    exact ⟨⟨_, hz⟩, hθeq j k w ⟨_, hz⟩ rfl⟩
  have hne : Multiplicative.toAdd (θ j w₀) ≠ 0 := by
    intro h0
    apply hw₀1
    apply hj
    rw [map_one]
    exact Multiplicative.toAdd.injective h0
  have htop := burnsideC48_eq_top_of_invariant hTinv ⟨w₀, rfl⟩ hne
  intro y
  have hy : Multiplicative.toAdd y ∈ T := htop ▸ AddSubgroup.mem_top _
  obtain ⟨w, hw⟩ := hy
  exact ⟨w, Multiplicative.toAdd.injective hw⟩

theorem burnsideC48_prod_equiv {V V₁ V₂ : Subgroup G} (hV : V = V₁ ⊔ V₂)
    (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hdisj : V₁ ⊓ V₂ = ⊥) :
    ∃ e : ↥V₁ × ↥V₂ ≃* ↥V, ∀ p : ↥V₁ × ↥V₂, (e p : G) = (p.1 : G) * p.2 := by
  have hV₁ : V₁ ≤ V := hV ▸ le_sup_left
  have hV₂ : V₂ ≤ V := hV ▸ le_sup_right
  let μ : ↥V₁ × ↥V₂ →* ↥V :=
    { toFun := fun p => ⟨(p.1 : G) * p.2, V.mul_mem (hV₁ p.1.2) (hV₂ p.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun p q => by
        apply Subtype.ext
        show (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * p.2 * (q.1 * q.2)
        have hc : (q.1 : G) * p.2 = p.2 * q.1 := hab _ (hV₁ q.1.2) _ (hV₂ p.2.2)
        rw [mul_assoc, ← mul_assoc (q.1 : G), hc]
        group }
  have hμ : Function.Bijective μ := by
    refine ⟨(injective_iff_map_eq_one μ).mpr fun p hp => ?_, fun v => ?_⟩
    · have h1 : (p.1 : G) * p.2 = 1 := congrArg Subtype.val hp
      have h2 : (p.1 : G) ∈ V₁ ⊓ V₂ := by
        refine ⟨p.1.2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact V₂.inv_mem p.2.2
      rw [hdisj, Subgroup.mem_bot] at h2
      have h3 : (p.2 : G) = 1 := by rw [h2, one_mul] at h1; exact h1
      exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
    · have hv : (v : G) ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := hV ▸ v.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂
        (C48.le_normalizer_of_le_centralizer fun x hx => Subgroup.mem_centralizer_iff.mpr
          fun y hy => hab _ (hV₂ hy) _ (hV₁ hx))] at hv
      obtain ⟨a, ha, b, hb, hab'⟩ := hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab'⟩
  exact ⟨MulEquiv.ofBijective μ hμ, fun _ => rfl⟩

theorem burnsideC48_decomp_unique {V₁ V₂ : Subgroup G} (hdisj : V₁ ⊓ V₂ = ⊥)
    {a a' b b' : G} (ha : a ∈ V₁) (ha' : a' ∈ V₁) (hb : b ∈ V₂) (hb' : b' ∈ V₂)
    (hc : b * b'⁻¹ = b'⁻¹ * b) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ V₁ ⊓ V₂ :=
    ⟨V₁.mul_mem (V₁.inv_mem ha') ha, h1 ▸ V₂.mul_mem hb' (V₂.inv_mem hb)⟩
  rw [hdisj, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

end Groups

section Finite

variable {G : Type} [Group G] [Finite G]

theorem burnsideC48_natural_bot {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hL0 : L = CFSG.Quasithin.conjClosure L M) (hLK : L ≤ K) {n : ℕ} {F : Type} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) (hpsl : IsPSL 2 2 n (ModO2 L)) {V₁ : Subgroup G}
    (hV₁ : V₁ ≤ V) (hline : IsStabilizedLineOfNatural F R M K V₁) (hnt : ⁅V₁, L⁆ ≠ ⊥) :
    CFSG.Quasithin.IsNaturalSection (L ⊔ R) V₁ ⊥ (R.subgroupOf (L ⊔ R))
        (CFSG.Open.StatedSL 2 F) ∧
      V₁ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨W, -, α, β, ⟨-, -, -, hβs, hβker, hβeq⟩, hfl, hMK⟩ := hline
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLV : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro x hx
    have hx' : x ∈ M ⊓ K := ⟨hLM hx, hLK hx⟩
    rw [hMK] at hx'
    exact hx'.2
  have hRV : R ≤ Subgroup.centralizer (V₁ : Set G) :=
    (C48.le_centralizer_V h).trans (Subgroup.centralizer_le hV₁)
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set G) := by
    have h0 := C48.pCoreOf_conjClosure_le h
    rw [← hL0] at h0
    exact h0.trans hRV
  have hNS := C48.isNaturalSection_of_line α β hβs hβker hβeq hfl hLK hLV
    (perfect_of_mem_cComp h.comp) (by rw [Nat.card_eq_fintype_card, hF]) hpsl hO
    (fun hle => hnt (le_bot_iff.mp hle))
  have hZ := C48.inf_centralizer_eq_bot_of_isNaturalSection hNS
  have hN := C48.subgroupOf_conjClosure_eq h
  rw [← hL0] at hN
  rw [← hN] at hNS
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
  exact ⟨C48.isNaturalSection_sup hNS hLR hRV, hZ⟩

theorem burnsideC48_c48Case1_of_twoLines {H R M L V K V₁ V₂ : Subgroup G}
    (h : HypC28 H R M L V) (hL0 : L = CFSG.Quasithin.conjClosure L M) (hLK : L ≤ K)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hn : 1 < n) (hF : Fintype.card F = 2 ^ n)
    (hpsl : IsPSL 2 2 n (ModO2 L)) (h134 : IsC134Case 2 (K ⊔ R) R K)
    (hl1 : IsStabilizedLineOfNatural F R M K V₁) (hl2 : IsStabilizedLineOfNatural F R M K V₂)
    (hV12 : V = V₁ ⊔ V₂) : ChC.C48Case1 R L V := by
  have hVL : ⁅V, L⁆ = V := by
    have h0 := h.V_comm
    rwa [← hL0] at h0
  have hVne : ⁅V, L⁆ ≠ ⊥ := by
    rw [hVL]
    exact h.V_ne
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.V_elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLn : ∀ {W : Subgroup G}, IsStabilizedLineOfNatural F R M K W →
      L ≤ Subgroup.normalizer (W : Set G) := by
    intro W hW x hx
    obtain ⟨-, -, -, -, -, -, hMK⟩ := hW
    have hx' : x ∈ M ⊓ K := ⟨hLM hx, hLK hx⟩
    rw [hMK] at hx'
    exact hx'.2
  have hV₁ : V₁ ≤ V := hV12 ▸ le_sup_left
  have hV₂ : V₂ ≤ V := hV12 ▸ le_sup_right
  have hRV : R ≤ Subgroup.centralizer (V : Set G) := C48.le_centralizer_V h
  have hfirst : ∀ {W : Subgroup G}, IsStabilizedLineOfNatural F R M K W → V = W →
      ChC.C48Case1 R L V := by
    intro W hW hVW
    refine ⟨n, hpsl, Or.inl ⟨F, inferInstance, inferInstance, hF, ?_⟩⟩
    have hW' := hW
    rw [← hVW] at hW'
    exact C48.isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl le_rfl hW' hVne
  by_cases h1 : ⁅V₁, L⁆ = ⊥
  · exact hfirst hl2 (C48.eq_right_of_commutator_eq_bot hV12 hab (hLn hl2) h1 hVL)
  by_cases h2 : ⁅V₂, L⁆ = ⊥
  · exact hfirst hl1
      (C48.eq_right_of_commutator_eq_bot (sup_comm V₁ V₂ ▸ hV12) hab (hLn hl1) h2 hVL)
  obtain ⟨W₁, hW₁, α₁, β₁, hns₁, hfl₁, hMK₁⟩ := id hl1
  obtain ⟨W₂, hW₂, α₂, β₂, hns₂, hfl₂, hMK₂⟩ := id hl2
  obtain ⟨⟨n', F', _, _, α', -, ⟨hα's, -⟩, hsum⟩, -⟩ := h134
  have hWQ : ∀ {W : Subgroup G}, W ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆ →
      W ≤ c134Q (K ⊔ R) K := fun hW =>
    hW.trans (Subgroup.commutator_mono (burnsideC48_omegaOneCenterOf_le _) le_rfl)
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hns₁.2.2.2.2.1, Subgroup.bot_subgroupOf]
  have hβ₂i : Function.Injective β₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, hns₂.2.2.2.2.1, Subgroup.bot_subgroupOf]
  have hc₁ := burnsideC48_card_line hβ₁i hns₁.2.2.2.1 hfl₁
  have hc₂ := burnsideC48_card_line hβ₂i hns₂.2.2.2.1 hfl₂
  have hV₁W₁ : V₁ ≤ W₁ := hfl₁.1
  have hV₂W₂ : V₂ ≤ W₂ := hfl₂.1
  have hKW₁ := hns₁.1
  have hKW₂ := hns₂.1
  have hP : K ⊓ Subgroup.normalizer (V₁ : Set G) = K ⊓ Subgroup.normalizer (V₂ : Set G) := by
    rw [← hMK₁, ← hMK₂]
  have hW₁ne : W₁ ≠ ⊥ := by
    intro hb
    obtain ⟨w, hw⟩ := hns₁.2.2.2.1 (Multiplicative.ofAdd (Pi.single 0 1))
    have hw1 : w = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall W₁).mp hb (w : G) w.2)
    rw [hw1, map_one] at hw
    have := congrFun (congrArg Multiplicative.toAdd hw) 0
    simp at this
  rcases burnsideC48_natural_irred hns₁ (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW₁ hk, hKW₂ hk⟩) with hb | ht
  swap
  · have hW₁₂ : W₁ ≤ W₂ := ht ▸ inf_le_right
    have hWeq : W₁ = W₂ := by
      rcases burnsideC48_natural_irred hns₂ hW₁₂ hKW₁ with hb' | ht'
      · exact absurd hb' hW₁ne
      · exact ht'
    have hV₂W₁ : V₂ ≤ W₁ := hWeq ▸ hV₂W₂
    have hN₂ : K ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (V₂ : Set G) :=
      hP ▸ inf_le_right
    have hle : V₂ ≤ V₁ := by
      by_contra hnot
      have hge := burnsideC48_le_of_stab hns₁ hfl₁ hV₂W₁ hN₂ hnot
      exact hnot (Subgroup.eq_of_le_of_card_ge hge (le_of_eq (hc₂.trans hc₁.symm))).ge
    have heq : V₂ = V₁ := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hc₁.trans hc₂.symm))
    exact hfirst hl1 (by rw [hV12, heq, sup_idem])
  have hdisj : V₁ ⊓ V₂ = ⊥ := eq_bot_iff.mpr ((inf_le_inf hV₁W₁ hV₂W₂).trans hb.le)
  obtain ⟨θ₁, hθ₁b, hθ₁eq⟩ := burnsideC48_theta hns₁ hα's hsum (hWQ hW₁)
  obtain ⟨θ₂, hθ₂b, hθ₂eq⟩ := burnsideC48_theta hns₂ hα's hsum (hWQ hW₂)
  let e₁ : ↥W₁ ≃* Multiplicative (Fin 3 → F') := MulEquiv.ofBijective θ₁ hθ₁b
  let τ' : ↥W₂ →* ↥W₁ := e₁.symm.toMonoidHom.comp θ₂
  have hτ'i : Function.Injective τ' := e₁.symm.injective.comp hθ₂b.1
  have hθτ : ∀ x, θ₁ (τ' x) = θ₂ x := fun x => e₁.apply_symm_apply (θ₂ x)
  have hτ'eq : ∀ (k : ↥K) (u v : ↥W₂), (v : G) = k * u * k⁻¹ →
      ((τ' v : ↥W₁) : G) = k * (τ' u : G) * k⁻¹ := by
    intro k u v huv
    have hz : (k : G) * (τ' u : G) * (k : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKW₁ k.2) _).mp (τ' u).2
    have : τ' v = ⟨_, hz⟩ := by
      apply hθ₁b.1
      apply Multiplicative.toAdd.injective
      rw [hθτ, hθ₂eq k u v huv, hθ₁eq k (τ' u) ⟨_, hz⟩ rfl, hθτ]
    rw [this]
    rfl
  let U : Subgroup G := ((V₂.subgroupOf W₂).map τ').map W₁.subtype
  have hUW : U ≤ W₁ := Subgroup.map_subtype_le _
  have hUN : K ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) := by
    refine burnsideC48_le_normalizer fun p hp y hy => ?_
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
    have hpK : p ∈ K := hp.1
    have hpN₂ : p ∈ Subgroup.normalizer (V₂ : Set G) := (hP ▸ hp).2
    have hxV : (x : G) ∈ V₂ := hx
    have hz : p * (x : G) * p⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hKW₂ hpK) x).mp x.2
    have hzV : p * (x : G) * p⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hpN₂ x).mp hxV
    exact ⟨τ' ⟨_, hz⟩, ⟨⟨_, hz⟩, hzV, rfl⟩, hτ'eq ⟨p, hpK⟩ x ⟨_, hz⟩ rfl⟩
  have hcU : Nat.card U = Nat.card V₂ := by
    rw [Subgroup.card_map_of_injective W₁.subtype_injective,
      Subgroup.card_map_of_injective hτ'i]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂W₂).toEquiv
  have hUV : U = V₁ := by
    have hle : U ≤ V₁ := by
      by_contra hnot
      have hge := burnsideC48_le_of_stab hns₁ hfl₁ hUW hUN hnot
      exact hnot (Subgroup.eq_of_le_of_card_ge hge
        (le_of_eq (hcU.trans (hc₂.trans hc₁.symm)))).ge
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq ((hc₁.trans hc₂.symm).trans hcU.symm))
  have hτV : ∀ x : ↥W₂, (x : G) ∈ V₂ → ((τ' x : ↥W₁) : G) ∈ V₁ := by
    intro x hx
    rw [← hUV]
    exact ⟨τ' x, ⟨x, hx, rfl⟩, rfl⟩
  have hτVs : ∀ y ∈ V₁, ∃ x : ↥W₂, (x : G) ∈ V₂ ∧ ((τ' x : ↥W₁) : G) = y := by
    intro y hy
    rw [← hUV] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  let τ : ↥V₂ →* ↥V₁ :=
    { toFun := fun x => ⟨τ' ⟨x, hV₂W₂ x.2⟩, hτV _ x.2⟩
      map_one' := by
        apply Subtype.ext
        show ((τ' 1 : ↥W₁) : G) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((τ' (⟨a, hV₂W₂ a.2⟩ * ⟨b, hV₂W₂ b.2⟩) : ↥W₁) : G) = _
        rw [map_mul]
        rfl }
  have hτi : Function.Injective τ := by
    intro a b hab
    have h3 : τ' ⟨a, hV₂W₂ a.2⟩ = τ' ⟨b, hV₂W₂ b.2⟩ :=
      Subtype.ext (congrArg (fun y : ↥V₁ => (y : G)) hab)
    exact Subtype.ext (congrArg (fun y : ↥W₂ => (y : G)) (hτ'i h3))
  obtain ⟨hNS₁, hC₁⟩ := burnsideC48_natural_bot h hL0 hLK hF hpsl hV₁ hl1 h1
  obtain ⟨-, hC₂⟩ := burnsideC48_natural_bot h hL0 hLK hF hpsl hV₂ hl2 h2
  obtain ⟨-, α, hα, hαker, γ, hγs, hγker, hγeq⟩ := hNS₁
  have hγi : Function.Injective γ := by
    rw [← MonoidHom.ker_eq_bot_iff, hγker, Subgroup.bot_subgroupOf]
  obtain ⟨e, he⟩ := burnsideC48_prod_equiv hV12 hab hdisj
  have hsplit : ∀ v : ↥V, (((e.symm v).1 : ↥V₁) : G) * ((e.symm v).2 : G) = v := by
    intro v
    rw [← he (e.symm v), e.apply_symm_apply]
  have hRV₁ : R ≤ Subgroup.centralizer (V₁ : Set G) := hRV.trans (Subgroup.centralizer_le hV₁)
  have hRV₂ : R ≤ Subgroup.centralizer (V₂ : Set G) := hRV.trans (Subgroup.centralizer_le hV₂)
  have hLR₁ : L ⊔ R ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (hLn hl1) (C48.le_normalizer_of_le_centralizer hRV₁)
  have hLR₂ : L ⊔ R ≤ Subgroup.normalizer (V₂ : Set G) :=
    sup_le (hLn hl2) (C48.le_normalizer_of_le_centralizer hRV₂)
  have hconj : ∀ a ∈ L ⊔ R, ∀ u v : ↥V, (v : G) = a * u * a⁻¹ →
      (((e.symm v).1 : ↥V₁) : G) = a * ((e.symm u).1 : G) * a⁻¹ ∧
        (((e.symm v).2 : ↥V₂) : G) = a * ((e.symm u).2 : G) * a⁻¹ := by
    intro a ha u v huv
    have h1' : a * ((e.symm u).1 : G) * a⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hLR₁ ha) _).mp (e.symm u).1.2
    have h2' : a * ((e.symm u).2 : G) * a⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hLR₂ ha) _).mp (e.symm u).2.2
    have hprod : (((e.symm v).1 : ↥V₁) : G) * ((e.symm v).2 : G) =
        (a * ((e.symm u).1 : G) * a⁻¹) * (a * ((e.symm u).2 : G) * a⁻¹) := by
      rw [hsplit v, huv, ← hsplit u]
      group
    have hc : ((e.symm v).2 : G) * (a * ((e.symm u).2 : G) * a⁻¹)⁻¹ =
        (a * ((e.symm u).2 : G) * a⁻¹)⁻¹ * ((e.symm v).2 : G) :=
      hab _ (hV₂ (e.symm v).2.2) _ (hV₂ (V₂.inv_mem h2'))
    exact burnsideC48_decomp_unique hdisj (e.symm v).1.2 h1' (e.symm v).2.2 h2' hc hprod
  let pair : Multiplicative (Fin 2 → F) × Multiplicative (Fin 2 → F) →*
      Multiplicative (Fin 2 → Fin 2 → F) :=
    { toFun := fun p => Multiplicative.ofAdd ![Multiplicative.toAdd p.1, Multiplicative.toAdd p.2]
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl
      map_mul' := fun p q => by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl }
  let β : ↥V →* Multiplicative (Fin 2 → Fin 2 → F) :=
    pair.comp ((γ.prodMap (γ.comp τ)).comp e.symm.toMonoidHom)
  have hβ0 : ∀ v, Multiplicative.toAdd (β v) 0 = Multiplicative.toAdd (γ (e.symm v).1) :=
    fun _ => rfl
  have hβ1 : ∀ v, Multiplicative.toAdd (β v) 1 = Multiplicative.toAdd (γ (τ (e.symm v).2)) :=
    fun _ => rfl
  have hβs : Function.Surjective β := by
    intro t
    obtain ⟨a, ha⟩ := hγs (Multiplicative.ofAdd (Multiplicative.toAdd t 0))
    obtain ⟨b, hb⟩ := hγs (Multiplicative.ofAdd (Multiplicative.toAdd t 1))
    obtain ⟨x, hxV, hx⟩ := hτVs b b.2
    have hτx : τ ⟨x, hxV⟩ = b := Subtype.ext hx
    refine ⟨e (a, ⟨x, hxV⟩), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · show Multiplicative.toAdd (β (e (a, ⟨x, hxV⟩))) 0 = _
      rw [hβ0, e.symm_apply_apply, ha]
      rfl
    · show Multiplicative.toAdd (β (e (a, ⟨x, hxV⟩))) 1 = _
      rw [hβ1, e.symm_apply_apply]
      show Multiplicative.toAdd (γ (τ ⟨x, hxV⟩)) = _
      rw [hτx, hb]
      rfl
  have hβi : Function.Injective β := by
    refine (injective_iff_map_eq_one β).mpr fun v hv => ?_
    have h0 : γ (e.symm v).1 = 1 := by
      apply Multiplicative.toAdd.injective
      have := congrFun (congrArg Multiplicative.toAdd hv) 0
      rw [hβ0] at this
      rw [this]
      rfl
    have h1'' : γ (τ (e.symm v).2) = 1 := by
      apply Multiplicative.toAdd.injective
      have := congrFun (congrArg Multiplicative.toAdd hv) 1
      rw [hβ1] at this
      rw [this]
      rfl
    have hp1 : (e.symm v).1 = 1 := hγi (h0.trans (map_one γ).symm)
    have hp2 : (e.symm v).2 = 1 :=
      hτi ((hγi (h1''.trans (map_one γ).symm)).trans (map_one τ).symm)
    have h3 : e.symm v = 1 := Prod.ext hp1 hp2
    have h4 := congrArg e h3
    rw [e.apply_symm_apply, map_one] at h4
    exact h4
  have hVC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    have hcen : ∀ l ∈ L, l * v * l⁻¹ = v := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff.mp hvC l hl, mul_inv_cancel_right]
    have hc1 : (((e.symm ⟨v, hvV⟩).1 : ↥V₁) : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h3 := (hconj l (Subgroup.mem_sup_left hl) ⟨v, hvV⟩ ⟨v, hvV⟩ (hcen l hl).symm).1
      calc l * (((e.symm ⟨v, hvV⟩).1 : ↥V₁) : G)
          = (l * (((e.symm ⟨v, hvV⟩).1 : ↥V₁) : G) * l⁻¹) * l := by group
        _ = (((e.symm ⟨v, hvV⟩).1 : ↥V₁) : G) * l := by rw [← h3]
    have hc2 : (((e.symm ⟨v, hvV⟩).2 : ↥V₂) : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h3 := (hconj l (Subgroup.mem_sup_left hl) ⟨v, hvV⟩ ⟨v, hvV⟩ (hcen l hl).symm).2
      calc l * (((e.symm ⟨v, hvV⟩).2 : ↥V₂) : G)
          = (l * (((e.symm ⟨v, hvV⟩).2 : ↥V₂) : G) * l⁻¹) * l := by group
        _ = (((e.symm ⟨v, hvV⟩).2 : ↥V₂) : G) * l := by rw [← h3]
    have h1' : (((e.symm ⟨v, hvV⟩).1 : ↥V₁) : G) ∈ V₁ ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(e.symm ⟨v, hvV⟩).1.2, hc1⟩
    have h2' : (((e.symm ⟨v, hvV⟩).2 : ↥V₂) : G) ∈ V₂ ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(e.symm ⟨v, hvV⟩).2.2, hc2⟩
    rw [hC₁, Subgroup.mem_bot] at h1'
    rw [hC₂, Subgroup.mem_bot] at h2'
    have h3 := hsplit ⟨v, hvV⟩
    rw [h1', h2', one_mul] at h3
    rw [Subgroup.mem_bot]
    exact h3.symm
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
  have hβeq : ∀ (a : ↥(L ⊔ R)) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false ((α a : GL (Fin 2) F))).mulVec (Multiplicative.toAdd (β u) i) := by
    intro a u v huv i
    obtain ⟨hc1, hc2⟩ := hconj a a.2 u v huv
    obtain ⟨l, hl, r, hr, hlr⟩ := C48.exists_mul_of_mem_sup hLR a.2
    show _ = ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec _
    fin_cases i
    · show Multiplicative.toAdd (β v) 0 = ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β u) 0)
      rw [hβ0, hβ0]
      exact hγeq a (e.symm u).1 (e.symm v).1 hc1
    · show Multiplicative.toAdd (β v) 1 = ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β u) 1)
      rw [hβ1, hβ1]
      refine hγeq a (τ (e.symm u).2) (τ (e.symm v).2) ?_
      have hx : (((e.symm v).2 : ↥V₂) : G) = l * ((e.symm u).2 : G) * l⁻¹ := by
        rw [hc2, ← hlr]
        exact C48.conj_mul_eq_of_mem_centralizer hRV hr (hV₂ (e.symm u).2.2)
      have h3 := hτ'eq ⟨l, hLK hl⟩ ⟨_, hV₂W₂ (e.symm u).2.2⟩ ⟨_, hV₂W₂ (e.symm v).2.2⟩ hx
      show ((τ' ⟨_, hV₂W₂ (e.symm v).2.2⟩ : ↥W₁) : G) =
        (a : G) * ((τ' ⟨_, hV₂W₂ (e.symm u).2.2⟩ : ↥W₁) : G) * (a : G)⁻¹
      rw [h3, ← hlr]
      exact (C48.conj_mul_eq_of_mem_centralizer hRV hr (hV₁ (hτV _ (e.symm u).2.2))).symm
  have hsupN : ∀ {A B : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) →
        x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro A B x hA hB
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  refine ⟨n, hpsl, Or.inr (Or.inr ⟨hn, F, inferInstance, inferInstance, hF, α, hα, hαker,
    ?_, inf_le_left, β, hβs, ?_, hβeq⟩)⟩
  · intro x hx
    rw [hV12]
    exact hsupN (hLR₁ hx) (hLR₂ hx)
  · rw [hVC, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
    exact hβi

end Finite

end CFSG.ASVolI
