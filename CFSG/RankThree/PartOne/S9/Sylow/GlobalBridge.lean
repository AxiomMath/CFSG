module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup
open scoped commutatorElement

variable {G K : Type*} [Group G] [Group K] {f : K →* G}

theorem map_le_normalizer_map_iff (hf : Function.Injective f) {X Y : Subgroup K} :
    X.map f ≤ Subgroup.normalizer (Y.map f : Set G) ↔ X ≤ Subgroup.normalizer (Y : Set K) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_map_of_mem f hx)) (f y)
    rw [Subgroup.mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hf] at h1
    exact h1
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      exact ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp (h hx) y).mp hy, by simp⟩
    · intro hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (h hx) (x⁻¹ * y * x)).mpr
          (by simpa [mul_assoc] using hy)
      · have : g = f x⁻¹ * f y * f x := by
          rw [hyg]; simp [mul_assoc]
        simp [this]

theorem map_le_centralizer_map_iff (hf : Function.Injective f) {X Y : Subgroup K} :
    X.map f ≤ Subgroup.centralizer (Y.map f : Set G) ↔ X ≤ Subgroup.centralizer (Y : Set K) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_map_of_mem f hx)) (f y)
      (Subgroup.mem_map_of_mem f hy)
    exact hf (by simpa using this)
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have := Subgroup.mem_centralizer_iff.mp (h hx) y hy
    simp [← map_mul, this]

theorem isPGroup_map_iff (hf : Function.Injective f) {p : ℕ} {X : Subgroup K} :
    IsPGroup p ↥(X.map f) ↔ IsPGroup p ↥X :=
  ⟨fun h => h.of_equiv (X.equivMapOfInjective f hf).symm,
    fun h => h.of_equiv (X.equivMapOfInjective f hf)⟩

theorem isElementaryAbelian_iff_forall {p : ℕ} {X : Subgroup G} :
    IsElementaryAbelian p ↥X ↔ (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) ∧ ∀ x ∈ X, x ^ p = 1 := by
  constructor
  · intro h
    refine ⟨fun x hx y hy => ?_, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := X)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro ⟨h1, h2⟩
    exact
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (h1 a.1 a.2 b.1 b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
          fun x => Subtype.ext (by simpa using h2 x.1 x.2) }

theorem isElementaryAbelian_map_iff (hf : Function.Injective f) {p : ℕ} {X : Subgroup K} :
    IsElementaryAbelian p ↥(X.map f) ↔ IsElementaryAbelian p ↥X := by
  rw [isElementaryAbelian_iff_forall, isElementaryAbelian_iff_forall]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx y hy => hf ?_, fun x hx => hf ?_⟩
    · rw [map_mul, map_mul]
      exact h1 _ (Subgroup.mem_map_of_mem f hx) _ (Subgroup.mem_map_of_mem f hy)
    · rw [map_pow, map_one]
      exact h2 _ (Subgroup.mem_map_of_mem f hx)
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, h1 x' hx' y' hy']
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, h2 x' hx', map_one]

theorem forall_pow_eq_one_map_iff (hf : Function.Injective f) {p : ℕ} {X : Subgroup K} :
    (∀ x ∈ X.map f, x ^ p = 1) ↔ ∀ x ∈ X, x ^ p = 1 := by
  constructor
  · intro h x hx
    exact hf (by rw [map_pow, map_one]; exact h _ (Subgroup.mem_map_of_mem f hx))
  · intro h x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h x' hx', map_one]

theorem isSylowOf_map (hf : Function.Injective f) {p : ℕ} {T X : Subgroup K}
    (h : IsSylowOf p T X) : IsSylowOf p (T.map f) (X.map f) :=
  ⟨Subgroup.map_mono h.1, (isPGroup_map_iff hf).2 h.2.1, by
    rw [Subgroup.relIndex_map_map_of_injective _ _ hf]; exact h.2.2⟩

theorem isSylowOf_map_iff (hf : Function.Injective f) {p : ℕ} {T X : Subgroup K} :
    IsSylowOf p (T.map f) (X.map f) ↔ IsSylowOf p T X :=
  ⟨fun h => ⟨(Subgroup.map_le_map_iff_of_injective hf).mp h.1, (isPGroup_map_iff hf).mp h.2.1, by
    have := h.2.2
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hf] at this⟩, isSylowOf_map hf⟩

theorem map_inf_centralizer_map (hf : Function.Injective f) (X Y : Subgroup K) :
    (X ⊓ Subgroup.centralizer (Y : Set K)).map f =
      X.map f ⊓ Subgroup.centralizer (Y.map f : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hx.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have := Subgroup.mem_centralizer_iff.mp hx.2 y hy
    rw [← map_mul, ← map_mul, this]
  · rintro g ⟨hg1, hg2⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg1
    refine Subgroup.mem_map.mpr ⟨x, ⟨hx, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    exact hf (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hg2 (f y) (Subgroup.mem_map_of_mem f hy))

theorem characteristic_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {N : Subgroup X} (h : N.Characteristic) : (N.map e.toMonoidHom).Characteristic := by
  refine ⟨fun φ => ?_⟩
  have hψ := h.fixed (e.trans (φ.trans e.symm))
  ext y
  rw [Subgroup.mem_comap, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have h2 : e.symm (φ y) ∈ N ↔
      e.symm y ∈ N.comap (e.trans (φ.trans e.symm)).toMonoidHom := by
    simp
  show e.symm (φ y) ∈ N ↔ e.symm y ∈ N
  rw [h2, hψ]

@[expose] def normalizerConj (Q : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    ↥Q ≃* ↥Q where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr (by simp [mul_assoc])
    exact this⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem normalizerConj_apply_coe (Q : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    ((normalizerConj Q g hg x : ↥Q) : G) = g * x * g⁻¹ := rfl

theorem mem_normalizer_of_characteristic {Q D : Subgroup G} (hDQ : D ≤ Q)
    (hc : (D.subgroupOf Q).Characteristic) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  have hfix := hc.fixed (normalizerConj Q g hg)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxQ : (⟨x, hDQ hx⟩ : Q) ∈ D.subgroupOf Q := hx
    rw [← hfix] at hxQ
    exact hxQ
  · intro hx
    have hxQ : g * x * g⁻¹ ∈ Q := hDQ hx
    have hxQ' : x ∈ Q := (Subgroup.mem_normalizer_iff.mp hg x).mpr hxQ
    have : (⟨x, hxQ'⟩ : Q) ∈ (D.subgroupOf Q).comap (normalizerConj Q g hg).toMonoidHom := hx
    rw [hfix] at this
    exact this

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (frattini P).map e.toMonoidHom = frattini Q := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · intro x hx
    have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
    have hx' : e.symm x ∈ frattini P := h hx
    exact ⟨e.symm x, hx', by simp⟩

theorem map_inSubgroup_frattini (hf : Function.Injective f) (Y : Subgroup K) :
    (inSubgroup frattini Y).map f = inSubgroup frattini (Y.map f) := by
  rw [inSubgroup, inSubgroup, ← map_frattini_mulEquiv (Y.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_omegaOne (hf : Function.Injective f) (q : ℕ) (X : Subgroup K) :
    (omegaOne q X).map f = omegaOne q (X.map f) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx, hxq⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, by rw [← map_pow, hxq, map_one]⟩
  · rintro ⟨hy, hyq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, hf (by rw [map_pow, hyq, map_one])⟩, rfl⟩

theorem map_inf_centralizer_self (hf : Function.Injective f) (Y : Subgroup K) :
    (Y ⊓ Subgroup.centralizer (Y : Set K)).map f =
      Y.map f ⊓ Subgroup.centralizer (Y.map f : Set G) :=
  map_inf_centralizer_map hf Y Y

theorem isQDShape_map_iff (hf : Function.Injective f) {q : ℕ} {Y : Subgroup K} :
    IsQDShape q (Y.map f) ↔ IsQDShape q Y := by
  have e1 : (Y.map f ⊓ Subgroup.centralizer (Y.map f : Set G) = ⁅Y.map f, Y.map f⁆) ↔
      (Y ⊓ Subgroup.centralizer (Y : Set K) = ⁅Y, Y⁆) := by
    rw [← map_inf_centralizer_self hf, ← Subgroup.map_commutator]
    exact (Subgroup.map_injective hf).eq_iff
  have e2 : (inSubgroup frattini (Y.map f) = ⁅Y.map f, Y.map f⁆) ↔
      (inSubgroup frattini Y = ⁅Y, Y⁆) := by
    rw [← map_inSubgroup_frattini hf, ← Subgroup.map_commutator]
    exact (Subgroup.map_injective hf).eq_iff
  have e3 : Nat.card ↥⁅Y.map f, Y.map f⁆ = Nat.card ↥⁅Y, Y⁆ := by
    rw [← Subgroup.map_commutator]; exact Subgroup.card_map_of_injective hf
  unfold IsQDShape
  rw [isElementaryAbelian_map_iff hf, Subgroup.card_map_of_injective hf,
    forall_pow_eq_one_map_iff hf, e3, e1, e2]

end CFSG.RankThree.PartOne.Sec9B
