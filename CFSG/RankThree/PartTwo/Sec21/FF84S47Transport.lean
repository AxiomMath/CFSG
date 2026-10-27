module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

section Tr

variable {G H : Type} [Group G] [Group H] {L : Subgroup G} {A : Subgroup H}

@[expose] def trX (e : ↥L ≃* ↥A) (X : Subgroup G) : Subgroup H :=
  (X.subgroupOf L).map (A.subtype.comp e.toMonoidHom)

theorem mem_trX (e : ↥L ≃* ↥A) {X : Subgroup G} {y : H} :
    y ∈ trX e X ↔ ∃ x : ↥L, (x : G) ∈ X ∧ ((e x : ↥A) : H) = y := by
  unfold trX
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]

theorem trX_le (e : ↥L ≃* ↥A) (X : Subgroup G) : trX e X ≤ A := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := (mem_trX e).1 hy
  exact (e x).2

theorem trX_mono (e : ↥L ≃* ↥A) {X Z : Subgroup G} (h : X ≤ Z) : trX e X ≤ trX e Z := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_trX e).1 hy
  exact (mem_trX e).2 ⟨x, h hx, rfl⟩

theorem trX_symm_trX (e : ↥L ≃* ↥A) {X : Subgroup G} (hX : X ≤ L) :
    trX e.symm (trX e X) = X := by
  ext g
  rw [mem_trX]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := (mem_trX e).1 ha
    have : e.symm a = x := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext hxa.symm
    rw [this]
    exact hx
  · intro hg
    refine ⟨e ⟨g, hX hg⟩, (mem_trX e).2 ⟨⟨g, hX hg⟩, hg, rfl⟩, ?_⟩
    simp

theorem trX_trX_symm (e : ↥L ≃* ↥A) {Y : Subgroup H} (hY : Y ≤ A) :
    trX e (trX e.symm Y) = Y := by
  have := trX_symm_trX e.symm hY
  simpa using this

theorem trX_le_iff (e : ↥L ≃* ↥A) {X Z : Subgroup G} (hX : X ≤ L) (hZ : Z ≤ L) :
    trX e X ≤ trX e Z ↔ X ≤ Z := by
  refine ⟨fun h => ?_, trX_mono e⟩
  have := trX_mono e.symm h
  rwa [trX_symm_trX e hX, trX_symm_trX e hZ] at this

theorem trX_injOn (e : ↥L ≃* ↥A) {X Z : Subgroup G} (hX : X ≤ L) (hZ : Z ≤ L)
    (h : trX e X = trX e Z) : X = Z :=
  le_antisymm ((trX_le_iff e hX hZ).1 h.le) ((trX_le_iff e hZ hX).1 h.ge)

theorem trX_inf (e : ↥L ≃* ↥A) (X Z : Subgroup G) : trX e (X ⊓ Z) = trX e X ⊓ trX e Z := by
  ext y
  rw [Subgroup.mem_inf, mem_trX, mem_trX, mem_trX]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have : x = z := e.injective (Subtype.ext (hxy.trans hzy.symm))
    subst this
    exact ⟨x, ⟨hx, hz⟩, hxy⟩

theorem trX_bot (e : ↥L ≃* ↥A) : trX e (⊥ : Subgroup G) = ⊥ := by
  ext y
  rw [mem_trX, Subgroup.mem_bot]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at hx
    have : x = 1 := Subtype.ext hx
    subst this
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem trX_eq_bot_iff (e : ↥L ≃* ↥A) {X : Subgroup G} (hX : X ≤ L) :
    trX e X = ⊥ ↔ X = ⊥ := by
  constructor
  · intro h
    exact trX_injOn e hX bot_le (h.trans (trX_bot e).symm)
  · rintro rfl
    exact trX_bot e

theorem isPGroup_trX (e : ↥L ≃* ↥A) {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) :
    IsPGroup p (trX e X) := by
  unfold trX
  exact (hX.comap_of_injective L.subtype Subtype.coe_injective |>.map _)

theorem isPGroup_trX_iff (e : ↥L ≃* ↥A) {p : ℕ} {X : Subgroup G} (hX : X ≤ L) :
    IsPGroup p (trX e X) ↔ IsPGroup p X := by
  refine ⟨fun h => ?_, isPGroup_trX e⟩
  have := isPGroup_trX e.symm h
  rwa [trX_symm_trX e hX] at this

theorem le_nor_of_conj {X Z : Subgroup G} (h : ∀ g ∈ Z, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    Z ≤ Nor X := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_of_le_nor {X Z : Subgroup G} (h : Z ≤ Nor X) {g x : G} (hg : g ∈ Z) (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.1 (h hg) x).1 hx

theorem trX_nor_fwd (e : ↥L ≃* ↥A) {X Z : Subgroup G} (h : Z ≤ Nor X) :
    trX e Z ≤ Nor (trX e X) := by
  apply le_nor_of_conj
  intro g hg y hy
  obtain ⟨z, hz, rfl⟩ := (mem_trX e).1 hg
  obtain ⟨x, hx, rfl⟩ := (mem_trX e).1 hy
  refine (mem_trX e).2 ⟨z * x * z⁻¹, ?_, ?_⟩
  · have := conj_mem_of_le_nor h hz hx
    simpa using this
  · simp

theorem trX_nor_iff (e : ↥L ≃* ↥A) {X Z : Subgroup G} (hX : X ≤ L) (hZ : Z ≤ L) :
    trX e Z ≤ Nor (trX e X) ↔ Z ≤ Nor X := by
  refine ⟨fun h => ?_, trX_nor_fwd e⟩
  have := trX_nor_fwd e.symm h
  rwa [trX_symm_trX e hX, trX_symm_trX e hZ] at this

theorem natCard_trX (e : ↥L ≃* ↥A) {X : Subgroup G} (hX : X ≤ L) :
    Nat.card (trX e X) = Nat.card X := by
  unfold trX
  have hinj : Function.Injective (A.subtype.comp e.toMonoidHom) :=
    Subtype.coe_injective.comp e.injective
  rw [Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem isEA_iff {K : Type*} [Group K] (p : ℕ) (hp : 0 < p) (X : Subgroup K) :
    IsElementaryAbelian p X ↔ (∀ a ∈ X, ∀ c ∈ X, a * c = c * a) ∧ ∀ a ∈ X, a ^ p = 1 := by
  constructor
  · intro h
    exact ⟨fun a ha c hc => by
      have : (⟨a, ha⟩ : X) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨a, ha⟩ :=
        IsMulCommutative.is_comm.comm _ _
      exact congrArg Subtype.val this,
      fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha⟩
  · rintro ⟨h1, h2⟩
    have hc : IsMulCommutative X := ⟨⟨fun a c => Subtype.ext (h1 a a.2 c c.2)⟩⟩
    exact
      { toIsMulCommutative := hc
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by simpa using h2 a a.2) }

theorem isElemAb_trX_fwd (e : ↥L ≃* ↥A) {p k : ℕ} (hp : 0 < p) {X : Subgroup G} (hX : X ≤ L)
    (h : IsElemAb p k X) : IsElemAb p k (trX e X) := by
  obtain ⟨h1, h2⟩ := h
  rw [isEA_iff p hp] at h1
  refine ⟨(isEA_iff p hp _).2 ⟨?_, ?_⟩, by rw [natCard_trX e hX, h2]⟩
  · intro a ha c hc
    obtain ⟨x, hx, rfl⟩ := (mem_trX e).1 ha
    obtain ⟨z, hz, rfl⟩ := (mem_trX e).1 hc
    have : x * z = z * x := Subtype.ext (h1.1 _ hx _ hz)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, this]
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := (mem_trX e).1 ha
    have : x ^ p = 1 := Subtype.ext (h1.2 _ hx)
    rw [← Subgroup.coe_pow, ← map_pow, this]
    simp

theorem isElemAb_trX_iff (e : ↥L ≃* ↥A) {p k : ℕ} (hp : 0 < p) {X : Subgroup G} (hX : X ≤ L) :
    IsElemAb p k (trX e X) ↔ IsElemAb p k X := by
  refine ⟨fun h => ?_, isElemAb_trX_fwd e hp hX⟩
  have := isElemAb_trX_fwd e.symm hp (trX_le e X) h
  rwa [trX_symm_trX e hX] at this

theorem trX_inf_cen (e : ↥L ≃* ↥A) (X : Subgroup G) {g : G} (hg : g ∈ L) :
    trX e (X ⊓ Cen g) = trX e X ⊓ Cen (((e ⟨g, hg⟩ : ↥A) : H)) := by
  ext y
  rw [Subgroup.mem_inf, mem_trX, mem_trX, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨⟨x, hx1, rfl⟩, ?_⟩
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 hx2
    have : x * ⟨g, hg⟩ = ⟨g, hg⟩ * x := Subtype.ext h2
    have h3 := congrArg (fun w : ↥L => ((e w : ↥A) : H)) this
    simpa [map_mul] using h3
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 : e (⟨g, hg⟩ * x) = e (x * ⟨g, hg⟩) := by
      apply Subtype.ext
      simpa [map_mul] using hc.symm
    have := e.injective h1
    exact (congrArg Subtype.val this).symm

theorem trX_zpowers (e : ↥L ≃* ↥A) {g : G} (hg : g ∈ L) :
    trX e (Subgroup.zpowers g) = Subgroup.zpowers (((e ⟨g, hg⟩ : ↥A) : H)) := by
  ext y
  rw [mem_trX, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨k, ?_⟩
    have : (⟨g, hg⟩ : ↥L) ^ k = x := Subtype.ext (by simpa using hk)
    rw [← this]
    simp [map_zpow]
  · rintro ⟨k, rfl⟩
    refine ⟨⟨g, hg⟩ ^ k, ?_, ?_⟩
    · simp
    · simp [map_zpow]

theorem mem_nor_trX_iff (e : ↥L ≃* ↥A) {ℓ : G} (hℓ : ℓ ∈ L) {U : Subgroup G} (hU : U ≤ L) :
    ℓ ∈ Nor U ↔ ((e ⟨ℓ, hℓ⟩ : ↥A) : H) ∈ Nor (trX e U) := by
  have hz : Subgroup.zpowers ℓ ≤ L := Subgroup.zpowers_le.2 hℓ
  rw [← Subgroup.zpowers_le, ← Subgroup.zpowers_le, ← trX_nor_iff e hU hz, trX_zpowers e hℓ]

theorem trX_map (e : ↥L ≃* ↥A) (Y : Subgroup ↥L) :
    trX e (Y.map L.subtype) = Y.map (A.subtype.comp e.toMonoidHom) := by
  unfold trX
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective]

theorem trX_closure_pair (e : ↥L ≃* ↥A) {x y : G} (hx : x ∈ L) (hy : y ∈ L) :
    trX e (Subgroup.closure {x, y}) =
      Subgroup.closure {((e ⟨x, hx⟩ : ↥A) : H), ((e ⟨y, hy⟩ : ↥A) : H)} := by
  have h1 : (Subgroup.closure {x, y} : Subgroup G) =
      (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥L)).map L.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨⟨z, hx⟩, Or.inl rfl, rfl⟩
      · exact ⟨⟨z, hy⟩, Or.inr rfl, rfl⟩
    · rintro ⟨w, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [h1, trX_map, MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro ⟨w, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem trX_piStar_fwd (e : ↥L ≃* ↥A) {q : ℕ} {P U : Subgroup G} (hP : P ≤ L) (hU : U ≤ L)
    (h : U ∈ PiStar L P q) : trX e U ∈ PiStar A (trX e P) q := by
  obtain ⟨-, hpg, hnor, hmax⟩ := h
  refine ⟨trX_le e U, isPGroup_trX e hpg, trX_nor_fwd e hnor, ?_⟩
  intro V' hUV' hV'A hV'p hV'nor
  have hVL : trX e.symm V' ≤ L := trX_le e.symm V'
  have hV : trX e (trX e.symm V') = V' := by
    have := trX_symm_trX e.symm hV'A
    simpa using this
  have hUV : U ≤ trX e.symm V' := by
    refine (trX_le_iff e hU hVL).1 ?_
    rw [hV]; exact hUV'
  have hVp : IsPGroup q (trX e.symm V') := by
    refine (isPGroup_trX_iff e hVL).1 ?_
    rw [hV]; exact hV'p
  have hVn : P ≤ Nor (trX e.symm V') := by
    refine (trX_nor_iff e hVL hP).1 ?_
    rw [hV]; exact hV'nor
  have := hmax _ hUV hVL hVp hVn
  rw [← hV, this]

theorem trX_piStar_iff (e : ↥L ≃* ↥A) {q : ℕ} {P U : Subgroup G} (hP : P ≤ L) (hU : U ≤ L) :
    U ∈ PiStar L P q ↔ trX e U ∈ PiStar A (trX e P) q := by
  refine ⟨trX_piStar_fwd e hP hU, fun h => ?_⟩
  have := trX_piStar_fwd e.symm (trX_le e P) (trX_le e U) h
  rwa [trX_symm_trX e hU, trX_symm_trX e hP] at this

end Tr

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
