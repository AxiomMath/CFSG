module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc15

section Helpers

variable {L : Type*} [Group L]

theorem le_normalizer_of_forall_conj {K V : Subgroup L}
    (h : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) : K ≤ Subgroup.normalizer (V : Set L) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h k hk v hv, fun hv => ?_⟩
  have h' := h k⁻¹ (K.inv_mem hk) _ hv
  have e : k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v := by group
  rwa [e] at h'

theorem map_normalizer_le {G H : Type*} [Group G] [Group H] (f : G →* H) (X : Subgroup G) :
    (Subgroup.normalizer (X : Set G)).map f ≤
      Subgroup.normalizer ((X.map f : Subgroup H) : Set H) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx, by simp⟩
  · rintro ⟨x, hx, hxe⟩
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_, ?_⟩
    · have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [e]
    · have e : f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by simp
      rw [e, hxe]
      group

theorem map_le_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {T X : Subgroup G}
    (h : T ≤ Subgroup.normalizer (X : Set G)) :
    T.map f ≤ Subgroup.normalizer ((X.map f : Subgroup H) : Set H) :=
  (Subgroup.map_mono h).trans (map_normalizer_le f X)

theorem card_prod_subgroup {M N : Type*} [Group M] [Group N] (A : Subgroup M) (B : Subgroup N) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B :=
  (Nat.card_congr (Subgroup.prodEquiv A B).toEquiv).trans (Nat.card_prod _ _)

theorem isPGroup_prod [Finite L] {V₀ V₁ : Subgroup L} (h₀ : IsPGroup 2 V₀) (h₁ : IsPGroup 2 V₁) :
    IsPGroup 2 (V₀.prod V₁) := by
  obtain ⟨m, hm⟩ := h₀.exists_card_eq
  obtain ⟨n, hn⟩ := h₁.exists_card_eq
  exact IsPGroup.of_card (n := m + n) (by rw [card_prod_subgroup, hm, hn, pow_add])

theorem prod_le_normalizer {A₀ A₁ V₀ V₁ : Subgroup L}
    (h₀ : A₀ ≤ Subgroup.normalizer (V₀ : Set L)) (h₁ : A₁ ≤ Subgroup.normalizer (V₁ : Set L)) :
    A₀.prod A₁ ≤ Subgroup.normalizer ((V₀.prod V₁ : Subgroup (L × L)) : Set (L × L)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  rw [Subgroup.mem_normalizer_iff.mp (h₀ hx.1) n.1, Subgroup.mem_normalizer_iff.mp (h₁ hx.2) n.2]

theorem exists_odd_map_ne_one [Finite L] {G : Type*} [Group G] (π : G →* L) {X : Subgroup G}
    (hO : oTwoUpper X = X) (hY : X.map π ≠ ⊥) : ∃ x ∈ X, Odd (orderOf x) ∧ π x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hY
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  have hle : oTwoUpper X ≤ π.ker := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    exact hcon y hy.1 hy.2
  exact hle (by rw [hO]; exact hx)

theorem inl_mem_of_comm {T X : Subgroup (L × L)}
    (hTX : T ≤ Subgroup.normalizer (X : Set (L × L))) {V : Subgroup L}
    (hVT : ∀ v ∈ V, ((v, 1) : L × L) ∈ T) {y : L × L} (hy : y ∈ X)
    (hcomm : ∀ w ∈ V, ∃ v ∈ V, w = v * y.1 * v⁻¹ * y.1⁻¹) : ∀ w ∈ V, ((w, 1) : L × L) ∈ X := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hcomm w hw
  have h1 : ((v, 1) : L × L) * y * ((v, 1) : L × L)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hTX (hVT v hv)) y).mp hy
  have h2 := X.mul_mem h1 (X.inv_mem hy)
  convert h2 using 1
  ext <;> simp

theorem inr_mem_of_comm {T X : Subgroup (L × L)}
    (hTX : T ≤ Subgroup.normalizer (X : Set (L × L))) {V : Subgroup L}
    (hVT : ∀ v ∈ V, ((1, v) : L × L) ∈ T) {y : L × L} (hy : y ∈ X)
    (hcomm : ∀ w ∈ V, ∃ v ∈ V, w = v * y.2 * v⁻¹ * y.2⁻¹) : ∀ w ∈ V, ((1, w) : L × L) ∈ X := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hcomm w hw
  have h1 : ((1, v) : L × L) * y * ((1, v) : L × L)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hTX (hVT v hv)) y).mp hy
  have h2 := X.mul_mem h1 (X.inv_mem hy)
  convert h2 using 1
  ext <;> simp

end Helpers

section Local

variable {L : Type*} [Group L]

structure LocalData (R Y V : Subgroup L) : Prop where
  le_R : V ≤ R
  R_le : R ≤ Subgroup.normalizer (V : Set L)
  Y_le : Y ≤ Subgroup.normalizer (V : Set L)
  card_V : Nat.card V = 4
  card_Y : Nat.card Y = 12
  comm : ∀ y ∈ Y, y ≠ 1 → Odd (orderOf y) → ∀ w ∈ V, ∃ v ∈ V, w = v * y * v⁻¹ * y⁻¹
  weak : ∀ k : L, (∀ v ∈ V, k * v * k⁻¹ ∈ R) → ∃ y ∈ Y, ∃ r ∈ R, k = y * r

theorem LocalData.map {L' : Type*} [Group L'] (e : L ≃* L') {R Y V : Subgroup L}
    (h : LocalData R Y V) :
    LocalData (R.map e.toMonoidHom) (Y.map e.toMonoidHom) (V.map e.toMonoidHom) where
  le_R := Subgroup.map_mono h.le_R
  R_le := map_le_normalizer_map _ h.R_le
  Y_le := map_le_normalizer_map _ h.Y_le
  card_V := (Subgroup.card_map_of_injective e.injective).trans h.card_V
  card_Y := (Subgroup.card_map_of_injective e.injective).trans h.card_Y
  comm := by
    rintro _ ⟨y, hy, rfl⟩ hy1 hodd _ ⟨w, hw, rfl⟩
    have hy1' : y ≠ 1 := fun h1 => hy1 (by simp [h1])
    have hodd' : Odd (orderOf y) := by
      have : orderOf (e.toMonoidHom y) = orderOf y := MulEquiv.orderOf_eq e y
      rwa [this] at hodd
    obtain ⟨v, hv, rfl⟩ := h.comm y hy hy1' hodd' w hw
    exact ⟨e v, Subgroup.mem_map_of_mem _ hv, by simp⟩
  weak := by
    intro k hk
    have hk' : ∀ v ∈ V, e.symm k * v * (e.symm k)⁻¹ ∈ R := by
      intro v hv
      have := hk (e v) (Subgroup.mem_map_of_mem _ hv)
      obtain ⟨r, hr, hre⟩ := this
      have : e.symm k * v * (e.symm k)⁻¹ = r := by
        apply e.injective
        simpa using hre.symm
      rwa [this]
    obtain ⟨y, hy, r, hr, hkyr⟩ := h.weak _ hk'
    refine ⟨e y, Subgroup.mem_map_of_mem _ hy, e r, Subgroup.mem_map_of_mem _ hr, ?_⟩
    have : k = e (e.symm k) := (e.apply_symm_apply k).symm
    rw [this, hkyr, map_mul]

end Local

section Main

variable {L : Type*} [Group L]

theorem weak_prod [Finite L] (h9 : ¬ 9 ∣ Nat.card L)
    (hL : ∀ R Y : Subgroup L, IsSylowTwoOf R ⊤ → R ≤ Subgroup.normalizer (Y : Set L) →
      oTwoUpper Y = Y → Y ≠ ⊥ → ¬ 7 ∣ Nat.card Y → ∃ V : Subgroup L, LocalData R Y V)
    {T X : Subgroup (L × L)} (hT : IsSylowTwoOf T ⊤)
    (hTX : T ≤ Subgroup.normalizer (X : Set (L × L))) (hO : oTwoUpper X = X)
    (hX : ∃ a : ℕ, Nat.card X = 9 * 2 ^ a) (k : L × L)
    (hk : ∀ w ∈ pCoreOf 2 (X ⊔ T), k * w * k⁻¹ ∈ T) : k ∈ X ⊔ T := by
  classical
  obtain ⟨a, ha⟩ := hX
  have hTmax := A4.isSylowTwoOf_iff_maximal.mp hT
  set R₀ : Subgroup L := T.map (MonoidHom.fst L L) with hR₀
  set R₁ : Subgroup L := T.map (MonoidHom.snd L L) with hR₁
  set Y₀ : Subgroup L := X.map (MonoidHom.fst L L) with hY₀
  set Y₁ : Subgroup L := X.map (MonoidHom.snd L L) with hY₁
  have hR₀P : IsPGroup 2 R₀ := hTmax.2.1.map _
  have hR₁P : IsPGroup 2 R₁ := hTmax.2.1.map _
  have hTle : T ≤ R₀.prod R₁ := Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
  have hTeq : T = R₀.prod R₁ :=
    le_antisymm hTle (hTmax.2.2 _ le_top (isPGroup_prod hR₀P hR₁P) hTle)
  have hTmem : ∀ x : L × L, x ∈ T ↔ x.1 ∈ R₀ ∧ x.2 ∈ R₁ := fun x => by
    rw [hTeq]
    exact Subgroup.mem_prod
  have hR₀S : IsSylowTwoOf R₀ ⊤ := by
    refine A4.isSylowTwoOf_iff_maximal.mpr ⟨le_top, hR₀P, fun P' _ hP' hle => ?_⟩
    have hle' : P'.prod R₁ ≤ T := by
      refine hTmax.2.2 _ le_top (isPGroup_prod hP' hR₁P) ?_
      rw [hTeq]
      exact fun x hx => ⟨hle hx.1, hx.2⟩
    intro p hp
    exact ((hTmem _).mp (hle' (⟨hp, R₁.one_mem⟩ : ((p, 1) : L × L) ∈ P'.prod R₁))).1
  have hR₁S : IsSylowTwoOf R₁ ⊤ := by
    refine A4.isSylowTwoOf_iff_maximal.mpr ⟨le_top, hR₁P, fun P' _ hP' hle => ?_⟩
    have hle' : R₀.prod P' ≤ T := by
      refine hTmax.2.2 _ le_top (isPGroup_prod hR₀P hP') ?_
      rw [hTeq]
      exact fun x hx => ⟨hx.1, hle hx.2⟩
    intro p hp
    exact ((hTmem _).mp (hle' (⟨R₀.one_mem, hp⟩ : ((1, p) : L × L) ∈ R₀.prod P'))).2
  have hR₀N : R₀ ≤ Subgroup.normalizer (Y₀ : Set L) := map_le_normalizer_map _ hTX
  have hR₁N : R₁ ≤ Subgroup.normalizer (Y₁ : Set L) := map_le_normalizer_map _ hTX
  have hOY₀ : oTwoUpper Y₀ = Y₀ := by rw [hY₀, oTwoUpper_map, hO]
  have hOY₁ : oTwoUpper Y₁ = Y₁ := by rw [hY₁, oTwoUpper_map, hO]
  have hXY : X ≤ Y₀.prod Y₁ := Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
  have hdvdX : Nat.card X ∣ Nat.card Y₀ * Nat.card Y₁ := by
    rw [← card_prod_subgroup]
    exact Subgroup.card_dvd_of_le hXY
  have h9X : 9 ∣ Nat.card X := ⟨2 ^ a, ha⟩
  have hY₀ne : Y₀ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Y₀ = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1, one_mul] at hdvdX
    exact h9 (h9X.trans (hdvdX.trans (Subgroup.card_subgroup_dvd_card Y₁)))
  have hY₁ne : Y₁ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Y₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1, mul_one] at hdvdX
    exact h9 (h9X.trans (hdvdX.trans (Subgroup.card_subgroup_dvd_card Y₀)))
  have h7 : ∀ Y : Subgroup L, Nat.card Y ∣ Nat.card X → ¬ 7 ∣ Nat.card Y := by
    intro Y hY h7Y
    have h7X : 7 ∣ 9 * 2 ^ a := ha ▸ h7Y.trans hY
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7X with h | h
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
      omega
  obtain ⟨V₀, hV₀⟩ := hL R₀ Y₀ hR₀S hR₀N hOY₀ hY₀ne (h7 _ (Subgroup.card_map_dvd X (MonoidHom.fst L L)))
  obtain ⟨V₁, hV₁⟩ := hL R₁ Y₁ hR₁S hR₁N hOY₁ hY₁ne (h7 _ (Subgroup.card_map_dvd X (MonoidHom.snd L L)))
  obtain ⟨x₀, hx₀X, hx₀odd, hx₀ne⟩ := exists_odd_map_ne_one (MonoidHom.fst L L) hO hY₀ne
  obtain ⟨x₁, hx₁X, hx₁odd, hx₁ne⟩ := exists_odd_map_ne_one (MonoidHom.snd L L) hO hY₁ne
  have hy₀ : x₀.1 ∈ Y₀ := Subgroup.mem_map_of_mem (MonoidHom.fst L L) hx₀X
  have hy₁ : x₁.2 ∈ Y₁ := Subgroup.mem_map_of_mem (MonoidHom.snd L L) hx₁X
  have hodd₀ : Odd (orderOf x₀.1) :=
    hx₀odd.of_dvd_nat (orderOf_map_dvd (MonoidHom.fst L L) x₀)
  have hodd₁ : Odd (orderOf x₁.2) :=
    hx₁odd.of_dvd_nat (orderOf_map_dvd (MonoidHom.snd L L) x₁)
  have hV₀X : ∀ w ∈ V₀, ((w, 1) : L × L) ∈ X :=
    inl_mem_of_comm hTX (fun v hv => (hTmem _).mpr ⟨hV₀.le_R hv, R₁.one_mem⟩) hx₀X
      (fun w hw => hV₀.comm x₀.1 hy₀ hx₀ne hodd₀ w hw)
  have hV₁X : ∀ w ∈ V₁, ((1, w) : L × L) ∈ X :=
    inr_mem_of_comm hTX (fun v hv => (hTmem _).mpr ⟨R₀.one_mem, hV₁.le_R hv⟩) hx₁X
      (fun w hw => hV₁.comm x₁.2 hy₁ hx₁ne hodd₁ w hw)
  have hVX : V₀.prod V₁ ≤ X := fun w hw => by
    have := X.mul_mem (hV₀X w.1 hw.1) (hV₁X w.2 hw.2)
    simpa using this
  have hcardV : Nat.card (V₀.prod V₁) = 16 := by
    rw [card_prod_subgroup, hV₀.card_V, hV₁.card_V]
  have hcardY : Nat.card (Y₀.prod Y₁) = 144 := by
    rw [card_prod_subgroup, hV₀.card_Y, hV₁.card_Y]
  have h16 : 16 ∣ Nat.card X := hcardV ▸ Subgroup.card_dvd_of_le hVX
  have h144 : Nat.card X ∣ 144 := hcardY ▸ Subgroup.card_dvd_of_le hXY
  have ha4 : a = 4 := by
    rw [ha] at h16 h144
    have hle : 9 * 2 ^ a ≤ 144 := Nat.le_of_dvd (by norm_num) h144
    have ha5 : a < 5 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    have key : ∀ a < 5, 16 ∣ 9 * 2 ^ a → a = 4 := by decide
    exact key a ha5 h16
  have hXeq : X = Y₀.prod Y₁ :=
    Subgroup.eq_of_le_of_card_ge hXY (by rw [hcardY, ha, ha4]; norm_num)
  have hXmem : ∀ x : L × L, x ∈ X ↔ x.1 ∈ Y₀ ∧ x.2 ∈ Y₁ := fun x => by
    rw [hXeq]
    exact Subgroup.mem_prod
  have hJ : V₀.prod V₁ ≤ pCoreOf 2 (X ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVX.trans le_sup_left) ?_
      (IsPGroup.of_card (n := 4) (by rw [hcardV]; norm_num))
    refine sup_le ?_ ?_
    · rw [hXeq]
      exact prod_le_normalizer hV₀.Y_le hV₁.Y_le
    · rw [hTeq]
      exact prod_le_normalizer hV₀.R_le hV₁.R_le
  have hk₀ : ∀ v ∈ V₀, k.1 * v * k.1⁻¹ ∈ R₀ := by
    intro v hv
    have hw : ((v, 1) : L × L) ∈ pCoreOf 2 (X ⊔ T) := hJ ⟨hv, V₁.one_mem⟩
    have := ((hTmem _).mp (hk _ hw)).1
    simpa using this
  have hk₁ : ∀ v ∈ V₁, k.2 * v * k.2⁻¹ ∈ R₁ := by
    intro v hv
    have hw : ((1, v) : L × L) ∈ pCoreOf 2 (X ⊔ T) := hJ ⟨V₀.one_mem, hv⟩
    have := ((hTmem _).mp (hk _ hw)).2
    simpa using this
  obtain ⟨y₀, hy₀', r₀, hr₀, hk₀eq⟩ := hV₀.weak k.1 hk₀
  obtain ⟨y₁, hy₁', r₁, hr₁, hk₁eq⟩ := hV₁.weak k.2 hk₁
  have hkmem : k = (y₀, y₁) * (r₀, r₁) := Prod.ext (by simpa using hk₀eq) (by simpa using hk₁eq)
  rw [hkmem]
  exact Subgroup.mul_mem_sup ((hXmem _).mpr ⟨hy₀', hy₁'⟩) ((hTmem _).mpr ⟨hr₀, hr₁⟩)

end Main

end SBc15

end CFSG.Quasithin
