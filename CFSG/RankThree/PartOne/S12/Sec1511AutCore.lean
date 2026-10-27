module

public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne.K159

namespace Sec1511

theorem conj_data {p : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (U : Subgroup ↥S) (hexp : ∀ u ∈ U, u ^ p = 1) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) ≤ Nat.card U) :
    Nat.card (omegaOne p P) = Nat.card U ∧ ∃ h : H, ∀ y : ↥S, (∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      h * (y : H) * h⁻¹ ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H) ∧
      (h * (y : H) * h⁻¹ ∈ Subgroup.centralizer ((omegaOne p P : Subgroup H) : Set H) ↔
        ∀ u ∈ U, y * u * y⁻¹ = u) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set UH : Subgroup H := U.map S.subtype with hUH
  have hUHp : IsPGroup p UH := isPGroup_map_subtype hexp
  have hUHexp : ∀ x ∈ UH, x ^ p = 1 := exp_map_subtype' hexp
  have hUHcard : Nat.card UH = Nat.card U := Subgroup.card_map_of_injective S.subtype_injective
  have hUHmem : ∀ u : S, (u : H) ∈ UH ↔ u ∈ U := fun u =>
    Subgroup.mem_map_iff_mem S.subtype_injective
  obtain ⟨h, hh⟩ := exists_conj_le_sylow hP hUHp
  have hle : conjSub h UH ≤ omegaOne p P := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_omegaOne hh hy (hUHexp y hy)
  have hge : Nat.card U ≤ Nat.card (omegaOne p P) := by
    have := Subgroup.card_le_of_le hle
    rwa [card_conjSub, hUHcard] at this
  have hcardeq : Nat.card (omegaOne p P) = Nat.card U := le_antisymm hΩ hge
  have heq : conjSub h UH = omegaOne p P := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSub, hUHcard, hcardeq]
  set E : Subgroup H := omegaOne p P with hE
  have hmemE : ∀ x : H, x ∈ E ↔ h⁻¹ * x * h ∈ UH := fun x => by
    rw [← heq, mem_conjSub_iff]
  refine ⟨hcardeq, h, fun g hgU => ?_⟩
  have hgU' : ∀ u : S, g * u * g⁻¹ ∈ U ↔ u ∈ U := by
    intro u
    refine ⟨fun hu => ?_, fun hu => hgU u hu⟩
    have hinj : Function.Injective (fun v : U => (⟨g * (v : S) * g⁻¹, hgU v v.2⟩ : U)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨g * u * g⁻¹, hu⟩
    have : (v : S) = u := by
      have := congrArg Subtype.val hv
      simpa using this
    exact this ▸ v.2
  have hgUH : ∀ y : H, y ∈ UH ↔ (g : H) * y * (g : H)⁻¹ ∈ UH := by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact (hUHmem (g * u * g⁻¹)).2 (hgU u hu)
    · intro hy
      have h1 : (g : H) * y * (g : H)⁻¹ ∈ S := Subgroup.map_subtype_le U hy
      have hyS : y ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem g.2) h1) g.2
        simpa [mul_assoc] using this
      have h2 : (g * ⟨y, hyS⟩ * g⁻¹ : S) ∈ U := (hUHmem _).1 (by simpa using hy)
      exact (hUHmem ⟨y, hyS⟩).2 ((hgU' _).1 h2)
  set g' : H := h * (g : H) * h⁻¹ with hg'
  have hg'N : g' ∈ Subgroup.normalizer (E : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemE x, hmemE (g' * x * g'⁻¹)]
    have e1 : h⁻¹ * (g' * x * g'⁻¹) * h = (g : H) * (h⁻¹ * x * h) * (g : H)⁻¹ := by
      simp only [hg']; group
    rw [e1]
    exact hgUH _
  refine ⟨hg'N, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc u hu
    have hx : h * (u : H) * h⁻¹ ∈ E := by
      rw [hmemE]
      have : h⁻¹ * (h * (u : H) * h⁻¹) * h = (u : H) := by group
      rw [this]
      exact (hUHmem u).2 hu
    have h1 := hc _ hx
    apply Subtype.ext
    have h2 : (u : H) = (g : H) * (u : H) * (g : H)⁻¹ := by
      have := congrArg (fun z => h⁻¹ * z * h) h1
      have e2 : h⁻¹ * (h * ↑u * h⁻¹ * (h * ↑g * h⁻¹)) * h = (u : H) * (g : H) := by group
      have e3 : h⁻¹ * (h * ↑g * h⁻¹ * (h * ↑u * h⁻¹)) * h = (g : H) * (u : H) := by group
      simp only [hg', e2, e3] at this
      calc (u : H) = (u : H) * (g : H) * (g : H)⁻¹ := by group
        _ = (g : H) * (u : H) * (g : H)⁻¹ := by rw [this]
    simpa using h2.symm
  · intro hc x hx
    have hxU : h⁻¹ * x * h ∈ UH := (hmemE x).1 hx
    obtain ⟨u, hu, hux⟩ := hxU
    have h1 := hc u hu
    have h2 : (g : H) * (u : H) = (u : H) * (g : H) := by
      have h3 : g * u = u * g := by
        calc g * u = (g * u * g⁻¹) * g := by group
          _ = u * g := by rw [h1]
      simpa using congrArg Subtype.val h3
    have hxe : x = h * (u : H) * h⁻¹ := by
      have : (u : H) = h⁻¹ * x * h := hux
      rw [this]; group
    rw [hxe]
    calc h * (u : H) * h⁻¹ * (h * (g : H) * h⁻¹)
        = h * ((u : H) * (g : H)) * h⁻¹ := by group
      _ = h * ((g : H) * (u : H)) * h⁻¹ := by rw [h2]
      _ = h * (g : H) * h⁻¹ * (h * (u : H) * h⁻¹) := by group

theorem exact_of_witness {p : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (U : Subgroup ↥S) (hexp : ∀ u ∈ U, u ^ p = 1) (g : ↥S)
    (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) {r : ℕ} (hr : 0 < r)
    (hgr : ∀ u ∈ U, g ^ r * u * (g ^ r)⁻¹ = u)
    (hmove : ∀ k : ℕ, 0 < k → k < r → ∃ u ∈ U, g ^ k * u * (g ^ k)⁻¹ ≠ u)
    {P : Subgroup H} (hP : IsSylowOf p P ⊤) (hΩ : Nat.card (omegaOne p P) ≤ Nat.card U) :
    Nat.card (omegaOne p P) = Nat.card U ∧
      ∃ g' ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
        OrderModC (omegaOne p P) g' r := by
  obtain ⟨hcard, h, hh⟩ := conj_data hp U hexp hP hΩ
  have hgpow : ∀ k : ℕ, ∀ u ∈ U, g ^ k * u * (g ^ k)⁻¹ ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
        intro u hu
        have := hgU _ (ih u hu)
        simpa [pow_succ', mul_assoc] using this
  refine ⟨hcard, h * (g : H) * h⁻¹, (hh g hgU).1, hr, ?_, fun k hk0 hkr hck => ?_⟩
  · have e : (h * (g : H) * h⁻¹) ^ r = h * ((g ^ r : S) : H) * h⁻¹ := by
      rw [conj_pow]; simp
    rw [e]
    exact (hh (g ^ r) (hgpow r)).2.2 hgr
  · obtain ⟨u, hu, hne⟩ := hmove k hk0 hkr
    have e : (h * (g : H) * h⁻¹) ^ k = h * ((g ^ k : S) : H) * h⁻¹ := by
      rw [conj_pow]; simp
    rw [e] at hck
    exact hne ((hh (g ^ k) (hgpow k)).2.1 hck u hu)

@[expose] def ExactWit (p c r : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ (U : Subgroup S) (g : S), (∀ u ∈ U, u ^ p = 1) ∧ Nat.card U = c ∧ (∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧
    0 < r ∧ (∀ u ∈ U, g ^ r * u * (g ^ r)⁻¹ = u) ∧
    ∀ k : ℕ, 0 < k → k < r → ∃ u ∈ U, g ^ k * u * (g ^ k)⁻¹ ≠ u

theorem ExactWit.of_mulEquiv {p c r : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : ExactWit p c r S) : ExactWit p c r T := by
  obtain ⟨U, g, hexp, hcard, hgU, hr, hgr, hmove⟩ := h
  refine ⟨U.map e.toMonoidHom, e g, ?_, ?_, ?_, hr, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨g * u * g⁻¹, hgU u hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    have h2 := congrArg e (hgr u hu)
    simpa [map_mul, map_pow, map_inv] using h2
  · intro k hk0 hkr
    obtain ⟨u, hu, hne⟩ := hmove k hk0 hkr
    refine ⟨e u, ⟨u, hu, rfl⟩, fun h => hne ?_⟩
    apply e.injective
    simpa [map_mul, map_pow, map_inv] using h

theorem ExactWit.row {p c r : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (hS : ExactWit p c r ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) ≤ c) :
    Nat.card (omegaOne p P) = c ∧
      ∃ g' ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
        OrderModC (omegaOne p P) g' r := by
  obtain ⟨U, g, hexp, hcard, hgU, hr, hgr, hmove⟩ := hS
  rw [← hcard] at hΩ ⊢
  exact exact_of_witness hp U hexp g hgU hr hgr hmove hP hΩ

theorem inv_conj_mem {S : Type*} [Group S] [Finite S] (U : Subgroup S) {x : S}
    (hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U) : ∀ u ∈ U, x⁻¹ * u * x ∈ U := by
  intro u hu
  have hinj : Function.Injective (fun v : U => (⟨x * (v : S) * x⁻¹, hx v v.2⟩ : U)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨u, hu⟩
  have : x * (v : S) * x⁻¹ = u := by simpa using congrArg Subtype.val hv
  have h2 : x⁻¹ * u * x = (v : S) := by rw [← this]; group
  rw [h2]
  exact v.2

@[expose] def BigAutWit (p c m : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ (U : Subgroup S) (F : Finset S), (∀ u ∈ U, u ^ p = 1) ∧ Nat.card U = c ∧ F.card = m ∧
    (∀ x ∈ F, ∀ u ∈ U, x * u * x⁻¹ ∈ U) ∧
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∃ u ∈ U, (x⁻¹ * y) * u * (x⁻¹ * y)⁻¹ ≠ u

theorem BigAutWit.of_mulEquiv {p c m : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : BigAutWit p c m S) : BigAutWit p c m T := by
  classical
  obtain ⟨U, F, hexp, hcard, hF, hnorm, hmove⟩ := h
  refine ⟨U.map e.toMonoidHom, F.image e, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
  · rw [Finset.card_image_of_injective _ e.injective]; exact hF
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨x0 * u * x0⁻¹, hnorm x0 hx0 u hu, by simp⟩
  · intro x hx y hy hxy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨u, hu, hne⟩ := hmove x0 hx0 y0 hy0 (fun h => hxy (by rw [h]))
    refine ⟨e u, ⟨u, hu, rfl⟩, fun h => hne ?_⟩
    apply e.injective
    simpa [map_mul, map_inv] using h

theorem BigAutWit.row {p c m : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (hS : BigAutWit p c m ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) ≤ c) :
    Nat.card (omegaOne p P) = c ∧
      ∃ F : Finset H, F.card = m ∧
        (∀ x ∈ F, x ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H)) ∧
        ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
          x⁻¹ * y ∉ Subgroup.centralizer ((omegaOne p P : Subgroup H) : Set H) := by
  classical
  obtain ⟨U, F, hexp, hcard, hF, hnorm, hmove⟩ := hS
  rw [← hcard] at hΩ ⊢
  obtain ⟨hcard', h, hh⟩ := conj_data hp U hexp hP hΩ
  refine ⟨hcard', F.image (fun x : ↥S => h * (x : H) * h⁻¹), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective, hF]
    intro x y hxy
    have h1 : (x : H) = y := by simpa using hxy
    exact Subtype.ext h1
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    exact (hh x0 (hnorm x0 hx0)).1
  · intro x hx y hy hxy hc
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hy
    have hne : x0 ≠ y0 := fun h' => hxy (by rw [h'])
    obtain ⟨u, hu, hne'⟩ := hmove x0 hx0 y0 hy0 hne
    have hcomb : ∀ w ∈ U, (x0⁻¹ * y0) * w * (x0⁻¹ * y0)⁻¹ ∈ U := by
      intro w hw
      have h1 := hnorm y0 hy0 w hw
      have h2 := inv_conj_mem U (hnorm x0 hx0) _ h1
      simpa [mul_assoc] using h2
    have e : (h * (x0 : H) * h⁻¹)⁻¹ * (h * (y0 : H) * h⁻¹) = h * (((x0⁻¹ * y0 : ↥S)) : H) * h⁻¹ := by
      simp; group
    rw [e] at hc
    exact hne' ((hh (x0⁻¹ * y0) hcomb).2.1 hc u hu)

end Sec1511

end CFSG.RankThree.PartOne
