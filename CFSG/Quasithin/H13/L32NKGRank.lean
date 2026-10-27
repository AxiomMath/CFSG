module

public import CFSG.Quasithin.H13.L32NKGG22
public import Certificates.Certificate7115

public section

namespace CFSG.Quasithin.H13.KGCert

@[expose] def KGG22RankModel : Prop :=
  ∀ a ∈ g22Mats, ∀ b ∈ g22Mats, ∀ c ∈ g22Mats, ∀ e ∈ g22Mats,
    a * a = 1 → b * b = 1 → c * c = 1 → e * e = 1 → a ≠ 1 → b ≠ 1 → c ≠ 1 → e ≠ 1 →
    a * b = b * a → a * c = c * a → b * c = c * b → a * e = e * a → b * e = e * b →
    c * e = e * c → b ≠ a → c ≠ a → c ≠ b → c ≠ a * b →
    e = a ∨ e = b ∨ e = c ∨ e = a * b ∨ e = a * c ∨ e = b * c ∨ e = a * b * c

theorem kgG22RankModel :
    KGG22RankModel := by
  intro a ha b hb c hc e he ha2 hb2 hc2 he2 ha1 hb1 hc1 he1 hab hac hbc hae hbe hce hba hca hcb
    hcab
  obtain ⟨ax, hax, rfl⟩ := (mem_g22Mats_iff a).mp ha
  obtain ⟨bx, hbx, rfl⟩ := (mem_g22Mats_iff b).mp hb
  obtain ⟨cx, hcx, rfl⟩ := (mem_g22Mats_iff c).mp hc
  obtain ⟨ex, hex, rfl⟩ := (mem_g22Mats_iff e).mp he
  have hmul : ∀ {x y : List ℕ}, ValidC y → decodeC (mulC x y) = decodeC x * decodeC y :=
    fun hy => decodeC_mulC _ _ hy.1
  have hinv : ∀ {x : List ℕ}, x ∈ g22Elems → decodeC x * decodeC x = 1 → decodeC x ≠ 1 →
      x ∈ g22Invs := by
    intro x hx h2 h1
    have hxV := validC_of_mem hx
    have e1 : mulC x x = oneC :=
      decodeC_injOn (validC_mulC hxV hxV) validC_oneC (by rw [hmul hxV, h2, decodeC_oneC])
    have e2 : x ≠ oneC := fun h => h1 (by rw [h, decodeC_oneC])
    refine List.mem_filter.mpr ⟨hx, ?_⟩
    simp [e1, e2]
  have hcomm : ∀ {x y : List ℕ}, x ∈ g22Elems → y ∈ g22Elems →
      decodeC x * decodeC y = decodeC y * decodeC x → commC x y = true := by
    intro x y hx hy h
    have hxV := validC_of_mem hx
    have hyV := validC_of_mem hy
    have h' : mulC x y = mulC y x := decodeC_injOn (validC_mulC hxV hyV) (validC_mulC hyV hxV)
      (by rw [hmul hyV, hmul hxV, h])
    simp [commC, h']
  have haI := hinv hax ha2 ha1
  have hbI := hinv hbx hb2 hb1
  have hcI := hinv hcx hc2 hc1
  have heI := hinv hex he2 he1
  have hb' : bx ≠ ax := fun h => hba (by rw [h])
  have hc'a : cx ≠ ax := fun h => hca (by rw [h])
  have hc'b : cx ≠ bx := fun h => hcb (by rw [h])
  have hc'ab : cx ≠ mulC ax bx := fun h => hcab (by rw [h, hmul (validC_of_mem hbx)])
  have hcheck := Certificates.certificate7115
  simp only [g22RankCheck, List.all_eq_true] at hcheck
  have h1 := hcheck ax haI bx (List.mem_filter.mpr ⟨hbI, hcomm hax hbx hab⟩)
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h1
  have h2 := (h1.resolve_left hb') cx (List.mem_filter.mpr
    ⟨List.mem_filter.mpr ⟨hcI, hcomm hax hcx hac⟩, hcomm hbx hcx hbc⟩)
  have h3 := h2.resolve_left (fun h => by
    rcases h with (h | h) | h
    · exact hc'a h
    · exact hc'b h
    · exact hc'ab h)
  have h4 := h3 ex (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨heI, hcomm hax hex hae⟩, hcomm hbx hex hbe⟩, hcomm hcx hex hce⟩)
  have hcV := validC_of_mem hcx
  have hbV := validC_of_mem hbx
  rcases h4 with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · right; right; right; left; exact hmul hbV
  · right; right; right; right; left; exact hmul hcV
  · right; right; right; right; right; left; exact hmul hcV
  · right; right; right; right; right; right; rw [hmul hcV, hmul hbV]

variable {X : Type*} [Group X]

theorem exists_mem_not_mem (A : Subgroup X) [Finite A] (l : List X) (hl : l.length < Nat.card A) :
    ∃ x ∈ A, x ∉ l := by
  classical
  by_contra hc
  push Not at hc
  have hsub : (A : Set X) ⊆ ↑l.toFinset := fun x hx => List.mem_toFinset.mpr (hc x hx)
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  have h2 := List.toFinset_card_le l
  change Nat.card ↥A ≤ _ at h1
  omega

theorem exists_four (A : Subgroup X) [Finite A] (h8 : 8 < Nat.card A) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ e ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧
      c ≠ a * b ∧ e ≠ 1 ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ a * b ∧ e ≠ a * c ∧ e ≠ b * c ∧
      e ≠ a * b * c := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_not_mem A [1] (by simp; omega)
  obtain ⟨b, hb, hb'⟩ := exists_mem_not_mem A [1, a] (by simp; omega)
  obtain ⟨c, hc, hc'⟩ := exists_mem_not_mem A [1, a, b, a * b] (by simp; omega)
  obtain ⟨e, he, he'⟩ := exists_mem_not_mem A [1, a, b, c, a * b, a * c, b * c, a * b * c]
    (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha' hb' hc' he'
  exact ⟨a, ha, b, hb, c, hc, e, he, ha', hb'.1, hb'.2, hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2,
    he'.1, he'.2.1, he'.2.2.1, he'.2.2.2.1, he'.2.2.2.2.1, he'.2.2.2.2.2.1, he'.2.2.2.2.2.2.1,
    he'.2.2.2.2.2.2.2⟩

theorem kgG22Rank_of (hM : KGG22RankModel) (hO : KGSp6Order12096) : KGG22Rank := by
  intro V _ _ _ B hBalt hBnd hdim Γ hΓB hcard A hAΓ hAc hA2
  obtain ⟨b, hb⟩ := hO V B hBalt hBnd hdim Γ hΓB hcard
  set m : (V ≃ₗ[ZMod 2] V) → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    fun γ => LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) with hm
  have hmul : ∀ γ δ : V ≃ₗ[ZMod 2] V, m (γ * δ) = m γ * m δ := fun γ δ => by
    simp only [hm, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hone : m 1 = 1 := by
    simp only [hm, LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
  have hinj : ∀ γ δ : V ≃ₗ[ZMod 2] V, m γ = m δ → γ = δ := fun γ δ h =>
    LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h)
  have hmem : ∀ γ ∈ A, m γ ∈ g22Mats := fun γ hγ => (hb _).mpr ⟨γ, hAΓ hγ, rfl⟩
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun γ : V ≃ₗ[ZMod 2] V => (γ : V → V)) fun _ _ h =>
      LinearEquiv.ext (congrFun h)
  by_contra h8
  push Not at h8
  obtain ⟨x, hx, y, hy, z, hz, e, he, hx1, hy1, hyx, hz1, hzx, hzy, hzxy, he1, hex, hey, hez,
    hexy, hexz, heyz, hexyz⟩ := exists_four A h8
  have hne : ∀ γ δ : V ≃ₗ[ZMod 2] V, γ ≠ δ → m γ ≠ m δ := fun γ δ h h' => h (hinj γ δ h')
  have hsq : ∀ γ ∈ A, m γ * m γ = 1 := fun γ hγ => by rw [← hmul, hA2 γ hγ, hone]
  have hc : ∀ γ ∈ A, ∀ δ ∈ A, m γ * m δ = m δ * m γ := fun γ hγ δ hδ => by
    rw [← hmul, ← hmul, hAc γ hγ δ hδ]
  have h1 : ∀ γ : V ≃ₗ[ZMod 2] V, γ ≠ 1 → m γ ≠ 1 := fun γ hγ h => hγ (hinj γ 1 (h.trans hone.symm))
  rcases hM (m x) (hmem x hx) (m y) (hmem y hy) (m z) (hmem z hz) (m e) (hmem e he)
      (hsq x hx) (hsq y hy) (hsq z hz) (hsq e he) (h1 x hx1) (h1 y hy1) (h1 z hz1) (h1 e he1)
      (hc x hx y hy) (hc x hx z hz) (hc y hy z hz) (hc x hx e he) (hc y hy e he) (hc z hz e he)
      (hne y x hyx) (hne z x hzx) (hne z y hzy) (by rw [← hmul]; exact hne z (x * y) hzxy) with
    h | h | h | h | h | h | h
  · exact hex (hinj e x h)
  · exact hey (hinj e y h)
  · exact hez (hinj e z h)
  · exact hexy (hinj e (x * y) (by rw [hmul]; exact h))
  · exact hexz (hinj e (x * z) (by rw [hmul]; exact h))
  · exact heyz (hinj e (y * z) (by rw [hmul]; exact h))
  · exact hexyz (hinj e (x * y * z) (by rw [hmul, hmul]; exact h))

theorem kgG22Rank
    (hO : KGSp6Order12096) : KGG22Rank :=
  kgG22Rank_of kgG22RankModel hO

end CFSG.Quasithin.H13.KGCert
