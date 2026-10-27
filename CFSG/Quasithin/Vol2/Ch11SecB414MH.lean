module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3E

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {G : Type} [Group G] {F : Type} [Field F]

structure Model (Γ V Z : Subgroup G) (F : Type) [Field F] (k : ℕ) (α : ↥Γ →* PGL3 F) where
  β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F)
  sl : ∀ v, Matrix.trace (Multiplicative.toAdd (β v)) = 0
  onto : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → ∃ v, Multiplicative.toAdd (β v) = M
  ker : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Z
  act : ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * (γ : G)⁻¹ → ∀ g : GL (Fin 3) F,
    ProjGenLinGroup.mk g = α γ →
      Multiplicative.toAdd (β v) = twAdj k g (Multiplicative.toAdd (β u))
  normV : Γ ≤ Subgroup.normalizer (V : Set G)
  le : Z ≤ V

variable {Γ V Z : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)

@[expose] def Model.pre (W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) : Subgroup G where
  carrier := {v | ∃ h : v ∈ V, Multiplicative.toAdd (m.β ⟨v, h⟩) ∈ W}
  one_mem' := ⟨V.one_mem, by
    have : m.β (⟨1, V.one_mem⟩ : ↥V) = 1 := map_one m.β
    rw [this, toAdd_one]
    exact W.zero_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    have : m.β (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = m.β ⟨a, ha⟩ * m.β ⟨b, hb⟩ :=
      map_mul m.β ⟨a, ha⟩ ⟨b, hb⟩
    rw [this, toAdd_mul]
    exact W.add_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨V.inv_mem ha, ?_⟩
    have : m.β (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (m.β ⟨a, ha⟩)⁻¹ := map_inv m.β ⟨a, ha⟩
    rw [this, toAdd_inv]
    exact W.neg_mem ha'

theorem Model.pre_le_V (W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) : m.pre W ≤ V :=
  fun _ ⟨h, _⟩ => h

theorem Model.toAdd_eq_zero (v : ↥V) : Multiplicative.toAdd (m.β v) = 0 ↔ (v : G) ∈ Z := by
  rw [← m.ker v]
  exact ⟨fun h => congrArg Multiplicative.ofAdd h, fun h => congrArg Multiplicative.toAdd h⟩

theorem Model.le_pre (W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) : Z ≤ m.pre W := fun z hz =>
  ⟨m.le hz, by rw [(m.toAdd_eq_zero ⟨z, m.le hz⟩).mpr hz]; exact W.zero_mem⟩

theorem Model.pre_mono {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)} (h : W ≤ W') :
    m.pre W ≤ m.pre W' := fun _ ⟨hv, hW⟩ => ⟨hv, h hW⟩

theorem Model.mem_pre_of {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)} (v : ↥V)
    (hv : Multiplicative.toAdd (m.β v) ∈ W) : (v : G) ∈ m.pre W := ⟨v.2, hv⟩

theorem Model.pre_lt {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)} (h : W ≤ W')
    {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ W') (hMt : M.trace = 0) (hMW : M ∉ W) :
    m.pre W < m.pre W' := by
  refine lt_of_le_of_ne (m.pre_mono h) fun he => hMW ?_
  obtain ⟨v, hv⟩ := m.onto M hMt
  have : (v : G) ∈ m.pre W := he ▸ m.mem_pre_of v (hv ▸ hM)
  obtain ⟨_, h'⟩ := this
  rwa [← hv]

theorem Model.pre_le_normalizer (W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) :
    m.pre W' ≤ Subgroup.normalizer (m.pre W : Set G) := by
  rintro s ⟨hs, -⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ c : G, c ∈ m.pre W → s * c * s⁻¹ ∈ m.pre W := by
    rintro c ⟨hc, hcW⟩
    have hmem : s * c * s⁻¹ ∈ V := V.mul_mem (V.mul_mem hs hc) (V.inv_mem hs)
    refine ⟨hmem, ?_⟩
    have e : (⟨s * c * s⁻¹, hmem⟩ : ↥V) = ⟨s, hs⟩ * ⟨c, hc⟩ * (⟨s, hs⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul m.β, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_mul, toAdd_inv]
    convert hcW using 1
    abel
  intro c
  refine ⟨key c, fun h => ?_⟩
  have hsi : s⁻¹ ∈ V := V.inv_mem hs
  obtain ⟨hc', hcW'⟩ := h
  have hcV : c ∈ V := by
    have := V.mul_mem (V.mul_mem hsi hc') hs
    rwa [show s⁻¹ * (s * c * s⁻¹) * s = c by group] at this
  refine ⟨hcV, ?_⟩
  have e : (⟨s * c * s⁻¹, hc'⟩ : ↥V) = ⟨s, hs⟩ * ⟨c, hcV⟩ * (⟨s, hs⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul m.β, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_mul, toAdd_inv] at hcW'
  convert hcW' using 1
  abel

theorem Model.le_normalizer_pre {K : Subgroup G} (hKΓ : K ≤ Γ)
    {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (hW : ∀ γ (hγ : γ ∈ K), ∃ g : GL (Fin 3) F, ProjGenLinGroup.mk g = α ⟨γ, hKΓ hγ⟩ ∧
      ∀ M ∈ W, twAdj k g M ∈ W) :
    K ≤ Subgroup.normalizer (m.pre W : Set G) := by
  have key : ∀ γ ∈ K, ∀ c ∈ m.pre W, γ * c * γ⁻¹ ∈ m.pre W := by
    rintro γ hγ c ⟨hc, hcW⟩
    have hmem : γ * c * γ⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (m.normV (hKΓ hγ)) c).mp hc
    obtain ⟨g, hg, hgW⟩ := hW γ hγ
    refine ⟨hmem, ?_⟩
    rw [m.act ⟨γ, hKΓ hγ⟩ ⟨c, hc⟩ ⟨_, hmem⟩ rfl g hg]
    exact hgW _ hcW
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key γ hγ c, fun h => ?_⟩
  have := key γ⁻¹ (K.inv_mem hγ) _ h
  rwa [show γ⁻¹ * (γ * c * γ⁻¹) * γ⁻¹⁻¹ = c by group] at this

theorem Model.eq_or_eq_of_index_two {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    {M₀ : Matrix (Fin 3) (Fin 3) F} (h2 : ∀ M ∈ W', M ∈ W ∨ M - M₀ ∈ W) {J : Subgroup G}
    (hJ1 : m.pre W ≤ J) (hJ2 : J ≤ m.pre W') : J = m.pre W ∨ J = m.pre W' := by
  by_cases hJ : J ≤ m.pre W
  · exact Or.inl (le_antisymm hJ hJ1)
  right
  refine le_antisymm hJ2 fun s hs => ?_
  obtain ⟨j, hjJ, hjW⟩ := Set.not_subset.mp hJ
  obtain ⟨hjV, hjW'⟩ := hJ2 hjJ
  have hj : Multiplicative.toAdd (m.β ⟨j, hjV⟩) - M₀ ∈ W :=
    (h2 _ hjW').resolve_left fun h => hjW ⟨hjV, h⟩
  obtain ⟨hsV, hsW'⟩ := hs
  rcases h2 _ hsW' with h | h
  · exact hJ1 ⟨hsV, h⟩
  · have hsj : s * j⁻¹ ∈ m.pre W := by
      refine ⟨V.mul_mem hsV (V.inv_mem hjV), ?_⟩
      have e : (⟨s * j⁻¹, V.mul_mem hsV (V.inv_mem hjV)⟩ : ↥V) = ⟨s, hsV⟩ * (⟨j, hjV⟩ : ↥V)⁻¹ :=
        rfl
      rw [e, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_inv]
      convert W.sub_mem h hj using 1
      abel
    have := J.mul_mem (hJ1 hsj) hjJ
    rwa [inv_mul_cancel_right] at this

omit [Field F] in
theorem eq_of_card_four [Field F] [Finite F] (hF : Nat.card F = 4) {a b d t : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (hd : d ≠ 0) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ht : t ≠ 0) :
    t = a ∨ t = b ∨ t = d := by
  by_contra h
  push Not at h
  obtain ⟨hta, htb, htd⟩ := h
  have hinj : Function.Injective (![0, a, b, d, t] : Fin 5 → F) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin, hF] at this
  omega

theorem Model.mul_inv_mem_pre {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    {M₀ : Matrix (Fin 3) (Fin 3) F} {s j : G} (hs : s ∈ V) (hj : j ∈ V) {t : F}
    (hst : Multiplicative.toAdd (m.β ⟨s, hs⟩) - t • M₀ ∈ W)
    (hjt : Multiplicative.toAdd (m.β ⟨j, hj⟩) - t • M₀ ∈ W) : s * j⁻¹ ∈ m.pre W := by
  refine ⟨V.mul_mem hs (V.inv_mem hj), ?_⟩
  have e : (⟨s * j⁻¹, V.mul_mem hs (V.inv_mem hj)⟩ : ↥V) = ⟨s, hs⟩ * (⟨j, hj⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_inv]
  convert W.sub_mem hst hjt using 1
  abel

theorem Model.eq_or_eq_of_scalar [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)} {M₀ : Matrix (Fin 3) (Fin 3) F}
    (hdec : ∀ M ∈ W', ∃ t : F, M - t • M₀ ∈ W) {y : G} (hyV : ∀ s ∈ V, y * s * y⁻¹ ∈ V)
    {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hy : ∀ (s : G) (hs : s ∈ V), s ∈ m.pre W' → ∀ t : F,
      Multiplicative.toAdd (m.β ⟨s, hs⟩) - t • M₀ ∈ W →
        Multiplicative.toAdd (m.β ⟨y * s * y⁻¹, hyV s hs⟩) - (c * t) • M₀ ∈ W)
    {J : Subgroup G} (hJ1 : m.pre W ≤ J) (hJ2 : J ≤ m.pre W')
    (hyJ : y ∈ Subgroup.normalizer (J : Set G)) : J = m.pre W ∨ J = m.pre W' := by
  by_cases hJ : J ≤ m.pre W
  · exact Or.inl (le_antisymm hJ hJ1)
  right
  refine le_antisymm hJ2 fun s hs => ?_
  obtain ⟨j, hjJ, hjW⟩ := Set.not_subset.mp hJ
  obtain ⟨hjV, hjW'⟩ := hJ2 hjJ
  obtain ⟨t₀, ht₀⟩ := hdec _ hjW'
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_zero] at ht₀
    exact hjW ⟨hjV, ht₀⟩
  have hj₁J : y * j * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hyJ j).mp hjJ
  have hj₁ := hy j hjV ⟨hjV, hjW'⟩ t₀ ht₀
  have hj₂J : j * (y * j * y⁻¹) ∈ J := J.mul_mem hjJ hj₁J
  have hj₂V : j * (y * j * y⁻¹) ∈ V := V.mul_mem hjV (hyV j hjV)
  have hj₂ : Multiplicative.toAdd (m.β ⟨_, hj₂V⟩) - ((1 + c) * t₀) • M₀ ∈ W := by
    have e : (⟨j * (y * j * y⁻¹), hj₂V⟩ : ↥V) = ⟨j, hjV⟩ * ⟨y * j * y⁻¹, hyV j hjV⟩ := rfl
    rw [e, map_mul m.β, toAdd_mul]
    convert W.add_mem ht₀ hj₁ using 1
    rw [add_mul, one_mul, add_smul]
    abel
  obtain ⟨hsV, hsW'⟩ := hs
  obtain ⟨t, ht⟩ := hdec _ hsW'
  by_cases ht0 : t = 0
  · subst ht0
    rw [zero_smul, sub_zero] at ht
    exact hJ1 ⟨hsV, ht⟩
  have h1c : 1 + c ≠ 0 := fun h => hc1 (by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2)
  rcases eq_of_card_four hF ht₀0 (mul_ne_zero hc0 ht₀0) (mul_ne_zero h1c ht₀0)
      (fun h => hc1 (by rw [eq_comm, mul_left_eq_self₀] at h; tauto))
      (fun h => hc0 (by
        have : (1 + c - 1) * t₀ = 0 := by linear_combination -h
        simpa [ht₀0] using this))
      (fun h => (one_ne_zero : (1 : F) ≠ 0) (by
        have : (1 + c - c) * t₀ = 0 := by linear_combination -h
        simp [ht₀0] at this)) ht0 with h | h | h
  · subst h
    have := J.mul_mem (hJ1 (m.mul_inv_mem_pre hsV hjV ht ht₀)) hjJ
    rwa [inv_mul_cancel_right] at this
  · subst h
    have := J.mul_mem (hJ1 (m.mul_inv_mem_pre hsV (hyV j hjV) ht hj₁)) hj₁J
    rwa [inv_mul_cancel_right] at this
  · subst h
    have := J.mul_mem (hJ1 (m.mul_inv_mem_pre hsV hj₂V ht hj₂)) hj₂J
    rwa [inv_mul_cancel_right] at this

end CFSG.Quasithin.H13.Ch4.B414.M
