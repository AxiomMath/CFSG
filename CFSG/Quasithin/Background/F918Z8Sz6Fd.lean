module

public import CFSG.Quasithin.Background.F918Z8Sz6Fc
public import CFSG.Quasithin.Background.F918Z8Sz6Fa

public section

namespace CFSG.Quasithin.SzTorus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.Ree

section Assembly

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem fixV_zpowers_iff_apply {g : MulAut Y} {v : Y} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite Y] in
theorem map_inf_fixV {P : Subgroup (MulAut Y)} {z : MulAut Y} (hzP : ∀ y, y ∈ P ↔ z⁻¹ * y * z ∈ P)
    (A : Subgroup Y) : A.map z.toMonoidHom ⊓ fixV P = (A ⊓ fixV P).map z.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hyP⟩
    refine ⟨v, ⟨hv, fun p hp => ?_⟩, rfl⟩
    have hp' : z * p * z⁻¹ ∈ P := by
      rw [hzP]
      simpa [mul_assoc] using hp
    have h1 : (z * p * z⁻¹) (z v) = z v := hyP _ hp'
    have h2 : z (p v) = z v := by simpa [MulAut.mul_apply] using h1
    exact z.injective h2
  · rintro ⟨v, ⟨hv, hvP⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, fun p hp => ?_⟩
    have hp' : z⁻¹ * p * z ∈ P := (hzP p).1 hp
    have h1 : (z⁻¹ * p * z) v = v := hvP _ hp'
    have h2 : z⁻¹ (p (z v)) = v := by simpa [MulAut.mul_apply] using h1
    show p (z v) = z v
    calc p (z v) = z (z⁻¹ (p (z v))) := by simp
      _ = z v := by rw [h2]

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_normalizing (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {g : MulAut Y} (hg : g ∈ Γ) :
    ∃ z : MulAut Y, (∀ l ∈ Λ, z⁻¹ * l * z ∈ Λ) ∧ (∀ y, y ∈ C.P ↔ z⁻¹ * y * z ∈ C.P) ∧
      V.map z.toMonoidHom = V.map g.toMonoidHom := by
  have hg' : ∀ l ∈ Λ, g⁻¹ * l * g⁻¹⁻¹ ∈ Λ := fun l hl => hΓ g⁻¹ (inv_mem hg) l hl
  have hsyl : IsSylowTwoOf (szConj g⁻¹ C.P) Λ :=
    isSylowTwoOf_szConj hg' C.P_le (C.card_P hK |>.trans (by
      rw [← pow_mul, mul_comm (2 * a + 1) 2] : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1))))
      (C.card_Lam hK) (odd_cofactor a)
  obtain ⟨h, hhΛ, hh⟩ := A4.exists_conj_of_isSylowTwoOf (C.isSylowTwoOf_P hK) hsyl
  have hhΛ' : ∀ l ∈ Λ, h⁻¹ * l * h ∈ Λ := fun l hl =>
    Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hhΛ) hl) hhΛ
  refine ⟨g * h, fun l hl => ?_, fun y => ?_, ?_⟩
  · have e : (g * h)⁻¹ * l * (g * h) = h⁻¹ * (g⁻¹ * l * g) * h := by group
    rw [e]
    exact hhΛ' _ (by simpa using hΓ g⁻¹ (inv_mem hg) l hl)
  · have e1 : y ∈ C.P ↔ g⁻¹ * y * g ∈ szConj g⁻¹ C.P := by
      rw [mem_szConj]
      have : g⁻¹⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this]
    rw [e1, hh]
    have e : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
    rw [e]
  · ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨h v, C.inv h hhΛ v hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨h⁻¹ v, C.inv _ (Λ.inv_mem hhΛ) v hv, ?_⟩
      show (g * h) (h⁻¹ v) = g v
      simp [MulAut.mul_apply]

omit [Finite Y] in
theorem fixGood_map (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1)) {t : MulAut Y}
    (htΛ : t ∈ Λ) (htN : t ∈ Subgroup.normalizer (C.P : Set (MulAut Y)))
    (hord : orderOf t = 2 ^ (2 * a + 1) - 1) {z : MulAut Y}
    (hzΛ : ∀ l ∈ Λ, z⁻¹ * l * z ∈ Λ) (hzP : ∀ y, y ∈ C.P ↔ z⁻¹ * y * z ∈ C.P) :
    FixGood (2 ^ (2 * a + 1) - 1) C.P t (V.map z.toMonoidHom) := by
  have hmap := map_inf_fixV hzP V
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hmap, Subgroup.card_map_of_injective z.injective,
      Subgroup.card_map_of_injective z.injective, C.card_fix_P hK,
      Nat.card_congr C.Θ.toEquiv, card_natModule, hK]
  · refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    rw [hmap] at hy
    obtain ⟨⟨v, ⟨hvV, hvP⟩, rfl⟩, hyZ⟩ := hy
    have hz'N : z⁻¹ ∈ Subgroup.normalizer (C.P : Set (MulAut Y)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simpa using hzP y
    have hzN : z ∈ Subgroup.normalizer (C.P : Set (MulAut Y)) := by
      simpa using inv_mem hz'N
    have hsN : z⁻¹ * t * z ∈ Subgroup.normalizer (C.P : Set (MulAut Y)) :=
      mul_mem (mul_mem hz'N htN) hzN
    have hords : orderOf (z⁻¹ * t * z) = 2 ^ (2 * a + 1) - 1 := by
      rw [← hord]
      have := orderOf_injective (MulAut.conj z⁻¹).toMonoidHom (MulAut.conj z⁻¹).injective t
      simpa [MulAut.conj_apply] using this
    have hspow : (z⁻¹ * t * z) ^ k = z⁻¹ * t ^ k * z := by
      have := conj_pow (a := z⁻¹) (b := t) (i := k)
      simpa using this
    have h1 : (t ^ k) (z v) = z v := hyZ (t ^ k) (Subgroup.mem_zpowers _)
    have h2 : ((z⁻¹ * t * z) ^ k) v = v := by
      rw [hspow]
      have : z⁻¹ ((t ^ k) (z v)) = v := by rw [h1]; simp
      simpa [MulAut.mul_apply] using this
    have hv : v ∈ V ⊓ fixV C.P ⊓ fixV (Subgroup.zpowers ((z⁻¹ * t * z) ^ k)) :=
      ⟨⟨hvV, hvP⟩, fixV_zpowers_iff_apply.2 h2⟩
    rw [C.fix_zpowers_eq_bot hK (hzΛ t htΛ) hsN hords hk, Subgroup.mem_bot] at hv
    rw [hv]
    simp

theorem suz_torus_fix_of_coord (C : SzCoord Λ V a K) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤) :
    ∃ (P : Subgroup (MulAut Y)) (t : MulAut Y), IsSylowTwoOf P Λ ∧ t ∈ Λ ∧
      t ∈ Subgroup.normalizer (P : Set (MulAut Y)) ∧ orderOf t = 2 ^ (2 * a + 1) - 1 ∧
      ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
        Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4 ∧
        ∀ k : ℕ, ¬ (2 ^ (2 * a + 1) - 1 ∣ k) →
          U ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥ := by
  obtain ⟨t, htΛ, htN, hord⟩ := C.exists_torus hK
  refine ⟨C.P, t, C.isSylowTwoOf_P hK, htΛ, htN, hord, fun U hU => ?_⟩
  have hgood : ∀ g ∈ Γ, FixGood (2 ^ (2 * a + 1) - 1) C.P t (V.map g.toMonoidHom) := by
    intro g hg
    obtain ⟨z, hzΛ, hzP, hzV⟩ := exists_normalizing C hK hΓ hg
    rw [← hzV]
    exact fixGood_map C hK htΛ htN hord hzΛ hzP
  exact fixGood_of_gen C.P_le htΛ hΓ hirr hgen hgood hU

end Assembly

end CFSG.Quasithin.SzTorus
