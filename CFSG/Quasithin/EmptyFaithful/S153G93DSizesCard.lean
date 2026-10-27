module

public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin.S153G93D.Sizes

theorem card_eq_of_realizesVia {V : Type*} [CommGroup V] {D : FFModel} {J : Subgroup (MulAut V)}
    {π : D.Gam →* ↥J} (h : D.RealizesVia J ⊤ ⊥ π) : Nat.card V = Nat.card D.Mod := by
  obtain ⟨-, -, -, -, -, -, -, β, hsurj, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hker u).1 hu))
  rw [← Subgroup.card_top (G := V)]
  exact Nat.card_congr (Equiv.ofBijective β ⟨hinj, hsurj⟩)

theorem card_sec_eq (D : FFModel) :
    Nat.card ↥D.sec = Nat.card D.Mod * Nat.card ↥(D.ker.subgroupOf D.sec) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem card_mod_le (D : FFModel) (hfin : Finite ↥D.sec) : Nat.card D.Mod ≤ Nat.card ↥D.sec :=
  Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := D.ker.subgroupOf D.sec))

theorem card_mod_eq_of_top_bot (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥) :
    Nat.card D.Mod = Nat.card D.Amb := by
  have h1 : Nat.card ↥(D.ker.subgroupOf D.sec) = 1 := by
    rw [hk, Subgroup.bot_subgroupOf, Subgroup.card_bot]
  have h2 : Nat.card ↥D.sec = Nat.card D.Amb := by
    rw [hs, Subgroup.card_top]
  rw [← h2, card_sec_eq D, h1, mul_one]

theorem card_nat_mod {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  rw [card_mod_eq_of_top_bot _ rfl rfl]
  change Nat.card (Multiplicative (ι → K)) = _
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem card_eq_binaryNaturalSL {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {d a : ℕ}
    (h : BinaryNaturalSL J ⊤ ⊥ d a) : Nat.card W = 2 ^ (d * a) := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  rw [card_eq_of_realizesVia hπ, card_nat_mod, hK, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_eq_binaryNaturalSp4 {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {a : ℕ}
    (h : BinaryNaturalSp4 J ⊤ ⊥ a) : Nat.card W = 2 ^ (4 * a) := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
    rw [Fintype.card_sum, Fintype.card_fin]
  rw [card_eq_of_realizesVia hπ, card_nat_mod, hK, hι, ← pow_mul, mul_comm]

theorem card_permMod (n : ℕ) : Nat.card (G6.PermMod n) = 2 ^ n := by
  change Nat.card (Multiplicative (Fin n → ZMod 2)) = _
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_coreMod_le (n : ℕ) : Nat.card ↥(G6.coreMod n) ≤ 2 ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := Nat.card_le_card_of_injective (Subtype.val : ↥(G6.coreMod 0) → G6.PermMod 0)
      Subtype.val_injective
    rw [card_permMod] at h
    exact h
  · let coordSum : G6.PermMod n →* Multiplicative (ZMod 2) :=
      { toFun := fun x => Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
        map_one' := by simp
        map_mul' := fun x y => by simp [Finset.sum_add_distrib] }
    have hker : coordSum.ker = G6.coreMod n := by
      ext x
      rw [MonoidHom.mem_ker, G6.mem_coreMod]
      exact ofAdd_eq_one
    have hsurj : Function.Surjective coordSum := by
      intro c
      refine ⟨Multiplicative.ofAdd (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c)), ?_⟩
      change Multiplicative.ofAdd (∑ i, (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c) :
        Fin n → ZMod 2) i) = c
      rw [Finset.sum_pi_single']
      simp only [Finset.mem_univ, ↓reduceIte, ofAdd_toAdd]
    have h := Subgroup.card_ker_mul_card_range coordSum
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker, card_permMod] at h
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
    have h3 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2, h3] at h
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).le

theorem card_le_alternatingNatural {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {n : ℕ}
    (h : AlternatingNatural J ⊤ ⊥ n) : Nat.card W ≤ 2 ^ (n - 1) := by
  obtain ⟨π, hπ⟩ := h
  have hfin : Finite ↥(FFModel.altDn n).sec := inferInstanceAs (Finite ↥(G6.coreMod n))
  rw [card_eq_of_realizesVia hπ]
  exact (card_mod_le _ hfin).trans (card_coreMod_le n)

theorem card_le_symmetricNatural {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {n : ℕ}
    (h : SymmetricNatural J ⊤ ⊥ n) : Nat.card W ≤ 2 ^ (n - 1) := by
  obtain ⟨π, hπ⟩ := h
  have hfin : Finite ↥(FFModel.symDn n).sec := inferInstanceAs (Finite ↥(G6.coreMod n))
  rw [card_eq_of_realizesVia hπ]
  exact (card_mod_le _ hfin).trans (card_coreMod_le n)

theorem card_eq_a7Four {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    (h : A7Four J ⊤ ⊥) : Nat.card W = 2 ^ 4 := by
  obtain ⟨α, π, hπ⟩ := h
  rw [card_eq_of_realizesVia hπ, card_mod_eq_of_top_bot _ rfl rfl]
  change Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 2 ^ 4
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end CFSG.Quasithin.S153G93D.Sizes
