module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private def s16h_dc_commHom {W : Type} [CommGroup W] (t : MulAut W) : W →* W where
  toFun y := t y * y⁻¹
  map_one' := by simp
  map_mul' y y' := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private lemma s16h_dc_commHom_apply {W : Type} [CommGroup W] (t : MulAut W) (y : W) :
    s16h_dc_commHom t y = t y * y⁻¹ := rfl

private lemma s16h_dc_disjoint_pair {W : Type} [Group W] {Δ : Fin 3 → Subgroup W}
    (hinj : Function.Injective Δ) (hind : sSupIndep (Set.range Δ)) {a b : Fin 3}
    (hab : a ≠ b) : Disjoint (Δ a) (Δ b) :=
  hind.pairwiseDisjoint (Set.mem_range_self a) (Set.mem_range_self b)
    (fun h => hab (hinj h))

private lemma s16h_dc_disjoint_third {W : Type} [Group W] {Δ : Fin 3 → Subgroup W}
    (hinj : Function.Injective Δ) (hind : sSupIndep (Set.range Δ)) {a b i : Fin 3}
    (hi_a : i ≠ a) (hi_b : i ≠ b) : Disjoint (Δ a ⊔ Δ b) (Δ i) := by
  have hsub : ({Δ a, Δ b} : Set (Subgroup W)) ⊆ Set.range Δ := by
    rintro d (rfl | rfl)
    · exact Set.mem_range_self a
    · exact Set.mem_range_self b
  have hnot : Δ i ∉ ({Δ a, Δ b} : Set (Subgroup W)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact hi_a (hinj h)
    · exact hi_b (hinj h)
  have h := hind.disjoint_sSup (Set.mem_range_self i) hsub hnot
  rw [sSup_pair] at h
  exact h.symm

theorem s16h_dc_fixed_of_rank {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {t : MulAut W} (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    {Δ : Fin 3 → Subgroup W} (hinj : Function.Injective Δ) (hind : sSupIndep (Set.range Δ))
    (hrk : ∀ i, rk ↥(Δ i) = 3) {π : Equiv.Perm (Fin 3)} (hπ : π.IsSwap)
    (hact : ∀ i, (Δ i).map t.toMonoidHom = Δ (π i)) :
    ∀ i, π i = i → ∀ x ∈ Δ i, t x = x := by
  intro i hi x hx
  by_contra htx
  obtain ⟨a, b, hab, hπeq⟩ := hπ
  have hia : i ≠ a := by
    rintro rfl
    rw [hπeq, Equiv.swap_apply_left] at hi
    exact hab hi.symm
  have hib : i ≠ b := by
    rintro rfl
    rw [hπeq, Equiv.swap_apply_right] at hi
    exact hab hi
  have hπa : π a = b := by rw [hπeq, Equiv.swap_apply_left]
  have hπb : π b = a := by rw [hπeq, Equiv.swap_apply_right]
  have hmapa : (Δ a).map t.toMonoidHom = Δ b := by rw [hact a, hπa]
  have hmapb : (Δ b).map t.toMonoidHom = Δ a := by rw [hact b, hπb]
  have hmapi : (Δ i).map t.toMonoidHom = Δ i := by rw [hact i, hi]
  set z : W := x * (t x)⁻¹ with hz_def
  have hz_ne : z ≠ 1 := by
    intro h
    rw [hz_def] at h
    exact htx (mul_inv_eq_one.mp h).symm
  have hz_comm : z ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := by
    have hgen : t x * x⁻¹ ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, x, Subgroup.mem_top x, rfl⟩
    have hz_eq : z = (t x * x⁻¹)⁻¹ := by rw [hz_def, mul_inv_rev, inv_inv]
    rw [hz_eq]
    exact (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)).inv_mem hgen
  have htx_mem : t x ∈ Δ i := by
    have h1 : t.toMonoidHom x ∈ (Δ i).map t.toMonoidHom :=
      Subgroup.mem_map_of_mem t.toMonoidHom hx
    rw [hmapi] at h1
    simpa using h1
  have hz_mem : z ∈ Δ i := by
    rw [hz_def]
    exact (Δ i).mul_mem hx ((Δ i).inv_mem htx_mem)
  let Z : Subgroup W := Subgroup.zpowers z
  have hZ_le_Di : Z ≤ Δ i := Subgroup.zpowers_le.mpr hz_mem
  have hZ_le_comm : Z ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) :=
    Subgroup.zpowers_le.mpr hz_comm
  have hZcard : Nat.card ↥Z = 2 := by
    show Nat.card ↥(Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (hW z) hz_ne
  have hZ_rk : rk ↥Z = 1 := by
    unfold rk
    rw [hZcard]
    simpa using (padicValNat.prime_pow (p := 2) (n := 1))
  let φ : W →* W := s16h_dc_commHom t
  let I : Subgroup W := (Δ a).map φ
  have hφ_ker : ∀ y ∈ Δ a, φ y = 1 → y = 1 := by
    intro y hy hy1
    have hty : t y = y := by
      have h2 : t y * y⁻¹ = 1 := by
        rw [← s16h_dc_commHom_apply t y]
        exact hy1
      exact mul_inv_eq_one.mp h2
    have hty_mem : t y ∈ Δ b := by
      have h1 : t.toMonoidHom y ∈ (Δ a).map t.toMonoidHom :=
        Subgroup.mem_map_of_mem t.toMonoidHom hy
      rw [hmapa] at h1
      simpa using h1
    have hy_inf : y ∈ Δ a ⊓ Δ b := ⟨hy, hty ▸ hty_mem⟩
    have hbot : Δ a ⊓ Δ b = ⊥ := disjoint_iff.mp (s16h_dc_disjoint_pair hinj hind hab)
    rw [hbot] at hy_inf
    exact Subgroup.mem_bot.mp hy_inf
  have hφ_injOn : Set.InjOn φ (Δ a : Set W) := by
    intro y hy y' hy' h
    have hmem : y * y'⁻¹ ∈ Δ a := (Δ a).mul_mem hy ((Δ a).inv_mem hy')
    have h1 : φ (y * y'⁻¹) = 1 := by
      rw [map_mul, h, map_inv, mul_inv_cancel]
    have h2 : y * y'⁻¹ = 1 := hφ_ker (y * y'⁻¹) hmem h1
    exact mul_inv_eq_one.mp h2
  have hI_card : Nat.card ↥I = Nat.card ↥(Δ a) := by
    have h := Nat.card_image_of_injOn hφ_injOn
    have hIset : (I : Set W) = φ '' (Δ a : Set W) := by
      change ((Δ a).map φ : Set W) = φ '' (Δ a : Set W)
      exact Subgroup.coe_map φ (Δ a)
    have h' : Nat.card (I : Set W) = Nat.card (Δ a : Set W) := by
      rw [hIset]
      exact h
    exact h'
  have hI_rk : rk ↥I = 3 := by
    unfold rk
    rw [hI_card, card_eq_two_pow hW (Δ a), hrk a]
    simpa using (padicValNat.prime_pow (p := 2) (n := 3))
  have hI_le_comm : I ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := by
    intro y hy
    change y ∈ (Δ a).map φ at hy
    rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
    show t y' * y'⁻¹ ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t)
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, y', Subgroup.mem_top y', rfl⟩
  have hI_le_sup : I ≤ Δ a ⊔ Δ b := by
    intro y hy
    change y ∈ (Δ a).map φ at hy
    rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
    have h1 : t.toMonoidHom y' ∈ (Δ a).map t.toMonoidHom :=
      Subgroup.mem_map_of_mem t.toMonoidHom hy'
    rw [hmapa] at h1
    have h1' : t y' ∈ Δ b := by simpa using h1
    show t y' * y'⁻¹ ∈ Δ a ⊔ Δ b
    exact (Δ a ⊔ Δ b).mul_mem (Subgroup.mem_sup_right h1')
      (Subgroup.mem_sup_left ((Δ a).inv_mem hy'))
  have hIZ_bot : I ⊓ Z = ⊥ := by
    have hIZ_le : I ⊓ Z ≤ (Δ a ⊔ Δ b) ⊓ Δ i := inf_le_inf hI_le_sup hZ_le_Di
    have hbot : (Δ a ⊔ Δ b) ⊓ Δ i = ⊥ :=
      disjoint_iff.mp (s16h_dc_disjoint_third hinj hind hia hib)
    exact le_bot_iff.mp (hbot ▸ hIZ_le)
  have hrkIZ : rk ↥(I ⊓ Z) = 0 := by rw [hIZ_bot, rk_bot]
  have hsup_rk : rk ↥(I ⊔ Z) = 4 := by
    have h := rk_sup_add_rk_inf I Z
    rw [hI_rk, hZ_rk, hrkIZ] at h
    omega
  have hle : I ⊔ Z ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) :=
    sup_le hI_le_comm hZ_le_comm
  have hfin := rk_mono hle
  rw [hsup_rk] at hfin
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
