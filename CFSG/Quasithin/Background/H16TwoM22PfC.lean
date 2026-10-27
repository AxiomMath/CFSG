module

public import CFSG.Quasithin.Background.H16TwoM22PfB
public import CFSG.Quasithin.Background.H16TwoM22PfA

public section

namespace CFSG.Quasithin.H.Mathieu.H16Pf

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Open Pointwise

theorem smul_eq_of_maps {m : Equiv.Perm (Fin 24)} {S : Finset (Fin 24)}
    (h : ∀ y ∈ S, m y ∈ S) : m • S = S := by
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (Finset.card_smul_finset m S).ge
  obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
  exact h y hy

theorem mem_maskSet_252 (i : Fin 24) : i ∈ maskSet 252 ↔ 2 ≤ (i : ℕ) ∧ (i : ℕ) < 8 := by
  rw [mem_maskSet]; revert i; decide

theorem mem_maskSet_192 (i : Fin 24) : i ∈ maskSet 192 ↔ 6 ≤ (i : ℕ) ∧ (i : ℕ) < 8 := by
  rw [mem_maskSet]; revert i; decide

theorem mem_maskSet_60 (i : Fin 24) : i ∈ maskSet 60 ↔ 2 ≤ (i : ℕ) ∧ (i : ℕ) < 6 := by
  rw [mem_maskSet]; revert i; decide

theorem dPerm_two : ∀ x : Fin 24, 2 ≤ (x : ℕ) → (x : ℕ) < 6 → ∃ j : Fin 8, dPerm j 2 = x := by
  decide +kernel

theorem dPerm_six : ∀ x : Fin 24, 6 ≤ (x : ℕ) → (x : ℕ) < 8 → ∃ j : Fin 8, dPerm j 6 = x := by
  decide +kernel

theorem card_le_stab {M : Subgroup (Equiv.Perm (Fin 24))} (hM : M ≤ mog22) {S : Finset (Fin 24)}
    (hS : ∀ m ∈ M, m • S = S) :
    Nat.card M ≤ Nat.card (MulAction.stabilizer ↥mog22 S) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv]
  exact Subgroup.card_le_of_le fun m hm => hS _ hm

section Orbits


theorem card_stab_lt {m₀ : ℕ} (hm : m₀ = 192 ∨ m₀ = 60) :
    Nat.card (MulAction.stabilizer ↥mog22 (maskSet m₀)) < 5760 := by
  obtain ⟨-, h2, h3, -, h5, h6, -, h8, h9, -, h11, h12⟩ := bfs_checks
  rcases hm with rfl | rfl
  · have := card_stab_mul_le h3 h6 h9
    rw [h12] at this
    omega
  · have := card_stab_mul_le h2 h5 h8
    rw [h11] at this
    omega

theorem card_stab_hexad_le : Nat.card (MulAction.stabilizer ↥mog22 (maskSet 252)) ≤ 5760 := by
  obtain ⟨h1, -, -, h4, -, -, h7, -, -, h10, -, -⟩ := bfs_checks
  have := card_stab_mul_le h1 h4 h7
  rw [h10] at this
  omega

theorem le_stab_hexad {M : Subgroup (Equiv.Perm (Fin 24))} (hM : M ≤ mog22) (hP : PO ≤ M)
    (hc : Nat.card M = 5760) : ∀ m ∈ M, m • maskSet 252 = maskSet 252 := by
  have h01 : ∀ m ∈ M, ∀ y : Fin 24, (y : ℕ) < 2 → m y = y := by
    intro m hm y hy
    obtain ⟨⟨-, h0⟩, h1⟩ := hM hm
    rcases (by omega : (y : ℕ) = 0 ∨ (y : ℕ) = 1) with h | h
    · rw [show y = 0 from Fin.ext h]; exact (mem_stab_iff 0 m).1 h0
    · rw [show y = 1 from Fin.ext h]; exact (mem_stab_iff 1 m).1 h1
  have h2' : ∀ m ∈ M, ∀ y : Fin 24, 2 ≤ (y : ℕ) → 2 ≤ ((m y : Fin 24) : ℕ) := by
    intro m hm y hy
    by_contra h
    have := h01 m hm (m y) (by omega)
    exact absurd (m.injective this) (fun e => by rw [e] at h; omega)
  let R : Fin 24 → Fin 24 → Prop := fun x y => ∃ m ∈ M, m x = y
  have Rsymm : ∀ {x y}, R x y → R y x := fun ⟨m, hm, h⟩ =>
    ⟨m⁻¹, M.inv_mem hm, by rw [← h]; exact m.symm_apply_apply _⟩
  have Rtrans : ∀ {x y z}, R x y → R y z → R x z := fun ⟨m, hm, h⟩ ⟨m', hm', h'⟩ =>
    ⟨m' * m, M.mul_mem hm' hm, by rw [Equiv.Perm.mul_apply, h, h']⟩
  have R8 : ∀ y : Fin 24, 8 ≤ (y : ℕ) → R 8 y := fun y hy =>
    ⟨koPerm ⟨y - 8, by omega⟩, hP (koPerm_mem_PO _),
      Fin.ext (by rw [koPerm_eight]; dsimp only; omega)⟩
  have R2 : ∀ y : Fin 24, 2 ≤ (y : ℕ) → (y : ℕ) < 6 → R 2 y := fun y h1 h2 => by
    obtain ⟨j, hj⟩ := dPerm_two y h1 h2
    exact ⟨dPerm j, hP (dPerm_mem_PO j), hj⟩
  have R6 : ∀ y : Fin 24, 6 ≤ (y : ℕ) → (y : ℕ) < 8 → R 6 y := fun y h1 h2 => by
    obtain ⟨j, hj⟩ := dPerm_six y h1 h2
    exact ⟨dPerm j, hP (dPerm_mem_PO j), hj⟩
  have hcls : ∀ x y : Fin 24, 2 ≤ (y : ℕ) → R x y →
      (8 ≤ (y : ℕ) → R x 8) ∧ ((y : ℕ) < 6 → R x 2) ∧ (6 ≤ (y : ℕ) → (y : ℕ) < 8 → R x 6) :=
    fun x y _ hxy => ⟨fun h => Rtrans hxy (Rsymm (R8 y h)),
      fun h => Rtrans hxy (Rsymm (R2 y (by omega) h)),
      fun h h' => Rtrans hxy (Rsymm (R6 y h h'))⟩
  by_cases hA : R 8 2 <;> by_cases hB : R 8 6
  ·
    exfalso
    have horb : MulAction.orbit ↥M (8 : Fin 24) = {y : Fin 24 | 2 ≤ (y : ℕ)} := by
      ext y
      constructor
      · rintro ⟨⟨m, hm⟩, rfl⟩
        exact h2' m hm 8 (by decide)
      · intro hy
        obtain ⟨m, hm, hmy⟩ : R 8 y := by
          by_cases h8 : 8 ≤ (y : ℕ)
          · exact R8 y h8
          by_cases h6 : (y : ℕ) < 6
          · exact Rtrans hA (R2 y hy h6)
          · exact Rtrans hB (R6 y (by omega) (by omega))
        exact ⟨⟨m, hm⟩, hmy⟩
    have h22 : (MulAction.orbit ↥M (8 : Fin 24)).ncard = 22 := by
      rw [horb, Set.ncard_eq_toFinset_card']
      decide
    have hdvd := (MulAction.stabilizer ↥M (8 : Fin 24)).index_dvd_card
    rw [MulAction.index_stabilizer, h22, hc] at hdvd
    exact absurd hdvd (by decide)
  ·
    exfalso
    have hS : ∀ m ∈ M, m • maskSet 192 = maskSet 192 := fun m hm => smul_eq_of_maps fun y hy => by
      rw [mem_maskSet_192] at hy ⊢
      have hmy := h2' m hm y (by omega)
      have hR : R y (m y) := ⟨m, hm, rfl⟩
      obtain ⟨c1, c2, -⟩ := hcls y (m y) hmy hR
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hB (Rtrans hA (Rsymm (Rtrans (R6 y hy.1 hy.2) (c2 (by omega)))))
      · by_contra h
        exact hB (Rsymm (Rtrans (R6 y hy.1 hy.2) (c1 (by omega))))
    have := (card_le_stab hM hS).trans_lt (card_stab_lt (Or.inl rfl))
    omega
  ·
    exfalso
    have hS : ∀ m ∈ M, m • maskSet 60 = maskSet 60 := fun m hm => smul_eq_of_maps fun y hy => by
      rw [mem_maskSet_60] at hy ⊢
      have hmy := h2' m hm y hy.1
      have hR : R y (m y) := ⟨m, hm, rfl⟩
      obtain ⟨c1, -, c3⟩ := hcls y (m y) hmy hR
      refine ⟨hmy, ?_⟩
      by_contra h
      by_cases h8 : 8 ≤ ((m y : Fin 24) : ℕ)
      · exact hA (Rsymm (Rtrans (R2 y hy.1 hy.2) (c1 h8)))
      · exact hA (Rtrans hB (Rsymm (Rtrans (R2 y hy.1 hy.2) (c3 (by omega) (by omega)))))
    have := (card_le_stab hM hS).trans_lt (card_stab_lt (Or.inr rfl))
    omega
  ·
    intro m hm
    have hbig : ∀ m ∈ M, ∀ y : Fin 24, 8 ≤ (y : ℕ) → 8 ≤ ((m y : Fin 24) : ℕ) := by
      intro m hm y hy
      by_contra h
      have hR : R 8 (m y) := Rtrans (R8 y hy) ⟨m, hm, rfl⟩
      obtain ⟨-, c2, c3⟩ := hcls 8 (m y) (h2' m hm y (by omega)) hR
      by_cases h6 : ((m y : Fin 24) : ℕ) < 6
      · exact hA (c2 h6)
      · exact hB (c3 (by omega) (by omega))
    refine smul_eq_of_maps fun y hy => ?_
    rw [mem_maskSet_252] at hy ⊢
    refine ⟨h2' m hm y hy.1, ?_⟩
    by_contra h
    have := hbig m⁻¹ (M.inv_mem hm) (m y) (by omega)
    rw [show m⁻¹ (m y) = y from m.symm_apply_apply y] at this
    omega

end Orbits

@[expose] def fixW10 (R : Subgroup (Equiv.Perm (Fin 24))) : Set W10 :=
  {w | ∀ x (hx : x ∈ R ⊓ mog22), rhoC10 mog22 mog22_le_mog22plus ⟨x, hx.2⟩ w = w}

theorem preserves_O {m : Equiv.Perm (Fin 24)} (h0 : m 0 = 0) (h1 : m 1 = 1)
    (hS : m • maskSet 252 = maskSet 252) (i : Fin 24) :
    ((m i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  have hin : ∀ j : Fin 24, (j : ℕ) < 8 → ((m j : Fin 24) : ℕ) < 8 := by
    intro j hj
    by_cases h2 : (j : ℕ) < 2
    · rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h | h
      · rw [show j = 0 from Fin.ext h, h0]; decide
      · rw [show j = 1 from Fin.ext h, h1]; decide
    · have hj' : j ∈ maskSet 252 := (mem_maskSet_252 j).2 ⟨by omega, hj⟩
      have : m j ∈ m • maskSet 252 := Finset.smul_mem_smul_finset hj'
      rw [hS, mem_maskSet_252] at this
      exact this.2
  refine ⟨fun h => ?_, hin i⟩
  by_contra hi
  set T := Finset.univ.filter fun j : Fin 24 => (j : ℕ) < 8
  have hsub : T.image m ⊆ T := fun y hy => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hin j hj
  have heq := Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injective _ m.injective).ge
  have hmi : m i ∈ T.image m := by
    rw [heq]; simpa [T] using h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hmi
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [m.injective hji] at hj
  exact hi hj

theorem fix_of_conj (g : ↥mog22) {k : Equiv.Perm (Fin 24)} (hk : k ∈ mog22) {w : W10}
    (h : (g : Equiv.Perm (Fin 24)) * k * (g : Equiv.Perm (Fin 24))⁻¹ ∈ mog22)
    (hw : rhoC10 mog22 mog22_le_mog22plus ⟨_, h⟩ w = w) :
    rhoC10 mog22 mog22_le_mog22plus ⟨k, hk⟩ ((rhoC10 mog22 mog22_le_mog22plus g)⁻¹ w) =
      (rhoC10 mog22 mog22_le_mog22plus g)⁻¹ w := by
  have he : (⟨_, h⟩ : ↥mog22) = g * ⟨k, hk⟩ * g⁻¹ := Subtype.ext (by simp)
  rw [he, map_mul, map_mul, map_inv] at hw
  simp only [MulAut.mul_apply] at hw
  have h2 := congrArg (rhoC10 mog22 mog22_le_mog22plus g).symm hw
  rw [MulEquiv.symm_apply_apply] at h2
  simpa [MulAut.inv_def] using h2

section Fix


theorem fixW10_pCoreOf {N : Subgroup (Equiv.Perm (Fin 24))} (hN : N ≤ mog22)
    (hc : Nat.card N = 5760) : ∃ w₀ : W10, w₀ ≠ 1 ∧ fixW10 (pCoreOf 2 N) = {1, w₀} := by
  obtain ⟨g, hg, hgP⟩ := exists_conj_PO hN hc
  set M : Subgroup (Equiv.Perm (Fin 24)) := N.map (MulAut.conj g⁻¹).toMonoidHom
  have hMmem : ∀ x, x ∈ M ↔ g * x * g⁻¹ ∈ N := by
    intro x
    constructor
    · rintro ⟨n, hn, rfl⟩
      convert hn using 1
      simp [mul_assoc]
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  have hMle : M ≤ mog22 := fun x hx => by
    have h2 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h2]
    exact mog22.mul_mem (mog22.mul_mem (mog22.inv_mem hg) (hN ((hMmem x).1 hx))) hg
  have hcM : Nat.card M = 5760 := by
    rw [← hc]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hhex := le_stab_hexad hMle (fun x hx => (hMmem x).2 (hgP x hx)) hcM
  have hstab : M.subgroupOf mog22 = MulAction.stabilizer ↥mog22 (maskSet 252) := by
    refine Subgroup.eq_of_le_of_card_ge (fun m hm => hhex _ hm) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMle).toEquiv, hcM]
    exact card_stab_hexad_le
  have hKM : fixO ≤ M := by
    intro k hk
    have : (⟨k, fixO_le_mog22 hk⟩ : ↥mog22) ∈ M.subgroupOf mog22 := by
      rw [hstab]
      refine smul_eq_of_maps fun y hy => ?_
      rw [hk.2 y ((mem_maskSet_252 y).1 hy).2]
      exact hy
    exact this
  have hMnorm : ∀ m ∈ M, m ∈ Subgroup.normalizer (fixO : Set (Equiv.Perm (Fin 24))) := by
    intro m hm
    obtain ⟨⟨hA, h0⟩, h1⟩ := hMle hm
    exact mem_normalizer_fixO hA (preserves_O ((mem_stab_iff 0 m).1 h0)
      ((mem_stab_iff 1 m).1 h1) (hhex m hm))
  set K' := fixO.map (MulAut.conj g).toMonoidHom
  have hK'N : K' ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    exact (hMmem k).1 (hKM hk)
  have hK'norm : N ≤ Subgroup.normalizer (K' : Set (Equiv.Perm (Fin 24))) := by
    intro n hn
    have hm : g⁻¹ * n * g ∈ M := (hMmem _).2 (by simpa [mul_assoc] using hn)
    have hmn := Subgroup.mem_normalizer_iff.1 (hMnorm _ hm)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨_, (hmn k).1 hk, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨k, hk, hkh⟩
      refine ⟨g⁻¹ * h * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      refine (hmn _).2 ?_
      have : g⁻¹ * n * g * (g⁻¹ * h * g) * (g⁻¹ * n * g)⁻¹ = k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkh
        rw [show g⁻¹ * n * g * (g⁻¹ * h * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * h * n⁻¹) * g by
          group, ← hkh]
        group
      rw [this]
      exact hk
  have hK'core : K' ≤ pCoreOf 2 N := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hK'N
    hK'norm (isPGroup_fixO.map _)
  set ρ := rhoC10 mog22 mog22_le_mog22plus
  set gg : ↥mog22 := ⟨g, hg⟩
  set w₀ := ρ gg (toW 10 1)
  have hsub : fixW10 (pCoreOf 2 N) ⊆ {1, w₀} := by
    intro w hw
    have key : ∀ t : Fin 16, koRho t ((ρ gg)⁻¹ w) = (ρ gg)⁻¹ w := by
      intro t
      have hx : g * koPerm t * g⁻¹ ∈ pCoreOf 2 N ⊓ mog22 :=
        ⟨hK'core ⟨_, (mem_fixO_iff _).2 ⟨t, rfl⟩, rfl⟩,
          mog22.mul_mem (mog22.mul_mem hg (koPerm_mem_mog22 t)) (mog22.inv_mem hg)⟩
      exact fix_of_conj gg (koPerm_mem_mog22 t) hx.2 (hw _ hx)
    rcases (fix_koRho _).1 ⟨key 1, key 2, key 4, key 8⟩ with h | h
    · left
      rw [← (ρ gg).apply_symm_apply w]
      simp only [MulAut.inv_def] at h
      rw [h, map_one]
    · right
      rw [← (ρ gg).apply_symm_apply w]
      simp only [MulAut.inv_def] at h
      rw [h]
      exact Set.mem_singleton _
  have hone : (1 : W10) ∈ fixW10 (pCoreOf 2 N) := fun x hx => map_one _
  let φ : ↥(pCoreOf 2 N) →* MulAut W10 :=
    ρ.comp (Subgroup.inclusion ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hN))
  let _ : MulAction ↥(pCoreOf 2 N) W10 := MulAction.compHom W10 φ
  have hdvd : 2 ∣ Nat.card W10 := by
    rw [Nat.card_congr (Multiplicative.toAdd : W10 ≃ (Fin 10 → ZMod 2)), Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 (by norm_num)
  have hfix1 : (1 : W10) ∈ MulAction.fixedPoints ↥(pCoreOf 2 N) W10 := fun r => map_one (φ r)
  obtain ⟨b, hb, hb1⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).of_equiv
    (MulEquiv.refl _) |>.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hdvd hfix1
  have hbF : b ∈ fixW10 (pCoreOf 2 N) := fun x hx => hb ⟨x, hx.1⟩
  have hbw : b = w₀ := by
    rcases hsub hbF with h | h
    · exact absurd h.symm hb1
    · exact h
  refine ⟨w₀, hbw ▸ Ne.symm hb1, Set.Subset.antisymm hsub ?_⟩
  rintro w (rfl | rfl)
  · exact hone
  · exact hbw ▸ hbF

end Fix

end CFSG.Quasithin.H.Mathieu.H16Pf
