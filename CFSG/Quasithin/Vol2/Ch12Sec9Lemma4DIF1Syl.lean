module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Flags

public section

namespace CFSG.Quasithin.H13.C1294

open Module MulAction

theorem natCard_GL_four {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (hI : finrank (ZMod 2) I = 4) : Nat.card (I ≃ₗ[ZMod 2] I) = 20160 := by
  have hV : finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : V4 ≃ₗ[ZMod 2] I := LinearEquiv.ofFinrankEq V4 I (by rw [hV, hI])
  rw [← Nat.card_congr (Equiv.ofBijective (PsiE e) (PsiE_bijective e))]
  rw [Matrix.card_SL_field, ZMod.card]
  decide

theorem natCard_of_index_315 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hG : Nat.card G = 20160) (hH : H.index = 315) : Nat.card H = 64 := by
  have h := Subgroup.card_mul_index (H := H)
  rw [hH, hG] at h
  omega

theorem natCard_of_two_group_odd_index {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hG : Nat.card G = 20160) (hH : IsPGroup 2 H) (hodd : ¬ 2 ∣ H.index) : Nat.card H = 64 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := H)).1 hH
  have h := Subgroup.card_mul_index (H := H)
  rw [hG, hn] at h
  have hn15 : n < 15 := by
    by_contra hc
    have hc : 15 ≤ n := by omega
    have h1 : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 2 ^ n ≤ 20160 := by
      have hidx : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have : 2 ^ n ≤ 2 ^ n * H.index := Nat.le_mul_of_pos_right _ hidx
      omega
    omega
  interval_cases n <;> omega

instance finite_linearEquiv_self {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I] :
    Finite (I ≃ₗ[ZMod 2] I) :=
  Finite.of_injective (fun f : I ≃ₗ[ZMod 2] I => (f : I → I)) DFunLike.coe_injective

theorem card_sylow_eq_64 {G : Type} [Group G] [Finite G] (hG : Nat.card G = 20160) {Q H : Subgroup G}
    (hQ : IsPGroup 2 Q) (hHQ : H ≤ Q) (hH : Nat.card H = 64) : Nat.card Q = 64 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).1 hQ
  have h1 : Nat.card Q ∣ 20160 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [hG] at this
  have h2 : 64 ∣ Nat.card Q := by
    have := Subgroup.card_dvd_of_le hHQ
    rwa [hH] at this
  rw [hm] at h1 h2
  have hm6 : m ≤ 6 := by
    by_contra hc
    have h7 : 2 ^ 7 ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
    have h8 := Nat.dvd_trans h7 h1
    norm_num at h8
  have hm6' : 6 ≤ m := by
    by_contra hc
    have hle : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2 ^ m := by positivity
    have h9 := Nat.le_of_dvd hpos h2
    norm_num at hle
    omega
  have hm6eq : m = 6 := by omega
  calc Nat.card Q = 2 ^ m := hm
    _ = 2 ^ 6 := by rw [hm6eq]
    _ = 64 := by norm_num

open scoped Pointwise in
theorem exists_conj_of_card_64 {G : Type} [Group G] [Finite G] (hG : Nat.card G = 20160)
    {H K : Subgroup G} (hH : IsPGroup 2 H) (hK : IsPGroup 2 K) (hHc : Nat.card H = 64)
    (hKc : Nat.card K = 64) : ∃ c : G, H = K.map (MulAut.conj c).toMonoidHom := by
  haveI : Finite (Sylow 2 G) :=
    Finite.of_injective (fun P : Sylow 2 G => (P : Set G))
      (fun P Q h => Sylow.ext (SetLike.coe_injective h))
  obtain ⟨QH, hHQ⟩ := IsPGroup.exists_le_sylow hH
  obtain ⟨QK, hKQ⟩ := IsPGroup.exists_le_sylow hK
  have eH : H = (QH : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hHQ
      (le_of_eq ((card_sylow_eq_64 hG QH.isPGroup' hHQ hHc).trans hHc.symm))
  have eK : K = (QK : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hKQ
      (le_of_eq ((card_sylow_eq_64 hG QK.isPGroup' hKQ hKc).trans hKc.symm))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G QK QH
  have hsm : MulAut.conj c • (QK : Subgroup G) =
      (QK : Subgroup G).map (MulAut.conj c).toMonoidHom := rfl
  refine ⟨c, ?_⟩
  rw [eH, eK, ← hc, Sylow.coe_subgroup_smul, hsm]

theorem conj_stabS {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (g : I ≃ₗ[ZMod 2] I)
    (S : Submodule (ZMod 2) I) :
    (stabS S).map (MulAut.conj g).toMonoidHom = stabS (S.map (g : I →ₗ[ZMod 2] I)) := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    show ∀ v, v ∈ S.map (g : I →ₗ[ZMod 2] I) ↔ x v ∈ S.map (g : I →ₗ[ZMod 2] I)
    intro v
    have hv := h (g.symm v)
    have e : (g⁻¹ * x * g) (g.symm v) = g.symm (x v) := by
      show g.symm (x (g (g.symm v))) = g.symm (x v)
      rw [LinearEquiv.apply_symm_apply]
    rw [e] at hv
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv]
    exact hv
  · intro h
    show ∀ w, w ∈ S ↔ (g⁻¹ * x * g) w ∈ S
    intro w
    have hw := h (g w)
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hw
    exact hw

theorem map_flagStab_conj {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (c : I ≃ₗ[ZMod 2] I)
    (p ℓ Pl : Submodule (ZMod 2) I) :
    (stabS p ⊓ stabS ℓ ⊓ stabS Pl : Subgroup (I ≃ₗ[ZMod 2] I)).map (MulAut.conj c).toMonoidHom =
      stabS (p.map (c : I →ₗ[ZMod 2] I)) ⊓ stabS (ℓ.map (c : I →ₗ[ZMod 2] I)) ⊓
        stabS (Pl.map (c : I →ₗ[ZMod 2] I)) := by
  rw [Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
    Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
    conj_stabS, conj_stabS, conj_stabS]

theorem flag_lt_of_le_finrank_ne {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    {X Y : Submodule (ZMod 2) I} (h : X ≤ Y)
    (hd : Module.finrank (ZMod 2) X ≠ Module.finrank (ZMod 2) Y) : X < Y :=
  lt_of_le_of_ne h fun e =>
    hd (congrArg (fun Z : Submodule (ZMod 2) I => Module.finrank (ZMod 2) Z) e)

theorem exists_std_flag {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (hI : Module.finrank (ZMod 2) I = 4) :
    ∃ p ℓ Pl : Submodule (ZMod 2) I, Module.finrank (ZMod 2) p = 1 ∧
      Module.finrank (ZMod 2) ℓ = 2 ∧ Module.finrank (ZMod 2) Pl = 3 ∧ p < ℓ ∧ ℓ < Pl := by
  have hV : Module.finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : V4 ≃ₗ[ZMod 2] I := LinearEquiv.ofFinrankEq V4 I (by rw [hV, hI])
  have hfin : ∀ k : ℕ, k ≤ 2 → Module.finrank (ZMod 2) (flagI e0 k) = k + 1 := fun k hk =>
    finrank_flagI e0 k hk
  have hmono : ∀ k k' : ℕ, k ≤ k' → flagI e0 k ≤ flagI e0 k' := fun k k' h =>
    Submodule.map_mono (Wc_le h)
  refine ⟨flagI e0 0, flagI e0 1, flagI e0 2, (hfin 0 (by norm_num)).trans (by norm_num),
    (hfin 1 (by norm_num)).trans (by norm_num), (hfin 2 (by norm_num)).trans (by norm_num),
    ?_, ?_⟩
  · exact flag_lt_of_le_finrank_ne (hmono 0 1 (by norm_num))
      (by rw [hfin 0 (by norm_num), hfin 1 (by norm_num)]; norm_num)
  · exact flag_lt_of_le_finrank_ne (hmono 1 2 (by norm_num))
      (by rw [hfin 1 (by norm_num), hfin 2 (by norm_num)]; norm_num)

theorem natCard_std_flag {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    {p ℓ Pl : Submodule (ZMod 2) I} (hI : Module.finrank (ZMod 2) I = 4)
    (hp : Module.finrank (ZMod 2) p = 1) (hℓ : Module.finrank (ZMod 2) ℓ = 2)
    (hPl : Module.finrank (ZMod 2) Pl = 3) (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    Nat.card (stabS p ⊓ stabS ℓ ⊓ stabS Pl : Subgroup (I ≃ₗ[ZMod 2] I)) = 64 :=
  natCard_of_index_315 (natCard_GL_four hI)
    (index_flag_values hI hp hℓ hPl hpℓ hℓPl).2.2.2.2.2.2

end CFSG.Quasithin.H13.C1294
