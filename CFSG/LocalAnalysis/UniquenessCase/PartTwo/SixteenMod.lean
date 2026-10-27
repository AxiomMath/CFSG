module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s16_Mod_exists_involution_transvection {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} (hA : A ≠ ⊥) (hm : E3.mParam A = 1) :
    ∃ t ∈ A, orderOf t = 2 ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 1 := by
  by_cases hev : Even (Nat.card ↥A)
  · unfold E3.mParam at hm
    rw [if_pos hev] at hm
    set S : Set ℕ :=
      {n : ℕ | ∃ t ∈ A, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} with hS
    have hne : S.Nonempty := by
      rcases Set.eq_empty_or_nonempty S with h | h
      · rw [h, Nat.sInf_empty] at hm
        omega
      · exact h
    have hmem := Nat.sInf_mem hne
    rw [hS] at hmem
    obtain ⟨t, htA, ht2, hteq⟩ := hmem
    refine ⟨t, htA, ht2, ?_⟩
    rw [← commV_eq_commSub, ← rkIdx_fixV_zpowers t, ← hteq, hm]
  · unfold E3.mParam at hm
    rw [if_neg hev] at hm
    have hcard : Nat.card W = 2 := by
      rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW), hm, pow_one]
    obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
    have hone : (1 : W) = x ∨ (1 : W) = y := by
      have h1 : (1 : W) ∈ ({x, y} : Set W) := by
        rw [huniv]
        exact Set.mem_univ 1
      simpa using h1
    have hsingle : ∀ a b : W, a ≠ 1 → b ≠ 1 → a = b := by
      intro a b ha hb
      have ham : a = x ∨ a = y := by
        have h1 : a ∈ ({x, y} : Set W) := by
          rw [huniv]
          exact Set.mem_univ a
        simpa using h1
      have hbm : b = x ∨ b = y := by
        have h1 : b ∈ ({x, y} : Set W) := by
          rw [huniv]
          exact Set.mem_univ b
        simpa using h1
      rcases ham with rfl | rfl <;> rcases hbm with rfl | rfl
      · rfl
      · rcases hone with h1 | h1
        · exact absurd h1.symm ha
        · exact absurd h1.symm hb
      · rcases hone with h1 | h1
        · exact absurd h1.symm hb
        · exact absurd h1.symm ha
      · rfl
    have htriv : ∀ φ : MulAut W, φ = 1 := by
      intro φ
      ext w
      by_cases hw : w = 1
      · subst hw
        simp
      · have hφw : φ w ≠ 1 := by
          intro h
          apply hw
          exact φ.injective (h.trans (map_one φ).symm)
        exact (hsingle w (φ w) hw hφw).symm
    exfalso
    apply hA
    rw [Subgroup.eq_bot_iff_forall]
    intro t _
    exact htriv t

theorem s16_Mod_commSub_zpowers_map {W W' : Type} [CommGroup W] [CommGroup W'] (π : W →* W')
    (hπ : Function.Surjective π) {t : MulAut W} {t' : MulAut W'}
    (h : ∀ w, π (t w) = t' (π w)) :
    commSub ⊤ (Subgroup.zpowers t') = (commSub ⊤ (Subgroup.zpowers t)).map π := by
  have hinv : ∀ w : W, π (t⁻¹ w) = t'⁻¹ (π w) := by
    intro w
    have h1 := h (t⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    calc π (t⁻¹ w) = t'⁻¹ (t' (π (t⁻¹ w))) := by simp
      _ = t'⁻¹ (π w) := by rw [← h1]
  have hpow : ∀ (k : ℤ) (w : W), π ((t ^ k) w) = (t' ^ k) (π w) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [zpow_add_one, MulAut.mul_apply, ih (t w), h w, zpow_add_one, MulAut.mul_apply]
    | pred n ih =>
      intro w
      rw [zpow_sub_one, MulAut.mul_apply, ih (t⁻¹ w), hinv w, zpow_sub_one,
        MulAut.mul_apply]
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, -, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨w₀, rfl⟩ := hπ w
    refine ⟨(t ^ k) w₀ * w₀⁻¹,
      ⟨t ^ k, Subgroup.zpow_mem_zpowers t k, w₀, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, hpow]
  · rintro ⟨c₀, ⟨x, hx, w, -, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨t' ^ k, Subgroup.zpow_mem_zpowers t' k, π w, Subgroup.mem_top _,
      by simp only [map_mul, map_inv, hpow]⟩

private lemma s16_Mod_stabSub_map {W : Type} [CommGroup W] (e t : MulAut W)
    (U : Subgroup W) :
    t ∈ stabSub (U.map e.toMonoidHom) ↔ (e⁻¹ * t * e) ∈ stabSub U := by
  rw [mem_stabSub, mem_stabSub]
  constructor
  · intro h u
    have h1 := h (e u)
    rw [Subgroup.mem_map_equiv] at h1
    simpa [MulAut.mul_apply, MulAut.coe_inv] using h1
  · intro h v
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have h1 := h (e.symm v)
    simpa [MulAut.mul_apply, MulAut.coe_inv] using h1

private lemma s16_Mod_commSub_map {W : Type} [CommGroup W] (e t : MulAut W)
    (U : Subgroup W) :
    commSub (U.map e.toMonoidHom) (Subgroup.zpowers t) =
      (commSub U (Subgroup.zpowers (e⁻¹ * t * e))).map e.toMonoidHom := by
  have hpow : ∀ (k : ℤ) (u : W),
      e.toMonoidHom (((e⁻¹ * t * e) ^ k) u) = (t ^ k) (e u) := by
    intro k u
    have hconj : (e⁻¹ * t * e) ^ k = e⁻¹ * t ^ k * e := by
      have h1 : e⁻¹ * t * e = e⁻¹ * t * (e⁻¹)⁻¹ := by rw [inv_inv]
      rw [h1]
      exact conj_zpow
    rw [hconj]
    simp [MulAut.mul_apply]
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨((e⁻¹ * t * e) ^ k) u * u⁻¹,
      ⟨(e⁻¹ * t * e) ^ k, Subgroup.zpow_mem_zpowers (e⁻¹ * t * e) k, u, hu, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, hpow]
    rfl
  · rintro ⟨c₀, ⟨x, hx, u, hu, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨t ^ k, Subgroup.zpow_mem_zpowers t k, e u,
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, by
        simp only [map_mul, map_inv, hpow]
        rfl⟩

private lemma s16_Mod_rk_commSub_map {W : Type} [CommGroup W] (e t : MulAut W)
    (U : Subgroup W) :
    rk ↥(commSub (U.map e.toMonoidHom) (Subgroup.zpowers t)) =
      rk ↥(commSub U (Subgroup.zpowers (e⁻¹ * t * e))) := by
  rw [s16_Mod_commSub_map e t U]
  unfold rk
  rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem s16_Mod_inducesTransvection_conj {W : Type} [CommGroup W] (e t : MulAut W)
    (U : Subgroup W) :
    InducesTransvection t (U.map e.toMonoidHom) ↔ InducesTransvection (e⁻¹ * t * e) U := by
  unfold InducesTransvection
  rw [s16_Mod_stabSub_map e t U, s16_Mod_rk_commSub_map e t U]

theorem s16_Mod_transvection_summand {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {S : Set (Subgroup W)} (hind : sSupIndep S) (hspan : sSup S = ⊤)
    (hrk : ∀ X ∈ S, 2 ≤ rk ↥X) {t : MulAut W} (hperm : ∀ X ∈ S, X.map t.toMonoidHom ∈ S)
    (ht : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 1) :
    ∃ X ∈ S, InducesTransvection t X := by
  classical
  have hfix : ∀ X ∈ S, X.map t.toMonoidHom = X := by
    intro X hX
    set Y := X.map t.toMonoidHom with hYdef
    have hY : Y ∈ S := by
      rw [hYdef]
      exact hperm X hX
    by_contra hYX
    have hXY : X ⊓ Y = ⊥ := by
      have hd : Disjoint X (sSup (S \ {X})) := hind hX
      have hmem : Y ∈ S \ {X} := by
        rw [Set.mem_sdiff, Set.mem_singleton_iff]
        exact ⟨hY, hYX⟩
      have hle : Y ≤ sSup (S \ {X}) := le_sSup hmem
      exact disjoint_iff.mp (hd.mono_right hle)
    have hker : X ⊓ (commHom t).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      rw [Subgroup.mem_inf, ker_commHom] at hu
      obtain ⟨huX, hufix⟩ := hu
      have htu : t u = u := mem_fixV_zpowers_iff.mp hufix
      have huY : u ∈ Y := by
        rw [hYdef]
        exact Subgroup.mem_map.mpr ⟨u, huX, by simpa using htu⟩
      have huXY : u ∈ X ⊓ Y := ⟨huX, huY⟩
      rw [hXY, Subgroup.mem_bot] at huXY
      exact huXY
    have htot := rk_map_add_rk_inf_ker (commHom t) X
    rw [hker, rk_bot, add_zero] at htot
    have hrkX : 2 ≤ rk ↥(X.map (commHom t)) := by
      rw [htot]
      exact hrk X hX
    have hle : X.map (commHom t) ≤ commSub ⊤ (Subgroup.zpowers t) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [commHom_apply]
      exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, x, Subgroup.mem_top x, rfl⟩
    have hle2 : rk ↥(X.map (commHom t)) ≤
        rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono hle
    rw [ht] at hle2
    omega
  have hex : ∃ X ∈ S, commSub X (Subgroup.zpowers t) ≠ ⊥ := by
    by_contra hcon
    have hle : sSup S ≤ fixV (Subgroup.zpowers t) := by
      refine sSup_le fun X hX => ?_
      rw [← commSub_eq_bot_iff]
      by_contra hne
      exact hcon ⟨X, hX, hne⟩
    rw [hspan] at hle
    have htop : fixV (Subgroup.zpowers t) = ⊤ := le_antisymm le_top hle
    have hbot : commSub ⊤ (Subgroup.zpowers t) = ⊥ := by
      rw [commSub_eq_bot_iff, htop]
    rw [hbot, rk_bot] at ht
    omega
  obtain ⟨X, hX, hne⟩ := hex
  refine ⟨X, hX, ?_⟩
  unfold InducesTransvection
  constructor
  · rw [mem_stabSub]
    intro u
    have hXmap : X.map t.toMonoidHom = X := hfix X hX
    constructor
    · intro hu
      have hmem : t u ∈ X.map t.toMonoidHom := by
        rw [hXmap]
        exact hu
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
      have hxu : x = u := t.injective (by simpa using hxeq)
      rwa [← hxu]
    · intro hu
      rw [← hXmap]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · have hle : commSub X (Subgroup.zpowers t) ≤ commSub ⊤ (Subgroup.zpowers t) :=
      commSub_mono le_top le_rfl
    have hle1 : rk ↥(commSub X (Subgroup.zpowers t)) ≤ 1 := by
      have h1 := rk_mono hle
      rw [ht] at h1
      exact h1
    have hpos : 0 < rk ↥(commSub X (Subgroup.zpowers t)) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hne ((rk_eq_zero_iff hW).mp h0)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
