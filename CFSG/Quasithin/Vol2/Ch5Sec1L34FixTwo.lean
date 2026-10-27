module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsFin

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL fixed_of_unip
  exists_add_frobPow_ne_zero unipSL_mul_self)

variable {G : Type} [Group G]

theorem mem_normalizer_inf {T L : Subgroup G} {t : G} (htT : t ∈ T)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer htT) s
  have h2 := Subgroup.mem_normalizer_iff.mp htL s
  simp only [Subgroup.mem_inf]
  exact and_congr h1 h2

theorem pow_three_autHom {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    {d : G} (hdL : d ∈ L) (hd3 : orderOf d = 3) : autHom hLW ⟨d, hdL⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨d, hdL⟩ : ↥L) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hd3]
    exact pow_orderOf_eq_one d
  rw [this, map_one]

section Moving

variable [Finite G] {L T W : Subgroup G} {F : Type} [Field F] [Finite F]

theorem exists_moving {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (ψ : ↥(autOn L W) ≃* SL(2, F))
    (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn (T ⊓ L) W ↔ ∃ b : F, ψ x = unipSL b)
    {d : G} (hdL : d ∈ L)
    (hd10 : (ψ (autHom hLW ⟨d, hdL⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hdT : d ∉ Subgroup.normalizer (T : Set G)) :
    ∃ (t : G) (ht : t ∈ T) (h : SL(2, F)) (σ : RingAut F),
      (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (∀ y y' : ↥(autOn L W), (y' : MulAut ↥W) =
          conjAct W ⟨t, hTW ht⟩ * y * (conjAct W ⟨t, hTW ht⟩)⁻¹ →
        ψ y' = h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ y) * h⁻¹) ∧
      σ ((ψ (autHom hLW ⟨d, hdL⟩) : Matrix (Fin 2) (Fin 2) F) 0 0) ≠
        (ψ (autHom hLW ⟨d, hdL⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  by_contra hno
  apply hdT
  apply mem_normalizer_of_conj_mem
  intro t ht
  set xd := autHom hLW ⟨d, hdL⟩ with hxd
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  set τ : Subgroup.normalizer ((autOn L W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    ⟨conjAct W ⟨t, hTW ht⟩, conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩ (hTL ht)⟩ with hτ
  have hτP : (τ : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩ (mem_normalizer_inf ht (hTL ht))
  obtain ⟨h, σ, hh, hασ, -⟩ := exists_upper_of_normalizes hn hcard ψ hP τ hτP
  have hy' : ∀ y y' : ↥(autOn L W), (y' : MulAut ↥W) =
      conjAct W ⟨t, hTW ht⟩ * y * (conjAct W ⟨t, hTW ht⟩)⁻¹ →
        ψ y' = h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ y) * h⁻¹ := by
    intro y y' hyy'
    have : y' = (autOn L W).normalizerMonoidHom τ y := by
      apply Subtype.ext
      rw [hyy', Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this, hασ]
  have hfix : σ c = c := by
    by_contra hne
    exact hno ⟨t, ht, h, σ, hh, hy', hne⟩
  have htd : t * d * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL ht) d).mp hdL
  set xtd := autHom hLW ⟨t * d * t⁻¹, htd⟩ with hxtd
  have hxtd' : (xtd : MulAut ↥W) =
      conjAct W ⟨t, hTW ht⟩ * xd * (conjAct W ⟨t, hTW ht⟩)⁻¹ := by
    rw [hxtd, hxd]
    change conjAct W ⟨t * d * t⁻¹, _⟩ = conjAct W ⟨t, hTW ht⟩ * conjAct W ⟨d, _⟩ *
      (conjAct W ⟨t, hTW ht⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hψtd := hy' xd xtd hxtd'
  obtain ⟨e1, e2⟩ := upper_conj_map σ hh hd10
  rw [← hψtd] at e1 e2
  rw [← hc, hfix] at e2
  have hdet := upper_det e1
  obtain ⟨f1, f2⟩ := upper_inv e1
  obtain ⟨g1, g2⟩ := upper_mul hd10 f1
  have h00 : ((ψ xd * (ψ xtd)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [g2, f2, ← hc]
    rw [e2] at hdet
    exact hdet
  have hU := eq_unipSL_of_upper g1 h00
  have hmem : ((xd * xtd⁻¹ : ↥(autOn L W)) : MulAut ↥W) ∈ autOn (T ⊓ L) W :=
    (hP _).mpr ⟨((ψ xd * (ψ xtd)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1, by
      rw [map_mul, map_inv]
      exact hU⟩
  set u : Subgroup.normalizer (W : Set G) := ⟨d, hLW hdL⟩ * (⟨t * d * t⁻¹, hLW htd⟩)⁻¹ with hu
  have hu' : (u : G) = d * t * d⁻¹ * t⁻¹ := by
    rw [hu]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have huLT : (u : G) ∈ L ⊔ T := by
    rw [hu']
    have hdLT : d ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) hdL
    have htLT : t ∈ L ⊔ T := (le_sup_right : T ≤ L ⊔ T) ht
    exact mul_mem (mul_mem (mul_mem hdLT htLT) (inv_mem hdLT)) (inv_mem htLT)
  have hcu : conjAct W u = ((xd * xtd⁻¹ : ↥(autOn L W)) : MulAut ↥W) := by
    rw [hu, map_mul, map_inv]
    rfl
  have huT := mem_of_conjAct_mem_autOn hC u huLT (by rw [hcu]; exact hmem)
  rw [hu'] at huT
  have : d * t * d⁻¹ = (d * t * d⁻¹ * t⁻¹) * t := by group
  rw [this]
  exact mul_mem huT ht

end Moving

section Orth

variable [Finite G] {L T W : Subgroup G}

theorem card_fix_eq_two_orth {m : ℕ} {d : G} (hW : IsOrthCh5 L W (2 * m)) (hm : m = 2 ∨ m = 4)
    (hT : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hS : IsSylowTwoOf (T ⊓ L) L)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T)
    (hd : d ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) (hd3 : orderOf d = 3)
    (hdT : d ∉ Subgroup.normalizer (T : Set G)) :
    Nat.card ↥(W ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint, hP⟩ := hW.exists_sylowCoord hS
  have := Fintype.ofFinite F
  have hm1 : 1 ≤ m := by omega
  have hσ : ∀ x : F, (x ^ 2 ^ m) ^ 2 ^ m = x := fun x => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hb0 := exists_add_frobPow_ne_zero hm1 hF
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set xd := autHom hLW ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLW hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have hc3 : c ^ 3 = 1 := by
    have h1 : ψ xd ^ 3 = 1 := by rw [← map_pow, pow_three_autHom hLW hd.1 hd3, map_one]
    have h2 := (upper_pow hxd10 3).2
    rw [h1] at h2
    simpa using h2.symm
  obtain ⟨t, ht, h, σ, hh, hασ, hσc⟩ :=
    exists_moving (n := 2 * m) (by omega) hF hLW hTL hTW hC ψ hP hd.1 hxd10 hdT
  obtain ⟨j, hj⟩ := exists_eq_pow_two_pow hF σ
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with hje | hjo
    · exact absurd (by rw [hj]; exact pow_two_pow_eq_self_of_even hc3 hje) hσc
    · exact hjo
  have hjm : Nat.Coprime j m := by
    have h2 : Nat.Coprime j 2 := Nat.coprime_two_right.mpr hjodd
    rcases hm with rfl | rfl
    · exact h2
    · exact Nat.Coprime.mul_right h2 h2
  have hline : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
      (Multiplicative.toAdd (Y v)) 0 1 = 0 ∧ (Multiplicative.toAdd (Y v)) 1 0 = 0 ∧
        (Multiplicative.toAdd (Y v)) 1 1 = 0 := by
    intro v hv
    refine fixed_of_unip hσ hb0 (hYherm v) fun b => ?_
    have hxP : ((ψ.symm (unipSL b) : ↥(autOn L W)) : MulAut ↥W) ∈ autOn (T ⊓ L) W :=
      (hP _).mpr ⟨b, MulEquiv.apply_symm_apply _ _⟩
    have hfix := (mem_centralizer_iff_autOn (hS.1.trans hLW) v).mp hv _ hxP
    have h1 := hYint (ψ.symm (unipSL b)) v
    rw [hfix, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hyq : ∀ v : ↥W, (Multiplicative.toAdd (Y v)) 0 0 ^ 2 ^ m =
      (Multiplicative.toAdd (Y v)) 0 0 := fun v => by
    have := congrFun (congrFun (hYherm v) 0) 0
    simpa [frobPow, Matrix.transpose_apply] using this
  have hy0 : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) → v ≠ 1 →
      (Multiplicative.toAdd (Y v)) 0 0 ≠ 0 := by
    intro v hv hv1 h00
    obtain ⟨h01, h10, h11⟩ := hline v hv
    apply hv1
    apply hYinj
    rw [map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact mat2_ext (by rw [h00]; rfl) (by rw [h01]; rfl) (by rw [h10]; rfl) (by rw [h11]; rfl)
  have hborel : ∀ (x : ↥(autOn L W)) (v : ↥W), (ψ x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
      (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 0 0 = (ψ x : Matrix (Fin 2) (Fin 2) F) 0 0 *
          (Multiplicative.toAdd (Y v)) 0 0 * (ψ x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 ^ m ∧
        (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 0 1 = 0 ∧
        (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 1 0 = 0 ∧
        (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 1 1 = 0 := by
    intro x v hx hv
    obtain ⟨h01, h10, h11⟩ := hline v hv
    rw [hYint]
    exact twist_upper m hx h01 h10 h11
  have hCT : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (T : Set G) →
      (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun v hv => Subgroup.centralizer_le (by exact inf_le_left) hv
  have hτv : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (T : Set G) →
      conjAct W ⟨t, hTW ht⟩ v = v := by
    intro v hv
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp hv t ht
    calc t * (v : G) * t⁻¹ = (v : G) * t * t⁻¹ := by rw [this]
      _ = v := by group
  have huniq : ∀ v₁ v₂ : ↥W, (v₁ : G) ∈ Subgroup.centralizer (T : Set G) →
      (v₂ : G) ∈ Subgroup.centralizer (T : Set G) → v₁ ≠ 1 → v₂ ≠ 1 → v₁ = v₂ := by
    intro v₁ v₂ hv₁ hv₂ h1 h2
    have hv₁' := hCT v₁ hv₁
    have hv₂' := hCT v₂ hv₂
    set y₁ := (Multiplicative.toAdd (Y v₁)) 0 0 with hy₁def
    set y₂ := (Multiplicative.toAdd (Y v₂)) 0 0 with hy₂def
    have hy₁ := hy0 v₁ hv₁' h1
    have hy₂ := hy0 v₂ hv₂' h2
    set k := y₂ / y₁ with hk
    have hk0 : k ≠ 0 := div_ne_zero hy₂ hy₁
    have hkq : k ^ 2 ^ m = k := by
      have e1 : y₁ ^ 2 ^ m = y₁ := hyq v₁
      have e2 : y₂ ^ 2 ^ m = y₂ := hyq v₂
      rw [hk, div_pow, e1, e2]
    have hky : k * y₁ = y₂ := div_mul_cancel₀ y₂ hy₁
    obtain ⟨c₀, hc₀, hc₀k⟩ := exists_pow_add_one_eq hF hk0 hkq
    set b₀ := ψ.symm (diagSL hc₀) with hb₀def
    have hb₀ : ψ b₀ = diagSL hc₀ := MulEquiv.apply_symm_apply _ _
    have hb₀10 : (ψ b₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hb₀]; simp [coe_diagSL]
    have hb₀00 : (ψ b₀ : Matrix (Fin 2) (Fin 2) F) 0 0 = c₀ := by rw [hb₀]; simp [coe_diagSL]
    have hNk : c₀ * c₀ ^ 2 ^ m = k := by rw [← pow_succ', hc₀k]
    have hbv : (b₀ : MulAut ↥W) v₁ = v₂ := by
      apply hYinj
      apply Multiplicative.toAdd.injective
      obtain ⟨e00, e01, e10, e11⟩ := hborel b₀ v₁ hb₀10 hv₁'
      obtain ⟨h01, h10, h11⟩ := hline v₂ hv₂'
      refine mat2_ext ?_ (by rw [e01, h01]) (by rw [e10, h10]) (by rw [e11, h11])
      rw [e00, hb₀00, ← hy₁def, ← hy₂def, ← hky, ← hNk]
      ring
    set τ := conjAct W ⟨t, hTW ht⟩ with hτ
    have hτb : τ * (b₀ : MulAut ↥W) * τ⁻¹ ∈ autOn L W :=
      (Subgroup.mem_normalizer_iff.mp (conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩ (hTL ht)) _).mp
        b₀.2
    set b₁ : ↥(autOn L W) := ⟨τ * (b₀ : MulAut ↥W) * τ⁻¹, hτb⟩ with hb₁def
    have hψb₁ : ψ b₁ = h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ b₀) * h⁻¹ :=
      hασ b₀ b₁ rfl
    obtain ⟨u1, u2⟩ := upper_conj_map σ hh hb₀10
    rw [← hψb₁, hb₀00] at u2
    rw [← hψb₁] at u1
    have hb₁v : (b₁ : MulAut ↥W) v₁ = v₂ := by
      have hτinv : τ⁻¹ v₁ = v₁ := by
        have := MulAut.inv_apply_self _ τ v₁
        rwa [hτv v₁ hv₁] at this
      change τ ((b₀ : MulAut ↥W) (τ⁻¹ v₁)) = v₂
      rw [hτinv, hbv, hτv v₂ hv₂]
    have e := (hborel b₁ v₁ u1 hv₁').1
    rw [hb₁v, u2, ← hy₁def, ← hy₂def] at e
    have hσk : σ k = k := by
      have h1 : σ c₀ * σ c₀ ^ 2 ^ m = σ k := by rw [← map_pow, ← map_mul, hNk]
      have h2 : y₂ = σ k * y₁ := by rw [e, ← h1]; ring
      exact mul_right_cancel₀ hy₁ (h2.symm.trans hky.symm)
    rw [hj] at hσk
    have hk2 : k ^ 2 = k := sq_eq_self_of_pow_two_pow hjm hσk hkq
    have hk1 : k = 1 := by
      have : k * (k - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hk2, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk0)
    have hy : y₂ = y₁ := (div_eq_one_iff_eq hy₁).mp hk1
    apply hYinj
    apply Multiplicative.toAdd.injective
    obtain ⟨a01, a10, a11⟩ := hline v₁ hv₁'
    obtain ⟨b01, b10, b11⟩ := hline v₂ hv₂'
    exact mat2_ext hy.symm (by rw [a01, b01]) (by rw [a10, b10]) (by rw [a11, b11])
  have hW2 : IsPGroup 2 W := by
    intro w
    refine ⟨1, hYinj ?_⟩
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, pow_one, two_nsmul]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hW1 : W ≠ ⊥ := by
    have h0 : (0 : F) ^ 2 ^ m = 0 := zero_pow (by positivity)
    obtain ⟨w, hw⟩ := hYsurj !![1, 0; 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, Matrix.transpose_apply, h0])
    intro hbot
    have hw1 : w = 1 := by
      have h1 : (w : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact w.2
      exact Subtype.ext (Subgroup.mem_bot.mp h1)
    rw [hw1, map_one, toAdd_one] at hw
    have := congrFun (congrFun hw 0) 0
    simp at this
  have hne := inf_centralizer_ne_bot_of_two hT hW2 hTW hW1
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨v₀, hv₀⟩, fun h0 => hv₀1 h0.symm, ?_⟩
  ext ⟨z, hz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hz1 : z = 1
  · left
    exact Subtype.ext hz1
  · right
    have hv₀1' : (⟨v₀, hv₀.1⟩ : ↥W) ≠ 1 := fun h0 =>
      hv₀1 (Subtype.ext (congrArg (Subtype.val : ↥W → G) h0))
    have hz1' : (⟨z, hz.1⟩ : ↥W) ≠ 1 := fun h0 => hz1 (congrArg Subtype.val h0)
    have := huniq ⟨z, hz.1⟩ ⟨v₀, hv₀.1⟩ hz.2 hv₀.2 hz1' hv₀1'
    exact Subtype.ext (congrArg (Subtype.val : ↥W → G) this)

end Orth

section Nat

variable [Finite G] {L T W : Subgroup G}

theorem card_fix_eq_two_nat {n : ℕ} {d : G} (hW : IsNatModCh5 L W n) (hn : n = 2 ∨ n = 4)
    (hT : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hS : IsSylowTwoOf (T ⊓ L) L)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T)
    (hd : d ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) (hd3 : orderOf d = 3)
    (hdT : d ∉ Subgroup.normalizer (T : Set G)) :
    Nat.card ↥(W ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.1
  obtain ⟨F, _, _, _, hF, ψ, Y, hYint, hP⟩ := hW.exists_sylowCoord hS
  have := Fintype.ofFinite F
  have hn1 : 1 ≤ n := by omega
  set xd := autHom hLW ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLW hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have hc3 : c ^ 3 = 1 := by
    have h1 : ψ xd ^ 3 = 1 := by rw [← map_pow, pow_three_autHom hLW hd.1 hd3, map_one]
    have h2 := (upper_pow hxd10 3).2
    rw [h1] at h2
    simpa using h2.symm
  obtain ⟨t, ht, h, σ, hh, hασ, hσc⟩ :=
    exists_moving hn1 hF hLW hTL hTW hC ψ hP hd.1 hxd10 hdT
  obtain ⟨j, hj⟩ := exists_eq_pow_two_pow hF σ
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with hje | hjo
    · exact absurd (by rw [hj]; exact pow_two_pow_eq_self_of_even hc3 hje) hσc
    · exact hjo
  have hjn : Nat.Coprime j n := by
    have h2 : Nat.Coprime j 2 := Nat.coprime_two_right.mpr hjodd
    rcases hn with rfl | rfl
    · exact h2
    · exact Nat.Coprime.mul_right h2 h2
  have hFq : ∀ x : F, x ^ 2 ^ n = x := fun x => by
    rw [← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hline : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
      (Multiplicative.toAdd (Y v)) 1 = 0 := by
    intro v hv
    have hxP : ((ψ.symm (unipSL 1) : ↥(autOn L W)) : MulAut ↥W) ∈ autOn (T ⊓ L) W :=
      (hP _).mpr ⟨1, MulEquiv.apply_symm_apply _ _⟩
    have hfix := (mem_centralizer_iff_autOn (hS.1.trans hLW) v).mp hv _ hxP
    have h1 := hYint (ψ.symm (unipSL 1)) v
    rw [hfix, MulEquiv.apply_symm_apply] at h1
    have h2 := congrFun h1 0
    simp [coe_unipSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    exact h2
  have hy0 : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) → v ≠ 1 →
      (Multiplicative.toAdd (Y v)) 0 ≠ 0 := by
    intro v hv hv1 h0
    apply hv1
    apply Y.injective
    rw [map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    funext i
    fin_cases i
    · exact h0
    · exact hline v hv
  have hborel : ∀ (x : ↥(autOn L W)) (v : ↥W), (ψ x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
      (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 0 =
          (ψ x : Matrix (Fin 2) (Fin 2) F) 0 0 * (Multiplicative.toAdd (Y v)) 0 ∧
        (Multiplicative.toAdd (Y ((x : MulAut ↥W) v))) 1 = 0 := by
    intro x v hx hv
    have h1 := hline v hv
    rw [hYint]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx, h1]
  have hCT : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (T : Set G) →
      (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun v hv => Subgroup.centralizer_le (by exact inf_le_left) hv
  have hτv : ∀ v : ↥W, (v : G) ∈ Subgroup.centralizer (T : Set G) →
      conjAct W ⟨t, hTW ht⟩ v = v := by
    intro v hv
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp hv t ht
    calc t * (v : G) * t⁻¹ = (v : G) * t * t⁻¹ := by rw [this]
      _ = v := by group
  have huniq : ∀ v₁ v₂ : ↥W, (v₁ : G) ∈ Subgroup.centralizer (T : Set G) →
      (v₂ : G) ∈ Subgroup.centralizer (T : Set G) → v₁ ≠ 1 → v₂ ≠ 1 → v₁ = v₂ := by
    intro v₁ v₂ hv₁ hv₂ h1 h2
    have hv₁' := hCT v₁ hv₁
    have hv₂' := hCT v₂ hv₂
    set y₁ := (Multiplicative.toAdd (Y v₁)) 0 with hy₁def
    set y₂ := (Multiplicative.toAdd (Y v₂)) 0 with hy₂def
    have hy₁ := hy0 v₁ hv₁' h1
    have hy₂ := hy0 v₂ hv₂' h2
    set k := y₂ / y₁ with hk
    have hk0 : k ≠ 0 := div_ne_zero hy₂ hy₁
    have hky : k * y₁ = y₂ := div_mul_cancel₀ y₂ hy₁
    set b₀ := ψ.symm (diagSL hk0) with hb₀def
    have hb₀ : ψ b₀ = diagSL hk0 := MulEquiv.apply_symm_apply _ _
    have hb₀10 : (ψ b₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [hb₀]; simp [coe_diagSL]
    have hb₀00 : (ψ b₀ : Matrix (Fin 2) (Fin 2) F) 0 0 = k := by rw [hb₀]; simp [coe_diagSL]
    have hbv : (b₀ : MulAut ↥W) v₁ = v₂ := by
      apply Y.injective
      apply Multiplicative.toAdd.injective
      obtain ⟨e0, e1⟩ := hborel b₀ v₁ hb₀10 hv₁'
      funext i
      fin_cases i
      · change (Multiplicative.toAdd (Y ((b₀ : MulAut ↥W) v₁))) 0 = y₂
        rw [e0, hb₀00, ← hy₁def, hky]
      · change (Multiplicative.toAdd (Y ((b₀ : MulAut ↥W) v₁))) 1 =
          (Multiplicative.toAdd (Y v₂)) 1
        rw [e1, hline v₂ hv₂']
    set τ := conjAct W ⟨t, hTW ht⟩ with hτ
    have hτb : τ * (b₀ : MulAut ↥W) * τ⁻¹ ∈ autOn L W :=
      (Subgroup.mem_normalizer_iff.mp (conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩ (hTL ht)) _).mp
        b₀.2
    set b₁ : ↥(autOn L W) := ⟨τ * (b₀ : MulAut ↥W) * τ⁻¹, hτb⟩ with hb₁def
    have hψb₁ : ψ b₁ = h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ b₀) * h⁻¹ :=
      hασ b₀ b₁ rfl
    obtain ⟨u1, u2⟩ := upper_conj_map σ hh hb₀10
    rw [← hψb₁, hb₀00] at u2
    rw [← hψb₁] at u1
    have hb₁v : (b₁ : MulAut ↥W) v₁ = v₂ := by
      have hτinv : τ⁻¹ v₁ = v₁ := by
        have := MulAut.inv_apply_self _ τ v₁
        rwa [hτv v₁ hv₁] at this
      change τ ((b₀ : MulAut ↥W) (τ⁻¹ v₁)) = v₂
      rw [hτinv, hbv, hτv v₂ hv₂]
    have e := (hborel b₁ v₁ u1 hv₁').1
    rw [hb₁v, u2, ← hy₁def, ← hy₂def] at e
    have hσk : σ k = k := mul_right_cancel₀ hy₁ (e.symm.trans hky.symm)
    rw [hj] at hσk
    have hk2 : k ^ 2 = k := sq_eq_self_of_pow_two_pow hjn hσk (hFq k)
    have hk1 : k = 1 := by
      have : k * (k - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hk2, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk0)
    have hy : y₂ = y₁ := (div_eq_one_iff_eq hy₁).mp hk1
    apply Y.injective
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hy.symm
    · change (Multiplicative.toAdd (Y v₁)) 1 = (Multiplicative.toAdd (Y v₂)) 1
      rw [hline v₁ hv₁', hline v₂ hv₂']
  have hW2 : IsPGroup 2 W := by
    intro w
    refine ⟨1, Y.injective ?_⟩
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, pow_one, two_nsmul]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hW1 : W ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := Y.surjective (Multiplicative.ofAdd ![1, 0])
    have hw1 : w = 1 := by
      have h1 : (w : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact w.2
      exact Subtype.ext (Subgroup.mem_bot.mp h1)
    rw [hw1, map_one] at hw
    have := congrFun (congrArg Multiplicative.toAdd hw) 0
    simp at this
  have hne := inf_centralizer_ne_bot_of_two hT hW2 hTW hW1
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨v₀, hv₀⟩, fun h0 => hv₀1 h0.symm, ?_⟩
  ext ⟨z, hz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hz1 : z = 1
  · left
    exact Subtype.ext hz1
  · right
    have hv₀1' : (⟨v₀, hv₀.1⟩ : ↥W) ≠ 1 := fun h0 =>
      hv₀1 (Subtype.ext (congrArg (Subtype.val : ↥W → G) h0))
    have hz1' : (⟨z, hz.1⟩ : ↥W) ≠ 1 := fun h0 => hz1 (congrArg Subtype.val h0)
    have := huniq ⟨z, hz.1⟩ ⟨v₀, hv₀.1⟩ hz.2 hv₀.2 hz1' hv₀1'
    exact Subtype.ext (congrArg (Subtype.val : ↥W → G) this)

end Nat

theorem l2ModFixTwoFact : L2ModFixTwoFact := by
  intro G _ _ L T W n d hmod hT hTL hTW hS hC hd hd3 hdT
  rcases hmod with ⟨hW, hn⟩ | ⟨hW, hn⟩
  · exact card_fix_eq_two_nat hW hn hT hTL hTW hS hC hd hd3 hdT
  · obtain ⟨m, hm2, -⟩ := id hW
    subst hm2
    exact card_fix_eq_two_orth hW (by omega) hT hTL hTW hS hC hd hd3 hdT

end CFSG.Quasithin.H13
