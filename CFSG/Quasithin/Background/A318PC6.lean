module

public import CFSG.Quasithin.Background.A318PC4
public import CFSG.Quasithin.Background.A318PC5

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Aux

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_cube_eq_smul {y : GL (Fin 3) K} (h : y ^ 3 ∈ StatedScalars (Fin 3) K) :
    ∃ ℓ : K, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1 := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : K), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]

theorem irreducible_of_mul_scalar {y z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, ((y * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  obtain ⟨c, rfl⟩ := hz
  intro W hW
  refine hirr W fun v hv => ?_
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (hW v hv)

end Aux

section Lifts3

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

omit [Finite X] in
theorem cube_mem_zPi_of_isPGLAt (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {g : X}
    (hg3 : g ^ 3 = 1) {y : GL (Fin 3) K} (hy : IsPGLAt e g y) : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h1 := isPGLAt_pow hy 3
  rw [hg3] at h1
  have h2 := (isPGLAt_one_iff e h1.1).1 h1
  have hscal : y ^ 3 ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
    have := h2 ⟨m, hm⟩
    change y ^ 3 * m * (y ^ 3)⁻¹ = m at this
    calc y ^ 3 * m = y ^ 3 * m * (y ^ 3)⁻¹ * y ^ 3 := by group
      _ = m * y ^ 3 := by rw [this]
  rw [zPi_eq hπ hq' hτ hτ1]
  exact Subgroup.mem_inf.2 ⟨pow_mem hy.1 3, hscal⟩

omit [Finite X] in
theorem isPGLAt_symm (hπ : π = false → UnitaryFieldData p f K) (t : slPi π 3 (p ^ f) K) :
    IsPGLAt e ((e.symm t : ↥S) : X) (t : GL (Fin 3) K) := by
  have h := isPGLAt_of_mem e hπ (e.symm t).2
  have h2 : (e ⟨((e.symm t : ↥S) : X), (e.symm t).2⟩ : slPi π 3 (p ^ f) K) = t := by
    have : (⟨((e.symm t : ↥S) : X), (e.symm t).2⟩ : ↥S) = e.symm t := rfl
    rw [this, MulEquiv.apply_symm_apply]
  rw [h2] at h
  exact h

theorem exists_twist (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x : X}
    {y : GL (Fin 3) K} (hxy : IsPGLAt e x y) (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hCS : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c ∈ S) :
    ∀ c ∈ (Subgroup.center ↥S).map S.subtype, ∃ s ∈ S, s * x * s⁻¹ = x * c := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hyZs : y ^ 3 ∈ StatedScalars (Fin 3) K :=
    (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hy3)).2
  obtain ⟨ℓ, hℓy⟩ := exists_cube_eq_smul hyZs
  have hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ := not_cube_of_irreducible hτ hτ1 hℓy hirr
  obtain ⟨w, hwL, hwy⟩ := exists_w hK hq hτ hτ1 hxy.1 hℓ hℓy
  set sw : ↥S := e.symm ⟨w, hwL⟩ with hsw
  have hIw : IsPGLAt e (sw : X) w := isPGLAt_symm hπ ⟨w, hwL⟩
  have hconj : IsPGLAt e ((sw : X) * x * (sw : X)⁻¹) (w * y * w⁻¹) :=
    isPGLAt_mul e (isPGLAt_mul e hIw hxy) (isPGLAt_inv hIw)
  have hwyw : w * y = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (y * w) := by
    apply Units.ext
    rw [Units.val_mul, hwy, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hc' : IsPGLAt e (x⁻¹ * ((sw : X) * x * (sw : X)⁻¹)) (y⁻¹ * (w * y * w⁻¹)) :=
    isPGLAt_mul e (isPGLAt_inv hxy) hconj
  have hscal : y⁻¹ * (w * y * w⁻¹) ∈ StatedScalars (Fin 3) K := by
    refine ⟨Units.mk0 τ hτ0, ?_⟩
    have h1 : w * y * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * y := by
      rw [hwyw]
      group
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 τ hτ0) y⁻¹).eq
    rw [h1, ← mul_assoc, hc, mul_assoc, inv_mul_cancel, mul_one]
  set cw : X := x⁻¹ * ((sw : X) * x * (sw : X)⁻¹) with hcwdef
  have hcC : cw ∈ Subgroup.centralizer (S : Set X) := mem_centralizer_of_isPGLAt_scalar hc' hscal
  have hcS : cw ∈ S := hCS cw fun s hs => ((Subgroup.mem_centralizer_iff.1 hcC) s hs).symm
  have hcZ : cw ∈ (Subgroup.center ↥S).map S.subtype :=
    ⟨⟨cw, hcS⟩, Subgroup.mem_center_iff.2 fun s =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hcC) s s.2), rfl⟩
  have hcw1 : cw ≠ 1 := by
    intro h1
    have hsx : (sw : X) * x * (sw : X)⁻¹ = x := by
      have : x⁻¹ * ((sw : X) * x * (sw : X)⁻¹) = 1 := h1
      calc (sw : X) * x * (sw : X)⁻¹ = x * (x⁻¹ * ((sw : X) * x * (sw : X)⁻¹)) := by group
        _ = x := by rw [this, mul_one]
    have hcomm : (sw : X) * x = x * (sw : X) := by
      calc (sw : X) * x = (sw : X) * x * (sw : X)⁻¹ * (sw : X) := by group
        _ = x * (sw : X) := by rw [hsx]
    have h2 := (mem_centralizer_iff_of_isPGLAt hxy sw).1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
    have hesw : (e sw : slPi π 3 (p ^ f) K) = ⟨w, hwL⟩ := by rw [hsw, MulEquiv.apply_symm_apply]
    rw [hesw] at h2
    have h3 : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.1 h2
    have h4 : ((y * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        τ • ((y * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      calc ((y * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((w * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h3]
        _ = (w : Matrix (Fin 3) (Fin 3) K) * y := Units.val_mul _ _
        _ = τ • ((y : Matrix (Fin 3) (Fin 3) K) * w) := hwy
        _ = τ • ((y * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [Units.val_mul]
    have h5 : ((1 : K) - τ) • ((y * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
      rw [sub_smul, one_smul, ← h4, sub_self]
    exact (y * w).ne_zero ((smul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hτ1.symm))
  have hZ'card : Nat.card ((Subgroup.center ↥S).map S.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hZ]
  have hcw3 : cw ^ 3 = 1 := by
    have := pow_card_eq_one' (G := (Subgroup.center ↥S).map S.subtype) (x := ⟨cw, hcZ⟩)
    rw [hZ'card] at this
    exact congrArg Subtype.val this
  have hcwo : orderOf cw = 3 := orderOf_eq_prime hcw3 hcw1
  have hZ'eq : (Subgroup.center ↥S).map S.subtype = Subgroup.zpowers cw := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcZ) ?_).symm
    rw [Nat.card_zpowers, hcwo, hZ'card]
  have hsx' : (sw : X) * x * (sw : X)⁻¹ = x * cw := by rw [hcwdef]; group
  have hswc : (sw : X) * cw = cw * (sw : X) := (Subgroup.mem_centralizer_iff.1 hcC) _ sw.2
  have htw : ∀ k : ℕ, (sw : X) ^ k * x * ((sw : X) ^ k)⁻¹ = x * cw ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hswck : (sw : X) * cw ^ k = cw ^ k * (sw : X) :=
        (show Commute (sw : X) cw from hswc).pow_right k |>.eq
      calc (sw : X) ^ (k + 1) * x * ((sw : X) ^ (k + 1))⁻¹ =
          (sw : X) * ((sw : X) ^ k * x * ((sw : X) ^ k)⁻¹) * (sw : X)⁻¹ := by group
        _ = (sw : X) * (x * cw ^ k) * (sw : X)⁻¹ := by rw [ih]
        _ = ((sw : X) * x * (sw : X)⁻¹) * ((sw : X) * cw ^ k * (sw : X)⁻¹) := by group
        _ = (x * cw) * cw ^ k := by
          rw [hsx', hswck]
          group
        _ = x * cw ^ (k + 1) := by group
  intro c hc
  rw [hZ'eq] at hc
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hc)
  exact ⟨(sw : X) ^ k, pow_mem sw.2 k, htw k⟩

theorem exists_conj_of_orderThree
    (e : ↥S ≃* slPi π 3 (p ^ f) K) (hQ : CFSG.IsQuasisimple ↥S)
    (hS2 : 2 ≤ CFSG.Open.pRank 3 S) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (hZ : Nat.card (Subgroup.center ↥S) = 3) (hP : CFSG.pPrimeCore 3 X = ⊥) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S)
    (hA : ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x)
    {Y : Subgroup X} (hY : Nat.card Y = 3) (hYS : ¬ Y ≤ S) :
    ∃ l ∈ S, Y = (Subgroup.zpowers x).map (MulAut.conj l).toMonoidHom := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, hxy, hy3, hirr, hnon, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
  have hCS := centralizer_le_S hK hq hP hx hxy hy3 hnon hZ hA
  have htw := exists_twist hK hq hxy hy3 hirr hZ hCS
  obtain ⟨g, hgY, hgS⟩ : ∃ g ∈ Y, g ∉ S := by
    by_contra h
    push Not at h
    exact hYS h
  have hg3 : g ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Y) (x := ⟨g, hgY⟩)
    rw [hY] at this
    exact congrArg Subtype.val this
  have hg1 : g ≠ 1 := fun h => hgS (h ▸ S.one_mem)
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hgA : g ∈ S ⊔ Subgroup.zpowers x := hA g ⟨1, by rw [hgord, pow_one]⟩
  obtain ⟨l₀, hl₀, n, hn, hgn⟩ := mem_sup_zpowers_cube hx hgA
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨g', hg'Y, hg'⟩ : ∃ g' ∈ Y, ∃ l ∈ S, g' = l * x := by
    interval_cases n
    · exact absurd (by simpa [hgn] using hl₀) hgS
    · exact ⟨g, hgY, l₀, hl₀, by simpa using hgn⟩
    · refine ⟨g⁻¹, Y.inv_mem hgY, x * l₀⁻¹ * x⁻¹, ?_, ?_⟩
      · simpa using hSn.conj_mem _ (S.inv_mem hl₀) x
      · rw [hgn]
        have : x ^ 2 = x⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
        rw [this]
        group
  obtain ⟨l, hl, rfl⟩ := hg'
  have hg'S : l * x ∉ S := fun h => hxS (by simpa using S.mul_mem (S.inv_mem hl) h)
  have hg'3 : (l * x) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Y) (x := ⟨l * x, hg'Y⟩)
    rw [hY] at this
    exact congrArg Subtype.val this
  have hg'ord : orderOf (l * x) = 3 := orderOf_eq_prime hg'3 fun h => hg'S (h ▸ S.one_mem)
  have hYg' : Y = Subgroup.zpowers (l * x) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg'Y)
      (by rw [Nat.card_zpowers, hg'ord, hY])).symm
  have hy₂ : IsPGLAt e (l * x) ((e ⟨l, hl⟩ : GL (Fin 3) K) * y) :=
    isPGLAt_mul e (isPGLAt_of_mem e hπ hl) hxy
  have hy₂3 := cube_mem_zPi_of_isPGLAt hK hq hg'3 hy₂
  obtain ⟨yg, hxyg, -, hirrg, -, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hg'ord hg'S
  have hsc := isPGLAt_inv_mul_mem hK hq hy₂ hxyg
  have hirr₂ : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (((e ⟨l, hl⟩ : GL (Fin 3) K) * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈
        W) → W = ⊥ ∨ W = ⊤ :=
    irreducible_of_mul_scalar hsc (by rw [mul_inv_cancel_left]; exact hirrg)
  have hy₁s : y ^ 3 ∈ StatedScalars (Fin 3) K :=
    (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hy3)).2
  obtain ⟨ℓ₁, hℓ₁y⟩ := exists_cube_eq_smul hy₁s
  have hℓ₁ := not_cube_of_irreducible hτ hτ1 hℓ₁y hirr
  have hy₂s : ((e ⟨l, hl⟩ : GL (Fin 3) K) * y) ^ 3 ∈ StatedScalars (Fin 3) K :=
    (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hy₂3)).2
  obtain ⟨ℓ₂, hℓ₂y⟩ := exists_cube_eq_smul hy₂s
  have hℓ₂ := not_cube_of_irreducible hτ hτ1 hℓ₂y hirr₂
  have hdet₁ := det_eq_of_cube hℓ₁ hℓ₁y
  have hdet₂ := det_eq_of_cube hℓ₂ hℓ₂y
  have hdl : ((e ⟨l, hl⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_slPi_iff hπ).1 (e ⟨l, hl⟩).2).2
  have hℓeq : ℓ₂ = ℓ₁ := by
    rw [← hdet₂, Units.val_mul, det_mul, hdl, one_mul, hdet₁]
  rw [hℓeq] at hℓ₂y
  obtain ⟨t, ht, hty⟩ := exists_conj_slPi hK hq hxy.1 hy₂.1 hℓ₁ hℓ₁y hℓ₂y
  set s₀ : X := ((e.symm ⟨t, ht⟩ : ↥S) : X) with hs₀
  have hs₀S : s₀ ∈ S := (e.symm ⟨t, ht⟩).2
  have hIt : IsPGLAt e s₀ t := isPGLAt_symm hπ ⟨t, ht⟩
  have hconj : IsPGLAt e (s₀ * x * s₀⁻¹) (t * y * t⁻¹) :=
    isPGLAt_mul e (isPGLAt_mul e hIt hxy) (isPGLAt_inv hIt)
  rw [hty] at hconj
  have hc₁ : IsPGLAt e ((l * x)⁻¹ * (s₀ * x * s₀⁻¹))
      (((e ⟨l, hl⟩ : GL (Fin 3) K) * y)⁻¹ * ((e ⟨l, hl⟩ : GL (Fin 3) K) * y)) :=
    isPGLAt_mul e (isPGLAt_inv hy₂) hconj
  have hc₁C : (l * x)⁻¹ * (s₀ * x * s₀⁻¹) ∈ Subgroup.centralizer (S : Set X) :=
    mem_centralizer_of_isPGLAt_scalar hc₁ (by rw [inv_mul_cancel]; exact one_mem _)
  set c₁ : X := (l * x)⁻¹ * (s₀ * x * s₀⁻¹) with hc₁def
  have hc₁S : c₁ ∈ S := hCS c₁ fun s hs => ((Subgroup.mem_centralizer_iff.1 hc₁C) s hs).symm
  have hc₁Z : c₁ ∈ (Subgroup.center ↥S).map S.subtype :=
    ⟨⟨c₁, hc₁S⟩, Subgroup.mem_center_iff.2 fun s =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc₁C) s s.2), rfl⟩
  obtain ⟨s, hsS, hsx⟩ := htw c₁⁻¹ (inv_mem hc₁Z)
  have hs₀c : s₀ * c₁ = c₁ * s₀ := (Subgroup.mem_centralizer_iff.1 hc₁C) s₀ hs₀S
  have hs₀ci : s₀ * c₁⁻¹ = c₁⁻¹ * s₀ := (show Commute s₀ c₁ from hs₀c).inv_right.eq
  have hlx : l * x = (s₀ * s) * x * (s₀ * s)⁻¹ := by
    calc l * x = (s₀ * x * s₀⁻¹) * c₁⁻¹ := by rw [hc₁def]; group
      _ = s₀ * (x * c₁⁻¹) * s₀⁻¹ := by
        calc (s₀ * x * s₀⁻¹) * c₁⁻¹ = s₀ * x * (s₀⁻¹ * c₁⁻¹ * s₀) * s₀⁻¹ := by group
          _ = s₀ * x * c₁⁻¹ * s₀⁻¹ := by
            have : s₀⁻¹ * c₁⁻¹ * s₀ = c₁⁻¹ := by
              rw [mul_assoc, ← hs₀ci]
              group
            rw [this]
          _ = s₀ * (x * c₁⁻¹) * s₀⁻¹ := by group
      _ = s₀ * (s * x * s⁻¹) * s₀⁻¹ := by rw [hsx]
      _ = (s₀ * s) * x * (s₀ * s)⁻¹ := by group
  refine ⟨s₀ * s, mul_mem hs₀S hsS, ?_⟩
  rw [hYg', hlx, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end Lifts3

end A318P

end CFSG.Quasithin
