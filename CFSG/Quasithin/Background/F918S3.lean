module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.F918S0
public import CFSG.Quasithin.Background.F918S1
public import CFSG.Quasithin.Background.F918S2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

theorem _root_.CFSG.Quasithin.d35InspSum_holds : CFSG.Quasithin.D35InspSum := by
  classical
  intro Y _ _ Lb A n U₁ U₂ hn hdir hex hAel hnorm hnotstab
  obtain ⟨π, h1, h2⟩ := hex
  have hR1 : RealM Lb U₁ ⊥ π mat := realM_mat_iff.2 h1
  have hR2 : RealM Lb U₂ ⊥ π dmat := realM_dmat_iff.2 h2
  have hπ : Function.Bijective π := ⟨hR1.injective (Or.inl rfl), hR1.1⟩
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hgL : ∀ g ∈ A, ∀ x ∈ Lb, g * x * g⁻¹ ∈ Lb := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hnorm hg) x).1 hx
  have hgL' : ∀ g ∈ A, ∀ x ∈ Lb, g⁻¹ * x * g ∈ Lb := fun g hg x hx => by
    simpa using (Subgroup.mem_normalizer_iff.1 (hnorm (A.inv_mem hg)) x).1 hx
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ stabSub U₁ := by
    by_contra hcon
    push Not at hcon
    exact hnotstab fun g hg => hcon g hg
  have hrkU : ∀ {X : Subgroup Y} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)},
      RealM Lb X ⊥ π M → rk X = n := by
    intro X M hX
    have e1 := hX.card_sec
    have e2 := card_sec_mul (bot_le : (⊥ : Subgroup Y) ≤ X)
    rw [Subgroup.card_bot, mul_one, e1] at e2
    unfold rk
    rw [← e2, padicValNat.prime_pow]
  have hrkU₁ := hrkU hR1
  have hrkU₂ := hrkU hR2
  have hsq : ∀ z : Multiplicative (Fin n → ZMod 2), z ^ 2 = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    have h22 : (2 : ZMod 2) = 0 := by decide
    simp [h22]
  have hU : ∀ {X : Subgroup Y} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)},
      RealM Lb X ⊥ π M → ∀ x ∈ X, x ^ 2 = 1 := by
    intro X M hX x hx
    obtain ⟨-, -, -, -, β, -, hβk, -⟩ := hX
    have h2 : β (⟨x, hx⟩ ^ 2) = 1 := by rw [map_pow]; exact hsq _
    have h3 := (hβk _).1 h2
    simpa using h3
  have hV : ∀ v : Y, v ^ 2 = 1 := by
    intro v
    have hv : v ∈ U₁ ⊔ U₂ := by rw [hdir.1]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [mul_pow, hU hR1 x hx, hU hR2 y hy, mul_one]
  have hU₁ne : U₁ ≠ ⊥ := fun h => by rw [h, rk_bot] at hrkU₁; omega
  have hU₁₂ : U₁ ≠ U₂ := fun h => hU₁ne (by rw [← hdir.2, ← h, inf_idem])
  have hperm := fun g (hg : g ∈ A) => perm_of_normalizer hn hdir hR1 hR2 (hgL g hg) (hgL' g hg)
  obtain ⟨ha₁, ha₂⟩ : U₁.map a.toMonoidHom = U₂ ∧ U₂.map a.toMonoidHom = U₁ := by
    rcases hperm a haA with ⟨h, -⟩ | h
    · exact absurd (mem_stabSub_iff_map_eq.mpr h) haU
    · exact h
  have haa : a * a = 1 := by simpa [pow_two] using hAel.2 a haA
  set A₀ : Subgroup (MulAut Y) := A ⊓ stabSub U₁ with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hmem : ∀ g, g ∈ A₀ ↔ g ∈ A ∧ U₁.map g.toMonoidHom = U₁ := fun g => by
    rw [hA₀, Subgroup.mem_inf, mem_stabSub_iff_map_eq]
  have hA₀L : A₀ ≤ Lb := by
    intro g hg
    obtain ⟨hgA, hg₁⟩ := (hmem g).1 hg
    have hg₂ : U₂.map g.toMonoidHom = U₂ := by
      rcases hperm g hgA with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hg₁.symm.trans h) hU₁₂
    exact mem_of_stab_pair hn hdir hR1 hR2 (hgL g hgA) (hgL' g hgA) hg₁ hg₂
  have hswap : ∀ x ∈ A, x ∉ A₀ → U₁.map x.toMonoidHom = U₂ := by
    intro x hx hxn
    rcases hperm x hx with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd ((hmem x).2 ⟨hx, h⟩) hxn
    · exact h
  have hax : ∀ x ∈ A, x ∉ A₀ → a * x ∈ A₀ := by
    intro x hx hxn
    refine (hmem _).2 ⟨A.mul_mem haA hx, ?_⟩
    rw [map_mul_aut', hswap x hx hxn, ha₂]
  have hcardA : Nat.card A ≤ 2 * Nat.card A₀ := by
    let f : ↥A → ↥A₀ × Fin 2 := fun x =>
      if hx : (x : MulAut Y) ∈ A₀ then (⟨x, hx⟩, 0) else (⟨a * x, hax x x.2 hx⟩, 1)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : MulAut Y) ∈ A₀ <;> by_cases hy : (y : MulAut Y) ∈ A₀
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        exact Subtype.ext (Subtype.mk_eq_mk.1 hxy.1)
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have e : a * (x : MulAut Y) = a * (y : MulAut Y) := congrArg Subtype.val hxy.1
        exact Subtype.ext (mul_left_cancel e)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_fin, mul_comm] at this
  obtain ⟨P, hPs, hPc⟩ := exists_symm_of_swap hn hdir hR1 hR2 (hgL a haA) (hgL' a haA) haa ha₁ ha₂
  set B : Subgroup ↥(StatedSL n (ZMod 2)) := pre π A₀ with hB
  have hBmem : ∀ γ, γ ∈ B ↔ ((π γ : ↥Lb) : MulAut Y) ∈ A₀ := fun γ => mem_pre
  have hBexp : ∀ γ ∈ B, γ * γ = 1 := by
    intro γ hγ
    have h := hAel.2 _ (hA₀A ((hBmem γ).1 hγ))
    apply hπ.1
    apply Subtype.ext
    rw [map_mul, map_one]
    simpa [pow_two] using h
  have hBcomm : ∀ γ ∈ B, ∀ δ ∈ B, γ * δ = δ * γ := by
    intro γ hγ δ hδ
    apply hπ.1
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact hAel.1 _ (hA₀A ((hBmem γ).1 hγ)) _ (hA₀A ((hBmem δ).1 hδ))
  have hBP : ∀ γ ∈ B, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
      dmat γ * (P : Matrix (Fin n) (Fin n) (ZMod 2)) := fun γ hγ =>
    hPc γ (hAel.1 a haA _ (hA₀A ((hBmem γ).1 hγ)))
  have hcore := sym_rank_bound hn B hBexp hBcomm P hPs hBP
  have hcardB : Nat.card B = Nat.card A₀ := card_pre hπ hA₀L
  have huniq : ∀ x ∈ U₁, ∀ x' ∈ U₁, ∀ z ∈ U₂, ∀ z' ∈ U₂, x * z = x' * z' → x = x' ∧ z = z' := by
    intro x hx x' hx' z hz z' hz' h
    have h1 : x'⁻¹ * x = z' * z⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * z) * z⁻¹ := by group
        _ = x'⁻¹ * (x' * z') * z⁻¹ := by rw [h]
        _ = z' * z⁻¹ := by group
    have h2 : x'⁻¹ * x ∈ U₁ ⊓ U₂ :=
      ⟨U₁.mul_mem (U₁.inv_mem hx') hx, h1 ▸ U₂.mul_mem hz' (U₂.inv_mem hz)⟩
    rw [hdir.2, Subgroup.mem_bot] at h2
    have hxx : x = x' := by
      have := congrArg (x' * ·) h2
      simpa using this
    refine ⟨hxx, ?_⟩
    subst hxx
    exact mul_left_cancel h
  have hA₀U₂ : ∀ b ∈ A₀, ∀ x ∈ U₂, b x ∈ U₂ := by
    intro b hb x hx
    have : U₂.map b.toMonoidHom = U₂ := by
      rcases hperm b (hA₀A hb) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (((hmem b).1 hb).2.symm.trans h) hU₁₂
    rw [← this]
    exact ⟨x, hx, rfl⟩
  have hA₀U₁ : ∀ b ∈ A₀, ∀ x ∈ U₁, b x ∈ U₁ := by
    intro b hb x hx
    rw [← ((hmem b).1 hb).2]
    exact ⟨x, hx, rfl⟩
  have haU₁ : ∀ x ∈ U₁, a x ∈ U₂ := by
    intro x hx
    rw [← ha₁]
    exact ⟨x, hx, rfl⟩
  have haU₂ : ∀ x ∈ U₂, a x ∈ U₁ := by
    intro x hx
    rw [← ha₂]
    exact ⟨x, hx, rfl⟩
  have hc₁ : rk ↥(U₁ ⊓ fixV A₀) = finrank (ZMod 2) ↥(fixN B) := by
    have e1 : rkSub A₀ U₁ = n - finrank (ZMod 2) ↥(fixN B) := by
      have := hR1.rkSub_eq hA₀L
      rwa [fixM_mat] at this
    have e2 : rkSub A₀ U₁ = rk U₁ - rk ↥(U₁ ⊓ fixV A₀) := rfl
    have e3 := rk_mono (inf_le_left : U₁ ⊓ fixV A₀ ≤ U₁)
    have e4 := finrank_fixN_le B
    omega
  have hfix : Nat.card (fixV A) ≤ 2 ^ finrank (ZMod 2) ↥(fixN B) := by
    let τ : Y →* Y := MonoidHom.id Y * a.toMonoidHom
    have hτ : ∀ y, τ y = y * a y := fun y => rfl
    have hsub : fixV A ≤ (U₁ ⊓ fixV A₀).map τ := by
      intro y hy
      have hya : a y = y := hy a haA
      have hy' : y ∈ U₁ ⊔ U₂ := by rw [hdir.1]; exact Subgroup.mem_top y
      obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hy'
      have h1 : a w * a u = u * w := by
        rw [mul_comm (a w) (a u), ← map_mul]
        exact hya
      obtain ⟨h1a, h1b⟩ := huniq (a w) (haU₂ w hw) u hu (a u) (haU₁ u hu) w hw h1
      have hfixu : u ∈ fixV A₀ := by
        intro b hb
        have hb' : b (u * w) = u * w := hy b (hA₀A hb)
        rw [map_mul] at hb'
        exact (huniq (b u) (hA₀U₁ b hb u hu) u hu (b w) (hA₀U₂ b hb w hw) w hw hb').1
      exact ⟨u, ⟨hu, hfixu⟩, by rw [hτ, h1b]⟩
    calc Nat.card ↥(fixV A) ≤ Nat.card ↥((U₁ ⊓ fixV A₀).map τ) := Subgroup.card_le_of_le hsub
      _ ≤ Nat.card ↥(U₁ ⊓ fixV A₀) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (U₁ ⊓ fixV A₀) τ)
      _ = 2 ^ rk ↥(U₁ ⊓ fixV A₀) := card_eq_two_pow hV _
      _ = 2 ^ finrank (ZMod 2) ↥(fixN B) := by rw [hc₁]
  have hrkV : rk Y = 2 * n := by
    have e1 := rk_sup_add_rk_inf U₁ U₂
    rw [hdir.1, hdir.2, rk_bot, add_zero, rk_top, hrkU₁, hrkU₂] at e1
    omega
  have hcardY : Nat.card Y = 2 ^ (2 * n) := by
    have := card_eq_two_pow hV (⊤ : Subgroup Y)
    rw [rk_top, hrkV, Subgroup.card_top] at this
    exact this
  calc Nat.card A * Nat.card (fixV A) ≤ (2 * Nat.card A₀) * 2 ^ finrank (ZMod 2) ↥(fixN B) :=
        Nat.mul_le_mul hcardA hfix
    _ = 2 * (Nat.card B * 2 ^ finrank (ZMod 2) ↥(fixN B)) := by rw [hcardB]; ring
    _ ≤ 2 * 2 ^ (2 * n - 2) := Nat.mul_le_mul_left 2 hcore
    _ = 2 ^ (2 * n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
    _ < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = Nat.card Y := hcardY.symm

end CFSG.Quasithin.B5.Ln
