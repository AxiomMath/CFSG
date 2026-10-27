module

public import CFSG.Quasithin.Background.SmithB51LnSum
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

section SumSit

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {n : ℕ}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L}

private theorem rk_eq_of_realM_aux {W : Subgroup V}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (hW : RealM L W ⊥ π M) :
    rk W = n := by
  have e1 := hW.card_sec
  have e2 := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ W)
  rw [Subgroup.card_bot, mul_one, e1] at e2
  unfold rk
  rw [← e2, padicValNat.prime_pow]

private theorem map_eq_or_eq_aux (hn3 : 3 ≤ n) (hπ : Function.Bijective π)
    (hV : ∀ v : V, v ^ 2 = 1) {W W' : Subgroup V}
    {M M' : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : RealM L W ⊥ π M) (h' : RealM L W' ⊥ π M')
    (hMM : (M = mat ∧ M' = dmat) ∨ (M = dmat ∧ M' = mat))
    (hsup : W ⊔ W' = ⊤) (hinf : W ⊓ W' = ⊥) {g : MulAut V}
    (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) :
    W.map g.toMonoidHom = W ∨ W.map g.toMonoidHom = W' := by
  have hM : M = mat ∨ M = dmat := by rcases hMM with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hM' : M' = mat ∨ M' = dmat := by rcases hMM with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  set X : Subgroup V := W.map g.toMonoidHom with hX
  have hWinv : ∀ l ∈ L, ∀ x ∈ W, l x ∈ W := fun l hl x hx => h.2.2.1 ⟨l, hl⟩ x hx
  have hW'inv : ∀ l ∈ L, ∀ x ∈ W', l x ∈ W' := fun l hl x hx => h'.2.2.1 ⟨l, hl⟩ x hx
  have hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X := by
    rintro l hl _ ⟨u, hu, rfl⟩
    refine ⟨(g⁻¹ * l * g) u, hWinv _ (hgL' l hl) u hu, ?_⟩
    simp [MulAut.mul_apply]
  have hrkW := rk_eq_of_realM_aux h
  have hrkW' := rk_eq_of_realM_aux h'
  have hcardX : Nat.card X = Nat.card W :=
    Subgroup.card_map_of_injective (fun x y hxy => g.injective hxy)
  have hrkX : rk X = n := by
    have e1 := card_eq_two_pow hV X
    have e2 := card_eq_two_pow hV W
    rw [hcardX, e2] at e1
    have := Nat.pow_right_injective (le_refl 2) e1
    omega
  rcases h.eq_or_eq hM (isInv_inf hWinv hXinv) bot_le inf_le_left with h0 | h0
  · rcases h'.eq_or_eq hM' (isInv_inf hW'inv hXinv) bot_le inf_le_left with h0' | h0'
    · exfalso
      have hrkTop : rk ↥(⊤ : Subgroup V) = 2 * n := by
        have e := rk_sup_add_rk_inf W W'
        rw [hsup, hinf, rk_bot, add_zero, hrkW, hrkW'] at e
        omega
      have hXW : X ⊔ W = ⊤ := by
        apply eq_of_le_of_rk_le hV le_top
        have e := rk_sup_add_rk_inf X W
        rw [inf_comm, h0, rk_bot, add_zero, hrkX, hrkW] at e
        omega
      have hXW' : X ⊔ W' = ⊤ := by
        apply eq_of_le_of_rk_le hV le_top
        have e := rk_sup_add_rk_inf X W'
        rw [inf_comm, h0', rk_bot, add_zero, hrkX, hrkW'] at e
        omega
      obtain ⟨B₀, hB₀⟩ := exists_fixD_lt_fixN hn3
      set C : Subgroup (MulAut V) := (B₀.map π).map L.subtype with hC
      have hCL : C ≤ L := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have hpreC : pre π C = B₀ := by
        ext γ
        rw [mem_pre]
        constructor
        · rintro ⟨y, ⟨δ, hδ, rfl⟩, hy⟩
          have : δ = γ := hπ.1 (Subtype.ext hy)
          rw [← this]
          exact hδ
        · intro hγ
          exact ⟨π γ, ⟨γ, hγ, rfl⟩, rfl⟩
      have hCW : ∀ a ∈ C, ∀ x ∈ W, a x ∈ W := fun a ha => hWinv a (hCL ha)
      have hCW' : ∀ a ∈ C, ∀ x ∈ W', a x ∈ W' := fun a ha => hW'inv a (hCL ha)
      have hCX : ∀ a ∈ C, ∀ x ∈ X, a x ∈ X := fun a ha => hXinv a (hCL ha)
      have e1 : rkSub C ⊤ = rkSub C W + rkSub C W' := by
        rw [← hsup]
        exact rkSub_sup hCW hCW' hinf
      have e2 : rkSub C ⊤ = rkSub C X + rkSub C W := by
        rw [← hXW]
        exact rkSub_sup hCX hCW (by rw [inf_comm]; exact h0)
      have e3 : rkSub C ⊤ = rkSub C X + rkSub C W' := by
        rw [← hXW']
        exact rkSub_sup hCX hCW' (by rw [inf_comm]; exact h0')
      have e4 : rkSub C W = rkSub C W' := by omega
      rw [h.rkSub_eq hCL, h'.rkSub_eq hCL, hpreC] at e4
      have f1 := finrank_fixN_le B₀
      have f2 := finrank_fixD_add B₀
      rcases hMM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [fixM_mat, fixM_dmat] at e4
        omega
      · rw [fixM_mat, fixM_dmat] at e4
        omega
    · right
      have hle : W' ≤ X := inf_eq_left.1 h0'
      have hcard : Nat.card X ≤ Nat.card W' := by
        have e1 := card_eq_two_pow hV W'
        have e2 := card_eq_two_pow hV X
        rw [hrkW'] at e1
        rw [hrkX] at e2
        rw [e1, e2]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  · left
    have hle : W ≤ X := inf_eq_left.1 h0
    exact (Subgroup.eq_of_le_of_card_ge hle hcardX.le).symm



private theorem fix_of_comm_aux {W : Subgroup V}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M = mat ∨ M = dmat)
    (hn : 1 ≤ n) (h : RealM L W ⊥ π M) {c : MulAut V} (hcW : ∀ w ∈ W, c w ∈ W)
    (hcomm : ∀ x ∈ L, c * x = x * c) : ∀ w ∈ W, c w = w := by
  have hcard := rk_eq_of_realM_aux h
  obtain ⟨hπs, -, hLW, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have := (hβk w).1 hw
    exact Subtype.ext (by simpa using this)
  let e : ↥W ≃* Multiplicative (Fin n → ZMod 2) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let cW : ↥W →* ↥W := MonoidHom.codRestrict (c.toMonoidHom.comp W.subtype) W (fun w => hcW w w.2)
  let χ : Multiplicative (Fin n → ZMod 2) →* Multiplicative (Fin n → ZMod 2) :=
    β.comp (cW.comp e.symm.toMonoidHom)
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (χ (Multiplicative.ofAdd x))) (fun x y => by
      rw [ofAdd_add, map_mul, toAdd_mul])
  have hφ : ∀ w : ↥W, φ (Multiplicative.toAdd (β w)) =
      Multiplicative.toAdd (β ⟨c w, hcW w w.2⟩) := by
    intro w
    have : e.symm (β w) = w := e.symm_apply_apply w
    show Multiplicative.toAdd (χ (Multiplicative.ofAdd (Multiplicative.toAdd (β w)))) = _
    simp only [χ, ofAdd_toAdd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this]
    rfl
  have hφne : φ ≠ 0 := by
    intro h0
    have hWne : W ≠ ⊥ := fun hW => by rw [hW, rk_bot] at hcard; omega
    obtain ⟨⟨w, hwW⟩, hw1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hWne)
    have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
    have h1 := hφ ⟨w, hwW⟩
    rw [h0] at h1
    have h2 : β ⟨c w, hcW w hwW⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact h1.symm
    have h3 := (hβk _).1 h2
    have h4 : c w = 1 := by simpa using h3
    exact hw1 (c.injective (h4.trans (map_one c).symm))
  have hB : ∀ g : ↥(StatedSL n (ZMod 2)), ∃ g', M g' = mat g := by
    intro g
    rcases hM with rfl | rfl
    · exact ⟨g, rfl⟩
    · exact exists_dmat_eq (g : GL (Fin n) (ZMod 2))
  have hint : ∀ (γ : ↥(StatedSL n (ZMod 2))) (x : Fin n → ZMod 2),
      φ (M γ *ᵥ x) = M γ *ᵥ φ x := by
    intro γ x
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β w) := by rw [hw]; rfl
    have hπw : ((π γ : ↥L) : MulAut V) w ∈ W := hLW (π γ) w w.2
    have e1 := hβe γ w hπw
    have e2 := hβe γ ⟨c w, hcW w w.2⟩ (hLW (π γ) _ (hcW w w.2))
    have hcw : c (((π γ : ↥L) : MulAut V) w) = ((π γ : ↥L) : MulAut V) (c w) := by
      have := congrArg (fun φ : MulAut V => φ (w : V)) (hcomm _ (π γ).2)
      simpa [MulAut.mul_apply] using this
    rw [hx, ← e1, hφ ⟨_, hπw⟩]
    have e3 : (⟨c (((π γ : ↥L) : MulAut V) w), hcW _ hπw⟩ : ↥W) =
        ⟨((π γ : ↥L) : MulAut V) (c w), hLW (π γ) _ (hcW w w.2)⟩ := Subtype.ext hcw
    rw [show (⟨c (((π γ : ↥L) : MulAut V) (w : V)), hcW _ hπw⟩ : ↥W) =
        ⟨((π γ : ↥L) : MulAut V) (c w), hLW (π γ) _ (hcW w w.2)⟩ from e3, e2, hφ w]
  obtain ⟨P, hPφ, hPM⟩ := exists_conj_of_intertwine hφne hB hint
  have hP1 : P = 1 := by
    have hcent : ∀ g : ↥(StatedSL n (ZMod 2)), (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat g =
        mat g * (P : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      intro g
      obtain ⟨g', hg'⟩ := hB g
      rw [← hg']
      exact hPM g'
    have hz : ofGL P = 1 := by
      apply eq_one_of_forall_commute
      intro g
      apply mat_injective
      rw [mat_mul, mat_mul, mat_ofGL]
      exact hcent g
    have := congrArg Subtype.val hz
    exact this
  intro w hwW
  have h1 := hφ ⟨w, hwW⟩
  rw [← hPφ, hP1, Units.val_one, one_mulVec] at h1
  have h2 : β ⟨c w, hcW w hwW⟩ = β ⟨w, hwW⟩ := Multiplicative.toAdd.injective h1.symm
  have h3 := hβi h2
  exact congrArg Subtype.val h3

omit [Finite V] in
private theorem exp_two_aux {U₁ U₂ : Subgroup V}
    {M₁ M₂ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (h1 : RealM L U₁ ⊥ π M₁) (h2 : RealM L U₂ ⊥ π M₂) (hsup : U₁ ⊔ U₂ = ⊤) :
    ∀ v : V, v ^ 2 = 1 := by
  have hsq : ∀ z : Multiplicative (Fin n → ZMod 2), z ^ 2 = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    have h22 : (2 : ZMod 2) = 0 := by decide
    simp [h22]
  have hU : ∀ {X : Subgroup V} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)},
      RealM L X ⊥ π M → ∀ x ∈ X, x ^ 2 = 1 := by
    intro X M hX x hx
    obtain ⟨-, -, -, -, β, -, hβk, -⟩ := hX
    have h2 : β (⟨x, hx⟩ ^ 2) = 1 := by rw [map_pow]; exact hsq _
    have h3 := (hβk _).1 h2
    simpa using h3
  intro v
  have hv : v ∈ U₁ ⊔ U₂ := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [mul_pow, hU h1 x hx, hU h2 y hy, mul_one]

variable {U₁ U₂ : Subgroup V}

theorem perm_of_normalizer (hn : n = 4 ∨ n = 5) (hdir : IsIntDirect U₁ U₂ ⊤)
    (h1 : RealM L U₁ ⊥ π mat) (h2 : RealM L U₂ ⊥ π dmat) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) :
    (U₁.map g.toMonoidHom = U₁ ∧ U₂.map g.toMonoidHom = U₂) ∨
      (U₁.map g.toMonoidHom = U₂ ∧ U₂.map g.toMonoidHom = U₁) := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hπ : Function.Bijective π := ⟨h1.injective (Or.inl rfl), h1.1⟩
  let _ := hgL
  have hV := exp_two_aux h1 h2 hdir.1
  have hrk1 := rk_eq_of_realM_aux h1
  have hU₁ne : U₁ ≠ ⊥ := fun h => by rw [h, rk_bot] at hrk1; omega
  have hU₁₂ : U₁ ≠ U₂ := fun h => hU₁ne (by rw [← hdir.2, ← h, inf_idem])
  have c1 := map_eq_or_eq_aux hn3 hπ hV h1 h2 (Or.inl ⟨rfl, rfl⟩) hdir.1 hdir.2 hgL' (g := g)
  have c2 := map_eq_or_eq_aux hn3 hπ hV h2 h1 (Or.inr ⟨rfl, rfl⟩) (by rw [sup_comm]; exact hdir.1)
    (by rw [inf_comm]; exact hdir.2) hgL' (g := g)
  have hinj : Function.Injective (Subgroup.map g.toMonoidHom) :=
    Subgroup.map_injective (fun x y hxy => g.injective hxy)
  rcases c1 with c1 | c1
  · left
    refine ⟨c1, ?_⟩
    rcases c2 with c2 | c2
    · exact c2
    · exact absurd (hinj (c2.trans c1.symm)).symm hU₁₂
  · right
    refine ⟨c1, ?_⟩
    rcases c2 with c2 | c2
    · exact absurd (hinj (c2.trans c1.symm)).symm hU₁₂
    · exact c2


theorem mem_of_stab_pair (hn : n = 4 ∨ n = 5) (hdir : IsIntDirect U₁ U₂ ⊤)
    (h1 : RealM L U₁ ⊥ π mat) (h2 : RealM L U₂ ⊥ π dmat) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    (hg₁ : U₁.map g.toMonoidHom = U₁) (hg₂ : U₂.map g.toMonoidHom = U₂) : g ∈ L := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨l, hl, hinner⟩ := h1.exists_inner (Or.inl rfl) hn1 hgL hgL'
    (mem_stabSub_iff_map_eq.2 hg₁) (stabSub_bot_le ⊤ (Subgroup.mem_top g))
  set c : MulAut V := l⁻¹ * g with hc
  have hcomm : ∀ x ∈ L, c * x = x * c := by
    intro x hx
    have := hinner x hx
    calc c * x = l⁻¹ * (g * x * g⁻¹) * g := by rw [hc]; group
      _ = l⁻¹ * (l * x * l⁻¹) * g := by rw [this]
      _ = x * c := by rw [hc]; group
  have hg₁' : ∀ w ∈ U₁, g w ∈ U₁ := fun w hw => by
    rw [← hg₁]; exact ⟨w, hw, rfl⟩
  have hg₂' : ∀ w ∈ U₂, g w ∈ U₂ := fun w hw => by
    rw [← hg₂]; exact ⟨w, hw, rfl⟩
  have hcU₁ : ∀ w ∈ U₁, c w ∈ U₁ := fun w hw =>
    h1.2.2.1 ⟨l⁻¹, L.inv_mem hl⟩ (g w) (hg₁' w hw)
  have hcU₂ : ∀ w ∈ U₂, c w ∈ U₂ := fun w hw =>
    h2.2.2.1 ⟨l⁻¹, L.inv_mem hl⟩ (g w) (hg₂' w hw)
  have hf₁ := fix_of_comm_aux (Or.inl rfl) hn1 h1 hcU₁ hcomm
  have hf₂ := fix_of_comm_aux (Or.inr rfl) hn1 h2 hcU₂ hcomm
  have hc1 : c = 1 := by
    ext v
    have hv : v ∈ U₁ ⊔ U₂ := by rw [hdir.1]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, hf₁ x hx, hf₂ y hy]
    rfl
  have hgl : g = l := by
    have : l⁻¹ * g = 1 := hc1
    exact (inv_mul_eq_one.1 this).symm
  rw [hgl]
  exact hl

end SumSit

end CFSG.Quasithin.B5.Ln
