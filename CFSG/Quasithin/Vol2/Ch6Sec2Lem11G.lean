module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11E
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

theorem nonempty_mulEquiv_fin_zmod_two_ch611 {E : Type*} [CommGroup E] [Finite E]
    (hE : ∀ x : E, x ^ 2 = 1) {n : ℕ} (hcard : Nat.card E = 2 ^ n) :
    Nonempty (E ≃* Multiplicative (Fin n → ZMod 2)) := by
  have hA : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hE]
    rfl
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hA
  let _ : Fintype (Additive E) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive E) = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, ← Nat.card_congr Additive.ofMul, hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact ⟨AddEquiv.toMultiplicativeRight
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hfin).equivFun.toAddEquiv⟩

@[expose] def permCoordCh611 {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2) where
  toFun f := Multiplicative.ofAdd (fun i => Multiplicative.toAdd f (σ i))
  invFun f := Multiplicative.ofAdd (fun i => Multiplicative.toAdd f (σ.symm i))
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := rfl

theorem permCoordCh611_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Multiplicative (Fin n → ZMod 2))
    (i : Fin n) : Multiplicative.toAdd (permCoordCh611 σ f) i = Multiplicative.toAdd f (σ i) := rfl

theorem permCoordCh611_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    permCoordCh611 (σ ^ k) = (permCoordCh611 σ) ^ k := by
  induction k with
  | zero =>
    ext f i
    rfl
  | succ k ih =>
    rw [pow_succ', pow_succ, ← ih]
    ext f i
    rfl

theorem exists_mulAut_order_three_ch611 {E : Type*} [CommGroup E] [Finite E]
    (hE : ∀ x : E, x ^ 2 = 1) (h8 : 8 ≤ Nat.card E) : ∃ φ : MulAut E, orderOf φ = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact hE x⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_fin_zmod_two_ch611 hE hn
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  set σ := Equiv.swap a b * Equiv.swap a c with hσ
  have hσ3 : orderOf σ = 3 := (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf
  set ψ := permCoordCh611 σ with hψ
  have hψ3 : ψ ^ 3 = 1 := by
    rw [hψ, ← permCoordCh611_pow, ← hσ3, pow_orderOf_eq_one]
    ext f i
    rfl
  have hψ1 : ψ ≠ 1 := by
    intro h1
    have hσ1 : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hσ3
      omega
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hcon
      push Not at hcon
      exact hσ1 (Equiv.ext hcon)
    have := congrArg (fun φ : MulAut (Multiplicative (Fin n → ZMod 2)) =>
      Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single (σ i) 1))) i) h1
    simp only [hψ, permCoordCh611_apply, MulAut.one_apply, toAdd_ofAdd] at this
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hi.symm] at this
    exact one_ne_zero this
  refine ⟨MulAut.congr e.symm ψ, ?_⟩
  apply orderOf_eq_prime
  · rw [← map_pow, hψ3, map_one]
  · intro h1
    apply hψ1
    exact (MulAut.congr e.symm).injective (h1.trans (map_one _).symm)

namespace G31Out

variable {V : Type} [CommGroup V] {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V}
  (D : G31Out Gm X₀)

theorem exists_elemAbelian_27 [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (htop : g31V (orbitCh611 Gm X₀) = ⊤) (h3 : 3 ≤ D.s) :
    ∃ E : Subgroup (MulAut V), E ≤ Gm ∧ IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  classical
  have hV0sq : ∀ w : ↥D.V0, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  obtain ⟨φ, hφ⟩ := exists_mulAut_order_three_ch611 hV0sq D.eight
  obtain ⟨g₀, hg₀, hg₀φ⟩ := D.aut φ
  set i0 : Fin D.s := ⟨0, D.hs⟩ with hi0
  set i1 : Fin D.s := ⟨1, by omega⟩ with hi1
  set i2 : Fin D.s := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  obtain ⟨c₁, -, hc₁V, hc₁G⟩ := D.trans i0 i1
  obtain ⟨c₂, -, hc₂V, hc₂G⟩ := D.trans i0 i2
  have hconjG : ∀ (c : MulAut V) (k : Fin D.s),
      (g31G Gm (D.Δ i0)).map (MulAut.conj c).toMonoidHom = g31G Gm (D.Δ k) →
        c * g₀ * c⁻¹ ∈ g31G Gm (D.Δ k) := by
    intro c k hk
    rw [← hk]
    exact ⟨g₀, hg₀, rfl⟩
  set g₁ := c₁ * g₀ * c₁⁻¹ with hg₁def
  set g₂ := c₂ * g₀ * c₂⁻¹ with hg₂def
  have hg₁ : g₁ ∈ g31G Gm (D.Δ i1) := hconjG c₁ i1 hc₁G
  have hg₂ : g₂ ∈ g31G Gm (D.Δ i2) := hconjG c₂ i2 hc₂G
  have hpow0 : ∀ k : ℕ, ∀ w : ↥D.V0, (g₀ ^ k) (w : V) = (((φ ^ k) w : ↥D.V0) : V) := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply, hg₀φ]
  have hconjpow : ∀ (c : MulAut V) (k : ℕ) (w : V),
      ((c * g₀ * c⁻¹) ^ k) (c w) = c ((g₀ ^ k) w) := by
    intro c k w
    rw [conj_pow, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hmemV : ∀ (c : MulAut V) (k : Fin D.s), (D.V0).map c.toMonoidHom = g31V (D.Δ k) →
      ∀ w ∈ D.V0, c w ∈ g31V (D.Δ k) := by
    intro c k hk w hw
    rw [← hk]
    exact ⟨w, hw, rfl⟩
  have hφeq : ∀ a b : ℕ, a < 3 → b < 3 → (∀ w : ↥D.V0, (((φ ^ a) w : ↥D.V0) : V) =
      (((φ ^ b) w : ↥D.V0) : V)) → a = b := by
    intro a b ha hb hab
    have h1 : φ ^ a = φ ^ b := by
      ext w
      exact hab w
    rw [pow_eq_pow_iff_modEq, hφ] at h1
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    exact h1
  have hg₀3 : g₀ ^ 3 = 1 := by
    refine D.eq_one_of_fix htop ((g31G Gm (D.Δ i0)).pow_mem hg₀ 3) ?_
    intro v hv
    rw [hpow0 3 ⟨v, hv⟩, ← hφ, pow_orderOf_eq_one]
    rfl
  set E := Subgroup.closure ({g₀, g₁, g₂} : Set (MulAut V)) with hE
  have hg₀E : g₀ ∈ E := Subgroup.subset_closure (by simp)
  have hg₁E : g₁ ∈ E := Subgroup.subset_closure (by simp)
  have hg₂E : g₂ ∈ E := Subgroup.subset_closure (by simp)
  have hcomm : ({g₀, g₁, g₂} : Set (MulAut V)).Pairwise Commute := by
    have c01 := D.comm i0 i1 h01 g₀ hg₀ g₁ hg₁
    have c02 := D.comm i0 i2 h02 g₀ hg₀ g₂ hg₂
    have c12 := D.comm i1 i2 h12 g₁ hg₁ g₂ hg₂
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy
      | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
  have hEcomm : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hcomm
  refine ⟨E, ?_, ⟨hEcomm, ?_⟩, ?_⟩
  · rw [hE, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact D.g31G_le_Gm _ hg₀
    · exact D.g31G_le_Gm _ hg₁
    · exact D.g31G_le_Gm _ hg₂
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hg₀3
      · rw [hg₁def, conj_pow, hg₀3, mul_one, mul_inv_cancel]
      · rw [hg₂def, conj_pow, hg₀3, mul_one, mul_inv_cancel]
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have := hEcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, ihx, ihy, mul_one]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  ·
    let F : Fin 3 × Fin 3 × Fin 3 → ↥E := fun t =>
      ⟨g₀ ^ (t.1 : ℕ) * g₁ ^ (t.2.1 : ℕ) * g₂ ^ (t.2.2 : ℕ),
        E.mul_mem (E.mul_mem (E.pow_mem hg₀E _) (E.pow_mem hg₁E _)) (E.pow_mem hg₂E _)⟩
    have hF : Function.Injective F := by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      have h1 : g₀ ^ (a : ℕ) * g₁ ^ (b : ℕ) * g₂ ^ (c : ℕ) =
          g₀ ^ (a' : ℕ) * g₁ ^ (b' : ℕ) * g₂ ^ (c' : ℕ) := congrArg Subtype.val h
      have hfix : ∀ (g : MulAut V) (i j : Fin D.s), i ≠ j → g ∈ g31G Gm (D.Δ i) →
          ∀ k : ℕ, ∀ v ∈ g31V (D.Δ j), (g ^ k) v = v := fun g i j hij hg k v hv =>
        D.cent i j hij _ ((g31G Gm (D.Δ i)).pow_mem hg k) v hv
      have ha : (a : ℕ) = a' := by
        apply hφeq a a' a.2 a'.2
        intro w
        have h2 := congrArg (fun g : MulAut V => g (w : V)) h1
        simp only [MulAut.mul_apply] at h2
        rw [hfix g₂ i2 i0 h02.symm hg₂ _ w w.2, hfix g₁ i1 i0 h01.symm hg₁ _ w w.2,
          hfix g₂ i2 i0 h02.symm hg₂ _ w w.2, hfix g₁ i1 i0 h01.symm hg₁ _ w w.2,
          hpow0, hpow0] at h2
        exact h2
      have hb : (b : ℕ) = b' := by
        apply hφeq b b' b.2 b'.2
        intro w
        have hw1 := hmemV c₁ i1 hc₁V w w.2
        have h2 := congrArg (fun g : MulAut V => g (c₁ w)) h1
        simp only [MulAut.mul_apply] at h2
        rw [hfix g₂ i2 i1 h12.symm hg₂ _ _ hw1, hfix g₂ i2 i1 h12.symm hg₂ _ _ hw1] at h2
        have hm : ∀ k : ℕ, (g₁ ^ k) (c₁ w) ∈ g31V (D.Δ i1) := by
          intro k
          rw [hg₁def, hconjpow]
          exact hmemV c₁ i1 hc₁V _ (by rw [hpow0]; exact ((φ ^ k) w).2)
        rw [hfix g₀ i0 i1 h01 hg₀ _ _ (hm _), hfix g₀ i0 i1 h01 hg₀ _ _ (hm _), hg₁def,
          hconjpow, hconjpow] at h2
        have h3 := c₁.injective h2
        rw [hpow0, hpow0] at h3
        exact h3
      have hc : (c : ℕ) = c' := by
        apply hφeq c c' c.2 c'.2
        intro w
        have hw2 := hmemV c₂ i2 hc₂V w w.2
        have h2 := congrArg (fun g : MulAut V => g (c₂ w)) h1
        simp only [MulAut.mul_apply] at h2
        have hm : ∀ k : ℕ, (g₂ ^ k) (c₂ w) ∈ g31V (D.Δ i2) := by
          intro k
          rw [hg₂def, hconjpow]
          exact hmemV c₂ i2 hc₂V _ (by rw [hpow0]; exact ((φ ^ k) w).2)
        rw [hfix g₁ i1 i2 h12 hg₁ _ _ (hm _), hfix g₁ i1 i2 h12 hg₁ _ _ (hm _),
          hfix g₀ i0 i2 h02 hg₀ _ _ (hm _), hfix g₀ i0 i2 h02 hg₀ _ _ (hm _), hg₂def,
          hconjpow, hconjpow] at h2
        have h3 := c₂.injective h2
        rw [hpow0, hpow0] at h3
        exact h3
      rw [Fin.ext ha, Fin.ext hb, Fin.ext hc]
    have := Nat.card_le_card_of_injective F hF
    simpa [Nat.card_prod] using this

end G31Out

end CFSG.Quasithin.H13
