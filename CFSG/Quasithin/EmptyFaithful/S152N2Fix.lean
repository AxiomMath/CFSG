module

public import CFSG.Quasithin.EmptyFaithful.S152N2Lin

public section

namespace CFSG.Quasithin

namespace S152N2

variable {V : Type*} [CommGroup V]

@[expose] def restrictPerm (P : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) : P →* Equiv.Perm W where
  toFun g :=
    { toFun := fun w => ⟨(g : MulAut V) w, hW g g.2 w w.2⟩
      invFun := fun w => ⟨(g : MulAut V)⁻¹ w, hW g⁻¹ (P.inv_mem g.2) w w.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem card_modEq_card_inf_fixV [Finite V] {P : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {W : Subgroup V} (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) :
    Nat.card W ≡ Nat.card ↥(W ⊓ fixV P) [MOD p] := by
  let _ : MulAction P W := MulAction.compHom W (restrictPerm P W hW)
  have h := IsPGroup.card_modEq_card_fixedPoints (α := W) hP
  have hset : Nat.card (MulAction.fixedPoints P W) = Nat.card ↥(W ⊓ fixV P) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun w => ⟨(w.1 : V), w.1.2, fun x hx => by
          have := w.2 ⟨x, hx⟩
          exact congrArg Subtype.val this⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun g => by
          apply Subtype.ext
          exact v.2.2 g g.2⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun v => by ext; rfl }
  rw [hset] at h
  exact h

theorem isPGroup_zpowers_of_pow_prime {Γ : Type*} [Group Γ] {x : Γ} {p : ℕ} [Fact p.Prime]
    (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Fact.out).mp hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)

theorem card_eq_one_or_sixteen {W : Subgroup V} [Finite V] (hcard : Nat.card V = 16)
    (h : Nat.card W ≡ 1 [MOD 5]) : Nat.card W = 1 ∨ Nat.card W = 16 := by
  have hdvd : Nat.card W ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card W
    rw [hcard] at this
    simpa using this
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hci] at h ⊢
  interval_cases i <;> simp [Nat.ModEq] at h ⊢

theorem fixV_zpowers_eq_bot_of_pow_five [Finite V] (hcard : Nat.card V = 16)
    {x : MulAut V} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) : fixV (Subgroup.zpowers x) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP := isPGroup_zpowers_of_pow_prime hx5
  have h := card_modEq_card_inf_fixV hP (W := ⊤) (fun g _ w _ => Subgroup.mem_top _)
  rw [top_inf_eq, Subgroup.card_top, hcard] at h
  have h' : Nat.card (fixV (Subgroup.zpowers x)) ≡ 1 [MOD 5] := by
    have : (16 : ℕ) ≡ 1 [MOD 5] := by decide
    exact h.symm.trans this
  rcases card_eq_one_or_sixteen hcard h' with h1 | h16
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hx1
    have hfull : fixV (Subgroup.zpowers x) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, h16])
    ext v
    have : v ∈ fixV (Subgroup.zpowers x) := by rw [hfull]; exact Subgroup.mem_top v
    exact this x (Subgroup.mem_zpowers x)

theorem fixV_zpowers_eq_bot_of_commute [Finite V] (hcard : Nat.card V = 16) {w y : MulAut V}
    (hw5 : w ^ 5 = 1) (hw1 : w ≠ 1) (hy1 : y ≠ 1) (hcomm : w * y = y * w) :
    fixV (Subgroup.zpowers y) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP := isPGroup_zpowers_of_pow_prime hw5
  have hfw := fixV_zpowers_eq_bot_of_pow_five hcard hw5 hw1
  have hW : ∀ g ∈ Subgroup.zpowers w, ∀ v ∈ fixV (Subgroup.zpowers y),
      g v ∈ fixV (Subgroup.zpowers y) := by
    intro g hg v hv
    rw [mem_fixV_zpowers_iff] at hv ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hck : (w ^ k) * y = y * (w ^ k) := (Commute.zpow_left hcomm k)
    have := congrArg (fun φ : MulAut V => φ v) hck
    simp only [MulAut.mul_apply] at this
    rw [← this, hv]
  have h := card_modEq_card_inf_fixV hP hW
  rw [hfw, inf_bot_eq, Subgroup.card_bot] at h
  rcases card_eq_one_or_sixteen hcard h with h1 | h16
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hy1
    have hfull : fixV (Subgroup.zpowers y) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, h16])
    ext v
    have : v ∈ fixV (Subgroup.zpowers y) := by rw [hfull]; exact Subgroup.mem_top v
    exact this y (Subgroup.mem_zpowers y)

theorem eq_one_of_fixes_orbit [Finite V] (hcard : Nat.card V = 16) {w c : MulAut V}
    (hw5 : w ^ 5 = 1) (hw1 : w ≠ 1) (hc : c * w = w * c) {v : V} (hv1 : v ≠ 1)
    (hcv : c v = v) : c = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP := isPGroup_zpowers_of_pow_prime hw5
  have hfw := fixV_zpowers_eq_bot_of_pow_five hcard hw5 hw1
  set S : Set V := {u | ∃ k : ℤ, u = (w ^ k) v} with hS
  set W : Subgroup V := Subgroup.closure S with hW
  have hvW : v ∈ W := Subgroup.subset_closure ⟨0, by simp⟩
  have hWinv : ∀ g ∈ Subgroup.zpowers w, ∀ u ∈ W, g u ∈ W := by
    intro g hg u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      apply Subgroup.subset_closure
      refine ⟨m + k, ?_⟩
      rw [zpow_add, MulAut.mul_apply]
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact W.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact W.inv_mem hx
  have hcfix : ∀ u ∈ W, c u = u := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hck : c * w ^ k = w ^ k * c := (Commute.zpow_right hc k)
      have := congrArg (fun φ : MulAut V => φ v) hck
      simp only [MulAut.mul_apply] at this
      rw [this, hcv]
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hmod := card_modEq_card_inf_fixV hP hWinv
  have hinf : W ⊓ fixV (Subgroup.zpowers w) = ⊥ := by rw [hfw, inf_bot_eq]
  rw [hinf, Subgroup.card_bot] at hmod
  rcases card_eq_one_or_sixteen hcard hmod with h1 | h16
  · exfalso
    have hWbot : W = ⊥ := Subgroup.card_eq_one.mp h1
    apply hv1
    have := hvW
    rw [hWbot, Subgroup.mem_bot] at this
    exact this
  · have hfull : W = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard, h16])
    ext u
    have hu : u ∈ W := by rw [hfull]; exact Subgroup.mem_top u
    exact hcfix u hu

theorem exists_fixed_of_involution [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {c : MulAut V} (hc : c * c = 1) : ∃ v : V, v ≠ 1 ∧ c v = v := by
  have h1 := card_fixV_mul_card_commV hc
  have h2 : Nat.card (commV (Subgroup.zpowers c)) ≤ Nat.card (fixV (Subgroup.zpowers c)) :=
    Subgroup.card_le_of_le (commV_le_fixV_of_sq hV hc)
  rw [hcard] at h1
  have h3 : 4 ≤ Nat.card (fixV (Subgroup.zpowers c)) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (fixV (Subgroup.zpowers c)) * Nat.card (commV (Subgroup.zpowers c)) ≤ 3 * 3 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hne : fixV (Subgroup.zpowers c) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨v, fun h => hv1 (Subtype.ext h), ?_⟩
  exact hv c (Subgroup.mem_zpowers c)

theorem card_le_fifteen [Finite V] (hcard : Nat.card V = 16) {w : MulAut V} (hw5 : w ^ 5 = 1)
    (hw1 : w ≠ 1) {C : Subgroup (MulAut V)} (hC : ∀ c ∈ C, c * w = w * c) :
    Nat.card C ≤ 15 := by
  have hex : ∃ v : V, v ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => by rw [h a, h b]⟩, ⟨1⟩⟩
    omega
  obtain ⟨v₀, hv₀⟩ := hex
  let f : C → {v : V // v ≠ 1} := fun c => ⟨(c : MulAut V) v₀, fun h => by
    have : (c : MulAut V) v₀ = 1 := h
    rw [← map_one (c : MulAut V)] at this
    exact hv₀ ((c : MulAut V).injective this)⟩
  have hf : Function.Injective f := by
    intro c c' h
    have h1 : (c : MulAut V) v₀ = (c' : MulAut V) v₀ := congrArg Subtype.val h
    have h2 : ((c' : MulAut V)⁻¹ * c) v₀ = v₀ := by
      rw [MulAut.mul_apply, h1]
      simp
    have hcomm : ((c' : MulAut V)⁻¹ * c) * w = w * ((c' : MulAut V)⁻¹ * c) := by
      have h3 := hC c c.2
      have h4 : (c' : MulAut V) * w = w * (c' : MulAut V) := hC c' c'.2
      have h5 : (c' : MulAut V)⁻¹ * w = w * (c' : MulAut V)⁻¹ := by
        calc (c' : MulAut V)⁻¹ * w = (c' : MulAut V)⁻¹ * (w * c') * (c' : MulAut V)⁻¹ := by group
          _ = (c' : MulAut V)⁻¹ * (c' * w) * (c' : MulAut V)⁻¹ := by rw [h4]
          _ = w * (c' : MulAut V)⁻¹ := by group
      calc (c' : MulAut V)⁻¹ * c * w = (c' : MulAut V)⁻¹ * (c * w) := by group
        _ = (c' : MulAut V)⁻¹ * (w * c) := by rw [h3]
        _ = ((c' : MulAut V)⁻¹ * w) * c := by group
        _ = (w * (c' : MulAut V)⁻¹) * c := by rw [h5]
        _ = w * ((c' : MulAut V)⁻¹ * c) := by group
    have := eq_one_of_fixes_orbit hcard hw5 hw1 hcomm hv₀ h2
    apply Subtype.ext
    exact (inv_mul_eq_one.mp this).symm
  have hcardS : Nat.card {v : V // v ≠ 1} ≤ 15 := by
    have : Fintype V := Fintype.ofFinite V
    classical
    have h1 : Fintype.card {v : V // v ≠ 1} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun v => v ≠ 1) (x := 1) (by simp)
    have h2 : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
    have h3 : Nat.card {v : V // v ≠ 1} = Fintype.card {v : V // v ≠ 1} :=
      Nat.card_eq_fintype_card
    omega
  calc Nat.card C ≤ Nat.card {v : V // v ≠ 1} := Nat.card_le_card_of_injective f hf
    _ ≤ 15 := hcardS

end S152N2

end CFSG.Quasithin
