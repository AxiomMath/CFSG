module

public import CFSG.Quasithin.Background.FixVLattice

public section

namespace CFSG.Quasithin

namespace G6

variable {V : Type*} [CommGroup V]

theorem mem_commV_of_mem {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (v : V) :
    x v * v⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem commV_le_iff {X : Subgroup (MulAut V)} {U : Subgroup V} :
    commV X ≤ U ↔ ∀ x ∈ X, ∀ v : V, x v * v⁻¹ ∈ U :=
  CFSG.Quasithin.FixVLat.commV_le_iff

theorem commV_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : commV X ≤ commV Y :=
  commV_le_iff.2 fun _ hx v => mem_commV_of_mem (h hx) v

theorem apply_mem_commV {X : Subgroup (MulAut V)} {k : MulAut V}
    (hk : ∀ x ∈ X, k * x * k⁻¹ ∈ X) {w : V} (hw : w ∈ commV X) : k w ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hk hw

private theorem exists_character_of_isCoatom (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup V}
    (hH : IsCoatom H) : ∃ f : V →* ℤˣ, f ≠ 1 ∧ ∀ w ∈ H, f w = 1 := by
  classical
  have key : ∀ x y : V, x ∉ H → y ∉ H → x * y ∈ H := by
    intro x y hx hy
    have hlt : H < H ⊔ Subgroup.zpowers x := by
      refine lt_of_le_of_ne le_sup_left fun h => hx ?_
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have htop : H ⊔ Subgroup.zpowers x = ⊤ := hH.2 _ hlt
    have hy' : y ∈ H ⊔ Subgroup.zpowers x := htop ▸ Subgroup.mem_top y
    obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hxk : x ^ k = 1 ∨ x ^ k = x := by
      have hx2 : x ^ (2 : ℤ) = 1 := by simpa using hV x
      have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · left
        rw [hk, h0, add_zero, zpow_mul, hx2, one_zpow]
      · right
        rw [hk, h1, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]
    rcases hxk with h1 | h1
    · exact absurd (by simpa [h1] using hh) hy
    · rw [h1] at hy ⊢
      have : x * (h * x) = h := by
        calc x * (h * x) = h * (x * x) := mul_left_comm x h x
          _ = h * 1 := by rw [← pow_two, hV x]
          _ = h := mul_one h
      rw [this]
      exact hh
  let φ : V → ℤˣ := fun x => if x ∈ H then 1 else -1
  have hφ : ∀ x y : V, φ (x * y) = φ x * φ y := by
    intro x y
    by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
    · simp [φ, hx, hy, H.mul_mem hx hy]
    · have : x * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem hx) h)
      simp [φ, hx, hy, this]
    · have : x * y ∉ H := fun h => hx (by simpa using H.mul_mem h (H.inv_mem hy))
      simp [φ, hx, hy, this]
    · simp [φ, hx, hy, key x y hx hy]
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hH.1 (eq_top_iff.2 fun x _ => hcon x)
  refine ⟨{ toFun := φ, map_one' := by simp [φ], map_mul' := hφ }, ?_, ?_⟩
  · intro h
    have := DFunLike.congr_fun h v
    simp [φ, hv] at this
  · intro w hw
    simp [φ, hw]

theorem exists_character_of_ne_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V}
    (hW : W ≠ ⊤) : ∃ f : V →* ℤˣ, f ≠ 1 ∧ ∀ w ∈ W, f w = 1 := by
  obtain ⟨H, hH, hWH⟩ := (eq_top_or_exists_le_coatom W).resolve_left hW
  obtain ⟨f, hf1, hfH⟩ := exists_character_of_isCoatom hV hH
  exact ⟨f, hf1, fun w hw => hfH w (hWH hw)⟩

private def chars (W : Subgroup V) : Subgroup (V →* ℤˣ) where
  carrier := {f | ∀ w ∈ W, f w = 1}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {f g} hf hg w hw => by simp [hf w hw, hg w hw]
  inv_mem' := fun {f} hf w hw => by simp [hf w hw]

private theorem mem_chars {W : Subgroup V} {f : V →* ℤˣ} :
    f ∈ chars W ↔ ∀ w ∈ W, f w = 1 := Iff.rfl

private def charAct (W : Subgroup V) (K : Subgroup (MulAut V))
    (hW : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W) : K →* Equiv.Perm (chars W) where
  toFun k :=
    { toFun := fun f => ⟨f.1.comp (k : MulAut V)⁻¹.toMonoidHom, fun w hw => by
        simpa using f.2 _ (hW _ (K.inv_mem k.2) w hw)⟩
      invFun := fun f => ⟨f.1.comp (k : MulAut V).toMonoidHom, fun w hw => by
        simpa using f.2 _ (hW _ k.2 w hw)⟩
      left_inv := fun f => Subtype.ext (MonoidHom.ext fun v => by simp)
      right_inv := fun f => Subtype.ext (MonoidHom.ext fun v => by simp) }
  map_one' := by
    ext f v
    simp
  map_mul' := fun k l => by
    ext f v
    simp

private theorem charAct_apply (W : Subgroup V) (K : Subgroup (MulAut V))
    (hW : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W) (k : K) (f : chars W) (v : V) :
    (charAct W K hW k f).1 v = f.1 ((k : MulAut V)⁻¹ v) := rfl

theorem commV_ne_top_of_two_power [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {K N : Subgroup (MulAut V)}
    (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hp : ∀ k ∈ K, ∃ m : ℕ, k ^ 2 ^ m ∈ N) (hN : commV N ≠ ⊤) :
    commV K ≠ ⊤ := by
  classical
  set W := commV N with hWdef
  have hWinv : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W := fun k hk w hw =>
    apply_mem_commV (X := N) (fun x hx => hNn k hk x hx) hw
  let ρ := charAct W K hWinv
  have hρN : ∀ (n : K), (n : MulAut V) ∈ N → ρ n = 1 := by
    intro n hn
    refine Equiv.ext fun f => Subtype.ext (MonoidHom.ext fun v => ?_)
    rw [show (ρ n f).1 v = f.1 ((n : MulAut V)⁻¹ v) from rfl]
    have h1 : f.1 (((n : MulAut V)⁻¹ v) * v⁻¹) = 1 :=
      f.2 _ (mem_commV_of_mem (N.inv_mem hn) v)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  let Q : Subgroup (Equiv.Perm (chars W)) := ρ.range
  have hQ : IsPGroup 2 Q := by
    intro q
    obtain ⟨k, hk⟩ := q.2
    obtain ⟨m, hm⟩ := hp k k.2
    refine ⟨m, ?_⟩
    apply Subtype.ext
    have : ρ (k ^ 2 ^ m) = 1 := hρN _ (by simpa using hm)
    rw [map_pow] at this
    simpa [hk] using this
  obtain ⟨f₀, hf₀1, hf₀W⟩ := exists_character_of_ne_top hV hN
  have hf₀ : f₀ ∈ chars W := hf₀W
  have heven : 2 ∣ Nat.card (chars W) := by
    have hsq : (⟨f₀, hf₀⟩ : chars W) ^ 2 = 1 := by
      apply Subtype.ext
      ext v
      simp [pow_two]
    have hne : (⟨f₀, hf₀⟩ : chars W) ≠ 1 := fun h => hf₀1 (congrArg Subtype.val h)
    have := orderOf_eq_prime hsq hne
    rw [← this]
    exact orderOf_dvd_natCard _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hQ.card_modEq_card_fixedPoints (chars W)
  obtain ⟨f, hfix, hf1⟩ : ∃ f : chars W, f ∈ MulAction.fixedPoints Q (chars W) ∧ f ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hone : (1 : chars W) ∈ MulAction.fixedPoints Q (chars W) := by
      intro q
      obtain ⟨q', k, hk⟩ := q
      show q' 1 = 1
      rw [← hk]
      exact Subtype.ext (MonoidHom.ext fun v => by
        show ((1 : chars W).1) (((k : MulAut V))⁻¹ v) = _
        simp)
    have hcard : Nat.card (MulAction.fixedPoints Q (chars W)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, hone⟩⟩⟩
      rw [hcon a a.2, hcon b b.2]
    rw [hcard] at hmod
    unfold Nat.ModEq at hmod
    omega
  refine fun hK => hf1 (Subtype.ext (MonoidHom.ext fun v => ?_))
  have hk : ∀ k ∈ K, ∀ v : V, f.1 (k v) = f.1 v := by
    intro k hk v
    have h1 : ρ ⟨k⁻¹, K.inv_mem hk⟩ f = f := hfix ⟨ρ ⟨k⁻¹, K.inv_mem hk⟩, ⟨_, rfl⟩⟩
    have h2 := congrArg (fun g : chars W => g.1 v) h1
    simpa [ρ, charAct_apply] using h2
  have hker : commV K ≤ f.1.ker := by
    rw [commV_le_iff]
    intro k hk' v
    rw [MonoidHom.mem_ker, map_mul, hk k hk' v, map_inv, mul_inv_cancel]
  have hv : v ∈ commV K := by
    rw [hK]
    exact Subgroup.mem_top v
  simpa using hker hv

end G6

end CFSG.Quasithin
