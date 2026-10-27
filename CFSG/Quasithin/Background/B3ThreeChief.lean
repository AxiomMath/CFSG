module

public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.B3ThreeGen

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {V : Type*} [CommGroup V]

@[expose] def IsChief (ρ : LG n →* MulAut V) (X Y : Subgroup V) : Prop :=
  X < Y ∧ ∀ Z : Subgroup V, IsInv ρ Z → X ≤ Z → Z ≤ Y → Z = X ∨ Z = Y

@[expose] def IsCentralFac (ρ : LG n →* MulAut V) (X Y : Subgroup V) : Prop :=
  ∀ g, ∀ y ∈ Y, ρ g y * y⁻¹ ∈ X

structure HasOneChief (n : ℕ) (ρ : LG n →* MulAut V) : Prop where
  chain : ∃ (m : ℕ) (S : ℕ → Subgroup V) (hS : ∀ i ≤ m, IsInv ρ (S i)) (j : ℕ) (hj : j < m),
    S 0 = ⊥ ∧ S m = ⊤ ∧ (∀ i < m, IsChief ρ (S i) (S (i + 1))) ∧
      (∀ i < m, i ≠ j → IsCentralFac ρ (S i) (S (i + 1))) ∧
      ∃ ψ : Sec (S (j + 1)) (S j) ≃* Mod.V n Mod.ut0,
        ∀ g x, ψ (secAct ρ (hS (j + 1) hj) (hS j hj.le) g x) = actL n Mod.ut0 g (ψ x)

theorem commutator_LG (hn : 5 ≤ n) : commutator (LG n) = ⊤ := by
  have := commutator_alternatingGroup_eq_top (α := Fin n) (by simpa using hn)
  exact this

theorem exists_nontrivial_action (hn : 5 ≤ n) :
    ∃ g : LG n, ∃ w : Mod.V n Mod.ut0, actL n Mod.ut0 g w ≠ w := by
  by_contra hcon
  push Not at hcon
  have hnt : Nontrivial (Mod.V n Mod.ut0) := (B3_1_1 hn).1
  obtain ⟨w, hw⟩ := exists_ne (1 : Mod.V n Mod.ut0)
  have hirr := (B3_1_1 hn).2 (Subgroup.zpowers w) (by
    intro g hg x hx
    have : actL n Mod.ut0 ⟨g, hg⟩ x = x := hcon ⟨g, hg⟩ x
    show actL n Mod.ut0 ⟨g, hg⟩ x ∈ _
    rw [this]
    exact hx)
  rcases hirr with h | h
  · apply hw
    have : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · have hc1 : Nat.card (Subgroup.zpowers w) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (V_sq _ _))
    rw [h, Subgroup.card_top] at hc1
    have hcard := card_eq_two_pow_of_isPGroup
      (isPGroup_two_of_sq_eq_one (V_sq' (n := n) Mod.ut0))
    rw [hcard, rk_Vut0 (by omega)] at hc1
    have h8 : 2 ^ 3 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8' : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    split_ifs at hc1
    · omega
    · omega

theorem secAct_mk {ρ : LG n →* MulAut V} {W N : Subgroup V} (hW : IsInv ρ W) (hN : IsInv ρ N)
    (g : LG n) (w : ↥W) :
    secAct ρ hW hN g (QuotientGroup.mk w) = QuotientGroup.mk (restrictEquiv ρ W hW g w) := rfl

theorem trivial_below (hn : 5 ≤ n) {ρ : LG n →* MulAut V} {m : ℕ} {S : ℕ → Subgroup V}
    {j : ℕ} (hjm : j < m) (h0 : S 0 = ⊥)
    (hcent : ∀ i < m, i ≠ j → IsCentralFac ρ (S i) (S (i + 1))) :
    ∀ i, i ≤ j → ∀ g, ∀ a ∈ S i, ρ g a = a := by
  have hperf := commutator_LG hn
  intro i
  induction i with
  | zero =>
    intro _ g a ha
    rw [h0, Subgroup.mem_bot] at ha
    rw [ha, map_one]
  | succ i ih =>
    intro hi g a ha
    have hcen := hcent i (by omega) (by omega)
    have hder : ∀ x, pder ρ a x = 1 := der_eq_one_of_trivial hperf (ρ := ρ) (N := S i)
      (fun g' x hx => ih (by omega) g' x hx) (isDer_pder ρ a) (fun x => hcen x a ha)
    have := hder g
    simp only [pder] at this
    exact mul_inv_eq_one.1 this

theorem mem_of_central {Γ : Type*} [Group Γ] (hperf : commutator Γ = ⊤) {ρ : Γ →* MulAut V}
    {X Y : Subgroup V} (hcen : ∀ g, ∀ y ∈ Y, ρ g y * y⁻¹ ∈ X) {d : Γ → V} (hd : IsDer ρ d)
    (hY : ∀ x, d x ∈ Y) (x : Γ) : d x ∈ X := by
  let f : Γ →* Sec Y X :=
    { toFun := fun x => QuotientGroup.mk ⟨d x, hY x⟩
      map_one' := by
        have : (⟨d 1, hY 1⟩ : ↥Y) = 1 := Subtype.ext hd.map_one
        show (QuotientGroup.mk ⟨d 1, hY 1⟩ : Sec Y X) = 1
        rw [this]
        rfl
      map_mul' := fun x y => by
        show (QuotientGroup.mk ⟨d (x * y), hY _⟩ : Sec Y X) =
          QuotientGroup.mk ⟨d x, hY x⟩ * QuotientGroup.mk ⟨d y, hY y⟩
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        show (d (x * y))⁻¹ * (d x * d y) ∈ X
        rw [hd x y]
        have h1 := hcen x (d y) (hY y)
        have e : (d x * ρ x (d y))⁻¹ * (d x * d y) = (ρ x (d y) * (d y)⁻¹)⁻¹ := by
          rw [mul_inv, mul_inv, inv_inv]
          calc (d x)⁻¹ * (ρ x (d y))⁻¹ * (d x * d y)
              = ((d x)⁻¹ * d x) * ((ρ x (d y))⁻¹ * d y) := by ac_rfl
            _ = (ρ x (d y))⁻¹ * d y := by rw [inv_mul_cancel, one_mul]
        rw [e]
        exact X.inv_mem h1 }
  have h := eq_one_of_perfect hperf f x
  have h' := (QuotientGroup.eq_one_iff (⟨d x, hY x⟩ : ↥Y)).1 h
  exact h'

theorem trivial_above (hn : 5 ≤ n) {ρ : LG n →* MulAut V} {m : ℕ} {S : ℕ → Subgroup V}
    {j : ℕ} (hm : S m = ⊤)
    (hcent : ∀ i < m, i ≠ j → IsCentralFac ρ (S i) (S (i + 1))) :
    ∀ k i, i + k = m → j < i → ∀ g v, ρ g v * v⁻¹ ∈ S i := by
  have hperf := commutator_LG hn
  intro k
  induction k with
  | zero =>
    intro i hi _ g v
    have : i = m := by omega
    rw [this, hm]
    exact Subgroup.mem_top _
  | succ k ih =>
    intro i hi hji g v
    have hih := ih (i + 1) (by omega) (by omega)
    have hcen := hcent i (by omega) (by omega)
    exact mem_of_central hperf (X := S i) (Y := S (i + 1)) hcen (isDer_pder ρ v)
      (fun x => hih x v) g

theorem threeStep_of_chief (hn : 5 ≤ n) {ρ : LG n →* MulAut V} (h : HasOneChief n ρ) :
    ∃ (A B : Subgroup V) (hA : IsInv ρ A) (hB : IsInv ρ B), ThreeStep ρ A B ∧
      ∃ ψ : Sec B A ≃* Mod.V n Mod.ut0,
        ∀ g x, ψ (secAct ρ hB hA g x) = actL n Mod.ut0 g (ψ x) := by
  obtain ⟨m, S, hS, j, hj, h0, hm, hchief, hcent, ψ, hψ⟩ := h.chain
  have hA := hS j hj.le
  have hB := hS (j + 1) hj
  refine ⟨S j, S (j + 1), hA, hB, ⟨(hchief j hj).1.le, hA, hB, ?_, ?_, ?_, ?_⟩, ψ, hψ⟩
  · exact trivial_below hn hj h0 hcent j le_rfl
  · exact trivial_above hn hm hcent (m - (j + 1)) (j + 1) (by omega) (by omega)
  · intro Z hZ hAZ hZB
    exact (hchief j hj).2 Z hZ hAZ hZB
  · obtain ⟨g, w, hgw⟩ := exists_nontrivial_action hn
    obtain ⟨x, rfl⟩ := ψ.surjective w
    induction x using QuotientGroup.induction_on with
    | H b =>
      refine ⟨g, b, b.2, fun hmem => hgw ?_⟩
      rw [← hψ, secAct_mk]
      congr 1
      rw [QuotientGroup.eq]
      show ((restrictEquiv ρ (S (j + 1)) hB g b)⁻¹ * b : ↥(S (j + 1))) ∈ (S j).subgroupOf _
      rw [Subgroup.mem_subgroupOf]
      have := (S j).inv_mem hmem
      simpa [restrictEquiv_apply, mul_comm] using this

end CFSG.Quasithin.B3
