module

public import CFSG.Quasithin.EmptyFaithful.S153E56E8
public import CFSG.Quasithin.EmptyFaithful.S153E56E7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E56e

open CFSG.Quasithin.S153E

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem count_main (H : Hyps56 cx N₁ N₂ g s y) :
    ∃ (β : ↥(Jgp153 T M V₁ Mc y) →* SL(2, ZMod 2))
      (φ : ↥(pCoreOf 2 (Jgp153 T M V₁ Mc y)) →* MR (s + 1)),
      NatStr (Jgp153 T M V₁ Mc y) (pCoreOf 2 (Jgp153 T M V₁ Mc y)) (Egp153 T M V₁ Mc y) (s + 1) β φ ∧
        Nat.card (Egp153 T M V₁ Mc y) = 2 ^ (s + 3) := by
  obtain ⟨r, hr⟩ := H.iJ.nat
  obtain ⟨β, φ, h⟩ := exists_natStr hr
  have hrle := r_le H h
  have hFR : Fgp153 T M V₁ Mc y ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    rw [H.iJ.R_eq]
    exact le_sup_left
  have hXR : Xgp153 T M V₁ Mc y ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    rw [H.iJ.R_eq]
    exact le_sup_right
  have hFX : Fgp153 T M V₁ Mc y ⊓ Xgp153 T M V₁ Mc y = Egp153 T M V₁ Mc y := rfl
  have hsup : Fgp153 T M V₁ Mc y ⊔ Xgp153 T M V₁ Mc y = pCoreOf 2 (Jgp153 T M V₁ Mc y) :=
    H.iJ.R_eq.symm
  have hcard : Nat.card (Fgp153 T M V₁ Mc y) = Nat.card (Xgp153 T M V₁ Mc y) :=
    (card_conjSubgroup _ y).symm
  have hF := h.card_F hFR hXR hFX hsup hcard
  rw [card_F_eq H] at hF
  have hEle : Nat.card (Egp153 T M V₁ Mc y) ≤ 2 ^ (s + 3) := by
    have := card_E_sq_le H
    have h2 : 2 * 2 ^ (2 * s + 5) = 2 ^ (s + 3) * 2 ^ (s + 3) := by ring
    rw [h2] at this
    exact Nat.mul_self_le_mul_self_iff.1 this
  have hb_le : 2 ^ r ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) hrle
  have h1 : Nat.card (Egp153 T M V₁ Mc y) * 2 ^ r = 2 ^ (s + 3) * 2 ^ (s + 1) := by
    rw [← hF]
    ring
  have h2 : Nat.card (Egp153 T M V₁ Mc y) * 2 ^ r ≤ 2 ^ (s + 3) * 2 ^ r :=
    Nat.mul_le_mul_right _ hEle
  have h3 : 2 ^ (s + 3) * 2 ^ r ≤ 2 ^ (s + 3) * 2 ^ (s + 1) := Nat.mul_le_mul_left _ hb_le
  have hEa : Nat.card (Egp153 T M V₁ Mc y) = 2 ^ (s + 3) := by
    have h4 : 2 ^ (s + 3) * 2 ^ r ≤ Nat.card (Egp153 T M V₁ Mc y) * 2 ^ r := by
      rw [h1]
      exact h3
    have : Nat.card (Egp153 T M V₁ Mc y) * 2 ^ r = 2 ^ (s + 3) * 2 ^ r := le_antisymm h2 h4
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  have hr' : r = s + 1 := by
    have : 2 ^ (s + 3) * 2 ^ r = 2 ^ (s + 3) * 2 ^ (s + 1) := by
      rw [hEa] at h1
      exact h1
    have h5 : 2 ^ r = 2 ^ (s + 1) := Nat.eq_of_mul_eq_mul_left (by positivity) this
    exact Nat.pow_right_injective (le_refl 2) h5
  subst hr'
  exact ⟨β, φ, h, hEa⟩

theorem F_le_R (H : Hyps56 cx N₁ N₂ g s y) :
    Fgp153 T M V₁ Mc y ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
  rw [H.iJ.R_eq]
  exact le_sup_left

theorem X_le_R (H : Hyps56 cx N₁ N₂ g s y) :
    Xgp153 T M V₁ Mc y ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
  rw [H.iJ.R_eq]
  exact le_sup_right

theorem E_le_X (_H : Hyps56 cx N₁ N₂ g s y) : Egp153 T M V₁ Mc y ≤ Xgp153 T M V₁ Mc y :=
  inf_le_right

theorem X_inf_Q_aux (H : Hyps56 cx N₁ N₂ g s y) :
    Xgp153 T M V₁ Mc y ⊓ pCoreOf 2 Mc = Egp153 T M V₁ Mc y := by
  obtain ⟨β, φ, hN, hcardE⟩ := count_main H
  obtain ⟨a, hae, hac⟩ := cent_E_card H
  have hc : Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G)) = Nat.card (Egp153 T M V₁ Mc y) := by
    rw [hcardE] at hae ⊢
    have ha : a = 2 ^ (s + 2) := by
      have : a * 2 = 2 ^ (s + 2) * 2 := by
        rw [hae]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    rw [ha] at hac
    have : 2 ^ (s + 2) * Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
        Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G)) = 2 ^ (s + 2) * 2 ^ (s + 3) := by
      rw [hac]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hEeq : Egp153 T M V₁ Mc y = conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G) :=
    Subgroup.eq_of_le_of_card_ge (E_le_cent H) hc.le
  apply le_antisymm
  · rintro x ⟨hxX, hxQ⟩
    have hxU' : x ∈ conjSubgroup (UH153 T M V₁ Mc) y := by
      rw [X_eq H] at hxX
      exact hxX.1
    have hxC : x ∈ Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      have h1 : e * x * e⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T :=
        cx.hF.commutator_conjClosure_le e (E_le_U H he) x hxQ
      have h2 : e * x * e⁻¹ * x⁻¹ ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
        commutator_U'_mem cx (E_le_U' H he) hxU'
      have h3 : e * x * e⁻¹ * x⁻¹ ∈
          quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y := ⟨h1, h2⟩
      rw [Z_inf_Z' H, Subgroup.mem_bot] at h3
      calc e * x = (e * x * e⁻¹ * x⁻¹) * (x * e) := by group
        _ = x * e := by rw [h3, one_mul]
    have hmem : x ∈ conjSubgroup (UH153 T M V₁ Mc) y ⊓
        Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G) := ⟨hxU', hxC⟩
    rwa [← hEeq] at hmem
  · exact le_inf (E_le_X H) ((E_le_U H).trans (U_le_Q cx))

theorem isElemAbelianOfRank_of_card_56 {V : Type*} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x * x = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) :
    IsElemAbelianOfRank 2 n V := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  have hd : Module.finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hcard' : Nat.card (Additive V) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

theorem X_rank_aux (H : Hyps56 cx N₁ N₂ g s y) :
    IsElemAbelianOfRank 2 (s + 1)
      ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) := by
  obtain ⟨β, φ, hN, hcardE⟩ := count_main H
  have hXMc := X_le_Mc H
  have hcard : Nat.card ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) = 2 ^ (s + 1) := by
    have h1 := cx.hF.card_autOn_tilde hXMc
    show Nat.card ↥(autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) = _
    rw [h1, X_inf_Q_aux H]
    have e1 := Subgroup.relIndex_mul_card (Egp153 T M V₁ Mc y) (Xgp153 T M V₁ Mc y)
    rw [inf_eq_left.2 (E_le_X H), hcardE] at e1
    have hX : Nat.card (Xgp153 T M V₁ Mc y) = 2 ^ (2 * s + 4) := by
      show Nat.card (conjSubgroup (Fgp153 T M V₁ Mc y) y) = _
      rw [card_conjSubgroup, card_F_eq H]
    rw [hX] at e1
    have e2 : (Egp153 T M V₁ Mc y).relIndex (Xgp153 T M V₁ Mc y) * 2 ^ (s + 3) =
        2 ^ (s + 1) * 2 ^ (s + 3) := by
      rw [e1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) e2
  have hrho : ∀ n n' : ↥(S153E57.NZ T), (n : G) ∈ Xgp153 T M V₁ Mc y →
      (n' : G) ∈ Xgp153 T M V₁ Mc y →
      S153E57.rho cx n * S153E57.rho cx n' = S153E57.rho cx n' * S153E57.rho cx n := by
    intro n n' hn hn'
    have hUm : ((n * n' * (n' * n)⁻¹ : ↥(S153E57.NZ T)) : G) ∈ UH153 T M V₁ Mc := by
      have e : ((n * n' * (n' * n)⁻¹ : ↥(S153E57.NZ T)) : G) =
          (n : G) * n' * (n : G)⁻¹ * (n' : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        group
      rw [e]
      exact E_le_U H (hN.comm_mem (X_le_R H hn) (X_le_R H hn'))
    have h1 := S153E57.rho_eq_one_of_mem_U cx _ hUm
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 h1
  have hcomm : ∀ a b : ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)), a * b = b * a := by
    intro a b
    obtain ⟨n, hn, hna⟩ := (S153E57.mem_XStar_iff cx _ _).1 a.2
    obtain ⟨n', hn', hnb⟩ := (S153E57.mem_XStar_iff cx _ _).1 b.2
    apply Subtype.ext
    have := hrho n n' hn hn'
    rw [hna, hnb] at this
    exact this
  have hsq : ∀ a : ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)), a * a = 1 := by
    intro a
    obtain ⟨n, hn, hna⟩ := (S153E57.mem_XStar_iff cx _ _).1 a.2
    apply Subtype.ext
    have hUm : ((n * n : ↥(S153E57.NZ T)) : G) ∈ UH153 T M V₁ Mc := by
      have e : ((n * n : ↥(S153E57.NZ T)) : G) = (n : G) * n := rfl
      rw [e]
      exact E_le_U H (hN.sq_mem (X_le_R H hn))
    have h1 := S153E57.rho_eq_one_of_mem_U cx _ hUm
    rw [map_mul, hna] at h1
    exact h1
  exact isElemAbelianOfRank_of_card_56 hcomm hsq hcard

end Main

end S153E56e

end CFSG.Quasithin
