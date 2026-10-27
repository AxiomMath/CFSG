module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type} [Group G] [Finite G]

section Word

private def b5_dih_word {S : Type*} [Group S] (r s : S) (M : ℕ) : DihedralGroup M → S
  | .r j => r ^ j.val
  | .sr j => s * r ^ j.val

private theorem b5_dih_pow_val_add {S : Type*} [Monoid S] {M : ℕ} [NeZero M] {c : S}
    (hc : c ^ M = 1) (x y : ZMod M) : c ^ (x + y).val = c ^ x.val * c ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hc

private theorem b5_dih_pow_val_sub_mul {S : Type*} [Monoid S] {M : ℕ} [NeZero M] {c : S}
    (hc : c ^ M = 1) (x y : ZMod M) : c ^ (y - x).val * c ^ x.val = c ^ y.val := by
  rw [← b5_dih_pow_val_add hc, sub_add_cancel]

private theorem b5_dih_conj_pow {S : Type*} [Group S] {r s : S} (hs : s * s = 1)
    (hrel : s * r * s = r⁻¹) (n : ℕ) : s * r ^ n * s = (r ^ n)⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h := conj_pow (a := s) (b := r) (i := n)
  rw [hsinv, hrel, inv_pow] at h
  exact h.symm

private def b5_dih_wordHom {S : Type*} [Group S] (r s : S) (M : ℕ) [NeZero M] (hr : r ^ M = 1)
    (hs : s * s = 1) (hrel : s * r * s = r⁻¹) : DihedralGroup M →* S where
  toFun := b5_dih_word r s M
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [b5_dih_word]
  map_mul' := by
    have hcomm : ∀ n : ℕ, r ^ n * s = s * (r ^ n)⁻¹ := by
      intro n
      rw [← b5_dih_conj_pow hs hrel n, ← mul_assoc, ← mul_assoc, hs, one_mul]
    have hsub : ∀ x y : ZMod M, r ^ (y - x).val = (r ^ x.val)⁻¹ * r ^ y.val := by
      intro x y
      rw [eq_inv_mul_iff_mul_eq, (Commute.pow_pow_self r _ _).eq, b5_dih_pow_val_sub_mul hr]
    intro a b
    cases a with
    | r x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.r_mul_r, b5_dih_word, b5_dih_pow_val_add hr]
      | sr y =>
        simp only [DihedralGroup.r_mul_sr, b5_dih_word, hsub, ← mul_assoc, hcomm]
    | sr x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.sr_mul_r, b5_dih_word, b5_dih_pow_val_add hr, mul_assoc]
      | sr y =>
        simp only [DihedralGroup.sr_mul_sr, b5_dih_word, hsub]
        rw [show s * r ^ x.val * (s * r ^ y.val) = (s * r ^ x.val * s) * r ^ y.val by group,
          b5_dih_conj_pow hs hrel]

private theorem b5_dih_wordHom_bijective {S : Type*} [Group S] {r s : S} {M : ℕ} [NeZero M]
    [Finite S] (hM : 2 ≤ M) (hcard : Nat.card S = 2 * M)
    (hgen : Subgroup.closure {r, s} = ⊤) (hr : r ^ M = 1) (hs : s * s = 1)
    (hrel : s * r * s = r⁻¹) : Function.Bijective (b5_dih_wordHom r s M hr hs hrel) := by
  have : Fact (1 < M) := ⟨by omega⟩
  have hsurj : Function.Surjective (b5_dih_wordHom r s M hr hs hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨DihedralGroup.r 1, by simp [b5_dih_wordHom, b5_dih_word, ZMod.val_one]⟩
    · exact ⟨DihedralGroup.sr 0, by simp [b5_dih_wordHom, b5_dih_word]⟩
  exact hsurj.bijective_of_nat_card_le (by rw [DihedralGroup.nat_card, hcard])

end Word

theorem nonempty_mulEquiv_dihedralGroup_of_inverts {H X : Subgroup G} {p : ℕ} (hp : p.Prime)
    {a : G} (hXcard : Nat.card X = p) (hH : H = X ⊔ Subgroup.zpowers a) (ha : a * a = 1)
    (haX : a ∉ X) (hinv : ∀ x ∈ X, a * x * a⁻¹ = x⁻¹) :
    Nonempty (↥H ≃* DihedralGroup p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ha_ne_one : a ≠ 1 := by
    intro h
    exact haX (h ▸ X.one_mem)
  have hX_ne_bot : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card X = 1 := by rw [hbot, Subgroup.card_bot]
    exact hp.ne_one (by rw [← hXcard, h1])
  haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX_ne_bot
  obtain ⟨x, hx, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial X
  have horder_dvd : orderOf x ∣ p := by
    rw [← hXcard]
    exact Subgroup.orderOf_dvd_natCard X hx
  have horder_ne_one : orderOf x ≠ 1 := by
    intro h
    exact hxne (orderOf_eq_one_iff.mp h)
  have horder : orderOf x = p :=
    (hp.eq_one_or_self_of_dvd (orderOf x) horder_dvd).resolve_left horder_ne_one
  have hxpow : x ^ p = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one x
  have hzpowersX : Subgroup.zpowers x = X := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hx)
    rw [Nat.card_zpowers, horder]
    exact le_of_eq hXcard
  have ha_sq : a ^ 2 = 1 := by rw [pow_two, ha]
  have ha_order : orderOf a = 2 := orderOf_eq_prime ha_sq ha_ne_one
  have hzpow_two : ∀ k : ℤ, a ^ k = 1 ∨ a ^ k = a := by
    intro k
    rw [zpow_eq_zpow_emod k (show a ^ (2 : ℤ) = 1 by simpa using ha_sq)]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
    · left; simp
    · right; simp
  have hdisj : Subgroup.zpowers a ⊓ X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hza, hzX⟩ := hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hza
    rcases hzpow_two k with h | h
    · rw [← hk, h]
    · exfalso
      exact haX (by rw [← h, hk]; exact hzX)
  have ha_norm : a ∈ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    rw [hinv y hy]
    exact X.inv_mem hy
  have hzp_norm : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr ha_norm
  have hrel2 : X.relIndex (Subgroup.zpowers a) = 2 := by
    rw [← Subgroup.inf_relIndex_right X (Subgroup.zpowers a), inf_comm, hdisj,
      Subgroup.relIndex_bot_left, Nat.card_zpowers a, ha_order]
  have hrel1 : X.relIndex (Subgroup.zpowers a ⊔ X) = X.relIndex (Subgroup.zpowers a) :=
    CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hzp_norm
  have hXH : X ≤ H := by rw [hH]; exact le_sup_left
  have hsup : Subgroup.zpowers a ⊔ X = H := by rw [sup_comm, ← hH]
  have hidx : (X.subgroupOf H).index = 2 := by
    rw [← hsup]
    exact hrel1.trans hrel2
  have hHcard : Nat.card ↥H = 2 * p := by
    have hcardX : Nat.card (X.subgroupOf H) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXcard]
    calc Nat.card ↥H = Nat.card (X.subgroupOf H) * (X.subgroupOf H).index :=
          (Subgroup.card_mul_index (X.subgroupOf H)).symm
      _ = p * 2 := by rw [hcardX, hidx]
      _ = 2 * p := by ring
  have haH : a ∈ H := by rw [hH]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  set r : ↥H := ⟨x, hXH hx⟩ with hr
  set s : ↥H := ⟨a, haH⟩ with hs
  have hrp : r ^ p = 1 := by
    rw [hr]
    apply Subtype.ext
    simpa using hxpow
  have hss : s * s = 1 := by
    rw [hs]
    apply Subtype.ext
    simpa using ha
  have hsrs : s * r * s = r⁻¹ := by
    rw [hr, hs]
    apply Subtype.ext
    simpa [ha_inv] using hinv x hx
  have hclosure : Subgroup.closure ({(x : G), a} : Set G) = H := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure x,
      ← Subgroup.zpowers_eq_closure a, hzpowersX, ← hH]
  have hgen : Subgroup.closure ({r, s} : Set ↥H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair, hr, hs]
    change Subgroup.closure ({(x : G), a} : Set G) = H
    exact hclosure
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥H := inferInstance
  have hbij : Function.Bijective (b5_dih_wordHom r s p hrp hss hsrs) :=
    b5_dih_wordHom_bijective (r := r) (s := s) (M := p) hp.two_le hHcard hgen hrp hss hsrs
  exact ⟨(MulEquiv.ofBijective _ hbij).symm⟩

end CFSG.LocalAnalysis.WeakClosure81
