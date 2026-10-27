module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch10SecQ4H3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {v : G}
  (hUe : IsElemAbelian 2 (conjClosure (Subgroup.zpowers v) H))

omit [Finite G] in
theorem pow_apply_eq_of_apply_eq {M : Type*} [Group M] {φ : MulAut M} {w : M} (h : φ w = w)
    (m : ℕ) : (φ ^ m) w = w := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem relIndex_eq_three {v₂ : G} {w₂ : IntMod (conjClosure (Subgroup.zpowers v) H) hUe}
    (hw₂ : w₂.val = v₂) {y : MulAut (IntMod (conjClosure (Subgroup.zpowers v) H) hUe)}
    (hyG : y ∈ autI hUe H) (hy2 : y w₂ = w₂) (hy3 : orderOf y = 3)
    (hy1 : y (centreI hUe) ≠ centreI hUe)
    (hodd : ∀ z ∈ autI hUe H, z w₂ = w₂ → Odd (orderOf z) → z ∈ Subgroup.zpowers y) :
    (Subgroup.centralizer (conjClosure (Subgroup.zpowers v)
        (oTwoUpper (H ⊓ Subgroup.centralizer ({v₂} : Set G))) : Set G)).relIndex
      (oTwoUpper (H ⊓ Subgroup.centralizer ({v₂} : Set G))) = 3 := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (Subgroup.zpowers v) H : Set G) :=
    le_normalizer_conjClosure _ H
  set Y := oTwoUpper (H ⊓ Subgroup.centralizer ({v₂} : Set G)) with hYdef
  have hYH : Y ≤ H := (oTwoUpper_le _).trans inf_le_left
  have hYN := hYH.trans hHU
  have hyH : Subgroup.zpowers y ≤ autI hUe H := (Subgroup.zpowers_le).mpr hyG
  have hfix : ∀ (g : Subgroup.normalizer (conjClosure (Subgroup.zpowers v) H : Set G)),
      (g : G) ∈ Subgroup.centralizer ({v₂} : Set G) → convI hUe g w₂ = w₂ := by
    intro g hg
    apply IntMod.val_injective
    rw [convI_apply_val, hw₂]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [h1, mul_inv_cancel_right]
  have hle : autI hUe Y ≤ Subgroup.zpowers y := by
    have hYW : Y ≤ preI hUe H hHU (Subgroup.zpowers y) := by
      rw [hYdef, oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxHC, hxo⟩
      refine (mem_preI hUe).2 ⟨hxHC.1, hodd _ (convI_mem_autI hUe hxHC.1 (hHU hxHC.1)) ?_ ?_⟩
      · exact hfix ⟨x, hHU hxHC.1⟩ hxHC.2
      · have h1 := orderOf_map_dvd (convHom hUe H hHU) ⟨x, hxHC.1⟩
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hxo h1
    calc autI hUe Y ≤ autI hUe (preI hUe H hHU (Subgroup.zpowers y)) := autI_mono hUe hYW
      _ = Subgroup.zpowers y := autI_preI hUe hyH
  obtain ⟨g, hgH, hgy⟩ := (mem_autI hUe).1 hyG
  have hgC : (g : G) ∈ Subgroup.centralizer ({v₂} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg IntMod.val (show convI hUe g w₂ = w₂ by rw [hgy]; exact hy2)
    rw [convI_apply_val, hw₂] at h1
    calc (g : G) * v₂ = ((g : G) * v₂ * (g : G)⁻¹) * g := by group
      _ = v₂ * g := by rw [h1]
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hdvd : 2 ^ e ∣ orderOf (g : G) := ⟨m, hn⟩
  have hodd' : Odd (orderOf ((g : G) ^ 2 ^ e)) := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hn, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hgY : (g : G) ^ 2 ^ e ∈ Y :=
    mem_oTwoUpper_of_odd ⟨H.pow_mem hgH _, Subgroup.pow_mem _ hgC _⟩ hodd'
  have himg : convI hUe ⟨(g : G) ^ 2 ^ e, hYN hgY⟩ = y ^ 2 ^ e := by
    rw [← hgy, ← map_pow]
    rfl
  have hcop : (orderOf y).Coprime (2 ^ e) := by
    rw [hy3]
    exact Nat.Coprime.pow_right e (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop.symm
  have hyY : y ∈ autI hUe Y := by
    rw [← hk, ← himg]
    exact Subgroup.pow_mem _ (convI_mem_autI hUe hgY _) _
  have heq : autI hUe Y = Subgroup.zpowers y :=
    le_antisymm hle ((Subgroup.zpowers_le).mpr hyY)
  have hcard : (Y ⊓ Subgroup.centralizer
      (conjClosure (Subgroup.zpowers v) H : Set G)).relIndex Y = 3 := by
    rw [← card_autI_eq hUe hYN, heq, Nat.card_zpowers, hy3]
  set C := Subgroup.centralizer (conjClosure (Subgroup.zpowers v) Y : Set G) with hC
  have hCU : Y ⊓ Subgroup.centralizer (conjClosure (Subgroup.zpowers v) H : Set G) ≤ C ⊓ Y :=
    fun x hx => ⟨Subgroup.centralizer_le (conjClosure_mono le_rfl hYH) hx.2, hx.1⟩
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hCU inf_le_right
  rw [hcard, Subgroup.inf_relIndex_right] at hmul
  have hne : C.relIndex Y ≠ 1 := by
    intro h1
    have hYC := Subgroup.relIndex_eq_one.mp h1
    have hv : v ∈ conjClosure (Subgroup.zpowers v) Y := le_conjClosure _ Y (Subgroup.mem_zpowers v)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hYC hgY) v hv
    apply hy1
    have hfixv : (y ^ 2 ^ e) (centreI hUe) = centreI hUe := by
      rw [← himg]
      apply IntMod.val_injective
      rw [convI_apply_val]
      show (g : G) ^ 2 ^ e * v * ((g : G) ^ 2 ^ e)⁻¹ = v
      rw [← hcomm, mul_inv_cancel_right]
    rw [← hk]
    exact pow_apply_eq_of_apply_eq hfixv k
  have hd : C.relIndex Y ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd h hne
  · exact h

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
