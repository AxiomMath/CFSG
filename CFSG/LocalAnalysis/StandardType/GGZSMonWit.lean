module

public import CFSG.LocalAnalysis.StandardType.GGZSMonShape
import CFSG.LocalAnalysis.StandardType.GGZSMonCount
import CFSG.LocalAnalysis.StandardType.GGZSMonFrame

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma exists_perm_apply_eq_pair {n : ℕ} {i j y w : Fin n}
    (hij : i ≠ j) (hyw : y ≠ w) :
    ∃ π : Equiv.Perm (Fin n), π i = y ∧ π j = w := by
  have hf : Function.Injective (![i, j] : Fin 2 → Fin n) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hg : Function.Injective (![y, w] : Fin 2 → Fin n) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (![i, j] : Fin 2 → Fin n)
    (![y, w] : Fin 2 → Fin n) hf hg
  exact ⟨π, by simpa using hπ 0, by simpa using hπ 1⟩

private lemma not_commute_of_diagonal_product {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    {r t : U ≃ₗ[ZMod p] U} {x y : Fin n} {ζ : (ZMod p)ˣ} (hζ : ζ ^ 2 ≠ 1)
    (hrefl : IsRefl p r) (hrt_diag : IsDiagonal b (r * t) (pairUnit p x y ζ))
    (ht2 : t * t = 1) : ¬ Commute t r := by
  classical
  intro hc
  have hsq : (r * t) * (r * t) = 1 := by
    calc
      (r * t) * (r * t) = r * (t * r) * t := by group
      _ = r * (r * t) * t := by rw [hc.eq]
      _ = (r * r) * (t * t) := by group
      _ = 1 := by rw [hrefl.1, ht2, mul_one]
  have hrtx : (r * t) (b x) = (ζ : ZMod p) • b x := by
    simpa [pairUnit] using hrt_diag x
  have hx1 : ((r * t) * (r * t)) (b x) = b x := by rw [hsq]; rfl
  have hx2 : ((r * t) * (r * t)) (b x) = ((ζ : ZMod p) * ζ) • b x := by
    rw [LinearEquiv.mul_apply, hrtx, map_smul, hrtx, smul_smul]
  have hcoeff : (ζ : ZMod p) * ζ = 1 := by
    have h := congrArg (fun v => b.repr v x) (hx1.symm.trans hx2)
    simpa [map_smul, Module.Basis.repr_self_apply, smul_eq_mul,
      Finsupp.single_apply] using h.symm
  apply hζ
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  exact hcoeff

private lemma exists_witness_of_adjacent_lines [Fact p.Prime]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    (hn : 3 ≤ n) (hperm : ∀ σ : Equiv.Perm (Fin n), permMap p b σ ∈ A)
    {δ : U ≃ₗ[ZMod p] U} (hδA : δ ∈ A) {i j : Fin n} {ζ : (ZMod p)ˣ}
    (hij : i ≠ j) (hζ : ζ ^ 2 ≠ 1) (hδ : IsDiagonal b δ (pairUnit p i j ζ))
    {r r₂ : U ≃ₗ[ZMod p] U} {x y z : Fin n} {a d : (ZMod p)ˣ}
    (hrtw : IsTwistedSwap b r x y a)
    (hr₂tw : IsTwistedSwap b r₂ y z d) (hxz : x ≠ z) (hrefl : IsRefl p r) :
    ∃ g ∈ A, ¬ (Commute (g * r * g⁻¹) r ∧ Commute (g * r * g⁻¹) r₂) ∧
      ¬ Nat.card (Subgroup.closure ({r, r₂, g * r * g⁻¹} : Set (U ≃ₗ[ZMod p] U))) ∣ 48 := by
  classical
  have hxy : x ≠ y := hrtw.1
  have h2 : 2 < n := Nat.lt_of_succ_le hn
  obtain ⟨w, hwx, hwy⟩ := Fin.exists_ne_and_ne_of_two_lt x y h2
  have hyw : y ≠ w := hwy.symm
  obtain ⟨π, hπi, hπj⟩ := exists_perm_apply_eq_pair hij hyw
  let e : Fin n → (ZMod p)ˣ := pairUnit p i j ζ ∘ π.symm
  let g : U ≃ₗ[ZMod p] U := permMap p b π * δ * (permMap p b π)⁻¹
  have hgA : g ∈ A := by
    have hπA := hperm π
    exact A.mul_mem (A.mul_mem hπA hδA) (A.inv_mem hπA)
  have hdiag : IsDiagonal b g e := IsDiagonal.permMap_conj hδ π
  have hπsy : π.symm y = i := by rw [← hπi, Equiv.symm_apply_apply]
  have hxi : π.symm x ≠ i := by
    intro h
    apply hxy
    calc x = π (π.symm x) := (π.apply_symm_apply x).symm
      _ = π i := by rw [h]
      _ = y := hπi
  have hxj : π.symm x ≠ j := by
    intro h
    apply hwx
    calc w = π j := hπj.symm
      _ = π (π.symm x) := by rw [h]
      _ = x := π.apply_symm_apply x
  have hex : e x = 1 := by simp [e, pairUnit, hxi, hxj]
  have hey : e y = ζ := by simp [e, pairUnit, hπsy]
  let t : U ≃ₗ[ZMod p] U := g * r * g⁻¹
  have ht_tw : IsTwistedSwap b t x y (a * ζ) := by
    have h := IsDiagonal.conj_isTwistedSwap hdiag hrtw
    have hscalar : a * e y * (e x)⁻¹ = a * ζ := by rw [hex, hey]; simp
    rw [hscalar] at h
    simpa [t] using h
  have hrt_diag : IsDiagonal b (r * t) (pairUnit p x y ζ) := by
    have h := IsTwistedSwap.mul_isDiagonal hrtw ht_tw
    have hscalar : (a * ζ) * a⁻¹ = ζ := by
      rw [mul_assoc, mul_comm ζ a⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hscalar] at h
    exact h
  let H : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({r, r₂, t} : Set (U ≃ₗ[ZMod p] U))
  have hrH : r ∈ H := Subgroup.subset_closure (by simp)
  have hr₂H : r₂ ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have hrtH : r * t ∈ H := H.mul_mem hrH htH
  have hcard : 54 ≤ Nat.card H :=
    le_card_of_isTwistedSwap hxz hrtw hr₂tw hrt_diag hζ hrH hr₂H hrtH
  have ht2 : t * t = 1 := by
    have h : t * t = g * (r * r) * g⁻¹ := by
      show (g * r * g⁻¹) * (g * r * g⁻¹) = g * (r * r) * g⁻¹
      group
    rw [h, hrefl.1]
    group
  have hnc : ¬ Commute t r := not_commute_of_diagonal_product hζ hrefl hrt_diag ht2
  refine ⟨g, hgA, fun hc => hnc hc.1, ?_⟩
  intro hdiv
  have hcard' : 54 ≤ Nat.card (Subgroup.closure ({r, r₂, g * r * g⁻¹} :
      Set (U ≃ₗ[ZMod p] U))) := hcard
  have := Nat.le_of_dvd (by norm_num) hdiv
  omega

private lemma exists_witness_of_same_lines [Fact p.Prime]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    (hn : 3 ≤ n) (hperm : ∀ σ : Equiv.Perm (Fin n), permMap p b σ ∈ A)
    {r r₂ : U ≃ₗ[ZMod p] U} {x y : Fin n} {a β : (ZMod p)ˣ}
    (hrtw : IsTwistedSwap b r x y a)
    (hr₂tw : IsTwistedSwap b r₂ x y β) (hβa : (β * a⁻¹) ^ 2 ≠ 1) :
    ∃ g ∈ A, ¬ (Commute (g * r * g⁻¹) r ∧ Commute (g * r * g⁻¹) r₂) ∧
      ¬ Nat.card (Subgroup.closure ({r, r₂, g * r * g⁻¹} : Set (U ≃ₗ[ZMod p] U))) ∣ 48 := by
  classical
  have hxy : x ≠ y := hrtw.1
  have h2 : 2 < n := Nat.lt_of_succ_le hn
  obtain ⟨z, hzx, hzy⟩ := Fin.exists_ne_and_ne_of_two_lt x y h2
  let g : U ≃ₗ[ZMod p] U := permMap p b (Equiv.swap y z)
  have hgA : g ∈ A := hperm (Equiv.swap y z)
  let t : U ≃ₗ[ZMod p] U := g * r * g⁻¹
  have hswap_x : Equiv.swap y z x = x := Equiv.swap_apply_of_ne_of_ne hxy hzx.symm
  have hswap_y : Equiv.swap y z y = z := Equiv.swap_apply_left y z
  have ht_tw : IsTwistedSwap b t x z a := by
    have h := IsTwistedSwap.permMap_conj hrtw (Equiv.swap y z)
    rw [hswap_x, hswap_y] at h
    simpa [t] using h
  have hrr₂_diag : IsDiagonal b (r * r₂) (pairUnit p x y (β * a⁻¹)) :=
    IsTwistedSwap.mul_isDiagonal hrtw hr₂tw
  have hdiag : IsDiagonal b (r * r₂) (pairUnit p y x ((β * a⁻¹)⁻¹)) := by
    rw [pairUnit_swap hxy (β * a⁻¹)]
    exact hrr₂_diag
  have hζinv : ((β * a⁻¹)⁻¹) ^ 2 ≠ 1 := by
    intro h
    apply hβa
    have := congrArg Inv.inv h
    simpa [pow_two, mul_inv_rev] using this
  let H : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({r, r₂, t} : Set (U ≃ₗ[ZMod p] U))
  have hrH : r ∈ H := Subgroup.subset_closure (by simp)
  have hr₂H : r₂ ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have hrr₂H : r * r₂ ∈ H := H.mul_mem hrH hr₂H
  have hcard : 54 ≤ Nat.card H :=
    le_card_of_isTwistedSwap (H := H) hzy.symm hrtw.symm ht_tw hdiag hζinv
      hrH htH hrr₂H
  have hnc : ¬ Commute t r := by
    intro hc
    have hby : t (b y) = b y := ht_tw.2.2.2 y hxy.symm hzy.symm
    have hL : (t * r) (b y) = b z := by
      rw [LinearEquiv.mul_apply, hrtw.2.2.1, map_smul, ht_tw.2.1, smul_smul]
      rw [← Units.val_mul, inv_mul_cancel]
      simp
    have hR : (r * t) (b y) = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) • b x := by
      rw [LinearEquiv.mul_apply, hby, hrtw.2.2.1]
    have heq : b z = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) • b x := by
      rw [← hL, hc.eq, hR]
    have hzx' : z = x :=
      LinearIndependent.eq_of_smul_apply_eq_smul_apply b.linearIndependent 1
        ((a⁻¹ : (ZMod p)ˣ) : ZMod p) z x one_ne_zero (by simpa only [one_smul] using heq)
    exact hzx hzx'
  refine ⟨g, hgA, fun hc => hnc hc.1, ?_⟩
  intro hdiv
  have hcard' : 54 ≤ Nat.card (Subgroup.closure ({r, r₂, g * r * g⁻¹} :
      Set (U ≃ₗ[ZMod p] U))) := hcard
  have := Nat.le_of_dvd (by norm_num) hdiv
  omega

theorem witL51_of_frame [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod p) U} (hn : 3 ≤ n)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hperm : ∀ σ : Equiv.Perm (Fin n), permMap p b σ ∈ A) {δ : U ≃ₗ[ZMod p] U} (hδA : δ ∈ A)
    {i j : Fin n} {ζ : (ZMod p)ˣ} (hij : i ≠ j) (hζ : ζ ^ 2 ≠ 1)
    (hδ : IsDiagonal b δ (pairUnit p i j ζ)) {r : U ≃ₗ[ZMod p] U} (hr : r ∈ A)
    (hrefl : IsRefl p r) : WitL51 p A r := by
  intro r₂ hr₂A hr₂ hord
  obtain ⟨x, y, a, hrtw, hcases⟩ :=
    exists_isTwistedSwap_of_orderOf_eq_three hp2 hrefl hr₂ (hmon r hr) (hmon r₂ hr₂A) hord
  rcases hcases with ⟨z, d, hzx, hr₂tw⟩ | ⟨d, hr₂tw, hβa⟩
  · exact exists_witness_of_adjacent_lines hn hperm hδA hij hζ hδ hrtw hr₂tw hzx.symm hrefl
  · exact exists_witness_of_same_lines hn hperm hrtw hr₂tw hβa

theorem witL51_of_witMON [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hRG : ReflGen p A) (hAI : AbsIrred p A) (hM : WitMON p A) {r : U ≃ₗ[ZMod p] U}
    (hr : r ∈ A) (hrefl : IsRefl p r) : WitL51 p A r := by
  obtain ⟨n, b, hn, hmon, hperm, δ, hδA, i, j, ζ, hij, hζ, hδ⟩ :=
    exists_frame_of_witMON hp2 hRG hAI hM
  exact witL51_of_frame hp2 hn hmon hperm hδA hij hζ hδ hr hrefl

end CFSG.StandardType.ZS

end
