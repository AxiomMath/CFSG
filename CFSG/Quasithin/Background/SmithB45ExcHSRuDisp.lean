module

public import CFSG.Quasithin.Background.SmithB45ExcEngine

public section

namespace CFSG.Quasithin.B45Exc.HSRu

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.B45Exc

variable {W : Type} [CommGroup W]

theorem fixV_map_conj (E : Subgroup (MulAut W)) (g : MulAut W) :
    fixV (E.map (MulAut.conj g).toMonoidHom) = (fixV E).map (g : W ≃* W).toMonoidHom :=
  fixV_map_conj_eq E g

theorem index_fixV_map_conj (E : Subgroup (MulAut W)) (g : MulAut W) :
    (fixV (E.map (MulAut.conj g).toMonoidHom)).index = (fixV E).index := by
  rw [fixV_map_conj]
  exact Subgroup.index_map_equiv (fixV E) (g : W ≃* W)

theorem index_fixV_sup_conj_le [Finite W] (E : Subgroup (MulAut W)) (g : MulAut W) :
    (fixV (E ⊔ E.map (MulAut.conj g).toMonoidHom)).index ≤ (fixV E).index ^ 2 := by
  rw [fixV_sup, sq]
  calc (fixV E ⊓ fixV (E.map (MulAut.conj g).toMonoidHom)).index
      ≤ (fixV E).index * (fixV (E.map (MulAut.conj g).toMonoidHom)).index :=
        Subgroup.index_inf_le
    _ = (fixV E).index * (fixV E).index := by rw [index_fixV_map_conj]

theorem index_fixV_zpowers_le_sq [Finite W] {E : Subgroup (MulAut W)} {g y : MulAut W}
    (hy : y ∈ E ⊔ E.map (MulAut.conj g).toMonoidHom) :
    (fixV (Subgroup.zpowers y)).index ≤ (fixV E).index ^ 2 := by
  refine le_trans ?_ (index_fixV_sup_conj_le E g)
  apply Subgroup.index_antitone
  apply fixV_anti
  rw [Subgroup.zpowers_le]
  exact hy

theorem conj_mem_map_conj {E : Subgroup (MulAut W)} (g : MulAut W) {x : MulAut W}
    (hx : x ∈ E) : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem card_le_index_sq_of_le_sup [Finite W] {L E : Subgroup (MulAut W)} (hirr : IsIrrOn L)
    (hL : L ≠ ⊥) {g : MulAut W} (hLE : L ≤ E ⊔ E.map (MulAut.conj g).toMonoidHom) :
    Nat.card W ≤ (fixV E).index ^ 2 := by
  have hbot : fixV (E ⊔ E.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    rw [eq_bot_iff, ← fixV_eq_bot_of_irr hirr hL]
    exact fixV_anti hLE
  have h := index_fixV_sup_conj_le E g
  rwa [hbot, Subgroup.index_bot] at h

section Quad

variable (hW : ∀ w : W, w * w = 1)
include hW

theorem inv_eq_self (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW w)

theorem disp_fixed_of_sq {d : MulAut W} (hd : d * d = 1) (w : W) :
    d (dispHom d w) = dispHom d w := by
  have hdd : d (d w) = w := by
    have := congrArg (fun x : MulAut W => x w) hd
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  rw [dispHom_apply, map_mul, map_inv, hdd, inv_eq_self hW, inv_eq_self hW, mul_comm]

omit hW in
theorem disp_fixed_of_comm {c d : MulAut W} (hcd : c * d = d * c)
    (hfix : ∀ w : W, c (dispHom d w) = dispHom d w) (w : W) :
    d (dispHom c w) = dispHom c w := by
  have h1 := hfix w
  rw [dispHom_apply, map_mul, map_inv] at h1
  have hdc : d (c w) = c (d w) := by
    have := congrArg (fun x : MulAut W => x w) hcd
    simpa only [MulAut.mul_apply] using this.symm
  have h2 : c (d w) = d w * w⁻¹ * c w := by
    calc c (d w) = c (d w) * (c w)⁻¹ * c w := by group
      _ = d w * w⁻¹ * c w := by rw [h1]
  rw [dispHom_apply, map_mul, map_inv, hdc, h2, mul_inv_eq_iff_eq_mul]
  ac_rfl

omit hW in
theorem apply_disp_of_comm {c g : MulAut W} (hgc : g * c = c * g) (w : W) :
    g (dispHom c w) = dispHom c (g w) := by
  have : g (c w) = c (g w) := by
    have := congrArg (fun x : MulAut W => x w) hgc
    simpa only [MulAut.mul_apply] using this
  rw [dispHom_apply, map_mul, map_inv, this, dispHom_apply]

omit hW in
theorem disp_mem_fixV_of_fix {c y : MulAut W} (hyc : y * c = c * y)
    (hfix : ∀ w : W, y (dispHom c w) = dispHom c w) (w : W) :
    dispHom y w ∈ fixV (Subgroup.zpowers c) := by
  rw [mem_fixV_zpowers]
  have h1 := hfix w
  rw [apply_disp_of_comm hyc, dispHom_apply, dispHom_apply] at h1
  have h2 : c (y w) = c w * w⁻¹ * y w := by
    calc c (y w) = c (y w) * (y w)⁻¹ * y w := by group
      _ = c w * w⁻¹ * y w := by rw [h1]
  rw [dispHom_apply, map_mul, map_inv, h2, mul_inv_eq_iff_eq_mul]
  ac_rfl

theorem index_fixV_le_card_fixV [Finite W] {E : Subgroup (MulAut W)} (hEel : IsElemAbelian2 E)
    {d c e e' g : MulAut W} (hd : d ∈ E) (hc : c ∈ E) (he : e ∈ E) (he' : e' ∈ E)
    (hgc : g * c = c * g) (hdisp : (fixV E).index ≤ (fixV (Subgroup.zpowers d)).index) :
    (fixV (Subgroup.zpowers (g * e * g⁻¹ * e'))).index ≤
      Nat.card (fixV (Subgroup.zpowers c)) := by
  have hd2 : d * d = 1 := by
    have := hEel.2 d hd
    rwa [sq] at this
  have hfixE : fixV E = fixV (Subgroup.zpowers d) := fixV_eq_of_index_le hd hdisp
  have hdE : ∀ w : W, dispHom d w ∈ fixV E := by
    intro w
    rw [hfixE, mem_fixV_zpowers]
    exact disp_fixed_of_sq hW hd2 w
  have hcd : c * d = d * c := hEel.1 c hc d hd
  have hcE : ∀ w : W, dispHom c w ∈ fixV E := by
    intro w
    rw [hfixE, mem_fixV_zpowers]
    exact disp_fixed_of_comm hcd (fun v => hdE v c hc) w
  set y := g * e * g⁻¹ * e' with hy
  have hginv : g⁻¹ * c = c * g⁻¹ := by
    calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * c) * g⁻¹ := by rw [hgc]
      _ = c * g⁻¹ := by group
  have hyfix : ∀ w : W, y (dispHom c w) = dispHom c w := by
    intro w
    have h1 : e' (dispHom c w) = dispHom c w := hcE w e' he'
    have h2 : g⁻¹ (dispHom c w) = dispHom c (g⁻¹ w) := apply_disp_of_comm hginv w
    have h3 : e (dispHom c (g⁻¹ w)) = dispHom c (g⁻¹ w) := hcE (g⁻¹ w) e he
    show g (e (g⁻¹ (e' (dispHom c w)))) = dispHom c w
    rw [h1, h2, h3, ← h2, MulAut.apply_inv_self]
  have hec : e * c = c * e := hEel.1 e he c hc
  have he'c : e' * c = c * e' := hEel.1 e' he' c hc
  have hyc : y * c = c * y := by
    calc y * c = g * e * (g⁻¹ * c) * e' := by rw [hy, mul_assoc _ e' c, he'c]; group
      _ = g * e * (c * g⁻¹) * e' := by rw [hginv]
      _ = g * (e * c) * g⁻¹ * e' := by group
      _ = g * (c * e) * g⁻¹ * e' := by rw [hec]
      _ = (g * c) * e * g⁻¹ * e' := by group
      _ = (c * g) * e * g⁻¹ * e' := by rw [hgc]
      _ = c * y := by rw [hy]; group
  have hrange : (dispHom y).range ≤ fixV (Subgroup.zpowers c) := by
    rintro _ ⟨w, rfl⟩
    exact disp_mem_fixV_of_fix hyc hyfix w
  have hker : (dispHom y).ker = fixV (Subgroup.zpowers y) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_dispHom]
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_of_le hrange

end Quad

end CFSG.Quasithin.B45Exc.HSRu
