module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Side

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)}

theorem Br3TwoComp.comm_X_mem (h : Br3TwoComp Y T L₁ L₂) {a b : LGL 2 V}
    (ha : a ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hb : b ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) :
    a * b * a⁻¹ * b⁻¹ ∈ quasiCentre L₁ ⊔ quasiCentre L₂ := by
  have haC₂ : a ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := ha.2
  have hbC₁ : b ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := hb.2
  have haminv : a⁻¹ ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem ha
  have hbminv : b⁻¹ ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
    (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))).inv_mem hb
  let c : LGL 2 V := a * b * a⁻¹ * b⁻¹
  have hc_def : c = a * b * a⁻¹ * b⁻¹ := rfl
  have hcY : c ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem ha.1 hb.1) (Y.inv_mem ha.1)) (Y.inv_mem hb.1)
  have hc₁ : ∀ l ∈ L₁, c * l = l * c := by
    intro l hl
    have hbl : b⁻¹ * l * b = l := by
      have h := Subgroup.mem_centralizer_iff.mp hbC₁ l hl
      calc b⁻¹ * l * b = b⁻¹ * (l * b) := by group
        _ = b⁻¹ * (b * l) := by rw [h]
        _ = l := by group
    have hm : a⁻¹ * l * a ∈ L₁ := by
      have := h.core₁.normal a⁻¹ haminv l hl
      simpa using this
    have hbm : b * (a⁻¹ * l * a) * b⁻¹ = a⁻¹ * l * a := by
      have h := Subgroup.mem_centralizer_iff.mp hbC₁ (a⁻¹ * l * a) hm
      calc b * (a⁻¹ * l * a) * b⁻¹ = ((a⁻¹ * l * a) * b) * b⁻¹ := by rw [← h]
        _ = a⁻¹ * l * a := by group
    have hcl : c * l * c⁻¹ = l := by
      rw [hc_def]
      calc (a * b * a⁻¹ * b⁻¹) * l * (a * b * a⁻¹ * b⁻¹)⁻¹
          = a * b * a⁻¹ * (b⁻¹ * l * b) * a * b⁻¹ * a⁻¹ := by group
        _ = a * b * a⁻¹ * l * a * b⁻¹ * a⁻¹ := by rw [hbl]
        _ = a * (b * (a⁻¹ * l * a) * b⁻¹) * a⁻¹ := by group
        _ = a * (a⁻¹ * l * a) * a⁻¹ := by rw [hbm]
        _ = l := by group
    calc c * l = c * l * c⁻¹ * c := by group
      _ = l * c := by rw [hcl]
  have hc₂ : ∀ l ∈ L₂, c * l = l * c := by
    intro m hm
    have ham : a * m * a⁻¹ = m := by
      have h := Subgroup.mem_centralizer_iff.mp haC₂ m hm
      calc a * m * a⁻¹ = (m * a) * a⁻¹ := by rw [← h]
        _ = m := by group
    have hnb : b⁻¹ * m * b ∈ L₂ := by
      have := h.core₂.normal b⁻¹ hbminv m hm
      simpa using this
    have hna : a⁻¹ * (b⁻¹ * m * b) * a = b⁻¹ * m * b := by
      have h := Subgroup.mem_centralizer_iff.mp haC₂ (b⁻¹ * m * b) hnb
      calc a⁻¹ * (b⁻¹ * m * b) * a = a⁻¹ * ((b⁻¹ * m * b) * a) := by group
        _ = a⁻¹ * (a * (b⁻¹ * m * b)) := by rw [← h]
        _ = b⁻¹ * m * b := by group
    have hcm : c * m * c⁻¹ = m := by
      rw [hc_def]
      calc (a * b * a⁻¹ * b⁻¹) * m * (a * b * a⁻¹ * b⁻¹)⁻¹
          = a * b * (a⁻¹ * (b⁻¹ * m * b) * a) * b⁻¹ * a⁻¹ := by group
        _ = a * b * (b⁻¹ * m * b) * b⁻¹ * a⁻¹ := by rw [hna]
        _ = a * m * a⁻¹ := by group
        _ = m := by rw [ham]
    calc c * m = c * m * c⁻¹ * c := by group
      _ = m * c := by rw [hcm]
  rw [← hc_def]
  exact h.mem_kStar_of_cent hcY hc₁ hc₂

private theorem w183K3SideB_orderOf_odd_of_mem_quasiCentre {L : Subgroup (LGL 2 V)}
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) {z : LGL 2 V} (hz : z ∈ quasiCentre L) :
    Odd (orderOf z) := by
  obtain ⟨hzL, hzc⟩ := mem_quasiCentre.mp hz
  have hmem : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hzc (y : LGL 2 V) y.2).symm
  have hdvd : orderOf (⟨⟨z, hzL⟩, hmem⟩ : ↥(Subgroup.center ↥L)) ∣
      Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard _
  have heq : orderOf (⟨⟨z, hzL⟩, hmem⟩ : ↥(Subgroup.center ↥L)) = orderOf z :=
    (Subgroup.orderOf_coe (G := ↥L) (H := Subgroup.center ↥L) _).symm.trans
      (Subgroup.orderOf_mk (H := L) z hzL)
  rw [heq] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

private theorem w183K3SideB_mem_of_sq_mem_of_odd {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx2 : x * x ∈ H) (hodd : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨s, hs⟩ := hodd
  have hpow : x = (x * x) ^ (s + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (s + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hpow]
  exact Subgroup.pow_mem H hx2 (s + 1)

theorem Br3TwoComp.comm_X_of_sq_eq_one (h : Br3TwoComp Y T L₁ L₂) {a b : LGL 2 V}
    (ha : a ∈ Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hb : b ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) (ha2 : a * a = 1)
    (hb2 : b * b = 1) : a * b = b * a := by
  have ha'inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb'inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcommZ : ∀ x ∈ quasiCentre L₁, ∀ y ∈ quasiCentre L₂, x * y = y * x :=
    fun x hx y hy => h.comm x (quasiCentre_le L₁ hx) y (quasiCentre_le L₂ hy)
  let k : LGL 2 V := a * b * a * b
  have hk_eq : k = a * b * a * b := rfl
  have hk : k ∈ quasiCentre L₁ ⊔ quasiCentre L₂ := by
    rw [hk_eq]
    simpa only [ha'inv, hb'inv] using h.comm_X_mem ha hb
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁z₂⟩ := w183two_exists_mul_of_mem_sup hcommZ hk
  have hu : a * z₁ * a⁻¹ ∈ quasiCentre L₁ := by
    rw [mem_quasiCentre]
    refine ⟨h.core₁.normal a ha z₁ (quasiCentre_le L₁ hz₁), fun l hl => ?_⟩
    have hna : a⁻¹ * l * a ∈ L₁ := by
      simpa using h.core₁.normal a⁻¹
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem ha) l hl
    have hzc := (mem_quasiCentre.mp hz₁).2 (a⁻¹ * l * a) hna
    calc a * z₁ * a⁻¹ * l = a * (z₁ * (a⁻¹ * l * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * l * a) * z₁) * a⁻¹ := by rw [hzc]
      _ = l * (a * z₁ * a⁻¹) := by group
  have haz₂ : a * z₂ * a⁻¹ = z₂ := by
    have hh := Subgroup.mem_centralizer_iff.mp ha.2 z₂ (quasiCentre_le L₂ hz₂)
    calc a * z₂ * a⁻¹ = z₂ * a * a⁻¹ := by rw [← hh]
      _ = z₂ := by group
  have hv : b * z₂ * b⁻¹ ∈ quasiCentre L₂ := by
    rw [mem_quasiCentre]
    refine ⟨h.core₂.normal b hb z₂ (quasiCentre_le L₂ hz₂), fun l hl => ?_⟩
    have hnb : b⁻¹ * l * b ∈ L₂ := by
      simpa using h.core₂.normal b⁻¹
        ((Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))).inv_mem hb) l hl
    have hzc := (mem_quasiCentre.mp hz₂).2 (b⁻¹ * l * b) hnb
    calc b * z₂ * b⁻¹ * l = b * (z₂ * (b⁻¹ * l * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * l * b) * z₂) * b⁻¹ := by rw [hzc]
      _ = l * (b * z₂ * b⁻¹) := by group
  have hbz₁ : b * z₁ * b⁻¹ = z₁ := by
    have hh := Subgroup.mem_centralizer_iff.mp hb.2 z₁ (quasiCentre_le L₁ hz₁)
    calc b * z₁ * b⁻¹ = z₁ * b * b⁻¹ := by rw [← hh]
      _ = z₁ := by group
  have hkinv : k⁻¹ = z₂⁻¹ * z₁⁻¹ := by rw [← hz₁z₂, mul_inv_rev]
  have hkinv' : k⁻¹ = b * a * b * a := by
    rw [hk_eq]
    simp only [mul_inv_rev, ha'inv, hb'inv]
    group
  have hauk_inv : a * k * a⁻¹ = k⁻¹ := by
    rw [hk_eq]
    calc a * (a * b * a * b) * a⁻¹ = (a * a) * b * a * b * a⁻¹ := by group
      _ = b * a * b * a⁻¹ := by rw [ha2]; group
      _ = b * a * b * a := by rw [ha'inv]
      _ = k⁻¹ := hkinv'.symm
  have hbk_inv : b * k * b⁻¹ = k⁻¹ := by
    rw [hk_eq]
    calc b * (a * b * a * b) * b⁻¹ = b * a * b * a * (b * b⁻¹) := by group
      _ = b * a * b * a := by group
      _ = k⁻¹ := hkinv'.symm
  have hak_u : a * k * a⁻¹ = (a * z₁ * a⁻¹) * z₂ := by
    rw [← hz₁z₂]
    calc a * (z₁ * z₂) * a⁻¹ = (a * z₁ * a⁻¹) * (a * z₂ * a⁻¹) := by group
      _ = (a * z₁ * a⁻¹) * z₂ := by rw [haz₂]
  have huz : (a * z₁ * a⁻¹) * z₂ = z₂⁻¹ * z₁⁻¹ := by
    rw [← hak_u, hauk_inv, hkinv]
  have hz₂sq : z₂ * z₂ ∈ quasiCentre L₁ := by
    have h1 : (a * z₁ * a⁻¹) * (z₂ * z₂) = z₁⁻¹ := by
      have hc : z₁⁻¹ * z₂ = z₂ * z₁⁻¹ := hcommZ z₁⁻¹ ((quasiCentre L₁).inv_mem hz₁) z₂ hz₂
      calc (a * z₁ * a⁻¹) * (z₂ * z₂) = ((a * z₁ * a⁻¹) * z₂) * z₂ := by group
        _ = (z₂⁻¹ * z₁⁻¹) * z₂ := by rw [huz]
        _ = z₂⁻¹ * (z₁⁻¹ * z₂) := by group
        _ = z₂⁻¹ * (z₂ * z₁⁻¹) := by rw [hc]
        _ = z₁⁻¹ := by group
    have h2 : z₂ * z₂ = (a * z₁ * a⁻¹)⁻¹ * z₁⁻¹ := by rw [← h1]; group
    rw [h2]
    exact (quasiCentre L₁).mul_mem ((quasiCentre L₁).inv_mem hu) ((quasiCentre L₁).inv_mem hz₁)
  have hz₁sq : z₁ * z₁ ∈ quasiCentre L₂ := by
    have hbk_v : b * k * b⁻¹ = z₁ * (b * z₂ * b⁻¹) := by
      rw [← hz₁z₂]
      calc b * (z₁ * z₂) * b⁻¹ = (b * z₁ * b⁻¹) * (b * z₂ * b⁻¹) := by group
        _ = z₁ * (b * z₂ * b⁻¹) := by rw [hbz₁]
    have h1 : (z₁ * z₁) * (b * z₂ * b⁻¹) = z₂⁻¹ := by
      have hc : z₁ * z₂⁻¹ = z₂⁻¹ * z₁ := hcommZ z₁ hz₁ z₂⁻¹ ((quasiCentre L₂).inv_mem hz₂)
      have hz₁v : z₁ * (b * z₂ * b⁻¹) = z₂⁻¹ * z₁⁻¹ := by
        rw [← hbk_v, hbk_inv, hkinv]
      calc (z₁ * z₁) * (b * z₂ * b⁻¹) = z₁ * (z₁ * (b * z₂ * b⁻¹)) := by group
        _ = z₁ * (z₂⁻¹ * z₁⁻¹) := by rw [hz₁v]
        _ = (z₁ * z₂⁻¹) * z₁⁻¹ := by group
        _ = (z₂⁻¹ * z₁) * z₁⁻¹ := by rw [hc]
        _ = z₂⁻¹ := by group
    have h2 : z₁ * z₁ = z₂⁻¹ * (b * z₂ * b⁻¹)⁻¹ := by rw [← h1]; group
    rw [h2]
    exact (quasiCentre L₂).mul_mem ((quasiCentre L₂).inv_mem hz₂) ((quasiCentre L₂).inv_mem hv)
  have hz₂_odd : Odd (orderOf z₂) := w183K3SideB_orderOf_odd_of_mem_quasiCentre h.odd₂ hz₂
  have hz₁_odd : Odd (orderOf z₁) := w183K3SideB_orderOf_odd_of_mem_quasiCentre h.odd₁ hz₁
  have hz₂Z₁ : z₂ ∈ quasiCentre L₁ := w183K3SideB_mem_of_sq_mem_of_odd hz₂sq hz₂_odd
  have hz₁Z₂ : z₁ ∈ quasiCentre L₂ := w183K3SideB_mem_of_sq_mem_of_odd hz₁sq hz₁_odd
  have hkZ₁ : k ∈ quasiCentre L₁ := by
    rw [← hz₁z₂]
    exact (quasiCentre L₁).mul_mem hz₁ hz₂Z₁
  have hkZ₂ : k ∈ quasiCentre L₂ := by
    rw [← hz₁z₂]
    exact (quasiCentre L₂).mul_mem hz₁Z₂ hz₂
  have hak : a * k * a⁻¹ = k := by
    have hh := Subgroup.mem_centralizer_iff.mp ha.2 k (quasiCentre_le L₂ hkZ₂)
    calc a * k * a⁻¹ = k * a * a⁻¹ := by rw [← hh]
      _ = k := by group
  have hk_eq_inv : k = k⁻¹ := hak.symm.trans hauk_inv
  have hkk : k * k = 1 := by
    calc k * k = k⁻¹ * k := congrArg (· * k) hk_eq_inv
      _ = 1 := inv_mul_cancel k
  have hk1 : k = 1 :=
    quasi_centre_two_pow_eq_one (L := L₁) h.odd₁ hkZ₁ (k := 1)
      (by simpa [pow_two] using hkk)
  have hcomm1 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have e : a * b * a⁻¹ * b⁻¹ = k := by rw [hk_eq, ha'inv, hb'inv]
    rw [e, hk1]
  have h3 : a * b * a⁻¹ = b := mul_inv_eq_one.mp hcomm1
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h3]

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
