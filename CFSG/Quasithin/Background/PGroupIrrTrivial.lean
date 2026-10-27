module

public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_mem_diff_commutator_mem_of_isPGroup {Y : Subgroup (MulAut W)}
    (hY : IsPGroup 2 Y) (hexp : ∀ w : W, w ^ 2 = 1) {V C : Subgroup W} (hCV : C < V)
    (hV : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V) (hC : ∀ y ∈ Y, ∀ c ∈ C, y c ∈ C) :
    ∃ v ∈ V, v ∉ C ∧ ∀ y ∈ Y, y v * v⁻¹ ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C' : Subgroup ↥V := C.subgroupOf V
  let φ : ↥Y → ↥V →* ↥V := fun y =>
    { toFun := fun v => ⟨(y : MulAut W) v, hV y y.2 v v.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hφ : ∀ y : ↥Y, C' ≤ C'.comap (φ y) := fun y c hc => hC y y.2 c hc
  let _ : MulAction ↥Y (↥V ⧸ C') :=
    { smul := fun y => QuotientGroup.map C' C' (φ y) (hφ y)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H v => exact congrArg QuotientGroup.mk (Subtype.ext rfl)
      mul_smul := fun a b q => by
        induction q using QuotientGroup.induction_on with
        | H v => exact congrArg QuotientGroup.mk (Subtype.ext rfl) }
  have hV2 : IsPGroup 2 ↥V := isPGroup_two_of_sq_eq_one fun v => Subtype.ext (hexp v)
  have hdvd : 2 ∣ Nat.card (↥V ⧸ C') := by
    obtain ⟨n, hn⟩ := hV2.index C'
    have hcard : Nat.card (↥V ⧸ C') = C'.index := rfl
    rw [hcard, hn]
    refine dvd_pow_self 2 ?_
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one] at hn
    apply hCV.not_ge
    intro v hv
    have : (⟨v, hv⟩ : ↥V) ∈ C' := hn ▸ Subgroup.mem_top _
    exact this
  have h1 : (1 : ↥V ⧸ C') ∈ MulAction.fixedPoints ↥Y (↥V ⧸ C') := by
    rw [MulAction.mem_fixedPoints]
    intro y
    exact map_one (QuotientGroup.map C' C' (φ y) (hφ y))
  obtain ⟨b, hb, hb1⟩ := hY.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥V ⧸ C') hdvd h1
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨v, v.2, fun hvC => hb1 ?_, fun y hy => ?_⟩
  · exact ((QuotientGroup.eq_one_iff v).mpr hvC).symm
  · have h := MulAction.mem_fixedPoints.mp hb ⟨y, hy⟩
    have h' : (QuotientGroup.mk (φ ⟨y, hy⟩ v) : ↥V ⧸ C') = QuotientGroup.mk v := h
    have h'' := QuotientGroup.eq.mp h'
    have hmem : ((y : MulAut W) v)⁻¹ * (v : W) ∈ C := h''
    have e : (y : MulAut W) v * (v : W)⁻¹ = (((y : MulAut W) v)⁻¹ * (v : W))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [e]
    exact C.inv_mem hmem

theorem trivial_on_of_isPGroup_commute {Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (hexp : ∀ w : W, w ^ 2 = 1) (hirr : V ∈ IrrPlus Mp (⊤ : Subgroup W))
    {Y : Subgroup (MulAut W)} (hY : IsPGroup 2 Y) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V)
    (hYMp : ∀ y ∈ Y, ∀ m ∈ Mp, y * m = m * y) : ∀ y ∈ Y, ∀ v ∈ V, y v = v := by
  obtain ⟨hinv, hcomm, hlt, hirr'⟩ := mem_irrPlus_top_iff.mp hirr
  set C : Subgroup W := V ⊓ fixV Mp with hC
  have hcomm_pt : ∀ y ∈ Y, ∀ m ∈ Mp, ∀ w : W, y (m w) = m (y w) := fun y hy m hm w => by
    have := congrArg (fun φ : MulAut W => φ w) (hYMp y hy m hm)
    simpa [MulAut.mul_apply] using this
  have hYC : ∀ y ∈ Y, ∀ c ∈ C, y c ∈ C := by
    intro y hy c hc
    refine ⟨hYV y hy c hc.1, fun m hm => ?_⟩
    rw [← hcomm_pt y hy m hm, hc.2 m hm]
  let J : Subgroup W :=
    { carrier := {v | v ∈ V ∧ ∀ y ∈ Y, y v * v⁻¹ ∈ C}
      one_mem' := ⟨V.one_mem, fun y _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, fun y hy => by
        have e : y (a * b) * (a * b)⁻¹ = (y a * a⁻¹) * (y b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [e]
        exact C.mul_mem (ha.2 y hy) (hb.2 y hy)⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, fun y hy => by
        have e : y a⁻¹ * (a⁻¹)⁻¹ = (y a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
        rw [e]
        exact C.inv_mem (ha.2 y hy)⟩ }
  have hCJ : C ≤ J := fun c hc => ⟨hc.1, fun y hy => C.mul_mem (hYC y hy c hc) (C.inv_mem hc)⟩
  have hJV : J ≤ V := fun v hv => hv.1
  have hJinv : ∀ m ∈ Mp, ∀ w ∈ J, m w ∈ J := by
    intro m hm w hw
    refine ⟨hinv m hm w hw.1, fun y hy => ?_⟩
    have e : y (m w) * (m w)⁻¹ = m (y w * w⁻¹) := by
      rw [hcomm_pt y hy m hm, map_mul, map_inv]
    rw [e]
    have hc := hw.2 y hy
    rw [hc.2 m hm]
    exact hc
  have hJeq : J = V := by
    rcases hirr' J hJinv hCJ hJV with h | h
    · exfalso
      obtain ⟨v, hvV, hvC, hv⟩ :=
        exists_mem_diff_commutator_mem_of_isPGroup hY hexp hlt hYV hYC
      exact hvC (h ▸ ⟨hvV, hv⟩)
    · exact h
  have hall : ∀ v ∈ V, ∀ y ∈ Y, y v * v⁻¹ ∈ C := fun v hv y hy => by
    have hvJ : v ∈ J := by rw [hJeq]; exact hv
    exact hvJ.2 y hy
  intro y hy
  have hgen : commSub V Mp ≤ (y : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    show y (m v * v⁻¹) = m v * v⁻¹
    have hc := hall v hv y hy
    have h1 : m (y v * v⁻¹) = y v * v⁻¹ := hc.2 m hm
    have e : y v = (y v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    calc y (m v * v⁻¹) = m (y v) * (y v)⁻¹ := by rw [map_mul, map_inv, hcomm_pt y hy m hm]
      _ = m ((y v * v⁻¹) * v) * (y v)⁻¹ := by rw [← e]
      _ = (y v * v⁻¹) * m v * (y v)⁻¹ := by rw [map_mul, h1]
      _ = (y v * (y v)⁻¹) * (m v * v⁻¹) := by ac_rfl
      _ = m v * v⁻¹ := by rw [mul_inv_cancel, one_mul]
  intro v hv
  have hv' : v ∈ commSub V Mp := hcomm.symm ▸ hv
  exact hgen hv'

end CFSG.Quasithin
