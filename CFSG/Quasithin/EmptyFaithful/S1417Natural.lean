module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.B1NaturalL2

public section

namespace CFSG.Quasithin

variable {W : Type*} [CommGroup W]

theorem commV_stable (L : Subgroup (MulAut W)) {l : MulAut W} (hl : l ∈ L) {u : W}
    (hu : u ∈ commV L) : l u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem hl hu

namespace S1417

open Matrix

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

theorem card_SL2 : Nat.card SL2 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_F2sq : Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_of_actsAsNaturalL2 {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) : Nat.card L = 6 ∧ Nat.card U = 4 := by
  obtain ⟨e, φ, -⟩ := hN
  exact ⟨(Nat.card_congr e.toEquiv).trans card_SL2, (Nat.card_congr φ.toEquiv).trans card_F2sq⟩

theorem exists_model {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) :
    ∃ (e : ↥L ≃* SL2) (φ : ↥U ≃* Multiplicative (Fin 2 → ZMod 2)),
      ∀ (l : ↥L) (u : ↥U),
        φ ⟨(l : MulAut W) u, hst l l.2 u u.2⟩ =
          Multiplicative.ofAdd ((e l : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (φ u)) := by
  obtain ⟨e, φ, hc⟩ := hN
  exact ⟨e, φ, fun l u => hc l u (hst l l.2 u u.2)⟩

theorem eq_one_of_forall_apply_eq {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) {l : MulAut W} (hl : l ∈ L)
    (h : ∀ u ∈ U, l u = u) : l = 1 := by
  obtain ⟨e, φ, hc⟩ := exists_model hN hst
  have hmat : ((e ⟨l, hl⟩ : SL2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    apply B1.mulVec_ext
    intro x
    rw [Matrix.one_mulVec]
    set u : U := φ.symm (Multiplicative.ofAdd x) with hu
    have h1 := hc ⟨l, hl⟩ u
    have h2 : (⟨((⟨l, hl⟩ : L) : MulAut W) u, hst l hl u u.2⟩ : U) = u := Subtype.ext (h u u.2)
    rw [h2] at h1
    have h3 : φ u = Multiplicative.ofAdd x := by simp [hu]
    rw [h3] at h1
    simpa using h1.symm
  have h4 : e ⟨l, hl⟩ = 1 := Subtype.ext hmat
  have h5 : (⟨l, hl⟩ : L) = 1 := e.injective (by rw [h4, map_one])
  exact congrArg Subtype.val h5

theorem exists_apply_eq {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (ψ : MulAut U) :
    ∃ l ∈ L, ∀ u : U, (l : MulAut W) u = ((ψ u : U) : W) := by
  obtain ⟨e, φ, hc⟩ := exists_model hN hst
  obtain ⟨g, hg⟩ := B1.slHom_surjective (MulAut.congr φ ψ)
  refine ⟨((e.symm g : ↥L) : MulAut W), (e.symm g).2, fun u => ?_⟩
  have h1 := hc (e.symm g) u
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : B1.slHom g (φ u) = φ (ψ u) := by
    rw [hg, MulAut.congr_apply]
    simp
  rw [B1.slHom, MonoidHom.coe_mk, OneHom.coe_mk, B1.slAut_apply] at h2
  have h3 : φ ⟨((e.symm g : ↥L) : MulAut W) u, hst _ (e.symm g).2 u u.2⟩ = φ (ψ u) := by
    rw [h1]; exact h2
  exact congrArg Subtype.val (φ.injective h3)

theorem SL2_fixed_of_sq : ∀ M : SL2, M ^ 2 = 1 → M ≠ 1 →
    ∃ x₀ : Fin 2 → ZMod 2, x₀ ≠ 0 ∧ ∀ x : Fin 2 → ZMod 2,
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x = x ↔ (x = 0 ∨ x = x₀) := by
  decide

theorem SL2_fixed_of_cube : ∀ M : SL2, M ^ 3 = 1 → M ≠ 1 → ∀ x : Fin 2 → ZMod 2,
    (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ x = x → x = 0 := by
  decide

theorem SL2_conj_inv : ∀ s x : SL2, s ^ 2 = 1 → s ≠ 1 → x ^ 3 = 1 → x ≠ 1 →
    s * x * s⁻¹ = x⁻¹ := by
  decide

theorem SL2_exists_sq : ∃ s : SL2, s ^ 2 = 1 ∧ s ≠ 1 := by decide

theorem SL2_exists_cube : ∃ x : SL2, x ^ 3 = 1 ∧ x ≠ 1 := by decide

section Natural

variable {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem exists_fixed_vector (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    {s : MulAut W} (hs : s ∈ L) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ a ∈ U, a ≠ 1 ∧ ∀ u ∈ U, s u = u ↔ (u = 1 ∨ u = a) := by
  obtain ⟨e, φ, hc⟩ := exists_model hN hst
  have hM2 : (e ⟨s, hs⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨s, hs⟩ : L) ^ 2 = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hM1 : e ⟨s, hs⟩ ≠ 1 := by
    intro h
    apply hs1
    have h' : (⟨s, hs⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  obtain ⟨x₀, hx₀, hfix⟩ := SL2_fixed_of_sq _ hM2 hM1
  have haφ : φ (φ.symm (Multiplicative.ofAdd x₀)) = Multiplicative.ofAdd x₀ := by simp
  refine ⟨((φ.symm (Multiplicative.ofAdd x₀) : U) : W), (φ.symm _).2, ?_, fun u hu => ?_⟩
  · intro h
    have h1 : φ.symm (Multiplicative.ofAdd x₀) = 1 := Subtype.ext h
    have h2 : Multiplicative.ofAdd x₀ = 1 := by
      have := congrArg φ h1
      rwa [haφ, map_one] at this
    exact hx₀ (by simpa using h2)
  · have h1 := hc ⟨s, hs⟩ ⟨u, hu⟩
    have hiff : s u = u ↔ (e ⟨s, hs⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (φ ⟨u, hu⟩) = Multiplicative.toAdd (φ ⟨u, hu⟩) := by
      constructor
      · intro h
        have h2 : (⟨((⟨s, hs⟩ : L) : MulAut W) u, hst s hs u hu⟩ : U) = ⟨u, hu⟩ := Subtype.ext h
        rw [h2] at h1
        have h3 := congrArg Multiplicative.toAdd h1
        simpa using h3.symm
      · intro h
        have h2 : φ ⟨((⟨s, hs⟩ : L) : MulAut W) u, hst s hs u hu⟩ = φ ⟨u, hu⟩ := by
          rw [h1, h]; simp
        exact congrArg Subtype.val (φ.injective h2)
    rw [hiff, hfix]
    constructor
    · rintro (h | h)
      · left
        have : φ ⟨u, hu⟩ = 1 := by
          have h' := congrArg Multiplicative.ofAdd h
          simpa using h'
        exact congrArg Subtype.val (φ.injective (this.trans (map_one φ).symm))
      · right
        have : φ ⟨u, hu⟩ = φ (φ.symm (Multiplicative.ofAdd x₀)) := by
          rw [haφ]
          have h' := congrArg Multiplicative.ofAdd h
          simpa using h'
        exact congrArg Subtype.val (φ.injective this)
    · rintro (h | h)
      · left
        have h1' : (⟨u, hu⟩ : U) = 1 := Subtype.ext h
        rw [h1', map_one]
        rfl
      · right
        have h1' : (⟨u, hu⟩ : U) = φ.symm (Multiplicative.ofAdd x₀) := Subtype.ext h
        rw [h1', MulEquiv.apply_symm_apply]
        rfl

theorem eq_one_of_odd_of_fixed (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    {l : MulAut W} (hl : l ∈ L) (hodd : Odd (orderOf l)) {u : W} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hlu : l u = u) : l = 1 := by
  obtain ⟨e, φ, hc⟩ := exists_model hN hst
  have hcard := (card_of_actsAsNaturalL2 hN).1
  have hdvd : orderOf l ∣ 6 := by
    have h1 : orderOf (⟨l, hl⟩ : L) ∣ Nat.card L := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    exact h1
  have h3 : orderOf l ∣ 3 := by
    have hcop : Nat.Coprime (orderOf l) 2 := Nat.coprime_two_right.mpr hodd
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  have hl3 : l ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  by_contra hne
  have hM3 : (e ⟨l, hl⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨l, hl⟩ : L) ^ 3 = 1 := Subtype.ext hl3
    rw [this, map_one]
  have hM1 : e ⟨l, hl⟩ ≠ 1 := by
    intro h
    apply hne
    have h' : (⟨l, hl⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have h1 := hc ⟨l, hl⟩ ⟨u, hu⟩
  have h2 : (⟨((⟨l, hl⟩ : L) : MulAut W) u, hst l hl u hu⟩ : U) = ⟨u, hu⟩ := Subtype.ext hlu
  rw [h2] at h1
  have h3' := congrArg Multiplicative.toAdd h1
  simp only [toAdd_ofAdd] at h3'
  have h4 := SL2_fixed_of_cube _ hM3 hM1 _ h3'.symm
  apply hu1
  have : φ ⟨u, hu⟩ = 1 := by
    have h5 := congrArg Multiplicative.ofAdd h4
    simpa using h5
  exact congrArg Subtype.val (φ.injective (this.trans (map_one φ).symm))

theorem exists_involution (hN : ActsAsNaturalL2 L U) :
    ∃ s ∈ L, s ^ 2 = 1 ∧ s ≠ 1 := by
  obtain ⟨e, -, -⟩ := hN
  obtain ⟨g, hg2, hg1⟩ := SL2_exists_sq
  refine ⟨((e.symm g : ↥L) : MulAut W), (e.symm g).2, ?_, ?_⟩
  · have : (e.symm g) ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
    exact congrArg Subtype.val this
  · intro h
    have : e.symm g = 1 := Subtype.ext h
    apply hg1
    simpa using congrArg e this

theorem exists_orderThree (hN : ActsAsNaturalL2 L U) :
    ∃ x ∈ L, x ^ 3 = 1 ∧ x ≠ 1 := by
  obtain ⟨e, -, -⟩ := hN
  obtain ⟨g, hg3, hg1⟩ := SL2_exists_cube
  refine ⟨((e.symm g : ↥L) : MulAut W), (e.symm g).2, ?_, ?_⟩
  · have : (e.symm g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    exact congrArg Subtype.val this
  · intro h
    have : e.symm g = 1 := Subtype.ext h
    apply hg1
    simpa using congrArg e this

theorem conj_inv (hN : ActsAsNaturalL2 L U) {s x : MulAut W} (hs : s ∈ L) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (hx : x ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨e, -, -⟩ := hN
  have h2 : (e ⟨s, hs⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨s, hs⟩ : L) ^ 2 = 1 := Subtype.ext hs2
    rw [this, map_one]
  have h3 : (e ⟨x, hx⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : L) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have h1 : e ⟨s, hs⟩ ≠ 1 := by
    intro h
    apply hs1
    have h' : (⟨s, hs⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have h1' : e ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hx1
    have h' : (⟨x, hx⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have := SL2_conj_inv _ _ h2 h1 h3 h1'
  have h4 : (⟨s, hs⟩ : L) * ⟨x, hx⟩ * ⟨s, hs⟩⁻¹ = ⟨x, hx⟩⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv]
    exact this
  exact congrArg Subtype.val h4

end Natural

theorem mem_stabSub_of_forall {U : Subgroup W} {g : MulAut W} (h1 : ∀ u ∈ U, g u ∈ U)
    (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    have := h2 _ hu
    simpa using this
  · intro hu
    exact h1 u hu

theorem exists_apply_eq_of_stab {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) {g : MulAut W}
    (hg : g ∈ stabSub U) : ∃ l ∈ L, ∀ u ∈ U, l u = g u := by
  obtain ⟨l, hl, h⟩ := exists_apply_eq hN hst (resAut U ⟨g, hg⟩)
  refine ⟨l, hl, fun u hu => ?_⟩
  exact h ⟨u, hu⟩

end S1417

end CFSG.Quasithin
