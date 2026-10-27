module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2CubicDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN

section Centralizer

variable {M : Type} [Field M]

theorem isUnit_det_torusDiag {h : ModGL Tag.F4 M} (hh : h ∈ torusGroup Tag.F4 M)
    (κ : F4A2Kind) :
    IsUnit (diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
      torusRootChar h (Pi.single κ.j 1), 1]).det := by
  have hdiag := torusGroup_le_diagonalGroup hh
  rw [det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mul_one]
  exact (mul_ne_zero (mul_ne_zero (torusRootChar_ne_zero hdiag _)
    (torusRootChar_ne_zero hdiag _)) (torusRootChar_ne_zero hdiag _)).isUnit

theorem commute_torusDiag_mul_of_commute (κ : F4A2Kind) {V : Subgroup (ModGL Tag.F4 M)}
    (hVQ : V ≤ subsystemGroup Tag.F4 M {κ.i, κ.j}) {h : ModGL Tag.F4 M}
    (hh : h ∈ torusGroup Tag.F4 M) {v : ModGL Tag.F4 M}
    (hv : v ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}) (hc : ∀ s ∈ V, h * v * s = s * (h * v))
    {s : ModGL Tag.F4 M} (hs : s ∈ V) :
    diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
        torusRootChar h (Pi.single κ.j 1), 1] *
        ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) *
        ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) =
      ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) *
        (diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
          torusRootChar h (Pi.single κ.j 1), 1] *
        ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M)) := by
  obtain ⟨hN, hconj⟩ := f4A2Equiv_torus_mul_conj κ hh hv
  have hXdet : IsUnit (diagonal ![torusRootChar h (Pi.single κ.i 1) *
      torusRootChar h (Pi.single κ.j 1), torusRootChar h (Pi.single κ.j 1), 1] *
      ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M)).det := by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact isUnit_det_torusDiag hh κ
  have hss := hconj ⟨s, hVQ hs⟩
  have e : (⟨h * v * s * (h * v)⁻¹, hN _ (hVQ hs)⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) =
      ⟨s, hVQ hs⟩ :=
    Subtype.ext (by
      change h * v * s * (h * v)⁻¹ = s
      rw [hc s hs, mul_inv_cancel_right])
  rw [e] at hss
  exact matrix_mul_comm_of_eq_conj hXdet hss

theorem mem_char_of_commute_of_scalar (κ : F4A2Kind) {V : Subgroup (ModGL Tag.F4 M)}
    (hVQ : V ≤ subsystemGroup Tag.F4 M {κ.i, κ.j})
    (hV : ∀ X : Matrix (Fin 3) (Fin 3) M, (∀ s (hs : s ∈ V),
      X * ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) =
      ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) * X) → X ∈ Set.range (scalar (Fin 3)))
    {h : ModGL Tag.F4 M} (hh : h ∈ torusGroup Tag.F4 M) {v : ModGL Tag.F4 M}
    (hv : v ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}) (hc : ∀ s ∈ V, h * v * s = s * (h * v)) :
    h * v ∈ torusGroup Tag.F4 M ∧ torusRootChar (h * v) (Pi.single κ.i 1) = 1 ∧
      torusRootChar (h * v) (Pi.single κ.j 1) = 1 := by
  obtain ⟨μ, hμ⟩ := hV _ fun s hs => commute_torusDiag_mul_of_commute κ hVQ hh hv hc hs
  have hDdet := isUnit_det_torusDiag hh κ
  have hvdiag : ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
      Matrix (Fin 3) (Fin 3) M).IsDiag := by
    have e : ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) =
        (diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
          torusRootChar h (Pi.single κ.j 1), 1])⁻¹ * scalar (Fin 3) μ := by
      rw [hμ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDdet, Matrix.one_mul]
    rw [e, Matrix.inv_diagonal, Matrix.scalar_apply, diagonal_mul_diagonal]
    exact isDiag_diagonal _
  obtain ⟨g₀, hg₀T, hg₀⟩ := (f4A2Equiv_torus_iff κ (f4A2Equiv M κ ⟨v, hv⟩)).2 hvdiag
  have hvT : v ∈ torusGroup Tag.F4 M := by
    have e := congrArg Subtype.val ((f4A2Equiv M κ).injective hg₀)
    rw [← show ((⟨v, hv⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) = v from rfl,
      ← e]
    exact subsystemTorus_le_torusGroup' hg₀T
  have hyH : h * v ∈ torusGroup Tag.F4 M := mul_mem hh hvT
  have hc' : ∀ s ∈ V, h * v * 1 * s = s * (h * v * 1) := fun s hs => by
    rw [mul_one]
    exact hc s hs
  obtain ⟨μ', hμ'⟩ := hV _ fun s hs =>
    commute_torusDiag_mul_of_commute κ hVQ hyH (one_mem _) hc' hs
  have h1 : ((f4A2Equiv M κ ⟨1, one_mem _⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
      Matrix (Fin 3) (Fin 3) M) = 1 := by
    rw [show (⟨1, one_mem _⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) = 1 from rfl, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  rw [h1, Matrix.mul_one] at hμ'
  have e00 := congrFun (congrFun hμ' 0) 0
  have e11 := congrFun (congrFun hμ' 1) 1
  have e22 := congrFun (congrFun hμ' 2) 2
  simp only [Matrix.scalar_apply, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e00 e11 e22
  have hj : torusRootChar (h * v) (Pi.single κ.j 1) = 1 := by rw [← e11, e22]
  refine ⟨hyH, ?_, hj⟩
  calc torusRootChar (h * v) (Pi.single κ.i 1) =
        torusRootChar (h * v) (Pi.single κ.i 1) * torusRootChar (h * v) (Pi.single κ.j 1) := by
        rw [hj, mul_one]
    _ = μ' := e00.symm
    _ = 1 := e22

theorem levi_centralizer_of_scalar [Finite M] [CharP M 2] (κ : F4A2Kind)
    {Z L QK V : Subgroup (ModGL Tag.F4 M)}
    (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 M ∧ torusRootChar h (Pi.single κ.i 1) = 1 ∧
      torusRootChar h (Pi.single κ.j 1) = 1)
    (hL : L = torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M {κ.i, κ.j})
    (hVQ : V ≤ subsystemGroup Tag.F4 M {κ.i, κ.j})
    (hV : ∀ X : Matrix (Fin 3) (Fin 3) M, (∀ s (hs : s ∈ V),
      X * ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) =
      ((f4A2Equiv M κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) * X) → X ∈ Set.range (scalar (Fin 3)))
    {a : ModGL Tag.F4 M} (ha : a ∈ subsystemGroup Tag.F4 M {κ.i, κ.j})
    (hQK : ∀ g, g ∈ QK ↔ ∃ y ∈ V, g = a * y * a⁻¹) :
    L ⊓ Subgroup.centralizer (QK : Set (ModGL Tag.F4 M)) = Z ∧
      (Subgroup.center L).map L.subtype = Z ∧ Odd (Nat.card Z) := by
  have hHcomm := (triangular_borel_structure.{0, 0} Tag.F4 M).1
  have hZH : ∀ z ∈ Z, z ∈ torusGroup Tag.F4 M := fun z hz => ((hZ z).1 hz).1
  have hZQ : ∀ z ∈ Z, ∀ x ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}, z * x = x * z := by
    intro z hz x hx
    obtain ⟨hzH, h1, h2⟩ := (hZ z).1 hz
    refine commute_of_mem_subsystemGroup hzH (fun k hk => ?_) hx
    rcases hk with rfl | hk
    · exact h1
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      exact h2
  have hHL : torusGroup Tag.F4 M ≤ L := hL ▸ le_sup_left
  have hQL : subsystemGroup Tag.F4 M {κ.i, κ.j} ≤ L := hL ▸ le_sup_right
  have hQKQ : ∀ g ∈ QK, g ∈ subsystemGroup Tag.F4 M {κ.i, κ.j} := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hQK g).1 hg
    exact mul_mem (mul_mem ha (hVQ hy)) (inv_mem ha)
  have hZL : ∀ z ∈ Z, ∀ g ∈ L, z * g = g * z := by
    intro z hz g hg
    have hle : L ≤ Subgroup.centralizer ({z} : Set (ModGL Tag.F4 M)) := by
      rw [hL]
      refine sup_le (fun h hh => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hHcomm h hh z (hZH z hz)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hZQ z hz x hx).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hnorm : torusGroup Tag.F4 M ≤
      Subgroup.normalizer (subsystemGroup Tag.F4 M {κ.i, κ.j} : Set (ModGL Tag.F4 M)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨hN, -⟩ := f4A2Equiv_torus_mul_conj κ hh (one_mem _)
    obtain ⟨hN', -⟩ := f4A2Equiv_torus_mul_conj κ (inv_mem hh) (one_mem _)
    constructor
    · intro hz
      have := hN z hz
      rwa [mul_one] at this
    · intro hz
      have := hN' _ hz
      have e : h⁻¹ * 1 * (h * z * h⁻¹) * (h⁻¹ * 1)⁻¹ = z := by group
      rwa [e] at this
  have hcent : L ⊓ Subgroup.centralizer (QK : Set (ModGL Tag.F4 M)) = Z := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyL, hyc⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_iff] at hyc
      have haL : a ∈ L := hQL ha
      have hy'L : a⁻¹ * y * a ∈ L := mul_mem (mul_mem (inv_mem haL) hyL) haL
      have hy'L' : a⁻¹ * y * a ∈ ((torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M {κ.i, κ.j} :
          Subgroup (ModGL Tag.F4 M)) : Set (ModGL Tag.F4 M)) := by rw [← hL]; exact hy'L
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hy'L'
      obtain ⟨h, hh, v, hv, hhv⟩ := hy'L'
      have hc : ∀ s ∈ V, h * v * s = s * (h * v) := by
        intro s hs
        have hm : a * s * a⁻¹ ∈ QK := (hQK _).2 ⟨s, hs, rfl⟩
        have e := hyc _ hm
        change h * v = a⁻¹ * y * a at hhv
        rw [hhv]
        calc a⁻¹ * y * a * s = a⁻¹ * (y * (a * s * a⁻¹)) * a := by group
          _ = a⁻¹ * ((a * s * a⁻¹) * y) * a := by rw [e]
          _ = _ := by group
      obtain ⟨hyH, h1, h2⟩ := mem_char_of_commute_of_scalar κ hVQ hV hh hv hc
      change h * v = a⁻¹ * y * a at hhv
      rw [hhv] at hyH h1 h2
      have hy' : a⁻¹ * y * a ∈ Z := (hZ _).2 ⟨hyH, h1, h2⟩
      have e : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
      rw [e, ← hZQ _ hy' _ ha, mul_inv_cancel_right]
      exact hy'
    · intro z hz
      refine Subgroup.mem_inf.2 ⟨hHL (hZH z hz), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hZQ z hz x (hQKQ x hx)).symm
  refine ⟨hcent, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      rw [← hcent]
      refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have hxL : x ∈ L := hQL (hQKQ x hx)
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hg) ⟨x, hxL⟩)
    · intro z hz
      refine Subgroup.mem_map.2 ⟨⟨z, hHL (hZH z hz)⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (hZL z hz g g.2).symm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := finite_modGL (τ := Tag.F4) (K := M)
    have hdvd : Nat.card Z ∣ Nat.card (torusGroup Tag.F4 M) :=
      Subgroup.card_dvd_of_le fun z hz => hZH z hz
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h2 => not_dvd_card_torusGroup (τ := Tag.F4) (K := M) 2 (h2.trans hdvd)

end Centralizer

end CFSG.RankThree.Chevalley
