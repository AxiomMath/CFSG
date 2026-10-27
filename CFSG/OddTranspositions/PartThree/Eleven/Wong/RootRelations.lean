module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootFourth
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootTwist

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] (D : RootData G)

section Basic

variable [Finite G]

private theorem card_Q : Nat.card D.Q = 125 :=
  (D.odd_complement_of_diagonal_centralizer).1

private theorem Q_commute {x y : G} (hx : x ∈ D.Q) (hy : y ∈ D.Q) : Commute x y :=
  (D.elementary_abelian_three_space).2.1 x hx y hy

private theorem Q_coords_unique (x : G) (hx : x ∈ D.Q) :
    ∃! a : Fin 3 → ZMod 5,
      x = D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2)) :=
  (D.elementary_abelian_three_space).2.2.2.2.1 x hx

private noncomputable def qcf (x : G) : Fin 3 → ZMod 5 := by
  classical
  exact if hx : x ∈ D.Q then Classical.choose (Q_coords_unique D x hx).exists
    else (0 : Fin 3 → ZMod 5)

private theorem qcf_spec (x : G) (hx : x ∈ D.Q) :
    x = D.q1 (.ofAdd (qcf D x 0)) * D.q2 (.ofAdd (qcf D x 1)) *
      D.q3 (.ofAdd (qcf D x 2)) := by
  rw [qcf, dif_pos hx]
  exact Classical.choose_spec (Q_coords_unique D x hx).exists

private theorem qcf_eq (x : G) (hx : x ∈ D.Q) {a : Fin 3 → ZMod 5}
    (h : x = D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2))) :
    qcf D x = a := by
  rw [qcf, dif_pos hx]
  exact ExistsUnique.unique (Q_coords_unique D x hx)
    (Classical.choose_spec (Q_coords_unique D x hx).exists) h

private theorem P1_le_Q : D.P1 ≤ D.Q := by
  intro x hx
  have hQV := (D.first_root_centralizer_odd_core).2.2.2.2.2.2
  have hP1V := (D.first_root_centralizer_odd_core).2.2.2.1
  have hxV : x ∈ D.V := hP1V hx
  have hxQV : x ∈ D.Q ⊓ D.V := by
    rw [hQV]
    exact Subgroup.mem_sup_left hx
  exact hxQV.1

private theorem P3_le_V : D.P3 ≤ D.V := by
  intro x hx
  have hV := (D.four_root_order_and_products).2.2.1
  show x ∈ (D.V : Set G)
  rw [hV]
  have hm : (1 * x) * 1 ∈ (D.P1 : Set G) * (D.P3 : Set G) * (D.P4 : Set G) :=
    Set.mul_mem_mul (Set.mul_mem_mul (one_mem _) hx) (one_mem _)
  simpa using hm

private theorem P4_le_V : D.P4 ≤ D.V := by
  intro x hx
  have hV := (D.four_root_order_and_products).2.2.1
  show x ∈ (D.V : Set G)
  rw [hV]
  have hm : (1 * 1) * x ∈ (D.P1 : Set G) * (D.P3 : Set G) * (D.P4 : Set G) :=
    Set.mul_mem_mul (Set.mul_mem_mul (one_mem _) (one_mem _)) hx
  simpa using hm

private theorem P3_le_Q : D.P3 ≤ D.Q := by
  intro x hx
  have hQV := (D.first_root_centralizer_odd_core).2.2.2.2.2.2
  have hxV : x ∈ D.V := P3_le_V D hx
  have hxQV : x ∈ D.Q ⊓ D.V := by
    rw [hQV]
    exact Subgroup.mem_sup_right hx
  exact hxQV.1

private theorem q1_mem_Q (a : ZMod 5) : D.q1 (.ofAdd a) ∈ D.Q :=
  P1_le_Q D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

private theorem q3_mem_Q (a : ZMod 5) : D.q3 (.ofAdd a) ∈ D.Q :=
  P3_le_Q D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

private theorem qcf_q1 (a : ZMod 5) :
    qcf D (D.q1 (.ofAdd a)) = Pi.single 0 a := by
  exact qcf_eq D _ (q1_mem_Q D a) (a := Pi.single 0 a) (by
    simp [Pi.single_eq_same, Pi.single_eq_of_ne])

private theorem qcf_q3 (a : ZMod 5) :
    qcf D (D.q3 (.ofAdd a)) = Pi.single 2 a := by
  exact qcf_eq D _ (q3_mem_Q D a) (a := Pi.single 2 a) (by
    simp [Pi.single_eq_same, Pi.single_eq_of_ne])

private theorem qcf_q1_zero : qcf D (1 : G) = 0 := by
  have h : (1 : G) = D.q1 (.ofAdd (0 : ZMod 5)) := by simp
  rw [h, qcf_q1]
  simp

end Basic

section QCoordEquiv

variable [Finite G]

private theorem qcf_injective_on_Q {x y : D.Q} (h : qcf D x.1 = qcf D y.1) : x = y := by
  apply Subtype.ext
  rw [qcf_spec D x.1 x.2, qcf_spec D y.1 y.2, h]

private theorem Q_coord_surjective (a : Fin 3 → ZMod 5) :
    ∃ x ∈ D.Q, x = D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2)) := by
  have : Fintype D.Q := Fintype.ofFinite D.Q
  let f : D.Q → (Fin 3 → ZMod 5) := fun x => qcf D x.1
  have hf : Function.Injective f := fun x y h => qcf_injective_on_Q D h
  have hcard : Fintype.card D.Q = Fintype.card (Fin 3 → ZMod 5) := by
    rw [show Fintype.card D.Q = 125 from by
      rw [← Nat.card_eq_fintype_card]
      exact card_Q D]
    simp [ZMod.card]
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).2
  obtain ⟨x, hx⟩ := hsurj a
  refine ⟨x.1, x.2, ?_⟩
  have hspec := qcf_spec D x.1 x.2
  rw [show qcf D x.1 = a from hx] at hspec
  exact hspec

private theorem q2_mem_Q (a : ZMod 5) : D.q2 (.ofAdd a) ∈ D.Q := by
  obtain ⟨x, hxQ, hx⟩ := Q_coord_surjective D (Pi.single (1 : Fin 3) a)
  rw [show D.q2 (.ofAdd a) = x from ?_]
  · exact hxQ
  · rw [hx]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem qcf_q2 (a : ZMod 5) :
    qcf D (D.q2 (.ofAdd a)) = Pi.single 1 a := by
  exact qcf_eq D _ (q2_mem_Q D a) (a := Pi.single (1 : Fin 3) a) (by
    simp [Pi.single_eq_same, Pi.single_eq_of_ne])

end QCoordEquiv


section VCoord

variable [Finite G]

private noncomputable def vMapFun : (ZMod 5 × ZMod 5 × ZMod 5) → D.V := fun p =>
  ⟨D.q1 (.ofAdd p.1) * D.q3 (.ofAdd p.2.1) * D.q4 (.ofAdd p.2.2), by
    have hV := (D.four_root_order_and_products).2.2.1
    show D.q1 (.ofAdd p.1) * D.q3 (.ofAdd p.2.1) * D.q4 (.ofAdd p.2.2) ∈ (D.V : Set G)
    rw [hV]
    exact Set.mul_mem_mul (Set.mul_mem_mul (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩)) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)⟩

private theorem vMapFun_surjective : Function.Surjective (vMapFun D) := by
  intro x
  have hxV : (x : G) ∈ (D.V : Set G) := x.2
  have hV := (D.four_root_order_and_products).2.2.1
  rw [hV] at hxV
  rw [Set.mem_mul] at hxV
  obtain ⟨y, hy, p4, hp4, hxy⟩ := hxV
  rw [Set.mem_mul] at hy
  obtain ⟨p1, hp1, p3, hp3, hy'⟩ := hy
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hp1
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hp3
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hp4
  subst hy'
  refine ⟨(a.toAdd, b.toAdd, c.toAdd), ?_⟩
  apply Subtype.ext
  simpa [vMapFun] using hxy

private noncomputable def vEquiv : (ZMod 5 × ZMod 5 × ZMod 5) ≃ D.V := by
  haveI : Fintype D.V := Fintype.ofFinite D.V
  refine Equiv.ofBijective (vMapFun D)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨vMapFun_surjective D, ?_⟩)
  rw [show Fintype.card D.V = 125 from by
    rw [← Nat.card_eq_fintype_card]
    exact (D.four_root_order_and_products).1]
  simp [ZMod.card]

private theorem vEquiv_apply (p : ZMod 5 × ZMod 5 × ZMod 5) :
    vEquiv D p = vMapFun D p :=
  Equiv.ofBijective_apply _ _ _

private noncomputable def vFull (x : G) : ZMod 5 × ZMod 5 × ZMod 5 := by
  classical
  exact if hx : x ∈ D.V then (vEquiv D).symm ⟨x, hx⟩ else 0

private noncomputable def vp (x : G) : ZMod 5 × ZMod 5 :=
  ((vFull D x).2.1, (vFull D x).2.2)

private theorem vFull_spec {x : G} (hx : x ∈ D.V) :
    x = D.q1 (.ofAdd (vFull D x).1) * D.q3 (.ofAdd (vFull D x).2.1) *
      D.q4 (.ofAdd (vFull D x).2.2) := by
  have h : vFull D x = (vEquiv D).symm ⟨x, hx⟩ := by rw [vFull, dif_pos hx]
  rw [h]
  have h2 := congrArg Subtype.val ((vEquiv D).apply_symm_apply ⟨x, hx⟩)
  rw [vEquiv_apply] at h2
  exact h2.symm

private theorem vFull_eq {x : G} (hx : x ∈ D.V) {a b c : ZMod 5}
    (h : x = D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) :
    vFull D x = (a, b, c) := by
  have h1 : vEquiv D (vFull D x) = vEquiv D (a, b, c) := by
    rw [show vFull D x = (vEquiv D).symm ⟨x, hx⟩ from by rw [vFull, dif_pos hx],
      (vEquiv D).apply_symm_apply, vEquiv_apply]
    apply Subtype.ext
    exact h
  exact (vEquiv D).injective h1

private theorem vp_q3 (a : ZMod 5) : vp D (D.q3 (.ofAdd a)) = (a, 0) := by
  have hmem : D.q3 (.ofAdd a) ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h := vFull_eq D hmem (a := 0) (b := a) (c := 0) (by simp)
  simp [vp, h]

private theorem vp_q4 (a : ZMod 5) : vp D (D.q4 (.ofAdd a)) = (0, a) := by
  have hmem : D.q4 (.ofAdd a) ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h := vFull_eq D hmem (a := 0) (b := 0) (c := a) (by simp)
  simp [vp, h]

end VCoord

section VMul

variable [Finite G]

private theorem P1_le_V : D.P1 ≤ D.V :=
  (D.first_root_centralizer_odd_core).2.2.2.1

private theorem P1_commute_V {z y : G} (hz : z ∈ D.P1) (hy : y ∈ D.V) : Commute z y :=
  (D.first_root_centralizer_odd_core).2.2.2.2.1 z hz y hy

private theorem commutator_V_le_P1 : ⁅D.V, D.V⁆ ≤ D.P1 :=
  (D.first_root_centralizer_odd_core).2.2.2.2.2.1

private theorem V_q3q4_mul (b c b' c' : ZMod 5) :
    ∃ t : ZMod 5,
      (D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) * (D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) =
      D.q1 (.ofAdd t) * D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c')) := by
  have hv : D.q3 (.ofAdd b) ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hv' : D.q3 (.ofAdd b') ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hw : D.q4 (.ofAdd c) ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hw' : D.q4 (.ofAdd c') ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hz : ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ ∈ D.P1 :=
    commutator_V_le_P1 D (Subgroup.commutator_mem_commutator hw hv')
  have hconj : D.q4 (.ofAdd c) * D.q3 (.ofAdd b') =
      ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ * D.q3 (.ofAdd b') * D.q4 (.ofAdd c) := by
    rw [commutatorElement_def]
    group
  obtain ⟨t, ht⟩ : ∃ t : ZMod 5, D.q1 (.ofAdd t) = ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ :=
    MonoidHom.mem_range.mp hz
  have h3add : D.q3 (.ofAdd b) * D.q3 (.ofAdd b') = D.q3 (.ofAdd (b + b')) := by
    rw [← map_mul D.q3, ofAdd_add]
  have h4add : D.q4 (.ofAdd c) * D.q4 (.ofAdd c') = D.q4 (.ofAdd (c + c')) := by
    rw [← map_mul D.q4, ofAdd_add]
  refine ⟨t, ?_⟩
  calc
    (D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) * (D.q3 (.ofAdd b') * D.q4 (.ofAdd c'))
        = D.q3 (.ofAdd b) * (D.q4 (.ofAdd c) * D.q3 (.ofAdd b')) *
            D.q4 (.ofAdd c') := by group
    _ = D.q3 (.ofAdd b) * (⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ *
            D.q3 (.ofAdd b') * D.q4 (.ofAdd c)) * D.q4 (.ofAdd c') := by rw [hconj]
    _ = D.q3 (.ofAdd b) * ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ *
            D.q3 (.ofAdd b') * D.q4 (.ofAdd c) * D.q4 (.ofAdd c') := by group
    _ = ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ * D.q3 (.ofAdd b) *
            D.q3 (.ofAdd b') * D.q4 (.ofAdd c) * D.q4 (.ofAdd c') := by
          rw [show D.q3 (.ofAdd b) * ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ =
            ⁅D.q4 (.ofAdd c), D.q3 (.ofAdd b')⁆ * D.q3 (.ofAdd b) from
            (P1_commute_V D hz hv).eq.symm]
    _ = D.q1 (.ofAdd t) * D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c')) := by
          rw [← ht, ← h3add, ← h4add]
          group

private theorem V_mul_coords (a b c a' b' c' : ZMod 5) :
    ∃ t : ZMod 5,
      (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
        (D.q1 (.ofAdd a') * D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) =
      D.q1 (.ofAdd t) * D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c')) := by
  obtain ⟨t0, ht0⟩ := V_q3q4_mul D b c b' c'
  have hu : D.q1 (.ofAdd a) ∈ D.P1 := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hu' : D.q1 (.ofAdd a') ∈ D.P1 := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hv : D.q3 (.ofAdd b) ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hv' : D.q3 (.ofAdd b') ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hw : D.q4 (.ofAdd c) ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hw' : D.q4 (.ofAdd c') ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hcomm_u' : Commute (D.q1 (.ofAdd a')) (D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) :=
    (P1_commute_V D hu' hv).mul_right (P1_commute_V D hu' hw)
  obtain ⟨t, ht⟩ : ∃ t : ZMod 5, D.q1 (.ofAdd t) =
      D.q1 (.ofAdd a) * D.q1 (.ofAdd a') * D.q1 (.ofAdd t0) := by
    have hmem : D.q1 (.ofAdd a) * D.q1 (.ofAdd a') * D.q1 (.ofAdd t0) ∈ D.P1 :=
      D.P1.mul_mem (D.P1.mul_mem hu hu') (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    exact MonoidHom.mem_range.mp hmem
  refine ⟨t, ?_⟩
  calc
    (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
        (D.q1 (.ofAdd a') * D.q3 (.ofAdd b') * D.q4 (.ofAdd c'))
        = D.q1 (.ofAdd a) * (D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
            D.q1 (.ofAdd a') * (D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) := by group
    _ = D.q1 (.ofAdd a) * ((D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
            D.q1 (.ofAdd a')) * (D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) := by group
    _ = D.q1 (.ofAdd a) * (D.q1 (.ofAdd a') *
            (D.q3 (.ofAdd b) * D.q4 (.ofAdd c))) *
            (D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) := by rw [hcomm_u'.eq.symm]
    _ = D.q1 (.ofAdd a) * D.q1 (.ofAdd a') *
            (D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
            (D.q3 (.ofAdd b') * D.q4 (.ofAdd c')) := by group
    _ = D.q1 (.ofAdd a) * D.q1 (.ofAdd a') *
            ((D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
              (D.q3 (.ofAdd b') * D.q4 (.ofAdd c'))) := by group
    _ = D.q1 (.ofAdd a) * D.q1 (.ofAdd a') *
            (D.q1 (.ofAdd t0) * D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c'))) := by
          rw [ht0]
    _ = (D.q1 (.ofAdd a) * D.q1 (.ofAdd a') * D.q1 (.ofAdd t0)) *
            D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c')) := by group
    _ = D.q1 (.ofAdd t) * D.q3 (.ofAdd (b + b')) * D.q4 (.ofAdd (c + c')) := by
          rw [← ht]

end VMul

section Powers

variable [Finite G]

omit [Finite G] in
private theorem mul_three_pow {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (n : ℕ) : (a * b * c) ^ n = a ^ n * b ^ n * c ^ n := by
  rw [show a * b * c = a * (b * c) from by group]
  rw [Commute.mul_pow (hab.mul_right hac), Commute.mul_pow hbc]
  group

private theorem Q_pow (a b c : ZMod 5) (n : ℕ) :
    (D.q1 (.ofAdd a) * D.q2 (.ofAdd b) * D.q3 (.ofAdd c)) ^ n =
      D.q1 (.ofAdd (n • a)) * D.q2 (.ofAdd (n • b)) * D.q3 (.ofAdd (n • c)) := by
  rw [mul_three_pow (Q_commute D (q1_mem_Q D a) (q2_mem_Q D b))
    (Q_commute D (q1_mem_Q D a) (q3_mem_Q D c))
    (Q_commute D (q2_mem_Q D b) (q3_mem_Q D c)) n]
  have h1 : D.q1 (.ofAdd a) ^ n = D.q1 (.ofAdd (n • a)) := by
    rw [← map_pow, ← ofAdd_nsmul]
  have h2 : D.q2 (.ofAdd b) ^ n = D.q2 (.ofAdd (n • b)) := by
    rw [← map_pow, ← ofAdd_nsmul]
  have h3 : D.q3 (.ofAdd c) ^ n = D.q3 (.ofAdd (n • c)) := by
    rw [← map_pow, ← ofAdd_nsmul]
  rw [h1, h2, h3]

private theorem V_pow_mod (A B C : ZMod 5) (n : ℕ) :
    ∃ t : ZMod 5, (D.q1 (.ofAdd A) * D.q3 (.ofAdd B) * D.q4 (.ofAdd C)) ^ n =
      D.q1 (.ofAdd t) * D.q3 (.ofAdd (n • B)) * D.q4 (.ofAdd (n • C)) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := V_mul_coords D t (n • B) (n • C) A B C
      refine ⟨t', ?_⟩
      rw [pow_succ, ht, ht']
      have hB : n • B + B = (n + 1) • B := by rw [succ_nsmul]
      have hC : n • C + C = (n + 1) • C := by rw [succ_nsmul]
      rw [← hB, ← hC]

end Powers

section Coeffs

variable [Finite G]

private theorem q4_mem_normalizer_Q : D.q4 (.ofAdd 1) ∈ normalizer (D.Q : Set G) := by
  have hUH := (D.four_root_order_and_products).2.2.2.2.2.2.2.2.2.2
  exact hUH (Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))))

private theorem q4_inv_q2_mul_mem_Q :
    (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1) ∈ D.Q := by
  have h := (Subgroup.mem_normalizer_iff''.mp (q4_mem_normalizer_Q D) (D.q2 (.ofAdd 1))).mp
    (q2_mem_Q D 1)
  simpa [mul_assoc] using h

private theorem q4_inv_q3_mul_mem_Q :
    (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1) ∈ D.Q := by
  have h := (Subgroup.mem_normalizer_iff''.mp (q4_mem_normalizer_Q D) (D.q3 (.ofAdd 1))).mp
    (q3_mem_Q D 1)
  simpa [mul_assoc] using h

private def P13 : Subgroup G where
  carrier := {x | ∃ t s : ZMod 5, x = D.q1 (.ofAdd t) * D.q3 (.ofAdd s)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨t, s, rfl⟩ ⟨t', s', rfl⟩
    refine ⟨t + t', s + s', ?_⟩
    have hc : Commute (D.q3 (.ofAdd s)) (D.q1 (.ofAdd t')) :=
      Q_commute D (q3_mem_Q D s) (q1_mem_Q D t')
    calc
      D.q1 (.ofAdd t) * D.q3 (.ofAdd s) * (D.q1 (.ofAdd t') * D.q3 (.ofAdd s'))
          = D.q1 (.ofAdd t) * (D.q3 (.ofAdd s) * D.q1 (.ofAdd t')) *
              D.q3 (.ofAdd s') := by group
      _ = D.q1 (.ofAdd t) * (D.q1 (.ofAdd t') * D.q3 (.ofAdd s)) *
              D.q3 (.ofAdd s') := by rw [hc.eq]
      _ = D.q1 (.ofAdd t) * D.q1 (.ofAdd t') *
              (D.q3 (.ofAdd s) * D.q3 (.ofAdd s')) := by group
      _ = D.q1 (.ofAdd (t + t')) * D.q3 (.ofAdd (s + s')) := by
            rw [← map_mul D.q1, ← map_mul D.q3, ofAdd_add, ofAdd_add]
  inv_mem' := by
    rintro x ⟨t, s, rfl⟩
    refine ⟨-t, -s, ?_⟩
    rw [mul_inv_rev, ← map_inv D.q3, ← map_inv D.q1, ← ofAdd_neg, ← ofAdd_neg]
    exact (Q_commute D (q3_mem_Q D (-s)) (q1_mem_Q D (-t))).eq

private theorem P13_eq : P13 D = D.P1 ⊔ D.P3 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, s, rfl⟩ := hx
    exact (D.P1 ⊔ D.P3).mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
      (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
      exact ⟨t.toAdd, 0, by simp⟩
    · intro x hx
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
      exact ⟨0, s.toAdd, by simp⟩

private theorem mem_P13 {x : G} (hx : x ∈ D.P1 ⊔ D.P3) :
    ∃ t s : ZMod 5, x = D.q1 (.ofAdd t) * D.q3 (.ofAdd s) := by
  rwa [← P13_eq D] at hx

private theorem q2_inv_q4_inv_q2_q4_mem : (D.q2 (.ofAdd 1))⁻¹ * (D.q4 (.ofAdd 1))⁻¹ *
    D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1) ∈ D.P1 ⊔ D.P3 := by
  have hu2 : D.q2 (.ofAdd 1) ∈ D.U :=
    Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hu4 : D.q4 (.ofAdd 1) ∈ D.U :=
    Subgroup.mem_sup_right (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  have hu4inv : (D.q4 (.ofAdd 1))⁻¹ ∈ D.U := by simpa using D.U.inv_mem hu4
  have hu2inv : (D.q2 (.ofAdd 1))⁻¹ ∈ D.U := by simpa using D.U.inv_mem hu2
  have hcomm : ⁅(D.q2 (.ofAdd 1))⁻¹, (D.q4 (.ofAdd 1))⁻¹⁆ ∈ ⁅D.U, D.U⁆ :=
    Subgroup.commutator_mem_commutator hu2inv hu4inv
  have hle := (D.four_root_order_and_products).2.2.2.2.2.2.2.2.1
  have hmem := hle hcomm
  have heq : (D.q2 (.ofAdd 1))⁻¹ * (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      ⁅(D.q2 (.ofAdd 1))⁻¹, (D.q4 (.ofAdd 1))⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact hmem

private theorem q4_conj_q2_form :
    ∃ m g : ZMod 5, (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd m) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd g) := by
  obtain ⟨t, s, hs⟩ := mem_P13 D (q2_inv_q4_inv_q2_q4_mem D)
  refine ⟨t, s, ?_⟩
  calc
    (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1)
        = D.q2 (.ofAdd 1) * ((D.q2 (.ofAdd 1))⁻¹ * (D.q4 (.ofAdd 1))⁻¹ *
            D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1)) := by group
    _ = D.q2 (.ofAdd 1) * (D.q1 (.ofAdd t) * D.q3 (.ofAdd s)) := by rw [hs]
    _ = D.q1 (.ofAdd t) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd s) := by
          rw [(Q_commute D (q2_mem_Q D 1) (q1_mem_Q D t)).eq.symm]
          group

private noncomputable def mcoef : ZMod 5 := Classical.choose (q4_conj_q2_form D)

private noncomputable def gcoef : ZMod 5 :=
  Classical.choose (Classical.choose_spec (q4_conj_q2_form D))

private theorem q4_conj_q2 :
    (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd (gcoef D)) :=
  Classical.choose_spec (Classical.choose_spec (q4_conj_q2_form D))

private theorem q4_conj_q3_form :
    ∃ l : ZMod 5, (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd l) * D.q3 (.ofAdd 1) := by
  have hv : D.q3 (.ofAdd 1) ∈ D.V := P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hw : D.q4 (.ofAdd 1) ∈ D.V := P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hz : ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ ∈ D.P1 :=
    commutator_V_le_P1 D (Subgroup.commutator_mem_commutator hv hw)
  have hcomm : (D.q4 (.ofAdd 1))⁻¹ * ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ *
      D.q4 (.ofAdd 1) = ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ := by
    calc
      (D.q4 (.ofAdd 1))⁻¹ * ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ * D.q4 (.ofAdd 1)
          = (D.q4 (.ofAdd 1))⁻¹ * (⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ *
              D.q4 (.ofAdd 1)) := by group
      _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q4 (.ofAdd 1) *
              ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆) := by rw [(P1_commute_V D hz hw).eq]
      _ = ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ := by group
  have hdecomp : (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ * D.q3 (.ofAdd 1) := by
    have h1 : D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1) =
        ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ * D.q4 (.ofAdd 1) * D.q3 (.ofAdd 1) := by
      rw [commutatorElement_def]
      group
    calc
      (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1)
          = (D.q4 (.ofAdd 1))⁻¹ * (D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1)) := by group
      _ = (D.q4 (.ofAdd 1))⁻¹ * (⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ *
            D.q4 (.ofAdd 1) * D.q3 (.ofAdd 1)) := by rw [h1]
      _ = ((D.q4 (.ofAdd 1))⁻¹ * ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ *
            D.q4 (.ofAdd 1)) * D.q3 (.ofAdd 1) := by group
      _ = ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ * D.q3 (.ofAdd 1) := by rw [hcomm]
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hz
  refine ⟨l.toAdd, ?_⟩
  have hl' : D.q1 (.ofAdd l.toAdd) = ⁅D.q3 (.ofAdd 1), D.q4 (.ofAdd 1)⁆ := by
    simpa using hl
  rw [hdecomp, hl']

private noncomputable def lcoef : ZMod 5 := Classical.choose (q4_conj_q3_form D)

private theorem q4_conj_q3 :
    (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd (lcoef D)) * D.q3 (.ofAdd 1) :=
  Classical.choose_spec (q4_conj_q3_form D)

private theorem P1_inf_P3 : D.P1 ⊓ D.P3 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx3⟩ := hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx1
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx3
  have hv1 := vFull_eq D (P1_le_V D (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
    (a := a.toAdd) (b := 0) (c := 0) (by simp)
  have hv3 := vFull_eq D (P3_le_V D (MonoidHom.mem_range.mpr ⟨b, rfl⟩))
    (a := 0) (b := b.toAdd) (c := 0) (by simp)
  rw [← hb] at hv1
  rw [hv1] at hv3
  have ha0 : a.toAdd = 0 := by
    have := congrArg (fun p : ZMod 5 × ZMod 5 × ZMod 5 => p.1) hv3
    simpa using this
  have ha1 : a = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using ha0
  rw [Subgroup.mem_bot, ha1, map_one]

end Coeffs

section TuvAction

variable [Finite G]

omit [Finite G] in
private theorem v_conj_q2 : D.v⁻¹ * D.q2 (.ofAdd 1) * D.v = (D.q2 (.ofAdd 1))⁻¹ := by
  have hv : D.v = D.h1 * D.h2 := rfl
  have h3 : D.q2 (.ofAdd ((4 : ZMod 5) * 1)) = (D.q2 (.ofAdd 1))⁻¹ := by
    rw [show ((4 : ZMod 5) * 1) = -1 from by decide]
    simp only [ofAdd_neg, map_inv]
  calc
    D.v⁻¹ * D.q2 (.ofAdd 1) * D.v
        = D.h2⁻¹ * (D.h1⁻¹ * D.q2 (.ofAdd 1) * D.h1) * D.h2 := by
          rw [hv]; group
    _ = D.h2⁻¹ * D.q2 (.ofAdd 1) * D.h2 := by rw [D.h1_conj_q2]
    _ = D.q2 (.ofAdd ((4 : ZMod 5) * 1)) := D.h2_conj_q2 1
    _ = (D.q2 (.ofAdd 1))⁻¹ := h3

private theorem v_conj_q3 : D.v⁻¹ * D.q3 (.ofAdd 1) * D.v = (D.q3 (.ofAdd 1))⁻¹ := by
  obtain ⟨ρ, hρ2, hρ⟩ := (D.elementary_abelian_three_space).2.2.2.2.2
  have hv : D.v = D.h1 * D.h2 := rfl
  have h1a := (hρ 1).1
  have h2a := (hρ ρ).2
  have hρρ : ρ * ρ = -1 := by
    have := hρ2
    rw [pow_two] at this
    exact this
  have hρ1 : D.q3 (.ofAdd (ρ * ρ)) = (D.q3 (.ofAdd 1))⁻¹ := by
    rw [hρρ]
    simp only [ofAdd_neg, map_inv]
  calc
    D.v⁻¹ * D.q3 (.ofAdd 1) * D.v
        = D.h2⁻¹ * (D.h1⁻¹ * D.q3 (.ofAdd 1) * D.h1) * D.h2 := by
          rw [hv]; group
    _ = D.h2⁻¹ * D.q3 (.ofAdd (ρ * 1)) * D.h2 := by rw [h1a]
    _ = D.h2⁻¹ * D.q3 (.ofAdd ρ) * D.h2 := by rw [mul_one]
    _ = D.q3 (.ofAdd (ρ * ρ)) := h2a
    _ = (D.q3 (.ofAdd 1))⁻¹ := hρ1

omit [Finite G] in
private theorem tuv_conj_q1 : (D.t * D.u * D.v)⁻¹ * D.q1 (.ofAdd 1) * (D.t * D.u * D.v) =
    (D.q2 (.ofAdd 1))⁻¹ := by
  calc
    (D.t * D.u * D.v)⁻¹ * D.q1 (.ofAdd 1) * (D.t * D.u * D.v)
        = D.v⁻¹ * (D.u⁻¹ * (D.t⁻¹ * D.q1 (.ofAdd 1) * D.t) * D.u) * D.v := by group
    _ = D.v⁻¹ * (D.u⁻¹ * D.q1 (.ofAdd 1) * D.u) * D.v := by rw [D.t_conj_q1]
    _ = D.v⁻¹ * D.q2 (.ofAdd 1) * D.v := by rw [D.u_conj_q1]
    _ = (D.q2 (.ofAdd 1))⁻¹ := v_conj_q2 D

omit [Finite G] in
private theorem tuv_conj_q2 : (D.t * D.u * D.v)⁻¹ * D.q2 (.ofAdd 1) * (D.t * D.u * D.v) =
    (D.q1 (.ofAdd 1))⁻¹ := by
  calc
    (D.t * D.u * D.v)⁻¹ * D.q2 (.ofAdd 1) * (D.t * D.u * D.v)
        = D.v⁻¹ * (D.u⁻¹ * (D.t⁻¹ * D.q2 (.ofAdd 1) * D.t) * D.u) * D.v := by group
    _ = D.v⁻¹ * (D.u⁻¹ * D.q2 (.ofAdd 1) * D.u) * D.v := by rw [D.t_conj_q2]
    _ = D.v⁻¹ * D.q1 (.ofAdd 1) * D.v := by rw [D.u_conj_q2]
    _ = (D.q1 (.ofAdd 1))⁻¹ := by
          rw [show D.v = D.h1 * D.h2 from rfl]
          calc
            (D.h1 * D.h2)⁻¹ * D.q1 (.ofAdd 1) * (D.h1 * D.h2)
                = D.h2⁻¹ * (D.h1⁻¹ * D.q1 (.ofAdd 1) * D.h1) * D.h2 := by group
            _ = D.h2⁻¹ * D.q1 (.ofAdd ((4 : ZMod 5) * 1)) * D.h2 := by rw [D.h1_conj_q1]
            _ = D.q1 (.ofAdd ((4 : ZMod 5) * 1)) := by rw [D.h2_conj_q1]
            _ = (D.q1 (.ofAdd 1))⁻¹ := by
                  rw [show ((4 : ZMod 5) * 1) = -1 from by decide]
                  simp only [ofAdd_neg, map_inv]

private theorem tuv_conj_q3 : (D.t * D.u * D.v)⁻¹ * D.q3 (.ofAdd 1) * (D.t * D.u * D.v) =
    (D.q3 (.ofAdd 1))⁻¹ := by
  calc
    (D.t * D.u * D.v)⁻¹ * D.q3 (.ofAdd 1) * (D.t * D.u * D.v)
        = D.v⁻¹ * (D.u⁻¹ * (D.t⁻¹ * D.q3 (.ofAdd 1) * D.t) * D.u) * D.v := by group
    _ = D.v⁻¹ * (D.u⁻¹ * D.q3 (.ofAdd (-1)) * D.u) * D.v := by rw [D.t_conj_q3]
    _ = D.v⁻¹ * D.q3 (.ofAdd 1) * D.v := by
          rw [D.u_conj_q3]
          norm_num
    _ = (D.q3 (.ofAdd 1))⁻¹ := v_conj_q3 D

end TuvAction

section StepTwo

variable [Finite G]

private theorem Q_mul_triple (a b c a' b' c' : ZMod 5) :
    (D.q1 (.ofAdd a) * D.q2 (.ofAdd b) * D.q3 (.ofAdd c)) *
      (D.q1 (.ofAdd a') * D.q2 (.ofAdd b') * D.q3 (.ofAdd c')) =
      D.q1 (.ofAdd (a + a')) * D.q2 (.ofAdd (b + b')) * D.q3 (.ofAdd (c + c')) := by
  let u1 : D.Q := ⟨D.q1 (.ofAdd a), q1_mem_Q D a⟩
  let v1 : D.Q := ⟨D.q2 (.ofAdd b), q2_mem_Q D b⟩
  let w1 : D.Q := ⟨D.q3 (.ofAdd c), q3_mem_Q D c⟩
  let u2 : D.Q := ⟨D.q1 (.ofAdd a'), q1_mem_Q D a'⟩
  let v2 : D.Q := ⟨D.q2 (.ofAdd b'), q2_mem_Q D b'⟩
  let w2 : D.Q := ⟨D.q3 (.ofAdd c'), q3_mem_Q D c'⟩
  let : CommGroup D.Q :=
    { (inferInstance : Group D.Q) with
      mul_comm := fun x y =>
        Subtype.ext (D.elementary_abelian_three_space.2.1 x.1 x.2 y.1 y.2).eq }
  have key : ((u1 * v1 * w1) * (u2 * v2 * w2) : D.Q) = (u1 * u2) * (v1 * v2) * (w1 * w2) := by
    ac_rfl
  have hG := congrArg Subtype.val key
  simp only [Subgroup.coe_mul] at hG
  have h1a : D.q1 (.ofAdd a) * D.q1 (.ofAdd a') = D.q1 (.ofAdd (a + a')) := by
    rw [← map_mul D.q1, ofAdd_add]
  have h2a : D.q2 (.ofAdd b) * D.q2 (.ofAdd b') = D.q2 (.ofAdd (b + b')) := by
    rw [← map_mul D.q2, ofAdd_add]
  have h3a : D.q3 (.ofAdd c) * D.q3 (.ofAdd c') = D.q3 (.ofAdd (c + c')) := by
    rw [← map_mul D.q3, ofAdd_add]
  rw [h1a, h2a, h3a] at hG
  simpa [u1, v1, w1, u2, v2, w2] using hG

private theorem Q_inv_triple (a b c : ZMod 5) :
    (D.q1 (.ofAdd a) * D.q2 (.ofAdd b) * D.q3 (.ofAdd c))⁻¹ =
      D.q1 (.ofAdd (-a)) * D.q2 (.ofAdd (-b)) * D.q3 (.ofAdd (-c)) := by
  have h : (D.q1 (.ofAdd a) * D.q2 (.ofAdd b) * D.q3 (.ofAdd c)) *
      (D.q1 (.ofAdd (-a)) * D.q2 (.ofAdd (-b)) * D.q3 (.ofAdd (-c))) = 1 := by
    rw [Q_mul_triple]
    simp
  exact eq_inv_of_mul_eq_one_right h |>.symm

private def Xelem : G := D.t * D.u * D.v * D.q4 (.ofAdd 1)

omit [Finite G] in
private theorem Xelem_cube : Xelem D ^ 3 = 1 :=
  (D.twist_root_and_weyl_images).2.2

private theorem X_conj_q1 :
    (Xelem D)⁻¹ * D.q1 (.ofAdd 1) * Xelem D =
      D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) * D.q3 (.ofAdd (-(gcoef D))) := by
  calc
    (Xelem D)⁻¹ * D.q1 (.ofAdd 1) * Xelem D
        = (D.q4 (.ofAdd 1))⁻¹ * ((D.t * D.u * D.v)⁻¹ * D.q1 (.ofAdd 1) *
            (D.t * D.u * D.v)) * D.q4 (.ofAdd 1) := by
          rw [Xelem]; group
    _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q2 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd 1) := by rw [tuv_conj_q1]
    _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1))⁻¹ := by group
    _ = (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd (gcoef D)))⁻¹ := by
          rw [← q4_conj_q2]
    _ = D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) * D.q3 (.ofAdd (-(gcoef D))) :=
          Q_inv_triple D _ _ _

private theorem X_conj_q2 :
    (Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D = (D.q1 (.ofAdd 1))⁻¹ := by
  calc
    (Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D
        = (D.q4 (.ofAdd 1))⁻¹ * ((D.t * D.u * D.v)⁻¹ * D.q2 (.ofAdd 1) *
            (D.t * D.u * D.v)) * D.q4 (.ofAdd 1) := by
          rw [Xelem]; group
    _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q1 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd 1) := by rw [tuv_conj_q2]
    _ = (D.q1 (.ofAdd 1))⁻¹ := by
          have hc : Commute ((D.q4 (.ofAdd 1))⁻¹) ((D.q1 (.ofAdd 1))⁻¹) :=
            (P1_commute_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
              (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))).symm.inv_left.inv_right
          rw [hc.eq]
          group

private theorem X_conj_q3 :
    (Xelem D)⁻¹ * D.q3 (.ofAdd 1) * Xelem D =
      D.q1 (.ofAdd (-(lcoef D))) * D.q3 (.ofAdd (-1)) := by
  calc
    (Xelem D)⁻¹ * D.q3 (.ofAdd 1) * Xelem D
        = (D.q4 (.ofAdd 1))⁻¹ * ((D.t * D.u * D.v)⁻¹ * D.q3 (.ofAdd 1) *
            (D.t * D.u * D.v)) * D.q4 (.ofAdd 1) := by
          rw [Xelem]; group
    _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q3 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd 1) := by rw [tuv_conj_q3]
    _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1))⁻¹ := by group
    _ = (D.q1 (.ofAdd (lcoef D)) * D.q3 (.ofAdd 1))⁻¹ := by rw [← q4_conj_q3]
    _ = (D.q1 (.ofAdd (lcoef D)) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd 1))⁻¹ := by simp
    _ = D.q1 (.ofAdd (-(lcoef D))) * D.q2 (.ofAdd (-0)) * D.q3 (.ofAdd (-1)) :=
          Q_inv_triple D _ _ _
    _ = D.q1 (.ofAdd (-(lcoef D))) * D.q3 (.ofAdd (-1)) := by simp

end StepTwo

section StepTwoMain

variable [Finite G]

omit [Finite G] in
private theorem conj_pow (g y : G) (n : ℕ) : g⁻¹ * y ^ n * g = (g⁻¹ * y * g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [show g⁻¹ * (y ^ n * y) * g = (g⁻¹ * y ^ n * g) * (g⁻¹ * y * g) from by group]
      rw [ih]

omit [Finite G] in
private theorem q1_pow_val (a : ZMod 5) :
    D.q1 (.ofAdd a) = (D.q1 (.ofAdd 1)) ^ a.val := by
  rw [← map_pow, ← ofAdd_nsmul,
    show a.val • (1 : ZMod 5) = a from by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]]

omit [Finite G] in
private theorem q3_pow_val (a : ZMod 5) :
    D.q3 (.ofAdd a) = (D.q3 (.ofAdd 1)) ^ a.val := by
  rw [← map_pow, ← ofAdd_nsmul,
    show a.val • (1 : ZMod 5) = a from by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]]

private theorem conj_xelem_power_product_eq_q2_one :
    (D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D)))) ^ (mcoef D).val *
        (D.q1 (.ofAdd 1))⁻¹ *
        (D.q1 (.ofAdd (-(lcoef D))) * D.q2 (.ofAdd 0) *
          D.q3 (.ofAdd (-1))) ^ (gcoef D).val = D.q2 (.ofAdd 1) := by
  have hX3 : Xelem D ^ 3 = 1 := Xelem_cube D
  have hfix : (Xelem D)⁻¹ * ((Xelem D)⁻¹ * ((Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D) *
      Xelem D) * Xelem D = D.q2 (.ofAdd 1) := by
    rw [show (Xelem D)⁻¹ * ((Xelem D)⁻¹ * ((Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D) *
      Xelem D) * Xelem D = ((Xelem D) ^ 3)⁻¹ * D.q2 (.ofAdd 1) * (Xelem D) ^ 3 from by
        rw [show (Xelem D) ^ 3 = (Xelem D) * (Xelem D) * (Xelem D) from by
          rw [pow_three]; group]
        group]
    rw [hX3, inv_one, one_mul, mul_one]
  have step1 : (Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D = (D.q1 (.ofAdd 1))⁻¹ :=
    X_conj_q2 D
  have step2 : (Xelem D)⁻¹ * (D.q1 (.ofAdd 1))⁻¹ * Xelem D =
      D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd (gcoef D)) := by
    rw [show (Xelem D)⁻¹ * (D.q1 (.ofAdd 1))⁻¹ * Xelem D =
        ((Xelem D)⁻¹ * D.q1 (.ofAdd 1) * Xelem D)⁻¹ from by group]
    rw [X_conj_q1, Q_inv_triple]
    simp
  have hq1 : (Xelem D)⁻¹ * D.q1 (.ofAdd (mcoef D)) * Xelem D =
      (D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D)))) ^ (mcoef D).val := by
    rw [q1_pow_val D (mcoef D), conj_pow]
    congr 1
    exact X_conj_q1 D
  have hq3 : (Xelem D)⁻¹ * D.q3 (.ofAdd (gcoef D)) * Xelem D =
      (D.q1 (.ofAdd (-(lcoef D))) * D.q2 (.ofAdd 0) *
        D.q3 (.ofAdd (-1))) ^ (gcoef D).val := by
    rw [q3_pow_val D (gcoef D), conj_pow]
    congr 1
    rw [X_conj_q3]
    simp
  have step3 : (Xelem D)⁻¹ * (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) *
      D.q3 (.ofAdd (gcoef D))) * Xelem D =
      (D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D)))) ^ (mcoef D).val * (D.q1 (.ofAdd 1))⁻¹ *
        (D.q1 (.ofAdd (-(lcoef D))) * D.q2 (.ofAdd 0) *
          D.q3 (.ofAdd (-1))) ^ (gcoef D).val := by
    rw [show (Xelem D)⁻¹ * (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) *
        D.q3 (.ofAdd (gcoef D))) * Xelem D =
        ((Xelem D)⁻¹ * D.q1 (.ofAdd (mcoef D)) * Xelem D) *
          ((Xelem D)⁻¹ * D.q2 (.ofAdd 1) * Xelem D) *
          ((Xelem D)⁻¹ * D.q3 (.ofAdd (gcoef D)) * Xelem D) from by group]
    rw [hq1, step1, hq3]
  rw [← step3, ← step2, ← step1]
  exact hfix

private theorem conj_xelem_power_product_expand :
    (D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D)))) ^ (mcoef D).val *
        (D.q1 (.ofAdd 1))⁻¹ *
        (D.q1 (.ofAdd (-(lcoef D))) * D.q2 (.ofAdd 0) *
          D.q3 (.ofAdd (-1))) ^ (gcoef D).val =
      D.q1 (.ofAdd ((mcoef D).val • (-(mcoef D)) + (-1) +
          (gcoef D).val • (-(lcoef D)))) *
        D.q2 (.ofAdd ((mcoef D).val • (-1))) *
        D.q3 (.ofAdd ((mcoef D).val • (-(gcoef D)) + (gcoef D).val • (-1))) := by
  rw [Q_pow, Q_pow]
  rw [show (D.q1 (.ofAdd 1))⁻¹ = D.q1 (.ofAdd (-1)) from by
    rw [← map_inv D.q1, ofAdd_neg]]
  have hmul1 : (D.q1 (.ofAdd ((mcoef D).val • (-(mcoef D)))) *
      D.q2 (.ofAdd ((mcoef D).val • (-1))) *
        D.q3 (.ofAdd ((mcoef D).val • (-(gcoef D))))) *
      D.q1 (.ofAdd (-1)) =
        D.q1 (.ofAdd ((mcoef D).val • (-(mcoef D)) + (-1))) *
          D.q2 (.ofAdd ((mcoef D).val • (-1))) *
          D.q3 (.ofAdd ((mcoef D).val • (-(gcoef D)))) := by
    rw [show D.q1 (.ofAdd (-1)) =
        D.q1 (.ofAdd (-1)) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd 0) from by simp]
    rw [Q_mul_triple]
    simp
  rw [hmul1]
  rw [Q_mul_triple]
  simp

private theorem conj_xelem_q2_coordinate_constraints
    (h : D.q1 (.ofAdd ((mcoef D).val • (-(mcoef D)) + (-1) +
          (gcoef D).val • (-(lcoef D)))) *
        D.q2 (.ofAdd ((mcoef D).val • (-1))) *
        D.q3 (.ofAdd ((mcoef D).val • (-(gcoef D)) + (gcoef D).val • (-1))) =
      D.q2 (.ofAdd 1)) :
    (mcoef D).val • (-1 : ZMod 5) = 1 ∧
      (mcoef D).val • (-(mcoef D)) + (-1 : ZMod 5) +
        (gcoef D).val • (-(lcoef D)) = 0 := by
  have hcoord : (![((mcoef D).val • (-(mcoef D)) + (-1) + (gcoef D).val • (-(lcoef D))),
      ((mcoef D).val • (-1)),
      ((mcoef D).val • (-(gcoef D)) + (gcoef D).val • (-1))] : Fin 3 → ZMod 5) =
      Pi.single (1 : Fin 3) (1 : ZMod 5) := by
    have h1 := qcf_eq D _ (q2_mem_Q D 1)
      (a := ![((mcoef D).val • (-(mcoef D)) + (-1) + (gcoef D).val • (-(lcoef D))),
        ((mcoef D).val • (-1)),
        ((mcoef D).val • (-(gcoef D)) + (gcoef D).val • (-1))]) (by
          rw [show D.q2 (.ofAdd 1) = D.q1 (.ofAdd 0) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd 0) from
            by simp]
          rw [← h]
          simp [Matrix.cons_val_zero, Matrix.cons_val_one])
    rw [qcf_q2] at h1
    exact h1.symm
  have hY : (mcoef D).val • (-1 : ZMod 5) = 1 := by
    have h := congrFun hcoord 1
    simpa using h
  have hX : (mcoef D).val • (-(mcoef D)) + (-1 : ZMod 5) +
      (gcoef D).val • (-(lcoef D)) = 0 := by
    have h := congrFun hcoord 0
    simpa using h
  exact ⟨hY, hX⟩

private theorem step2_coeffs : mcoef D = -1 ∧ lcoef D * gcoef D = 3 := by
  have hpow := conj_xelem_power_product_eq_q2_one D
  have hexpand := conj_xelem_power_product_expand D
  have hq2 : D.q1 (.ofAdd ((mcoef D).val • (-(mcoef D)) + (-1) +
        (gcoef D).val • (-(lcoef D)))) *
      D.q2 (.ofAdd ((mcoef D).val • (-1))) *
      D.q3 (.ofAdd ((mcoef D).val • (-(gcoef D)) + (gcoef D).val • (-1))) =
      D.q2 (.ofAdd 1) := by
    rw [← hexpand]
    exact hpow
  obtain ⟨hY, hX⟩ := conj_xelem_q2_coordinate_constraints D hq2
  have hm : mcoef D = -1 := by
    have h := hY
    rw [nsmul_eq_mul] at h
    rw [ZMod.natCast_zmod_val] at h
    have h' : mcoef D * (-1 : ZMod 5) = -mcoef D := by ring
    rw [h'] at h
    linear_combination -h
  refine ⟨hm, ?_⟩
  have hgl : gcoef D * lcoef D = 3 := by
    have h := hX
    rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hm] at h
    have h1 : (-1 : ZMod 5) * -(-1) = -1 := by decide
    rw [h1] at h
    have h2 : gcoef D * (-(lcoef D)) = -(gcoef D * lcoef D) := by ring
    rw [h2] at h
    have h3 : (-1 : ZMod 5) + -1 = -2 := by decide
    rw [h3] at h
    rw [show (-2 : ZMod 5) = 3 from by decide] at h
    linear_combination -h
  rw [mul_comm]
  exact hgl

end StepTwoMain

section PairAction

variable [Finite G]

omit [Finite G] in
private theorem c2_mul_c2 : D.c2 * D.c2 = D.t := by
  rw [show D.c2 = D.i2 cM from rfl, ← map_mul, ← pow_two, cM_sq, ← D.t_eq_i2]

omit [Finite G] in
private theorem c2_conj_q4 (a : ZMod 5) :
    D.c2⁻¹ * D.q4 (.ofAdd a) * D.c2 = D.q3 (.ofAdd (-a)) := by
  have h : D.t⁻¹ = D.c2⁻¹ * D.c2⁻¹ := by
    rw [← c2_mul_c2 D, mul_inv_rev]
  rw [q4_ofAdd]
  calc
    D.c2⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.c2
        = (D.c2⁻¹ * D.c2⁻¹) * D.q3 (.ofAdd a) * (D.c2 * D.c2) := by group
    _ = D.t⁻¹ * D.q3 (.ofAdd a) * D.t := by rw [← h, c2_mul_c2]
    _ = D.q3 (.ofAdd (-a)) := D.t_conj_q3 a

omit [Finite G] in
private theorem c2_mul_q3_mul_c2_inv (b : ZMod 5) :
    D.c2 * D.q3 (.ofAdd b) * D.c2⁻¹ = D.q4 (.ofAdd (-b)) := by
  have ht : D.t⁻¹ * D.q3 (.ofAdd (-b)) * D.t = D.q3 (.ofAdd b) := by
    simpa using D.t_conj_q3 (-b)
  have hq3 : D.q3 (.ofAdd b) =
      D.c2⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd (-b)) * D.c2) * D.c2 := by
    rw [← ht, ← c2_mul_c2 D, mul_inv_rev]
    group
  rw [q4_ofAdd]
  calc
    D.c2 * D.q3 (.ofAdd b) * D.c2⁻¹
        = D.c2 * (D.c2⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd (-b)) * D.c2) * D.c2) *
            D.c2⁻¹ := by rw [hq3]
    _ = D.c2⁻¹ * D.q3 (.ofAdd (-b)) * D.c2 := by group

omit [Finite G] in
private theorem c2_mul_q4_mul_c2_inv (c : ZMod 5) :
    D.c2 * D.q4 (.ofAdd c) * D.c2⁻¹ = D.q3 (.ofAdd c) := by
  rw [q4_ofAdd]
  group

private theorem vp_q1 (a : ZMod 5) : vp D (D.q1 (.ofAdd a)) = (0, 0) := by
  have hmem : D.q1 (.ofAdd a) ∈ D.V :=
    P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h := vFull_eq D hmem (a := a) (b := 0) (c := 0) (by simp)
  simp [vp, h]

private theorem vp_mul {x y : G} (hx : x ∈ D.V) (hy : y ∈ D.V) :
    vp D (x * y) = vp D x + vp D y := by
  obtain ⟨a, b, c, hx'⟩ : ∃ a b c, vFull D x = (a, b, c) := ⟨_, _, _, rfl⟩
  obtain ⟨a', b', c', hy'⟩ : ∃ a' b' c', vFull D y = (a', b', c') := ⟨_, _, _, rfl⟩
  have hxspec := vFull_spec D hx
  have hyspec := vFull_spec D hy
  rw [hx'] at hxspec
  rw [hy'] at hyspec
  obtain ⟨t, ht⟩ := V_mul_coords D a b c a' b' c'
  have hmem : x * y ∈ D.V := D.V.mul_mem hx hy
  have hfull : vFull D (x * y) = (t, b + b', c + c') := by
    refine vFull_eq D hmem ?_
    rw [hxspec, hyspec, ht]
  have hvx : vp D x = (b, c) := by simp [vp, hx']
  have hvy : vp D y = (b', c') := by simp [vp, hy']
  rw [hvx, hvy]
  simp only [vp]
  rw [hfull]
  simp

private theorem vp_one : vp D (1 : G) = 0 := by
  have hmem : (1 : G) ∈ D.V := D.V.one_mem
  have h : vFull D 1 = (0, 0, 0) := by
    refine vFull_eq D hmem ?_
    simp
  simp [vp, h]

private theorem vp_pow {x : G} (hx : x ∈ D.V) (n : ℕ) :
    vp D (x ^ n) = n • vp D x := by
  induction n with
  | zero => simp [vp_one D]
  | succ n ih =>
      rw [pow_succ, vp_mul D (D.V.pow_mem hx n) hx, ih, succ_nsmul]

private theorem vp_inv {x : G} (hx : x ∈ D.V) : vp D x⁻¹ = -vp D x := by
  have h := vp_mul D hx (D.V.inv_mem hx)
  rw [mul_inv_cancel, vp_one D] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem c2_conj_mem_vp {x : G} (hx : x ∈ D.V) :
    D.c2⁻¹ * x * D.c2 ∈ D.V ∧
      vp D (D.c2⁻¹ * x * D.c2) = (-(vp D x).2, (vp D x).1) := by
  obtain ⟨a, b, c, hx'⟩ : ∃ a b c, vFull D x = (a, b, c) := ⟨_, _, _, rfl⟩
  have hxspec := vFull_spec D hx
  rw [hx'] at hxspec
  have hvx : vp D x = (b, c) := by simp [vp, hx']
  have hconj : D.c2⁻¹ * x * D.c2 =
      D.q1 (.ofAdd a) * D.q4 (.ofAdd b) * D.q3 (.ofAdd (-c)) := by
    rw [hxspec]
    rw [show D.c2⁻¹ * (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
          D.c2 =
        (D.c2⁻¹ * D.q1 (.ofAdd a) * D.c2) * (D.c2⁻¹ * D.q3 (.ofAdd b) * D.c2) *
          (D.c2⁻¹ * D.q4 (.ofAdd c) * D.c2) from by group]
    rw [D.c2_conj_q1 (.ofAdd a), ← q4_ofAdd D b, c2_conj_q4 D c]
  have hq1V : D.q1 (.ofAdd a) ∈ D.V :=
    P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq4V : D.q4 (.ofAdd b) ∈ D.V :=
    P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq3V : D.q3 (.ofAdd (-c)) ∈ D.V :=
    P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hmul : D.q1 (.ofAdd a) * D.q4 (.ofAdd b) * D.q3 (.ofAdd (-c)) ∈ D.V :=
    D.V.mul_mem (D.V.mul_mem hq1V hq4V) hq3V
  have hvp : vp D (D.q1 (.ofAdd a) * D.q4 (.ofAdd b) * D.q3 (.ofAdd (-c))) =
      (-c, b) := by
    rw [vp_mul D (D.V.mul_mem hq1V hq4V) hq3V, vp_mul D hq1V hq4V,
      vp_q1 D a, vp_q4 D b, vp_q3 D (-c)]
    simp
  refine ⟨?_, ?_⟩
  · rw [hconj]
    exact hmul
  · rw [hconj, hvp, hvx]

private theorem c2_mul_mem_vp {x : G} (hx : x ∈ D.V) :
    D.c2 * x * D.c2⁻¹ ∈ D.V ∧
      vp D (D.c2 * x * D.c2⁻¹) = ((vp D x).2, -(vp D x).1) := by
  obtain ⟨a, b, c, hx'⟩ : ∃ a b c, vFull D x = (a, b, c) := ⟨_, _, _, rfl⟩
  have hxspec := vFull_spec D hx
  rw [hx'] at hxspec
  have hvx : vp D x = (b, c) := by simp [vp, hx']
  have hq1 : D.c2 * D.q1 (.ofAdd a) * D.c2⁻¹ = D.q1 (.ofAdd a) := by
    calc
      D.c2 * D.q1 (.ofAdd a) * D.c2⁻¹
          = D.c2 * (D.c2⁻¹ * D.q1 (.ofAdd a) * D.c2) * D.c2⁻¹ := by
            rw [D.c2_conj_q1 (.ofAdd a)]
      _ = D.q1 (.ofAdd a) := by group
  have hconj : D.c2 * x * D.c2⁻¹ =
      D.q1 (.ofAdd a) * D.q4 (.ofAdd (-b)) * D.q3 (.ofAdd c) := by
    rw [hxspec]
    rw [show D.c2 * (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
          D.c2⁻¹ =
        (D.c2 * D.q1 (.ofAdd a) * D.c2⁻¹) * (D.c2 * D.q3 (.ofAdd b) * D.c2⁻¹) *
          (D.c2 * D.q4 (.ofAdd c) * D.c2⁻¹) from by group]
    rw [hq1, c2_mul_q3_mul_c2_inv D b, c2_mul_q4_mul_c2_inv D c]
  have hq1V : D.q1 (.ofAdd a) ∈ D.V :=
    P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq4V : D.q4 (.ofAdd (-b)) ∈ D.V :=
    P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq3V : D.q3 (.ofAdd c) ∈ D.V :=
    P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hmul : D.q1 (.ofAdd a) * D.q4 (.ofAdd (-b)) * D.q3 (.ofAdd c) ∈ D.V :=
    D.V.mul_mem (D.V.mul_mem hq1V hq4V) hq3V
  have hvp : vp D (D.q1 (.ofAdd a) * D.q4 (.ofAdd (-b)) * D.q3 (.ofAdd c)) =
      (c, -b) := by
    rw [vp_mul D (D.V.mul_mem hq1V hq4V) hq3V, vp_mul D hq1V hq4V,
      vp_q1 D a, vp_q4 D (-b), vp_q3 D c]
    simp
  refine ⟨?_, ?_⟩
  · rw [hconj]
    exact hmul
  · rw [hconj, hvp, hvx]

private theorem q2_one_inv_eq_q4_conj_triple_inv :
    (D.q2 (.ofAdd 1))⁻¹ =
        D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) *
          D.q3 (.ofAdd (gcoef D)))⁻¹ * (D.q4 (.ofAdd 1))⁻¹ := by
  have hq2 : D.q2 (.ofAdd 1) =
      D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) *
        D.q3 (.ofAdd (gcoef D))) * (D.q4 (.ofAdd 1))⁻¹ := by
    rw [← q4_conj_q2 D]
    group
  conv_lhs => rw [hq2]
  group

private theorem q2_inv_q4_mul_q2_combine :
    D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D))) * D.q2 (.ofAdd 1) =
      D.q1 (.ofAdd (-(mcoef D))) * D.q3 (.ofAdd (-(gcoef D))) := by
  have hq : D.q2 (.ofAdd (-1)) * D.q2 (.ofAdd 1) = 1 := by
    rw [← map_mul D.q2, ← ofAdd_add,
      show (-1 : ZMod 5) + 1 = 0 from by decide]
    simp
  have hcomm23 : D.q3 (.ofAdd (-(gcoef D))) * D.q2 (.ofAdd 1) =
      D.q2 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) :=
    (Q_commute D (q3_mem_Q D (-(gcoef D))) (q2_mem_Q D 1)).eq
  calc
    D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
        D.q3 (.ofAdd (-(gcoef D))) * D.q2 (.ofAdd 1)
        = D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
            (D.q3 (.ofAdd (-(gcoef D))) * D.q2 (.ofAdd 1)) := by group
    _ = D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
            (D.q2 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D)))) := by rw [hcomm23]
    _ = D.q1 (.ofAdd (-(mcoef D))) * D.q2 (.ofAdd (-1)) *
            D.q2 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) := by group
    _ = D.q1 (.ofAdd (-(mcoef D))) *
            (D.q2 (.ofAdd (-1)) * D.q2 (.ofAdd 1)) *
              D.q3 (.ofAdd (-(gcoef D))) := by group
    _ = D.q1 (.ofAdd (-(mcoef D))) * 1 * D.q3 (.ofAdd (-(gcoef D))) := by rw [hq]
    _ = D.q1 (.ofAdd (-(mcoef D))) * D.q3 (.ofAdd (-(gcoef D))) := by group

private theorem q2_one_conj_q4 :
    (D.q2 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd 1) * D.q2 (.ofAdd 1) =
      D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
        D.q1 (.ofAdd (-(mcoef D))) := by
  calc
    (D.q2 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd 1) * D.q2 (.ofAdd 1)
        = D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) *
            D.q3 (.ofAdd (gcoef D)))⁻¹ * D.q2 (.ofAdd 1) := by
          rw [q2_one_inv_eq_q4_conj_triple_inv D]
          group
    _ = D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (-(mcoef D))) *
          D.q2 (.ofAdd (-1)) * D.q3 (.ofAdd (-(gcoef D)))) *
            D.q2 (.ofAdd 1) := by
          rw [Q_inv_triple]
    _ = D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (-(mcoef D))) *
          D.q2 (.ofAdd (-1)) * D.q3 (.ofAdd (-(gcoef D))) *
            D.q2 (.ofAdd 1)) := by group
    _ = D.q4 (.ofAdd 1) * (D.q1 (.ofAdd (-(mcoef D))) *
          D.q3 (.ofAdd (-(gcoef D)))) := by rw [q2_inv_q4_mul_q2_combine D]
    _ = D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
          D.q1 (.ofAdd (-(mcoef D))) := by
          rw [(Q_commute D (q1_mem_Q D (-(mcoef D)))
            (q3_mem_Q D (-(gcoef D)))).eq]
          group

private theorem q2_conj_q4_pow (c : ZMod 5) :
    (D.q2 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd c) * D.q2 (.ofAdd 1) =
      (D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
        D.q1 (.ofAdd (-(mcoef D)))) ^ c.val := by
  have hq4val : D.q4 (.ofAdd c) = (D.q4 (.ofAdd 1)) ^ c.val := by
    rw [← map_pow, ← ofAdd_nsmul,
      show c.val • (1 : ZMod 5) = c from by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]]
  rw [hq4val, conj_pow, q2_one_conj_q4]

private theorem q2_conj_standard_eq (a b c : ZMod 5) :
    (D.q2 (.ofAdd 1))⁻¹ *
        (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) * D.q2 (.ofAdd 1) =
      D.q1 (.ofAdd a) * D.q3 (.ofAdd b) *
        (D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
          D.q1 (.ofAdd (-(mcoef D)))) ^ c.val := by
  have hq1 : (D.q2 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd a) * D.q2 (.ofAdd 1) =
      D.q1 (.ofAdd a) :=
    (Q_commute D (q2_mem_Q D 1) (q1_mem_Q D a)).inv_mul_cancel
  have hq3 : (D.q2 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) * D.q2 (.ofAdd 1) =
      D.q3 (.ofAdd b) :=
    (Q_commute D (q2_mem_Q D 1) (q3_mem_Q D b)).inv_mul_cancel
  rw [show (D.q2 (.ofAdd 1))⁻¹ *
        (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) * D.q4 (.ofAdd c)) *
          D.q2 (.ofAdd 1) =
      ((D.q2 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd a) * D.q2 (.ofAdd 1)) *
        ((D.q2 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) * D.q2 (.ofAdd 1)) *
          ((D.q2 (.ofAdd 1))⁻¹ * D.q4 (.ofAdd c) * D.q2 (.ofAdd 1)) from by
      group]
  rw [hq1, hq3, q2_conj_q4_pow D]

private theorem vp_q4_q3_q1_pow (c : ZMod 5) :
    D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) * D.q1 (.ofAdd (-(mcoef D))) ∈ D.V ∧
      vp D ((D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
        D.q1 (.ofAdd (-(mcoef D)))) ^ c.val) = (-(c * gcoef D), c) := by
  have hB : D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
      D.q1 (.ofAdd (-(mcoef D))) ∈ D.V :=
    D.V.mul_mem (D.V.mul_mem
      (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
      (P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)))
      (P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  have hvpB : vp D (D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
      D.q1 (.ofAdd (-(mcoef D)))) = (-(gcoef D), 1) := by
    rw [vp_mul D (D.V.mul_mem
        (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
        (P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)))
        (P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)),
      vp_mul D (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
        (P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)),
      vp_q4 D 1, vp_q3 D (-(gcoef D)), vp_q1 D (-(mcoef D))]
    simp
  constructor
  · exact hB
  · rw [vp_pow D hB c.val, hvpB]
    change (c.val • (-(gcoef D)), c.val • (1 : ZMod 5)) = (-(c * gcoef D), c)
    rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    ext <;> ring

private theorem vp_q1_q3_mul_q4_q3_q1_pow (a b c : ZMod 5) :
    vp D (D.q1 (.ofAdd a) * D.q3 (.ofAdd b) *
      (D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
        D.q1 (.ofAdd (-(mcoef D)))) ^ c.val) = (b - gcoef D * c, c) := by
  obtain ⟨hB, hvpBpow⟩ := vp_q4_q3_q1_pow D c
  have hq1V : D.q1 (.ofAdd a) ∈ D.V :=
    P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq3V : D.q3 (.ofAdd b) ∈ D.V :=
    P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  rw [vp_mul D (D.V.mul_mem hq1V hq3V) (D.V.pow_mem hB c.val),
    vp_mul D hq1V hq3V, vp_q1 D a, vp_q3 D b, hvpBpow]
  simp
  ring

private theorem q2_one_conj_mem_vp {x : G} (hx : x ∈ D.V) :
    (D.q2 (.ofAdd 1))⁻¹ * x * D.q2 (.ofAdd 1) ∈ D.V ∧
      vp D ((D.q2 (.ofAdd 1))⁻¹ * x * D.q2 (.ofAdd 1)) =
        ((vp D x).1 - gcoef D * (vp D x).2, (vp D x).2) := by
  obtain ⟨a, b, c, hx'⟩ : ∃ a b c, vFull D x = (a, b, c) := ⟨_, _, _, rfl⟩
  have hxspec := vFull_spec D hx
  rw [hx'] at hxspec
  have hvx : vp D x = (b, c) := by simp [vp, hx']
  have hconj : (D.q2 (.ofAdd 1))⁻¹ * x * D.q2 (.ofAdd 1) =
      D.q1 (.ofAdd a) * D.q3 (.ofAdd b) *
        (D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
          D.q1 (.ofAdd (-(mcoef D)))) ^ c.val := by
    rw [hxspec]
    exact q2_conj_standard_eq D a b c
  have hq1V : D.q1 (.ofAdd a) ∈ D.V :=
    P1_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hq3V : D.q3 (.ofAdd b) ∈ D.V :=
    P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hB : D.q4 (.ofAdd 1) * D.q3 (.ofAdd (-(gcoef D))) *
      D.q1 (.ofAdd (-(mcoef D))) ∈ D.V := (vp_q4_q3_q1_pow D c).1
  refine ⟨?_, ?_⟩
  · rw [hconj]
    exact D.V.mul_mem (D.V.mul_mem hq1V hq3V) (D.V.pow_mem hB c.val)
  · rw [hconj, vp_q1_q3_mul_q4_q3_q1_pow D a b c, hvx]

private theorem q2_pow_conj_mem_vp (n : ℕ) {x : G} (hx : x ∈ D.V) :
    ((D.q2 (.ofAdd 1)) ^ n)⁻¹ * x * ((D.q2 (.ofAdd 1)) ^ n) ∈ D.V ∧
      vp D (((D.q2 (.ofAdd 1)) ^ n)⁻¹ * x * ((D.q2 (.ofAdd 1)) ^ n)) =
        ((vp D x).1 - (n : ZMod 5) * gcoef D * (vp D x).2, (vp D x).2) := by
  induction n with
  | zero =>
      simp only [pow_zero, inv_one, one_mul, mul_one]
      exact ⟨hx, by simp⟩
  | succ n ih =>
      obtain ⟨hV, hv⟩ := ih
      have hstep := q2_one_conj_mem_vp D hV
      have heq : ((D.q2 (.ofAdd 1)) ^ (n + 1))⁻¹ * x *
          ((D.q2 (.ofAdd 1)) ^ (n + 1)) =
          (D.q2 (.ofAdd 1))⁻¹ * (((D.q2 (.ofAdd 1)) ^ n)⁻¹ * x *
            ((D.q2 (.ofAdd 1)) ^ n)) * D.q2 (.ofAdd 1) := by
        rw [pow_succ]
        group
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hstep.1
      · rw [heq, hstep.2, hv]
        rw [Nat.cast_succ]
        ring_nf

private theorem q2_conj_mem_vp (b : ZMod 5) {x : G} (hx : x ∈ D.V) :
    (D.q2 (.ofAdd b))⁻¹ * x * D.q2 (.ofAdd b) ∈ D.V ∧
      vp D ((D.q2 (.ofAdd b))⁻¹ * x * D.q2 (.ofAdd b)) =
        ((vp D x).1 - b * gcoef D * (vp D x).2, (vp D x).2) := by
  have hb : D.q2 (.ofAdd b) = (D.q2 (.ofAdd 1)) ^ b.val := by
    rw [← map_pow, ← ofAdd_nsmul,
      show b.val • (1 : ZMod 5) = b from by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]]
  rw [hb]
  simpa [ZMod.natCast_zmod_val] using q2_pow_conj_mem_vp D b.val hx

omit [Finite G] in
private theorem c2_mul_q2_one_cube : (D.c2 * D.q2 (.ofAdd 1)) ^ 3 = 1 := by
  have hmat : (cM * thetaM 1) ^ 3 = 1 := by decide
  rw [show D.c2 = D.i2 cM from rfl,
    show D.q2 (.ofAdd 1) = D.i2 (thetaM 1) from rfl, ← map_mul, ← map_pow,
    hmat, map_one]

private theorem vp_h2_conj_q3 :
    vp D (D.h2⁻¹ * D.q3 (.ofAdd 1) * D.h2) =
      (2 * gcoef D, 1 + 4 * gcoef D * gcoef D) := by
  have hMword : hM = thetaM 2 * cM * thetaM (-2) * cM * thetaM 2 * cM⁻¹ := by
    decide
  have hh2 : D.h2 = D.q2 (.ofAdd 2) * D.c2 * D.q2 (.ofAdd (-2)) * D.c2 *
      D.q2 (.ofAdd 2) * D.c2⁻¹ := by
    rw [show D.h2 = D.i2 hM from rfl, hMword]
    simp only [map_mul, map_inv]
    rfl
  have hx0 : D.q3 (.ofAdd 1) ∈ D.V :=
    P3_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h1 := q2_conj_mem_vp D 2 hx0
  set y1 := (D.q2 (.ofAdd 2))⁻¹ * D.q3 (.ofAdd 1) * D.q2 (.ofAdd 2) with hy1
  have hy1V : y1 ∈ D.V := by rw [hy1]; exact h1.1
  have hv1 : vp D y1 = (1, 0) := by
    rw [hy1, h1.2, vp_q3 D 1]
    simp
  have h2 := c2_conj_mem_vp D hy1V
  set y2 := D.c2⁻¹ * y1 * D.c2 with hy2
  have hy2V : y2 ∈ D.V := by rw [hy2]; exact h2.1
  have hv2 : vp D y2 = (0, 1) := by
    rw [hy2, h2.2, hv1]
    simp
  have h3 := q2_conj_mem_vp D (-2) hy2V
  set y3 := (D.q2 (.ofAdd (-2)))⁻¹ * y2 * D.q2 (.ofAdd (-2)) with hy3
  have hy3V : y3 ∈ D.V := by rw [hy3]; exact h3.1
  have hv3 : vp D y3 = (2 * gcoef D, 1) := by
    rw [hy3, h3.2, hv2]
    ext <;> ring
  have h4 := c2_conj_mem_vp D hy3V
  set y4 := D.c2⁻¹ * y3 * D.c2 with hy4
  have hy4V : y4 ∈ D.V := by rw [hy4]; exact h4.1
  have hv4 : vp D y4 = (-1, 2 * gcoef D) := by
    rw [hy4, h4.2, hv3]
  have h5 := q2_conj_mem_vp D 2 hy4V
  set y5 := (D.q2 (.ofAdd 2))⁻¹ * y4 * D.q2 (.ofAdd 2) with hy5
  have hy5V : y5 ∈ D.V := by rw [hy5]; exact h5.1
  have hv5 : vp D y5 = (-1 - 4 * gcoef D * gcoef D, 2 * gcoef D) := by
    rw [hy5, h5.2, hv4]
    ext <;> ring
  have h6 := c2_mul_mem_vp D hy5V
  set y6 := D.c2 * y5 * D.c2⁻¹ with hy6
  have hy6V : y6 ∈ D.V := by rw [hy6]; exact h6.1
  have hv6 : vp D y6 = (2 * gcoef D, 1 + 4 * gcoef D * gcoef D) := by
    rw [hy6, h6.2, hv5]
    ext <;> ring
  have hy6eq : y6 = D.h2⁻¹ * D.q3 (.ofAdd 1) * D.h2 := by
    rw [hy6, hy5, hy4, hy3, hy2, hy1, hh2]
    group
  rw [← hy6eq]
  exact hv6

private theorem gcoef_eq_one : gcoef D = 1 := by
  have hcube : (D.c2 * D.q2 (.ofAdd 1)) ^ 3 = 1 := c2_mul_q2_one_cube D
  have hx0 : D.q4 (.ofAdd 1) ∈ D.V :=
    P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h1 := c2_conj_mem_vp D hx0
  set x1 := D.c2⁻¹ * D.q4 (.ofAdd 1) * D.c2 with hx1
  have hx1V : x1 ∈ D.V := by rw [hx1]; exact h1.1
  have hv1 : vp D x1 = (-1, 0) := by
    rw [hx1, h1.2, vp_q4 D 1]
  have h2 := q2_conj_mem_vp D 1 hx1V
  set x2 := (D.q2 (.ofAdd 1))⁻¹ * x1 * D.q2 (.ofAdd 1) with hx2
  have hx2V : x2 ∈ D.V := by rw [hx2]; exact h2.1
  have hv2 : vp D x2 = (-1, 0) := by
    rw [hx2, h2.2, hv1]
    ext <;> simp
  have h3 := c2_conj_mem_vp D hx2V
  set x3 := D.c2⁻¹ * x2 * D.c2 with hx3
  have hx3V : x3 ∈ D.V := by rw [hx3]; exact h3.1
  have hv3 : vp D x3 = (0, -1) := by
    rw [hx3, h3.2, hv2]
    ext <;> simp
  have h4 := q2_conj_mem_vp D 1 hx3V
  set x4 := (D.q2 (.ofAdd 1))⁻¹ * x3 * D.q2 (.ofAdd 1) with hx4
  have hx4V : x4 ∈ D.V := by rw [hx4]; exact h4.1
  have hv4 : vp D x4 = (gcoef D, -1) := by
    rw [hx4, h4.2, hv3]
    ext <;> ring
  have h5 := c2_conj_mem_vp D hx4V
  set x5 := D.c2⁻¹ * x4 * D.c2 with hx5
  have hx5V : x5 ∈ D.V := by rw [hx5]; exact h5.1
  have hv5 : vp D x5 = (1, gcoef D) := by
    rw [hx5, h5.2, hv4]
    ext <;> simp
  have h6 := q2_conj_mem_vp D 1 hx5V
  set x6 := (D.q2 (.ofAdd 1))⁻¹ * x5 * D.q2 (.ofAdd 1) with hx6
  have hx6V : x6 ∈ D.V := by rw [hx6]; exact h6.1
  have hv6 : vp D x6 = (1 - gcoef D * gcoef D, gcoef D) := by
    rw [hx6, h6.2, hv5]
    ext <;> ring
  have hx6eq : x6 = ((D.c2 * D.q2 (.ofAdd 1)) ^ 3)⁻¹ * D.q4 (.ofAdd 1) *
      ((D.c2 * D.q2 (.ofAdd 1)) ^ 3) := by
    rw [hx6, hx5, hx4, hx3, hx2, hx1, pow_three]
    group
  rw [hx6eq, hcube, inv_one, one_mul, mul_one] at hv6
  rw [vp_q4 D 1] at hv6
  exact (congrArg Prod.snd hv6).symm

private theorem h2_conj_q3 (a : ZMod 5) :
    D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (2 * a)) := by
  obtain ⟨ρ, -, hρ⟩ := (D.elementary_abelian_three_space).2.2.2.2.2
  have hv := vp_h2_conj_q3 D
  rw [gcoef_eq_one D] at hv
  have hv' : vp D (D.h2⁻¹ * D.q3 (.ofAdd 1) * D.h2) = (2, 0) := by
    rw [hv]
    decide
  have hfix : D.h2⁻¹ * D.q3 (.ofAdd 1) * D.h2 = D.q3 (.ofAdd ρ) := by
    simpa using (hρ 1).2
  have hρeq : ρ = 2 := by
    have h1 : vp D (D.q3 (.ofAdd ρ)) = (2, 0) := by
      rw [← hfix]
      exact hv'
    rw [vp_q3 D ρ] at h1
    exact (Prod.ext_iff.mp h1).1
  rw [hρeq] at hρ
  exact (hρ a).2

end PairAction

section Assembly

variable [Finite G]

omit [Finite G] in
private theorem q2_pow_val (a : ZMod 5) :
    D.q2 (.ofAdd a) = (D.q2 (.ofAdd 1)) ^ a.val := by
  rw [← map_pow, ← ofAdd_nsmul,
    show a.val • (1 : ZMod 5) = a from by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]]

private theorem q4_conj_q1 (c a : ZMod 5) :
    (D.q4 (.ofAdd c))⁻¹ * D.q1 (.ofAdd a) * D.q4 (.ofAdd c) = D.q1 (.ofAdd a) := by
  have h : Commute (D.q1 (.ofAdd a)) (D.q4 (.ofAdd c)) :=
    P1_commute_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  exact h.symm.inv_mul_cancel

private theorem Q_mul_q1_triple (A B C x : ZMod 5) :
    D.q1 (.ofAdd A) * (D.q1 (.ofAdd x) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) =
      D.q1 (.ofAdd (A + x)) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C) := by
  rw [show D.q1 (.ofAdd A) * (D.q1 (.ofAdd x) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) =
      (D.q1 (.ofAdd A) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd 0)) *
        (D.q1 (.ofAdd x) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) from by simp]
  rw [Q_mul_triple]
  simp

private theorem Q_mul_triple_q1q3 (A B C x z : ZMod 5) :
    (D.q1 (.ofAdd A) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) *
        (D.q1 (.ofAdd x) * D.q3 (.ofAdd z)) =
      D.q1 (.ofAdd (A + x)) * D.q2 (.ofAdd B) * D.q3 (.ofAdd (C + z)) := by
  rw [show (D.q1 (.ofAdd A) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) *
        (D.q1 (.ofAdd x) * D.q3 (.ofAdd z)) =
      (D.q1 (.ofAdd A) * D.q2 (.ofAdd B) * D.q3 (.ofAdd C)) *
        (D.q1 (.ofAdd x) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd z)) from by simp]
  rw [Q_mul_triple]
  simp

private theorem Q_mul_q1_q1q3 (A x z : ZMod 5) :
    D.q1 (.ofAdd A) * (D.q1 (.ofAdd x) * D.q3 (.ofAdd z)) =
      D.q1 (.ofAdd (A + x)) * D.q3 (.ofAdd z) := by
  rw [show D.q1 (.ofAdd A) * (D.q1 (.ofAdd x) * D.q3 (.ofAdd z)) =
      (D.q1 (.ofAdd A) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd 0)) *
        (D.q1 (.ofAdd x) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd z)) from by simp]
  rw [Q_mul_triple]
  simp

private theorem q4_conj_q2_one (hg : gcoef D = 1) (b : ZMod 5) :
    (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd (-b)) * D.q2 (.ofAdd b) * D.q3 (.ofAdd b) := by
  have hm : mcoef D = -1 := (step2_coeffs D).1
  have hb : b.val • (1 : ZMod 5) = b := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
  have hbm : b.val • (-1 : ZMod 5) = -b := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  calc (D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd 1)
      = (D.q4 (.ofAdd 1))⁻¹ * (D.q2 (.ofAdd 1)) ^ b.val * D.q4 (.ofAdd 1) := by
        rw [q2_pow_val]
    _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1)) ^ b.val :=
        conj_pow (D.q4 (.ofAdd 1)) (D.q2 (.ofAdd 1)) b.val
    _ = (D.q1 (.ofAdd (mcoef D)) * D.q2 (.ofAdd 1) * D.q3 (.ofAdd (gcoef D))) ^ b.val := by
        rw [q4_conj_q2]
    _ = D.q1 (.ofAdd (b.val • mcoef D)) * D.q2 (.ofAdd (b.val • (1 : ZMod 5))) *
          D.q3 (.ofAdd (b.val • gcoef D)) := Q_pow D (mcoef D) 1 (gcoef D) b.val
    _ = D.q1 (.ofAdd (-b)) * D.q2 (.ofAdd b) * D.q3 (.ofAdd b) := by
        rw [hm, hg, hb, hbm]

private theorem q4_conj_q3_one (hg : gcoef D = 1) (b : ZMod 5) :
    (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd 1) =
      D.q1 (.ofAdd (-2 * b)) * D.q3 (.ofAdd b) := by
  have hl : lcoef D = -2 := by
    have h := (step2_coeffs D).2
    rw [hg, mul_one] at h
    rw [h]
    decide
  have hb : b.val • (1 : ZMod 5) = b := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
  have hbm : b.val • (-2 : ZMod 5) = -2 * b := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  calc (D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd 1)
      = (D.q4 (.ofAdd 1))⁻¹ * (D.q3 (.ofAdd 1)) ^ b.val * D.q4 (.ofAdd 1) := by
        rw [q3_pow_val]
    _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1)) ^ b.val :=
        conj_pow (D.q4 (.ofAdd 1)) (D.q3 (.ofAdd 1)) b.val
    _ = (D.q1 (.ofAdd (lcoef D)) * D.q3 (.ofAdd 1)) ^ b.val := by rw [q4_conj_q3]
    _ = (D.q1 (.ofAdd (lcoef D)) * D.q2 (.ofAdd 0) * D.q3 (.ofAdd 1)) ^ b.val := by simp
    _ = D.q1 (.ofAdd (b.val • lcoef D)) * D.q2 (.ofAdd (b.val • 0)) *
          D.q3 (.ofAdd (b.val • (1 : ZMod 5))) := Q_pow D (lcoef D) 0 1 b.val
    _ = D.q1 (.ofAdd (-2 * b)) * D.q3 (.ofAdd b) := by
        rw [hl, hbm, hb]
        simp

private theorem q4_conj_q2_succ (hg : gcoef D = 1) (b : ZMod 5) (n : ℕ)
    (ih : (D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q2 (.ofAdd b) *
        D.q4 (.ofAdd (n : ZMod 5)) =
      D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b)) * D.q2 (.ofAdd b) *
        D.q3 (.ofAdd ((n : ZMod 5) * b))) :
    (D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)))⁻¹ * D.q2 (.ofAdd b) *
        D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)) =
      D.q1 (.ofAdd (-((n + 1 : ℕ) : ZMod 5) ^ 2 * b)) * D.q2 (.ofAdd b) *
        D.q3 (.ofAdd (((n + 1 : ℕ) : ZMod 5) * b)) := by
  have hcast : ((n + 1 : ℕ) : ZMod 5) = (n : ZMod 5) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hq4 : D.q4 (.ofAdd ((n : ZMod 5) + 1)) =
      D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1) := by
    rw [ofAdd_add, map_mul]
  calc (D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)))⁻¹ * D.q2 (.ofAdd b) *
          D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5))
        = (D.q4 (.ofAdd ((n : ZMod 5) + 1)))⁻¹ * D.q2 (.ofAdd b) *
            D.q4 (.ofAdd ((n : ZMod 5) + 1)) := by rw [hcast]
      _ = (D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd b) *
            (D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1)) := by rw [hq4]
      _ = (D.q4 (.ofAdd 1))⁻¹ * ((D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q2 (.ofAdd b) *
            D.q4 (.ofAdd (n : ZMod 5))) * D.q4 (.ofAdd 1) := by group
      _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b)) *
            D.q2 (.ofAdd b) * D.q3 (.ofAdd ((n : ZMod 5) * b))) *
            D.q4 (.ofAdd 1) := by rw [ih]
      _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b)) *
            D.q4 (.ofAdd 1)) *
          ((D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd 1)) *
          ((D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd ((n : ZMod 5) * b)) *
            D.q4 (.ofAdd 1)) := by group
      _ = D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b)) *
          (D.q1 (.ofAdd (-b)) * D.q2 (.ofAdd b) * D.q3 (.ofAdd b)) *
          (D.q1 (.ofAdd (-2 * ((n : ZMod 5) * b))) *
            D.q3 (.ofAdd ((n : ZMod 5) * b))) := by
            rw [q4_conj_q1, q4_conj_q2_one D hg, q4_conj_q3_one D hg]
      _ = D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b + -b + -2 * ((n : ZMod 5) * b))) *
          D.q2 (.ofAdd b) * D.q3 (.ofAdd (b + (n : ZMod 5) * b)) := by
            rw [Q_mul_q1_triple, Q_mul_triple_q1q3]
      _ = D.q1 (.ofAdd (-(((n : ZMod 5) + 1) ^ 2) * b)) * D.q2 (.ofAdd b) *
          D.q3 (.ofAdd (((n : ZMod 5) + 1) * b)) := by
            have hA : -(n : ZMod 5) ^ 2 * b + -b + -2 * ((n : ZMod 5) * b) =
                -(((n : ZMod 5) + 1) ^ 2) * b := by ring
            have hB : b + (n : ZMod 5) * b = ((n : ZMod 5) + 1) * b := by ring
            rw [hA, hB]
      _ = D.q1 (.ofAdd (-((n + 1 : ℕ) : ZMod 5) ^ 2 * b)) * D.q2 (.ofAdd b) *
          D.q3 (.ofAdd (((n + 1 : ℕ) : ZMod 5) * b)) := by rw [hcast]

private theorem q4_conj_q3_succ (hg : gcoef D = 1) (b : ZMod 5) (n : ℕ)
    (ih : (D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q3 (.ofAdd b) *
        D.q4 (.ofAdd (n : ZMod 5)) =
      D.q1 (.ofAdd (-2 * (n : ZMod 5) * b)) * D.q3 (.ofAdd b)) :
    (D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)))⁻¹ * D.q3 (.ofAdd b) *
        D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)) =
      D.q1 (.ofAdd (-2 * ((n + 1 : ℕ) : ZMod 5) * b)) * D.q3 (.ofAdd b) := by
  have hcast : ((n + 1 : ℕ) : ZMod 5) = (n : ZMod 5) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hq4 : D.q4 (.ofAdd ((n : ZMod 5) + 1)) =
      D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1) := by
    rw [ofAdd_add, map_mul]
  calc (D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5)))⁻¹ * D.q3 (.ofAdd b) *
          D.q4 (.ofAdd ((n + 1 : ℕ) : ZMod 5))
        = (D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) *
            (D.q4 (.ofAdd (n : ZMod 5)) * D.q4 (.ofAdd 1)) := by rw [hcast, hq4]
      _ = (D.q4 (.ofAdd 1))⁻¹ * ((D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q3 (.ofAdd b) *
            D.q4 (.ofAdd (n : ZMod 5))) * D.q4 (.ofAdd 1) := by group
      _ = (D.q4 (.ofAdd 1))⁻¹ * (D.q1 (.ofAdd (-2 * (n : ZMod 5) * b)) *
            D.q3 (.ofAdd b)) * D.q4 (.ofAdd 1) := by rw [ih]
      _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd (-2 * (n : ZMod 5) * b)) *
            D.q4 (.ofAdd 1)) *
          ((D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd 1)) := by group
      _ = D.q1 (.ofAdd (-2 * (n : ZMod 5) * b)) *
          (D.q1 (.ofAdd (-2 * b)) * D.q3 (.ofAdd b)) := by
            rw [q4_conj_q1, q4_conj_q3_one D hg]
      _ = D.q1 (.ofAdd (-2 * (n : ZMod 5) * b + -2 * b)) * D.q3 (.ofAdd b) := by
            rw [Q_mul_q1_q1q3]
      _ = D.q1 (.ofAdd (-2 * ((n : ZMod 5) + 1) * b)) * D.q3 (.ofAdd b) := by
            have hA : -2 * (n : ZMod 5) * b + -2 * b =
                -2 * ((n : ZMod 5) + 1) * b := by ring
            rw [hA]
      _ = D.q1 (.ofAdd (-2 * ((n + 1 : ℕ) : ZMod 5) * b)) * D.q3 (.ofAdd b) := by
          rw [hcast]

private theorem q4_conj_q2_q3_nat (hg : gcoef D = 1) (b : ZMod 5) (n : ℕ) :
    (D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd (n : ZMod 5)) =
      D.q1 (.ofAdd (-(n : ZMod 5) ^ 2 * b)) * D.q2 (.ofAdd b) *
        D.q3 (.ofAdd ((n : ZMod 5) * b)) ∧
    (D.q4 (.ofAdd (n : ZMod 5)))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd (n : ZMod 5)) =
      D.q1 (.ofAdd (-2 * (n : ZMod 5) * b)) * D.q3 (.ofAdd b) := by
  induction n with
  | zero =>
      have h0 : ((0 : ℕ) : ZMod 5) = 0 := by norm_num
      have hm1 : ((0 : ZMod 5) * b) = 0 := by ring
      constructor <;> simp [h0, hm1]
  | succ n ih =>
      obtain ⟨ih2, ih3⟩ := ih
      exact ⟨q4_conj_q2_succ D hg b n ih2, q4_conj_q3_succ D hg b n ih3⟩

private theorem q4_conj_q2_general (hg : gcoef D = 1) (a b : ZMod 5) :
    (D.q4 (.ofAdd a))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd a) =
      D.q1 (.ofAdd (-a ^ 2 * b)) * D.q2 (.ofAdd b) * D.q3 (.ofAdd (a * b)) := by
  have h := (q4_conj_q2_q3_nat D hg b a.val).1
  simpa only [ZMod.natCast_zmod_val] using h

private theorem q4_conj_q3_general (hg : gcoef D = 1) (a b : ZMod 5) :
    (D.q4 (.ofAdd a))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd a) =
      D.q1 (.ofAdd (-2 * a * b)) * D.q3 (.ofAdd b) := by
  have h := (q4_conj_q2_q3_nat D hg b a.val).2
  simpa only [ZMod.natCast_zmod_val] using h

private theorem commute_q1_q3 (a b : ZMod 5) :
    Commute (D.q1 (.ofAdd a)) (D.q3 (.ofAdd b)) :=
  Q_commute D (q1_mem_Q D a) (q3_mem_Q D b)

private theorem commute_q2_q3 (a b : ZMod 5) :
    Commute (D.q2 (.ofAdd a)) (D.q3 (.ofAdd b)) :=
  Q_commute D (q2_mem_Q D a) (q3_mem_Q D b)

private theorem commute_q1_q4 (a b : ZMod 5) :
    Commute (D.q1 (.ofAdd a)) (D.q4 (.ofAdd b)) :=
  P1_commute_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (P4_le_V D (MonoidHom.mem_range.mpr ⟨_, rfl⟩))

private theorem h1_conj_q3_of_step3
    (hρ : ∀ a : ZMod 5, D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (2 * a)))
    (a : ZMod 5) : D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (2 * a)) := by
  obtain ⟨ρ, -, hρ'⟩ := (D.elementary_abelian_three_space).2.2.2.2.2
  have h1 : D.q3 (.ofAdd (ρ * 1)) = D.q3 (.ofAdd (2 * 1)) := by
    rw [← (hρ' 1).2, ← hρ 1]
  have h2 : ρ = 2 := by
    have h3 := D.q3_injective h1
    simpa using h3
  rw [(hρ' a).1, h2]

private theorem h1_conj_q4_of_step3
    (hρ : ∀ a : ZMod 5, D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (2 * a)))
    (a : ZMod 5) : D.h1⁻¹ * D.q4 (.ofAdd a) * D.h1 = D.q4 (.ofAdd (2 * a)) := by
  have hc : Commute D.h1 D.c2 := D.commute hM cM
  have hcA : D.h1⁻¹ * D.c2⁻¹ = D.c2⁻¹ * D.h1⁻¹ := hc.inv_left.inv_right.eq
  have hcB : D.c2 * D.h1 = D.h1 * D.c2 := hc.symm.eq
  calc D.h1⁻¹ * D.q4 (.ofAdd a) * D.h1
      = D.h1⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.h1 := by rw [q4_ofAdd]
    _ = D.c2⁻¹ * (D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1) * D.c2 := by
        calc D.h1⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.h1
            = D.h1⁻¹ * D.c2⁻¹ * D.q3 (.ofAdd a) * (D.c2 * D.h1) := by group
          _ = D.c2⁻¹ * D.h1⁻¹ * D.q3 (.ofAdd a) * (D.h1 * D.c2) := by rw [hcA, hcB]
          _ = D.c2⁻¹ * (D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1) * D.c2 := by group
    _ = D.c2⁻¹ * D.q3 (.ofAdd (2 * a)) * D.c2 := by
        rw [h1_conj_q3_of_step3 D hρ]
    _ = D.q4 (.ofAdd (2 * a)) := by rw [q4_ofAdd]

omit [Finite G] in
private theorem h2_conj_q4_of_step3
    (hρ : ∀ a : ZMod 5, D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (2 * a)))
    (a : ZMod 5) : D.h2⁻¹ * D.q4 (.ofAdd a) * D.h2 = D.q4 (.ofAdd (3 * a)) := by
  have hc : D.c2⁻¹ * D.h2 * D.c2 = D.h2⁻¹ := by
    rw [show D.c2 = D.i2 cM from rfl, show D.h2 = D.i2 hM from rfl]
    simp only [← map_inv, ← map_mul, cM_inv_mul_hM_mul_cM]
  have hcA : D.c2⁻¹ * D.h2 = D.h2⁻¹ * D.c2⁻¹ := by
    rw [← hc]
    group
  have hB : D.h2 = D.c2 * D.h2⁻¹ * D.c2⁻¹ := by
    rw [← hc]
    group
  have hcB : D.c2 * D.h2 = D.h2⁻¹ * D.c2 := by
    have hB' : D.h2⁻¹ = D.c2 * D.h2 * D.c2⁻¹ := by
      have := congrArg (fun x : G => x⁻¹) hB
      simpa [mul_inv_rev, mul_assoc] using this
    rw [hB']
    group
  have hq3 : D.h2 * D.q3 (.ofAdd a) * D.h2⁻¹ = D.q3 (.ofAdd (3 * a)) := by
    have h23 : (2 : ZMod 5) * 3 = 1 := by decide
    have h := hρ (3 * a)
    rw [show (2 : ZMod 5) * (3 * a) = a from by rw [← mul_assoc, h23, one_mul]] at h
    rw [← h]
    group
  calc D.h2⁻¹ * D.q4 (.ofAdd a) * D.h2
      = D.h2⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.h2 := by rw [q4_ofAdd]
    _ = D.c2⁻¹ * (D.h2 * D.q3 (.ofAdd a) * D.h2⁻¹) * D.c2 := by
        calc D.h2⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.h2
            = D.h2⁻¹ * D.c2⁻¹ * D.q3 (.ofAdd a) * (D.c2 * D.h2) := by group
          _ = D.c2⁻¹ * D.h2 * D.q3 (.ofAdd a) * (D.h2⁻¹ * D.c2) := by rw [← hcA, hcB]
          _ = D.c2⁻¹ * (D.h2 * D.q3 (.ofAdd a) * D.h2⁻¹) * D.c2 := by group
    _ = D.c2⁻¹ * D.q3 (.ofAdd (3 * a)) * D.c2 := by rw [hq3]
    _ = D.q4 (.ofAdd (3 * a)) := by rw [q4_ofAdd]
end Assembly

theorem exact_root_torus_and_weyl_actions [Finite G] (a b : ZMod 5) :
    Commute (D.q1 (.ofAdd a)) (D.q2 (.ofAdd b)) ∧ Commute (D.q1 (.ofAdd a)) (D.q3 (.ofAdd b)) ∧
    Commute (D.q1 (.ofAdd a)) (D.q4 (.ofAdd b)) ∧ Commute (D.q2 (.ofAdd a)) (D.q3 (.ofAdd b)) ∧
    (D.q4 (.ofAdd a))⁻¹ * D.q2 (.ofAdd b) * D.q4 (.ofAdd a) =
      D.q1 (.ofAdd (-a ^ 2 * b)) * D.q2 (.ofAdd b) * D.q3 (.ofAdd (a * b)) ∧
    (D.q4 (.ofAdd a))⁻¹ * D.q3 (.ofAdd b) * D.q4 (.ofAdd a) =
      D.q1 (.ofAdd (-2 * a * b)) * D.q3 (.ofAdd b) ∧
    D.h1⁻¹ * D.q1 (.ofAdd a) * D.h1 = D.q1 (.ofAdd (4 * a)) ∧
    D.h1⁻¹ * D.q2 (.ofAdd a) * D.h1 = D.q2 (.ofAdd a) ∧
    D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (2 * a)) ∧
    D.h1⁻¹ * D.q4 (.ofAdd a) * D.h1 = D.q4 (.ofAdd (2 * a)) ∧
    D.h2⁻¹ * D.q1 (.ofAdd a) * D.h2 = D.q1 (.ofAdd a) ∧
    D.h2⁻¹ * D.q2 (.ofAdd a) * D.h2 = D.q2 (.ofAdd (4 * a)) ∧
    D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (2 * a)) ∧
    D.h2⁻¹ * D.q4 (.ofAdd a) * D.h2 = D.q4 (.ofAdd (3 * a)) ∧
    D.u⁻¹ * D.q1 (.ofAdd a) * D.u = D.q2 (.ofAdd a) ∧
    D.u⁻¹ * D.q2 (.ofAdd a) * D.u = D.q1 (.ofAdd a) ∧
    D.u⁻¹ * D.q3 (.ofAdd a) * D.u = D.q3 (.ofAdd (-a)) ∧
    D.c2⁻¹ * D.q1 (.ofAdd a) * D.c2 = D.q1 (.ofAdd a) ∧
    D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2 = D.q4 (.ofAdd a) ∧
    D.c2⁻¹ * D.q4 (.ofAdd a) * D.c2 = D.q3 (.ofAdd (-a)) := by
  have hg := gcoef_eq_one D
  have hρ := h2_conj_q3 D
  exact ⟨D.commute_q1_q2 (.ofAdd a) (.ofAdd b), commute_q1_q3 D a b, commute_q1_q4 D a b,
      commute_q2_q3 D a b, q4_conj_q2_general D hg a b, q4_conj_q3_general D hg a b,
      D.h1_conj_q1 a, D.h1_conj_q2 (.ofAdd a), h1_conj_q3_of_step3 D hρ a,
      h1_conj_q4_of_step3 D hρ a, D.h2_conj_q1 (.ofAdd a), D.h2_conj_q2 a, hρ a,
      h2_conj_q4_of_step3 D hρ a, D.u_conj_q1 (.ofAdd a), D.u_conj_q2 (.ofAdd a),
      D.u_conj_q3 a, D.c2_conj_q1 (.ofAdd a), (q4_ofAdd D a).symm, c2_conj_q4 D a⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
