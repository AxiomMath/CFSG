module

public import CFSG.Quasithin.Vol2.Asc94.He42P427B

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem p427_inv_of_fpf (O : Subgroup G) {b : G} (hb2 : b * b = 1)
    (hbO : ∀ o ∈ O, b * o * b⁻¹ ∈ O) (hfp : ∀ o ∈ O, b * o * b⁻¹ = o → o = 1) :
    ∀ o ∈ O, b * o * b⁻¹ = o⁻¹ := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbb : b⁻¹ * b⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hb2, inv_one]
  let F : ↥O → ↥O := fun o => ⟨(o : G)⁻¹ * (b * (o : G) * b⁻¹), O.mul_mem (O.inv_mem o.2) (hbO o o.2)⟩
  have hFinj : Function.Injective F := by
    intro o o' h
    have h1 : (o : G)⁻¹ * (b * (o : G) * b⁻¹) = (o' : G)⁻¹ * (b * (o' : G) * b⁻¹) :=
      congrArg Subtype.val h
    have hs' : b * (o' : G) * b⁻¹ = (o' : G) * (o : G)⁻¹ * (b * (o : G) * b⁻¹) := by
      calc b * (o' : G) * b⁻¹ = (o' : G) * ((o' : G)⁻¹ * (b * (o' : G) * b⁻¹)) := by group
        _ = (o' : G) * ((o : G)⁻¹ * (b * (o : G) * b⁻¹)) := by rw [h1]
        _ = (o' : G) * (o : G)⁻¹ * (b * (o : G) * b⁻¹) := by group
    have hx : b * ((o' : G) * (o : G)⁻¹) * b⁻¹ = (o' : G) * (o : G)⁻¹ := by
      calc b * ((o' : G) * (o : G)⁻¹) * b⁻¹ = (b * (o' : G) * b⁻¹) * (b * (o : G)⁻¹ * b⁻¹) := by
            group
        _ = ((o' : G) * (o : G)⁻¹ * (b * (o : G) * b⁻¹)) * (b * (o : G)⁻¹ * b⁻¹) := by rw [hs']
        _ = (o' : G) * (o : G)⁻¹ := by group
    have hxO : (o' : G) * (o : G)⁻¹ ∈ O := O.mul_mem o'.2 (O.inv_mem o.2)
    have h4 : (o' : G) * (o : G)⁻¹ = 1 := hfp _ hxO hx
    apply Subtype.ext
    exact (mul_inv_eq_one.1 h4).symm
  have hFsurj : Function.Surjective F := Finite.injective_iff_surjective.1 hFinj
  intro o ho
  obtain ⟨p, hp⟩ := hFsurj ⟨o, ho⟩
  have hpo : (p : G)⁻¹ * (b * (p : G) * b⁻¹) = o := congrArg Subtype.val hp
  rw [← hpo]
  calc b * ((p : G)⁻¹ * (b * (p : G) * b⁻¹)) * b⁻¹
      = b * (p : G)⁻¹ * b * (p : G) * (b⁻¹ * b⁻¹) := by group
    _ = b * (p : G)⁻¹ * b * (p : G) := by rw [hbb, mul_one]
    _ = b * (p : G)⁻¹ * b⁻¹ * (p : G) := by rw [hbinv]
    _ = ((p : G)⁻¹ * (b * (p : G) * b⁻¹))⁻¹ := by group

theorem p427_card_conj_eq (R R' : Subgroup G) (c : G) (h1 : ∀ x ∈ R, c * x * c⁻¹ ∈ R')
    (h2 : ∀ y ∈ R', c⁻¹ * y * c ∈ R) : Nat.card ↥R = Nat.card ↥R' := by
  let f : ↥R → ↥R' := fun x => ⟨c * (x : G) * c⁻¹, h1 x x.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    have h' : c * (x : G) * c⁻¹ = c * (y : G) * c⁻¹ := congrArg Subtype.val h
    apply Subtype.ext
    have h'' := congrArg (fun t => c⁻¹ * t * c) h'
    simpa using h''
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨c⁻¹ * (y : G) * c, h2 y y.2⟩, ?_⟩
    apply Subtype.ext
    show c * (c⁻¹ * (y : G) * c) * c⁻¹ = (y : G)
    group
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p427_fin_comm : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 → ∀ X : HeJ.M2, X.det ≠ 0 →
    (X + 1).det ≠ 0 → g.val * X = X * g.val := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p427_fin_e12 : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 →
    ((Matrix.of ![![0, 1], ![0, 0]] : HeJ.M2) + g.val).det = 0 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p427_fin_g1 : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 → (g.val + 1).det ≠ 0 := by
  decide +kernel

theorem p427_det_conj (T : HeSetup G) (hfus : T.StepFus) {y y' g : G} (hy : y ∈ T.Z)
    (hy' : y' ∈ T.Z) (h : g⁻¹ * y * g = y') (hdet : (T.m y).det ≠ 0) : (T.m y').det ≠ 0 := by
  obtain ⟨n, hnN, hn⟩ := hfus y hy y' hy' g h
  have hn' : n⁻¹ ∈ T.N := T.N.inv_mem hnN
  have hm := T.hD.hT.m_conj T.N T.hD.hK.norm ⟨n⁻¹, hn'⟩ hy
  rw [show ((⟨n⁻¹, hn'⟩ : T.N) : G) = n⁻¹ from rfl, inv_inv, hn] at hm
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hPd : ((T.hD.hT.rho T.N T.hD.hK.norm ⟨n⁻¹, hn'⟩).1 : HeJ.M2).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (T.hD.hT.rho T.N T.hD.hK.norm ⟨n⁻¹, hn'⟩).1.isUnit).ne_zero
  have hQd : ((T.hD.hT.rho T.N T.hD.hK.norm ⟨n⁻¹, hn'⟩).2 : HeJ.M2).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (T.hD.hT.rho T.N T.hD.hK.norm ⟨n⁻¹, hn'⟩).2.isUnit).ne_zero
  exact mul_ne_zero (mul_ne_zero hPd hdet) hQd

end CFSG.Quasithin.A94.He42
