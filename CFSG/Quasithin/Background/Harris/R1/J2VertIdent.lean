module

public import CFSG.Quasithin.Background.Harris.R1.J2VertAut
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.F2 CFSG.Quasithin.J2Cz.QM Equiv
  CFSG.CosetTable

structure VertGens (H : Type) [Group H] where
  z : H
  y : Fin 4 → H
  a : H
  b : H
  lift : LiftRel z y
  a_sq : a * a = 1
  b_cube : b * b * b = 1
  ab_five : (a * b) ^ 5 = 1
  za : z * a = a * z
  zb : z * b = b * z
  ax : ∀ j : Fin 5, a * lift.liftHom (x j) * a⁻¹ = lift.liftHom (x (pa j))
  bx : ∀ j : Fin 5, b * lift.liftHom (x j) * b⁻¹ = lift.liftHom (x (pb j))

namespace VertGens

variable {H : Type} [Group H] (g : VertGens H)

noncomputable abbrev chi : QM →* H := g.lift.liftHom

noncomputable abbrev Q : Subgroup H := g.chi.range

noncomputable abbrev L : Subgroup H := Subgroup.closure {g.a, g.b}

theorem chi_z : g.chi QM.z = g.z := by
  show liftT g.z g.y ⟨i, o, o, o, o⟩ 1 = g.z
  simp [liftT]

theorem chi_x1 : g.chi (x 1) = g.y 0 := by
  show liftT g.z g.y ⟨o, i, o, o, o⟩ 1 = g.y 0
  simp [liftT]

theorem chi_x2 : g.chi (x 2) = g.y 1 := by
  show liftT g.z g.y ⟨o, o, i, o, o⟩ 1 = g.y 1
  simp [liftT]

theorem chi_x3 : g.chi (x 3) = g.y 2 := by
  show liftT g.z g.y ⟨o, o, o, i, o⟩ 1 = g.y 2
  simp [liftT]

theorem chi_x4 : g.chi (x 4) = g.y 3 := by
  show liftT g.z g.y ⟨o, o, o, o, i⟩ 1 = g.y 3
  simp [liftT]

theorem chi_injective (hz : g.z ≠ 1) : Function.Injective g.chi := by
  rw [injective_iff_map_eq_one]
  intro p hp
  by_contra hne
  by_cases hc : ∀ j, p * x j = x j * p
  · rcases eq_of_comm_x p hc with h | h
    · exact hne h
    · exact hz (by rw [← g.chi_z, ← h, hp])
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    rcases conj_x p j with h | h
    · exact hj (by
        calc p * x j = p * x j * p⁻¹ * p := by group
          _ = x j * p := by rw [h])
    · have h1 : p * x j * p⁻¹ * (x j)⁻¹ = QM.z := by rw [h]; group
      have h2 := congrArg g.chi h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hp, g.chi_z] at h2
      exact hz (by rw [← h2]; group)

theorem z_mem_Q : g.z ∈ g.Q := ⟨QM.z, g.chi_z⟩

variable {g}

noncomputable def kappa (hχ : Function.Injective g.chi) [g.Q.Normal] : H →* MulAut QM :=
  (MulAut.congr (MonoidHom.ofInjective hχ).symm).toMonoidHom.comp MulAut.conjNormal

variable (hχ : Function.Injective g.chi) [g.Q.Normal]

theorem chi_kappa (h : H) (p : QM) : g.chi (kappa hχ h p) = h * g.chi p * h⁻¹ := by
  have e : kappa hχ h p = (MonoidHom.ofInjective hχ).symm
      (MulAut.conjNormal h (MonoidHom.ofInjective hχ p)) := rfl
  rw [e, MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem kappa_eq {h : H} {σ : MulAut QM}
    (hσ : ∀ j : Fin 4, h * g.chi (x j.succ) * h⁻¹ = g.chi (σ (x j.succ))) : kappa hχ h = σ :=
  aut_ext fun j => hχ (by rw [chi_kappa, hσ])

theorem kappa_spec {h : H} {σ : MulAut QM} (hk : kappa hχ h = σ) (p : QM) :
    h * g.chi p * h⁻¹ = g.chi (σ p) := by
  rw [← chi_kappa hχ, hk]

theorem kappa_a : kappa hχ g.a = phiA :=
  kappa_eq hχ fun j => by rw [g.ax, phiA_x]

theorem kappa_b : kappa hχ g.b = phiB :=
  kappa_eq hχ fun j => by rw [g.bx, phiB_x]

theorem kappa_chi (p : QM) : kappa hχ (g.chi p) = MulAut.conj p :=
  kappa_eq hχ fun j => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem kappa_eq_one {h : H} (hk : kappa hχ h = 1) : ∀ q ∈ g.Q, h * q = q * h := by
  rintro _ ⟨p, rfl⟩
  have := kappa_spec hχ hk p
  rw [MulAut.one_apply] at this
  calc h * g.chi p = h * g.chi p * h⁻¹ * h := by group
    _ = g.chi p * h := by rw [this]

theorem kappa_mem_L0 {l : H} (hl : l ∈ g.L) : kappa hχ l ∈ L0 := by
  induction hl using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [kappa_a]; exact phiA_mem
    · rw [kappa_b]; exact phiB_mem
  | one => rw [map_one]; exact one_mem _
  | mul y w _ _ ihy ihw => rw [map_mul]; exact mul_mem ihy ihw
  | inv y _ ihy => rw [map_inv]; exact inv_mem ihy

theorem exists_mem_L {φ : MulAut QM} (hφ : φ ∈ L0) : ∃ l ∈ g.L, kappa hχ l = φ := by
  rw [← closure_phiA_phiB] at hφ
  induction hφ using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨g.a, Subgroup.subset_closure (Set.mem_insert _ _), kappa_a hχ⟩
    · exact ⟨g.b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), kappa_b hχ⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul y w _ _ ihy ihw =>
    obtain ⟨l, hl, rfl⟩ := ihy
    obtain ⟨m, hm, rfl⟩ := ihw
    exact ⟨l * m, mul_mem hl hm, map_mul _ l m⟩
  | inv y _ ihy =>
    obtain ⟨l, hl, rfl⟩ := ihy
    exact ⟨l⁻¹, inv_mem hl, map_inv _ l⟩

end VertGens

end CFSG.Quasithin.Background.Harris.R1.J2Vert
