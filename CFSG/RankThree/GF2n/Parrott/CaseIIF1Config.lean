module

public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Data
public import CFSG.RankThree.GF2n.Parrott.CaseII

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open _root_.Classical
attribute [local instance] _root_.Classical.propDecidable
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] {z : G}
variable {j y : G}

private abbrev Ksub (z j : G) : Subgroup G :=
  H z ⊓ Subgroup.centralizer ({j} : Set G)

private abbrev Qsub (z j : G) : Subgroup G :=
  J z ⊓ Subgroup.centralizer ({j} : Set G)

private abbrev Nsub (z j y : G) : Subgroup G :=
  Qsub z j |>.map (MulAut.conj y).toMonoidHom

private abbrev Esub (z j y : G) : Subgroup G := Qsub z j ⊓ Nsub z j y

private theorem mem_Ksub {x : G} : x ∈ Ksub z j ↔ x ∈ H z ∧ x * j = j * x := by
  rw [Ksub, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

private theorem mem_Qsub {x : G} : x ∈ Qsub z j ↔ x ∈ J z ∧ x * j = j * x := by
  rw [Qsub, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

private theorem mem_Nsub {n : G} :
    n ∈ Nsub z j y ↔ ∃ k ∈ Qsub z j, y * k * y⁻¹ = n := by
  simp [Nsub, Subgroup.mem_map, MulAut.conj_apply]

private theorem mem_Esub {e : G} :
    e ∈ Esub z j y ↔ e ∈ Qsub z j ∧ e ∈ Nsub z j y := by
  rw [Esub, Subgroup.mem_inf]

private theorem commute_of_conj_eq_self {a b : G} (h : a * b * a⁻¹ = b) :
    a * b = b * a := by
  have := congrArg (fun t => t * a) h
  simpa [mul_assoc] using this

private theorem conj_eq_self_of_commute {a b : G} (h : a * b = b * a) :
    a * b * a⁻¹ = b := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem rhoA_matrix_conj (a b : A45) :
    ((rhoA (a * b * a⁻¹) : GL8) : Mat8) =
      ((rhoA a : GL8) : Mat8) * ((rhoA b : GL8) : Mat8) *
        ((rhoA a⁻¹ : GL8) : Mat8) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]

private theorem conj_mem_K_of_maps {t : G}
    (htj : t * j * t⁻¹ = j) (htzj : t * (z * j) * t⁻¹ = z)
    (htz' : t⁻¹ * z * t = z * j) (htj' : t⁻¹ * j * t = j) {x : G}
    (hx : x ∈ Ksub z j) :
    t * x * t⁻¹ ∈ Ksub z j := by
  rw [mem_Ksub] at hx ⊢
  have hxzj : x * (z * j) * x⁻¹ = z * j := by
    have hcz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    have hcj : Commute x j := hx.2
    exact conj_eq_self_of_commute (hcz.mul_right hcj).eq
  constructor
  · change (t * x * t⁻¹) ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : (t * x * t⁻¹) * z * (t * x * t⁻¹)⁻¹ = z := by
      calc (t * x * t⁻¹) * z * (t * x * t⁻¹)⁻¹
          = t * (x * (t⁻¹ * z * t) * x⁻¹) * t⁻¹ := by group
        _ = t * (x * (z * j) * x⁻¹) * t⁻¹ := by rw [htz']
        _ = t * (z * j) * t⁻¹ := by rw [hxzj]
        _ = z := htzj
    exact commute_of_conj_eq_self hfix
  · have hfix : (t * x * t⁻¹) * j * (t * x * t⁻¹)⁻¹ = j := by
      calc (t * x * t⁻¹) * j * (t * x * t⁻¹)⁻¹
          = t * (x * (t⁻¹ * j * t) * x⁻¹) * t⁻¹ := by group
        _ = t * (x * j * x⁻¹) * t⁻¹ := by rw [htj']
        _ = t * j * t⁻¹ := by rw [conj_eq_self_of_commute hx.2]
        _ = j := htj
    exact commute_of_conj_eq_self hfix

private theorem y_maps (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) :
    y⁻¹ * z * y = z * j ∧ y * (z * j) * y⁻¹ = z ∧
      y⁻¹ * (z * j) * y = z ∧ y⁻¹ * j * y = j ∧ y * j * y⁻¹ = j := by
  have hyinvz : y⁻¹ * z * y = z * j := by
    have h1 : (y⁻¹ * z * y) * j = z := by
      calc (y⁻¹ * z * y) * j = y⁻¹ * z * (y * j) := by group
        _ = y⁻¹ * z * (j * y) := by rw [hyj]
        _ = y⁻¹ * (z * j) * y := by group
        _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [← hyz]
        _ = z := by group
    have h2 := congrArg (fun t => t * j) h1
    simpa [mul_assoc, hj2] using h2
  have hyinvj : y⁻¹ * j * y = j := by
    have h := congrArg (fun t => y⁻¹ * t) hyj
    simpa [mul_assoc] using h.symm
  have hyjinv : y * j * y⁻¹ = j := by
    rw [hyj, mul_assoc, mul_inv_cancel, mul_one]
  have hyzj : y * (z * j) * y⁻¹ = z := by
    calc y * (z * j) * y⁻¹ = (y * z * y⁻¹) * (y * j * y⁻¹) := by group
      _ = (z * j) * j := by rw [hyz, hyjinv]
      _ = z := by rw [mul_assoc, hj2, mul_one]
  have hyinvzj : y⁻¹ * (z * j) * y = z := by
    calc y⁻¹ * (z * j) * y = (y⁻¹ * z * y) * (y⁻¹ * j * y) := by group
      _ = (z * j) * j := by rw [hyinvz, hyinvj]
      _ = z := by rw [mul_assoc, hj2, mul_one]
  exact ⟨hyinvz, hyzj, hyinvzj, hyinvj, hyjinv⟩

private theorem conj_y_mem_K (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {x : G} (hx : x ∈ Ksub z j) :
    y * x * y⁻¹ ∈ Ksub z j := by
  obtain ⟨hyinvz, hyzj, hyinvzj, hyinvj, hyjinv⟩ := y_maps hj2 hyj hyz
  exact conj_mem_K_of_maps hyjinv hyzj hyinvz hyinvj hx

private theorem conj_yinv_mem_K (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {x : G} (hx : x ∈ Ksub z j) :
    y⁻¹ * x * y ∈ Ksub z j := by
  obtain ⟨hyinvz, hyzj, hyinvzj, hyinvj, hyjinv⟩ := y_maps hj2 hyj hyz
  simpa using conj_mem_K_of_maps (t := y⁻¹) (by simpa using hyinvj)
    (by simpa using hyinvzj) (by simpa using hyz) (by simpa using hyjinv) hx

private theorem y_sq_mem_K (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) : y * y ∈ Ksub z j := by
  obtain ⟨hyinvz, hyzj, hyinvzj, hyinvj, hyjinv⟩ := y_maps hj2 hyj hyz
  rw [mem_Ksub]
  constructor
  · change (y * y) ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : (y * y) * z * (y * y)⁻¹ = z := by
      calc (y * y) * z * (y * y)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ := by group
        _ = y * (z * j) * y⁻¹ := by rw [hyz]
        _ = z := hyzj
    exact commute_of_conj_eq_self hfix
  · have hfix : (y * y) * j * (y * y)⁻¹ = j := by
      calc (y * y) * j * (y * y)⁻¹ = y * (y * j * y⁻¹) * y⁻¹ := by group
        _ = y * j * y⁻¹ := by simp [hyjinv]
        _ = j := hyjinv
    exact commute_of_conj_eq_self hfix

private theorem Qsub_le_K [Finite G] : Qsub z j ≤ Ksub z j := by
  intro q hq
  rw [mem_Qsub] at hq
  rw [mem_Ksub]
  exact ⟨J_le_H hq.1, hq.2⟩

private theorem Nsub_le_K [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) : Nsub z j y ≤ Ksub z j := by
  intro n hn
  rw [mem_Nsub] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  exact conj_y_mem_K hj2 hyj hyz (Qsub_le_K hk)

private theorem Nsub_le_H [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) : Nsub z j y ≤ H z :=
  (Nsub_le_K hj2 hyj hyz).trans inf_le_left

private theorem Nsub_le_centralizer [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) :
    Nsub z j y ≤ Subgroup.centralizer ({j} : Set G) :=
  (Nsub_le_K hj2 hyj hyz).trans inf_le_right

private theorem conj_mem_Q_of_mem_K [Finite G] {x q : G} (hx : x ∈ Ksub z j)
    (hq : q ∈ Qsub z j) : x * q * x⁻¹ ∈ Qsub z j := by
  rw [mem_Ksub] at hx
  rw [mem_Qsub] at hq ⊢
  constructor
  · exact (Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A hx.1) q).mp hq.1
  · have hxinvj : x⁻¹ * j = j * x⁻¹ := by
      have hc : Commute x j := hx.2
      exact hc.inv_left.eq
    calc (x * q * x⁻¹) * j = x * q * (x⁻¹ * j) := by group
      _ = x * q * (j * x⁻¹) := by rw [hxinvj]
      _ = x * (q * j) * x⁻¹ := by group
      _ = x * (j * q) * x⁻¹ := by rw [hq.2]
      _ = (x * j) * q * x⁻¹ := by group
      _ = (j * x) * q * x⁻¹ := by rw [hx.2]
      _ = j * (x * q * x⁻¹) := by group

private theorem conj_mem_N_of_mem_K [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {x n : G} (hx : x ∈ Ksub z j)
    (hn : n ∈ Nsub z j y) : x * n * x⁻¹ ∈ Nsub z j y := by
  rw [mem_Nsub] at hn ⊢
  obtain ⟨k, hk, rfl⟩ := hn
  refine ⟨(y⁻¹ * x * y) * k * (y⁻¹ * x * y)⁻¹, ?_, ?_⟩
  · exact conj_mem_Q_of_mem_K (conj_yinv_mem_K hj2 hyj hyz hx) hk
  · group

private theorem conj_yinv_mem_N_of_mem_Q [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {k : G} (hk : k ∈ Qsub z j) :
    y⁻¹ * k * y ∈ Nsub z j y := by
  refine mem_Nsub.mpr ⟨(y * y)⁻¹ * k * (y * y), ?_, ?_⟩
  · simpa using conj_mem_Q_of_mem_K (x := (y * y)⁻¹) (q := k)
      ((Ksub z j).inv_mem (y_sq_mem_K hj2 hyj hyz)) hk
  · group

private theorem conj_yinv_mem_Q_of_mem_N {n : G} (hn : n ∈ Nsub z j y) :
    y⁻¹ * n * y ∈ Qsub z j := by
  rw [mem_Nsub] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  have h : y⁻¹ * (y * k * y⁻¹) * y = k := by group
  rw [h]
  exact hk

private theorem sq_mem_of_mem_Q {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) {k : G} (hk : k ∈ Qsub z j) :
    k * k = 1 ∨ k * k = z := by
  have h := hκ.sq k (mem_Qsub.mp hk).1
  by_cases hq : q (κ k) = 0
  · left
    rwa [if_pos hq] at h
  · right
    rwa [if_neg hq] at h

private theorem commutator_mem_of_mem_Q {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) {k k' : G} (hk : k ∈ Qsub z j) (hk' : k' ∈ Qsub z j) :
    k * k' * k⁻¹ * k'⁻¹ = 1 ∨ k * k' * k⁻¹ * k'⁻¹ = z := by
  have h := hκ.comm k (mem_Qsub.mp hk).1 k' (mem_Qsub.mp hk').1
  by_cases hb : b (κ k) (κ k') = 0
  · left
    rwa [if_pos hb] at h
  · right
    rwa [if_neg hb] at h

private theorem sq_mem_of_mem_N {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hyz : y * z * y⁻¹ = z * j) {n : G}
    (hn : n ∈ Nsub z j y) : n * n = 1 ∨ n * n = z * j := by
  rw [mem_Nsub] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  rcases sq_mem_of_mem_Q (z := z) (j := j) hκ hk with h | h
  · left
    calc (y * k * y⁻¹) * (y * k * y⁻¹) = y * (k * k) * y⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · right
    calc (y * k * y⁻¹) * (y * k * y⁻¹) = y * (k * k) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [h]
      _ = z * j := hyz

private theorem commutator_mem_of_mem_N {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hyz : y * z * y⁻¹ = z * j) {n n' : G}
    (hn : n ∈ Nsub z j y) (hn' : n' ∈ Nsub z j y) :
    n * n' * n⁻¹ * n'⁻¹ = 1 ∨ n * n' * n⁻¹ * n'⁻¹ = z * j := by
  rw [mem_Nsub] at hn hn'
  obtain ⟨k, hk, rfl⟩ := hn
  obtain ⟨k', hk', rfl⟩ := hn'
  rcases commutator_mem_of_mem_Q (z := z) (j := j) hκ hk hk' with h | h
  · left
    calc (y * k * y⁻¹) * (y * k' * y⁻¹) * (y * k * y⁻¹)⁻¹ * (y * k' * y⁻¹)⁻¹
        = y * (k * k' * k⁻¹ * k'⁻¹) * y⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · right
    calc (y * k * y⁻¹) * (y * k' * y⁻¹) * (y * k * y⁻¹)⁻¹ * (y * k' * y⁻¹)⁻¹
        = y * (k * k' * k⁻¹ * k'⁻¹) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [h]
      _ = z * j := hyz

private theorem sq_eq_one_of_mem_E {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) (hyz : y * z * y⁻¹ = z * j)
    (hzj_ne_z : z * j ≠ z) (hzj_ne_one : z * j ≠ 1) {e : G} (he : e ∈ Esub z j y) :
    e * e = 1 := by
  rw [mem_Esub] at he
  have hQ := sq_mem_of_mem_Q (z := z) (j := j) hκ he.1
  have hN := sq_mem_of_mem_N (z := z) (j := j) (y := y) hκ hyz he.2
  rcases hQ with h | h <;> rcases hN with h' | h'
  · exact h
  · exact absurd (h.symm.trans h').symm hzj_ne_one
  · exact absurd (h.symm.trans h') hz1
  · exact absurd (h.symm.trans h').symm hzj_ne_z

private theorem commute_of_mem_E {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) (hyz : y * z * y⁻¹ = z * j)
    (hzj_ne_z : z * j ≠ z) (hzj_ne_one : z * j ≠ 1) {e e' : G}
    (he : e ∈ Esub z j y) (he' : e' ∈ Esub z j y) : e * e' = e' * e := by
  rw [mem_Esub] at he he'
  have hQ := commutator_mem_of_mem_Q (z := z) (j := j) hκ he.1 he'.1
  have hN := commutator_mem_of_mem_N (z := z) (j := j) (y := y) hκ hyz he.2 he'.2
  have h1 : e * e' * e⁻¹ * e'⁻¹ = 1 := by
    rcases hQ with h | h <;> rcases hN with h' | h'
    · exact h
    · exact absurd (h.symm.trans h').symm hzj_ne_one
    · exact absurd (h.symm.trans h') hz1
    · exact absurd (h.symm.trans h').symm hzj_ne_z
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem conj_mem_E_of_mem_K [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {x e : G} (hx : x ∈ Ksub z j)
    (he : e ∈ Esub z j y) : x * e * x⁻¹ ∈ Esub z j y := by
  rw [mem_Esub] at he ⊢
  exact ⟨conj_mem_Q_of_mem_K hx he.1, conj_mem_N_of_mem_K hj2 hyj hyz hx he.2⟩

private theorem conj_y_mem_E [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {e : G} (he : e ∈ Esub z j y) :
    y * e * y⁻¹ ∈ Esub z j y := by
  rw [mem_Esub] at he ⊢
  constructor
  · have h1 : y⁻¹ * e * y ∈ Qsub z j := conj_yinv_mem_Q_of_mem_N he.2
    have h2 := conj_mem_Q_of_mem_K (x := y * y) (q := y⁻¹ * e * y)
      (y_sq_mem_K hj2 hyj hyz) h1
    have h3 : (y * y) * (y⁻¹ * e * y) * (y * y)⁻¹ = y * e * y⁻¹ := by group
    rwa [h3] at h2
  · exact mem_Nsub.mpr ⟨e, he.1, rfl⟩

private theorem conj_yinv_mem_E [Finite G] (hj2 : j * j = 1) (hyj : y * j = j * y)
    (hyz : y * z * y⁻¹ = z * j) {e : G} (he : e ∈ Esub z j y) :
    y⁻¹ * e * y ∈ Esub z j y := by
  rw [mem_Esub] at he ⊢
  exact ⟨conj_yinv_mem_Q_of_mem_N he.2,
    conj_yinv_mem_N_of_mem_Q hj2 hyj hyz he.1⟩

private noncomputable def psiN [Finite G] (ψ : ↥(H z) →* A45) (hj2 : j * j = 1)
    (hyj : y * j = j * y) (hyz : y * z * y⁻¹ = z * j) :
    ↥(Nsub z j y) →* A45 where
  toFun n := ψ ⟨(n : G), Nsub_le_H hj2 hyj hyz n.2⟩
  map_one' := by
    change ψ (1 : ↥(H z)) = 1
    simp
  map_mul' := by
    intro a b
    have h := map_mul ψ ⟨(a : G), Nsub_le_H hj2 hyj hyz a.2⟩
      ⟨(b : G), Nsub_le_H hj2 hyj hyz b.2⟩
    simpa using h

private theorem mem_spinStab_of_mem_K {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hjJ : j ∈ J z) {w₀ : V} (hjκ : κ j = w₀)
    {x : G} (hx : x ∈ Ksub z j) :
    ψ ⟨x, (mem_Ksub.mp hx).1⟩ ∈ spinStab w₀ := by
  have h := hκ.mem_spinStab hjJ (mem_Ksub.mp hx).1 (mem_Ksub.mp hx).2
  rwa [hjκ] at h

private theorem exists_mem_K_of_mem_spinStab [Finite G] {ψ : ↥(H z) →* A45}
    {κ : G → V} (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) (hjJ : j ∈ J z)
    {w₀ : V} (hjκ : κ j = w₀) (hnd : ∃ v : V, b v w₀ ≠ 0) {a : A45}
    (ha : a ∈ spinStab w₀) :
    ∃ (x : G) (hx : x ∈ H z), x * j = j * x ∧ ψ ⟨x, hx⟩ = a := by
  have hnd' : ∃ v : V, b v (κ j) ≠ 0 := by rwa [hjκ]
  have ha' : a ∈ spinStab (κ j) := by rwa [hjκ]
  exact hκ.exists_lift_of_mem_spinStab hzz hjJ hnd' ha'

private theorem comm_indicator_mul [Finite G] {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hz1 : z ≠ 1) (hzz : z * z = 1) (hj : j ∈ J z)
    {u v : G} (hu : u ∈ J z) (hv : v ∈ J z) :
    (if u * v * j = j * (u * v) then (0 : ZMod 2) else 1) =
      (if u * j = j * u then 0 else 1) + (if v * j = j * v then 0 else 1) := by
  have hcomm_u : ⁅u, j⁆ = 1 ∨ ⁅u, j⁆ = z := by
    have h := hκ.comm u hu j hj
    by_cases hv' : b (κ u) (κ j) = 0
    · left; rwa [if_pos hv'] at h
    · right; rwa [if_neg hv'] at h
  have hcomm_v : ⁅v, j⁆ = 1 ∨ ⁅v, j⁆ = z := by
    have h := hκ.comm v hv j hj
    by_cases hv' : b (κ v) (κ j) = 0
    · left; rwa [if_pos hv'] at h
    · right; rwa [if_neg hv'] at h
  have hcent : u * ⁅v, j⁆ * u⁻¹ = ⁅v, j⁆ := by
    rcases hcomm_v with h | h
    · rw [h, mul_one, mul_inv_cancel]
    · rw [h]
      exact conj_eq_self_of_commute (Subgroup.mem_centralizer_iff.mp
        (z_centralizes_J_A (z := z)) u hu)
  have hcab : ⁅u * v, j⁆ = ⁅v, j⁆ * ⁅u, j⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hcent]
  by_cases hu' : u * j = j * u <;> by_cases hv' : v * j = j * v
  · have hprod : u * v * j = j * (u * v) := by
      rw [← commutatorElement_eq_one_iff_mul_comm, hcab,
        commutatorElement_eq_one_iff_mul_comm.mpr hu',
        commutatorElement_eq_one_iff_mul_comm.mpr hv', mul_one]
    simp [hu', hv', hprod]
  · have hvval : ⁅v, j⁆ = z := by
      rcases hcomm_v with h | h
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hv'
      · exact h
    have hprod : ¬ u * v * j = j * (u * v) := by
      intro h
      have h1 : ⁅u * v, j⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
      rw [hcab, commutatorElement_eq_one_iff_mul_comm.mpr hu', hvval, mul_one] at h1
      exact hz1 h1
    simp [hu', hv', hprod]
  · have huval : ⁅u, j⁆ = z := by
      rcases hcomm_u with h | h
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hu'
      · exact h
    have hprod : ¬ u * v * j = j * (u * v) := by
      intro h
      have h1 : ⁅u * v, j⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
      rw [hcab, commutatorElement_eq_one_iff_mul_comm.mpr hv', huval, one_mul] at h1
      exact hz1 h1
    simp [hu', hv', hprod]
  · have huval : ⁅u, j⁆ = z := by
      rcases hcomm_u with h | h
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hu'
      · exact h
    have hvval : ⁅v, j⁆ = z := by
      rcases hcomm_v with h | h
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hv'
      · exact h
    have hprod : u * v * j = j * (u * v) := by
      rw [← commutatorElement_eq_one_iff_mul_comm, hcab, huval, hvval, hzz]
    simp [hu', hv', hprod]
    decide

private theorem card_Q_sub [Finite G] (h : Tim79a.ParrottHypA z)
    {ψ : ↥(H z) →* A45} {κ : G → V} (hκ : IsSpinCoord ψ κ) {w₀ : V}
    (hjκ : κ j = w₀) (hnd : ∃ v : V, b v w₀ ≠ 0) (hjJ : j ∈ J z) :
    Nat.card (Qsub z j) = 2 ^ 8 := by
  have hz1 : z ≠ 1 := by
    intro hz
    have hord := orderOf_z_A h
    rw [hz, orderOf_one] at hord
    norm_num at hord
  have hzz : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [orderOf_z_A h] at this
    simpa [pow_two] using h2
  let φQ : ↥(J z) →* Multiplicative (ZMod 2) :=
    { toFun := fun k => Multiplicative.ofAdd
        (if (k : G) * j = j * (k : G) then (0 : ZMod 2) else 1)
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [← ofAdd_add]
        congr 1
        exact comm_indicator_mul hκ hz1 hzz hjJ a.2 b.2 }
  have hker : φQ.ker = (Qsub z j).subgroupOf (J z) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Qsub]
    constructor
    · intro hk
      have h1 : (if (k : G) * j = j * (k : G) then (0 : ZMod 2) else 1) = 0 :=
        ofAdd_eq_one.mp hk
      by_cases hkj : (k : G) * j = j * (k : G)
      · exact ⟨k.2, hkj⟩
      · rw [if_neg hkj] at h1
        norm_num at h1
    · rintro ⟨hkJ, hkj⟩
      change Multiplicative.ofAdd
        (if (k : G) * j = j * (k : G) then (0 : ZMod 2) else 1) = 1
      rw [if_pos hkj]
      exact ofAdd_zero
  have htop : φQ.range = ⊤ := by
    have hk0 : ∃ k : ↥(J z), φQ k ≠ 1 := by
      obtain ⟨v, hv⟩ := hnd
      obtain ⟨k, hkJ, hkκ⟩ := hκ.surj v
      refine ⟨⟨k, hkJ⟩, ?_⟩
      intro h1
      have hzero : (if (k : G) * j = j * (k : G) then (0 : ZMod 2) else 1) = 0 :=
        ofAdd_eq_one.mp h1
      apply hv
      by_cases hc : (k : G) * j = j * (k : G)
      · have hb : b (κ j) (κ k) = 0 :=
          (hκ.commute_iff (j := j) (k := k) hz1 hjJ hkJ).mp hc.symm
        rw [hkκ, hjκ] at hb
        rw [spinB_comm v w₀]
        exact hb
      · rw [if_neg hc] at hzero
        norm_num at hzero
    obtain ⟨k0, hk0⟩ := hk0
    have hne : Nat.card φQ.range ≠ 1 := by
      intro hcard
      have hbot : φQ.range = ⊥ := Subgroup.eq_bot_of_card_eq φQ.range hcard
      have hmem : φQ k0 ∈ φQ.range := ⟨k0, rfl⟩
      rw [hbot] at hmem
      exact hk0 (Subgroup.mem_bot.mp hmem)
    have hdvd : Nat.card φQ.range ∣ Nat.card (Multiplicative (ZMod 2)) := by
      simpa using Subgroup.card_dvd_of_le (H := φQ.range) (K := ⊤) le_top
    have hcard2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hcard2] at hdvd
    have hrange2 : Nat.card φQ.range = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd h1 hne
      · exact h2
    exact Subgroup.eq_top_of_card_eq φQ.range (by rw [hrange2, hcard2])
  have hmul := Subgroup.card_ker_mul_card_range φQ
  have hker_card : Nat.card φQ.ker = Nat.card (Qsub z j) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show Qsub z j ≤ J z from inf_le_left)).toEquiv
  rw [hker_card, htop, Subgroup.card_top,
    show Nat.card (Multiplicative (ZMod 2)) = 2 by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod],
    card_J_A h] at hmul
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hmul
  omega

private theorem commutator_mem_E_of_mem_N_of_mem_Q [Finite G] (hj2 : j * j = 1)
    (hyj : y * j = j * y) (hyz : y * z * y⁻¹ = z * j) {n k : G}
    (hn : n ∈ Nsub z j y) (hk : k ∈ Qsub z j) :
    n * k * n⁻¹ * k⁻¹ ∈ Esub z j y := by
  rw [mem_Esub]
  constructor
  · have hnK : n ∈ Ksub z j := Nsub_le_K hj2 hyj hyz hn
    exact (Qsub z j).mul_mem (conj_mem_Q_of_mem_K hnK hk) ((Qsub z j).inv_mem hk)
  · have hkn : k * n * k⁻¹ ∈ Nsub z j y :=
      conj_mem_N_of_mem_K hj2 hyj hyz (Qsub_le_K hk) hn
    have h1 : k * n⁻¹ * k⁻¹ = (k * n * k⁻¹)⁻¹ := by group
    have h2 : n * k * n⁻¹ * k⁻¹ = n * (k * n⁻¹ * k⁻¹) := by group
    rw [h2, h1]
    exact (Nsub z j y).mul_mem hn ((Nsub z j y).inv_mem hkn)

theorem spinStabConfig_of_conj_eq [Finite G] (h : Tim79a.ParrottHypA z)
    {ψ : ↥(H z) →* A45} {κ : G → V} (hκ : IsSpinCoord ψ κ) {w₀ : V}
    (hinj : ∀ a : A45, ((rhoA a : GL8) : Mat8) = 1 → a = 1)
    (hnd : ∃ v : V, b v w₀ ≠ 0)
    {j : G} (hjJ : j ∈ J z) (hjκ : κ j = w₀)
    {y : G} (hyj : y * j = j * y) (hyz : y * z * y⁻¹ = z * j) :
    ∃ (W : Set V) (ℬ : Set Mat8), SpinStabConfig w₀ W ℬ := by
  classical
  have hz1 : z ≠ 1 := by
    intro hz
    have hord := orderOf_z_A h
    rw [hz, orderOf_one] at hord
    norm_num at hord
  have hzz : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [orderOf_z_A h] at this
    simpa [pow_two] using h2
  have hzJ : z ∈ J z := z_mem_J_A h
  have hw0 : w₀ ≠ 0 := by
    intro hw
    obtain ⟨v, hv⟩ := hnd
    apply hv
    rw [hw]
    have hq0 : q (0 : V) = 0 := by simp [q]
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    have hb : b v 0 = q v + q v := by simp [b, hq0]
    rw [hb, h2]
  have hjz : j ≠ z := by
    intro e
    apply hw0
    have h0 : κ j = 0 := by
      rw [e]
      exact (hκ.eq_zero_iff z hzJ).mpr (Or.inr rfl)
    rw [hjκ] at h0
    exact h0
  have hj1 : j ≠ 1 := by
    intro e
    apply hw0
    have h0 : κ j = 0 := by rw [e, hκ.kappa_one]
    rw [hjκ] at h0
    exact h0
  have hzj_comm : z * j = j * z :=
    (Subgroup.mem_centralizer_iff.mp (z_centralizes_J_A (z := z)) j hjJ).symm
  have hzj_sq : (z * j) * (z * j) = 1 := by
    calc (z * j) * (z * j) = (y * z * y⁻¹) * (y * z * y⁻¹) := by rw [← hyz]
      _ = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
  have hj2 : j * j = 1 := by
    calc j * j = (z * z) * (j * j) := by rw [hzz, one_mul]
      _ = ((z * z) * j) * j := by rw [← mul_assoc]
      _ = (z * (z * j)) * j := by rw [← mul_assoc z z j]
      _ = z * ((z * j) * j) := by rw [mul_assoc]
      _ = z * ((j * z) * j) := by rw [hzj_comm]
      _ = z * (j * (z * j)) := by rw [mul_assoc j z j]
      _ = (z * j) * (z * j) := by rw [← mul_assoc]
      _ = 1 := hzj_sq
  have hzj_ne_z : z * j ≠ z := by
    intro h
    exact hj1 (mul_left_cancel (a := z) (by simpa using h))
  have hzj_ne_one : z * j ≠ 1 := by
    intro h
    have h1 : y * z * y⁻¹ = 1 := by rw [hyz, h]
    have h2 : z = 1 := by
      have := congrArg (fun t => y⁻¹ * t * y) h1
      simpa [mul_assoc] using this
    exact hz1 h2
  obtain ⟨hyinvz, hyzj, hyinvzj, hyinvj, hyjinv⟩ := y_maps hj2 hyj hyz
  have hQK : Qsub z j ≤ Ksub z j := Qsub_le_K
  have hNK : Nsub z j y ≤ Ksub z j := Nsub_le_K hj2 hyj hyz
  have hNH : Nsub z j y ≤ H z := Nsub_le_H hj2 hyj hyz
  have hNC : Nsub z j y ≤ Subgroup.centralizer ({j} : Set G) :=
    Nsub_le_centralizer hj2 hyj hyz
  have hy2K : y * y ∈ Ksub z j := y_sq_mem_K hj2 hyj hyz
  have hzQ : z ∈ Qsub z j := mem_Qsub.mpr ⟨hzJ, hzj_comm⟩
  have hzjQ : z * j ∈ Qsub z j := by
    rw [mem_Qsub]
    refine ⟨(J z).mul_mem hzJ hjJ, ?_⟩
    have h1 : (z * j) * j = z := by rw [mul_assoc, hj2, mul_one]
    have h2 : j * (z * j) = z := by
      calc j * (z * j) = (j * z) * j := by rw [mul_assoc]
        _ = (z * j) * j := by rw [← hzj_comm]
        _ = z := h1
    exact h1.trans h2.symm
  have hzN : z ∈ Nsub z j y := mem_Nsub.mpr ⟨z * j, hzjQ, hyzj⟩
  have hzE : z ∈ Esub z j y := mem_Esub.mpr ⟨hzQ, hzN⟩
  have hjQ : j ∈ Qsub z j := mem_Qsub.mpr ⟨hjJ, rfl⟩
  have hjN : j ∈ Nsub z j y := mem_Nsub.mpr ⟨j, hjQ, hyjinv⟩
  have hjE : j ∈ Esub z j y := mem_Esub.mpr ⟨hjQ, hjN⟩
  have hsqE : ∀ e ∈ Esub z j y, e * e = 1 := fun e he =>
    sq_eq_one_of_mem_E hκ hz1 hyz hzj_ne_z hzj_ne_one he
  have hcommE : ∀ e ∈ Esub z j y, ∀ e' ∈ Esub z j y, e * e' = e' * e :=
    fun e he e' he' => commute_of_mem_E hκ hz1 hyz hzj_ne_z hzj_ne_one he he'
  have hconjEK : ∀ x ∈ Ksub z j, ∀ e ∈ Esub z j y, x * e * x⁻¹ ∈ Esub z j y :=
    fun x hx e he => conj_mem_E_of_mem_K hj2 hyj hyz hx he
  have hconjEy : ∀ e ∈ Esub z j y, y * e * y⁻¹ ∈ Esub z j y :=
    fun e he => conj_y_mem_E hj2 hyj hyz he
  have hconjEyinv : ∀ e ∈ Esub z j y, y⁻¹ * e * y ∈ Esub z j y :=
    fun e he => conj_yinv_mem_E hj2 hyj hyz he
  have hcommNQ : ∀ n ∈ Nsub z j y, ∀ k ∈ Qsub z j,
      n * k * n⁻¹ * k⁻¹ ∈ Esub z j y :=
    fun n hn k hk => commutator_mem_E_of_mem_N_of_mem_Q hj2 hyj hyz hn hk
  let W : Set V := {v : V | ∃ e : G, e ∈ Esub z j y ∧ κ e = v}
  let Φ : ↥(Nsub z j y) →* GL8 := rhoA.comp (psiN ψ hj2 hyj hyz)
  let ℬ : Set Mat8 := (fun u : GL8 => (u : Mat8)) '' (Φ.range : Set GL8)
  have hWmem : ∀ {v : V}, v ∈ W ↔ ∃ e : G, e ∈ Esub z j y ∧ κ e = v := by
    intro v
    rfl
  have hΦapply : ∀ n : ↥(Nsub z j y), Φ n = rhoA (ψ ⟨(n : G), hNH n.2⟩) := fun _ => rfl
  have hBmem : ∀ {σ : Mat8}, σ ∈ ℬ ↔ ∃ u : GL8, u ∈ Φ.range ∧ (u : Mat8) = σ := by
    intro σ
    exact Set.mem_image _ _ _
  refine ⟨W, ℬ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨1, (Esub z j y).one_mem, hκ.kappa_one⟩
  · rintro v ⟨e, he, rfl⟩ w ⟨e', he', rfl⟩
    refine ⟨e * e', (Esub z j y).mul_mem he he', ?_⟩
    rw [hκ.add e (mem_Esub.mp he).1.1 e' (mem_Esub.mp he').1.1]
  · exact ⟨j, hjE, hjκ⟩
  · rintro v ⟨e, he, rfl⟩
    exact (hκ.mul_self_eq_one_iff hz1 (mem_Esub.mp he).1.1).mp (hsqE e he)
  · rintro a ha v ⟨e, he, rfl⟩
    obtain ⟨x, hxH, hxj, hψx⟩ :=
      exists_mem_K_of_mem_spinStab hκ hzz hjJ hjκ hnd ha
    have hxK : x ∈ Ksub z j := mem_Ksub.mpr ⟨hxH, hxj⟩
    refine ⟨x * e * x⁻¹, hconjEK x hxK e he, ?_⟩
    rw [hκ.act x hxH e (mem_Esub.mp he).1.1, hψx]
  · rintro σ ⟨u, hu, hval⟩
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hu
    refine ⟨psiN ψ hj2 hyj hyz n, ?_, ?_⟩
    · exact mem_spinStab_of_mem_K hκ hjJ hjκ (hNK n.2)
    · rw [← hval, ← hn]
      rfl
  · exact hBmem.mpr ⟨1, Φ.range.one_mem, by simp⟩
  · intro σ hσ σ' hσ'
    obtain ⟨u, hu, hval⟩ := hBmem.mp hσ
    obtain ⟨u', hu', hval'⟩ := hBmem.mp hσ'
    exact hBmem.mpr ⟨u * u', Φ.range.mul_mem hu hu', by rw [Units.val_mul, hval, hval']⟩
  · intro a ha σ hσ
    obtain ⟨u, hu, hval⟩ := hBmem.mp hσ
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hu
    obtain ⟨x, hxH, hxj, hψx⟩ :=
      exists_mem_K_of_mem_spinStab hκ hzz hjJ hjκ hnd ha
    have hxK : x ∈ Ksub z j := mem_Ksub.mpr ⟨hxH, hxj⟩
    have hmem : x * (n : G) * x⁻¹ ∈ Nsub z j y :=
      conj_mem_N_of_mem_K hj2 hyj hyz hxK n.2
    have hpsi : ψ ⟨x * (n : G) * x⁻¹, hNH hmem⟩ =
        a * psiN ψ hj2 hyj hyz n * a⁻¹ := by
      rw [← hψx]
      change ψ ⟨x * (n : G) * x⁻¹, hNH hmem⟩ =
        ψ ⟨x, hxH⟩ * ψ ⟨(n : G), hNH n.2⟩ * (ψ ⟨x, hxH⟩)⁻¹
      have hsub : (⟨x * (n : G) * x⁻¹, hNH hmem⟩ : ↥(H z)) =
          ⟨x, hxH⟩ * ⟨(n : G), hNH n.2⟩ * ⟨x, hxH⟩⁻¹ := by
        ext
        rfl
      rw [hsub, map_mul, map_mul, map_inv]
    refine hBmem.mpr ⟨Φ ⟨x * (n : G) * x⁻¹, hmem⟩, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨x * (n : G) * x⁻¹, hmem⟩, rfl⟩
    · rw [← hval, ← hn, hΦapply ⟨x * (n : G) * x⁻¹, hmem⟩, hΦapply n, hpsi]
      exact rhoA_matrix_conj a (psiN ψ hj2 hyj hyz n)
  · rintro σ hσ v hv
    obtain ⟨u, hu, hval⟩ := hBmem.mp hσ
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hu
    rw [← hval, ← hn]
    obtain ⟨k, hkJ, hkκ⟩ := hκ.surj v
    have hkQ : k ∈ Qsub z j := by
      rw [mem_Qsub]
      refine ⟨hkJ, ?_⟩
      have hb : b (κ j) (κ k) = 0 := by
        rw [hjκ, hkκ, spinB_comm w₀ v]
        exact hv
      exact (hκ.commute_iff (j := j) (k := k) hz1 hjJ hkJ).mpr hb |>.symm
    have hnkJ : n * k * n⁻¹ ∈ J z :=
      (mem_Qsub.mp (conj_mem_Q_of_mem_K (hNK n.2) hkQ)).1
    have hnk : κ (n * k * n⁻¹) = ((Φ n : GL8) : Mat8) *ᵥ v := by
      have h := hκ.act (n : G) (hNH n.2) k hkJ
      rw [hkκ] at h
      rwa [← hΦapply n] at h
    have hsum : ((Φ n : GL8) : Mat8) *ᵥ v + v = κ (n * k * n⁻¹ * k⁻¹) := by
      have hnk' : κ (n * k * n⁻¹) = ((Φ n : GL8) : Mat8) *ᵥ κ k := by
        simpa [hkκ] using hnk
      rw [← hkκ, ← hnk', ← hκ.kappa_inv hkJ,
        hκ.add (n * k * n⁻¹) hnkJ (k⁻¹) ((J z).inv_mem hkJ)]
    exact ⟨n * k * n⁻¹ * k⁻¹, hcommNQ (n : G) n.2 k hkQ, hsum.symm⟩
  · rintro σ hσ v hv
    obtain ⟨u, hu, hval⟩ := hBmem.mp hσ
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hu
    rw [← hval, ← hn]
    obtain ⟨e, he, rfl⟩ := hv
    have heJ : e ∈ J z := (mem_Esub.mp he).1.1
    have hneJ : n * e * n⁻¹ ∈ J z :=
      (mem_Qsub.mp (conj_mem_Q_of_mem_K (hNK n.2) (mem_Esub.mp he).1)).1
    have hne : κ (n * e * n⁻¹) = ((Φ n : GL8) : Mat8) *ᵥ κ e := by
      have h := hκ.act (n : G) (hNH n.2) e heJ
      rwa [← hΦapply n] at h
    have hval' : ((Φ n : GL8) : Mat8) *ᵥ κ e + κ e = κ (n * e * n⁻¹ * e⁻¹) := by
      rw [← hne, ← hκ.kappa_inv heJ,
        hκ.add (n * e * n⁻¹) hneJ (e⁻¹) ((J z).inv_mem heJ)]
    rcases commutator_mem_of_mem_N hκ hyz n.2 (mem_Esub.mp he).2 with h | h
    · left
      simpa [h, hκ.kappa_one] using hval'
    · right
      simpa [h, hκ.add z hzJ j hjJ,
        (hκ.eq_zero_iff z hzJ).mpr (Or.inr rfl), zero_add, hjκ] using hval'
  · let φE : ↥(Esub z j y) →* Multiplicative V :=
      { toFun := fun e => Multiplicative.ofAdd (κ (e : G))
        map_one' := by simp [hκ.kappa_one]
        map_mul' := by
          intro a b
          change Multiplicative.ofAdd (κ ((a : G) * (b : G))) =
            Multiplicative.ofAdd (κ (a : G)) * Multiplicative.ofAdd (κ (b : G))
          rw [show κ ((a : G) * (b : G)) = κ (a : G) + κ (b : G) from
            hκ.add (a : G) (mem_Esub.mp a.2).1.1 (b : G) (mem_Esub.mp b.2).1.1,
            ofAdd_add] }
    have hφEker : φE.ker = Subgroup.zpowers (⟨z, hzE⟩ : ↥(Esub z j y)) := by
      apply le_antisymm
      · intro e he
        rw [MonoidHom.mem_ker] at he
        have hκe0 : κ (e : G) = 0 := ofAdd_eq_one.mp he
        have heJ : (e : G) ∈ J z := (mem_Esub.mp e.2).1.1
        rcases (hκ.eq_zero_iff (e : G) heJ).mp hκe0 with h1 | hz
        · have he1 : e = 1 := Subtype.ext h1
          rw [he1]
          exact Subgroup.one_mem _
        · have hez : e = ⟨z, hzE⟩ := Subtype.ext hz
          rw [hez]
          exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le]
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd (κ z) = 1
        rw [show κ z = 0 from (hκ.eq_zero_iff z hzJ).mpr (Or.inr rfl)]
        exact ofAdd_zero
    have hW_eq : W = Multiplicative.toAdd '' (φE.range : Set (Multiplicative V)) := by
      ext v
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨φE ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hm
        exact ⟨e, e.2, rfl⟩
    have hWcard : W.ncard = Nat.card φE.range := by
      rw [hW_eq, Set.ncard_image_of_injective _ Multiplicative.toAdd.injective]
      exact (Nat.card_coe_set_eq (φE.range : Set (Multiplicative V))).symm
    have hcardkerE : Nat.card φE.ker = 2 := by
      rw [hφEker, Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_z_A h]
    have hEcard : Nat.card (Esub z j y) = 2 * W.ncard := by
      have hmul := Subgroup.card_ker_mul_card_range φE
      calc Nat.card (Esub z j y) = Nat.card φE.ker * Nat.card φE.range := hmul.symm
        _ = 2 * Nat.card φE.range := by rw [hcardkerE]
        _ = 2 * W.ncard := by rw [← hWcard]
    have hQcard : Nat.card (Qsub z j) = 2 ^ 8 := card_Q_sub h hκ hjκ hnd hjJ
    have hNcard : Nat.card (Nsub z j y) = 2 ^ 8 := by
      rw [Nsub, Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective, hQcard]
    have hkerΦ : Φ.ker = (Esub z j y).subgroupOf (Nsub z j y) := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Esub]
      constructor
      · intro hn
        have hmat : ((rhoA (psiN ψ hj2 hyj hyz n) : GL8) : Mat8) = 1 := by
          have := congrArg (fun u : GL8 => ((u : GL8) : Mat8)) hn
          simpa [Φ] using this
        have hψ1 : psiN ψ hj2 hyj hyz n = 1 := hinj _ hmat
        have hnJ : (n : G) ∈ J z :=
          (hκ.eq_one_iff ⟨(n : G), hNH n.2⟩).mp hψ1
        have hnQ : (n : G) ∈ Qsub z j := ⟨hnJ, hNC n.2⟩
        exact ⟨hnQ, n.2⟩
      · rintro ⟨hnQ, hnN⟩
        have hnJ : (n : G) ∈ J z := hnQ.1
        have hψ1 : psiN ψ hj2 hyj hyz n = 1 :=
          (hκ.eq_one_iff ⟨(n : G), hNH n.2⟩).mpr hnJ
        change rhoA (psiN ψ hj2 hyj hyz n) = 1
        rw [hψ1, map_one]
    have hkerΦcard : Nat.card Φ.ker = Nat.card (Esub z j y) := by
      rw [hkerΦ]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (show Esub z j y ≤ Nsub z j y from inf_le_right)).toEquiv
    have hBcard : ℬ.ncard = Nat.card Φ.range := by
      have hBeq : ℬ = (fun u : GL8 => (u : Mat8)) '' (Φ.range : Set GL8) := rfl
      rw [hBeq, Set.ncard_image_of_injective _ Units.val_injective]
      exact (Nat.card_coe_set_eq (Φ.range : Set GL8)).symm
    have hEB : Nat.card (Esub z j y) * ℬ.ncard = Nat.card (Nsub z j y) := by
      have hmul := Subgroup.card_ker_mul_card_range Φ
      rw [hkerΦcard, ← hBcard] at hmul
      exact hmul
    rw [hEcard, hNcard] at hEB
    have h2 : 2 * (ℬ.ncard * W.ncard) = 2 * 128 := by
      calc 2 * (ℬ.ncard * W.ncard) = (2 * W.ncard) * ℬ.ncard := by ring
        _ = 2 ^ 8 := hEB
        _ = 2 * 128 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  · intro hperp σ hσ hfix
    obtain ⟨u, hu, hval⟩ := hBmem.mp hσ
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hu
    rw [← hval, ← hn]
    have hcenE : ∀ e ∈ Esub z j y, (n : G) * e = e * (n : G) := by
      intro e he
      have heJ : e ∈ J z := (mem_Esub.mp he).1.1
      have hκeW : κ e ∈ W := ⟨e, he, rfl⟩
      have hfixe : ((Φ n : GL8) : Mat8) *ᵥ κ e = κ e := by
        have h := hfix (κ e) hκeW
        rwa [← hval, ← hn] at h
      have hne : κ ((n : G) * e * (n : G)⁻¹) = κ e := by
        have h := hκ.act (n : G) (hNH n.2) e heJ
        rw [← hΦapply n] at h
        exact h.trans hfixe
      have hneQ : (n : G) * e * (n : G)⁻¹ ∈ Qsub z j :=
        conj_mem_Q_of_mem_K (hNK n.2) (mem_Esub.mp he).1
      have hneJ : (n : G) * e * (n : G)⁻¹ ∈ J z := (mem_Qsub.mp hneQ).1
      rcases (hκ.kappa_eq_iff heJ hneJ).mp hne with h | h
      · calc (n : G) * e = ((n : G) * e * (n : G)⁻¹) * (n : G) := by group
          _ = e * (n : G) := by rw [h]
      · exfalso
        have hcz : (n : G) * e * (n : G)⁻¹ * e⁻¹ = z := by
          rw [h, hcommE e he z hzE]
          group
        rcases commutator_mem_of_mem_N hκ hyz n.2 (mem_Esub.mp he).2 with hc | hc
        · rw [hcz] at hc
          exact hz1 hc
        · rw [hcz] at hc
          exact hzj_ne_z hc.symm
    let k : G := y⁻¹ * (n : G) * y
    have hkQ : k ∈ Qsub z j := by
      dsimp [k]
      exact conj_yinv_mem_Q_of_mem_N n.2
    have hcenEk : ∀ e ∈ Esub z j y, k * e = e * k := by
      intro e he
      have hconj : k * e * k⁻¹ = e := by
        have hc := hcenE (y * e * y⁻¹) (hconjEy e he)
        have h1 : k * e * k⁻¹ =
            y⁻¹ * ((n : G) * (y * e * y⁻¹) * (n : G)⁻¹) * y := by
          dsimp [k]
          simp [mul_assoc]
        rw [h1, hc]
        group
      exact commute_of_conj_eq_self hconj
    have hb : ∀ e ∈ Esub z j y, b (κ k) (κ e) = 0 := by
      intro e he
      have hkJ : k ∈ J z := (mem_Qsub.mp hkQ).1
      have heJ : e ∈ J z := (mem_Esub.mp he).1.1
      exact (hκ.commute_iff (j := k) (k := e) hz1 hkJ heJ).mp (hcenEk e he)
    have hperp_k : ∀ w ∈ W, b (κ k) w = 0 := by
      rintro w ⟨e, he, rfl⟩
      exact hb e he
    have hkW : κ k ∈ W := hperp (κ k) hperp_k
    obtain ⟨e', he', hκe'⟩ := hkW
    have hkE : k ∈ Esub z j y := by
      have he'J : e' ∈ J z := (mem_Esub.mp he').1.1
      have hkJ : k ∈ J z := (mem_Qsub.mp hkQ).1
      rcases (hκ.kappa_eq_iff (j := e') (k := k) he'J hkJ).mp hκe'.symm with h | h
      · rw [h]
        exact he'
      · rw [h]
        exact (Esub z j y).mul_mem he' hzE
    have hnE : (n : G) ∈ Esub z j y := by
      have h := hconjEy k hkE
      rwa [show y * k * y⁻¹ = (n : G) by dsimp [k]; group] at h
    have hnJ : (n : G) ∈ J z := (mem_Esub.mp hnE).1.1
    have hψn : psiN ψ hj2 hyj hyz n = 1 :=
      (hκ.eq_one_iff ⟨(n : G), hNH n.2⟩).mpr hnJ
    change ((rhoA (psiN ψ hj2 hyj hyz n) : GL8) : Mat8) = 1
    rw [hψn, map_one]
    rfl
end CFSG.RankThree.GF2n.Parrott
