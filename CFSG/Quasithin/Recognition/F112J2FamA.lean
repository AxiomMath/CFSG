module

public import CFSG.Quasithin.Recognition.F112J2Act

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.A5Model

namespace F112J2

variable {G : Type} [Group G] {K1 S : Subgroup G}

structure ActData (K1 S : Subgroup G) where
  θ : ↥K1 →* A5
  surj : Function.Surjective θ
  stab : ∀ k : ↥K1, θ k ∈ A4s ↔ (k : G) ∈ borelOf K1 S

namespace ActData

variable (D : ActData K1 S)

theorem exists_kf (j : Fin 5) : ∃ k : ↥K1, (D.θ k : Equiv.Perm (Fin 5)) 4 = j := by
  obtain ⟨g, hg⟩ := a5_trans 4 j
  obtain ⟨k, hk⟩ := D.surj g
  exact ⟨k, by rw [hk]; exact hg⟩

noncomputable def kf (j : Fin 5) : ↥K1 := (D.exists_kf j).choose

theorem kf_spec (j : Fin 5) : (D.θ (D.kf j) : Equiv.Perm (Fin 5)) 4 = j :=
  (D.exists_kf j).choose_spec

theorem mem_borelOf_of_pt_eq {k k' : ↥K1}
    (h : (D.θ k : Equiv.Perm (Fin 5)) 4 = (D.θ k' : Equiv.Perm (Fin 5)) 4) :
    ((k⁻¹ * k' : ↥K1) : G) ∈ borelOf K1 S := by
  rw [← D.stab]
  change ((D.θ (k⁻¹ * k') : A5) : Equiv.Perm (Fin 5)) 4 = 4
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← h]
  exact Equiv.symm_apply_apply _ _

@[expose] noncomputable def Vf (V : Subgroup G) (j : Fin 5) : Subgroup G := conjSub (D.kf j : G) V

variable {V : Subgroup G}

theorem conjSub_V (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) (k : ↥K1) :
    conjSub (k : G) V = D.Vf V ((D.θ k : Equiv.Perm (Fin 5)) 4) := by
  set j := (D.θ k : Equiv.Perm (Fin 5)) 4 with hj
  have h := D.mem_borelOf_of_pt_eq (k := D.kf j) (k' := k) (by rw [D.kf_spec])
  have hN : (((D.kf j)⁻¹ * k : ↥K1) : G) ∈ Subgroup.normalizer (V : Set G) := hVn h
  have e : (k : G) = (D.kf j : G) * (((D.kf j)⁻¹ * k : ↥K1) : G) := by simp
  rw [e, conjSub_mul, conjSub_eq_of_mem_normalizer hN]
  rfl

theorem conjSub_Vf (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) (k : ↥K1) (j : Fin 5) :
    conjSub (k : G) (D.Vf V j) = D.Vf V ((D.θ k : Equiv.Perm (Fin 5)) j) := by
  have e : (k : G) * (D.kf j : G) = ((k * D.kf j : ↥K1) : G) := rfl
  unfold Vf
  rw [← conjSub_mul, e, D.conjSub_V hVn (k * D.kf j)]
  have : ((D.θ (k * D.kf j) : A5) : Equiv.Perm (Fin 5)) 4 =
      (D.θ k : Equiv.Perm (Fin 5)) j := by
    rw [map_mul]
    show (D.θ k : Equiv.Perm (Fin 5)) ((D.θ (D.kf j) : Equiv.Perm (Fin 5)) 4) = _
    rw [D.kf_spec]
  rw [this]
  rfl

theorem conjClosure_eq_iSup (hSK : S ≤ Subgroup.normalizer (K1 : Set G))
    (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hVn : borelOf K1 S ≤ Subgroup.normalizer (V : Set G)) :
    conjClosure V (K1 ⊔ S) = ⨆ j, D.Vf V j := by
  apply le_antisymm
  · refine conjClosure_le fun c hc v hv => ?_
    obtain ⟨k, hk, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSK).mp hc
    have hv' : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hSV hs) v).mp hv
    have e : k * s * v * (k * s)⁻¹ = k * (s * v * s⁻¹) * k⁻¹ := by group
    rw [e]
    have hmem : k * (s * v * s⁻¹) * k⁻¹ ∈ conjSub k V := mul_mem_conjSub hv'
    rw [show conjSub k V = D.Vf V ((D.θ ⟨k, hk⟩ : Equiv.Perm (Fin 5)) 4) from
      D.conjSub_V hVn ⟨k, hk⟩] at hmem
    exact (le_iSup (fun j => D.Vf V j) _) hmem
  · refine iSup_le fun j => ?_
    intro x hx
    have hx' : (D.kf j : G)⁻¹ * x * (D.kf j : G) ∈ V := mem_conjSub.mp hx
    have := mem_conjClosure (Z := V) (H := K1 ⊔ S) (h := (D.kf j : G))
      (z := (D.kf j : G)⁻¹ * x * (D.kf j : G)) (Subgroup.mem_sup_left (D.kf j).2) hx'
    simpa [mul_assoc] using this

end ActData

end F112J2

end CFSG.Quasithin
