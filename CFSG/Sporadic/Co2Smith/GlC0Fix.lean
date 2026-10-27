module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
public import CFSG.Sporadic.Co2Smith.GlDataElts
public import CFSG.Sporadic.Co2Smith.GlDataStab

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_fixPts_perm_conj (σ τ : Equiv.Perm (Fin 2300)) :
    Nat.card {y : Fin 2300 // (σ * τ * σ⁻¹) y = y} = Nat.card {y : Fin 2300 // τ y = y} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨σ⁻¹ y, ?_⟩
      invFun := fun y => ⟨σ y, ?_⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have h := y.2
    simp only [Equiv.Perm.mul_apply] at h
    have h2 := congrArg (fun w => σ⁻¹ w) h
    simpa using h2
  · simp [Equiv.Perm.mul_apply, y.2]


@[expose] noncomputable def fixK (g : K) : ℕ :=
  Nat.card {x : Fin 2300 // co2PermHom g x = x}

theorem fixK_conj (g x : K) : fixK (g * x * g⁻¹) = fixK x := by
  unfold fixK
  rw [map_mul, map_mul, map_inv]
  exact card_fixPts_perm_conj _ _

theorem fixK_eq_of_isConj {x y : K} (h : IsConj x y) : fixK x = fixK y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact (fixK_conj c x).symm

theorem fixK_of_fixIs {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R) {k : ℕ}
    (h : Native.glMkFixIs R k = true) : fixK g = k := by
  simp only [Native.glMkFixIs, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hp, hk⟩ := h
  obtain ⟨-, hrep⟩ := rep_co2PermHom_of_permOK hg hp
  set p := Native.glPermArr R
  set pts := (List.range 2300).filter fun i => p[i]! == i
  have hnd : pts.Nodup := (List.nodup_range).filter _
  have hlt : ∀ x ∈ pts, x < 2300 := fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1
  have hset : {x : Fin 2300 | co2PermHom g x = x} = {y : Fin 2300 | (y : ℕ) ∈ pts} := by
    ext y
    simp only [Set.mem_ofPred_eq, pts, List.mem_filter, List.mem_range, y.2, true_and,
      beq_iff_eq]
    rw [hrep y]
    exact ⟨fun e => by rw [e], fun e => Fin.ext e⟩
  have hcard : fixK g = {x : Fin 2300 | co2PermHom g x = x}.ncard :=
    Nat.card_coe_set_eq {x : Fin 2300 | co2PermHom g x = x}
  rw [hcard, hset, ncard_setOf_mem hnd hlt]
  exact hk

end CFSG.Sporadic.Co2Smith
