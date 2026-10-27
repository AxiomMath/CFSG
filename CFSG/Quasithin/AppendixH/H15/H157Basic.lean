module

public import CFSG.Quasithin.Background.H153Grp
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def tA : ↥AutPerm := ⟨tP, tP_mem⟩

@[expose] def tFix : Finset (Fin 24) := {1, 5, 11, 15, 18, 22}

theorem mem_tFix_iff (i : Fin 24) : i ∈ tFix ↔ tP i = i := by
  have h : ∀ i : Fin 24, (tP i = i) ↔ (tArr[(i : ℕ)]! = (i : ℕ)) := by
    intro i
    rw [Fin.ext_iff, hasArr_tP i]
  rw [h i]
  revert i
  decide +kernel

theorem card_tFix : tFix.card = 6 := by
  decide

@[expose] def fixPt (j : Fin 6) : Fin 24 := ![1, 5, 11, 15, 18, 22] j

theorem colOf_fixPt (j : Fin 6) : colOf (fixPt j) = j := by
  revert j
  decide +kernel

theorem fixPt_mem_tFix (j : Fin 6) : fixPt j ∈ tFix := by
  revert j
  decide +kernel

theorem fixPt_injective : Function.Injective fixPt := by
  decide +kernel

theorem eq_fixPt_colOf {i : Fin 24} (hi : i ∈ tFix) : i = fixPt (colOf i) := by
  revert i
  decide +kernel

theorem mem_tFix_iff_exists {i : Fin 24} : i ∈ tFix ↔ ∃ j, fixPt j = i := by
  revert i
  decide +kernel

@[expose] noncomputable def fixW (y : ↥AutPerm) : Subgroup W11 :=
  fixV (Subgroup.zpowers (rhoM24 y))

theorem mem_fixW {y : ↥AutPerm} {w : W11} : w ∈ fixW y ↔ rhoM24 y w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff

@[expose] def Is3A (y : ↥AutPerm) : Prop := ∃ c : ↥AutPerm, c * y * c⁻¹ = tA

theorem Is3A.orderOf_eq {y : ↥AutPerm} (hy : Is3A y) : orderOf y = 3 := by
  obtain ⟨c, hc⟩ := hy
  have h1 : orderOf (MulAut.conj c y) = orderOf y := by
    simpa using orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  have hcy : MulAut.conj c y = tA := by
    rw [MulAut.conj_apply]
    exact hc
  rw [← h1, hcy]
  simpa [tA] using orderOf_tP

theorem Is3A.card_fixedPoints {y : ↥AutPerm} (hy : Is3A y) :
    (Finset.univ.filter fun i : Fin 24 => (y : S24) i = i).card = 6 := by
  obtain ⟨c, hc⟩ := hy
  have hcval : ((c : S24) * (y : S24) * (c : S24)⁻¹) = tP := by
    have := congrArg Subtype.val hc
    simpa [tA] using this
  have hyval : (y : S24) = (c : S24)⁻¹ * tP * (c : S24) := by
    rw [← hcval]
    group
  have hset : (Finset.univ.filter fun i : Fin 24 => (y : S24) i = i) =
      tFix.image (fun i : Fin 24 => (c : S24)⁻¹ i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [hyval]
    constructor
    · intro h
      refine ⟨(c : S24) i, ?_, ?_⟩
      · rw [mem_tFix_iff]
        have h2 : (c : S24) (((c : S24)⁻¹ * tP * (c : S24)) i) = (c : S24) i :=
          congrArg (fun x : Fin 24 => (c : S24) x) h
        simpa [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using h2
      · simp
    · rintro ⟨j, hj, rfl⟩
      rw [mem_tFix_iff] at hj
      simp [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, hj]
  rw [hset, Finset.card_image_of_injective tFix (f := fun i : Fin 24 => (c : S24)⁻¹ i)
    ((c : S24)⁻¹).injective, card_tFix]

theorem mem_fixW_conj (c y : ↥AutPerm) (w : W11) :
    rhoM24 c w ∈ fixW (c * y * c⁻¹) ↔ w ∈ fixW y := by
  rw [mem_fixW, mem_fixW]
  have h1 : rhoM24 (c * y * c⁻¹) = rhoM24 c * rhoM24 y * (rhoM24 c)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [h1, MulAut.mul_apply, MulAut.mul_apply]
  have hinv : (rhoM24 c)⁻¹ (rhoM24 c w) = w := by
    rw [← MulAut.mul_apply, ← map_inv, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv]
  constructor
  · intro h
    exact (rhoM24 c).injective h
  · intro h
    rw [h]

theorem card_fixW_conj (c y : ↥AutPerm) :
    Nat.card ↥(fixW (c * y * c⁻¹)) = Nat.card ↥(fixW y) := by
  have h : fixW (c * y * c⁻¹) = (fixW y).map (rhoM24 c).toMonoidHom := by
    ext w
    rw [Subgroup.mem_map]
    have happ : (rhoM24 c) ((rhoM24 c)⁻¹ w) = w := by
      rw [← MulAut.mul_apply, ← map_inv, ← map_mul, mul_inv_cancel, map_one]
      rfl
    constructor
    · intro hw
      refine ⟨(rhoM24 c)⁻¹ w, ?_, ?_⟩
      · refine (mem_fixW_conj c y ((rhoM24 c)⁻¹ w)).1 ?_
        rwa [happ]
      · exact happ
    · rintro ⟨w', hw', rfl⟩
      exact (mem_fixW_conj c y w').2 hw'
  rw [h]
  exact Subgroup.card_map_of_injective (K := fixW y) (f := (rhoM24 c).toMonoidHom)
    (rhoM24 c).injective

end CFSG.ASVolI.AppH.H157
