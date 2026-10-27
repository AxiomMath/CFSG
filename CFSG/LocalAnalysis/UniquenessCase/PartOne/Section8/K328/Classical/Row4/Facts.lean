module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

private abbrev k328r4f_M : Matrix (Fin 2) (Fin 2) (ZMod 2) := rhoOmega (ZMod 2)

private def k328r4f_z : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 k328r4f_M k328r4f_M k328r4f_M,
    blockDiag3 (ZMod 2) 6 (k328r4f_M ^ 2) (k328r4f_M ^ 2) (k328r4f_M ^ 2),
    by decide +kernel, by decide +kernel⟩

private def k328r4f_t : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 k328r4f_M (k328r4f_M ^ 2) 1,
    blockDiag3 (ZMod 2) 6 (k328r4f_M ^ 2) k328r4f_M 1,
    by decide +kernel, by decide +kernel⟩

private def k328r4f_P : GL (Fin 6) (ZMod 2) :=
  ⟨Matrix.of fun i j => if i = j + 2 then 1 else 0,
    Matrix.of fun i j => if j = i + 2 then 1 else 0,
    by decide +kernel, by decide +kernel⟩

private def k328r4f_S : GL (Fin 6) (ZMod 2) :=
  ⟨Matrix.of fun i j => if i = ![2, 3, 0, 1, 4, 5] j then 1 else 0,
    Matrix.of fun i j => if i = ![2, 3, 0, 1, 4, 5] j then 1 else 0,
    by decide +kernel, by decide +kernel⟩

private def k328r4f_Dz : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 1 (k328r4f_M ^ 2) k328r4f_M,
    blockDiag3 (ZMod 2) 6 1 k328r4f_M (k328r4f_M ^ 2),
    by decide +kernel, by decide +kernel⟩

private def k328r4f_Dt : GL (Fin 6) (ZMod 2) :=
  ⟨blockDiag3 (ZMod 2) 6 1 k328r4f_M (k328r4f_M ^ 2),
    blockDiag3 (ZMod 2) 6 1 (k328r4f_M ^ 2) k328r4f_M,
    by decide +kernel, by decide +kernel⟩

private theorem k328r4f_z_pow : k328r4f_z ^ 3 = 1 := by decide +kernel

private theorem k328r4f_t_pow : k328r4f_t ^ 3 = 1 := by decide +kernel

private theorem k328r4f_z_ne : k328r4f_z ≠ 1 := by decide +kernel

private theorem k328r4f_t_ne : k328r4f_t ≠ 1 := by decide +kernel

private theorem k328r4f_t_ne_z : k328r4f_t ≠ k328r4f_z := by decide +kernel

private theorem k328r4f_t_ne_z_sq : k328r4f_t ≠ k328r4f_z ^ 2 := by decide +kernel

private theorem k328r4f_zt_comm : k328r4f_z * k328r4f_t = k328r4f_t * k328r4f_z := by
  decide +kernel

private theorem k328r4f_P_comm : k328r4f_z * k328r4f_P = k328r4f_P * k328r4f_z := by
  decide +kernel

private theorem k328r4f_S_comm : k328r4f_z * k328r4f_S = k328r4f_S * k328r4f_z := by
  decide +kernel

private theorem k328r4f_Dz_comm : k328r4f_z * k328r4f_Dz = k328r4f_Dz * k328r4f_z := by
  decide +kernel

private theorem k328r4f_Dt_comm : k328r4f_z * k328r4f_Dt = k328r4f_Dt * k328r4f_z := by
  decide +kernel

private theorem k328r4f_comm_z :
    k328r4f_P * k328r4f_Dz * k328r4f_P⁻¹ * k328r4f_Dz⁻¹ = k328r4f_z := by decide +kernel

private theorem k328r4f_comm_t :
    k328r4f_S * k328r4f_Dt * k328r4f_S⁻¹ * k328r4f_Dt⁻¹ = k328r4f_t := by decide +kernel

private theorem k328r4f_t_not_mem_zpowers : k328r4f_t ∉ Subgroup.zpowers k328r4f_z := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h3 : orderOf k328r4f_z = 3 := orderOf_eq_prime k328r4f_z_pow k328r4f_z_ne
  have hmod := zpow_mod_orderOf k328r4f_z k
  rw [h3, hk] at hmod
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h | h | h <;> rw [h] at hmod
  · exact k328r4f_t_ne (by simpa using hmod.symm)
  · exact k328r4f_t_ne_z (by simpa using hmod.symm)
  · exact k328r4f_t_ne_z_sq (by simpa [sq] using hmod.symm)

private theorem k328r4f_phi_inj {F : Type} [Field F] (ι : ZMod 2 →+* F) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 6) ι) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => ι.injective ?_)
  rw [← Matrix.GeneralLinearGroup.map_apply ι i j a, ← Matrix.GeneralLinearGroup.map_apply ι i j b,
    h]

private theorem k328r4f_map_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (A B C : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    ι.mapMatrix (blockDiag3 (ZMod 2) 6 A B C) =
      blockDiag3 F 6 (ι.mapMatrix A) (ι.mapMatrix B) (ι.mapMatrix C) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, blockDiag3, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply]

private theorem k328r4f_map_rho {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) : ι.mapMatrix (rhoOmega (ZMod 2)) = rhoOmega F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoOmega]

private theorem k328r4f_phi_z {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (z₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    Matrix.GeneralLinearGroup.map ι k328r4f_z = z₀ := by
  apply Units.ext
  rw [hz]
  show ι.mapMatrix (blockDiag3 (ZMod 2) 6 k328r4f_M k328r4f_M k328r4f_M) = _
  rw [k328r4f_map_blockDiag3, k328r4f_map_rho]

private theorem k328r4f_phi_t {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ι : ZMod 2 →+* F) (t₀ : GL (Fin 6) F)
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    Matrix.GeneralLinearGroup.map ι k328r4f_t = t₀ := by
  apply Units.ext
  rw [ht]
  show ι.mapMatrix (blockDiag3 (ZMod 2) 6 k328r4f_M (k328r4f_M ^ 2) 1) = _
  rw [k328r4f_map_blockDiag3, map_pow, map_one, k328r4f_map_rho]

theorem row4_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    FactsLeaf (StatedSL 6 F) z₀ t₀ := by
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have : CharP F 2 := charP_of_card_eq_prime hF
  let ι : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let φ : GL (Fin 6) (ZMod 2) →* GL (Fin 6) F := Matrix.GeneralLinearGroup.map ι
  have hφ : Function.Injective φ := k328r4f_phi_inj ι
  have hz' : φ k328r4f_z = z₀ := k328r4f_phi_z ι z₀ hz
  have ht' : φ k328r4f_t = t₀ := k328r4f_phi_t ι t₀ ht
  have hH : ∀ g : GL (Fin 6) F, g ∈ StatedSL 6 F := fun g => by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 6]
    trivial
  have hcent : ∀ g : GL (Fin 6) (ZMod 2), k328r4f_z * g = g * k328r4f_z →
      φ g ∈ StatedSL 6 F ⊓ Subgroup.centralizer {z₀} := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hH _, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hz', ← map_mul, ← map_mul, hg]
  have hcomm : ∀ a b c : GL (Fin 6) (ZMod 2), k328r4f_z * a = a * k328r4f_z →
      k328r4f_z * b = b * k328r4f_z → a * b * a⁻¹ * b⁻¹ = c →
      φ c ∈ stdComp (StatedSL 6 F) z₀ := by
    intro a b c ha hb hc
    have := Subgroup.commutator_mem_commutator (hcent a ha) (hcent b hb)
    rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hc] at this
    exact this
  refine ⟨hH z₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hcomm k328r4f_P k328r4f_Dz k328r4f_z k328r4f_P_comm k328r4f_Dz_comm k328r4f_comm_z
    rwa [hz'] at this
  · have := hcomm k328r4f_S k328r4f_Dt k328r4f_t k328r4f_S_comm k328r4f_Dt_comm k328r4f_comm_t
    rwa [ht'] at this
  · rw [← hz', orderOf_injective φ hφ k328r4f_z]
    exact orderOf_eq_prime k328r4f_z_pow k328r4f_z_ne
  · rw [← ht', orderOf_injective φ hφ k328r4f_t]
    exact orderOf_eq_prime k328r4f_t_pow k328r4f_t_ne
  · rw [← hz', ← ht', ← map_mul, ← map_mul, k328r4f_zt_comm]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply k328r4f_t_not_mem_zpowers
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hφ ?_⟩
    rw [map_zpow, hz', ht']
    exact hk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
