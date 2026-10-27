module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K]

theorem spMat_torusHom (t : Fin 2 → Kˣ) :
    spMat (torusHom t : StatedSp 2 K) =
      diagonal (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) :=
  coe_torusHom t

theorem torusHom_mem_Q2 (j : Fin 2) (t : Fin 2 → Kˣ) : (torusHom t : StatedSp 2 K) ∈ Q2 K j := by
  have hj := j.isLt
  rw [Q2_eq]
  exact borelSubgroup_le_flagStabilizer (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega) (torus_le_borelSubgroup ⟨t, rfl⟩)

theorem blkQ_torusHom_zero (t : Fin 2 → Kˣ) :
    blkQ 0 ⟨torusHom t, torusHom_mem_Q2 0 t⟩ = !![(t 1 : K), 0; 0, (((t 1)⁻¹ : Kˣ) : K)] := by
  rw [blkQ_apply, spMat_torusHom]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]

theorem blkQ_torusHom_one (t : Fin 2 → Kˣ) :
    blkQ 1 ⟨torusHom t, torusHom_mem_Q2 1 t⟩ = !![(t 0 : K), 0; 0, (t 1 : K)] := by
  rw [blkQ_apply, spMat_torusHom]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]

variable [Finite K]

theorem torusHom_mem_N0_iff (hK4 : ∃ s : Finset K, s.card = 4) (t : Fin 2 → Kˣ) :
    (torusHom t : StatedSp 2 K) ∈ perfectCore (Q2 K 0) ↔ t 0 = 1 := by
  constructor
  · intro h
    have h1 := spMat_inl_zero_eq_one_of_perfectCore h
    rw [spMat_torusHom] at h1
    exact Units.ext (by simpa using h1)
  · intro h
    have e : (torusHom t : StatedSp 2 K) = spLevi 0 (sl2Diag (t 1)) := by
      have h0 : (spLevi (K := K) 0) = lam 1 := by simp [spLevi]
      rw [h0, lam_sl2Diag]
      congr 1
      funext i
      fin_cases i
      · simp [h]
      · simp
    rw [e]
    exact spLevi_mem_perfectCore hK4 0 _

theorem torusHom_mem_N1_iff (hK4 : ∃ s : Finset K, s.card = 4) (t : Fin 2 → Kˣ) :
    (torusHom t : StatedSp 2 K) ∈ perfectCore (Q2 K 1) ↔ t 0 * t 1 = 1 := by
  constructor
  · intro h
    have h1 := (blkN 1 ⟨_, h⟩).2
    rw [blkN_coe, ← blkQ_apply 1 ⟨torusHom t, torusHom_mem_Q2 1 t⟩, blkQ_torusHom_one,
      Matrix.det_fin_two_of] at h1
    apply Units.ext
    simpa using h1
  · intro h
    have h1 : t 1 = (t 0)⁻¹ := eq_inv_of_mul_eq_one_right h
    have e : (torusHom t : StatedSp 2 K) = spLevi 1 (sl2Diag (t 0)) := by
      apply statedSp_ext
      change spMat (torusHom t) = spMat (spLevi 1 (sl2Diag (t 0)))
      rw [spMat_leviSp_one, spMat_torusHom]
      ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k <;>
        simp [h1, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [e]
    exact spLevi_mem_perfectCore hK4 1 _

variable [CharP K 2]

theorem isPGroup_ker_blkN (j : Fin 2) : IsPGroup 2 (blkN (K := K) j).ker := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := K) 2 2
  intro x
  have hxU := blkN_ker (K := K) j (x : ↥(perfectCore (Q2 K j))) (MonoidHom.mem_ker.mp x.2)
  obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨_, hP₀ ▸ hxU⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem pCoreOf_N_eq (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    pCoreOf 2 (perfectCore (Q2 K j)) = ((blkN j).ker).map (perfectCore (Q2 K j)).subtype := by
  have := sl2_isSimple (K := K) hK4
  rw [pCoreOf,
    pCore_two_eq_ker (sl2_nonabelian hK4) (blkN j) (blkN_surjective hK4 j) (isPGroup_ker_blkN j)]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
