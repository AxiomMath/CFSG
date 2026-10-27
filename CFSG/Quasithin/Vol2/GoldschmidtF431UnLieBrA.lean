module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieDefs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnF48Tor
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.Un.OL

section Bridge

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (hf : 1 ≤ f)

include hF hf in
theorem brFD : UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

theorem brFD_bar (c : F) : (brFD hF hf).bar c = unitaryInvolution F 2 f c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

theorem miyamotoJ4_eq_antidiag : miyamotoJ4 F = antidiag 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, antidiag, Fin.rev]

theorem gramSU_eq_SU :
    gramSU (brFD hF hf) (miyamotoJ4 F) = SU (unitaryInvolution F 2 f) 4 := by
  refine Subgroup.ext fun g => ?_
  have hb : ((g : Matrix (Fin 4) (Fin 4) F).map (brFD hF hf).bar) =
      (g : Matrix (Fin 4) (Fin 4) F).map (unitaryInvolution F 2 f) := by
    ext i j
    simp only [Matrix.map_apply]
    exact brFD_bar hF hf _
  rw [mem_gramSU, mem_SU, hb, miyamotoJ4_eq_antidiag]
  exact and_comm

theorem brJ_mem : miyamotoJ4GL F ∈ gramSU (brFD hF hf) (miyamotoJ4 F) := by
  have hJ := miyamotoJ4_mul_self (K := F)
  refine ⟨?_, ?_⟩
  · show ((miyamotoJ4 F).map (brFD hF hf).bar)ᵀ * miyamotoJ4 F * miyamotoJ4 F = miyamotoJ4 F
    rw [miyamotoJ4_conjTranspose (brFD hF hf), hJ, Matrix.one_mul]
  · have h1 : (miyamotoJ4 F).det * (miyamotoJ4 F).det = 1 := by
      rw [← Matrix.det_mul, hJ, Matrix.det_one]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : ((miyamotoJ4 F).det - 1) * ((miyamotoJ4 F).det - 1) = 0 := by
      linear_combination h1 + (1 - (miyamotoJ4 F).det) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)

@[expose] def brEps : Xg (brFD hF hf) ≃* SU (unitaryInvolution F 2 f) 4 :=
  (MulAut.conj (⟨miyamotoJ4GL F, brJ_mem hF hf⟩ : Xg (brFD hF hf))).trans
    (MulEquiv.subgroupCongr (gramSU_eq_SU hF hf))

theorem coe_brEps (A : Xg (brFD hF hf)) :
    (((brEps hF hf A : SU (unitaryInvolution F 2 f) 4) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) =
      miyamotoJ4 F * ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * miyamotoJ4 F := rfl

theorem J4_mul_mul_J4_apply (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    (miyamotoJ4 F * M * miyamotoJ4 F) i j = M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct]

theorem brEq_of_sylow_le {G : Type*} [Group G] [Finite G] {P S : Subgroup G}
    (hP : IsSylowTwoOf P ⊤) (hPS : P ≤ S) (hS : IsPGroup 2 S) : P = S := by
  refine le_antisymm hPS ?_
  have h1 := Subgroup.relIndex_mul_relIndex P S ⊤ hPS le_top
  have h2 : ¬ 2 ∣ P.relIndex S := fun hd => hP.2.2 (by
    have e : P.relIndex ⊤ = (P.subgroupOf ⊤).index := rfl
    rw [← e, ← h1]
    exact Dvd.dvd.mul_right hd _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hS.index (P.subgroupOf S)
  have hn0 : n = 0 := by
    by_contra hne
    exact h2 (by rw [Subgroup.relIndex, hn]; exact dvd_pow_self 2 hne)
  rw [hn0, pow_zero, Subgroup.index_eq_one] at hn
  exact Subgroup.subgroupOf_eq_top.1 hn

theorem brUnU_entry_lt {y : SU (unitaryInvolution F 2 f) 4} (hy : y ∈ unU hF 4) {a b : Fin 4}
    (hab : b < a) : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) a b = 0 := by
  have h := idBelow_unU hF hy a b (by
    have : (b : ℕ) < a := hab
    simp only [lvl, one_mul]
    omega)
  rw [Matrix.one_apply_ne (ne_of_gt hab)] at h
  exact h

theorem brUnU_entry_diag {y : SU (unitaryInvolution F 2 f) 4} (hy : y ∈ unU hF 4) (a : Fin 4) :
    ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) a a = 1 := by
  have h := idBelow_unU hF hy a a (by simp [lvl])
  rw [Matrix.one_apply_eq] at h
  exact h

theorem brEps_map_Psy :
    (Psy (brFD hF hf)).map (brEps hF hf).toMonoidHom = unU hF 4 := by
  have hP2 : IsPGroup 2 ((Psy (brFD hF hf)).map (brEps hF hf).toMonoidHom) :=
    (isSylowTwoOf_Psy (brFD hF hf)).2.1.of_equiv
      ((Psy (brFD hF hf)).equivMapOfInjective _ (brEps hF hf).injective)
  refine (brEq_of_sylow_le (isSylowTwoOf_unU hF) (fun y hy => ?_) hP2).symm
  refine ⟨(brEps hF hf).symm y, ?_, by simp⟩
  set x := (brEps hF hf).symm y with hx
  have hJ := miyamotoJ4_mul_self (K := F)
  have hxy : ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      miyamotoJ4 F * ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * miyamotoJ4 F := by
    have h1 := coe_brEps hF hf x
    rw [hx, (brEps hF hf).apply_symm_apply] at h1
    rw [h1]
    simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [Matrix.mul_assoc _ _ (miyamotoJ4 F), hJ, Matrix.mul_one]
  have e : ∀ i j, ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i j =
      ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (Fin.rev i) (Fin.rev j) := fun i j => by
    rw [hxy, J4_mul_mul_J4_apply]
  have hmem := mem_P_of_lowerUnitriangular (brFD hF hf) (x : Xg (brFD hF hf)).2
    (by rw [e]; exact brUnU_entry_diag hF hy 3) (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_diag hF hy 2) (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_diag hF hy 1) (by rw [e]; exact brUnU_entry_lt hF hy (by decide))
    (by rw [e]; exact brUnU_entry_diag hF hy 0)
  exact Subgroup.mem_subgroupOf.2 hmem.1

theorem brEps_z1X : brEps hF hf (z1X (brFD hF hf)) = zUn hF := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_brEps, coe_zUn, coe_z1X, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoX, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

theorem brEps_z2X : brEps hF hf (z2X (brFD hF hf)) = tUn hF := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_brEps, coe_tUn, coe_z2X, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoX, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

end Bridge

end CFSG.Quasithin.H13.F431.Un
