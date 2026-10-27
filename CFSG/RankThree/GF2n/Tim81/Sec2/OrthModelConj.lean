module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelAbstract

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

private theorem hermAct_wMat_mul_uMat_11 (δ : F) (X : ↥(hermA l F)) :
    ((hermAct l (sig_sig hF) (wMat * uMat δ) X : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) 1 1 =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 +
        δ ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
          δ * (X : Matrix (Fin 2) (Fin 2) F) 1 0 +
            δ * δ ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have hcomp : hermAct l (sig_sig hF) (wMat * uMat δ) X =
      hermAct l (sig_sig hF) wMat (hermAct l (sig_sig hF) (uMat δ) X) := by
    have h := congrArg (fun f : AddMonoid.End ↥(hermA l F) => f X)
      (map_mul (hermAct l (sig_sig hF)) (wMat) (uMat δ))
    exact h
  rw [hcomp, hermAct_wMat l hF]
  exact hermAct_uMat_00 l (sig_sig hF) δ (X := X)

private theorem exists_mul_sig_eq' (hF : Fintype.card F = 2 ^ (2 * l))
    {e : F} (he : e ^ 2 ^ l = e) :
    ∃ ε : F, ε * ε ^ 2 ^ l = e := by
  by_cases he0 : e = 0
  · exact ⟨0, by simp [he0]⟩
  · obtain ⟨c, -, hc⟩ := exists_mul_sig_eq (hF := hF) he he0
    exact ⟨c, hc⟩

theorem eq_map_conj_upperSylow_of_forall_mem_iff {A : Subgroup SL(2, F)} {x : SL(2, F)}
    (hx : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperSylow) :
    A = upperSylow.map (MulAut.conj x).toMonoidHom := by
  ext a
  rw [CFSG.Timmesfeld.RankOne.mem_map_conj]
  exact hx a

theorem exists_hermRep_mem_commSub_upperSylow (X : ↥(hermA l F)) :
    ∃ g : SL(2, F), hermRep l hF g X ∈ commSub (hermRep l hF) upperSylow := by
  by_cases hd0 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  · refine ⟨1, ?_⟩
    rw [map_one, Module.End.one_apply, commSub_upperSylow]
    exact hd0
  · set a : F := (X : Matrix (Fin 2) (Fin 2) F) 0 0
    set b : F := (X : Matrix (Fin 2) (Fin 2) F) 0 1
    set d : F := (X : Matrix (Fin 2) (Fin 2) F) 1 1
    have ha : a ^ 2 ^ l = a := by
      have h := hermA_00 (a := l) X
      rwa [sig_apply] at h
    have hd : d ^ 2 ^ l = d := by
      have h := hermA_11 (a := l) X
      rwa [sig_apply] at h
    have hb10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = b ^ 2 ^ l := by
      rw [hermA_10 (a := l) X]
      rfl
    have hb01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = b := rfl
    have h00 : (X : Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl
    have h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = d := rfl
    have hdne : d ≠ 0 := hd0
    set e : F := (a * d + b * b ^ 2 ^ l) / d ^ 2 with hedef
    have he : e ^ 2 ^ l = e := by
      rw [hedef]
      rw [div_pow, add_pow_char_pow, mul_pow, mul_pow_fix (hF := hF) b, ha, hd]
      have hd2 : (d ^ 2) ^ 2 ^ l = d ^ 2 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hd]
      rw [hd2]
    obtain ⟨eps, heps⟩ := exists_mul_sig_eq' hF he
    set δ : F := eps + b / d with hδdef
    have hdσ : δ ^ 2 ^ l = eps ^ 2 ^ l + b ^ 2 ^ l / d := by
      rw [hδdef, add_pow_char_pow, div_pow, hd]
    refine ⟨wMat * uMat δ, ?_⟩
    rw [commSub_upperSylow]
    change ((hermRep l hF (wMat * uMat δ) X : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = 0
    rw [hermRep_apply, hermAct_wMat_mul_uMat_11 (hF := hF)]
    rw [h00, hb01, hb10, h11, hdσ, hδdef]
    have heps' : eps * eps ^ 2 ^ l = (a * d + b * b ^ 2 ^ l) / d ^ 2 := heps
    have heps'' : eps * eps ^ 2 ^ l * d ^ 2 = a * d + b * b ^ 2 ^ l := by
      rw [heps']
      field_simp [hdne]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    field_simp [hdne] at ⊢
    rw [mul_zero] at ⊢
    linear_combination heps'' +
      (d * eps ^ 2 ^ l * b + d * eps * b ^ 2 ^ l + a * d +
        2 * (b * b ^ 2 ^ l)) * h2

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

theorem IsOrthModule.exists_conj_mem_commSub (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) (w : W) :
    ∃ g : SL(2, F), ρ g w ∈ commSub ρ A := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth0
  have hs := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom :=
    eq_map_conj_upperSylow_of_forall_mem_iff hx
  obtain ⟨g0, hg0⟩ := exists_hermRep_mem_commSub_upperSylow (hF := hF) (β w)
  set g : SL(2, F) := (fieldAutEquiv j).symm (x * g0) with hgdef
  refine ⟨g, ?_⟩
  refine (commSub_fieldAut_mem (hF := hF) hβ A (ρ g w)).mpr ?_
  have hg : fieldAut F j g = x * g0 := by
    rw [hgdef, ← fieldAutEquiv_apply]
    exact (fieldAutEquiv j).apply_symm_apply (x * g0)
  rw [hβ, hg, hEq]
  rw [commSub_map_conj (hermRep l hF) x upperSylow]
  have hmap : hermAct l (sig_sig hF) (x * g0) (β w) =
      hermAct l (sig_sig hF) x (hermAct l (sig_sig hF) g0 (β w)) := by
    rw [map_mul]
    rfl
  rw [hmap]
  exact Submodule.mem_map_of_mem hg0

end CFSG.RankThree.GF2n.Tim81.Sec2
