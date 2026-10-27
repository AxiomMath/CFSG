module

public import Certificates.Certificate7186
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.Quasithin.H13.NQCatA314ASL

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Fischer CFSG.Open CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat PermLat

@[expose] def act4 (g : SpecialLinearGroup (Fin 3) F4) (v : Fin 2 → F4) : Fin 2 → F4 :=
  ![((g : Matrix (Fin 3) (Fin 3) F4).mulVec ![v 0, v 1, 1]) 0,
    ((g : Matrix (Fin 3) (Fin 3) F4).mulVec ![v 0, v 1, 1]) 1]

theorem mulVec_ext4 {g : SpecialLinearGroup (Fin 3) F4} (hg : g ∈ K4) (v : Fin 2 → F4) :
    (g : Matrix (Fin 3) (Fin 3) F4).mulVec ![v 0, v 1, 1] = ![act4 g v 0, act4 g v 1, 1] := by
  obtain ⟨g1, g2, g3⟩ := hg
  ext i
  fin_cases i
  · rfl
  · rfl
  · simp [mulVec, dotProduct, Fin.sum_univ_three, g1, g2, g3]

theorem act4_mul {g h : SpecialLinearGroup (Fin 3) F4} (hh : h ∈ K4) (v : Fin 2 → F4) :
    act4 (g * h) v = act4 g (act4 h v) := by
  have e : ((g * h : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).mulVec
      ![v 0, v 1, 1] = (g : Matrix (Fin 3) (Fin 3) F4).mulVec
        ![act4 h v 0, act4 h v 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, mulVec_ext4 hh]
  ext i
  fin_cases i
  · show (((g * h : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).mulVec
      ![v 0, v 1, 1]) 0 = _
    rw [e]
    rfl
  · show (((g * h : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).mulVec
      ![v 0, v 1, 1]) 1 = _
    rw [e]
    rfl

theorem act4_one (v : Fin 2 → F4) : act4 1 v = v := by
  ext i
  fin_cases i <;> simp [act4]

@[expose] def actPerm4 (g : ↥K4) : Perm (Fin 2 → F4) where
  toFun := act4 g
  invFun := act4 (g⁻¹ : ↥K4)
  left_inv v := by
    rw [← act4_mul g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, act4_one]
  right_inv v := by
    rw [← act4_mul (g⁻¹ : ↥K4).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      act4_one]

@[expose] def vecEquiv16 : (Fin 2 → F4) ≃ Fin 16 where
  toFun v := ⟨(v 0).code.val + 4 * (v 1).code.val, by omega⟩
  invFun n := ![⟨⟨n.val % 4, by omega⟩⟩, ⟨⟨n.val / 4, by omega⟩⟩]
  left_inv v := by
    ext i
    fin_cases i
    · show (⟨⟨((v 0).code.val + 4 * (v 1).code.val) % 4, _⟩⟩ : F4) = v 0
      apply f4_ext
      ext
      show ((v 0).code.val + 4 * (v 1).code.val) % 4 = (v 0).code.val
      omega
    · show (⟨⟨((v 0).code.val + 4 * (v 1).code.val) / 4, _⟩⟩ : F4) = v 1
      apply f4_ext
      ext
      show ((v 0).code.val + 4 * (v 1).code.val) / 4 = (v 1).code.val
      omega
  right_inv n := by
    ext
    show n.val % 4 + 4 * (n.val / 4) = n.val
    omega

@[expose] def rho4 : ↥K4 →* Perm (Fin 16) where
  toFun g := vecEquiv16.permCongr (actPerm4 g)
  map_one' := by
    ext n
    simp [actPerm4, Equiv.permCongr_apply, act4_one]
  map_mul' g h := by
    refine Equiv.ext fun n => ?_
    show vecEquiv16 (act4 ((g * h : ↥K4) : SpecialLinearGroup (Fin 3) F4) (vecEquiv16.symm n)) =
      vecEquiv16 (act4 g (vecEquiv16.symm (vecEquiv16 (act4 h (vecEquiv16.symm n)))))
    rw [Equiv.symm_apply_apply, Subgroup.coe_mul, act4_mul h.2]

theorem rho4_injective : Function.Injective rho4 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hfix : ∀ v, act4 g v = v := by
    intro v
    have h1 := congrArg (fun p : Perm (Fin 16) => p (vecEquiv16 v)) hg
    simp only [rho4, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
      Equiv.symm_apply_apply, Perm.one_apply] at h1
    exact vecEquiv16.injective h1
  obtain ⟨g1, g2, g3⟩ := g.2
  have e00 := congrFun (hfix ![0, 0]) 0
  have e01 := congrFun (hfix ![0, 0]) 1
  have e10 := congrFun (hfix ![1, 0]) 0
  have e11 := congrFun (hfix ![1, 0]) 1
  have e20 := congrFun (hfix ![0, 1]) 0
  have e21 := congrFun (hfix ![0, 1]) 1
  simp [act4, mulVec, dotProduct, Fin.sum_univ_three] at e00 e01 e10 e11 e20 e21
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

@[expose] def k1M22 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    apply f4_ext
    decide⟩

@[expose] def k2M22 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![0, F4.ω, 0; ⟨3⟩, F4.ω, 1; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    apply f4_ext
    decide⟩

theorem k1M22_mem : k1M22 ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem k2M22_mem : k2M22 ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem rho4_gens :
    M22Asl.aslGens = [rho4 ⟨k1M22, k1M22_mem⟩, rho4 ⟨k2M22, k2M22_mem⟩] := by
  decide

theorem card_Tr4 : Nat.card Tr4 = 16 := by
  have hb : Function.Bijective (fun v : Fin 2 → F4 => (⟨tau4 v, tau4_mem v⟩ : ↥Tr4)) := by
    refine ⟨fun v w h => tau4_injective (congrArg Subtype.val h), fun t => ?_⟩
    obtain ⟨v, hv⟩ := mem_Tr4_iff.mp t.2
    exact ⟨v, Subtype.ext hv.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_fun, Nat.card_eq_fintype_card, F4.card,
    Nat.card_fin]
  norm_num

theorem card_K4 : Nat.card ↥K4 = 960 := by
  have h := Subgroup.card_ker_mul_card_of_surjective alpha4_surjective
  rw [ker_alpha4, card_sl2F4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tr4_le_K4).toEquiv,
    card_Tr4] at h
  omega

theorem closure_aslGens_le : Subgroup.closure {g | g ∈ M22Asl.aslGens} ≤ rho4.range := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [rho4_gens] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem k4_equiv_B0 :
    Nonempty (↥K4 ≃* ↥(Subgroup.closure {g | g ∈ p5Gens})) := by
  have hc : diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 16) → RN 16) 64
      p5Gens M22Asl.aslGens 960 960 = true := Certificates.certificate7186
  obtain ⟨hA, hB, V, hVn, -, -, ⟨e⟩⟩ := exists_ext_of_diagExt (rawIsEnc 22) (rawIsEnc 16) hc
  have hV : V = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [Nat.card_congr e.toEquiv, hA, hB] at h
    exact Subgroup.eq_bot_of_card_eq V (by omega)
  let e' : ↥(Subgroup.closure {g | g ∈ p5Gens}) ≃* ↥(Subgroup.closure {g | g ∈ M22Asl.aslGens}) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hV.symm)).trans e
  have hR : Subgroup.closure {g | g ∈ M22Asl.aslGens} = rho4.range :=
    Subgroup.eq_of_le_of_card_ge closure_aslGens_le (by
      rw [hB, ← Nat.card_congr (MonoidHom.ofInjective rho4_injective).toEquiv, card_K4])
  exact ⟨(MonoidHom.ofInjective rho4_injective).trans ((MulEquiv.subgroupCongr hR.symm).trans
    e'.symm)⟩

end CFSG.Quasithin.H13.NQCat.A314D
