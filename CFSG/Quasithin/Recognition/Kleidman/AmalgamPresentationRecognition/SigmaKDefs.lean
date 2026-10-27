module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SigmaCheckData

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM CFSG.Quasithin.J2Cz.F2 Equiv

section Shadow

theorem actC_x (π : Perm (Fin 5)) (j : Fin 4) : shAct π (x j.succ) = x (π j.succ) := by
  fin_cases j <;> simp [shAct, liftT, x, pw]

theorem act_eq (l : L0) (p : QM) :
    (L0.subtype l) p = shAct (linePermHom (l : MulAut QM)) p := by
  have h : (L0.subtype l).toMonoidHom =
      (liftRel_perm (linePerm (l : MulAut QM))).liftHom := by
    apply hom_ext
    · exact aut_z _
    · intro j
      show (l : MulAut QM) (x j.succ) = _
      rw [l.2 j.succ, (liftRel_perm _).liftHom_apply]
      exact (actC_x _ j).symm
  exact DFunLike.congr_fun h p

noncomputable def enc (P : Model) : ShC := (P.left, linePermHom (P.right : MulAut QM))

theorem enc_mul (a b : Model) : enc (a * b) = shMul (enc a) (enc b) := by
  simp only [enc, shMul]
  refine Prod.ext ?_ ?_
  · show (a * b).left = _
    rw [SemidirectProduct.mul_left]
    simp only
    rw [act_eq]
  · show linePermHom ((a * b).right : MulAut QM) = _
    rw [SemidirectProduct.mul_right]
    exact map_mul linePermHom _ _

theorem enc_one : enc 1 = shOne := by
  simp only [enc, shOne]
  refine Prod.ext rfl ?_
  show linePermHom ((1 : Model).right : MulAut QM) = 1
  simp

theorem enc_inv (a : Model) : enc a⁻¹ = shInv (enc a) := by
  simp only [enc, shInv]
  refine Prod.ext ?_ ?_
  · rw [SemidirectProduct.inv_left]
    rw [act_eq]
    simp only [Subgroup.coe_inv]
    exact congrArg (fun π => shAct π a.left⁻¹) (map_inv linePermHom (a.right : MulAut QM))
  · simp

theorem enc_injective : Function.Injective enc := by
  intro a b h
  simp only [enc, Prod.mk.injEq] at h
  apply SemidirectProduct.ext h.1
  apply Subtype.ext
  apply aut_ext
  intro j
  rw [(a.right).2, (b.right).2]
  exact congrArg (fun π => x (π j.succ)) h.2

theorem lp_aL : linePermHom (aL : MulAut QM) = pa := linePerm_phiA

theorem lp_bL : linePermHom (bL : MulAut QM) = pb := linePerm_phiB

theorem enc_modelTuple (k : Fin 6) : enc (modelTuple k) = shTuple k := by
  fin_cases k <;> simp [enc, modelTuple, shTuple, map_mul, map_inv, lp_aL, lp_bL]

theorem mem_allQ (q : QM) : q ∈ shAllQ := by
  revert q
  decide +kernel

theorem enc_mem_allC (P : Model) : enc P ∈ shAll := by
  have hs : Equiv.Perm.sign (linePerm (P.right : MulAut QM)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (linePerm_mem_alternatingGroup P.right.2)
  obtain ⟨w, hw, hwe⟩ := a5words_spec _ hs
  unfold shAll
  rw [List.mem_flatMap]
  refine ⟨P.left, mem_allQ _, ?_⟩
  rw [List.mem_map]
  exact ⟨w, hw, by simp only [enc]; rw [hwe]; rfl⟩

end Shadow

section Forced

@[expose] noncomputable def elY : Model := modelTuple 0

@[expose] noncomputable def elX : Model := modelTuple 2

@[expose] noncomputable def elZ : Model := modelTuple 3

@[expose] noncomputable def elU : Model := (modelTuple 4)⁻¹ * modelTuple 1

@[expose] noncomputable def elK : Model := modelTuple 4 * modelTuple 4

@[expose] noncomputable def elT : Model := modelTuple 3 * modelTuple 1 * (modelTuple 4)⁻¹

@[expose] noncomputable def elA : Model := elY⁻¹ * elX

@[expose] noncomputable def elG : Fin 5 → Model := ![elY, elX, elZ, elU, elK]

@[expose] noncomputable def KK : Subgroup Model := Subgroup.centralizer ({elX, elZ} : Set Model)

theorem mem_KK {P : Model} : P ∈ KK ↔ elX * P = P * elX ∧ elZ * P = P * elZ := by
  unfold KK
  rw [Subgroup.mem_centralizer_iff]
  simp

theorem enc_elY : enc elY = shY := enc_modelTuple 0

theorem enc_elX : enc elX = shX := enc_modelTuple 2

theorem enc_elZ : enc elZ = shZ := enc_modelTuple 3

theorem enc_elU : enc elU = shU := by
  simp [elU, shU, enc_mul, enc_inv, enc_modelTuple]

theorem enc_elK : enc elK = shKgen := by
  simp [elK, shKgen, enc_mul, enc_modelTuple]

theorem enc_elT : enc elT = shT := by
  simp [elT, shT, shZ, enc_mul, enc_inv, enc_modelTuple]

theorem enc_elA : enc elA = shA := by
  simp [elA, shA, enc_mul, enc_inv, enc_elX, enc_elY]

theorem enc_elG (j : Fin 5) : enc (elG j) = shGen j := by
  fin_cases j <;> simp [elG, shGen, enc_elY, enc_elX, enc_elZ, enc_elU, enc_elK]

theorem mem_KK_iff_enc {P : Model} : P ∈ KK ↔
    shMul shX (enc P) = shMul (enc P) shX ∧ shMul shZ (enc P) = shMul (enc P) shZ := by
  rw [mem_KK, ← enc_injective.eq_iff, ← enc_injective.eq_iff (a := elZ * P), enc_mul, enc_mul,
    enc_mul, enc_mul, enc_elX, enc_elZ]

theorem enc_mem_shK {P : Model} (hP : P ∈ KK) : enc P ∈ shK := by
  unfold shK
  rw [List.mem_filter]
  refine ⟨enc_mem_allC P, ?_⟩
  obtain ⟨h1, h2⟩ := mem_KK_iff_enc.1 hP
  simp [h1, h2]

theorem elG_mem (j : Fin 5) : elG j ∈ KK := by
  rw [mem_KK_iff_enc, enc_elG]
  revert j
  decide +kernel

@[expose] noncomputable def gK (j : Fin 5) : KK := ⟨elG j, elG_mem j⟩

@[expose] noncomputable def evalK (g : Fin 5 → KK) (w : List (Fin 5 × Bool)) : KK :=
  (w.map fun a => cond a.2 (g a.1) (g a.1)⁻¹).prod

theorem enc_evalK (g : Fin 5 → KK) (w : List (Fin 5 × Bool)) :
    enc ((evalK g w : KK) : Model) = shEval (fun j => enc (g j)) w := by
  induction w with
  | nil => simp [evalK, shEval, enc_one]
  | cons a w ih =>
    have h : evalK g (a :: w) = cond a.2 (g a.1) (g a.1)⁻¹ * evalK g w := by
      simp [evalK]
    rw [h]
    simp only [shEval] at ih ⊢
    rw [List.foldr_cons, ← ih, Subgroup.coe_mul, enc_mul]
    cases a.2 <;> simp [enc_inv]

theorem map_evalK (σ : KK →* KK) (g : Fin 5 → KK) (w : List (Fin 5 × Bool)) :
    σ (evalK g w) = evalK (fun j => σ (g j)) w := by
  unfold evalK
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨j, b⟩ _
  cases b <;> simp

end Forced

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
