module

public import CFSG.Milestones.ASVolI.F437U.Gen
public import CFSG.Milestones.ASVolI.F431.BF436U4
public import CFSG.Milestones.ASVolI.F429.One
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F437.Deg

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

section U4Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF437U_U4_fix_eq : burnsideF437U_fix (frob h).toMonoidHom = frobFix h := by
  ext g
  exact Iff.rfl

theorem burnsideF437U_U4_sadm : SAdm h 0 1 0 := by
  show (0 : K) + h.bar 0 = h.bar 0 * 1 + h.bar 1 * 0
  simp

@[expose] noncomputable def burnsideF437U_U4_N : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def burnsideF437U_U4_u : hypSU h 2 0 :=
  sElt h (burnsideF437U_U4_sadm h) * levHom h (burnsideF437U_U4_N h)

theorem burnsideF437U_U4_coe_u (a b : Ix) :
    (((burnsideF437U_U4_u h : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a b =
      if a = b ∨ (a = ie1 ∧ b = ie2) ∨ (a = ie2 ∧ b = if2) ∨ (a = ie1 ∧ b = if2) ∨
        (a = if2 ∧ b = if1) then 1 else 0 := by
  rw [burnsideF437U_U4_u, coe_mul_hypSU, coe_sElt, coe_levHom, mul_apply, sum_ix]
  rcases ix_cases a with rfl | rfl | rfl | rfl <;> rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, levMat_apply, slMat, one_apply, ie1, ie2, if1, if2, burnsideF437U_U4_N]

theorem burnsideF437U_U4_frob_u :
    (frob h).toMonoidHom (burnsideF437U_U4_u h) = burnsideF437U_U4_u h := by
  show frobElt h (burnsideF437U_U4_u h) = burnsideF437U_U4_u h
  apply hypSU_ext h
  rw [coe_frobElt]
  ext a b
  rw [map_apply, burnsideF437U_U4_coe_u]
  split_ifs <;> simp

theorem burnsideF437U_U4_u_mem : burnsideF437U_U4_u h ∈ pCoreOf 2 (parP h ⊓ parP2 h) := by
  rw [burnsideF4gU4Inv_pCore_borel, mem_hypUnitriangular]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [burnsideF437U_U4_coe_u]
    rcases ix_cases a with rfl | rfl | rfl | rfl <;>
      rcases ix_cases b with rfl | rfl | rfl | rfl <;> simp_all
  · rw [burnsideF437U_U4_coe_u, if_pos (Or.inl rfl)]

theorem burnsideF437U_U4_reg (g : hypSU h 2 0)
    (hg : g * burnsideF437U_U4_u h * g⁻¹ ∈ pCoreOf 2 (parP h ⊓ parP2 h)) :
    g ∈ parP h ⊓ parP2 h := by
  rw [burnsideF4gU4Inv_pCore_borel, mem_hypUnitriangular] at hg
  obtain ⟨hT, hD⟩ := hg
  set x := g * burnsideF437U_U4_u h * g⁻¹ with hx
  have hux : burnsideF437U_U4_u h * g⁻¹ = g⁻¹ * x := by rw [hx]; group
  have hM : (((burnsideF437U_U4_u h : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) *
      ((g⁻¹ : hypSU h 2 0) : GL Ix K) =
      (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) * ((x : GL Ix K) : Matrix Ix Ix K) := by
    rw [← coe_mul_hypSU, ← coe_mul_hypSU, hux]
  set Y := (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) with hY
  set Xm := ((x : GL Ix K) : Matrix Ix Ix K) with hXm
  have x21 : Xm ie2 ie1 = 0 := hT (by simp)
  have x31 : Xm if1 ie1 = 0 := hT (by simp)
  have x41 : Xm if2 ie1 = 0 := hT (by simp)
  have x32 : Xm if1 ie2 = 0 := hT (by simp)
  have x42 : Xm if2 ie2 = 0 := hT (by simp)
  have x11 : Xm ie1 ie1 = 1 := hD ie1
  have x22 : Xm ie2 ie2 = 1 := hD ie2
  have e := fun a b => congrFun (congrFun hM a) b
  have c11 := e ie1 ie1
  have c21 := e ie2 ie1
  have c41 := e if2 ie1
  have c22 := e ie2 ie2
  have c42 := e if2 ie2
  simp only [mul_apply, sum_ix, burnsideF437U_U4_coe_u] at c11 c21 c41 c22 c42
  simp only [x21, x31, x41, x32, x42, x11, x22] at c11 c21 c41 c22 c42
  simp at c11 c21 c41 c22 c42
  have y41 : Y if2 ie1 = 0 := by linear_combination c21
  have y31 : Y if1 ie1 = 0 := by linear_combination c41
  have y21 : Y ie2 ie1 = 0 := by linear_combination c11 - c21
  have y42 : Y if2 ie2 = 0 := by linear_combination c22 + Xm ie1 ie2 * y21
  have y32 : Y if1 ie2 = 0 := by linear_combination c42 + Xm ie1 ie2 * y41
  have hyP : g⁻¹ ∈ parP h := by
    rw [mem_parP_iff]
    intro a ha
    rcases ix_cases a with rfl | rfl | rfl | rfl
    · exact absurd rfl ha
    · exact y21
    · exact y31
    · exact y41
  have hyP2 : g⁻¹ ∈ parP2 h := (mem_parP2_iff h _).mpr ⟨y31, y32, y41, y42⟩
  have := (parP h ⊓ parP2 h).inv_mem (Subgroup.mem_inf.mpr ⟨hyP, hyP2⟩)
  rwa [inv_inv] at this

theorem burnsideF437U_U4_sylow [Finite K] :
    IsSylowOf 2 (pCoreOf 2 (parP h ⊓ parP2 h)) (⊤ : Subgroup (hypSU h 2 0)) := by
  rw [burnsideF4gU4Inv_pCore_borel]
  have hS := isSylowTwoOf_hypUnitriangular h
  exact ⟨hS.1, hS.2.1, hS.2.2⟩

theorem burnsideF437U_sp_isLieParabolics (F : Type) [Field F] [Finite F] [CharP F 2] :
    IsLieParabolics 2 (⊤ : Subgroup (StatedSp 2 F))
      (CFSG.QuasithinUnique.Setup.X7a.Q2 F 0 ⊓ CFSG.QuasithinUnique.Setup.X7a.Q2 F 1)
      (CFSG.QuasithinUnique.Setup.X7a.Q2 F 0) (CFSG.QuasithinUnique.Setup.X7a.Q2 F 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (SymplecticFlag.proj 2 F) := by
    rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj]
    exact CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  refine burnsideF48_isLieParabolics_of_map (SymplecticFlag.proj 2 F) hinj ?_
  have hsurj : (⊤ : Subgroup (StatedSp 2 F)).map (SymplecticFlag.proj 2 F) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact SymplecticHigher.proj_surjective (r := 2) (K := F)
  have hQ0 : CFSG.QuasithinUnique.Setup.X7a.Q2 F 0 =
      SymplecticFlag.stabilizer 2 F (SymplecticFlag.flag 2 F 1) := rfl
  have hQ1 : CFSG.QuasithinUnique.Setup.X7a.Q2 F 1 =
      SymplecticFlag.stabilizer 2 F (SymplecticFlag.flag 2 F 2) := rfl
  have hB : (CFSG.QuasithinUnique.Setup.X7a.Q2 F 0 ⊓
      CFSG.QuasithinUnique.Setup.X7a.Q2 F 1).map (SymplecticFlag.proj 2 F) =
        SymplecticFlag.projBorel 2 F := by
    rw [hQ0, hQ1, burnsideF4h_cl_sp_stab_inf]
    rfl
  rw [hsurj, hB]
  exact burnsideF4h_cl_sp_isLieParabolics F 2

theorem burnsideF437U_U4_par [Finite K] :
    IsLieParabolics 2 (burnsideF437U_fix (frob h).toMonoidHom)
      (burnsideF437U_fix (frob h).toMonoidHom ⊓ (parP h ⊓ parP2 h))
      (burnsideF437U_fix (frob h).toMonoidHom ⊓ parP h)
      (burnsideF437U_fix (frob h).toMonoidHom ⊓ parP2 h) := by
  haveI := charP_fixedField h
  haveI : Finite h.fixedField := Subtype.finite
  have hmap := burnsideF48_isLieParabolics_map (spIncl h) (spIncl_injective h)
    (burnsideF437U_sp_isLieParabolics h.fixedField)
  rw [Subgroup.map_inf_eq _ _ _ (spIncl_injective h), map_spIncl_Q2,
    burnsideF4m_map_spIncl_Q2_one, ← MonoidHom.range_eq_map, range_spIncl] at hmap
  rw [burnsideF437U_U4_fix_eq]
  have e1 : frobFix h ⊓ (parP h ⊓ parP2 h) = parP h ⊓ frobFix h ⊓ (parP2 h ⊓ frobFix h) := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [e1, inf_comm (frobFix h) (parP h), inf_comm (frobFix h) (parP2 h)]
  exact hmap

theorem burnsideF437U_U4_ctr [Finite K] (z : hypSU h 2 0)
    (hz : z ∈ burnsideF437U_fix (frob h).toMonoidHom)
    (hc : ∀ y ∈ burnsideF437U_fix (frob h).toMonoidHom, z * y = y * z) : z = 1 := by
  haveI := charP_fixedField h
  haveI : Finite h.fixedField := Subtype.finite
  rw [burnsideF437U_U4_fix_eq, ← range_spIncl] at hz
  obtain ⟨A, rfl⟩ := hz
  have hA : A ∈ Subgroup.center (StatedSp 2 h.fixedField) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have := hc (spIncl h B) (by rw [burnsideF437U_U4_fix_eq, ← range_spIncl]; exact ⟨B, rfl⟩)
    rw [← map_mul, ← map_mul] at this
    exact (spIncl_injective h this).symm
  rw [CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two,
    Subgroup.mem_bot] at hA
  rw [hA, map_one]

end U4Model

section U4Main

theorem burnsideF437U_fixedInputDeg_U4 : burnsideF437_FixedInputDeg .U4 1 := by
  intro E _ Gp M₁ M₂ hyp fb hinv hFG
  haveI := hyp.finite
  haveI := hyp.normal
  have hfield : ¬ hyp.toHypF_4_4g.chart.IsFieldInv fb := by
    rintro ⟨-, -, sd, hsd, hdeg, -⟩
    omega
  have hgr : hyp.toHypF_4_4g.chart.IsGraphInv fb := hFG.resolve_left hfield
  have hidx : Gp.index = 2 := by
    rcases burnsideF429_F429_one_Un_two (Or.inl rfl) hyp with h | h
    · exact absurd (h ▸ Subgroup.mem_top fb) hinv.not_mem
    · exact h.1
  obtain ⟨K, fK, h, Φ, a, h1, h2, hs⟩ := burnsideF4m_u4_exists_frob_conj hyp.toHypF_4_4g hgr
  haveI : Finite K := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set a' : hypSU h 2 0 := Φ.symm a with ha'
  have hφa : φ a' = (a : E) := by simp [hφdef, ha']
  have hact : ∀ x, fb * φ x * fb⁻¹ = φ (a' * (frob h).toMonoidHom (a'⁻¹ * x * a') * a'⁻¹) := by
    intro x
    have e2 : ((Φ (a'⁻¹ * x * a') : ↥Gp) : E) = (a : E)⁻¹ * φ x * a := by
      rw [← hφa]
      simp [hφdef, map_mul, map_inv]
    rw [map_mul, map_mul, map_inv, hφa]
    show fb * φ x * fb⁻¹ = (a : E) * ((Φ (frobElt h (a'⁻¹ * x * a')) : ↥Gp) : E) * (a : E)⁻¹
    rw [← hs, e2]
    group
  obtain ⟨hpar, huniq, hrig⟩ := burnsideF437U_fixedFacts_of_model φ hφ hrange
    (frob h).toMonoidHom h1 h2 (burnsideF437U_U4_frob_u h) (burnsideF437U_U4_u_mem h)
    (burnsideF437U_U4_reg h) (burnsideF437U_U4_sylow h) (burnsideF437U_U4_par h)
    (burnsideF437U_U4_ctr h) hidx hinv a' hact
  exact ⟨fun hf => absurd hf hfield, hpar, huniq, hrig⟩

end U4Main

end CFSG.ASVolI
