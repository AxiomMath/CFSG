module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieBrA
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoF
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYamC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.Un.OL CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 Matrix

section Br

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  (hf : 1 ≤ f) (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)]

@[expose] def wUn (_hF : Nat.card F = (2 ^ f) ^ 2) : SU (unitaryInvolution F 2 f) 4 :=
  longRootHom (unitaryInvolution F 2 f) (i := (1 : Fin 4)) (by decide)
    (Multiplicative.ofAdd
      ⟨1, show (1 : F) + unitaryInvolution F 2 f 1 = 0 by
        rw [map_one]; exact CharTwo.add_self_eq_zero 1⟩)

theorem coe_wUn : (((wUn hF : SU (unitaryInvolution F 2 f) 4) : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = 1 + single 1 2 1 := rfl

theorem wUn_mem_unOct : wUn hF ∈ unOct hF 4 :=
  longRootHom_mem (unitaryInvolution_involutive hF) (by decide) (by decide) _

theorem wUn_ne_one : wUn hF ≠ 1 := by
  intro h
  have := congrArg (fun x : SU (unitaryInvolution F 2 f) 4 =>
    ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 2) h
  simp [coe_wUn] at this

theorem brEps_bX : brEps hF hf (bX (brFD hF hf)) = wUn hF := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_brEps, coe_wUn, coe_bX, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoX, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

theorem eq_one_of_mem_root_four_of_mem_Uplus_false {x : SU (unitaryInvolution F 2 f) 4}
    (hx4 : x ∈ unOct hF 4) (hx : x ∈ BN.Uplus (unSystem hF ζ) false) : x = 1 := by
  have hx' : x ∈ chainProd (unOct hF) [1, 2, 3] := by
    have h1 : x ∈ ((BN.Uplus (unSystem hF ζ) false : Subgroup _) : Set _) := hx
    rw [BN.coe_Uplus_false] at h1
    exact h1
  rw [chainProd_cons, chainProd_cons, chainProd_singleton] at hx'
  obtain ⟨a, ha, y, hy, hay⟩ := Set.mem_mul.1 hx'
  obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_mul.1 hy
  replace ha : a ∈ unOct hF 1 := ha
  replace hb : b ∈ unOct hF 2 := hb
  replace hc : c ∈ unOct hF 3 := hc
  have hl : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
  have key := (unOctagon hF).unique
    (fun k => if k = 1 then a else if k = 2 then b else if k = 3 then c else 1)
    (fun k => if k = 4 then x else 1) ?_ ?_ ?_ 4 (by rw [hl]; simp)
  · simpa using key.symm
  · intro k hk
    rw [hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [ha, hb, hc, one_mem]
  · intro k hk
    rw [hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [hx4, one_mem]
  · rw [hl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    norm_num
    rw [← hay, ← hbc]

theorem brSimple : IsSimpleGroup (Xg (brFD hF hf)) :=
  (brEps hF hf).isSimpleGroup_congr.2 (isSimpleGroup_unSU hF)

theorem brEps_map_Ln :
    (Ln (brFD hF hf)).map (brEps hF hf).toMonoidHom = (unSystem hF ζ).P₁ := by
  have := brSimple hF hf
  rcases overgroup_Xg hF ζ (brFD hF hf) (brEps hF hf) (brEps_map_Psy hF hf)
    (normalizer_Psy_le_Ln _) (Ln_ne_top _) (Ln_ne_normalizer _) with e | e
  · rw [e]
    exact BN.map_symm_map_equiv (brEps hF hf) _
  · exfalso
    have e2 : (Ln (brFD hF hf)).map (brEps hF hf).toMonoidHom = (unSystem hF ζ).P₂ := by
      rw [e]
      exact BN.map_symm_map_equiv (brEps hF hf) _
    have h3 : (A1X (brFD hF hf)).map (brEps hF hf).toMonoidHom =
        BN.Uplus (unSystem hF ζ) false := by
      rw [← pCoreOf_Ln (brFD hF hf), ← LieType.BorelTits.pCoreOf_map_mulEquiv 2 (brEps hF hf), e2]
      exact BN.Q_eq_Uplus (unSystem hF ζ) (isSylowTwoOf_unU hF) false
    have h4 : brEps hF hf (bX (brFD hF hf)) ∈ BN.Uplus (unSystem hF ζ) false := by
      rw [← h3]
      exact Subgroup.mem_map_of_mem _ (bX_mem_A1X _)
    rw [brEps_bX] at h4
    exact wUn_ne_one hF (eq_one_of_mem_root_four_of_mem_Uplus_false hF ζ (wUn_mem_unOct hF) h4)

theorem brEps_map_Pt :
    (Pt (brFD hF hf)).map (brEps hF hf).toMonoidHom = (unSystem hF ζ).P₂ := by
  have := brSimple hF hf
  rcases overgroup_Xg hF ζ (brFD hF hf) (brEps hF hf) (brEps_map_Psy hF hf)
    (normalizer_Psy_le_Pt _) (Pt_ne_top _) (Pt_ne_normalizer _) with e | e
  · exfalso
    apply Pt_ne_Ln (brFD hF hf)
    have hinj : Function.Injective (brEps hF hf).toMonoidHom := (brEps hF hf).injective
    apply Subgroup.map_injective hinj
    rw [brEps_map_Ln hF hf ζ, e]
    exact BN.map_symm_map_equiv (brEps hF hf) _
  · rw [e]
    exact BN.map_symm_map_equiv (brEps hF hf) _

theorem brEps_map_A1X :
    (A1X (brFD hF hf)).map (brEps hF hf).toMonoidHom = v4Un hF ζ := by
  rw [← pCoreOf_Ln (brFD hF hf), ← LieType.BorelTits.pCoreOf_map_mulEquiv 2 (brEps hF hf),
    brEps_map_Ln hF hf ζ]
  exact BN.Q_eq_Uplus (unSystem hF ζ) (isSylowTwoOf_unU hF) true

end Br

end CFSG.Quasithin.H13.F431.Un
