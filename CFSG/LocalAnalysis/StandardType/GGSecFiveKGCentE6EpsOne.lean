module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem theta_involutive_of_normalForm_one_E6
    {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Set (Fin Tag.E6.rank → Kˣ)} (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    (hF0 : famKernel F = ∅) {α : MulAut (adjointGroup .E6 K)} (h2 : ∃ k : ℕ, α ^ 2 ^ k = 1)
    {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K) {w : WeylGroup Tag.E6} {a : Fin Tag.E6.rank → Kˣ}
    (hα : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      h * canonicalRep (coxeterSystem .E6) K w * exactNormalAutGL .E6 K a 1 1 (x : ModGL .E6 K) *
        (h * canonicalRep (coxeterSystem .E6) K w)⁻¹)
    (hw : ∀ b ∈ F, canonicalRep (coxeterSystem .E6) K w *
        exactNormalAutGL .E6 K a 1 1 (rootDiagUnit .E6 b) *
          (canonicalRep (coxeterSystem .E6) K w)⁻¹ = rootDiagUnit .E6 b) :
    (∀ β, w • permLattice (exactPerm .E6 1) (w • permLattice (exactPerm .E6 1) β) = β) ∧
      ∀ b ∈ F, ∀ β, rootChar b (w • permLattice (exactPerm .E6 1) β) = rootChar b β := by
  obtain ⟨k, hk⟩ := h2
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨ω, hω, hωw⟩ := (coxeterSystem .E6).exists_isReduced w
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Equiv.Perm (Fin Tag.E6.rank), ρ = TwistTag.E6.perm := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ModGL .E6 K, P = diagramMap .E6 K := ⟨_, rfl⟩
  have hπ : exactPerm .E6 1 = ρ := by rw [hρ]; exact pow_one _
  have hρ2 : ∀ j, ρ.symm (ρ.symm j) = j := by rw [hρ]; decide
  have hρρ : ∀ v, permLattice ρ (permLattice ρ v) = v := fun v =>
    funext fun j => congrArg v (hρ2 j)
  have hρc : ∀ i j, Tag.E6.cartan (ρ i) (ρ j) = Tag.E6.cartan i j := by
    rw [hρ]
    exact TwistTag.E6.cartan_perm
  have hPd : ∀ b : Fin Tag.E6.rank → Kˣ,
      P * rootDiagUnit .E6 b * P⁻¹ = rootDiagUnit .E6 (fun i => b (ρ.symm i)) := fun b => by
    rw [hP, hρ]
    exact mul_inv_eq_of_eq_mul (diagramMap_mul_rootDiagUnit (t := .E6) b)
  have hPn : ∀ i, P * weylElt .E6 K i 1 * P⁻¹ = weylElt .E6 K (ρ i) 1 := fun i => by
    rw [hP, hρ]
    exact mul_inv_eq_of_eq_mul (diagramMap_mul_weylElt_one (t := .E6) (K := K) i)
  have hPP : P * P = 1 := by
    rw [hP]
    exact diagramMap_E6_mul_self
  have hψ : ∀ g : ModGL .E6 K, exactNormalAutGL .E6 K a 1 1 g =
      rootDiagUnit .E6 a * P * g * P⁻¹ * (rootDiagUnit .E6 a)⁻¹ := by
    intro g
    have hQ : exactQ .E6 K 1 = P := by rw [hP]; exact pow_one _
    have hσ : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [exactNormalAutGL_apply, hQ, hσ, show Units.map (entrywiseHom (RingHom.id K)) g = g from
      Units.ext (entrywise_id _)]
  rw [hπ]
  have hθχ : ∀ b ∈ F, ∀ β, rootChar b (w • permLattice ρ β) = rootChar b β := by
    intro b hb β
    have e : exactNormalAutGL .E6 K a 1 1 (rootDiagUnit .E6 b) =
        rootDiagUnit .E6 (fun i => b (ρ.symm i)) := by
      rw [hψ]
      calc _ = rootDiagUnit .E6 a * (P * rootDiagUnit .E6 b * P⁻¹) * (rootDiagUnit .E6 a)⁻¹ := by
            group
        _ = _ := by
          rw [hPd, ← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]
    have h1 := hw b hb
    rw [e] at h1
    rw [(rootDiagUnit_eq_conj_canonicalRep_iff b _ w).1 h1.symm, rootChar_permLattice]
    simp only [Equiv.symm_apply_apply]
  refine ⟨fun β => ?_, hθχ⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = w * (coxeterSystem .E6).wordProd (ω.map ρ) := ⟨_, rfl⟩
  have hθ2 : ∀ β, w₂ • β = w • permLattice ρ (w • permLattice ρ β) := fun β => by
    rw [hw₂, mul_smul]
    congr 1
    calc (coxeterSystem .E6).wordProd (ω.map ρ) • β
        = (ω.map ρ).foldr (reflect .E6) (permLattice ρ (permLattice ρ β)) := by
          rw [wordProd_smul, hρρ]
      _ = permLattice ρ (w • permLattice ρ β) := by
          rw [CFSG.RankThree.Chevalley.foldr_reflect_map_permLattice hρc, hωw, wordProd_smul]
  obtain ⟨g, hg⟩ : ∃ g : ModGL .E6 K, g = rootDiagUnit .E6 l *
      canonicalRep (coxeterSystem .E6) K w * rootDiagUnit .E6 a := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ModGL .E6 K, M = g * P := ⟨_, rfl⟩
  have hM : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      M * x * M⁻¹ := fun x => by
    rw [hα x, hψ, hMdef, hg]
    group
  have hpow : ∀ m : ℕ, ∀ x : adjointGroup .E6 K,
      (((α ^ m) x : adjointGroup .E6 K) : ModGL .E6 K) = M ^ m * x * (M ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ α m, MulAut.mul_apply, ih, hM x, pow_succ M m]
      group
  have hPg : P * g * P⁻¹ = rootDiagUnit .E6 (fun i => l (ρ.symm i)) *
      ((ω.map ρ).map fun i => weylElt .E6 K i 1).prod *
        rootDiagUnit .E6 (fun i => a (ρ.symm i)) := by
    have hn : P * canonicalRep (coxeterSystem .E6) K w * P⁻¹ =
        ((ω.map ρ).map fun i => weylElt .E6 K i 1).prod := by
      rw [hωw, canonicalRep_wordProd hω, ← MulAut.conj_apply, map_list_prod, List.map_map,
        List.map_map]
      exact congrArg List.prod (List.map_congr_left fun i _ => hPn i)
    rw [hg]
    calc _ = P * rootDiagUnit .E6 l * P⁻¹ * (P * canonicalRep (coxeterSystem .E6) K w * P⁻¹) *
          (P * rootDiagUnit .E6 a * P⁻¹) := by group
      _ = _ := by rw [hPd, hPd, hn]
  obtain ⟨N, hN⟩ : ∃ N : ModGL .E6 K, N = g * (P * g * P⁻¹) := ⟨_, rfl⟩
  have hMN : M ^ 2 = N := by
    rw [hMdef, hN, sq]
    calc _ = g * (P * g * P⁻¹) * (P * P) := by group
      _ = _ := by rw [hPP, mul_one]
  have hNmem : N ∈ RecipeExcLang.inndiagGroup .E6 K := by
    have hn' : ((ω.map ρ).map fun i => weylElt .E6 K i 1).prod ∈ adjointGroup .E6 K :=
      list_prod_mem fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact weylElt_mem_adjointGroup i 1
    rw [hN, hPg, hg]
    refine mul_mem (mul_mem (mul_mem (RecipeExcLang.rootDiagUnit_mem_inndiagGroup l)
      (RecipeExcLang.adjointGroup_le_inndiagGroup
        (canonicalRep_mem_adjointGroup (coxeterSystem .E6) K w)))
      (RecipeExcLang.rootDiagUnit_mem_inndiagGroup a)) ?_
    exact mul_mem (mul_mem (RecipeExcLang.rootDiagUnit_mem_inndiagGroup _)
      (RecipeExcLang.adjointGroup_le_inndiagGroup hn'))
      (RecipeExcLang.rootDiagUnit_mem_inndiagGroup _)
  have hNk : N ^ 2 ^ k = 1 := by
    refine RecipeExcLang.eq_one_of_commute_adjointGroup hK4 (pow_mem hNmem _) fun x hx => ?_
    have hα2 : α ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
    have hgP : M ^ 2 ^ (k + 1) = N ^ 2 ^ k := by rw [pow_succ', pow_mul, hMN]
    have h1 := hpow (2 ^ (k + 1)) ⟨x, hx⟩
    rw [hα2, MulAut.one_apply, eq_mul_inv_iff_mul_eq, hgP] at h1
    exact h1.symm
  have hD : ∀ c : Fin Tag.E6.rank → Kˣ, MapsRootLines (rootDiagUnit .E6 c) 1 := fun c β hβ =>
    ⟨rootChar c β, by rw [one_smul]; exact rootDiag_rootVec c hβ⟩
  have hNw : MapsRootLines N w₂ := by
    have h1 := (((hD l).mul (mapsRootLines_canonicalRep (R := K) w)).mul (hD a)).mul
      (((hD fun i => l (ρ.symm i)).mul (mapsRootLines_list_prod (R := K) (ω.map ρ))).mul
        (hD fun i => a (ρ.symm i)))
    rwa [one_mul, one_mul, mul_one, mul_one, ← hPg, ← hg, ← hN, ← hw₂] at h1
  have hw2 : w₂ ^ 2 ^ k = 1 := by
    have hNpow : ∀ m : ℕ, MapsRootLines (N ^ m) (w₂ ^ m) := fun m => by
      induction m with
      | zero => simpa using (mapsRootLines_one : MapsRootLines (1 : ModGL .E6 K) 1)
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact ih.mul hNw
    have h1 := hNpow (2 ^ k)
    rw [hNk] at h1
    exact (mapsRootLines_one.unique h1).symm
  have hw₂F : w₂ ∈ LayerExc.famStabilizerSubgroup F := by
    show ∀ b ∈ F, ∀ v, rootChar b (w₂ • v) = rootChar b v
    intro b hb v
    rw [hθ2 v, hθχ b hb, hθχ b hb]
  have hcop : Nat.Coprime (orderOf w₂) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hw2)
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
  have hw1 := LayerExc.mem_famReflectionGroup_of_coprime_orderOf hp F
    (fun b hb => ⟨1, funext fun i => by simpa using hF b hb i⟩) hw₂F hcop
  rw [LayerExc.famReflectionGroup, hF0] at hw1
  simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false,
    Subgroup.closure_empty, Subgroup.mem_bot] at hw1
  rw [← hθ2 β, hw1, one_smul]

end CFSG.StandardType.KGCentE6

end
