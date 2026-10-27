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

theorem eq_one_of_normalForm_zero_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Set (Fin Tag.E6.rank → Kˣ)} (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    (hF0 : famKernel F = ∅) {α : MulAut (adjointGroup .E6 K)} (h2 : ∃ k : ℕ, α ^ 2 ^ k = 1)
    {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K) {w : WeylGroup Tag.E6} {a : Fin Tag.E6.rank → Kˣ}
    (hα : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      h * canonicalRep (coxeterSystem .E6) K w * exactNormalAutGL .E6 K a 1 0 (x : ModGL .E6 K) *
        (h * canonicalRep (coxeterSystem .E6) K w)⁻¹)
    (hw : ∀ b ∈ F, canonicalRep (coxeterSystem .E6) K w *
        exactNormalAutGL .E6 K a 1 0 (rootDiagUnit .E6 b) *
          (canonicalRep (coxeterSystem .E6) K w)⁻¹ = rootDiagUnit .E6 b) :
    α = 1 := by
  obtain ⟨k, hk⟩ := h2
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hψ : ∀ g : ModGL .E6 K, exactNormalAutGL .E6 K a 1 0 g =
      rootDiagUnit .E6 a * g * (rootDiagUnit .E6 a)⁻¹ := by
    intro g
    have hQ : exactQ .E6 K 0 = 1 := pow_zero _
    have hσ : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [exactNormalAutGL_apply, hQ, hσ, show Units.map (entrywiseHom (RingHom.id K)) g = g from
      Units.ext (entrywise_id _), mul_one, inv_one, mul_one]
  obtain ⟨M, hMdef⟩ : ∃ M : ModGL .E6 K, M = rootDiagUnit .E6 l *
      canonicalRep (coxeterSystem .E6) K w * rootDiagUnit .E6 a := ⟨_, rfl⟩
  have hM : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      M * x * M⁻¹ := fun x => by
    rw [hα x, hψ, hMdef]
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
  have hMmem : M ∈ RecipeExcLang.inndiagGroup .E6 K := by
    rw [hMdef]
    exact mul_mem (mul_mem (RecipeExcLang.rootDiagUnit_mem_inndiagGroup l)
      (RecipeExcLang.adjointGroup_le_inndiagGroup
        (canonicalRep_mem_adjointGroup (coxeterSystem .E6) K w)))
      (RecipeExcLang.rootDiagUnit_mem_inndiagGroup a)
  have hMk : M ^ 2 ^ k = 1 := by
    refine RecipeExcLang.eq_one_of_commute_adjointGroup hK4 (pow_mem hMmem _) fun x hx => ?_
    have h1 := hpow (2 ^ k) ⟨x, hx⟩
    rw [hk, MulAut.one_apply, eq_mul_inv_iff_mul_eq] at h1
    exact h1.symm
  have hD : ∀ c : Fin Tag.E6.rank → Kˣ, MapsRootLines (rootDiagUnit .E6 c) 1 := fun c β hβ =>
    ⟨rootChar c β, by rw [one_smul]; exact rootDiag_rootVec c hβ⟩
  have hMw : MapsRootLines M w := by
    have h1 := ((hD l).mul (mapsRootLines_canonicalRep (R := K) w)).mul (hD a)
    rwa [one_mul, mul_one, ← hMdef] at h1
  have hw2 : w ^ 2 ^ k = 1 := by
    have hMpow : ∀ m : ℕ, MapsRootLines (M ^ m) (w ^ m) := fun m => by
      induction m with
      | zero => simpa using (mapsRootLines_one : MapsRootLines (1 : ModGL .E6 K) 1)
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact ih.mul hMw
    have h1 := hMpow (2 ^ k)
    rw [hMk] at h1
    exact (mapsRootLines_one.unique h1).symm
  have hwF : w ∈ LayerExc.famStabilizerSubgroup F := by
    show ∀ b ∈ F, ∀ v, rootChar b (w • v) = rootChar b v
    intro b hb
    have h1 := hw b hb
    rw [hψ, ← rootDiagUnit_mul, mul_comm a b, rootDiagUnit_mul, mul_inv_cancel_right] at h1
    exact (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 h1.symm
  have hcop : Nat.Coprime (orderOf w) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hw2)
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
  have hw1 := LayerExc.mem_famReflectionGroup_of_coprime_orderOf hp F
    (fun b hb => ⟨1, funext fun i => by simpa using hF b hb i⟩) hwF hcop
  rw [LayerExc.famReflectionGroup, hF0] at hw1
  simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false,
    Subgroup.closure_empty, Subgroup.mem_bot] at hw1
  rw [hw1, canonicalRep_one, mul_one, ← rootDiagUnit_mul] at hMdef
  have hMK : M ^ Nat.card Kˣ = 1 := by
    rw [hMdef]
    change rootDiagUnitHom .E6 K (l * a) ^ Nat.card Kˣ = 1
    rw [← map_pow, show (l * a) ^ Nat.card Kˣ = 1 from funext fun j => pow_card_eq_one',
      map_one]
  have hcop2 : Nat.Coprime (2 ^ k) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 LayerExc.odd_card_units)
  have hM1 := pow_gcd_eq_one.2 ⟨hMk, hMK⟩
  rw [hcop2.gcd_eq_one, pow_one] at hM1
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hM x, hM1, one_mul, inv_one, mul_one, MulAut.one_apply]

end CFSG.StandardType.KGCentE6

end
