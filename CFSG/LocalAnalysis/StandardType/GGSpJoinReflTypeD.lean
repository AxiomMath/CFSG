module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.Timmesfeld.ARS.CaseOAWeyl
public import CFSG.LieType.RootSystem.Positivity

public section

namespace CFSG.StandardType.SpJoinRefl



open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.Timmesfeld.ARS.CaseOA

private theorem td_ggCoxeterMatrixD_eq (r : ℕ) :
    ggCoxeterMatrixD r = coxeterMatrix (isFiniteType_cartanD r) := by
  ext i j
  rw [ggCoxeterMatrixD_apply, ← cartanD_eq r]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp [cartanD, TauCeti.coxeterOrder_four]
  · rw [if_neg hij]
    have hsymm : cartanD r j i = cartanD r i j := by
      rw [cartanD_eq]
      exact (CartanMatrix.D_isSymm r).apply i j
    rw [hsymm]
    have h01 : cartanD r i j = -1 ∨ cartanD r i j = 0 := by
      rw [cartanD_eq]
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rcases h01 with h | h
    · rw [h]
      simp [TauCeti.coxeterOrder_one]
    · rw [h]
      simp [TauCeti.coxeterOrder_zero]

section TypeD

variable {G : Type} [Group G]

theorem card_coxeterD_le (r : ℕ) (hr : 2 ≤ r) :
    Nat.card (ggCoxeterMatrixD r).Group ≤ 2 ^ (r - 1) * r.factorial := by
  rcases r with _ | n
  · omega
  rw [td_ggCoxeterMatrixD_eq]
  have hsub : n + 1 - 1 = n := by omega
  rw [hsub]
  classical
  have key : ∀ w : (coxeterMatrix (isFiniteType_cartanD (n + 1))).Group,
      ∃ q : Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → ℤ),
        (∀ c, q.2 c = 1 ∨ q.2 c = -1) ∧ (∏ c, q.2 c = 1) ∧
        ∀ v, toStdD (n + 1) (weylAction (isFiniteType_cartanD (n + 1)) w v) =
          fun c => q.2 c * toStdD (n + 1) v (q.1 c) := by
    intro w
    obtain ⟨π, s, hs, hprod, h⟩ := exists_signedPerm_toStdD_weylAction hr w
    exact ⟨(π, s), hs, hprod, h⟩
  choose q hq using key
  let f : (coxeterMatrix (isFiniteType_cartanD (n + 1))).Group →
      Equiv.Perm (Fin (n + 1)) × (Fin n → Bool) :=
    fun w => ((q w).1, fun c => decide ((q w).2 (Fin.castSucc c) = 1))
  have hf : Function.Injective f := by
    intro w w' hww
    have hπ : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww).1
    have hsgn : (fun c : Fin n => decide ((q w).2 (Fin.castSucc c) = 1)) =
        (fun c : Fin n => decide ((q w').2 (Fin.castSucc c) = 1)) := (Prod.ext_iff.mp hww).2
    have hcast : ∀ i : Fin n, (q w).2 (Fin.castSucc i) = (q w').2 (Fin.castSucc i) := by
      intro i
      have h := congrFun hsgn i
      simp only [decide_eq_decide] at h
      rcases (hq w).1 (Fin.castSucc i) with h1 | h1 <;>
        rcases (hq w').1 (Fin.castSucc i) with h2 | h2
      · rw [h1, h2]
      · rw [h1] at h
        rw [h2] at h
        exact absurd h (by norm_num)
      · rw [h1] at h
        rw [h2] at h
        exact absurd h (by norm_num)
      · rw [h1, h2]
    have hs : (q w).2 = (q w').2 := by
      funext c
      refine Fin.lastCases ?_ (fun i => hcast i) c
      have hprodw : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) * (q w).2 (Fin.last n) = 1 := by
        rw [← Fin.prod_univ_castSucc]
        exact (hq w).2.1
      have hprodw' : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) * (q w').2 (Fin.last n) = 1 := by
        rw [Finset.prod_congr rfl (fun i _ => hcast i)]
        rw [← Fin.prod_univ_castSucc]
        exact (hq w').2.1
      have hP : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i _
        rcases (hq w).1 (Fin.castSucc i) with h | h <;> rw [h] <;> norm_num
      exact mul_left_cancel₀ hP (by rw [hprodw, hprodw'])
    apply weylAction_injective (isFiniteType_cartanD (n + 1))
    refine LinearMap.ext fun v => toStdD_injective (n + 1) ?_
    rw [(hq w).2.2 v, (hq w').2.2 v, hs, hπ]
  calc Nat.card (coxeterMatrix (isFiniteType_cartanD (n + 1))).Group
      ≤ Nat.card (Equiv.Perm (Fin (n + 1)) × (Fin n → Bool)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ n * (n + 1).factorial := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_perm, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
        ring

theorem not_weylOfType_D_of_orbit [Finite G] {p n : ℕ} (hn : 2 ≤ n) {Bs : Subgroup G}
    {AL R : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p (ggCoxeterMatrixD (n + 1)) (AL ⊔ R))
    {y' : G} (hy' : y' ∈ Bs) (hfy' : ∀ ψ ∈ R, ((ψ ⟨y', hy'⟩ : ↥Bs) : G) = y')
    (hcR : 2 ^ n * n.factorial ≤ Nat.card R)
    (horb : 2 * n ≤ Nat.card (MulAction.orbit AL (⟨y', hy'⟩ : ↥Bs))) : False := by
  obtain ⟨e, -⟩ := hW
  set y : ↥Bs := ⟨y', hy'⟩ with hydef
  have hcardA' : Nat.card ↥(AL ⊔ R) = Nat.card (ggCoxeterMatrixD (n + 1)).Group :=
    (Nat.card_congr e.toEquiv).symm
  have hcardA : Nat.card ↥(AL ⊔ R) ≤ 2 ^ n * (n + 1).factorial := by
    rw [hcardA']
    have h := card_coxeterD_le (n + 1) (by omega)
    have hsub : n + 1 - 1 = n := by omega
    rwa [hsub] at h
  have hfix : ∀ ψ ∈ R, ψ y = y := by
    intro ψ hψ
    rw [hydef]
    exact Subtype.ext (hfy' ψ hψ)
  have h1 : Nat.card (MulAction.orbit ↥(AL ⊔ R) y) * Nat.card R ≤ Nat.card ↥(AL ⊔ R) :=
    card_orbit_mul_card_le le_sup_right y hfix
  have hsub_orbit : MulAction.orbit AL y ⊆ MulAction.orbit ↥(AL ⊔ R) y := by
    intro z hz
    rw [MulAction.mem_orbit_iff] at hz ⊢
    obtain ⟨g, hg⟩ := hz
    exact ⟨⟨g, Subgroup.mem_sup_left g.2⟩, hg⟩
  have hcard_orbit : Nat.card (MulAction.orbit AL y) ≤ Nat.card (MulAction.orbit ↥(AL ⊔ R) y) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub_orbit) (Set.inclusion_injective hsub_orbit)
  have hchain : 2 * n * (2 ^ n * n.factorial) ≤ 2 ^ n * (n + 1).factorial :=
    calc 2 * n * (2 ^ n * n.factorial)
        ≤ Nat.card (MulAction.orbit AL y) * Nat.card R := Nat.mul_le_mul horb hcR
      _ ≤ Nat.card (MulAction.orbit ↥(AL ⊔ R) y) * Nat.card R :=
            Nat.mul_le_mul_right _ hcard_orbit
      _ ≤ Nat.card ↥(AL ⊔ R) := h1
      _ ≤ 2 ^ n * (n + 1).factorial := hcardA
  have hK : 0 < 2 ^ n * n.factorial := by positivity
  have hineq : 2 * n * (2 ^ n * n.factorial) ≤ (n + 1) * (2 ^ n * n.factorial) := by
    calc 2 * n * (2 ^ n * n.factorial)
        ≤ 2 ^ n * (n + 1).factorial := hchain
      _ = (n + 1) * (2 ^ n * n.factorial) := by
            rw [Nat.factorial_succ]
            ring
  have hle : 2 * n ≤ n + 1 := Nat.le_of_mul_le_mul_right hineq hK
  omega

end TypeD

end CFSG.StandardType.SpJoinRefl
