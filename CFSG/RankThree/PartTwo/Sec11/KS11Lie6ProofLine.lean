module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjTup
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofWeyl

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

@[expose] def gA2 : Exp3 := ![2, 2, 0, 2]

theorem tup_two_mul {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1) (β : Exp3) :
    tup ω (fun i => 2 * β i) = tup ω β ^ 2 := by
  funext i
  simp only [tup, Pi.pow_apply]
  rw [two_mul, ← pow_val_add hω3, sq]

theorem tup_pow_three {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1) (β : Exp3) :
    tup ω β ^ 3 = 1 := by
  funext i
  simp only [tup, Pi.pow_apply, Pi.one_apply]
  rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]

theorem rootDiagUnit_pow'
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ (a ^ n) = rootDiagUnit τ a ^ n :=
  map_pow (rootDiagUnitHom τ K) a n

theorem rhoExp_eq_of_twistHom_fixed
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ} (hω : orderOf ω = 3)
    (hσω : Units.map σ.toMonoidHom ω = ω) {γ : Exp3}
    (h : twistHom TwistTag.D4 K σ (rootDiagUnit TwistTag.D4.tag (tup ω γ)) =
      rootDiagUnit TwistTag.D4.tag (tup ω γ)) : rhoExp γ = γ := by
  rw [twistHom_rootDiagUnit_eq] at h
  have h2 : (fun i => Units.map σ.toMonoidHom (tup ω γ (TwistTag.D4.perm.symm i))) =
      tup ω (rhoExp γ) := by
    funext i
    simp only [tup, rhoExp, map_pow, hσω]
  rw [h2] at h
  exact tup_injective hω (CFSG.LieType.Chevalley.rootDiagUnit_injective h)

@[expose] def lineCheck : Bool :=
  d4WeylTab.all fun e => !(decide (rhoExp (tabExp e gA2) = tabExp e gA2)) ||
    decide (tabExp e gA2 = gA2 ∨ tabExp e gA2 = fun i => 2 * gA2 i)

theorem lineCheck_eq : lineCheck = true := by decide +kernel

theorem eq_of_conj_gA2
    {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) {γ : Exp3} (hγ : rhoExp γ = γ)
    {g : ModGL TwistTag.D4.tag K} (hg : g ∈ adjointGroup TwistTag.D4.tag K)
    (hb : rootDiagUnit TwistTag.D4.tag (tup ω gA2) ∈ torusGroup TwistTag.D4.tag K)
    (ha : rootDiagUnit TwistTag.D4.tag (tup ω γ) ∈ torusGroup TwistTag.D4.tag K)
    (hconj : g * rootDiagUnit TwistTag.D4.tag (tup ω gA2) * g⁻¹ =
      rootDiagUnit TwistTag.D4.tag (tup ω γ)) :
    γ = gA2 ∨ γ = fun i => 2 * gA2 i := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨w, hw⟩ := exists_weyl_of_conj_rootDiagUnit ha hb hg hconj
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w⁻¹
  have hcol : ∀ i, w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hwe
  rw [weylTuple_tup_of_tab hω3 hcol] at hw
  have h1 : tabExp e gA2 = γ := tup_injective hω hw
  have h := List.all_eq_true.1 lineCheck_eq e he
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rw [h1] at h
  rcases h with h | h
  · exact absurd hγ h
  · exact h

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
