module

public import CFSG.LocalAnalysis.StandardType.GGFamTameTwoDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamTameD4
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem famExc_exc_kind {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (hk : twistKindM ρ χ i = .exc) :
    ¬ twistInner (componentRoots χ i)
        ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) ∧
      ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
        (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
          ¬ twistInner (componentRoots χ i)
            ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]))) := by
  unfold twistKindM at hk
  split_ifs at hk with h1 h2
  exact ⟨h1, h2⟩

private theorem famExc_e6_outer
    {τ : Tag} [M27Ok τ] [E6Sub τ] (hτne : ∀ t : TwistTag, t.tag ≠ τ)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 6)
    (hc : (componentRoots (famCharHom a) i).ncard = 72)
    (hhr : τ.rank < 2 * 6)
    {N : ℕ} (hN : N.Prime) (hN2 : N ≠ 2) {b : Fin τ.rank → Lˣ}
    (hbN : rootDiagUnit τ b ^ N = 1) (j : KernelComponent (rootCharHom b))
    (hbj : componentRoots (rootCharHom b) j = componentRoots (famCharHom a) i)
    {K : KacData τ} (hK : K.Facts)
    {E6C : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 6 → kacCount τ K.θ C = 72 → C = E6C)
    (hJ : ∀ k : Fin τ.rank, some k ∈ E6C ↔ k.val ≤ 5) (hnone : none ∉ E6C) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hNL : (N : L) ≠ 0 := by
    intro h
    have hdvd : 2 ∣ N := (CharP.cast_eq_zero_iff L 2 N).1 h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hN).1 hdvd).symm
  have hrb : compRank (componentRoots (rootCharHom b) j) = 6 := by rw [hbj]; exact hr
  have hcb : (componentRoots (rootCharHom b) j).ncard = 72 := by rw [hbj]; exact hc
  obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hN hNL hK hpin hJ hnone hbN j hrb hcb
  have hstab : S.ρ '' componentRoots (famCharHom a) i = componentRoots (famCharHom a) i :=
    image_componentRoots_eq_of_rank_gt_half S
      (fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ) i (by rw [hr]; exact hhr)
  have hρ : ∀ γ ∈ componentRoots (rootCharHom b) j,
      S.ρ γ ∈ componentRoots (rootCharHom b) j := by
    intro γ hγ
    rw [hbj] at hγ ⊢
    have hmem : S.ρ γ ∈ S.ρ '' componentRoots (famCharHom a) i := ⟨γ, hγ, rfl⟩
    rwa [hstab] at hmem
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hw : ∀ γ ∈ componentRoots (rootCharHom b) j,
      w • γ ∈ componentRoots (rootCharHom b) j := by
    intro γ hγ
    rw [← S.rho_eq_smul hτne hn hγ.1.1]
    exact hρ γ hγ
  have hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom b) j) :=
    isQuasisimple_rationalComponent_of_e6 hτne S hn b j v hv hρ hw
  rw [← rationalComponentM_eq] at hq
  exact rationalComponentM_eq_of_componentRoots_eq S.ρ S.Γ hbj ▸ hq

theorem langFamTame_exc
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .exc) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  obtain ⟨hnin, hA | hD⟩ := famExc_exc_kind S.ρ hk
  ·
    obtain ⟨hr, hc⟩ := hA
    rcases hτ with rfl | rfl | rfl
    ·
      exfalso
      obtain ⟨u, hu⟩ := h1
      obtain ⟨j, hj⟩ := exists_componentRoots_superset (χ := famCharHom a)
        (χ' := rootCharHom (a u)) i
        (fun γ hγ => ⟨hγ.1.1, ((mem_kernelRoots_famChar a).1 hγ.1).2 u⟩)
      have hle : Tag.E6.rootCount ≤ (componentRoots (rootCharHom (a u)) j).ncard := by
        calc Tag.E6.rootCount = 72 := by decide
          _ = (componentRoots (famCharHom a) i).ncard := hc.symm
          _ ≤ _ := Set.ncard_le_ncard hj
            ((finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1)
      exact hu (rootDiagUnit_eq_one_of_ncard j hle)
    ·
      obtain ⟨N, b, j, hN, hN2, hbN, hbj⟩ :=
        exists_isolating_element (Or.inr (Or.inl rfl)) a hp hp2 hap i
      exact famExc_e6_outer twistTag_tag_ne_E7 S hT i hr hc (by decide) hN hN2 hbN j hbj
        facts_E7 kacCount_E7_six (by decide) (by decide)
    ·
      obtain ⟨N, b, j, hN, hN2, hbN, hbj⟩ :=
        exists_isolating_element (Or.inr (Or.inr rfl)) a hp hp2 hap i
      exact famExc_e6_outer twistTag_tag_ne_E8 S hT i hr hc (by decide) hN hN2 hbN j hbj
        facts_E8 kacCount_E8_six (by decide) (by decide)
  ·
    exact langFamTame_twoD_four hτ S hp hp2 hT hap h1 i hD.1 hD.2.1 hnin

end CFSG.StandardType.TableCRes
