module

public import CFSG.LocalAnalysis.StandardType.GGTBJXNoncomm
public import CFSG.LocalAnalysis.StandardType.GGTBJXModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJX_torusJNoncomm
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* ↥(adjointGroup τ K)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p τ.rank ↥(adjointGroup τ K)
      (Set.range (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)))
      L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  obtain ⟨ζ, ψ, σ, Θ, hstd, hΘ⟩ := ggTBJX_stdModel hp hp2 hpq hdet hV hT hfullp ψ₀ A hA
  have : Fact p.Prime := ⟨hp⟩
  let f₀ : Multiplicative (Fin τ.rank → ZMod p) := Θ.symm ⟨y, hy⟩
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := MulEquiv.apply_symm_apply Θ _
  have hy_eq : y = MulAut.conj (σ f₀) := by rw [← hΘ f₀, hΘf₀]
  have hfix : fixSubgroup y = Subgroup.centralizer ({σ f₀} : Set L') := by
    ext x
    rw [mem_fixSubgroup, hy_eq, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => (mul_inv_eq_iff_eq_mul.mp h).symm,
      fun h => mul_inv_eq_iff_eq_mul.mpr h.symm⟩
  have hJ' : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')) := by
    rw [hfix] at hJ
    exact hJ
  let B : Subgroup (MulAut L') := A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')
  have hcardB : Nat.card ↥B = Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} := by
    refine Nat.card_congr ?_
    let toF : ↥B → {f : Multiplicative (Fin τ.rank → ZMod p) //
        ∀ j ∈ J, σ f * j = j * σ f} := fun b =>
      let f : Multiplicative (Fin τ.rank → ZMod p) :=
        Θ.symm ⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩
      ⟨f, by
        intro j hj
        have hbj : (b : MulAut L') j = j := by
          have h := MulAction.mem_stabilizer_iff.mp
            (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
          simpa [MulAut.smul_def] using h
        have hbf : (b : MulAut L') = MulAut.conj (σ f) := by
          have hfA : Θ f = (⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
            MulEquiv.apply_symm_apply Θ _
          rw [← hΘ f]
          exact (congrArg Subtype.val hfA).symm
        rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
        exact hbj⟩
    let toG : {f : Multiplicative (Fin τ.rank → ZMod p) // ∀ j ∈ J, σ f * j = j * σ f} → ↥B :=
      fun c => ⟨((Θ c.1 : ↥A) : MulAut L'), by
        refine Subgroup.mem_inf.mpr ⟨(Θ c.1).2, ?_⟩
        rw [Subgroup.mem_iInf]
        intro j
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hΘ, MulAut.conj_apply]
        have hcomm := c.2 j j.2
        rw [hcomm]
        group⟩
    refine ⟨toF, toG, ?_, ?_⟩
    · intro b
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.apply_symm_apply]
    · intro c
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.symm_apply_eq]
  have hcardA : Nat.card ↥A = p ^ τ.rank := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod (p := p) τ.rank
  have hcount' : p ^ 2 * Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ τ.rank := by
    rw [← hcardB, ← hcardA]
    exact hcount
  obtain ⟨m₁, m₂, s₁, s₂, hm₁, hm₂, hform₁, hform₂, hs₁, hs₂, hfix₁, hfix₂, hne⟩ :=
    ggTBJX_core hτ hp2 hstd f₀ hJ' hcount'
  obtain ⟨hn₁, heq₁⟩ :=
    exists_ggConjAut_eq_congr (n := m₁) (s := s₁) hstd.1 Θ hΘ hform₁
  obtain ⟨hn₂, heq₂⟩ :=
    exists_ggConjAut_eq_congr (n := m₂) (s := s₂) hstd.1 Θ hΘ hform₂
  have hcardV : Nat.card (Multiplicative (Fin τ.rank → ZMod p)) = p ^ τ.rank :=
    CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod (p := p) τ.rank
  have hfixV₁ : Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) // s₁ f = f} * p =
      Nat.card (Multiplicative (Fin τ.rank → ZMod p)) := by
    rw [hcardV]; exact hfix₁
  have hfixV₂ : Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) // s₂ f = f} * p =
      Nat.card (Multiplicative (Fin τ.rank → ZMod p)) := by
    rw [hcardV]; exact hfix₂
  have hrefl₁ : GGIsReflection p (MulAut.congr Θ s₁) :=
    ⟨by rw [← map_pow, hs₁, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₁) hfixV₁).2⟩
  have hrefl₂ : GGIsReflection p (MulAut.congr Θ s₂) :=
    ⟨by rw [← map_pow, hs₂, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₂) hfixV₂).2⟩
  have hrefl₁' : GGIsReflection p (ggConjAut A hn₁) := by rw [heq₁]; exact hrefl₁
  have hrefl₂' : GGIsReflection p (ggConjAut A hn₂) := by rw [heq₂]; exact hrefl₂
  have hne' : MulAut.congr Θ s₁ * MulAut.congr Θ s₂ ≠
      MulAut.congr Θ s₂ * MulAut.congr Θ s₁ := by
    intro h
    apply hne
    apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul]
    exact h
  have hconjne : ggConjAut A hn₁ * ggConjAut A hn₂ ≠
      ggConjAut A hn₂ * ggConjAut A hn₁ := by
    rw [heq₁, heq₂]
    exact hne'
  exact ⟨m₁, m₂, hn₁, hn₂, hm₁, hm₂,
    ggTorusWeylElt_of_model hstd.1 Θ hΘ (fun f => ⟨s₁ f, hform₁ f⟩),
    ggTorusWeylElt_of_model hstd.1 Θ hΘ (fun f => ⟨s₂ f, hform₂ f⟩),
    hrefl₁', hrefl₂', hconjne⟩

end CFSG.StandardType

end

