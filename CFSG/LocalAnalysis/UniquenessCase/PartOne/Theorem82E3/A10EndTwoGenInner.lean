module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open CFSG.HardMathSupport.Solomon.Coordinator

private theorem hyperGen_inner_of_scope
    {Fam : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : SeitzHyperLie Fam) {Y : Type} [Group Y] [Finite Y]
    {K E : Subgroup Y} [K.Normal] (d : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hpd : p ≠ d.1.characteristic) (hlist : ¬ P1ThreeLieList p d)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hker : ∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hin : E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) (hz : ¬ p ∣ Nat.card (Subgroup.center K))
    (hF : ∀ E₀ : Subgroup (Cat d), Fam d p E₀) : HyperGen p K E := by
  obtain ⟨e⟩ := he
  let ρ : K →* Cat d := (e : K ⧸ Subgroup.center K →* Cat d).comp
    (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ∀ k : K, ρ k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    change e (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψi, hψs⟩ := exists_quotientMap hp ρ hρk hz hEa.2 hker hin
  have hE₀ : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : Cat d) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hEa.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (hEa.2 x x.2)
      rw [this, map_one]
  have hcard : Nat.card ψ.range = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv).symm.trans hEc
  exact hyperGen_of_quotientMap hp ρ hρs hρk hz hEa.2 hEc hin ψ hψs
    (hL d p hp hp2 hpd hlist ψ.range hE₀ hcard (hF ψ.range))

theorem seitzHyperGamma_eq_top_of_inner_of
    {Fam : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop}
    (hL : SeitzHyperLie Fam) {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hlist : ¬ P1ThreeLieList p d)
    (hF : ∀ E₀ : Subgroup (Cat d), Fam d p E₀) {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hinn : E ≤ (MulAut.conj : S →* MulAut S).range) : seitzHyperGamma p E = ⊤ := by
  have hZ := ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab
  obtain ⟨-, hc, he⟩ := ChevQ.SeitzHyperGoodInAux.inn_data hs hnab e
  haveI : (MulAut.conj : S →* MulAut S).range.Normal := inferInstance
  refine ChevQ.SeitzHyperGoodInAux.seitzHyperGamma_eq_top_of_hyperGen_inn hZ p ?_
  refine hyperGen_inner_of_scope hp hp2 hL d he hpd hlist hE hcard ?_
    (le_sup_of_le_left hinn) (by rw [hc, Subgroup.card_bot]; exact hp.not_dvd_one) hF
  intro c hc' hco
  rw [ChevQ.SeitzHyperGoodInAux.centralizer_conj_range_eq_bot hZ] at hc'
  have : c = 1 := Subgroup.mem_bot.1 hc'.2
  rw [this, orderOf_one] at hco
  exact absurd hco hp.one_lt.ne

theorem seitzHyperLie_classical :
    SeitzHyperLie fun d p _ => IsClassicalIndex d.1 ∧ ¬ UToralRestPrime d p ∧
      ChevQ.SeitzGoodIndex p d.1 := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨hc, hnotrest, hgood⟩
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rcases (isClassicalIndex_iff hrange).1 hc with hl | hu | hs | ho
  · exact seitzHyperLieLinear_unconditional d p hp hp2 hpd hlist E₀ hE₀ hcard hl
  · obtain ⟨m, q, hd⟩ := hu
    by_cases hsplit : USplitPrime d p
    · exact seitzHyperLie_unitary_split d p hp hp2 hpd hlist E₀ hE₀ hcard hsplit
    by_cases hns : UNonsplitPrime d p
    · exact seitzHyperLie_unitary_nonsplit d p hp hp2 hpd hlist E₀ hE₀ hcard hns
    by_cases htor : UToralPrime d p
    · exact seitzHyperLie_unitary_toral d p hp hp2 hpd hlist E₀ hE₀ hcard htor
    exfalso
    have h1 : ¬ p ∣ q.card - 1 := fun h => hsplit ⟨m, q, hd, h⟩
    have h2 : p ∣ q.card + 1 := by
      by_contra h
      exact hns ⟨m, q, hd, h1, h⟩
    refine hnotrest ⟨m, q, hd, h2, ?_⟩
    by_contra h
    push Not at h
    exact htor ⟨m, q, hd, h2, h.1, h.2⟩
  · have hgood' : ¬ ChevQ.ExcIndex p d.1 :=
      hgood.resolve_right (ChevQ.SeitzHyperGoodInAux.not_isSixIndex_of_symplectic hs)
    have h32 : ¬ IsSpTwoThree d p :=
      fun h => hgood' (ChevQ.SeitzHyperGoodInAux.exc_of_isSpTwoThree h)
    rcases spReducible_or_spAnisoNotTwoThree hs hp hpd h32 E₀ with hred | hani
    · exact seitzHyperLie_symplecticReducible d p hp hp2 hpd hlist E₀ hE₀ hcard hred
    · exact seitzHyperLie_spAnisoNotTwoThree d p hp hp2 hpd hlist E₀ hE₀ hcard hani
  · by_cases hred : OReducible d p E₀
    · exact seitzHyperLie_orthReducible d p hp hp2 hpd hlist E₀ hE₀ hcard hred
    · exact ChevQ.seitzGoodInnerOrth_holds d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood⟩

theorem seitzHyperGamma_eq_top_of_classical {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hc : IsClassicalIndex d.1) (hu : ¬ UToralRestPrime d p)
    (hgood : ChevQ.SeitzGoodIndex p d.1) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hinn : E ≤ (MulAut.conj : S →* MulAut S).range) :
    seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_inner_of seitzHyperLie_classical hp hp2 hs hnab d e hpd ?_
    (fun _ => ⟨hc, hu, hgood⟩) hE hcard hinn
  rintro hP
  obtain ⟨hp3, q, hq2, hq3, hd | hd⟩ := ChevQ.SeitzBridgeAux.p1_cases hpd hP hgood
  · subst hp3
    rw [hd] at hc
    exact hc
  · subst hp3
    exact ChevQ.SeitzBridgeAux.no_cube_in_inner_u38 hs hnab d q ⟨hq2, hq3⟩ hd e hE hcard hinn

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen
