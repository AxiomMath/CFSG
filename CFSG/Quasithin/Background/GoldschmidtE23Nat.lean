module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace GE23

@[expose] noncomputable def quotTopBot (A : Type) [Group A] :
    ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ ≃* A :=
  ((QuotientGroup.quotientMulEquivOfEq (by simp : (⊥ : Subgroup A).subgroupOf ⊤ = ⊥)).trans
    QuotientGroup.quotientBot).trans Subgroup.topEquiv

theorem quotTopBot_mk (A : Type) [Group A] (m : ↥(⊤ : Subgroup A)) :
    quotTopBot A (QuotientGroup.mk m) = (m : A) := rfl

@[expose] def NatData {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V)
    (e : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
    ∃ (π : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H) (β : ↥U →* Multiplicative (Fin 2 → K)),
      Function.Surjective π ∧ Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      (∀ (h : ↥H) (u : V), u ∈ U → (h : MulAut V) u ∈ U) ∧
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {e : ℕ}

theorem natData_of_binaryNatural (h : BinaryNaturalSL H U Z 2 e) : NatData H U Z e := by
  obtain ⟨K, instK, instF, hK, π', hπs, -, -, hUinv, -, -, -, β', hβs, hβz, hβeq⟩ := h
  let π'' : ↥(StatedSL 2 K) →* ↥H := π'
  let β'' : ↥U →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤ := β'
  have hπs'' : Function.Surjective π'' := hπs
  have hβs'' : Function.Surjective β'' := hβs
  have hβz'' : ∀ u : ↥U, β'' u = 1 ↔ (u : V) ∈ Z := hβz
  have hβeq'' : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥U)
      (m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))))
      (hu : ((π'' γ : ↥H) : MulAut V) (u : V) ∈ U), β'' u = QuotientGroup.mk m →
      β'' ⟨((π'' γ : ↥H) : MulAut V) (u : V), hu⟩ =
        QuotientGroup.mk ⟨natAct (StatedSL 2 K) γ (m : Multiplicative (Fin 2 → K)), trivial⟩ :=
    fun γ u m hu hmk => hβeq γ u m hu trivial hmk
  refine ⟨K, instK, instF, hK, π''.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom,
    (quotTopBot (Multiplicative (Fin 2 → K))).toMonoidHom.comp β'', ?_, ?_, ?_,
    fun h u hu => hUinv h u hu, ?_⟩
  · exact hπs''.comp (specialLinearGroupEquivStatedSL 2 K).surjective
  · exact (quotTopBot (Multiplicative (Fin 2 → K))).surjective.comp hβs''
  · intro u
    show quotTopBot (Multiplicative (Fin 2 → K)) (β'' u) = 1 ↔ _
    rw [← hβz'' u, ← map_one (quotTopBot (Multiplicative (Fin 2 → K)))]
    exact (quotTopBot (Multiplicative (Fin 2 → K))).injective.eq_iff
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β'' u)
    have key := hβeq'' (specialLinearGroupEquivStatedSL 2 K γ) u m hu hm.symm
    change quotTopBot (Multiplicative (Fin 2 → K))
        (β'' ⟨((π'' (specialLinearGroupEquivStatedSL 2 K γ) : ↥H) : MulAut V) (u : V), hu⟩) =
      Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (quotTopBot (Multiplicative (Fin 2 → K)) (β'' u))))
    rw [key, ← hm, quotTopBot_mk, quotTopBot_mk]
    rfl

theorem sl2_eq_one_of_mulVec {K : Type} [Field K] (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : ∀ w : Fin 2 → K, (γ : Matrix (Fin 2) (Fin 2) K).mulVec w = w) : γ = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp at this
  rw [this, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Pi.single_apply]

theorem NatData.injective_of {K : Type} [Field K] {π : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H}
    {β : ↥U →* Multiplicative (Fin 2 → K)} (hβs : Function.Surjective β)
    (hUinv : ∀ (h : ↥H) (u : V), u ∈ U → (h : MulAut V) u ∈ U)
    (hβeq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
        Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply sl2_eq_one_of_mulVec
  intro w
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
  have hu' := hUinv (π γ) _ u.2
  have h1 := hβeq γ u hu'
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := by
    apply Subtype.ext
    show ((π γ : ↥H) : MulAut V) (u : V) = u
    rw [hγ]
    rfl
  rw [h2, hu] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  simpa using h3.symm

end GE23

end CFSG.Quasithin
