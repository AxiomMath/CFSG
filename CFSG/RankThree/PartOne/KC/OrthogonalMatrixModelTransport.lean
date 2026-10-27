module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalModel

open CFSG CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.Classical2
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.OuterAutomorphisms

section Layer

variable {G H : Type*} [Group G] [Group H]

theorem layer_map_mulEquiv (e : G ≃* H) :
    (CFSG.layer G).map e.toMonoidHom = CFSG.layer H :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem map_layerCentralizer {P T' : Type*} [Group P] [Group T'] (ψ : MulAut P ≃* MulAut T')
    (D : Subgroup (MulAut P)) (a : MulAut P) :
    (layerCentralizer D a).map ψ.toMonoidHom =
      layerCentralizer (D.map ψ.toMonoidHom) (ψ a) := by
  have hmap : (D ⊓ Subgroup.centralizer ({a} : Set (MulAut P))).map ψ.toMonoidHom =
      D.map ψ.toMonoidHom ⊓ Subgroup.centralizer ({ψ a} : Set (MulAut T')) :=
    map_inf_centralizer_singleton ψ D a
  set j := equivOfMap ψ hmap with hj
  unfold layerCentralizer
  rw [Subgroup.map_map]
  have h1 : ψ.toMonoidHom.comp (D ⊓ Subgroup.centralizer ({a} : Set (MulAut P))).subtype =
      (D.map ψ.toMonoidHom ⊓ Subgroup.centralizer ({ψ a} : Set (MulAut T'))).subtype.comp
        j.toMonoidHom :=
    MonoidHom.ext fun x => (equivOfMap_val ψ hmap x).symm
  rw [h1, ← Subgroup.map_map, layer_map_mulEquiv j]

end Layer

section Pointwise

variable {P : Type*} [Group P]

theorem iInf_centralizer_layerCentralizer_eq_bot_iff (D A : Subgroup (MulAut P)) :
    (⨅ (a : MulAut P) (_ : a ∈ A ∧ a ≠ 1),
        Subgroup.centralizer ((layerCentralizer D a : Subgroup (MulAut P)) : Set (MulAut P))) = ⊥ ↔
      ∀ α : MulAut P, (∀ a ∈ A, a ≠ 1 → ∀ d ∈ layerCentralizer D a, d * α = α * d) → α = 1 := by
  rw [eq_bot_iff]
  constructor
  · intro h α hα
    have : α ∈ (⨅ (a : MulAut P) (_ : a ∈ A ∧ a ≠ 1),
        Subgroup.centralizer ((layerCentralizer D a : Subgroup (MulAut P)) : Set (MulAut P))) := by
      rw [Subgroup.mem_iInf]
      intro a
      rw [Subgroup.mem_iInf]
      intro ha
      exact Subgroup.mem_centralizer_iff.mpr fun d hd => hα a ha.1 ha.2 d hd
    exact Subgroup.mem_bot.mp (h this)
  · intro h α hα
    rw [Subgroup.mem_bot]
    refine h α fun a ha ha1 d hd => ?_
    rw [Subgroup.mem_iInf] at hα
    have h1 := hα a
    rw [Subgroup.mem_iInf] at h1
    exact Subgroup.mem_centralizer_iff.mp (h1 ⟨ha, ha1⟩) d hd

end Pointwise

section Center

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem center_projOrthDerived_eq_bot (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center (ProjOrthDerived Q) = ⊥ := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
  · exact h
  · exfalso
    obtain ⟨c, d, hcd⟩ := hnonab
    exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)

end Center

section Main

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem matrix_model_of_intrinsic (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ}
    (hint : ∀ D' : Subgroup (MulAut (ProjOrthDerived Q)),
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D' →
      ∀ A' : Subgroup (ProjOrthDerived Q), Assembly.IsElemAbelian p A' → Nat.card A' = p ^ 2 →
        (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A' ∧ a ≠ 1),
          Subgroup.centralizer (((CFSG.layer ↥(D' ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
            (D' ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
            Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) = ⊥)
    (D : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hD : inner (matrixProjectiveDerived Q) ≤ D)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hAH : A ≤ inner (matrixProjectiveDerived Q)) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) :
    (⨅ (a : MulAut (matrixProjectiveDerived Q)) (_ : a ∈ A ∧ a ≠ 1),
        Subgroup.centralizer
          ((layerCentralizer D a : Subgroup (MulAut (matrixProjectiveDerived Q))) :
            Set (MulAut (matrixProjectiveDerived Q)))) = ⊥ := by
  classical
  rw [iInf_centralizer_layerCentralizer_eq_bot_iff]
  intro α hα
  set e : matrixProjectiveDerived Q ≃* ProjOrthDerived Q := bridgeEquiv Q hd with he
  set ψ : MulAut (matrixProjectiveDerived Q) ≃* MulAut (ProjOrthDerived Q) := MulAut.congr e
    with hψ
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have : FiniteDimensional K (Fin d → K) := inferInstance
    exact center_projOrthDerived_eq_bot hQ hT
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_trivial_center hcenter
  have hinnerT : inner (ProjOrthDerived Q) = (MulAut.conj : ProjOrthDerived Q →*
      MulAut (ProjOrthDerived Q)).range := rfl
  set D' : Subgroup (MulAut (ProjOrthDerived Q)) := D.map ψ.toMonoidHom with hD'
  have hD'inner : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D' := by
    rw [← hinnerT, ← inner_map_congr e]
    exact Subgroup.map_mono hD
  set A'' : Subgroup (MulAut (ProjOrthDerived Q)) := A.map ψ.toMonoidHom with hA''
  have hA''inner : A'' ≤ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range := by
    rw [← hinnerT, ← inner_map_congr e]
    exact Subgroup.map_mono hAH
  set A' : Subgroup (ProjOrthDerived Q) :=
    A''.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hA'
  have hmapA' : A'.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = A'' := by
    rw [hA', Subgroup.map_comap_eq, inf_eq_right.mpr hA''inner]
  have hcardA' : Nat.card A' = p ^ 2 := by
    rw [← hAcard, ← Subgroup.card_map_of_injective hinj (K := A'), hmapA', hA'',
      Subgroup.card_map_of_injective ψ.injective]
  have hA'el : Assembly.IsElemAbelian p A' := by
    have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
      intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      have hx' : MulAut.conj x ∈ A'' := hx
      have hy' : MulAut.conj y ∈ A'' := hy
      obtain ⟨x₀, hx₀, hx₀e⟩ := hx'
      obtain ⟨y₀, hy₀, hy₀e⟩ := hy'
      have := hA.1
      have h1 : x₀ * y₀ = y₀ * x₀ :=
        congrArg Subtype.val (mul_comm' (⟨x₀, hx₀⟩ : A) ⟨y₀, hy₀⟩)
      rw [← hx₀e, ← hy₀e, ← map_mul, ← map_mul, h1]
    refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    obtain ⟨x₀, hx₀, hx₀e⟩ : MulAut.conj x ∈ A'' := hx
    rw [← hx₀e, ← map_pow, elemPow_eq_one_of_isElementaryAbelian x₀ hx₀, map_one]
  have hres := hint D' hD'inner A' hA'el hcardA'
  have hpoint : ∀ β : MulAut (ProjOrthDerived Q),
      (∀ a' ∈ A', a' ≠ 1 → ∀ d ∈ layerCentralizer D' (MulAut.conj a'), d * β = β * d) →
      β = 1 := by
    intro β hβ
    have hmem : β ∈ (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A' ∧ a ≠ 1),
        Subgroup.centralizer (((CFSG.layer ↥(D' ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (D' ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
          Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) := by
      rw [Subgroup.mem_iInf]
      intro a
      rw [Subgroup.mem_iInf]
      intro ha
      exact Subgroup.mem_centralizer_iff.mpr fun d hd => hβ a ha.1 ha.2 d hd
    rw [hres] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hψα : ψ α = 1 := by
    refine hpoint (ψ α) fun a' ha' ha'1 d hd => ?_
    obtain ⟨a₀, ha₀, ha₀e⟩ : MulAut.conj a' ∈ A'' := ha'
    have ha₀1 : a₀ ≠ 1 := by
      rintro rfl
      apply ha'1
      apply hinj
      rw [← ha₀e, map_one, map_one]
    have hd' : d ∈ (layerCentralizer D a₀).map ψ.toMonoidHom := by
      rw [map_layerCentralizer]
      have h1 : ψ a₀ = MulAut.conj a' := ha₀e
      rw [h1]
      exact hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd'
    have h1 := hα a₀ ha₀ ha₀1 d₀ hd₀
    show ψ d₀ * ψ α = ψ α * ψ d₀
    rw [← map_mul, ← map_mul, h1]
  exact ψ.injective (hψα.trans (map_one ψ).symm)

end Main

end CFSG.RankThree.PartOne.KCOrthogonalModel
