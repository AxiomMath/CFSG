module

public import CFSG.Quasithin.Vol2.Ch3E213MG41F

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

@[expose] def FactSp4ReflBig : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (G₀ : Subgroup (antiSp k)),
    IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)) → (transvSet G₀).Nonempty →
    (∀ d ∈ transvSet G₀, ∀ d' ∈ transvSet G₀, commSpace d = commSpace d' → d = d') →
    (∃ r s : Fin 4 → k, G41.trv r 1 ∈ G₀ ∧ G41.trv s 1 ∈ G₀ ∧ spBil r s ≠ 0 ∧ spBil r s ≠ 1) →
    G41OrthW G₀

end CFSG.Quasithin.Ch3E213M

namespace CFSG.Quasithin.Ch3E213M.G41.Refl

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def normC (G₀ : Subgroup (antiSp k)) : Set (Fin 4 → k) :=
  {r | r ≠ 0 ∧ trv r 1 ∈ G₀}

@[expose] def OnePerCentre (G₀ : Subgroup (antiSp k)) : Prop :=
  ∀ d ∈ transvSet G₀, ∀ d' ∈ transvSet G₀, commSpace d = commSpace d' → d = d'

variable {G₀ : Subgroup (antiSp k)}

theorem trv_mem_transvSet_of_mem {r : Fin 4 → k} (hr : r ∈ normC G₀) :
    trv r 1 ∈ transvSet G₀ :=
  ⟨hr.2, isTransvection_trv hr.1 one_ne_zero⟩

theorem exists_sq_eq [Finite k] (c : k) : ∃ μ : k, μ ^ 2 = c := by
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) c
  exact ⟨μ, by rw [sq, hμ]⟩

theorem exists_normC_eq [Finite k] {d : antiSp k} (hd : d ∈ transvSet G₀) :
    ∃ r ∈ normC G₀, d = trv r 1 := by
  obtain ⟨v, c, hv, hc, -, rfl⟩ := exists_of_mem_transvSet hd
  obtain ⟨μ, hμ⟩ := exists_sq_eq c
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hμ]; ring)
  have he : trv (μ • v) 1 = trv v c := by rw [trv_smul, hμ, mul_one]
  exact ⟨μ • v, ⟨smul_ne_zero hμ0 hv, he ▸ hd.1⟩, he.symm⟩

theorem act_mem_normC {r : Fin 4 → k} (hr : r ∈ normC G₀) {g : antiSp k} (hg : g ∈ G₀) :
    natAct g r ∈ normC G₀ := by
  refine ⟨fun h => hr.1 (act_injective g (by rw [h, act_zero])), ?_⟩
  rw [← conj_trv]
  exact G₀.mul_mem (G₀.mul_mem hg hr.2) (G₀.inv_mem hg)

theorem eq_one_of_smul_mem (hone : OnePerCentre G₀) {r : Fin 4 → k} (hr : r ∈ normC G₀)
    {μ : k} (hμ : μ • r ∈ normC G₀) : μ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hμ.1 (zero_smul k r)
  have h1 := trv_mem_transvSet_of_mem hμ
  rw [trv_smul, mul_one] at h1
  have h2 := hone _ h1 _ (trv_mem_transvSet_of_mem hr)
    (by rw [commSpace_trv hr.1 (pow_ne_zero 2 hμ0), commSpace_trv hr.1 one_ne_zero])
  exact eq_one_of_sq_eq_one (trv_param_inj hr.1 h2)

theorem span_normC [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    (hD : (transvSet G₀).Nonempty) : Submodule.span k (normC G₀) = ⊤ := by
  have hW : DInv G₀ (Submodule.span k (normC G₀)) := by
    intro d hd w hw
    obtain ⟨s, hs, rfl⟩ := exists_normC_eq hd
    rw [act_trv]
    exact Submodule.add_mem _ hw (Submodule.smul_mem _ _ (Submodule.subset_span hs))
  rcases dInv_of_irr_closure hirr _ hW with h | h
  · obtain ⟨d, hd⟩ := hD
    obtain ⟨r, hr, -⟩ := exists_normC_eq hd
    have hr' : r ∈ Submodule.span k (normC G₀) := Submodule.subset_span hr
    rw [h, Submodule.mem_bot] at hr'
    exact absurd hr' hr.1
  · exact h

theorem orthW_of_forall (hspan : Submodule.span k (normC G₀) = ⊤)
    (Q : QuadraticForm k (Fin 4 → k)) (hpol : ∀ x y, QuadraticMap.polar Q x y = spBil x y)
    (hQ : ∀ r ∈ normC G₀, Q r = 1) : G41OrthW G₀ := by
  refine ⟨Q, hpol, fun g hg x => ?_⟩
  have hadd : ∀ a b : Fin 4 → k, Q (a + b) = Q a + Q b + spBil a b := fun a b => by
    rw [← hpol]
    unfold QuadraticMap.polar
    ring
  have hx : x ∈ Submodule.span k (normC G₀) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem r hr => rw [hQ _ (act_mem_normC hr hg), hQ r hr]
  | zero => rw [act_zero]
  | add x y _ _ hx hy => rw [act_add, hadd, hadd, hx, hy, bil_act]
  | smul a x _ hx => rw [act_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, hx]

end CFSG.Quasithin.Ch3E213M.G41.Refl
