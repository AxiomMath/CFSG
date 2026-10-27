module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.Permutation.SupportedAdjacent

public noncomputable section

namespace CFSG.StandardType

theorem exists_adapted_typeA_datum_of_supported_permutations_corank
    {G : Type} [Group G] [Finite G] {p r c : ℕ} [Fact p.Prime] (hrc : 1 ≤ r - c) (hcr : c ≤ r)
    {Bs X J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (ρ : Equiv.Perm (Fin (r + 1)) →* MulAut Bs)
    (hρX : ∀ σ, ρ σ ∈ ggAutomizer X Bs)
    (φ : Fin r → MulAut Bs) (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V)
    (hφ : ∀ i, φ i = ρ (Equiv.swap i.castSucc i.succ))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p))
    (f : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs))
    (hf : ∀ i, (f ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (S : Finset (Fin (r + 1))) (hS : S.card = r + 1 - c)
    (hJS : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ) :
    ∃ (φ' : Fin r → MulAut Bs) (h' : Fin r → V)
      (α' : Fin r → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (φ' i) v = v - α' i v • h' i) ∧
      (∀ i, GGIsReflection p (φ' i)) ∧
      (∀ i j, α' i (h' j) = (CartanMatrix.A r i j : ZMod p)) ∧
      (∃ e : (CoxeterMatrix.A r).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (e ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ' i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ') ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range (φ' ∘ Fin.castLE (by omega : r - c ≤ r))) := by
  classical
  have hecard : Nat.card S = r - c + 1 := by
    rw [Nat.card_eq_finsetCard, hS]
    omega
  let eS : Fin (r - c + 1) ≃ S := (Finite.equivFinOfCardEq hecard).symm
  let first : Fin (r - c + 1) ↪ Fin (r + 1) :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩
  let enumerated : Fin (r - c + 1) ↪ Fin (r + 1) :=
    eS.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding first enumerated
  have hτi : ∀ i, τ (first i) = eS i := by
    intro i
    have hh := congrArg (fun e : Fin (r - c + 1) ↪ Fin (r + 1) => e i) hτ
    simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def, enumerated,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coe_subtype] using hh
  let u := ρ τ
  let U := ggLin (p := p) ι u
  let φ' : Fin r → MulAut Bs := fun i => u * φ i * u⁻¹
  let h' : Fin r → V := fun i => U (h i)
  let α' : Fin r → Module.Dual (ZMod p) V := fun i => (α i).comp U.symm.toLinearMap
  have hlin' : ∀ i v, ggLin (p := p) ι (φ' i) v = v - α' i v • h' i := by
    intro i v
    exact l05nBL_lin_conj ι u (φ i) (hlin i) v
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.A r i j : ZMod p) := by
    intro i j
    change α i (U.symm (U (h j))) = _
    rw [LinearEquiv.symm_apply_apply, hpair]
  have hu : u ∈ ggAutomizer X Bs := hρX τ
  let cAut : ggAutomizer X Bs ≃* ggAutomizer X Bs := MulAut.conj ⟨u, hu⟩
  let f' := f.trans cAut
  have hf' : ∀ i, (f' ((CoxeterMatrix.A r).simple i) : MulAut Bs) = φ' i := by
    intro i
    change u * (f ((CoxeterMatrix.A r).simple i) : MulAut Bs) * u⁻¹ = _
    rw [hf]
  have hclos' : ggAutomizer X Bs = Subgroup.closure (Set.range φ') := by
    have heq := l05nBL_closure_conj (ggAutomizer X Bs) u hu
    rw [hclos, MonoidHom.map_closure, ← Set.range_comp] at heq
    rw [hclos]
    exact heq.symm
  have hsw : ∀ i : Fin (r - c),
      ρ (Equiv.swap (eS i.castSucc : Fin (r + 1)) (eS i.succ : Fin (r + 1))) =
        φ' (Fin.castLE (by omega) i) := by
    intro i
    let j : Fin r := Fin.castLE (by omega) i
    have hcast : first i.castSucc = j.castSucc := Fin.ext rfl
    have hsucc : first i.succ = j.succ := Fin.ext rfl
    rw [← hτi, ← hτi, hcast, hsucc, Equiv.swap_apply_apply,
      map_mul, map_mul, map_inv]
    change ρ τ * ρ (Equiv.swap j.castSucc j.succ) * (ρ τ)⁻¹ = _
    rw [← hφ j]
  refine ⟨φ', h', α', hlin',
    fun i => l05nBL_refl_conj (hrefl i) u, hpair', ⟨f', hf'⟩, hclos', ?_⟩
  rw [hJS, CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent S eS,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  exact hsw i

end CFSG.StandardType

end
