module

public import CFSG.Quasithin.Background.SmithB45SzIrr

public section

namespace CFSG.Quasithin

namespace B45Sz

open scoped TensorProduct
open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Semidihedral.Principal
open Representation Matrix

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K] (k : Type) [Field k] [Algebra K k]

section Tensor

variable {G : Type} [Group G]

omit [CharP K 2] [Fintype K] [Algebra K k] in
theorem repMultiplicity_tprod_sub_quot' {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k G V} (W : Subrepresentation ρ) {X : Type}
    [AddCommGroup X] [Module k X] [Module.Finite k X] (τ : Representation k G X) {E : Type}
    [AddCommGroup E] [Module k E] (σ : Representation k G E) :
    repMultiplicity (tprod ρ τ) σ = repMultiplicity (tprod W.toRepresentation τ) σ +
      repMultiplicity (tprod W.quotient τ) σ := by
  have : Module.Finite k (W.toSubmodule ⊗[k] X) := inferInstance
  have : Module.Finite k ((V ⧸ W.toSubmodule) ⊗[k] X) := inferInstance
  refine repMultiplicity_eq_add_of_exact (IntertwiningMap.rTensor τ (subIncl ρ W))
    (IntertwiningMap.rTensor τ (quotProj ρ W)) ?_ ?_ ?_ σ
  · exact Module.Flat.rTensor_preserves_injective_linearMap (M := X) (subIncl ρ W).toLinearMap
      W.toSubmodule.injective_subtype
  · exact LinearMap.rTensor_surjective X W.toSubmodule.mkQ_surjective
  · exact Module.Flat.rTensor_exact X (LinearMap.exact_subtype_mkQ W.toSubmodule)

omit [CharP K 2] [Fintype K] [Algebra K k] in
theorem equivRTensor_nonempty {V V' X : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup X] [Module k X]
    {ρ : Representation k G V} {ρ' : Representation k G V'}
    (e : Representation.Equiv ρ ρ') (τ : Representation k G X) :
    Nonempty (Representation.Equiv (tprod ρ τ) (tprod ρ' τ)) :=
  ⟨Representation.Equiv.mk (LinearEquiv.rTensor X e.toLinearEquiv) (fun g => by
    refine TensorProduct.ext' fun v w => ?_
    simp only [LinearMap.comp_apply, tprod_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.rTensor_tmul]
    have h : e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) :=
      IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap g v
    rw [h])⟩

omit [CharP K 2] [Fintype K] [Algebra K k] in
theorem equivLTensor_nonempty {V V' X : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup X] [Module k X]
    {ρ : Representation k G V} {ρ' : Representation k G V'}
    (τ : Representation k G X) (e : Representation.Equiv ρ ρ') :
    Nonempty (Representation.Equiv (tprod τ ρ) (tprod τ ρ')) := by
  obtain ⟨e'⟩ := equivRTensor_nonempty k e τ
  exact ⟨((Representation.TensorProduct.comm τ ρ).trans e').trans
    (Representation.TensorProduct.comm ρ' τ)⟩

end Tensor

section OnlySz

variable [CharP k 2]

@[expose] def OnlySz (hK : Nat.card K = 2 ^ (2 * a + 1)) {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k ↥(suzukiGroup a K) V) : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module k E] [Module.Finite k E]
    (σ : Representation k ↥(suzukiGroup a K) E), σ.IsIrreducible → 0 < repMultiplicity ρ σ →
      ∃ A : Finset ℕ, A ⊆ szOmega a ∧ Nonempty (Representation.Equiv (matRep (szT k hK A)) σ)

variable {k}

omit [CharP k 2] in
theorem OnlySz.congr {hK : Nat.card K = 2 ^ (2 * a + 1)} {V V' : Type} [AddCommGroup V]
    [Module k V] [AddCommGroup V'] [Module k V'] {ρ : Representation k ↥(suzukiGroup a K) V}
    {ρ' : Representation k ↥(suzukiGroup a K) V'} (e : Representation.Equiv ρ ρ')
    (h : OnlySz k hK ρ) : OnlySz k hK ρ' := by
  intro E _ _ _ σ hσ hpos
  exact h _ σ hσ (by rwa [repMultiplicity_congr_left e σ])

omit [CharP k 2] in
theorem OnlySz.of_subsingleton {hK : Nat.card K = 2 ^ (2 * a + 1)} {V : Type} [AddCommGroup V]
    [Module k V] [Subsingleton V] (ρ : Representation k ↥(suzukiGroup a K) V) :
    OnlySz k hK ρ := by
  intro E _ _ _ σ hσ hpos
  exfalso
  have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
  unfold repMultiplicity at hpos
  rw [compositionMultiplicity_of_subsingleton] at hpos
  exact lt_irrefl _ hpos

theorem onlySz_T (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Finset ℕ} (hA : A ⊆ szOmega a) : OnlySz k hK (matRep (szT k hK A)) := by
  intro E _ _ _ σ hσ hpos
  rw [repMultiplicity_of_isIrreducible (szT_fixed_irreducible k hK hA).2 σ] at hpos
  by_cases h : Nonempty (Representation.Equiv (matRep (szT k hK A)) σ)
  · exact ⟨A, hA, h⟩
  · simp [h] at hpos

omit [CharP k 2] in
theorem OnlySz.sub_quot {hK : Nat.card K = 2 ^ (2 * a + 1)} {V : Type} [AddCommGroup V]
    [Module k V] [Module.Finite k V] {ρ : Representation k ↥(suzukiGroup a K) V}
    (h : OnlySz k hK ρ) (W : Subrepresentation ρ) :
    OnlySz k hK W.toRepresentation ∧ OnlySz k hK W.quotient := by
  constructor
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega

omit [CharP k 2] in
theorem OnlySz.of_flag {hK : Nat.card K = 2 ^ (2 * a + 1)} {V : Type} [AddCommGroup V]
    [Module k V] [Module.Finite k V] {ρ : Representation k ↥(suzukiGroup a K) V}
    (L : List (FRep k ↥(suzukiGroup a K))) (hL : FlagTop ρ L)
    (h : ∀ Q ∈ L, OnlySz k hK Q.ρ) : OnlySz k hK ρ := by
  intro E _ _ _ σ hσ hpos
  rw [FlagTop.mult L ρ hL σ] at hpos
  have : ∃ Q ∈ L, 0 < repMultiplicity Q.ρ σ := by
    by_contra hcon
    push Not at hcon
    have : (L.map fun Q => repMultiplicity Q.ρ σ).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hx
      exact Nat.le_zero.mp (hcon Q hQ)
    omega
  obtain ⟨Q, hQ, hpos'⟩ := this
  exact h Q hQ _ σ hσ hpos'

theorem onlySz_tprod_T (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ (n : ℕ) (B : Finset ℕ), B ⊆ szOmega a → B.card = n → ∀ i : ℕ,
      OnlySz k hK (tprod (matRep (szT k hK B)) (matRep (szN k hK i))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hB hcard i
    have main : ∀ j : ℕ, j ∈ szOmega a →
        OnlySz k hK (tprod (matRep (szT k hK B)) (matRep (szN k hK j))) := by
      intro j hjΩ
      by_cases hmem : j ∈ B
      · set B' := B.erase j with hB'def
        have hB' : insert j B' = B := Finset.insert_erase hmem
        have hnot : j ∉ B' := Finset.notMem_erase j B
        have hB'sub : B' ⊆ szOmega a := (Finset.erase_subset j B).trans hB
        have hcard' : B'.card < n := by
          have hc : B'.card = B.card - 1 := Finset.card_erase_of_mem hmem
          have h1 : 0 < B.card := Finset.card_pos.mpr ⟨j, hmem⟩
          omega
        obtain ⟨eA⟩ := szInsert_nonempty k hK hnot
        rw [hB'] at eA
        let N := matRep (szN k hK j)
        let T' := matRep (szT k hK B')
        let X : FRep k ↥(suzukiGroup a K) := ⟨(B' → Fin 4) → k, T'⟩
        have hflag := FlagTop.tensor _ (tprod N N) (szSquare_filtration k hK j) X
        have hT' : OnlySz k hK T' := onlySz_T hK hB'sub
        obtain ⟨eR⟩ := equivRTensor_nonempty k eA N
        refine OnlySz.congr ((Representation.TensorProduct.comm (tprod N N) T').trans
          ((Representation.TensorProduct.assoc T' N N).symm.trans eR))
          (OnlySz.of_flag _ hflag ?_)
        intro Q hQ
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
          at hQ
        rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact OnlySz.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlySz.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 1))
        · exact OnlySz.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlySz.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 2))
        · exact OnlySz.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlySz.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 1))
        · exact OnlySz.congr (Representation.TensorProduct.lid k T').symm hT'
      · obtain ⟨e⟩ := szInsert_nonempty k hK hmem
        exact OnlySz.congr e.symm (onlySz_T hK (Finset.insert_subset hjΩ hB))
    obtain ⟨e⟩ := equivLTensor_nonempty k (matRep (szT k hK B)) (szFoldEquiv k hK i)
    exact OnlySz.congr e (main _ (szFold_mem i))

theorem onlySz_tprod_N (hK : Nat.card K = 2 ^ (2 * a + 1))
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k ↥(suzukiGroup a K) V) (hρ : OnlySz k hK ρ) (i : ℕ) :
    OnlySz k hK (tprod ρ (matRep (szN k hK i))) := by
  have key := rep_induction (k := k) (G := ↥(suzukiGroup a K))
    (fun {V} _ _ _ ρ => OnlySz k hK ρ → ∀ i : ℕ,
      OnlySz k hK (tprod ρ (matRep (szN k hK i))))
    (fun {V} _ _ _ ρ hsub _ i => by
      have h1 : Subsingleton V := hsub
      have : Subsingleton (V ⊗[k] (Fin 4 → k)) := by
        refine subsingleton_of_forall_eq 0 fun t => ?_
        induction t using TensorProduct.inductionOn with
        | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact OnlySz.of_subsingleton _)
    (fun {V} _ _ _ ρ hirr hρ i => by
      have hpos : 0 < repMultiplicity ρ ρ := by
        rw [repMultiplicity_of_isIrreducible hirr ρ]
        have : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
        simp [this]
      obtain ⟨B, hB, ⟨e⟩⟩ := hρ V ρ hirr hpos
      obtain ⟨e'⟩ := equivRTensor_nonempty k e (matRep (szN k hK i))
      exact OnlySz.congr e' (onlySz_tprod_T hK B.card B hB rfl i))
    (fun {V} _ _ _ ρ W hW1 hW2 hρ i => by
      obtain ⟨h1, h2⟩ := hρ.sub_quot W
      have hA := hW1 h1 i
      have hB := hW2 h2 i
      intro E _ _ _ σ hσ hpos
      rw [repMultiplicity_tprod_sub_quot' k W (matRep (szN k hK i)) σ] at hpos
      by_cases ha : 0 < repMultiplicity (tprod W.toRepresentation
          (matRep (szN k hK i))) σ
      · exact hA E σ hσ ha
      · exact hB E σ hσ (by omega))
  exact key _ ρ rfl hρ i

end OnlySz

section Classification

open CFSG.QuasithinUnique.Setup.X7a (kron kron_apply kron_mul kron_one)
open CFSG.QuasithinUnique.Setup.SL2Modules (powMat powMat_mul)

@[expose] noncomputable def szPow (hK : Nat.card K = 2 ^ (2 * a + 1)) (m : ℕ) :
    ↥(suzukiGroup a K) →* Matrix (Fin m → Fin 4) (Fin m → Fin 4) k :=
  (powRep (F := K) k m).comp (szIncl hK)

theorem szPow_succ_nonempty (hK : Nat.card K = 2 ^ (2 * a + 1))
    (m : ℕ) :
    Nonempty (Representation.Equiv
      (tprod (matRep (szPow k hK m)) (matRep (szN k hK 0))) (matRep (szPow k hK (m + 1)))) := by
  obtain ⟨e⟩ := powRep_succ_nonempty (F := K) k m
  exact ⟨equivComp (szIncl hK) e⟩

theorem szPow_zero_nonempty (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (Representation.Equiv (matRep (szPow k hK 0))
      (matRep (szT k hK (∅ : Finset ℕ)))) := by
  obtain ⟨e⟩ := powRep_zero_nonempty (F := K) k
  exact ⟨equivComp (szIncl hK) e⟩

theorem onlySz_szPow [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (m : ℕ) : OnlySz k hK (matRep (szPow k hK m)) := by
  induction m with
  | zero =>
    exact OnlySz.congr (szPow_zero_nonempty k hK).some.symm
      (onlySz_T hK (Finset.empty_subset _))
  | succ m ih =>
    exact OnlySz.congr (szPow_succ_nonempty k hK m).some (onlySz_tprod_N hK _ ih 0)

theorem szN_zero_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (szN k hK 0) := by
  intro g h hgh
  exact szIncl_injective hK (natRepS_zero_injective (F := K) (k := k) hgh)

theorem exists_szT_equiv [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {E : Type} [AddCommGroup E] [Module k E]
    [Module.Finite k E] (σ : Representation k ↥(suzukiGroup a K) E) (hσ : σ.IsIrreducible) :
    ∃ A : Finset ℕ, A ⊆ szOmega a ∧
      Nonempty (Representation.Equiv (matRep (szT k hK A)) σ) := by
  classical
  obtain ⟨m, -, φ, hφ, hcomm⟩ := CFSG.QuasithinUnique.Setup.SL2Modules.faithful_tensor_power
    (by norm_num : 0 < 4) (szN k hK 0) (szN_zero_injective k hK) σ hσ
  let Φ : IntertwiningMap (matRep (szPow k hK m)) σ :=
    ⟨φ, fun g => by
      refine LinearMap.ext fun v => ?_
      exact hcomm g v⟩
  have hex : Function.Exact (subIncl (matRep (szPow k hK m))
      (IntertwiningMap.ker (matRep (szPow k hK m)) σ Φ)) Φ := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  have hpos : 0 < repMultiplicity (matRep (szPow k hK m)) σ := by
    rw [repMultiplicity_eq_add_of_exact (subIncl _
      (IntertwiningMap.ker (matRep (szPow k hK m)) σ Φ)) Φ
      (IntertwiningMap.ker (matRep (szPow k hK m)) σ Φ).toSubmodule.injective_subtype hφ hex σ,
      repMultiplicity_of_isIrreducible hσ σ]
    have : Nonempty (Representation.Equiv σ σ) := ⟨Representation.Equiv.refl σ⟩
    simp [this]
  exact onlySz_szPow k hK m E σ hσ hpos

end Classification

end B45Sz

end CFSG.Quasithin
