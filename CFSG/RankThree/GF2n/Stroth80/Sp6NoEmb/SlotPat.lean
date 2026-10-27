module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.RecApply
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open Representation CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor frobTensor_isIrreducible
  frobTensor_empty_apply finrank_frobTensor)

section Pi

variable {k G V : Type} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

@[expose] def piRep {ι : Type} (ρ : ι → Representation k G V) : Representation k G (ι → V) where
  toFun g := LinearMap.pi fun i => ρ i g ∘ₗ LinearMap.proj i
  map_one' := by
    ext f i
    simp
  map_mul' g h := by
    ext f i
    simp

theorem piRep_apply {ι : Type} (ρ : ι → Representation k G V) (g : G) (f : ι → V) (i : ι) :
    piRep ρ g f i = ρ i g (f i) :=
  rfl

theorem repMultiplicity_piRep_fin [FiniteDimensional k V] {E : Type} [AddCommGroup E]
    [Module k E] (σ : Representation k G E) :
    ∀ {m : ℕ} (ρ : Fin m → Representation k G V),
      repMultiplicity (piRep ρ) σ = ∑ i, repMultiplicity (ρ i) σ := by
  intro m
  induction m with
  | zero =>
    intro ρ
    have : Subsingleton (piRep ρ).asModule := inferInstanceAs (Subsingleton (Fin 0 → V))
    rw [repMultiplicity, compositionMultiplicity_of_subsingleton, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ m ih =>
    intro ρ
    rw [Fin.sum_univ_succ, ← ih (fun i => ρ i.succ)]
    let f₁ : (ρ 0).IntertwiningMap (piRep ρ) :=
      ⟨LinearMap.single k (fun _ => V) 0, fun g => by
        ext x i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [piRep_apply]
        · simp [piRep_apply, Fin.succ_ne_zero]⟩
    let f₂ : (piRep ρ).IntertwiningMap (piRep fun i : Fin m => ρ i.succ) :=
      ⟨LinearMap.funLeft k V Fin.succ, fun g => by
        ext f i
        rfl⟩
    refine repMultiplicity_eq_add_of_exact f₁ f₂ (fun x y h => ?_) (fun f => ?_) (fun f => ?_) σ
    · simpa [f₁] using congrFun h 0
    · refine ⟨Fin.cons 0 f, funext fun i => ?_⟩
      show (Fin.cons (0 : V) f : Fin (m + 1) → V) i.succ = f i
      exact Fin.cons_succ _ _ _
    · constructor
      · intro hf
        refine ⟨f 0, funext fun i => Fin.cases ?_ (fun j => ?_) i⟩
        · simp [f₁]
        · have h1 : f j.succ = 0 := congrFun hf j
          simp [f₁, Fin.succ_ne_zero, h1]
      · rintro ⟨x, rfl⟩
        funext j
        show (Pi.single (0 : Fin (m + 1)) x : Fin (m + 1) → V) j.succ = 0
        simp [Fin.succ_ne_zero]

@[expose] def piRepReindex {ι ι' : Type} (e : ι' ≃ ι) (ρ : ι → Representation k G V) :
    (piRep ρ).Equiv (piRep (ρ ∘ e)) :=
  Representation.Equiv.mk (LinearEquiv.funCongrLeft k V e) fun g => by
    ext f i
    rfl

theorem repMultiplicity_piRep [FiniteDimensional k V] {ι : Type} [Fintype ι]
    (ρ : ι → Representation k G V) {E : Type} [AddCommGroup E] [Module k E]
    (σ : Representation k G E) :
    repMultiplicity (piRep ρ) σ = ∑ i, repMultiplicity (ρ i) σ := by
  rw [repMultiplicity_congr_left (piRepReindex (Fintype.equivFin ι).symm ρ),
    repMultiplicity_piRep_fin]
  exact Equiv.sum_comp (Fintype.equivFin ι).symm fun i => repMultiplicity (ρ i) σ

theorem repMultiplicity_piRep_const [FiniteDimensional k V] (m : ℕ) (σ : Representation k G V)
    {E : Type} [AddCommGroup E] [Module k E] (ρ' : Representation k G E) :
    repMultiplicity (piRep fun _ : Fin m => σ) ρ' = m * repMultiplicity σ ρ' := by
  rw [repMultiplicity_piRep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Pi

section Tensor

variable {k G V E R : Type} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup E]
  [Module k E] [AddCommGroup R] [Module k R] [Module.Finite k R]

@[expose] noncomputable def tensorPiEquiv {τ : Representation k G V} {σ : Representation k G E}
    (e : V ≃ₗ[k] E ⊗[k] R)
    (he : ∀ g v, e (τ g v) = TensorProduct.map (σ g) LinearMap.id (e v)) :
    τ.Equiv (piRep fun _ : Fin (finrank k R) => σ) :=
  Representation.Equiv.mk
    (e ≪≫ₗ TensorProduct.congr (LinearEquiv.refl k E) (Module.finBasis k R).equivFun ≪≫ₗ
      TensorProduct.piScalarRight k k E (Fin (finrank k R))) fun g => by
    ext v i
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.trans_apply, he, piRep_apply]
    generalize e v = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x r =>
      simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    | add t t' ht ht' => simp only [map_add, Pi.add_apply, ht, ht']

end Tensor

section Slot

variable {K : Type} [Field K] [CharP K 2]

theorem nonempty_slot_piEquiv (J : Fin 3 → Finset ℕ) (s : Fin 3) :
    Nonempty (Representation.Equiv ((cubeRep K J).comp (slot K s))
      (piRep fun _ : Fin (2 ^ ((J 0).card + (J 1).card + (J 2).card - (J s).card)) =>
        frobTensor K K (J s))) := by
  match s with
  | 0 =>
    have h : finrank K (((J 1 → Fin 2) → K) ⊗[K] ((J 2 → Fin 2) → K)) =
        2 ^ ((J 0).card + (J 1).card + (J 2).card - (J 0).card) := by
      rw [Module.finrank_tensorProduct, finrank_frobTensor, finrank_frobTensor, ← pow_add]
      congr 1
      omega
    exact ⟨(tensorPiEquiv (LinearEquiv.refl K _)
      (fun g v => LinearMap.congr_fun (cubeRep_slot_zero J g) v)).trans
        (piRepReindex (finCongr h.symm) _)⟩
  | 1 =>
    have h : finrank K (((J 0 → Fin 2) → K) ⊗[K] ((J 2 → Fin 2) → K)) =
        2 ^ ((J 0).card + (J 1).card + (J 2).card - (J 1).card) := by
      rw [Module.finrank_tensorProduct, finrank_frobTensor, finrank_frobTensor, ← pow_add]
      congr 1
      omega
    exact ⟨(tensorPiEquiv (TensorProduct.leftComm K _ _ _) (leftComm_cubeRep_slot_one J)).trans
        (piRepReindex (finCongr h.symm) _)⟩
  | 2 =>
    have h : finrank K (((J 0 → Fin 2) → K) ⊗[K] ((J 1 → Fin 2) → K)) =
        2 ^ ((J 0).card + (J 1).card + (J 2).card - (J 2).card) := by
      rw [Module.finrank_tensorProduct, finrank_frobTensor, finrank_frobTensor, ← pow_add]
      congr 1
      omega
    exact ⟨(tensorPiEquiv (cubeSwapTwo J) (cubeSwapTwo_cubeRep_slot_two J)).trans
        (piRepReindex (finCongr h.symm) _)⟩

theorem repMultiplicity_cubeRep_slot (J : Fin 3 → Finset ℕ) (s : Fin 3) {W : Type}
    [AddCommGroup W] [Module K W] (ρ' : Representation K SL(2, K) W) :
    repMultiplicity ((cubeRep K J).comp (slot K s)) ρ' =
      2 ^ ((J 0).card + (J 1).card + (J 2).card - (J s).card) *
        repMultiplicity (frobTensor K K (J s)) ρ' := by
  obtain ⟨e⟩ := nonempty_slot_piEquiv (K := K) J s
  rw [repMultiplicity_congr_left e, repMultiplicity_piRep_const]

variable [Fintype K] {n : ℕ}

theorem slPat_cubeRep_slot (hK : Fintype.card K = 2 ^ n) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (s : Fin 3) {J'' : Finset ℕ} (hJ'' : ∀ i ∈ J'', i < n) :
    slPat ((cubeRep K J).comp (slot K s)) J'' =
      if J'' = J s then 2 ^ ((J 0).card + (J 1).card + (J 2).card - (J s).card) else 0 := by
  rw [slPat, repMultiplicity_cubeRep_slot, ← slPat, slPat_frobTensor hK (hJ s) hJ'']
  split_ifs <;> simp

variable {V : Type} [AddCommGroup V] [Module K V]

theorem sum_pat_slPat (hK : Fintype.card K = 2 ^ n) (s : Fin 3) (J'' : Finset ℕ)
    [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    slPat (ρ.comp (slot K s)) J'' =
      ∑ J ∈ labels n, pat ρ J * slPat ((cubeRep K J).comp (slot K s)) J'' :=
  sum_pat hK (fun {V} _ _ _ ρ => slPat (ρ.comp (slot K s)) J'')
    (fun {V} _ _ _ ρ hsub => by
      haveI := hsub
      exact slPat_of_subsingleton _ _)
    (fun {V W} _ _ _ _ _ _ ρ σ e => slPat_congr (equivComp e (slot K s)) _)
    (fun {V} _ _ _ ρ U => repMultiplicity_sub_quot (ρ.comp (slot K s)) (subComp U (slot K s)) _)
    ρ

theorem slPat_slot_eq_sum (hK : Fintype.card K = 2 ^ n) (s : Fin 3) {J'' : Finset ℕ}
    (hJ'' : ∀ i ∈ J'', i < n) [Module.Finite K V] (ρ : Representation K (Cube K) V) :
    slPat (ρ.comp (slot K s)) J'' = ∑ J ∈ labels n, pat ρ J *
      if J'' = J s then 2 ^ ((J 0).card + (J 1).card + (J 2).card - (J s).card) else 0 := by
  rw [sum_pat_slPat hK s J'' ρ]
  exact Finset.sum_congr rfl fun J hJ => by
    rw [slPat_cubeRep_slot hK (mem_labels.mp hJ) s hJ'']

end Slot

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
