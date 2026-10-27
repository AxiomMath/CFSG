module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Twist
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.RecApply
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDGalois
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped TensorProduct
open Representation
open CFSG.Open
open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv)
open CFSG.Semidihedral.Principal (repMultiplicity_eq_add_of_exact)
open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)

section Generic

variable {K : Type} [Field K] {G : Type} [Group G] {V W : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

@[expose] def kerSubG {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [show f.toLinearMap (ρ g v) = σ g (f.toLinearMap v) from
      LinearMap.congr_fun (f.isIntertwining' g) v, hv, map_zero]

@[expose] noncomputable def equivQuotKerG {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : (kerSubG f).quotient.Equiv σ :=
  Representation.Equiv.mk (f.toLinearMap.quotKerEquivOfSurjective hf) fun g => by
    ext v
    exact LinearMap.congr_fun (f.isIntertwining' g) v

@[expose] def TwistEquiv.comp' {k' : Type} [Field k'] {τ : K ≃+* k'} {V' : Type}
    [AddCommGroup V'] [Module k' V'] {ρ : Representation K G V} {ρ' : Representation k' G V'}
    (T : TwistEquiv τ ρ ρ') {G' : Type} [Group G'] (α : G' →* G) :
    TwistEquiv τ (ρ.comp α) (ρ'.comp α) where
  e := T.e
  comm g v := T.comm (α g) v

@[expose] def interSub (ρ : Representation K G V) (U : ℕ → Subrepresentation ρ) :
    ℕ → Subrepresentation ρ
  | 0 => ⊤
  | m + 1 => interSub ρ U m ⊓ U m

theorem mem_interSub {ρ : Representation K G V} (U : ℕ → Subrepresentation ρ) (m : ℕ) (v : V) :
    v ∈ (interSub ρ U m).toSubmodule ↔ ∀ i < m, v ∈ (U i).toSubmodule := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => Submodule.mem_top⟩
  | succ m ih =>
    change v ∈ (interSub ρ U m).toSubmodule ⊓ (U m).toSubmodule ↔ _
    rw [Submodule.mem_inf, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      exacts [h1 i h, h2]
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h m (Nat.lt_succ_self m)⟩

end Generic

section CubePat

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V W : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem pat_prod [Module.Finite K V] [Module.Finite K W] (ρ : Representation K (Cube K) V)
    (σ : Representation K (Cube K) W) (J : Fin 3 → Finset ℕ) :
    pat (ρ.prod σ) J = pat ρ J + pat σ J := by
  let f : ρ.IntertwiningMap (ρ.prod σ) :=
    ⟨LinearMap.inl K V W, fun g => by ext v <;> simp⟩
  let g' : (ρ.prod σ).IntertwiningMap σ :=
    ⟨LinearMap.snd K V W, fun g => LinearMap.ext fun _ => rfl⟩
  have hex : Function.Exact f g' := by
    intro ⟨v, w⟩
    constructor
    · intro h
      change w = 0 at h
      subst h
      exact ⟨v, rfl⟩
    · rintro ⟨u, hu⟩
      rw [← hu]
      rfl
  exact repMultiplicity_eq_add_of_exact f g' (LinearMap.inl_injective) (LinearMap.snd_surjective)
    hex _

theorem pat_quot_inf_le [Module.Finite K V] (ρ : Representation K (Cube K) V)
    (A B : Subrepresentation ρ) (J : Fin 3 → Finset ℕ) :
    pat (A ⊓ B).quotient J ≤ pat A.quotient J + pat B.quotient J := by
  let ψ : (A ⊓ B).quotient.IntertwiningMap (A.quotient.prod B.quotient) :=
    ⟨LinearMap.prod (Submodule.mapQ _ _ LinearMap.id fun x hx => hx.1)
      (Submodule.mapQ _ _ LinearMap.id fun x hx => hx.2), fun g => by
        ext v
        · rfl
        · rfl⟩
  have hψ : Function.Injective ψ := by
    change Function.Injective ψ.toLinearMap
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : (Submodule.Quotient.mk v : V ⧸ A.toSubmodule) = 0 := congrArg Prod.fst hx
    have h2 : (Submodule.Quotient.mk v : V ⧸ B.toSubmodule) = 0 := congrArg Prod.snd hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  rw [← pat_prod]
  exact pat_le_of_injective ψ hψ J

theorem pat_quot_interSub_le [Module.Finite K V] (ρ : Representation K (Cube K) V)
    (U : ℕ → Subrepresentation ρ) (m : ℕ) (J : Fin 3 → Finset ℕ) :
    pat (interSub ρ U m).quotient J ≤ ∑ i ∈ Finset.range m, pat (U i).quotient J := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero]
    haveI : Subsingleton (V ⧸ (interSub ρ U 0).toSubmodule) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact (pat_of_subsingleton _ J).le
  | succ m ih =>
    rw [Finset.sum_range_succ]
    exact (pat_quot_inf_le ρ _ _ J).trans (Nat.add_le_add_right ih _)

@[expose] noncomputable def quotBotEquiv (ρ : Representation K (Cube K) V)
    (U : Subrepresentation ρ) (hU : U.toSubmodule = ⊥) : U.quotient.Equiv ρ :=
  Representation.Equiv.mk (U.toSubmodule.quotEquivOfEqBot hU) fun g => by
    ext v
    rfl

end CubePat

section BaseChange

variable {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
  {G : Type} [Group G] {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

@[expose] noncomputable def baseChangeRep (ρ : Representation (ZMod 2) G N) :
    Representation K G (K ⊗[ZMod 2] N) where
  toFun g := (ρ g).baseChange K
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_id
  map_mul' g h := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]
    rfl

theorem baseChangeRep_apply (ρ : Representation (ZMod 2) G N) (g : G) :
    baseChangeRep (K := K) ρ g = (ρ g).baseChange K := rfl

local notation "Φ" => CFSG.GH74.GLS.Stage4.Rest.frobTensor (p := 2) (F := K) N

@[expose] noncomputable def frobTwist (ρ : Representation (ZMod 2) G N) :
    TwistEquiv (frob K) (baseChangeRep (K := K) ρ) (baseChangeRep (K := K) ρ) where
  e :=
    { toFun := Φ
      invFun := (Equiv.ofBijective _ CFSG.GH74.GLS.Stage4.Rest.frobTensor_bijective).symm
      map_add' := map_add Φ
      map_smul' := fun c x => by
        rw [CFSG.GH74.GLS.Stage4.Rest.frobTensor_smul]
        simp [frob_apply]
      left_inv := (Equiv.ofBijective _ CFSG.GH74.GLS.Stage4.Rest.frobTensor_bijective).left_inv
      right_inv :=
        (Equiv.ofBijective _ CFSG.GH74.GLS.Stage4.Rest.frobTensor_bijective).right_inv }
  comm g v := CFSG.GH74.GLS.Stage4.Rest.frobTensor_baseChange (ρ g) v

theorem frobTensor_pow_card {n : ℕ} (hK : Fintype.card K = 2 ^ n) : Φ ^ n = 1 := by
  refine TensorProduct.ext' fun c a => ?_
  rw [CFSG.GH74.GLS.Stage4.Rest.frobTensor_pow_tmul, Module.End.one_apply, ← hK,
    FiniteField.pow_card]

@[expose] noncomputable def frobIter (ρ : Representation (ZMod 2) G N)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) :
    ℕ → Subrepresentation (baseChangeRep (K := K) ρ)
  | 0 => U₀
  | i + 1 => (frobTwist ρ).mapSub (frobIter ρ U₀ i)

theorem mem_frobIter (ρ : Representation (ZMod 2) G N)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) (i : ℕ) (x : K ⊗[ZMod 2] N) :
    x ∈ (frobIter ρ U₀ i).toSubmodule ↔ ∃ y ∈ U₀.toSubmodule, (Φ ^ i) y = x := by
  induction i generalizing x with
  | zero => exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => hyx ▸ hy⟩
  | succ i ih =>
    change x ∈ (frobIter ρ U₀ i).toSubmodule.map ((frobTwist (K := K) ρ).e :
      K ⊗[ZMod 2] N →ₛₗ[(frob K : K →+* K)] K ⊗[ZMod 2] N) ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (ih z).mp hz
      exact ⟨y, hy, by rw [pow_succ', Module.End.mul_apply]; rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(Φ ^ i) y, (ih _).mpr ⟨y, hy, rfl⟩, by rw [pow_succ', Module.End.mul_apply]; rfl⟩

theorem frobIter_card {n : ℕ} (hK : Fintype.card K = 2 ^ n) (ρ : Representation (ZMod 2) G N)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) : frobIter ρ U₀ n = U₀ := by
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [mem_frobIter, frobTensor_pow_card hK]
  exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem interSub_frobIter_eq_bot {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n)
    (ρ : Representation (ZMod 2) G N)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) G) ρ.asModule)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) (hU : U₀.toSubmodule ≠ ⊤) :
    (interSub _ (frobIter ρ U₀) n).toSubmodule = ⊥ := by
  haveI : Finite K := inferInstance
  have hΦ : ∀ x ∈ (interSub _ (frobIter ρ U₀) n).toSubmodule,
      Φ x ∈ (interSub _ (frobIter ρ U₀) n).toSubmodule := by
    intro x hx
    rw [mem_interSub] at hx ⊢
    intro i hi
    rcases i with _ | j
    · have h1 : Φ x ∈ (frobIter ρ U₀ n).toSubmodule := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact ⟨x, hx m (by omega), rfl⟩
      rwa [frobIter_card hK] at h1
    · exact ⟨x, hx j (by omega), rfl⟩
  have hG : ∀ g : G, ∀ x ∈ (interSub _ (frobIter ρ U₀) n).toSubmodule,
      (ρ g).baseChange K x ∈ (interSub _ (frobIter ρ U₀) n).toSubmodule := by
    intro g x hx
    rw [mem_interSub] at hx ⊢
    exact fun i hi => (frobIter ρ U₀ i).apply_mem_toSubmodule g (hx i hi)
  rcases CFSG.GH74.GLS.Stage4.Rest.frobTensor_stable_eq_bot_or_top ρ hW
    (interSub _ (frobIter ρ U₀) n).toSubmodule hΦ hG with h | h
  · exact h
  · exfalso
    apply hU
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (interSub _ (frobIter ρ U₀) n).toSubmodule := h ▸ Submodule.mem_top
    exact (mem_interSub _ n x).mp hx 0 (by omega)

end BaseChange

section Patterns

variable {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K] {n : ℕ}
  {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [Module.Finite (ZMod 2) N]

theorem pat_baseChange_shift (hK : Fintype.card K = 2 ^ n)
    (ρ : Representation (ZMod 2) (StatedSp 3 K) N) {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) :
    pat ((baseChangeRep (K := K) ρ).comp block) (shiftL n J) =
      pat ((baseChangeRep (K := K) ρ).comp block) J :=
  pat_twist hK (TwistEquiv.comp' (frobTwist ρ) block) hJ

theorem pat_frobIter_quot (hK : Fintype.card K = 2 ^ n)
    (ρ : Representation (ZMod 2) (StatedSp 3 K) N)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) (i : ℕ) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) :
    pat ((frobIter ρ U₀ i).quotient.comp block) ((shiftL n)^[i] J) =
      pat (U₀.quotient.comp block) J := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hJi : IsLabel n ((shiftL n)^[i] J) := by
      clear ih
      induction i with
      | zero => exact hJ
      | succ i ih' =>
        rw [Function.iterate_succ_apply']
        exact isLabel_shiftL ih'
    rw [Function.iterate_succ_apply', ← ih]
    exact pat_twist hK (TwistEquiv.comp' ((frobTwist ρ).quot (frobIter ρ U₀ i)) block) hJi

theorem pat_le_sum_frobIter (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n)
    (ρ : Representation (ZMod 2) (StatedSp 3 K) N)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule)
    (U₀ : Subrepresentation (baseChangeRep (K := K) ρ)) (hU : U₀.toSubmodule ≠ ⊤)
    {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) :
    pat ((baseChangeRep (K := K) ρ).comp block) J ≤
      ∑ i ∈ Finset.range n, pat (U₀.quotient.comp block) ((shiftL n)^[n - i] J) := by
  have hbot := interSub_frobIter_eq_bot hK hn ρ hW U₀ hU
  let UH : ℕ → Subrepresentation ((baseChangeRep (K := K) ρ).comp block) :=
    fun i => subComp (frobIter ρ U₀ i) block
  have hsub : (interSub _ UH n).toSubmodule = ⊥ := by
    rw [← hbot]
    ext x
    rw [mem_interSub, mem_interSub]
    rfl
  rw [← pat_congr (quotBotEquiv _ _ hsub) J]
  refine (pat_quot_interSub_le _ UH n J).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := (Finset.mem_range.mp hi).le
  have hJ' : IsLabel n ((shiftL n)^[n - i] J) := by
    generalize n - i = m
    induction m with
    | zero => exact hJ
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact isLabel_shiftL ih
  have h := pat_frobIter_quot hK ρ U₀ i hJ'
  rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hi', shiftL_iterate_self hJ] at h
  exact h.le

end Patterns

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
