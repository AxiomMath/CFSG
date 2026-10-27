module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSplit
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer

public section

namespace CFSG.Quasithin

namespace B45Sz

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Representation

section Restrict

variable {k : Type} [Field k] {G H : Type} [Monoid G] [Monoid H]

@[expose] def frepComp (φ : H →* G) (Q : FRep k G) : FRep k H := ⟨Q.V, Q.ρ.comp φ⟩

@[expose] def intertwiningComp (φ : H →* G) {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (ι : IntertwiningMap ρ σ) : IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := ι.toLinearMap
  isIntertwining' h := ι.isIntertwining' (φ h)

@[expose] def equivComp (φ : H →* G) {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (e : Representation.Equiv ρ σ) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => by
    have := e.toIntertwiningMap.isIntertwining' (φ h)
    exact this)

theorem flagTop_comp (φ : H →* G) : ∀ (L : List (FRep k G)) {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k G V), FlagTop ρ L →
      FlagTop (ρ.comp φ) (L.map (frepComp φ))
  | [], _, _, _, _, h => h
  | _ :: L, _, _, _, _, ⟨V', _, _, _, ρ', ι, π, hι, hπ, hex, hL⟩ =>
    ⟨V', inferInstance, inferInstance, inferInstance, ρ'.comp φ, intertwiningComp φ ι,
      intertwiningComp φ π, hι, hπ, hex, flagTop_comp φ L ρ' hL⟩

end Restrict

section Sz

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

@[expose] noncomputable def szIncl (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ↥(suzukiGroup a K) →* antiSp K :=
  Subgroup.inclusion (suzukiGroup_le_antiSp hK)

theorem coe_szIncl (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : ↥(suzukiGroup a K)) :
    ((szIncl hK g : antiSp K) : GL (Fin 4) K) = (g : GL (Fin 4) K) := rfl

theorem szIncl_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (szIncl hK) :=
  Subgroup.inclusion_injective _

omit [CharP K 2] in
theorem pow_two_pow_mod {f : ℕ} (hK : Nat.card K = 2 ^ f) (x : K) (n : ℕ) :
    x ^ 2 ^ n = x ^ 2 ^ (n % f) := by
  have hq : x ^ 2 ^ f = x := by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hmul : ∀ q : ℕ, x ^ 2 ^ (f * q) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hq]
  conv_lhs => rw [← Nat.div_add_mod n f, pow_add, pow_mul, hmul]

variable (k : Type) [Field k] [Algebra K k]

theorem natRepS_szIncl (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : ℕ)
    (g : ↥(suzukiGroup a K)) :
    natRepS k i (szIncl hK g) =
      (glMat (g : GL (Fin 4) K)).map fun x => algebraMap K k (x ^ 2 ^ ((a + 1) * i)) := by
  rw [natRepS_apply, glMat_minorAut_pow_of_mem hK i (g := szIncl hK g) g.2, Matrix.map_map]
  rfl

theorem natRepS_szIncl_eq (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i j : ℕ} (hij : (a + 1) * i % (2 * a + 1) = (a + 1) * j % (2 * a + 1))
    (g : ↥(suzukiGroup a K)) : natRepS k i (szIncl hK g) = natRepS k j (szIncl hK g) := by
  rw [natRepS_szIncl, natRepS_szIncl]
  ext x y
  simp only [Matrix.map_apply]
  rw [pow_two_pow_mod hK, hij, ← pow_two_pow_mod hK]

@[expose] def szFold (a i : ℕ) : ℕ := 2 * ((a + 1) * i % (2 * a + 1))

theorem natRepS_szIncl_fold (hK : Nat.card K = 2 ^ (2 * a + 1))
    (i : ℕ) (g : ↥(suzukiGroup a K)) :
    natRepS k (szFold a i) (szIncl hK g) = natRepS k i (szIncl hK g) := by
  refine natRepS_szIncl_eq k hK ?_ g
  rw [szFold]
  set c := (a + 1) * i % (2 * a + 1) with hc
  have h1 : (a + 1) * (2 * c) = c + (2 * a + 1) * c := by ring
  rw [h1, Nat.add_mul_mod_self_left, hc, Nat.mod_mod]

@[expose] def szOmega (a : ℕ) : Finset ℕ := (Finset.range (2 * a + 1)).image (2 * ·)

theorem mem_szOmega {i : ℕ} : i ∈ szOmega a ↔ ∃ c < 2 * a + 1, 2 * c = i := by
  simp [szOmega]

theorem szFold_mem (i : ℕ) : szFold a i ∈ szOmega a :=
  mem_szOmega.mpr ⟨_, Nat.mod_lt _ (by omega), rfl⟩

theorem szOmega_subset : szOmega a ⊆ Finset.range (2 * (2 * a + 1)) := by
  intro i hi
  obtain ⟨c, hc, rfl⟩ := mem_szOmega.mp hi
  simp only [Finset.mem_range]
  omega

theorem card_szOmega : (szOmega a).card = 2 * a + 1 := by
  rw [szOmega, Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_range]

@[expose] noncomputable def szT (hK : Nat.card K = 2 ^ (2 * a + 1)) (A : Finset ℕ) :
    ↥(suzukiGroup a K) →* Matrix (A → Fin 4) (A → Fin 4) k :=
  (tensorRepS (F := K) k A).comp (szIncl hK)

@[expose] noncomputable def szN (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : ℕ) :
    ↥(suzukiGroup a K) →* Matrix (Fin 4) (Fin 4) k :=
  (natRepS (F := K) k i).comp (szIncl hK)

theorem szT_apply (hK : Nat.card K = 2 ^ (2 * a + 1)) (A : Finset ℕ) (g : ↥(suzukiGroup a K)) :
    szT k hK A g = tensorRepS (F := K) k A (szIncl hK g) := rfl

theorem szN_apply (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : ℕ) (g : ↥(suzukiGroup a K)) :
    szN k hK i g = natRepS (F := K) k i (szIncl hK g) := rfl

theorem szInsert_nonempty (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : Finset ℕ} {i : ℕ}
    (hi : i ∉ A) :
    Nonempty (Representation.Equiv (tprod (matRep (szT k hK A)) (matRep (szN k hK i)))
      (matRep (szT k hK (insert i A)))) := by
  obtain ⟨e⟩ := tensorInsert_nonempty (F := K) k hi
  exact ⟨equivComp (szIncl hK) e⟩

@[expose] noncomputable def szFoldEquiv
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : ℕ) :
    Representation.Equiv (matRep (szN k hK (szFold a i))) (matRep (szN k hK i)) :=
  Representation.Equiv.mk (LinearEquiv.refl k _) (fun g => by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply, matRep_apply,
      szN_apply, natRepS_szIncl_fold])

theorem szSquare_filtration [CharP k 2] (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : ℕ) :
    FlagTop (tprod (matRep (szN k hK i)) (matRep (szN k hK i)))
      ([trivFRep (F := K) k, NFRep k (i + 1), trivFRep k, NFRep k (i + 2), trivFRep k,
        NFRep k (i + 1), trivFRep k].map (frepComp (szIncl hK))) :=
  flagTop_comp (szIncl hK) _ _ (fundamental_tensor_square_filtration (F := K) k i)

end Sz

end B45Sz

end CFSG.Quasithin
