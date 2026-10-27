module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 Matrix Multiplicative

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

@[expose] noncomputable def qTwoLMDivF_unitsIso (hF0 : Nat.card F0 = 4) :
    Multiplicative (ZMod 3) ≃* F0ˣ := by
  classical
  let ω : F0ˣ := Classical.choose (IsCyclic.exists_generator (α := F0ˣ))
  have hω : ∀ x : F0ˣ, x ∈ Subgroup.zpowers ω :=
    Classical.choose_spec (IsCyclic.exists_generator (α := F0ˣ))
  have hcard : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hF0]
  have hord : orderOf ω = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, hcard]
  have hmul : ∀ x y : Multiplicative (ZMod 3),
      ω ^ (toAdd (x * y)).val = ω ^ (toAdd x).val * ω ^ (toAdd y).val := by
    intro x y
    have h1 : toAdd (x * y) = toAdd x + toAdd y := rfl
    rw [h1, ZMod.val_add, ← pow_add]
    rw [pow_eq_pow_iff_modEq, hord]
    exact Nat.mod_modEq _ 3
  let f : Multiplicative (ZMod 3) →* F0ˣ :=
    { toFun := fun x => ω ^ (toAdd x).val
      map_one' := by simp
      map_mul' := hmul }
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hinj : Function.Injective f := by
    intro x y hxy
    have hmod : (toAdd x).val ≡ (toAdd y).val [MOD 3] := by
      have h := (pow_eq_pow_iff_modEq (x := ω)).mp hxy
      rwa [hord] at h
    have hx : (toAdd x).val < 3 := ZMod.val_lt _
    have hy : (toAdd y).val < 3 := ZMod.val_lt _
    have heq : (toAdd x).val = (toAdd y).val := Nat.ModEq.eq_of_lt_of_lt hmod hx hy
    exact Multiplicative.toAdd.injective (ZMod.val_injective 3 heq)
  refine MulEquiv.ofBijective f ?_
  refine Fintype.bijective_iff_injective_and_card f |>.mpr ⟨hinj, ?_⟩
  rw [show Fintype.card (Multiplicative (ZMod 3)) = 3 by decide,
    Fintype.card_units, ← Nat.card_eq_fintype_card, hF0]

@[expose] noncomputable def qTwoLMDivF_diagHom (hF0 : Nat.card F0 = 4) (m : ℕ) :
    (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0 :=
  (diagHom m).comp
    { toFun := fun f i => qTwoLMDivF_unitsIso hF0 (f i)
      map_one' := by funext i; simp
      map_mul' := by intro f g; funext i; simp }

theorem qTwoLMDivF_diagHom_coe (hF0 : Nat.card F0 = 4) {m : ℕ}
    (f : Fin m → Multiplicative (ZMod 3)) :
    ((qTwoLMDivF_diagHom hF0 m f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => ((qTwoLMDivF_unitsIso hF0 (f i) : F0ˣ) : F0)) :=
  rfl

theorem qTwoLMDivF_zpowers_oneVec_iff {m : ℕ} (f : Fin m → Multiplicative (ZMod 3)) :
    f ∈ Subgroup.zpowers (qTwoLMDivF_oneVec m) ↔ ∀ i j, f i = f j := by
  constructor
  · intro hf i j
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hf
    rw [← hk]
    simp [qTwoLMDivF_oneVec]
  · intro hf
    rcases m with _ | m
    · exact Subgroup.mem_zpowers_iff.mpr ⟨0, by funext i; exact i.elim0⟩
    · refine Subgroup.mem_zpowers_iff.mpr ⟨((toAdd (f 0)).val : ℤ), ?_⟩
      funext i
      rw [zpow_natCast]
      simp only [Pi.pow_apply, qTwoLMDivF_oneVec]
      rw [← ofAdd_nsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val]
      exact (ofAdd_toAdd (f 0)).trans (hf i 0).symm

structure QTwoDivFullTorus {m : ℕ} (hF0 : Nat.card F0 = 4)
    (δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0) : Prop where
  inj : Function.Injective δ
  diag : ∀ f, ggIsDiagMat (δ f)
  surj_diag : ∀ g : GL (Fin m) F0, ggIsDiagMat g → ∃ f, δ f = g
  perm : ∀ (σ : Equiv.Perm (Fin m)) f,
    permGL σ * δ f * (permGL σ)⁻¹ = δ (SpCoord.permAut σ f)
  const_coe : ∀ c : F0ˣ,
    ((δ (fun _ => (qTwoLMDivF_unitsIso hF0).symm c) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun _ => (c : F0))
  scalar : ∀ f, (∃ c : F0, ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun _ => c)) ↔ f ∈ Subgroup.zpowers (qTwoLMDivF_oneVec m)
  mono : ∀ u : GL (Fin m) F0, (∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      (u : Matrix (Fin m) (Fin m) F0) * ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (u : Matrix (Fin m) (Fin m) F0)) →
    ∃ ρ : Equiv.Perm (Fin m), ∀ f,
      u * (δ f : GL (Fin m) F0) = (δ (SpCoord.permAut ρ f) : GL (Fin m) F0) * u

end CFSG.StandardType.QTwo

end
