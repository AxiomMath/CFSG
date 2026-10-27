module

public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

section Transfer

variable {G : Type} [Group G] {K P K₀ U B V : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

theorem isSumOfNaturalModulesVia_transfer {φ : ↥K →* ↥Γ} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia K P K₀ φ dual k) (hPB : P ⊔ B = V) (hPiB : P ⊓ B = K₀)
    (hUV : U ≤ V) (hUB : U ⊔ B = V) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hPBn : P ≤ Subgroup.normalizer (B : Set G)) :
    IsSumOfNaturalModulesVia K U (U ⊓ B) φ dual k := by
  obtain ⟨hKP, hK₀P, β, hβs, hβk, hβc⟩ := h
  have hVB : V ≤ Subgroup.normalizer (B : Set G) := by
    rw [← hPB]
    exact sup_le hPBn Subgroup.le_normalizer
  have hPBset : ((P ⊔ B : Subgroup G) : Set G) = (P : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P B hPBn
  have hex : ∀ u : ↥U, ∃ p : ↥P, (p : G)⁻¹ * u ∈ B := by
    intro u
    have hu : (u : G) ∈ ((P ⊔ B : Subgroup G) : Set G) := by
      rw [hPB]
      exact hUV u.2
    rw [hPBset] at hu
    obtain ⟨p, hp, b, hb, hpb⟩ := hu
    refine ⟨⟨p, hp⟩, ?_⟩
    simp only
    rw [← hpb, inv_mul_cancel_left]
    exact hb
  choose pr hpr using hex
  have huniq : ∀ (u : ↥U) (p : ↥P), (p : G)⁻¹ * u ∈ B → β p = β (pr u) := by
    intro u p hp
    have hmem : (p : G)⁻¹ * (pr u : G) ∈ K₀ := by
      rw [← hPiB]
      refine ⟨P.mul_mem (P.inv_mem p.2) (pr u).2, ?_⟩
      have : (p : G)⁻¹ * (pr u : G) = ((p : G)⁻¹ * u) * ((pr u : G)⁻¹ * u)⁻¹ := by group
      rw [this]
      exact B.mul_mem hp (B.inv_mem (hpr u))
    have h1 : β (p⁻¹ * pr u) = 1 := by
      rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
      exact hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  let βU : ↥U →* Multiplicative (Fin k → ι → F) :=
    { toFun := fun u => β (pr u)
      map_one' := by
        rw [← huniq 1 1 (by simp), map_one]
      map_mul' := fun u v => by
        rw [← huniq (u * v) (pr u * pr v), map_mul]
        have : ((pr u * pr v : ↥P) : G)⁻¹ * ((u * v : ↥U) : G) =
            ((pr v : G)⁻¹ * ((pr u : G)⁻¹ * u) * (pr v : G)) * ((pr v : G)⁻¹ * v) := by
          simp only [Subgroup.coe_mul]
          group
        rw [this]
        refine B.mul_mem ?_ (hpr v)
        have := (Subgroup.mem_normalizer_iff.mp (hPBn (P.inv_mem (pr v).2)) _).mp (hpr u)
        simpa using this }
  have hβU : ∀ u, βU u = β (pr u) := fun _ => rfl
  refine ⟨hKU, inf_le_left, βU, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨p, rfl⟩ := hβs y
    have hp : (p : G) ∈ ((U ⊔ B : Subgroup G) : Set G) := by
      rw [hUB, ← hPB]
      exact Subgroup.mem_sup_left p.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U B (hUV.trans hVB)] at hp
    obtain ⟨u, hu, b, hb, hub⟩ := hp
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hβU, ← huniq ⟨u, hu⟩ p]
    simp only
    rw [← hub, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact B.inv_mem hb
  ·
    ext u
    rw [MonoidHom.mem_ker, hβU, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hp
      refine ⟨u.2, ?_⟩
      have : (u : G) = (pr u : G) * ((pr u : G)⁻¹ * u) := by group
      rw [this]
      exact B.mul_mem ((hPiB.symm ▸ hp : (pr u : G) ∈ P ⊓ B).2) (hpr u)
    · rintro ⟨-, huB⟩
      rw [← hPiB]
      refine ⟨(pr u).2, ?_⟩
      have : (pr u : G) = u * ((pr u : G)⁻¹ * u)⁻¹ := by group
      rw [this]
      exact B.mul_mem huB (B.inv_mem (hpr u))
  ·
    intro a u v huv i
    have hap : (a : G) * pr u * (a : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hKP a.2) _).mp (pr u).2
    rw [hβU, hβU, ← huniq v ⟨_, hap⟩]
    · exact hβc a (pr u) ⟨_, hap⟩ rfl i
    · simp only
      rw [huv, Subgroup.coe_inv]
      have : ((a : G) * (pr u : G) * (a : G)⁻¹)⁻¹ * ((a : G) * u * (a : G)⁻¹) =
          (a : G) * ((pr u : G)⁻¹ * u) * (a : G)⁻¹ := by group
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (hKB a.2) _).mp (hpr u)

end Transfer

section ConjSL

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]

@[expose] noncomputable def conjSL (s : SL3 F) (φ : ↥K →* ↥(StatedSL 3 F)) :
    ↥K →* ↥(StatedSL 3 F) :=
  (MulAut.conj (specialLinearGroupEquivStatedSL 3 F s)).toMonoidHom.comp φ

theorem conjSL_mat (s : SL3 F) (φ : ↥K →* ↥(StatedSL 3 F)) (a : ↥K) :
    (((conjSL s φ a : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      (s : Matrix (Fin 3) (Fin 3) F) *
        (((φ a : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
  have hinv : ((specialLinearGroupEquivStatedSL 3 F s : ↥(StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F)⁻¹ =
      ((specialLinearGroupEquivStatedSL 3 F s⁻¹ : ↥(StatedSL 3 F)) :
        Matrix.GeneralLinearGroup (Fin 3) F) := by
    rw [map_inv]
    rfl
  simp only [conjSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hinv]
  rfl

theorem toSL3_conjSL (s : SL3 F) (φ : ↥K →* ↥(StatedSL 3 F)) (a : ↥K) :
    toSL3 (conjSL s φ) a = s * toSL3 φ a * s⁻¹ := by
  apply Subtype.ext
  rw [toSL3_mat, conjSL_mat, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, toSL3_mat]

theorem conjSL_surjective {s : SL3 F} {φ : ↥K →* ↥(StatedSL 3 F)}
    (hφ : Function.Surjective φ) : Function.Surjective (conjSL s φ) :=
  (MulAut.conj (specialLinearGroupEquivStatedSL 3 F s)).surjective.comp hφ

theorem isSumOfNaturalModulesVia_conjSL {φ : ↥K →* ↥(StatedSL 3 F)}
    (h : IsSumOfNaturalModulesVia K V Z φ false 1) (s : SL3 F) :
    IsSumOfNaturalModulesVia K V Z (conjSL s φ) false 1 := by
  obtain ⟨hKV, hZV, β, hβs, hβk, hβc⟩ := h
  have hss : ∀ x : Fin 3 → F, (s : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hss' : ∀ x : Fin 3 → F, ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  let mA : (Fin 1 → Fin 3 → F) →+ (Fin 1 → Fin 3 → F) :=
    { toFun := fun x i => (s : Matrix (Fin 3) (Fin 3) F) *ᵥ x i
      map_zero' := by
        funext i
        simp
      map_add' := fun x y => by
        funext i
        simp [Matrix.mulVec_add] }
  have hmA : ∀ x i, mA x i = (s : Matrix (Fin 3) (Fin 3) F) *ᵥ x i := fun _ _ => rfl
  let m : Multiplicative (Fin 1 → Fin 3 → F) →* Multiplicative (Fin 1 → Fin 3 → F) :=
    AddMonoidHom.toMultiplicative mA
  have hm : ∀ x, Multiplicative.toAdd (m x) = mA (Multiplicative.toAdd x) := fun _ => rfl
  have hm_inj : Function.Injective m := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    have h1 := congrFun (congrArg Multiplicative.toAdd hxy) i
    rw [hm, hm, hmA, hmA] at h1
    have h2 := congrArg (fun w => ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) h1
    simp only [hss'] at h2
    exact h2
  refine ⟨hKV, hZV, m.comp β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd fun i =>
      ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd y i)
    refine ⟨v, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [MonoidHom.comp_apply, hm, hv, hmA]
    exact hss _
  · rw [← hβk]
    ext v
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h1
      exact hm_inj (h1.trans (map_one m).symm)
    · intro h1
      rw [h1, map_one]
  · intro a u v huv i
    have h1 := hβc a u v huv i
    simp only [moduleAct, Bool.false_eq_true, ite_false] at h1 ⊢
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hm, hm, hmA, hmA, h1, conjSL_mat,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.SpecialLinearGroup.coe_mul s⁻¹ s, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one]

end ConjSL

end CFSG.Quasithin.MS93.S4A
