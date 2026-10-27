module

public import CFSG.Quasithin.MS93.S34Lin
public import CFSG.Quasithin.MS93.MSPNorm
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open Matrix

variable {G : Type} [Group G]

section Normalizing

variable {V Z A : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {β : ↥V →* Multiplicative (Fin 1 → ι → F)} {Γ : Subgroup (GL ι F)}

theorem IsCoordAct.normalizes {α : ↥A →* ↥Γ} (hα : Function.Surjective α)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hβ : Function.Surjective β)
    (hβα : ∀ a : ↥A, IsCoordAct β a ((α a : GL ι F) : Matrix ι ι F).mulVec) {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    {γ : GL ι F} (hγ : IsCoordAct β t (γ : Matrix ι ι F).mulVec) (g : ↥Γ) :
    ∃ g' : ↥Γ, ∀ v : ι → F, (γ : Matrix ι ι F) *ᵥ ((g : GL ι F) : Matrix ι ι F) *ᵥ v =
      ((g' : GL ι F) : Matrix ι ι F) *ᵥ (γ : Matrix ι ι F) *ᵥ v := by
  obtain ⟨a, rfl⟩ := hα g
  have hta : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 htA a).1 a.2
  refine ⟨α ⟨_, hta⟩, fun v => ?_⟩
  have h1 := ((hγ.mul (hAV a.2) (hβα a)).mul (inv_mem htV) hγ.inv)
  have h2 := hβα ⟨_, hta⟩
  have heq := IsCoordAct.unique hβ (hAV hta) h1 h2
  have := congrFun heq ((γ : Matrix ι ι F) *ᵥ v)
  simp only [Function.comp_apply] at this
  have hv : ((γ⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ ((γ : Matrix ι ι F) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec]
    simp
  rw [← this, hv]

end Normalizing

section SL3

variable [Finite G] {M T L : Subgroup G}

theorem PUHyp.sl3Full_of_gl (h : PUHyp M T L) {n : ℕ} {F : Type} [Field F] [Fintype F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hcard : Fintype.card F = 2 ^ n) (hα : Function.Surjective α)
    (hX : Xq M = Zq M L ⊔ Uq M T L) (hZU : Zq M L ⊓ Uq M T L = ⊥)
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)} (hβ : Function.Surjective β)
    (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (a : ↥L) (u v : ↥(Uq M T L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    (hGL : ∀ t ∈ T, ∃ γ : GL (Fin 3) F, IsCoordAct β t (γ : Matrix (Fin 3) (Fin 3) F).mulVec) :
    IsSL3Full M T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  have hT : ∀ t ∈ T, ∃ γ : ↥(StatedSL 3 F),
      IsCoordAct β t ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec := by
    intro t ht
    obtain ⟨γ, hγ⟩ := hGL t ht
    obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
    have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have hdet := det_eq_one_of_isCoordAct hβ (hTV ht) he' hγ
    exact ⟨⟨γ, Subgroup.subset_closure hdet⟩, hγ⟩
  obtain ⟨α', hα', hnat⟩ := exists_natural_of_coordAct h.eq_sup hα hLV bot_le hβ hβker hβα hTV hT
  exact ⟨hX, hZU, n, F, inferInstance, inferInstance, α', hcard, hα', hnat⟩

end SL3

section Sp4

variable {M T L : Subgroup G}

theorem exists_sp4_of_gl {V : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    {α : ↥L →* ↥(StatedSp 2 F)} (hα : Function.Surjective α)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {β : ↥V →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)} (hβ : Function.Surjective β)
    (hβα : ∀ a : ↥L, IsCoordAct β a ((α a : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec)
    {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htL : t ∈ Subgroup.normalizer (L : Set G)) {e : ℕ} (hte : t ^ 2 ^ e = 1)
    {γ : GL (Fin 2 ⊕ Fin 2) F}
    (hγ : IsCoordAct β t (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec) :
    ∃ g : ↥(StatedSp 2 F), IsCoordAct β t ((g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec := by
  have : Finite (MSP.Sp4 F) := Subtype.finite
  let Tγ : MSP.V4 F →+ MSP.V4 F :=
    (Matrix.mulVecLin (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)).toAddMonoidHom
  have hTγ : ∀ v, Tγ v = (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v := fun v => rfl
  have hbij : Function.Bijective Tγ := by
    refine ⟨fun u v huv => ?_, fun w => ⟨((γ⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w, ?_⟩⟩
    · have := congrArg (fun x => ((γ⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x) huv
      simpa [hTγ, Matrix.mulVec_mulVec] using this
    · simp [hTγ, Matrix.mulVec_mulVec]
  have hnorm : MSP.Normalizes Tγ := by
    intro g
    obtain ⟨g', hg'⟩ := IsCoordAct.normalizes hα hLV hβ hβα htV htL hγ g
    exact ⟨g', fun v => by rw [hTγ, hTγ]; exact hg' v⟩
  have hlin : ∀ (c : F) (v : MSP.V4 F), Tγ (c • v) = c • Tγ v := fun c v => by
    rw [hTγ, hTγ, Matrix.mulVec_smul]
  have hpow : ((γ ^ 2 ^ e : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    have h := hγ.pow htV (2 ^ e)
    rw [hte] at h
    exact IsCoordAct.matrix_eq hβ (one_mem _) h isCoordAct_one_mulVec
  have hit : ∀ v : MSP.V4 F, Tγ^[2 ^ e] v = v := by
    intro v
    have key : ∀ m : ℕ, Tγ^[m] v = ((γ ^ m : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply', ih, hTγ, Matrix.mulVec_mulVec, pow_succ']
        rfl
    rw [key, hpow, Matrix.one_mulVec]
  obtain ⟨g, hg⟩ := MSP.exists_eq_mat_of_two_power hbij hnorm hlin hit
  refine ⟨g, hγ.congr fun v => ?_⟩
  rw [← hTγ, hg v]

variable [Finite G]

end Sp4

end CFSG.Quasithin.MS93
