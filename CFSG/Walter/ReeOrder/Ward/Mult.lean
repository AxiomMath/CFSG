module

public import CFSG.Walter.ReeOrder.Ward.Sections
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CharacterTransport

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.PSL2Table

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem ι_injective : Function.Injective S.ι := by
  rintro ⟨u, w⟩ ⟨u', w'⟩ h
  rw [ι_apply, ι_apply] at h
  rcases S.Z_cases u with rfl | rfl <;> rcases S.Z_cases u' with rfl | rfl
  · simp only [OneMemClass.coe_one, one_mul] at h
    rw [S.κ_inj h]
  · simp only [OneMemClass.coe_one, one_mul, Jz] at h
    exact absurd h.symm (S.J_mul_ne w' w)
  · simp only [OneMemClass.coe_one, one_mul, Jz] at h
    exact absurd h (S.J_mul_ne w w')
  · simp only [Jz, mul_right_inj] at h
    rw [S.κ_inj h]

theorem ι_mem (p : Subgroup.zpowers S.J × L) :
    S.ι p ∈ Subgroup.centralizer ({S.J} : Set G) := by
  rw [S.mem_centralizer_iff]
  rcases S.Z_cases p.1 with h | h
  · exact ⟨p.2, Or.inl (by rw [show p = (p.1, p.2) from rfl, h, ι_apply]; simp)⟩
  · exact ⟨p.2, Or.inr (by rw [show p = (p.1, p.2) from rfl, h, ι_apply]; rfl)⟩

@[expose] noncomputable def ιC : Subgroup.zpowers S.J × L →* Subgroup.centralizer ({S.J} : Set G) :=
  S.ι.codRestrict _ S.ι_mem

theorem ιC_bijective : Function.Bijective S.ιC := by
  refine ⟨fun a b h => S.ι_injective (congrArg Subtype.val h), ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨y, rfl | rfl⟩ := (S.mem_centralizer_iff g).mp hg
  · exact ⟨(1, y), Subtype.ext (by simp [ιC, ι_apply])⟩
  · exact ⟨(S.Jz, y), Subtype.ext (by simp [ιC, ι_apply, Jz])⟩

@[expose] noncomputable def eC : Subgroup.zpowers S.J × L ≃* Subgroup.centralizer ({S.J} : Set G) :=
  MulEquiv.ofBijective S.ιC S.ιC_bijective

theorem eC_apply (p : Subgroup.zpowers S.J × L) : (S.eC p : G) = S.ι p := rfl

theorem eC_symm_κ (y : L) :
    S.eC.symm ⟨S.κ y, S.κ_mem_centralizer y⟩ = (1, y) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [eC_apply, ι_apply]
  simp

theorem eC_symm_Jκ (y : L) (h : S.J * S.κ y ∈ Subgroup.centralizer ({S.J} : Set G)) :
    S.eC.symm ⟨S.J * S.κ y, h⟩ = (S.Jz, y) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [eC_apply, ι_apply]
  rfl

@[expose] noncomputable def ψ (ε : Subgroup.zpowers S.J → ℂ) (θ : L → ℂ) :
    Subgroup.centralizer ({S.J} : Set G) → ℂ :=
  outerProductCharacter ε θ ∘ S.eC.symm

theorem ψ_mem {ε : Subgroup.zpowers S.J → ℂ} (hε : ε ∈ BlocksIrr (Subgroup.zpowers S.J))
    {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    S.ψ ε θ ∈ BlocksIrr (Subgroup.centralizer ({S.J} : Set G)) :=
  CFSG.BrauerThirdMainTheorem.Helpers.irr_comp_equiv S.eC.symm
    (outerProductCharacter_mem_blocksIrr hε hθ)

theorem ψ_one_mem {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    S.ψ 1 θ ∈ BlocksIrr (Subgroup.centralizer ({S.J} : Set G)) :=
  S.ψ_mem (one_mem_blocksIrr _) hθ

theorem ψ_sgn_mem {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    S.ψ (signChar _) θ ∈ BlocksIrr (Subgroup.centralizer ({S.J} : Set G)) :=
  S.ψ_mem (signChar_mem_blocksIrr S.card_Z) hθ

theorem ψ_κ (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) (θ : L → ℂ) (y : L) :
    S.ψ ε θ ⟨S.κ y, S.κ_mem_centralizer y⟩ = θ y := by
  simp [ψ, S.eC_symm_κ, outerProductCharacter_apply, hε]

theorem ψ_Jκ (ε : Subgroup.zpowers S.J → ℂ) (θ : L → ℂ) (y : L)
    (h : S.J * S.κ y ∈ Subgroup.centralizer ({S.J} : Set G)) :
    S.ψ ε θ ⟨S.J * S.κ y, h⟩ = ε S.Jz * θ y := by
  simp [ψ, S.eC_symm_Jκ y h, outerProductCharacter_apply]

theorem inner_eC (f g : Subgroup.centralizer ({S.J} : Set G) → ℂ) :
    BlocksInnerProduct f g = BlocksInnerProduct (f ∘ S.eC) (g ∘ S.eC) := by
  unfold BlocksInnerProduct
  rw [Nat.card_congr S.eC.toEquiv]
  congr 1
  exact (Fintype.sum_equiv S.eC.toEquiv _ _ (fun _ => rfl)).symm

@[expose] def res (χ : G → ℂ) : Subgroup.centralizer ({S.J} : Set G) → ℂ := fun h => χ h

theorem inner_res_ψ (χ : G → ℂ) (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) (θ : L → ℂ) :
    BlocksInnerProduct (S.res χ) (S.ψ ε θ) =
      (BlocksInnerProduct (S.τ χ) θ + starRingEnd ℂ (ε S.Jz) * BlocksInnerProduct (S.σ χ) θ) /
        2 := by
  rw [S.inner_eC]
  have h1 : S.res χ ∘ S.eC = χ ∘ S.ι := by
    funext p
    rfl
  have h2 : S.ψ ε θ ∘ S.eC = outerProductCharacter ε θ := by
    funext p
    simp [ψ]
  rw [h1, h2, S.inner_ι χ ε hε θ]

@[expose] noncomputable def ma (χ : G → ℂ) (θ : L → ℂ) : ℕ :=
  if h : χ ∈ BlocksIrr G ∧ θ ∈ BlocksIrr L then Classical.choose (S.mult h.1 h.2) else 0

@[expose] noncomputable def mb (χ : G → ℂ) (θ : L → ℂ) : ℕ :=
  if h : χ ∈ BlocksIrr G ∧ θ ∈ BlocksIrr L then
    Classical.choose (Classical.choose_spec (S.mult h.1 h.2)) else 0

theorem ma_mb_spec {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksInnerProduct (S.τ χ) θ = (S.ma χ θ : ℂ) + S.mb χ θ ∧
      BlocksInnerProduct (S.σ χ) θ = (S.ma χ θ : ℂ) - S.mb χ θ := by
  have h : χ ∈ BlocksIrr G ∧ θ ∈ BlocksIrr L := ⟨hχ, hθ⟩
  simp only [ma, mb, h, and_self, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (S.mult hχ hθ))

@[expose] noncomputable def M (χ : G → ℂ) (θ : L → ℂ) : ℤ := (S.ma χ θ : ℤ) - S.mb χ θ

@[expose] noncomputable def Ar (χ : G → ℂ) (θ : L → ℂ) : ℤ := (S.ma χ θ : ℤ) + S.mb χ θ

theorem inner_σ {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksInnerProduct (S.σ χ) θ = S.M χ θ := by
  rw [(S.ma_mb_spec hχ hθ).2, M]
  push_cast
  ring

theorem inner_τ {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksInnerProduct (S.τ χ) θ = S.Ar χ θ := by
  rw [(S.ma_mb_spec hχ hθ).1, Ar]
  push_cast
  ring

theorem inner_res_ψ_one {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksInnerProduct (S.res χ) (S.ψ 1 θ) = S.ma χ θ := by
  rw [S.inner_res_ψ χ 1 rfl θ, (S.ma_mb_spec hχ hθ).1, (S.ma_mb_spec hχ hθ).2]
  simp only [Pi.one_apply, map_one, one_mul]
  ring

theorem inner_res_ψ_sgn {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksInnerProduct (S.res χ) (S.ψ (signChar _) θ) = S.mb χ θ := by
  rw [S.inner_res_ψ χ _ (by simp [signChar]) θ, S.signChar_Jz, (S.ma_mb_spec hχ hθ).1,
    (S.ma_mb_spec hχ hθ).2]
  simp only [map_neg, map_one, neg_mul, one_mul]
  ring

theorem σ_expand {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (y : L) :
    S.σ χ y = ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * θ y := by
  have h := congrFun ((irreducible_character_basis L).2.2.2 (S.σ χ)
    (S.σ_class (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)))) y
  rw [Finset.sum_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  rw [Set.Finite.mem_toFinset] at hθ
  rw [Pi.smul_apply, smul_eq_mul, S.inner_σ hχ hθ]

theorem τ_expand {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (y : L) :
    S.τ χ y = ∑ θ ∈ (irreducibles_finite L).toFinset, (S.Ar χ θ : ℂ) * θ y := by
  have h := congrFun ((irreducible_character_basis L).2.2.2 (S.τ χ)
    (S.τ_class (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)))) y
  rw [Finset.sum_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  rw [Set.Finite.mem_toFinset] at hθ
  rw [Pi.smul_apply, smul_eq_mul, S.inner_τ hχ hθ]

theorem two_ma (χ : G → ℂ) (θ : L → ℂ) : 2 * (S.ma χ θ : ℤ) = S.Ar χ θ + S.M χ θ := by
  simp only [Ar, M]
  ring

theorem two_mb (χ : G → ℂ) (θ : L → ℂ) : 2 * (S.mb χ θ : ℤ) = S.Ar χ θ - S.M χ θ := by
  simp only [Ar, M]
  ring

end WardSetup

end CFSG.Walter.Ward
