module

public import CFSG.Sporadic.Schreier.Co1EigenModules
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public import CFSG.Sporadic.Schreier.Co1TernaryCodeInputs
public import Certificates.Certificate2149
public import Certificates.Certificate2133
public import Certificates.Certificate2150
public import Certificates.Certificate3024

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

@[expose] def codeRightInv : Matrix (Fin 12) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 1, 1, 1; 1, 0, 0, 1, 2, 2; 1, 1, 0, 2, 0, 0; 0, 0, 0, 2, 2, 0; 1, 1, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]

@[expose] def codeProj : Matrix (Fin 12) (Fin 6) (ZMod 3) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    1, 0, 0, 2, 1, 0; 0, 0, 0, 0, 0, 0; 1, 1, 1, 2, 1, 2; 2, 1, 2, 0, 0, 1; 2, 0, 0, 1, 1, 1;
    0, 0, 2, 2, 2, 2; 1, 1, 1, 2, 1, 0]

theorem R_eq_γ (i : Fin 6) (j : Fin 12) : R i j = γ j i := by
  have h : ∀ j : Fin 12, ∀ i : Fin 6, R i j = γ j i := by decide
  exact h j i

theorem γ_zero : ∀ j, γ j 0 = 1 := by decide

theorem R_zero : R 0 = fun _ => 1 := by
  funext j
  revert j
  decide

theorem R_mul_codeRightInv : R * codeRightInv = 1 := by decide

theorem R_mul_transpose : R * Rᵀ = 0 := by decide

theorem codeProj_decomp : codeProj * R + Rᵀ * codeRightInvᵀ = 1 := by decide

theorem mem_T_iff (v : Fin 12 → ZMod 3) : v ∈ T ↔ ∃ b : Fin 6 → ZMod 3, b ᵥ* R = v := by
  have h := Submodule.mem_span_range_iff_exists_fun (ZMod 3)
    (v := fun i : Fin 6 => (R i : Fin 12 → ZMod 3)) (x := v)
  simp only [vecMul_eq_sum]
  exact h

theorem vecMul_R_mem (b : Fin 6 → ZMod 3) : b ᵥ* R ∈ T := (mem_T_iff _).mpr ⟨b, rfl⟩

theorem vecMul_R_injective : Function.Injective fun b : Fin 6 → ZMod 3 => b ᵥ* R := by
  intro b c h
  have h' : b ᵥ* R = c ᵥ* R := h
  rw [← vecMul_one b, ← vecMul_one c, ← R_mul_codeRightInv, ← vecMul_vecMul, ← vecMul_vecMul, h']

theorem range_vecMulLinear_R : LinearMap.range (vecMulLinear R) = T := by
  ext v
  rw [LinearMap.mem_range, mem_T_iff]
  simp only [vecMulLinear_apply]

@[expose] noncomputable def codeEquiv : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] T :=
  (LinearEquiv.ofInjective (vecMulLinear R) vecMul_R_injective).trans
    (LinearEquiv.ofEq _ _ range_vecMulLinear_R)

theorem codeEquiv_apply (b : Fin 6 → ZMod 3) : (codeEquiv b : Fin 12 → ZMod 3) = b ᵥ* R := rfl

theorem finrank_T : Module.finrank (ZMod 3) T = 6 := by
  rw [← codeEquiv.finrank_eq, Module.finrank_fin_fun]

@[expose] noncomputable def eCode : E ≃* Multiplicative T :=
  eEquiv.symm.trans (AddEquiv.toMultiplicative codeEquiv.toAddEquiv)

theorem eCode_apply (b : Fin 6 → ZMod 3) (h : eProd b ∈ E) :
    ((eCode ⟨eProd b, h⟩).toAdd : Fin 12 → ZMod 3) = fun j => ∑ i, b i * γ j i := by
  have h1 : (⟨eProd b, h⟩ : E) = eEquiv (Multiplicative.ofAdd b) :=
    Subtype.ext (eEquiv_apply b).symm
  rw [h1]
  unfold eCode
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  funext j
  change (b ᵥ* R) j = _
  simp only [vecMul, dotProduct, R_eq_γ]

theorem mem_T_iff_orthogonal (v : Fin 12 → ZMod 3) : v ∈ T ↔ ∀ w ∈ T, v ⬝ᵥ w = 0 := by
  constructor
  · intro hv w hw
    obtain ⟨b, rfl⟩ := (mem_T_iff v).mp hv
    obtain ⟨c, rfl⟩ := (mem_T_iff w).mp hw
    rw [← mulVec_transpose R c, dotProduct_mulVec, vecMul_vecMul, R_mul_transpose, vecMul_zero,
      zero_dotProduct]
  · intro h
    have h0 : v ᵥ* Rᵀ = 0 := by
      rw [vecMul_transpose]
      funext i
      rw [Pi.zero_apply]
      change (fun j => R i j) ⬝ᵥ v = 0
      rw [dotProduct_comm]
      exact h (R i) (Submodule.subset_span ⟨i, rfl⟩)
    refine (mem_T_iff v).mpr ⟨v ᵥ* codeProj, ?_⟩
    have := congrArg (fun M => v ᵥ* M) codeProj_decomp
    simp only [vecMul_add, vecMul_one, ← vecMul_vecMul, h0, zero_vecMul, add_zero] at this
    exact this

theorem weight_check : ∀ n < 13,
    (Finset.univ.filter fun b : Fin 6 → ZMod 3 => (tsupp (b ᵥ* R)).card = n).card =
      weightCount n :=
  Certificates.certificate2149.1

theorem support_check : sixSupports.card = 132 ∧
    ∀ F ∈ (Finset.univ : Finset (Fin 12)).powersetCard 5,
      (sixSupports.filter fun s => F ⊆ s).card = 1 :=
  Certificates.certificate2149.2

theorem card_subtype_T (p : (Fin 12 → ZMod 3) → Prop) [DecidablePred p] :
    Nat.card {v : T // p v} =
      (Finset.univ.filter fun b : Fin 6 → ZMod 3 => p (b ᵥ* R)).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (codeEquiv.toEquiv.subtypeEquiv fun b => Iff.rfl)).symm

theorem card_weight (n : ℕ) : Nat.card {v : T // (tsupp v).card = n} = weightCount n := by
  rw [card_subtype_T (fun v => (tsupp v).card = n)]
  by_cases hn : n < 13
  · exact weight_check n hn
  · have h1 : weightCount n = 0 := by
      unfold weightCount
      split_ifs <;> omega
    rw [h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hb
    have : (tsupp (b ᵥ* R)).card ≤ 12 := (Finset.card_le_univ _).trans (by simp)
    omega

theorem mem_sixSupports (s : Finset (Fin 12)) :
    (∃ v ∈ T, s = tsupp v ∧ s.card = 6) ↔ s ∈ sixSupports := by
  unfold sixSupports
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl, h6⟩
    obtain ⟨b, rfl⟩ := (mem_T_iff v).mp hv
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h6⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b ᵥ* R, vecMul_R_mem b, rfl, (Finset.mem_filter.mp hb).2⟩

theorem ncard_sixSupports :
    Set.ncard {s : Finset (Fin 12) | ∃ v ∈ T, s = tsupp v ∧ s.card = 6} = 132 := by
  have : {s : Finset (Fin 12) | ∃ v ∈ T, s = tsupp v ∧ s.card = 6} = ↑sixSupports := by
    ext s
    exact mem_sixSupports s
  rw [this, Set.ncard_coe_finset]
  exact support_check.1

theorem existsUnique_sixSupport (F : Finset (Fin 12)) (hF : F.card = 5) :
    ∃! s : Finset (Fin 12), (∃ v ∈ T, s = tsupp v ∧ s.card = 6) ∧ F ⊆ s := by
  have h := support_check.2 F (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hF⟩)
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp h
  have hs' : s ∈ sixSupports.filter fun s => F ⊆ s := by
    rw [hs]
    exact Finset.mem_singleton_self s
  rw [Finset.mem_filter] at hs'
  refine ⟨s, ⟨(mem_sixSupports s).mpr hs'.1, hs'.2⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  have : s' ∈ sixSupports.filter fun s => F ⊆ s :=
    Finset.mem_filter.mpr ⟨(mem_sixSupports s').mp h1, h2⟩
  rw [hs] at this
  exact Finset.mem_singleton.mp this

theorem ones_mem_T : (fun _ => 1 : Fin 12 → ZMod 3) ∈ T := by
  rw [← R_zero]
  exact Submodule.subset_span ⟨0, rfl⟩

end CFSG.Sporadic.Co1Schreier
