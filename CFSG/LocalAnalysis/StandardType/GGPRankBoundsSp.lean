module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.RankThree.PartTwo.Sec4.Item413Classical
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.SimpleCase
import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.StandardType

namespace PRankBounds

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Aut

theorem eq_zero_or_eq_one_galoisField_two (x : GaloisField 2 1) : x = 0 ∨ x = 1 :=
  CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one x

theorem ringEquiv_galoisField_two_eq_one (σ : GaloisField 2 1 ≃+* GaloisField 2 1) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_galoisField_two x with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

theorem exists_conj_of_mulAut_spTwo {r : ℕ} (hr : 3 ≤ r)
    (β : MulAut (StatedSp r (GaloisField 2 1))) :
    ∃ s : StatedSp r (GaloisField 2 1), ∀ g, β g = s * g * s⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero r := ⟨by omega⟩
  have hbij : Function.Bijective (proj r (GaloisField 2 1)) :=
    UnitaryHigher.proj_bijective_of_charTwo
  let ψ : StatedSp r (GaloisField 2 1) ≃* StatedProj (StatedSp r (GaloisField 2 1)) :=
    MulEquiv.ofBijective (proj r (GaloisField 2 1)) hbij
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := r) (K := GaloisField 2 1) hr).2
    (MulAut.congr ψ β)
  rw [ringEquiv_galoisField_two_eq_one σ, map_one, mul_one] at hα
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, fun g => ?_⟩
  apply hbij.1
  have h2 := congrArg (fun φ : MulAut (StatedProj (StatedSp r (GaloisField 2 1))) =>
    φ (proj r (GaloisField 2 1) g)) hα
  simp only [hs, conjAut_proj] at h2
  have h3 : (MulAut.congr ψ β) (proj r (GaloisField 2 1) g) = proj r (GaloisField 2 1) (β g) := by
    have hg : ψ.symm (proj r (GaloisField 2 1) g) = g := ψ.symm_apply_apply g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hg]
    rfl
  rw [← h3, h2]
  congr 1

theorem normalizer_range_eq_of_spTwo {G : Type} [Group G] {r : ℕ} (hr : 3 ≤ r)
    (ψ : StatedSp r (GaloisField 2 1) →* G) (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    Subgroup.normalizer (ψ.range : Set G) = ψ.range := by
  refine le_antisymm (fun m hm => ?_) Subgroup.le_normalizer
  have hm' : m⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := inv_mem hm
  have hconj : ∀ (x : G) (g : StatedSp r (GaloisField 2 1)),
      x ∈ Subgroup.normalizer (ψ.range : Set G) → ∃ g', ψ g' = x * ψ g * x⁻¹ :=
    fun x g hx => (Subgroup.mem_normalizer_iff.mp hx (ψ g)).mp ⟨g, rfl⟩
  choose f hf using fun g => hconj m g hm
  choose f' hf' using fun g => hconj m⁻¹ g hm'
  have hff' : ∀ g, f (f' g) = g := fun g => hψ (by rw [hf, hf']; group)
  have hf'f : ∀ g, f' (f g) = g := fun g => hψ (by rw [hf', hf]; group)
  let β : MulAut (StatedSp r (GaloisField 2 1)) :=
    { toFun := f
      invFun := f'
      left_inv := hf'f
      right_inv := hff'
      map_mul' := fun a b => hψ (by rw [hf, map_mul, map_mul, hf, hf]; group) }
  obtain ⟨s, hs⟩ := exists_conj_of_mulAut_spTwo hr β
  have hcent : (ψ s)⁻¹ * m ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    have h1 : m * ψ g * m⁻¹ = ψ s * ψ g * (ψ s)⁻¹ := by
      rw [← hf g, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg ψ (hs g)
    calc ψ g * ((ψ s)⁻¹ * m) = (ψ s)⁻¹ * (ψ s * ψ g * (ψ s)⁻¹) * m := by group
      _ = (ψ s)⁻¹ * (m * ψ g * m⁻¹) * m := by rw [h1]
      _ = (ψ s)⁻¹ * m * ψ g := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact ⟨s, hcent⟩

end Aut

section Rank

theorem three_ne_zero_galoisField_two : (3 : GaloisField 2 1) ≠ 0 := by
  have h2 : (2 : GaloisField 2 1) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 2 1) 2
  have h3 : (3 : GaloisField 2 1) = 1 := by linear_combination h2
  rw [h3]
  exact one_ne_zero

open Matrix in
theorem card_le_of_isElemAbelian_spSix {E : Subgroup (StatedSp 3 (GaloisField 2 1))}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  set P := E.map (StatedSp 3 (GaloisField 2 1)).subtype with hPdef
  have hP : P ≤ Subgroup.closure {A : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1) |
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))ᵀ *
        CFSG.Assembly.RankThreeEven.sympForm 3 (GaloisField 2 1) *
          (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) =
        CFSG.Assembly.RankThreeEven.sympForm 3 (GaloisField 2 1)} := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨x, hx⟩ ⟨y, hy⟩)
    change ((x * y : StatedSp 3 (GaloisField 2 1)) : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) =
      ((y * x : StatedSp 3 (GaloisField 2 1)) : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1))
    exact congrArg Subtype.val h
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change ((x ^ 3 : StatedSp 3 (GaloisField 2 1)) : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) = 1
    rw [hE.2 x hx]
    rfl
  have h := CFSG.RankThree.PartTwo.Sec4.card_sq_le_of_mem_closure_sp
    three_ne_zero_galoisField_two P hP hcomm hexp
  rw [hPdef, Subgroup.card_map_of_injective Subtype.coe_injective] at h
  norm_num at h ⊢
  nlinarith [h]

@[expose] def GGSpEightTwoLocalThreeInput : Prop :=
  ∀ E T : Subgroup (StatedSp 4 (GaloisField 2 1)), IsElemAbelian 3 E → 3 ^ 4 ≤ Nat.card E →
    T ≠ ⊥ → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set (StatedSp 4 (GaloisField 2 1))) → False

end Rank

end PRankBounds

open PRankBounds in
theorem ggSpSixEightRankInput_of_eight (h8 : GGSpEightTwoLocalThreeInput) :
    GGSpSixEightRankInput := by
  intro G _ _ n ψ hn hψ hC h4
  obtain ⟨E, T, hEM, hE, h81, hTM, hT1, hT2, hET⟩ := h4
  have hN := normalizer_range_eq_of_spTwo (by omega : 3 ≤ n) ψ hψ hC
  rw [hN] at hEM hTM
  have hE' := isElemAbelian_comap_of_inj ψ hψ hE
  have hcardE : Nat.card (E.comap ψ) = Nat.card E := by
    rw [← Subgroup.card_map_of_injective hψ, Subgroup.map_comap_eq_self hEM]
  have hT'1 : T.comap ψ ≠ ⊥ := fun h => hT1 (by
    rw [← Subgroup.map_comap_eq_self hTM, h, Subgroup.map_bot])
  have hT'2 : IsPGroup 2 (T.comap ψ) := hT2.comap_of_injective ψ hψ
  have hET' := comap_le_normalizer_comap ψ hET
  rcases hn with rfl | rfl
  · have h27 := card_le_of_isElemAbelian_spSix hE'
    have h34 : (3 : ℕ) ^ 3 < 3 ^ 4 := by norm_num
    omega
  · exact h8 _ _ hE' (hcardE ▸ h81) hT'1 hT'2 hET'

end CFSG.StandardType
