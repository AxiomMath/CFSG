module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Torus
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

instance : Finite SU4 := inferInstance

theorem card_SU4 : Nat.card SU4 =
    (2 ^ 3) ^ 6 * (((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 3 + 1) * ((2 ^ 3) ^ 4 - 1)) := by
  rw [← Nat.card_congr equivSU4.toEquiv, CFSG.RankThree.PartTwo.Sec21.card_projSU (by norm_num)
    (by norm_num), show (4 - 1 : ℕ) = 3 from rfl,
    CFSG.RankThree.PartTwo.Sec21.ordTwistedA_three_eq (by norm_num)]

theorem isSimpleGroup_SU4 : IsSimpleGroup SU4 :=
  have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 4 2 3) :=
    CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSU (by norm_num) (by norm_num)
  equivSU4.symm.isSimpleGroup

theorem center_SU4 : Subgroup.center SU4 = ⊥ := by
  have := isSimpleGroup_SU4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center SU4) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative SU4 :=
      ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a⟩⟩
    have hp := (Group.is_simple_iff_prime_card (α := SU4)).mp isSimpleGroup_SU4
    rw [card_SU4] at hp
    norm_num at hp

theorem mem_Dstd_of_isDiag {x : SU4}
    (hd : (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).IsDiag) (hx3 : x ^ 3 = 1) :
    x ∈ Dstd := by
  set M : Matrix (Fin 4) (Fin 4) K := ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  have hMd : diagonal (fun k => M k k) = M := hd.diagonal_diag
  have h3 : M ^ 3 = 1 := by
    have h := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hx3
    simpa using h
  have hcube : ∀ k, M k k ^ 3 = 1 := by
    intro k
    rw [← hMd, diagonal_pow] at h3
    have := congrFun (congrFun h3 k) k
    rwa [diagonal_apply_eq, one_apply_eq] at this
  have hne : ∀ k, M k k ≠ 0 := fun k h0 => by
    have := hcube k
    rw [h0] at this
    norm_num at this
  have hdet : ∏ k, M k k = 1 := by
    have := ((mem_SUid_iff (σ := σ4)).mp x.2).1
    rw [← hM] at this
    rwa [← hMd, det_diagonal] at this
  let u : Fin 3 → μ3 := fun i =>
    ⟨Units.mk0 (M i.castSucc i.castSucc) (hne _), (mem_rootsOfUnity 3 _).mpr
      (Units.ext (by simpa using hcube i.castSucc))⟩
  refine ⟨u, Subtype.ext (Units.ext ?_)⟩
  rw [coe_torusSU4, ← hM, ← hMd]
  congr 1
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [torusSnoc_last]
    have h1 : (∏ k, M k k) = (∏ i : Fin 3, M i.castSucc i.castSucc) * M (Fin.last 3) (Fin.last 3) :=
      Fin.prod_univ_castSucc _
    rw [hdet] at h1
    rw [Units.val_inv_eq_inv_val, Units.coe_prod]
    exact (inv_eq_of_mul_eq_one_right h1.symm)
  · rw [torusSnoc_castSucc]
    rfl

theorem exists_isPrimitiveRoot_three : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_K]; norm_num)
  have hprim : IsPrimitiveRoot ξ 3 := by
    have := IsPrimitiveRoot.orderOf ξ
    rwa [hξ] at this
  exact ⟨ξ, IsPrimitiveRoot.coe_units_iff.mpr hprim⟩

theorem SU4_le_primeFormUnitary :
    SUid σ4 4 ≤ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [SU4_eq_gramSU]
  exact fun g hg => hg.1

theorem exists_conj_isDiag {P : Subgroup SU4} (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hpow : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ g : SU4, ∀ x ∈ P,
      ((((g * x * g⁻¹ : SU4) : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  set ι : SU4 →* primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    Subgroup.inclusion SU4_le_primeFormUnitary with hι
  have hι_inj : Function.Injective ι := Subgroup.inclusion_injective _
  have hGcomm : ∀ x ∈ P.map ι, ∀ y ∈ P.map ι, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hGpow : ∀ x ∈ P.map ι, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  obtain ⟨Pm, hPm⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m hK hζ
    (by norm_num : 3 ∣ 2 ^ 3 + 1) (P.map ι) hGcomm hGpow
  obtain ⟨g₀, hg₀⟩ := exists_SU4_conj_eq (A := ((Pm⁻¹ : _) : GL (Fin 4) K)) (Pm⁻¹).2
  refine ⟨g₀, fun x hx => ?_⟩
  have h1 := hPm (ι x) (Subgroup.mem_map_of_mem _ hx)
  have h2 : (((g₀ * x * g₀⁻¹ : SU4) : GL (Fin 4) K)) =
      ((Pm⁻¹ * ι x * Pm : primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
        GL (Fin 4) K) := by
    have := hg₀ (x : GL (Fin 4) K)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at this ⊢
    rw [← this]
    rfl
  rw [h2]
  exact h1

theorem exists_map_conj_Dstd {P : Subgroup SU4} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hcard : Nat.card P = 27) : ∃ g : SU4, P = Dstd.map (MulAut.conj g).toMonoidHom := by
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hg⟩ := exists_conj_isDiag hcomm (fun x hx => hP.2 x hx)
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ Dstd := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_Dstd_of_isDiag (hg x hx) ?_
    change (g * x * g⁻¹) ^ 3 = 1
    rw [conj_pow, hP.2 x hx, mul_one, mul_inv_cancel]
  have hcard' : Nat.card Dstd ≤ Nat.card (P.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, card_Dstd]
  have heq : P.map (MulAut.conj g).toMonoidHom = Dstd := Subgroup.eq_of_le_of_card_ge hle hcard'
  refine ⟨g⁻¹, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, heq ▸ ⟨x, hx, rfl⟩, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group
  · rintro ⟨d, hd, rfl⟩
    rw [← heq] at hd
    obtain ⟨y, hy, rfl⟩ := hd
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem closure_map_conj_eq_top (g : SU4) :
    Subgroup.closure ((MulAut.conj g : SU4 ≃* SU4) '' {x : SU4 | Nat.Coprime (orderOf x) 3 ∧
      ∃ i : Fin 3, ∀ b ∈ Bsub i, b * x = x * b}) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : (MulAut.conj g).symm y ∈ Subgroup.closure {x : SU4 | Nat.Coprime (orderOf x) 3 ∧
      ∃ i : Fin 3, ∀ b ∈ Bsub i, b * x = x * b} := by
    rw [closure_coprime_centralized_eq_top]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
  rw [MonoidHom.map_closure] at h1
  have h2 : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) = y :=
    (MulAut.conj g).apply_symm_apply y
  rw [h2] at h1
  exact h1

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
