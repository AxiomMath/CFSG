module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenFlags
public import CFSG.LieType.BorelTits.Symplectic
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank

section SL

variable {K : Type} [Field K]

@[expose] noncomputable def slRep (n : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K →* Module.End K (Fin n → K) where
  toFun g := Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl

theorem slRep_apply {n : ℕ} (g : SpecialLinearGroup (Fin n) K) :
    slRep n K g = Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem slRep_injective (n : ℕ) : Function.Injective (slRep n K) := fun _ _ hgh =>
  Subtype.ext (Matrix.toLin'.injective hgh)

theorem det_slRep {n : ℕ} (g : SpecialLinearGroup (Fin n) K) : LinearMap.det (slRep n K g) = 1 := by
  rw [slRep_apply, LinearMap.det_toLin']
  exact g.2

theorem exists_slRep_eq_smul {n : ℕ} {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) : ∃ c : K, slRep n K z = c • 1 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  refine ⟨c, ?_⟩
  rw [slRep_apply, ← hc, Matrix.scalar_apply, ← smul_one_eq_diagonal, map_smul,
    Matrix.toLin'_one]
  rfl

theorem coprime_card_center_SL [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K))) 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp x.2
  have hx2 : ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    have := congrArg (fun y : Subgroup.center (SpecialLinearGroup (Fin n) K) =>
      ((y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) this
    simpa using this
  have hc2 : c * c = 1 := by
    have := congrFun (congrFun hx2 ⟨0, hn⟩) ⟨0, hn⟩
    rw [← hc, pow_two, Matrix.scalar_apply, diagonal_mul_diagonal, diagonal_apply_eq] at this
    simpa using this
  have hc1 : c = 1 := eq_one_of_mul_self_eq_one hc2
  have : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem mem_fixSpace_of_mem_normalizer {X V : Type*} [Group X] [AddCommGroup V] [Module K V]
    (ρ : X →* Module.End K V) {P : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (P : Set X)) {w : V} (hw : w ∈ fixSpace (ρ.comp P.subtype)) :
    ρ x w ∈ fixSpace (ρ.comp P.subtype) := by
  intro g
  have hg : x⁻¹ * g * x ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) g).mp g.2
    simpa using this
  have h1 := hw ⟨x⁻¹ * g * x, hg⟩
  change ρ g (ρ x w) = ρ x w
  change ρ (x⁻¹ * g * x) w = w at h1
  calc ρ g (ρ x w) = ρ x (ρ (x⁻¹ * g * x) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ x w := by rw [h1]

theorem fixSpace_ne_top {X V : Type*} [Group X] [AddCommGroup V] [Module K V]
    {ρ : X →* Module.End K V} (hρ : Function.Injective ρ) {P : Subgroup X} (hP : P ≠ ⊥) :
    fixSpace (ρ.comp P.subtype) ≠ ⊤ := by
  intro htop
  apply hP
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply hρ
  rw [map_one]
  ext v
  have : v ∈ fixSpace (ρ.comp P.subtype) := htop ▸ Submodule.mem_top
  exact this ⟨g, hg⟩

theorem localRank_three_PSL_two_le [Finite K] [CharP K 2] :
    localRank 3 (ProjectiveSpecialLinearGroup (Fin 2) K) ≤ 2 := by
  refine localRank_quotient_le_of_central _ le_rfl (coprime_card_center_SL (by norm_num))
    Nat.prime_three fun P _ _ E hZE _ h3 hcomm => ?_
  have hZ : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K), z = 1 := by
    intro z hz
    obtain ⟨c, hc2, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [Fintype.card_fin, pow_two] at hc2
    apply Subtype.ext
    rw [← hc, eq_one_of_mul_self_eq_one hc2, map_one]
    rfl
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) K)) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    exact fun z hz => (Subgroup.mem_bot).mpr (hZ z hz)
  have hab : ∀ x y : E, x * y = y * x := by
    intro x y
    have := hZ _ (hcomm x x.2 y y.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  let := commGroupOfCommute E hab
  have hle := card_le_three_of_det_eq_one (A := E) (fun x => Subtype.ext (hZ _ (h3 x x.2)))
    ((slRep 2 K).comp E.subtype) ((slRep_injective 2).comp Subtype.val_injective)
    (fun x => det_slRep _) (by rw [Module.finrank_fin_fun])
  rw [hcard, mul_one]
  omega

theorem localRank_three_PSL_three_le [Finite K] [CharP K 2] :
    localRank 3 (ProjectiveSpecialLinearGroup (Fin 3) K) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine localRank_quotient_le_of_central _ le_rfl (coprime_card_center_SL (by norm_num))
    Nat.prime_three fun P hP0 hP2 E _ hEN h3 hcomm => ?_
  set W := fixSpace ((slRep 3 K).comp P.subtype)
  have hW0 : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero (slRep 3 K) 2 P hP2
    intro hbot
    have : v ∈ W := fun g => hv g g.2
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  have h := card_le_of_central_dim_three (slRep 3 K) (slRep_injective 3) det_slRep
    (Module.finrank_fin_fun K) _ (fun z hz => exists_slRep_eq_smul hz) h3 hcomm
    (W := W) (fun x hx w hw => mem_fixSpace_of_mem_normalizer _ (hEN hx) hw) hW0
    (fixSpace_ne_top (slRep_injective 3) hP0)
  calc Nat.card E ≤ 9 * Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) := h
    _ = 3 ^ 2 * Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) := by norm_num

theorem card_SL_five_two : Nat.card (SpecialLinearGroup (Fin 5) (GaloisField 2 1)) = 9999360 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero]
  decide

theorem localRank_three_PSL_five_two_le :
    localRank 3 (ProjectiveSpecialLinearGroup (Fin 5) (GaloisField 2 1)) ≤ 2 := by
  refine localRank_le_of_pRank_le Nat.prime_three (pRank_le_two_of_not_dvd Nat.prime_three ?_)
  intro h
  have := h.trans (Subgroup.card_quotient_dvd_card _)
  rw [card_SL_five_two] at this
  exact absurd this (by decide)

end SL

section Sp

variable {K : Type} [Field K]

open CFSG.LieType.BorelTits

theorem eq_one_of_mem_statedScalars_statedSp [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {x : StatedSp n K} (hx : x ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) :
    x = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hx
  have hJ := transpose_mul_mul_of_mem_statedSp x.2
  rw [← hc, GeneralLinearGroup.coe_scalar] at hJ
  have hentry := congrFun (congrFun hJ (.inl ⟨0, hn⟩)) (.inr ⟨0, hn⟩)
  simp [Matrix.scalar_apply, spJ] at hentry
  have hc1 : (c : K) = 1 := eq_one_of_mul_self_eq_one (by simpa [pow_two] using hentry)
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]

theorem det_natRep_statedSp [CharP K 2] {n : ℕ} (g : StatedSp n K) :
    LinearMap.det (natRep (StatedSp n K) g) = 1 := by
  have hJ := transpose_mul_mul_of_mem_statedSp g.2
  have hdet := congrArg Matrix.det hJ
  rw [det_mul, det_mul, det_transpose] at hdet
  have hJ0 : (spJ n K).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (spJ_mul_spJ n K)
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := ((g : GL (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  have hg : A.det * A.det = 1 := by
    have : A.det * A.det * (spJ n K).det = 1 * (spJ n K).det := by
      rw [one_mul]
      linear_combination hdet
    exact mul_right_cancel₀ hJ0 this
  change LinearMap.det (Matrix.toLin' A) = 1
  rw [LinearMap.det_toLin']
  exact eq_one_of_mul_self_eq_one hg

theorem localRank_three_statedSp_two_le [Finite K] [CharP K 2] :
    localRank 3 (StatedProj (StatedSp 2 K)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := StatedSp 2 K
  set Z := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H
  have hZ1 : ∀ z ∈ Z, z = 1 := fun z hz => eq_one_of_mem_statedScalars_statedSp (by norm_num) hz
  have hcardZ : Nat.card Z = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    exact fun z hz => (Subgroup.mem_bot).mpr (hZ1 z hz)
  have hZc : Z ≤ Subgroup.center H := by
    intro z hz
    rw [hZ1 z hz]
    exact Subgroup.one_mem _
  refine localRank_quotient_le_of_central Z hZc (by rw [hcardZ]; norm_num) Nat.prime_three
    fun P hP0 hP2 E _ hEN h3 hcomm => ?_
  have hab : ∀ x y : E, x * y = y * x := by
    intro x y
    have := hZ1 _ (hcomm x x.2 y y.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  let := commGroupOfCommute E hab
  set F := spForm 2 K
  set ρ := natRep H
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSp 2 K
  have hle := card_le_nine_of_isotropic (A := E) (fun x => Subtype.ext (hZ1 _ (h3 x x.2)))
    (ρ.comp E.subtype) ((natRep_injective H).comp Subtype.val_injective)
    (fun x => det_natRep_statedSp _)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]) F
    (fun x u v => hρ x u v) (W := isoSeq F ρ P 1)
    (fun x w hw => apply_mem_isoSeq F ρ hρ P 1 (hEN x.2) hw)
    (isoSeq_one_ne_bot F ρ 2 hρ (natRep_injective H) P hP2 hP0)
    (isoSeq_isTotallyIsotropic F ρ P 1)
  rw [hcardZ, mul_one]
  omega

end Sp

end CFSG.RankThree.PartTwo.Census
