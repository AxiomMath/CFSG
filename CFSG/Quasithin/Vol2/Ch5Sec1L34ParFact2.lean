module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518D5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DLO
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin

variable {k : Type} [Field k]

@[expose] def torusDiag (ω : k) (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2], by
    rw [Matrix.det_fin_three]
    simp
    linear_combination hω⟩

theorem coe_torusDiag (ω : k) (hω : ω ^ 3 = 1) :
    ((torusDiag ω hω : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := rfl

theorem torusDiag_mem_stabilizer (ω : k) (hω : ω ^ 3 = 1) :
    torusDiag ω hω ∈ stabilizer (flagSpace 3 k 1) :=
  mem_stabilizer_flagSpace_one.mpr ⟨by simp [coe_torusDiag], by simp [coe_torusDiag]⟩

theorem torusDiag_pow_three (ω : k) (hω : ω ^ 3 = 1) : torusDiag ω hω ^ 3 = 1 := by
  rw [pow_three]
  apply Subtype.ext
  change !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * (!![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] *
    !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]) = (1 : Matrix (Fin 3) (Fin 3) k)
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hω
  · linear_combination (ω ^ 3 + 1) * hω

theorem torusDiag_mul_sq (ω : k) (hω : ω ^ 3 = 1) (hω' : (ω ^ 2) ^ 3 = 1) :
    torusDiag ω hω * torusDiag (ω ^ 2) hω' = 1 := by
  apply Subtype.ext
  change !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, (ω ^ 2) ^ 2] =
    (1 : Matrix (Fin 3) (Fin 3) k)
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hω
  · linear_combination (ω ^ 3 + 1) * hω

theorem rad_eq_commutator [CharP k 2] {ω : k} (hω : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0)
    (b c : k) :
    rad b c = rad (b * ω ^ 2) (c * ω) * torusDiag ω hω * (rad (b * ω ^ 2) (c * ω))⁻¹ *
      (torusDiag ω hω)⁻¹ := by
  have hω' : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  have hr : (rad (b * ω ^ 2) (c * ω))⁻¹ = rad (b * ω ^ 2) (c * ω) :=
    inv_eq_of_mul_eq_one_right (by
      rw [rad_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, rad_zero])
  have ht : (torusDiag ω hω)⁻¹ = torusDiag (ω ^ 2) hω' :=
    inv_eq_of_mul_eq_one_right (torusDiag_mul_sq ω hω hω')
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [hr, ht]
  apply Subtype.ext
  change !![1, b, c; 0, 1, 0; 0, 0, 1] =
    !![1, b * ω ^ 2, c * ω; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] *
      !![1, b * ω ^ 2, c * ω; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, (ω ^ 2) ^ 2]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-b * ω - b * ω ^ 2) * hω - b * hω2 + b * h2
  · linear_combination (-c * ω ^ 2 - c * ω ^ 4 - c * ω) * hω - c * hω2 + c * h2
  · linear_combination -hω
  · linear_combination (-ω ^ 3 - 1) * hω

variable (hk : Nat.card k = 4)
include hk

theorem exists_primitive_cube_root : ∃ ω : k, ω ^ 3 = 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk
  have hω3 : ω ^ 3 = 1 := pow_three_eq_one_of_ne_zero hk hω0
  refine ⟨ω, hω3, ?_⟩
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

theorem not_isPGroup_sl_two : ¬ IsPGroup 2 (SpecialLinearGroup (Fin 2) k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  intro h2
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  rw [card_sl_two hk] at hm
  have h5 : 5 ∣ 2 ^ m := hm ▸ (by norm_num : 5 ∣ 60)
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
  omega

theorem isPGroup_radP : IsPGroup 2 (radP (k := k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 4) (by rw [card_radP hk]; norm_num)

theorem oTwoUpper_projStabilizer_one :
    oTwoUpper (projStabilizer (flagSpace 3 k 1)) = projStabilizer (flagSpace 3 k 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  set P := projStabilizer (flagSpace 3 k 1) with hPdef
  refine le_antisymm (oTwoUpper_le P) ?_
  obtain ⟨ω, hω3, hω2⟩ := exists_primitive_cube_root hk
  have hodd : ∀ y : projectiveSL 3 k, y ^ 3 = 1 → Odd (orderOf y) := fun y hy =>
    (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one hy)
  have hR : radP ≤ oTwoUpper P := by
    intro x hx
    obtain ⟨b, c, rfl⟩ := mem_radP.mp hx
    rw [rad_eq_commutator hω3 hω2 b c, map_mul, map_mul, map_mul, map_inv, map_inv]
    set r := proj 3 k (rad (b * ω ^ 2) (c * ω)) with hr
    set t := proj 3 k (torusDiag ω hω3) with ht
    have htP : t ∈ P := ⟨_, torusDiag_mem_stabilizer ω hω3, rfl⟩
    have hrP : r ∈ P := ⟨_, rad_mem_stabilizer _ _, rfl⟩
    have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, torusDiag_pow_three, map_one]
    refine (oTwoUpper P).mul_mem
      (mem_oTwoUpper_of_odd (P.mul_mem (P.mul_mem hrP htP) (P.inv_mem hrP)) (hodd _ ?_))
      (mem_oTwoUpper_of_odd (P.inv_mem htP) (hodd _ ?_))
    · rw [conj_pow, ht3, mul_one, mul_inv_cancel]
    · rw [inv_pow, ht3, inv_one]
  have hs := isSimpleGroup_sl_two hk
  have hker : (leviP hk).ker = (radP (k := k)).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact leviP_eq_one_iff hk
  obtain ⟨hmap, -⟩ := map_oTwoUpper_eq_top_and_nonempty (not_isPGroup_sl_two hk) (leviP hk)
    (leviP_surjective hk) hker (isPGroup_radP hk)
  intro g hg
  have hmem : leviP hk ⟨g, hg⟩ ∈ ((oTwoUpper P).subgroupOf P).map (leviP hk) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyg⟩ := hmem
  have h1 : leviP hk (y⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
  have h2 : ((y⁻¹ * ⟨g, hg⟩ : ↥P) : projectiveSL 3 k) ∈ oTwoUpper P :=
    hR ((leviP_eq_one_iff hk).mp h1)
  have e : g = (y : projectiveSL 3 k) * ((y⁻¹ * ⟨g, hg⟩ : ↥P) : projectiveSL 3 k) := by simp
  rw [e]
  exact (oTwoUpper P).mul_mem hy h2

omit hk in
theorem mem_stabilizer_of_proj_mem {W : Submodule k (Fin 3 → k)} {g : SpecialLinearGroup (Fin 3) k}
    (hg : proj 3 k g ∈ projStabilizer W) : g ∈ stabilizer W := by
  obtain ⟨h, hh, he⟩ := hg
  have hz : h⁻¹ * g ∈ scalars 3 k := proj_eq_proj_iff.mp he
  have e : g = h * (h⁻¹ * g) := by group
  rw [e]
  exact (stabilizer W).mul_mem hh (scalars_le_stabilizer W hz)

omit hk in
@[expose] def lowerE21 : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by simp [Matrix.det_fin_three]⟩

omit hk in
theorem coe_lowerE21 :
    ((lowerE21 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, 1, 0; 0, 1, 1] := rfl

@[expose] noncomputable def alpha0Aut : MulAut (projectiveSL 3 k) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  LinearThreeFourOuter.nf (frobeniusEquiv k 2) w0GL 1 1

theorem alpha0Aut_map_projUnitriangular :
    (projUnitriangular 3 k).map (alpha0Aut hk).toMonoidHom = projUnitriangular 3 k := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  exact map_projUnitriangular_eq (fun x hx => alpha0_mem_projUnitriangular hx)

theorem map_projStabilizer_one_alpha0 :
    (projStabilizer (flagSpace 3 k 1)).map (alpha0Aut hk).toMonoidHom =
      projStabilizer (flagSpace 3 k 2) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases map_projStabilizer_mem hk (alpha0Aut_map_projUnitriangular hk) (d := 1) le_rfl
    (by norm_num) with h | h
  · exfalso
    have hx : proj 3 k lowerE21 ∈ projStabilizer (flagSpace 3 k 1) :=
      ⟨_, mem_stabilizer_flagSpace_one.mpr ⟨by simp [coe_lowerE21], by simp [coe_lowerE21]⟩, rfl⟩
    have hy : alpha0Aut hk (proj 3 k lowerE21) ∈ projStabilizer (flagSpace 3 k 1) := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hx
    have hinv : (lowerE21 : SpecialLinearGroup (Fin 3) k)⁻¹ = lowerE21 := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      change !![1, 0, 0; 0, 1, 0; 0, 1, 1] * !![1, 0, 0; 0, 1, 0; 0, 1, 1] =
        (1 : Matrix (Fin 3) (Fin 3) k)
      simp only [mul_fin_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
    change LinearThreeFourOuter.nf (frobeniusEquiv k 2) w0GL 1 1 (proj 3 k lowerE21) ∈ _ at hy
    rw [alpha0_proj] at hy
    have h10 := (mem_stabilizer_flagSpace_one.mp (mem_stabilizer_of_proj_mem hy)).1
    rw [alpha0_matrix, hinv, coe_lowerE21] at h10
    have hr0 : (Fin.rev (0 : Fin 3)) = 2 := rfl
    have hr1 : (Fin.rev (1 : Fin 3)) = 1 := rfl
    rw [hr0, hr1] at h10
    simp at h10
  · exact h

omit hk in
theorem map_radP_of_map_projStabilizer (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)}
    (hP : (projStabilizer (flagSpace 3 k 1)).map α.toMonoidHom = projStabilizer (flagSpace 3 k 1)) :
    (radP (k := k)).map α.toMonoidHom = radP := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hle : (radP (k := k)).map α.toMonoidHom ≤ radP := by
    refine le_radP_of_isPGroup hk ?_ ?_ ?_
    · rw [← hP]
      exact Subgroup.map_mono radP_le_projStabilizer
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 4) ?_
      rw [Subgroup.card_map_of_injective α.injective, card_radP hk]
      norm_num
    · intro x hx
      rw [← hP] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hyN : y ∈ Subgroup.normalizer (radP (k := k) : Set (projectiveSL 3 k)) := by
        rw [normalizer_radP hk]
        exact hy
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨y * r * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN r).mp hr, ?_⟩
        simp
      · rintro ⟨r, hr, hrz⟩
        refine ⟨y⁻¹ * r * y, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) r).mp hr
          simpa using this
        · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hrz ⊢
          rw [hrz]
          group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective α.injective]

theorem map_radP_mem {α : MulAut (projectiveSL 3 k)}
    (hα : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k) :
    (radP (k := k)).map α.toMonoidHom = radP ∨
      (radP (k := k)).map α.toMonoidHom = (radP (k := k)).map (alpha0Aut hk).toMonoidHom := by
  rcases map_projStabilizer_mem hk hα (d := 1) le_rfl (by norm_num) with h | h
  · exact Or.inl (map_radP_of_map_projStabilizer hk h)
  · right
    set α₀ := alpha0Aut hk with hα₀
    have h0 := map_projStabilizer_one_alpha0 hk
    have hβ : (projStabilizer (flagSpace 3 k 1)).map (α₀⁻¹ * α).toMonoidHom =
        projStabilizer (flagSpace 3 k 1) := by
      rw [← map_map_mulAut, h, ← h0, map_map_mulAut, inv_mul_cancel]
      exact Subgroup.map_id _
    have hR := map_radP_of_map_projStabilizer hk hβ
    rw [← map_map_mulAut] at hR
    calc (radP (k := k)).map α.toMonoidHom
        = (((radP (k := k)).map α.toMonoidHom).map α₀⁻¹.toMonoidHom).map α₀.toMonoidHom := by
          rw [map_map_mulAut, map_map_mulAut, mul_inv_cancel, one_mul]
      _ = (radP (k := k)).map α₀.toMonoidHom := by rw [hR]

end CFSG.Quasithin.H13.KGL34P

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def TwoParRad (X : Type) [Group X] (S₀ R : Subgroup X) : Prop :=
  R ≤ S₀ ∧ Subgroup.normalizer (S₀ : Set X) ≤ Subgroup.normalizer (R : Set X) ∧
    IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
    (∃ π : ↥(Subgroup.normalizer (R : Set X)) →*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
      Function.Surjective π ∧ π.ker = R.subgroupOf (Subgroup.normalizer (R : Set X))) ∧
    oTwoUpper (Subgroup.normalizer (R : Set X)) = Subgroup.normalizer (R : Set X) ∧
    ∀ α : MulAut X, Odd (orderOf α) → S₀.map α.toMonoidHom = S₀ → R.map α.toMonoidHom = R

@[expose] def TwoParConcl (X : Type) [Group X] (S₀ : Subgroup X) : Prop :=
  ∃ R₂ R₃ : Subgroup X, R₂ ≠ R₃ ∧ (∀ R : Subgroup X, (R = R₂ ∨ R = R₃) → TwoParRad X S₀ R) ∧
    Subgroup.normalizer (R₂ : Set X) ⊔ Subgroup.normalizer (R₃ : Set X) = ⊤ ∧
    ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ →
      (R₂.map α.toMonoidHom = R₂ ∨ R₂.map α.toMonoidHom = R₃) ∧
      (R₃.map α.toMonoidHom = R₂ ∨ R₃.map α.toMonoidHom = R₃)

theorem exists_parQuot_map {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {R : Subgroup Y}
    {Q : Type} [Group Q] (π : ↥(Subgroup.normalizer (R : Set Y)) →* Q)
    (hs : Function.Surjective π) (hk : π.ker = R.subgroupOf (Subgroup.normalizer (R : Set Y))) :
    ∃ π' : ↥(Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup X) : Set X)) →* Q,
      Function.Surjective π' ∧
        π'.ker = (R.map e.toMonoidHom).subgroupOf
          (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup X) : Set X)) := by
  have hN := Subgroup.map_equiv_normalizer_eq R e
  let ι : ↥(Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup X) : Set X)) ≃*
      ↥(Subgroup.normalizer (R : Set Y)) :=
    (MulEquiv.subgroupCongr hN.symm).trans (e.subgroupMap _).symm
  have hι : ∀ x, ((ι x : ↥(Subgroup.normalizer (R : Set Y))) : Y) = e.symm (x : X) := fun x => rfl
  refine ⟨π.comp ι.toMonoidHom, hs.comp ι.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hι, Subgroup.mem_map_equiv]

theorem isElemAbelian_map_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {p : ℕ}
    {E : Subgroup Y} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map e.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem congr_congr_symm {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) (α : MulAut X) :
    MulAut.congr e (MulAut.congr e.symm α) = α := by
  ext x
  simp [MulAut.congr_apply]

theorem map_congr_symm_eq {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {S₀ : Subgroup Y}
    {α : MulAut X} (hα : (S₀.map e.toMonoidHom).map α.toMonoidHom = S₀.map e.toMonoidHom) :
    S₀.map (MulAut.congr e.symm α).toMonoidHom = S₀ := by
  have h := map_map_congr e.symm α (S₀.map e.toMonoidHom)
  rw [hα, Subgroup.map_map] at h
  have h1 : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id Y := by
    ext y
    simp
  rw [h1, Subgroup.map_id] at h
  exact h.symm

theorem map_map_eq_congr_symm {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) (α : MulAut X)
    (R : Subgroup Y) :
    (R.map e.toMonoidHom).map α.toMonoidHom =
      (R.map (MulAut.congr e.symm α).toMonoidHom).map e.toMonoidHom := by
  rw [map_map_congr e (MulAut.congr e.symm α) R, congr_congr_symm]

theorem TwoParRad.map {X Y : Type} [Group X] [Group Y] [Finite Y] (e : Y ≃* X)
    {S₀ R : Subgroup Y} (h : TwoParRad Y S₀ R) :
    TwoParRad X (S₀.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  obtain ⟨hRS, hN, hab, hcard, ⟨π, hπs, hπk⟩, hO, hodd⟩ := h
  refine ⟨Subgroup.map_mono hRS, ?_, isElemAbelian_map_mulEquiv e hab, ?_,
    exists_parQuot_map e π hπs hπk, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hN
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rw [← Subgroup.map_equiv_normalizer_eq, oTwoUpper_map, hO]
  · intro α hα hαS
    have hS := map_congr_symm_eq e hαS
    have hord : Odd (orderOf (MulAut.congr e.symm α)) := by
      rwa [MulEquiv.orderOf_eq]
    rw [map_map_eq_congr_symm, hodd _ hord hS]

theorem TwoParConcl.map {X Y : Type} [Group X] [Group Y] [Finite Y] (e : Y ≃* X)
    {S₀ : Subgroup Y} (h : TwoParConcl Y S₀) : TwoParConcl X (S₀.map e.toMonoidHom) := by
  obtain ⟨R₂, R₃, hne, hR, hsup, hall⟩ := h
  refine ⟨R₂.map e.toMonoidHom, R₃.map e.toMonoidHom,
    fun h => hne (Subgroup.map_injective e.injective h), ?_, ?_, ?_⟩
  · rintro R (rfl | rfl)
    · exact (hR R₂ (Or.inl rfl)).map e
    · exact (hR R₃ (Or.inr rfl)).map e
  · rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_sup,
      hsup]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · intro α hα
    obtain ⟨h2, h3⟩ := hall _ (map_congr_symm_eq e hα)
    rw [map_map_eq_congr_symm, map_map_eq_congr_symm]
    refine ⟨?_, ?_⟩
    · rcases h2 with h2 | h2 <;> rw [h2]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases h3 with h3 | h3 <;> rw [h3]
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem twoParConcl_model {k : Type} [Field k] (hk : Nat.card k = 4) :
    TwoParConcl (projectiveSL 3 k) (projUnitriangular 3 k) := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α₀ := KGL34P.alpha0Aut hk with hα₀
  have hU0 := KGL34P.alpha0Aut_map_projUnitriangular hk
  have hN2 : Subgroup.normalizer (((KGL34P.radP (k := k)).map α₀.toMonoidHom :
      Subgroup (projectiveSL 3 k)) : Set (projectiveSL 3 k)) =
      projStabilizer (flagSpace 3 k 2) := by
    rw [← Subgroup.map_equiv_normalizer_eq, KGL34P.normalizer_radP hk,
      KGL34P.map_projStabilizer_one_alpha0 hk]
  have hne12 := KGL34P.projStabilizer_one_ne_two hk
  have hR2 : TwoParRad (projectiveSL 3 k) (projUnitriangular 3 k) KGL34P.radP := by
    refine ⟨KGL34P.radP_le_projUnitriangular, ?_, ?_, KGL34P.card_radP hk, ?_, ?_,
      fun α hα hαU => KGL34P.map_radP_of_odd hk hα hαU⟩
    · rw [normalizer_projUnitriangular 2, KGL34P.normalizer_radP hk]
      exact projUpperTriangular_le_projStabilizer 1
    · refine ⟨⟨⟨fun x y => Subtype.ext (KGL34P.radP_comm x.2 y.2)⟩⟩, fun x hx => ?_⟩
      exact KGL34P.radP_sq hk hx
    · have hN := KGL34P.normalizer_radP hk
      refine ⟨(KGL34P.piL2 hk).comp (MulEquiv.subgroupCongr hN).toMonoidHom,
        (KGL34P.piL2_surjective hk).comp (MulEquiv.subgroupCongr hN).surjective, ?_⟩
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, KGL34P.ker_piL2 hk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      rfl
    · rw [KGL34P.normalizer_radP hk]
      exact KGL34P.oTwoUpper_projStabilizer_one hk
  have hR3 : TwoParRad (projectiveSL 3 k) (projUnitriangular 3 k)
      ((KGL34P.radP (k := k)).map α₀.toMonoidHom) := by
    have := hR2.map α₀
    rwa [hU0] at this
  refine ⟨KGL34P.radP, (KGL34P.radP (k := k)).map α₀.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne12
    rw [← KGL34P.normalizer_radP hk, ← hN2, ← h]
  · rintro R (rfl | rfl)
    · exact hR2
    · exact hR3
  · rw [KGL34P.normalizer_radP hk, hN2]
    have hc1 := isCoatom_projStabilizer_flagSpace (K := k) (n := 3) (d := 1) le_rfl (by norm_num)
    have hc2 := isCoatom_projStabilizer_flagSpace (K := k) (n := 3) (d := 2) (by norm_num)
      (by norm_num)
    rcases eq_or_lt_of_le (le_sup_left : projStabilizer (flagSpace 3 k 1) ≤
        projStabilizer (flagSpace 3 k 1) ⊔ projStabilizer (flagSpace 3 k 2)) with h | h
    · exfalso
      have hle : projStabilizer (flagSpace 3 k 2) ≤ projStabilizer (flagSpace 3 k 1) := by
        rw [h]
        exact le_sup_right
      rcases eq_or_lt_of_le hle with h' | h'
      · exact hne12 h'.symm
      · exact hc1.1 (hc2.2 _ h')
    · exact hc1.2 _ h
  · intro α hα
    refine ⟨KGL34P.map_radP_mem hk hα, ?_⟩
    have hαα₀ : (projUnitriangular 3 k).map (α * α₀).toMonoidHom = projUnitriangular 3 k := by
      rw [← KGL34P.map_map_mulAut, hU0, hα]
    rw [KGL34P.map_map_mulAut]
    exact KGL34P.map_radP_mem hk hαα₀

theorem l34TwoParabolicFact : L34TwoParabolicFact := by
  intro X _ _ hX S₀ hS
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hS₀ : S₀ = (projUnitriangular 3 k).map e.symm.toMonoidHom := by
    rw [← he, Subgroup.map_map]
    simp
  have h := (twoParConcl_model hk).map e.symm
  rw [← hS₀] at h
  exact h

end CFSG.Quasithin.H13
