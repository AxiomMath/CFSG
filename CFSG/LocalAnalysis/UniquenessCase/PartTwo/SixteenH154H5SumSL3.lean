module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W]

private theorem s16h_sec_end_eq_one_or_id_of_natReal
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {X : Subgroup (MulAut W)} {U Z : Subgroup W}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥X}
    (R : SzN15.NatReal X U Z Γ π) (hLU : X ≤ stabSub U) (hLZ : X ≤ stabSub Z)
    (hscalar : H.HasScalarCommutant Γ) (hK2 : Nat.card K = 2)
    (f : Sec U Z →* Sec U Z)
    (hf : ∀ g ∈ autSec X U Z, ∀ x : Sec U Z, f (g x) = g (f x)) :
    f = 1 ∨ f = MonoidHom.id (Sec U Z) := by
  classical
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  let β₀ : Sec U Z →* Multiplicative (ι → K) :=
    QuotientGroup.lift (Z.subgroupOf U) β (by rw [hker])
  have hβ₀_mk : ∀ u : ↥U, β₀ (QuotientGroup.mk u : Sec U Z) = β u := by
    intro u
    rw [QuotientGroup.lift_mk']
  have hβ₀_inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [MonoidHom.mem_ker, hβ₀_mk u] at hx
      have huZ : (u : W) ∈ Z := (hβk u).mp hx
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact huZ
  have hβ₀_surj : Function.Surjective β₀ := by
    intro y
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨QuotientGroup.mk u, by rw [hβ₀_mk u]; exact hu⟩
  let βe : Sec U Z ≃* Multiplicative (ι → K) :=
    MulEquiv.ofBijective β₀ ⟨hβ₀_inj, hβ₀_surj⟩
  have hβe_mk : ∀ u : ↥U, βe (QuotientGroup.mk u : Sec U Z) = β u := hβ₀_mk
  have hβe_secHom : ∀ (γ : ↥Γ) (x : Sec U Z),
      βe (B5.secHom X hLU hLZ (π γ) x) = natAct Γ γ (βe x) := by
    intro γ x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [B5.secHom_mk]
      simp only [hβe_mk]
      exact hβe γ u _
  let f' : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    βe.toMonoidHom.comp (f.comp βe.symm.toMonoidHom)
  have hf'_eq : ∀ y, f' y = βe (f (βe.symm y)) := fun _ => rfl
  have hf'_apply : ∀ x : Sec U Z, f' (βe x) = βe (f x) := by
    intro x
    rw [hf'_eq, βe.symm_apply_apply]
  have hf'_comm : ∀ γ : ↥Γ, ∀ y, f' (natAct Γ γ y) = natAct Γ γ (f' y) := by
    intro γ y
    have h1 : βe.symm (natAct Γ γ y) = B5.secHom X hLU hLZ (π γ) (βe.symm y) := by
      apply βe.injective
      rw [βe.apply_symm_apply, hβe_secHom, βe.apply_symm_apply]
    have h2 : natAct Γ γ y = βe (B5.secHom X hLU hLZ (π γ) (βe.symm y)) := by
      rw [← βe.apply_symm_apply (natAct Γ γ y), h1]
    have hg : B5.secHom X hLU hLZ (π γ) ∈ autSec X U Z := by
      rw [← B5.range_secHom X hLU hLZ]
      exact ⟨π γ, rfl⟩
    calc f' (natAct Γ γ y)
        = f' (βe (B5.secHom X hLU hLZ (π γ) (βe.symm y))) := by rw [h2]
      _ = βe (f (B5.secHom X hLU hLZ (π γ) (βe.symm y))) := hf'_apply _
      _ = βe (B5.secHom X hLU hLZ (π γ) (f (βe.symm y))) := by rw [hf _ hg]
      _ = natAct Γ γ (βe (f (βe.symm y))) := hβe_secHom γ _
      _ = natAct Γ γ (f' y) := by rw [hf'_eq]
  let g' : (ι → K) →+ (ι → K) := (AddMonoidHom.toMultiplicative).symm f'
  have hg'_comm : ∀ γ ∈ Γ, ∀ v : ι → K,
      g' (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v) =
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ g' v := by
    intro γ hγ v
    have h : f' (Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v)) =
        natAct Γ ⟨γ, hγ⟩ (f' (Multiplicative.ofAdd v)) :=
      hf'_comm ⟨γ, hγ⟩ (Multiplicative.ofAdd v)
    change (f' (Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v))).toAdd =
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
        (f' (Multiplicative.ofAdd v)).toAdd
    rw [h]
    rfl
  obtain ⟨c, hc⟩ := hscalar g' hg'_comm
  have hc01 : c = 0 ∨ c = 1 := by
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      haveI : Finite Kˣ :=
        Finite.of_injective (fun u : Kˣ => (u : K)) (fun _ _ h => Units.ext h)
      have hunits : Nat.card Kˣ = 1 := by
        simp [Nat.card_units, hK2]
      haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp hunits.le
      exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc0) 1)
  rcases hc01 with hc0 | hc1
  · have hf'1 : f' = 1 := by
      apply MonoidHom.ext
      intro y
      conv_lhs => rw [← ofAdd_toAdd y]
      rw [show f' (Multiplicative.ofAdd (Multiplicative.toAdd y)) =
        Multiplicative.ofAdd (g' (Multiplicative.toAdd y)) from rfl]
      rw [hc (Multiplicative.toAdd y), hc0, zero_smul]
      rfl
    have hf1 : f = 1 := by
      ext x
      have h2 : βe (f x) = 1 := by
        rw [← hf'_apply x, hf'1]
        rfl
      exact βe.injective (by simpa using h2)
    exact Or.inl hf1
  · have hf'id : f' = MonoidHom.id (Multiplicative (ι → K)) := by
      apply MonoidHom.ext
      intro y
      conv_lhs => rw [← ofAdd_toAdd y]
      rw [show f' (Multiplicative.ofAdd (Multiplicative.toAdd y)) =
        Multiplicative.ofAdd (g' (Multiplicative.toAdd y)) from rfl]
      rw [hc (Multiplicative.toAdd y), hc1, one_smul]
      rfl
    have hfid : f = MonoidHom.id (Sec U Z) := by
      ext x
      have h2 : βe (f x) = βe x := by
        rw [← hf'_apply x, hf'id]
        rfl
      exact βe.injective (by simpa using h2)
    exact Or.inr hfid

theorem s16h_simpleScalar_binarySL3 [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hs : IsSLn ↥L 3 1) (h : BinaryNaturalSL L U Z 3 1) :
    s16h_SimpleScalar L U Z := by
  obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := h
  letI := hKfield
  letI := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hnat : BinaryNaturalSL L U Z 3 1 := ⟨K, hKfield, hKfin, hKcard, hReal⟩
  obtain ⟨π, hπ⟩ := hReal
  let R : SzN15.NatReal L U Z (StatedSL 3 K) π := SzN15.NatReal.of_realizesVia hπ
  have hZU : Z ≤ U := hπ.2.1
  have hLU : L ≤ stabSub U := by
    intro l hl
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have h1 := R.U_inv ((⟨l, hl⟩ : ↥L)⁻¹) ((l : MulAut W) u) hu
        simpa using h1,
      fun hu => R.U_inv ⟨l, hl⟩ u hu⟩
  have hLZ : L ≤ stabSub Z := by
    intro l hl
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have h1 := R.Z_inv ((⟨l, hl⟩ : ↥L)⁻¹) ((l : MulAut W) u) hu
        simpa using h1,
      fun hu => R.Z_inv ⟨l, hl⟩ u hu⟩
  refine ⟨?_, ?_⟩
  · refine SumOfNatShape.isIrrOn hq ?_
    refine ⟨3, Or.inl ⟨hs, ?_⟩⟩
    refine ⟨fun _ => U, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hZU
    · intro i
      have hbot : (⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥ := by
        apply iSup_eq_bot.mpr
        intro j
        apply iSup_eq_bot.mpr
        intro hj
        exact absurd (Subsingleton.elim j i) hj
      rw [hbot, sup_bot_eq]
      exact inf_le_right
    · have hsup : (⨆ _i : Fin 1, U) = U := iSup_const
      rw [hsup, sup_eq_right.mpr hZU]
    · intro i
      exact hnat
  · intro f hf
    exact s16h_sec_end_eq_one_or_id_of_natReal R hLU hLZ
      (H.hasScalarCommutant_statedSL (K := K) (d := 3) (by norm_num)) hK2 f hf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
