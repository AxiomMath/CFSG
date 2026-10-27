module

public import CFSG.RankThree.PartOne.Census3.Unitary
import CFSG.RankThree.PartTwo.Census.CommonUnipotent
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix

@[expose] def u68Exp (u : Fin 4 → ℤ) : Fin 6 → ℤ :=
  ![u 0, u 0, u 0 + 3 * u 1, u 0 + 6 * u 1 + 3 * u 2, u 0 + 6 * u 2 + 3 * u 3, -5 * u 0 + 6 * u 3]

theorem u68Exp_apply_zero (u : Fin 4 → ℤ) : u68Exp u 0 = u 0 := rfl
theorem u68Exp_apply_one (u : Fin 4 → ℤ) : u68Exp u 1 = u 0 := rfl
theorem u68Exp_apply_two (u : Fin 4 → ℤ) : u68Exp u 2 = u 0 + 3 * u 1 := rfl
theorem u68Exp_apply_three (u : Fin 4 → ℤ) : u68Exp u 3 = u 0 + 6 * u 1 + 3 * u 2 := rfl
theorem u68Exp_apply_four (u : Fin 4 → ℤ) : u68Exp u 4 = u 0 + 6 * u 2 + 3 * u 3 := rfl
theorem u68Exp_apply_five (u : Fin 4 → ℤ) : u68Exp u 5 = -5 * u 0 + 6 * u 3 := rfl

theorem u68Exp_zero : u68Exp 0 = 0 := by
  funext j
  fin_cases j <;> simp [u68Exp]

theorem u68Exp_add (u v : Fin 4 → ℤ) : u68Exp (u + v) = u68Exp u + u68Exp v := by
  funext j
  fin_cases j <;> simp [u68Exp] <;> ring

theorem sum_u68Exp (u : Fin 4 → ℤ) : ∑ j, u68Exp u j = 9 * (u 1 + u 2 + u 3) := by
  simp [u68Exp, Fin.sum_univ_six]
  ring

variable {K : Type} [Field K]

@[expose] def u68Diag (ζ : Kˣ) : Multiplicative (Fin 4 → ℤ) →* (Fin 6 → Kˣ) where
  toFun u j := ζ ^ u68Exp u.toAdd j
  map_one' := by
    funext j
    simp [u68Exp_zero]
  map_mul' u v := by
    funext j
    simp [u68Exp_add, _root_.zpow_add]

theorem four_le_localRank_three_statedSU_six_eight [Finite K] [CharP K 2]
    (hK : Nat.card K = 64) : 4 ≤ localRank 3 (StatedProj (StatedSU 6 (2 ^ 3) K)) := by
  have h : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hU : Nat.card Kˣ = 63 := by rw [Nat.card_units, hK]
  set ζ : Kˣ := g ^ 7 with hζdef
  have hζ : orderOf ζ = 9 := by
    rw [hζdef, orderOf_pow_of_dvd (by norm_num) (by rw [hg, hU]; norm_num), hg, hU]
  have hζz : ∀ m n : ℤ, ζ ^ m = ζ ^ n ↔ (9 : ℤ) ∣ n - m := by
    intro m n
    rw [zpow_eq_zpow_iff_modEq, hζ, Int.modEq_iff_dvd]
    norm_num
  set ψ₀ := (diagGL 6 K).comp (u68Diag ζ)
  have hcoe : ∀ u, ((ψ₀ u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun j => ((ζ ^ u68Exp u.toAdd j : Kˣ) : K) := fun _ => rfl
  have hmem : ∀ u, ψ₀ u ∈ StatedSU 6 (2 ^ 3) K := by
    intro u
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · have hprod : ∏ j, ζ ^ u68Exp u.toAdd j = ζ ^ (∑ j, u68Exp u.toAdd j) := by
        rw [Fin.prod_univ_six, Fin.sum_univ_six]
        simp only [_root_.zpow_add]
      rw [hcoe, det_diagonal, ← Units.coe_prod, hprod, sum_u68Exp]
      have : ζ ^ (9 * (u.toAdd 1 + u.toAdd 2 + u.toAdd 3)) = ζ ^ (0 : ℤ) :=
        (hζz _ _).mpr ⟨-(u.toAdd 1 + u.toAdd 2 + u.toAdd 3), by ring⟩
      rw [this, zpow_zero, Units.val_one]
    · rw [hcoe, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      refine congrArg diagonal (funext fun j => ?_)
      rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul]
      have : ζ ^ (u68Exp u.toAdd j * ((2 ^ 3 + 1 : ℕ) : ℤ)) = ζ ^ (0 : ℤ) :=
        (hζz _ _).mpr ⟨-u68Exp u.toAdd j, by push_cast; ring⟩
      rw [this, zpow_zero, Units.val_one]
  set Z := (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 3) K)
  set Φ : Multiplicative (Fin 4 → ℤ) →* StatedProj (StatedSU 6 (2 ^ 3) K) :=
    (QuotientGroup.mk' Z).comp (ψ₀.codRestrict _ hmem)
  have hscal : ∀ u, (∀ j, (9 : ℤ) ∣ u68Exp u.toAdd j - u68Exp u.toAdd 0) → Φ u = 1 := by
    intro u hu
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    refine ⟨ζ ^ u68Exp u.toAdd 0, Units.ext ?_⟩
    change scalar (Fin 6) ((ζ ^ u68Exp u.toAdd 0 : Kˣ) : K) = _
    rw [MonoidHom.codRestrict_apply, hcoe, scalar_apply]
    exact congrArg diagonal (funext fun j => congrArg Units.val ((hζz _ _).mpr (hu j)))
  have hscal' : ∀ u, Φ u = 1 → ∀ j, (9 : ℤ) ∣ u68Exp u.toAdd j - u68Exp u.toAdd 0 := by
    intro u hu j
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hu
    obtain ⟨c, hc⟩ := hu
    have hc' : GeneralLinearGroup.scalar (Fin 6) c = ψ₀ u := hc
    have hci : ∀ i, (c : K) = ((ζ ^ u68Exp u.toAdd i : Kˣ) : K) := by
      intro i
      have := congrArg (fun A : GL (Fin 6) K => (A : Matrix (Fin 6) (Fin 6) K) i i) hc'
      simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hcoe]
        using this
    exact (hζz _ _).mp (Units.ext ((hci 0).symm.trans (hci j)))
  have hΦeq : ∀ u u' : Fin 4 → ℤ, (∀ i, (3 : ℤ) ∣ u i - u' i) →
      Φ (Multiplicative.ofAdd u) = Φ (Multiplicative.ofAdd u') := by
    intro u u' hu
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    refine hscal _ fun j => ?_
    obtain ⟨a, ha⟩ := hu 0
    obtain ⟨b, hb⟩ := hu 1
    obtain ⟨c, hc⟩ := hu 2
    obtain ⟨d, hd⟩ := hu 3
    simp only [toAdd_ofAdd] at ha hb hc hd ⊢
    fin_cases j <;> simp [u68Exp] <;> omega
  set lift : (Fin 4 → ZMod 3) → (Fin 4 → ℤ) := fun v i => ((v i).val : ℤ) with hlift
  let ψ : Multiplicative (Fin 4 → ZMod 3) →* StatedProj (StatedSU 6 (2 ^ 3) K) :=
    { toFun := fun v => Φ (Multiplicative.ofAdd (lift v.toAdd))
      map_one' := by
        have : lift (Multiplicative.toAdd 1) = 0 := by
          funext i
          simp [hlift]
        rw [this, ofAdd_zero, map_one]
      map_mul' := fun v w => by
        rw [← map_mul, ← ofAdd_add]
        refine hΦeq _ _ fun i => ?_
        simp only [hlift, toAdd_mul, Pi.add_apply, ZMod.val_add]
        omega }
  have hψ : ∀ v, ψ v = Φ (Multiplicative.ofAdd (lift v.toAdd)) := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun v hv => ?_
    have h9 := hscal' _ hv
    have e2 := h9 2
    have e3 := h9 3
    have e4 := h9 4
    have e5 := h9 5
    simp only [toAdd_ofAdd, u68Exp_apply_zero, u68Exp_apply_two, u68Exp_apply_three,
      u68Exp_apply_four, u68Exp_apply_five, hlift] at e2 e3 e4 e5
    have hlt : ∀ i, (v.toAdd i).val < 3 := fun i => ZMod.val_lt _
    have h0 := hlt 0
    have h1 := hlt 1
    have h2 := hlt 2
    have h3 := hlt 3
    have hz : ∀ i, (v.toAdd i).val = 0 := by
      intro i
      fin_cases i
      · show (v.toAdd 0).val = 0
        omega
      · show (v.toAdd 1).val = 0
        omega
      · show (v.toAdd 2).val = 0
        omega
      · show (v.toAdd 3).val = 0
        omega
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
    rw [toAdd_one, Pi.zero_apply]
    exact (ZMod.val_eq_zero _).mp (hz i)
  have hn2 : 2 ≤ 6 := by norm_num
  set t : StatedSU 6 (2 ^ 3) K := ⟨swapGL hn2, swapGL_mem_statedSU h hn2⟩
  have htZ : t ∉ Z := by
    intro htZ
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp htZ
    have := congrArg (fun A : GL (Fin 6) K => (A : Matrix (Fin 6) (Fin 6) K) 0 1) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, t, coe_swapGL, swapBlock,
      Matrix.add_apply, of_apply, Matrix.one_apply] at this
    simp at this
  have ht2 : t ^ 2 ∈ Z := by
    rw [show t ^ 2 = 1 from Subtype.ext (Units.ext (by
      rw [pow_two]
      exact one_add_mul_one_add (swapBlock_mul_self hn2)))]
    exact Z.one_mem
  have hcard : Nat.card ψ.range = 3 ^ 4 :=
    (card_range_of_injective hψinj).trans (by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  have h3 : ∀ w : Fin 4 → ZMod 3, 3 • w = 0 := fun w => by
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  refine le_localRank_of_commute_involution Nat.prime_three (orderOf_mk_eq_two Z htZ ht2)
    (isElemAbelian_range_of_nsmul h3 ψ) hcard ?_
  rintro _ ⟨v, rfl⟩
  change Φ (Multiplicative.ofAdd (lift v.toAdd)) * QuotientGroup.mk' Z t =
    QuotientGroup.mk' Z t * Φ (Multiplicative.ofAdd (lift v.toAdd))
  rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  change ((ψ₀ _ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (1 + swapBlock 6 K) =
    (1 + swapBlock 6 K) * ((ψ₀ _ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  rw [hcoe]
  refine diagonal_mul_swap fun i j hi hj => ?_
  have key : ∀ l : Fin 6, l.val < 2 → u68Exp (lift v.toAdd) l = lift v.toAdd 0 := by
    intro l hl
    fin_cases l <;> simp [u68Exp] at hl ⊢
  simp only [toAdd_ofAdd]
  rw [key i hi, key j hj]

theorem localRankThreeU68 : LocalRankThreeU68 :=
  fun _ _ _ _ hK => four_le_localRank_three_statedSU_six_eight hK

end CFSG.RankThree.PartOne.Census3
