module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC5

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrn2b4_le_twoLocalRank_of_torusLift {X R : Type} [Group X] [Finite X] [Group R]
    {r : ℕ} (hT : GGTorusLift 3 r R) (e : X ⧸ Subgroup.center X ≃* R)
    (hcomm : commutator X = ⊤) : r ≤ LargeEvenTwoLocalRank 3 X := by
  let ψ : X →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      change e (QuotientGroup.mk' (Subgroup.center X) x) = 1 at hx
      rw [QuotientGroup.mk'_apply] at hx
      have h1 : QuotientGroup.mk x = 1 := e.injective (by rw [hx, map_one])
      rwa [QuotientGroup.eq_one_iff] at h1
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      show e (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  obtain ⟨U, E, hUne, hU2, hEU, hEab, hEcard, -⟩ := hT X ψ hψs hker.le hcomm
  exact TableB.le_twoLocalRank (p := 3) (by norm_num) ⟨U, hUne, hU2, rfl⟩
    (TableB.le_pRank_of_le (by norm_num) hEU hEab hEcard)

private lemma ltrn2b4_rank_bound
    {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {labX : LargeEvenLabel} {N b : ℕ}
    (hperf : commutator X = ⊤) (hAb : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hΛX : LargeEvenInLambda2 labX) (htag : labX.tag = .twA) (hX1 : labX.n = 1)
    (hN : N = labX.rank + 1) (hN3 : 3 * b = N) (hcardA : Nat.card A ≤ 3 ^ (b + 1))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : b ≤ 2 := by
  have h3N : 3 ∣ N := by rw [← hN3]; exact dvd_mul_right 3 b
  have hpq : 3 ∣ 2 ^ labX.n + 1 := by rw [hX1]; norm_num
  have hAll := largeEvenLabelAll_torusLift_twA (p := 3) hΛX htag Nat.prime_three hpq
  have hRaw := hAll (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hhX
  obtain ⟨R, hR, I, F, ⟨⟨e⟩, hT⟩⟩ := largeEvenRawDatum_exists hRaw
  letI := hR
  have hT' : GGTorusLift 3 (N - 3) R := by
    have hrankEq : ggUnitaryTorusRank 3 (labX.rank + 1) = N - 3 := by
      rw [ggUnitaryTorusRank, if_pos (by rw [← hN]; exact h3N), hN]
    rwa [hrankEq] at hT
  have hlift := ltrn2b4_le_twoLocalRank_of_torusLift (r := N - 3) hT' e hperf
  obtain ⟨m, hcardAb, hrankle⟩ := hrank
  have hrm : N - 3 ≤ m + 1 := by
    have hε : (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  have hmle : m ≤ b + 1 := by
    have h3m : 3 ^ m ≤ 3 ^ (b + 1) := by
      calc 3 ^ m = Nat.card Ab := hcardAb.symm
        _ ≤ Nat.card A := Subgroup.card_le_of_le hAb
        _ ≤ 3 ^ (b + 1) := hcardA
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3m
  omega

theorem ggN2RA_not_nine
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB 3 (3 ^ 5) (fun _ _ => True) A Ab σ J)
    (hhX : GGHasLabel (⟨.twA, 8, 1⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨⟨hloc, ⟨hAb, -, -⟩, -, hrank, hnum, -, -, hm⟩, -⟩ := hd
  have hperf : commutator X = ⊤ := hm.1
  have hcardA : Nat.card A ≤ 3 ^ (3 + 1) := by
    have h := hnum.1
    norm_num at h ⊢
    omega
  have hb : 3 ≤ 2 := ltrn2b4_rank_bound (N := 9) (b := 3) (labX := ⟨.twA, 8, 1⟩)
    hperf hAb hrank (by simp [LargeEvenInLambda2]) rfl rfl (by norm_num) (by norm_num) hcardA hhX
  omega

theorem ggN2RA_row_six {X : Type} [Group X] {J : Subgroup X}
    (hhJ : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X)) :
    GGTPNRow 3 J := by
  refine ⟨⟨.twA, 3, 1⟩, ⟨.twA, 5, 1⟩, ?_, ?_, ?_, hhJ, hhX⟩
  · simp [LargeEvenInLambda2]
  · simp [LargeEvenInLambda2]
  · simp [GGTablePRow]

end CFSG.StandardType

end
