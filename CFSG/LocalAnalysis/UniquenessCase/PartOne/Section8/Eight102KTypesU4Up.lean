module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Matrix CFSG.Open Subgroup
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD longSL mem_longSL_of pattern_long_of_mem
  entry_zero_zero_of_mem_longSL nonempty_longSL_mulEquiv coe_torusD)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [Finite F] [CharP F 2] in
private theorem exists_diag_entries {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    ∃ a : F, a ^ 3 = 1 ∧ a ≠ 1 ∧ a ≠ a⁻¹ ∧ (1 : F) ≠ a⁻¹ ∧
      ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        diagonal ![a, 1, 1, a⁻¹] := by
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  refine ⟨a, ha3, ha1, hainv, ?_, ?_⟩
  · intro h
    exact ha1 (by rw [← inv_inv a, ← h, inv_one])
  · rw [coe_torusD]
    simp [ha]

private theorem card_inf_longSL_le (hb : 0 < b) (hbe : Even b)
    (hF : Nat.card F = (2 ^ b) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (GL (Fin 4) F)} (hEab : IsElemAbelian p E) :
    Nat.card ↥(E ⊓ longSL (unitaryInvolution F 2 b)) ≤ p := by
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) hb hF
  have hcardK : @Fintype.card (GaloisField 2 b) (Fintype.ofFinite _) = 2 ^ b := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 b (by omega)
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
      ↥(longSL (unitaryInvolution F 2 b)) b :=
    @CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two
      ↥(longSL (unitaryInvolution F 2 b)) _ b hb2 (GaloisField 2 b) _
      (Fintype.ofFinite (GaloisField 2 b)) hcardK
      (eL.trans (CFSG.RankThree.PartTwo.Sec21.projSLTwoEquivSL (GaloisField 2 b)))
  have h1 : IsElemAbelian p ((E ⊓ longSL (unitaryInvolution F 2 b)).subgroupOf
      (longSL (unitaryInvolution F 2 b))) :=
    (hEab.mono inf_le_left).subgroupOf _
  have hinst : CFSG.IsElementaryAbelian p ↥((E ⊓ longSL (unitaryInvolution F 2 b)).subgroupOf
      (longSL (unitaryInvolution F 2 b))) := h1.isElementaryAbelian
  have h2 := @CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_rank
    ↥(longSL (unitaryInvolution F 2 b)) _ b p hp hp2 hL2
    ((E ⊓ longSL (unitaryInvolution F 2 b)).subgroupOf
      (longSL (unitaryInvolution F 2 b))) hinst
  have h3 : Nat.card ↥((E ⊓ longSL (unitaryInvolution F 2 b)).subgroupOf
      (longSL (unitaryInvolution F 2 b))) =
      Nat.card ↥(E ⊓ longSL (unitaryInvolution F 2 b)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : E ⊓ longSL (unitaryInvolution F 2 b) ≤
        longSL (unitaryInvolution F 2 b))).toEquiv
  rwa [h3] at h2

omit [CharP F 2] in
private theorem card_range_le_of_isElemAbelian {p : ℕ} (hp : p.Prime)
    {E : Subgroup (GL (Fin 4) F)} (hEab : IsElemAbelian p E) (f : ↥E →* Fˣ) :
    Nat.card f.range ≤ p := by
  have hexp : ∀ x : ↥f.range, x ^ p = 1 := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := hy
    apply Subtype.ext
    change (f e) ^ p = 1
    have hpow : e ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hEab.2 (e : GL (Fin 4) F) e.2)
    calc (f e) ^ p = f (e ^ p) := (map_pow f e p).symm
      _ = f 1 := by rw [hpow]
      _ = 1 := map_one f
  exact CFSG.Walter.JT.card_le_of_isCyclic_of_pow_eq_one hp.pos hexp

private theorem card_le_sq_of_isElemAbelian (hb : 0 < b) (hbe : Even b)
    (hF : Nat.card F = (2 ^ b) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (GL (Fin 4) F)}
    (hE : E ≤ SU (unitaryInvolution F 2 b) 4 ⊓
      centralizer (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)))
    (hEab : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨a, -, ha1, hainv, hinv1, ht⟩ := exists_diag_entries hω
  let σ : F ≃+* F := unitaryInvolution F 2 b
  let t : GL (Fin 4) F := torusD ((ω, 1) : D8Mod 3 F)
  let C : Subgroup (GL (Fin 4) F) := SU σ 4 ⊓ centralizer (zpowers t : Set (GL (Fin 4) F))
  have hEC : E ≤ C := hE
  let χF : C →* F :=
    { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨h01, h02, h03, -⟩ := pattern_long_of_mem ht ha1 hainv hinv1 x.2.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03] }
  let f : ↥E →* Fˣ := χF.toHomUnits.comp (Subgroup.inclusion hEC)
  have hrange : Nat.card f.range ≤ p := card_range_le_of_isElemAbelian hp hEab f
  have hlongSL : ∀ x : ↥f.ker, ((x : ↥E) : GL (Fin 4) F) ∈ longSL σ := by
    intro x
    have hχ : χF (Subgroup.inclusion hEC (x : ↥E)) = 1 := by
      have h : f (x : ↥E) = 1 := x.2
      change χF.toHomUnits (Subgroup.inclusion hEC (x : ↥E)) = 1 at h
      simpa using congrArg Units.val h
    have hxC : ((x : ↥E) : GL (Fin 4) F) ∈ C := hEC (x : ↥E).2
    have hpat := pattern_long_of_mem ht ha1 hainv hinv1 hxC.2
    have h00 : (((x : ↥E) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
      change χF (Subgroup.inclusion hEC (x : ↥E)) = 1
      exact hχ
    exact mem_longSL_of σ hxC.1 hpat h00
  have hker_eq : f.ker = (E ⊓ longSL σ).subgroupOf E := by
    ext x
    constructor
    · intro hx
      exact ⟨x.2, hlongSL ⟨x, hx⟩⟩
    · rintro ⟨-, hx⟩
      apply Units.ext
      change ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1
      exact entry_zero_zero_of_mem_longSL σ hx
  have hker : Nat.card f.ker ≤ p := by
    rw [hker_eq]
    have h4 : Nat.card ↥((E ⊓ longSL σ).subgroupOf E) = Nat.card ↥(E ⊓ longSL σ) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : E ⊓ longSL σ ≤ E)).toEquiv
    rw [h4]
    exact card_inf_longSL_le hb hbe hF hp hp2 hEab
  calc Nat.card E = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ p * p := Nat.mul_le_mul hker hrange
    _ = p ^ 2 := by rw [pow_two]

theorem pRank_centralizer_line_le (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Open.pRank p (SU (unitaryInvolution F 2 b) 4 ⊓
      centralizer (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≤ 2 := by
  have hbound : ∀ E : Subgroup (GL (Fin 4) F),
      E ≤ SU (unitaryInvolution F 2 b) 4 ⊓ centralizer
        (zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F)) →
      IsElemAbelian p E → Nat.card E ≤ p ^ 2 :=
    fun E hE hEab => card_le_sq_of_isElemAbelian hb hbe hF hω hp hp2 hE hEab
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, hE, hEab, hcard⟩
  have h := hbound E hE hEab
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
