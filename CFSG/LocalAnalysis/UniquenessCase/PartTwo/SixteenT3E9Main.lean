module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9Klein
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9Idem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3OddFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10OutFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3GapMV

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

theorem s16t_false_of_direct_eight {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (hrk : rk (⊤ : Subgroup T) = 8) {M A B : Subgroup (MulAut T)}
    (hA : IsElemAbelianOfRank 3 2 ↥A) (hnorm : ∀ g ∈ M, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hcent : ∀ g ∈ M, (∀ a ∈ A, g * a = a * g) → g ∈ A) (hind : IsIndivisible M)
    (hBM : B ≤ M) (hB1 : B ≠ ⊥) (hB2 : IsElemAbelian2 B) {Ut : Subgroup T} (hUt : Ut ≠ ⊤)
    (hk : rkIdx Ut ≤ 1) (hA4 : ∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B)
    (hA5 : rkIdx (fixV B) = rk ↥B + rkIdx Ut) : False := by
  classical
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  have hAcard : Nat.card A = 9 := by
    rw [s16c167_card_isElemAbelianOfRank hA]
    norm_num
  have hodd : Odd (Nat.card A) := by
    rw [hAcard]
    decide
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    omega
  have hfixA : fixV A = ⊥ := s16t_fixV_eq_bot_of_indivisible hT hind hnorm hodd hA1
  obtain ⟨a, haA, b, hbA, ha3, hb3, hab, hgen⟩ := s16t_exists_gens_E9 hA
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := by
    obtain ⟨e⟩ := hA
    intro x hx
    have h3pow : ∀ v : Multiplicative (Fin 2 → ZMod 3), v ^ 3 = 1 := by
      intro v
      induction v using Multiplicative.rec with
      | ofAdd w =>
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 w, ZMod.natCast_self 3,
          zero_smul, ofAdd_zero]
    have h1 : e ((⟨x, hx⟩ : ↥A) ^ 3) = e 1 := by
      rw [map_pow, map_one]
      exact h3pow _
    have h2 := e.injective h1
    simpa using congrArg Subtype.val h2
  have hcentB : ∀ b ∈ B, (∀ a ∈ A, b * a = a * b) → b = 1 := by
    intro b hb hc
    have hbA : b ∈ A := hcent b (hBM hb) hc
    have h3 := hA3 b hbA
    have h2 := hB2.2 b hb
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  obtain ⟨hcard4, hz⟩ := s16t_klein_of_selfCentralizing hA
    (fun b hb a ha => hnorm b (hBM hb) a ha) hcentB hB2.1 hB2.2
  by_cases hB : Nat.card B ≤ 2
  · exact hUt (s16c1610_ut_eq_top_of_card_le_two hT hB1 hB2 hB hA4)
  · obtain ⟨z, hzB, hzinv⟩ := hz (by omega)
    have hrkB : rk ↥B ≤ 2 := by
      have hp : IsPGroup 2 ↥B := E3.isPGroup_of_isElemAbelian2 hB2
      have h := card_eq_two_pow_of_isPGroup hp
      by_contra hlt
      have h8 : 2 ^ 3 ≤ 2 ^ rk ↥B := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hza : z * a * z⁻¹ = a⁻¹ := hzinv a haA
    have hzb : z * b * z⁻¹ = b⁻¹ := hzinv b hbA
    have hfix : ∀ v : T, a v = v → b v = v → v = 1 := by
      intro v hav hbv
      have hai : ∀ n : ℕ, (a ^ n) v = v := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hav, ih]
      have hbj : ∀ n : ℕ, (b ^ n) v = v := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hbv, ih]
      have hv : v ∈ fixV A := by
        intro x hx
        obtain ⟨i, j, rfl⟩ := hgen x hx
        rw [MulAut.mul_apply, hbj j, hai i]
      rw [hfixA] at hv
      exact Subgroup.mem_bot.1 hv
    have hcomm := s16t_fixV_le_commV_of_inv hT ha3 hb3 hab hza hzb hfix
    have h1 : rk (fixV (Subgroup.zpowers z)) ≤ rk (commV (Subgroup.zpowers z)) := rk_mono hcomm
    have h2 := rk_commV_add_rk_fixV z
    have h3 : rk T = 8 := by rw [← rk_top]; exact hrk
    have h4 := rkIdx_fixV_zpowers z
    have h5 : fixV B ≤ fixV (Subgroup.zpowers z) := fun v hv =>
      mem_fixV_zpowers_iff_apply.2 (hv z hzB)
    have h6 := rkIdx_anti h5
    omega

variable {G : Type} [Group G] [Finite G]

theorem s16t_fstarBar_selfCentralizing (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {x : MulAut (Vtil V₀ V hV)} (hx : x ∈ Mbar D.M V₀ V hV)
    (hcomm : ∀ a ∈ fstarBar D.M V₀ V hV, x * a = a * x) : x ∈ fstarBar D.M V₀ V hV := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  haveI : Finite ↥Mb := Subtype.finite
  have hself : centralizer (genFittingFStar ↥Mb : Set ↥Mb) ≤ genFittingFStar ↥Mb :=
    CFSG.Open.Open.generalized_fitting_self_centralizing ↥Mb
  have hmem : (⟨x, hx⟩ : ↥Mb) ∈ centralizer (genFittingFStar ↥Mb : Set ↥Mb) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (hcomm f.1 (Subgroup.mem_map.2 ⟨f, hf, rfl⟩)).symm
  exact Subgroup.mem_map.2 ⟨_, hself hmem, rfl⟩

section Certified


theorem s16t_no_calOStar_of_case168_8 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h8 : Case168_8 D V₀ V hV)
    (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, hk, -, hA4, hA5⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219
    (by rw [h8.2.2]; exact Set.mem_singleton 3)
  exact s16t_false_of_direct_eight (s15_Infra_vtil_sq_eq_one V₀ V hV) h8.2.1 h8.1
    (fun g hg a ha => s16t_fstarBar_conj_mem D hV hg ha)
    (fun x hx hcomm => s16t_fstarBar_selfCentralizing D hV hx hcomm)
    (TwelveSeventeen.isIndivisible D hin.hx hin.h61 hin.h127 hin.h1214
      hc.setting.hyp16.hyp125) hBM hB1 hB2 hUt (hk.trans hk1.le) hA4 hA5

end Certified

section CertifiedOut


theorem s16t_out10_of_case168_8_three (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h8 : Case168_8 D V₀ V hV) : Out10 D V₀ V hV := by
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hin.hSg hin.h1219 (by rw [h8.2.2]; exact Set.mem_singleton 3)
  have h1 := s16t_one_lt_mBar_of_three D h1217 h153 hc
  exact s16c1610_out10_of_no_calOStar D hin.hx hin.h61 hin.h127 hin.h1114 hin.h162
    hc.setting.hyp16.hyp125 (by omega) (fun _ g => s16t_no_calOStar_of_case168_8 D hin hc h8 g)

end CertifiedOut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
