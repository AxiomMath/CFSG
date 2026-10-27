module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4MSieg

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4M

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.Quasithin.Lie2Parabolic
open CFSG.Quasithin (perfectCore perfectCore_le conjClosure mem_conjClosure le_conjClosure
  conjClosure_le conjClosure_mono le_normalizer_conjClosure)
open CFSG.Open (pCoreOf)
open scoped commutatorElement

variable {F : Type} [Field F]

theorem entries_of_mem_Q0 {g : StatedSp 2 F} (hg : g ∈ Q2 F 0) :
    spMat g (Sum.inl 1) (Sum.inl 0) = 0 ∧ spMat g (Sum.inr 0) (Sum.inl 0) = 0 ∧
      spMat g (Sum.inr 1) (Sum.inl 0) = 0 ∧ spMat g (Sum.inr 0) (Sum.inl 1) = 0 ∧
      spMat g (Sum.inr 0) (Sum.inr 1) = 0 ∧
      spMat g (Sum.inl 0) (Sum.inl 0) * spMat g (Sum.inr 0) (Sum.inr 0) = 1 := by
  refine ⟨spMat_col_zero_of_mem_Q2_zero hg _ (by simp),
    spMat_col_zero_of_mem_Q2_zero hg _ (by simp), spMat_col_zero_of_mem_Q2_zero hg _ (by simp),
    spMat_inr_zero_of_mem_Q2_zero hg (by simp), spMat_inr_zero_of_mem_Q2_zero hg (by simp), ?_⟩
  have h := spMat_key_of_mem_Q2_zero hg (Sum.inr 0)
  simpa using h

theorem conj_xC_of_mem_Q0 {g : StatedSp 2 F} (hg : g ∈ Q2 F 0) (a : F) :
    g * xC a * g⁻¹ = xC (spMat g (Sum.inl 0) (Sum.inl 0) ^ 2 * a) := by
  obtain ⟨h1, h2, h3, h4, h5, hkey⟩ := entries_of_mem_Q0 hg
  rw [mul_inv_eq_iff_eq_mul]
  apply statedSp_ext
  change spMat g * spMat (xC a) = spMat (xC _) * spMat g
  rw [spMat_xC, spMat_xC]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, Matrix.one_apply, h1, h2, h3,
      h4, h5]
  linear_combination (-(spMat g (Sum.inl 0) (Sum.inl 0) * a)) * hkey

theorem xA_inv (t : F) : (xA t)⁻¹ = xA (-t) :=
  (eq_inv_of_mul_eq_one_right (by rw [xA_mul, add_neg_cancel, xA_zero])).symm

theorem conj_lo_xAB [CharP F 2] (u : F) :
    spLevi 0 (lo2 u) * xAB 1 * (spLevi 0 (lo2 u))⁻¹ = xAB 1 * xA u * xC u := by
  rw [mul_inv_eq_iff_eq_mul]
  apply statedSp_ext
  change spMat (spLevi 0 (lo2 u)) * spMat (xAB 1) =
    spMat (xAB 1) * spMat (xA u) * spMat (xC u) * spMat (spLevi 0 (lo2 u))
  rw [spMat_lam, spMat_xAB, spMat_xA, spMat_xC]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [lo2, pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply,
      Matrix.one_apply, CharTwo.neg_eq]
  all_goals first
    | ring1
    | linear_combination (-u) * (CharTwo.two_eq_zero : (2 : F) = 0)

variable [Finite F] [CharP F 2] {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem normalizer_XC : Subgroup.normalizer (XC F : Set (StatedSp 2 F)) = Q2 F 0 := by
  apply le_antisymm
  · intro g hg
    obtain ⟨b, hb⟩ := (Subgroup.mem_normalizer_iff.mp hg (xC 1)).mp (xC_mem_XC 1)
    have he : spMat g * spMat (xC 1) = spMat (xC b) * spMat g := by
      have : xC b * g = g * xC 1 := by
        rw [hb]
        group
      exact (congrArg (fun x : StatedSp 2 F => spMat x) this).symm
    have e : ∀ x : Fin 2 ⊕ Fin 2, x ≠ Sum.inl 0 → spMat g x (Sum.inl 0) = 0 := by
      intro x hx
      have := congrFun₂ he x (Sum.inr 0)
      rw [spMat_xC, spMat_xC] at this
      rcases x with x | x <;> fin_cases x
      · exact absurd rfl hx
      all_goals simpa [Matrix.mul_apply, Fintype.sum_sum_type, single_apply,
        Matrix.one_apply] using this
    show g ∈ stabilizer 2 F (flag 2 F 1)
    rw [CFSG.Quasithin.F134.Sp4.mem_stabilizer_one_iff]
    exact ⟨e _ (by simp), e _ (by simp), e _ (by simp)⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (conj_xC_of_mem_Q0 hg a).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨spMat g⁻¹ (Sum.inl 0) (Sum.inl 0) ^ 2 * b, ?_⟩
      rw [← conj_xC_of_mem_Q0 (inv_mem hg) b, hb]
      group

omit [CharP F 2] in
theorem L0_le_centralizer_XC :
    perfectCore (Q2 F 0) ≤ Subgroup.centralizer (XC F : Set (StatedSp 2 F)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  have h := conj_xC_of_mem_Q0 (perfectCore_le _ hg) a
  rw [spMat_inl_zero_eq_one_of_perfectCore hg, one_pow, one_mul, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem psl0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    IsPSL 2 2 n (ModO2 (perfectCore (Q2 F 0))) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  have := sl2_isSimple hK4
  have hnab := sl2_nonabelian hK4
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨(modO2EquivOfHom hnab (blkN 0) (blkN_surjective hK4 0)
      (blkN_ker_isPGroup ⟨n, hF⟩ 0)).trans sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

omit [CharP F 2] in
theorem spLevi_dg2_mem_L0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (s : Fˣ) :
    spLevi 0 (NQCat.dg2 s) ∈ perfectCore (Q2 F 0) :=
  spLevi_mem_perfectCore (NQCat.exists_finset_card_four_of_card hn hF) 0 _

omit [CharP F 2] in
theorem conj_dg2_xC (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (s : Fˣ) (a : F) :
    spLevi 0 (NQCat.dg2 s) * xC a * (spLevi 0 (NQCat.dg2 s))⁻¹ = xC a := by
  have := Subgroup.mem_centralizer_iff.mp (L0_le_centralizer_XC (spLevi_dg2_mem_L0 hn hF s))
    (xC a) (xC_mem_XC a)
  rw [← this, mul_inv_cancel_right]

theorem conjClosure_XAB_L0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    conjClosure (XAB F) (perfectCore (Q2 F 0)) = pCoreOf 2 (perfectCore (Q2 F 0)) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  apply le_antisymm
  · apply conjClosure_le
    intro h hh z hz
    exact (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (perfectCore (Q2 F 0)) hh) z).mp (XAB_le_R0 hn hF hz)
  · intro g hg
    obtain ⟨x, c₀, c₁, rfl⟩ := (mem_R0_iff hn hF).mp hg
    have hAB : ∀ t, xAB t ∈ conjClosure (XAB F) (perfectCore (Q2 F 0)) :=
      fun t => le_conjClosure _ _ (xAB_mem_XAB t)
    have hAC : ∀ u, xA u * xC u ∈ conjClosure (XAB F) (perfectCore (Q2 F 0)) := by
      intro u
      have h1 := mem_conjClosure (Z := XAB F) (spLevi_mem_perfectCore hK4 0 (lo2 u))
        (xAB_mem_XAB 1)
      rw [conj_lo_xAB, mul_assoc] at h1
      have := (conjClosure (XAB F) (perfectCore (Q2 F 0))).mul_mem
        ((conjClosure (XAB F) (perfectCore (Q2 F 0))).inv_mem (hAB 1)) h1
      rwa [inv_mul_cancel_left] at this
    obtain ⟨s, hs1⟩ := NQCat.exists_unit_ne_one hK4
    have hA : ∀ t, xA t ∈ conjClosure (XAB F) (perfectCore (Q2 F 0)) := by
      intro t
      have hw : (1 : F) - ((s⁻¹ : Fˣ) : F) ≠ 0 :=
        sub_ne_zero.mpr (NQCat.units_inv_ne_one hs1).symm
      have h1 := hAC (t / (1 - ((s⁻¹ : Fˣ) : F)))
      have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _
        (spLevi_dg2_mem_L0 hn hF s)) _).mp h1
      rw [show spLevi 0 (NQCat.dg2 s) * (xA (t / (1 - ((s⁻¹ : Fˣ) : F))) *
          xC (t / (1 - ((s⁻¹ : Fˣ) : F)))) * (spLevi 0 (NQCat.dg2 s))⁻¹ =
          (spLevi 0 (NQCat.dg2 s) * xA (t / (1 - ((s⁻¹ : Fˣ) : F))) *
            (spLevi 0 (NQCat.dg2 s))⁻¹) *
          (spLevi 0 (NQCat.dg2 s) * xC (t / (1 - ((s⁻¹ : Fˣ) : F))) *
            (spLevi 0 (NQCat.dg2 s))⁻¹) by group, conj_zero_xA, conj_dg2_xC hn hF] at h2
      have h3 := (conjClosure (XAB F) (perfectCore (Q2 F 0))).mul_mem h1
        ((conjClosure (XAB F) (perfectCore (Q2 F 0))).inv_mem h2)
      rw [_root_.mul_inv_rev, ← mul_assoc, mul_assoc (xA _), mul_inv_cancel, mul_one, xA_inv,
        xA_mul] at h3
      convert h3 using 2
      field_simp
      ring
    have hC : ∀ u, xC u ∈ conjClosure (XAB F) (perfectCore (Q2 F 0)) := by
      intro u
      have := (conjClosure (XAB F) (perfectCore (Q2 F 0))).mul_mem
        ((conjClosure (XAB F) (perfectCore (Q2 F 0))).inv_mem (hA u)) (hAC u)
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mul_mem (hA x) (hC c₀)) (hAB c₁)

theorem R0_inf_centralizer_L0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (perfectCore (Q2 F 0)) ⊓
        Subgroup.centralizer (perfectCore (Q2 F 0) : Set (StatedSp 2 F)) = XC F := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  apply le_antisymm
  · rintro g ⟨hgR, hgC⟩
    obtain ⟨x, c₀, c₁, rfl⟩ := (mem_R0_iff hn hF).mp hgR
    obtain ⟨s, hs1⟩ := NQCat.exists_unit_ne_one hK4
    have hcomm := Subgroup.mem_centralizer_iff.mp hgC _ (spLevi_dg2_mem_L0 hn hF s)
    have hconj : spLevi 0 (NQCat.dg2 s) * (xA x * xC c₀ * xAB c₁) *
        (spLevi 0 (NQCat.dg2 s))⁻¹ = xA x * xC c₀ * xAB c₁ := by
      rw [hcomm, mul_inv_cancel_right]
    rw [show spLevi 0 (NQCat.dg2 s) * (xA x * xC c₀ * xAB c₁) * (spLevi 0 (NQCat.dg2 s))⁻¹ =
        (spLevi 0 (NQCat.dg2 s) * xA x * (spLevi 0 (NQCat.dg2 s))⁻¹) *
        (spLevi 0 (NQCat.dg2 s) * xC c₀ * (spLevi 0 (NQCat.dg2 s))⁻¹) *
        (spLevi 0 (NQCat.dg2 s) * xAB c₁ * (spLevi 0 (NQCat.dg2 s))⁻¹) by group,
      conj_zero_xA, conj_dg2_xC hn hF, conj_zero_xAB] at hconj
    obtain ⟨hx, -, hc⟩ := rad0_inj hconj
    rw [eq_zero_of_mul_eq (NQCat.units_inv_ne_one hs1) hx, eq_zero_of_mul_eq hs1 hc, xA_zero,
      xAB_zero, one_mul, mul_one]
    exact xC_mem_XC c₀
  · intro g hg
    refine ⟨XC_le_R0 hn hF hg, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (L0_le_centralizer_XC hh) g hg).symm

theorem conjClosure_R1_L0 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    conjClosure (pCoreOf 2 (perfectCore (Q2 F 1))) (perfectCore (Q2 F 0)) =
      perfectCore (Q2 F 0) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  have := sl2_isSimple hK4
  apply le_antisymm
  · apply conjClosure_le
    intro h hh z hz
    exact mul_mem (mul_mem hh (mem_perfectCore_of_mem_unipotent hn hF 0
      (R1_le_unipotent hn hF hz))) (inv_mem hh)
  · intro k hk
    have hLevi : ∀ A, spLevi 0 A ∈
        conjClosure (pCoreOf 2 (perfectCore (Q2 F 1))) (perfectCore (Q2 F 0)) := by
      let N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (conjClosure (pCoreOf 2 (perfectCore (Q2 F 1))) (perfectCore (Q2 F 0))).comap (spLevi 0)
      have hN : N.Normal := ⟨fun A hA B => by
        refine Subgroup.mem_comap.mpr ?_
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _
          (spLevi_mem_perfectCore hK4 0 B)) _).mp (Subgroup.mem_comap.mp hA)⟩
      have hup : NQCat.up2 (1 : F) ∈ N := by
        refine Subgroup.mem_comap.mpr ?_
        rw [spLevi_zero_up2]
        exact le_conjClosure _ _ (xB_mem_R1 hn hF 1)
      have := hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
      · exfalso
        have h1 : NQCat.up2 (1 : F) = 1 := by
          rw [← Subgroup.mem_bot, ← h]
          exact hup
        have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
          (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
        simp [NQCat.up2] at this
      · intro A
        have hA : A ∈ N := by
          rw [h]
          exact Subgroup.mem_top A
        exact Subgroup.mem_comap.mp hA
    have hmem : k * (spLevi 0 (blkN 0 ⟨k, hk⟩))⁻¹ ∈ perfectCore (Q2 F 0) :=
      mul_mem hk (inv_mem (spLevi_mem_perfectCore hK4 0 _))
    have hr : k * (spLevi 0 (blkN 0 ⟨k, hk⟩))⁻¹ ∈ pCoreOf 2 (perfectCore (Q2 F 0)) := by
      rw [mem_pCoreOf_perfectCore_Q2 hn hF 0 hmem]
      have e : (⟨k * (spLevi 0 (blkN 0 ⟨k, hk⟩))⁻¹, hmem⟩ : ↥(perfectCore (Q2 F 0))) =
          ⟨k, hk⟩ * (⟨spLevi 0 (blkN 0 ⟨k, hk⟩), spLevi_mem_perfectCore hK4 0 _⟩)⁻¹ := rfl
      have h1 := congrArg (fun x => ((blkN 0 x : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) e
      simp only [map_mul, map_inv, blkN_spLevi hK4, mul_inv_cancel, blkN_coe,
        Matrix.SpecialLinearGroup.coe_one] at h1
      exact h1
    have hrN := conjClosure_mono (XAB_le_R1 hn hF) le_rfl
      ((conjClosure_XAB_L0 hn hF).symm ▸ hr)
    have := (conjClosure (pCoreOf 2 (perfectCore (Q2 F 1))) (perfectCore (Q2 F 0))).mul_mem hrN
      (hLevi (blkN 0 ⟨k, hk⟩))
    rwa [inv_mul_cancel_right] at this

end CFSG.Quasithin.H13.Ch4.Sp4M
