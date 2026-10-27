module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxLinear
import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.RankThree.PartOne.CTP CFSG.BenderSuzuki.MatrixGroups

section Arithmetic

theorem dvd_of_card_sl2_dvd {a b : ℕ} (ha : 1 ≤ a)
    (h : 2 ^ a * ((2 ^ a) ^ 2 - 1) ∣ 2 ^ b * ((2 ^ b) ^ 2 - 1)) : a ∣ b := by
  have h2a : (2 ^ a) ^ 2 - 1 = 2 ^ (2 * a) - 1 := by rw [← pow_mul, mul_comm]
  have h2b : (2 ^ b) ^ 2 - 1 = 2 ^ (2 * b) - 1 := by rw [← pow_mul, mul_comm]
  have hodd : Nat.Coprime (2 ^ (2 * a) - 1) (2 ^ b) := by
    apply Nat.Coprime.pow_right
    refine Nat.coprime_two_right.mpr (Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one)
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hdvd : 2 ^ (2 * a) - 1 ∣ 2 ^ (2 * b) - 1 := by
    rw [h2a, h2b] at h
    exact hodd.dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans h)
  have hmod := Nat.pow_sub_one_mod_pow_sub_one 2 (2 * a) (2 * b)
  rw [Nat.mod_eq_zero_of_dvd hdvd] at hmod
  have hle : 2 ^ (2 * b % (2 * a)) ≤ 1 := by omega
  have hz : 2 * b % (2 * a) = 0 := by
    by_contra hne
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.pos_of_ne_zero hne)
    omega
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (Nat.dvd_of_mod_eq_zero hz)

end Arithmetic

section SubfieldGroup

theorem card_psl2_matrixGroup_charTwo (L : Type) [Field L] [Finite L] [CharP L 2] :
    Nat.card (PSL2MatrixGroup L) = Nat.card L * (Nat.card L ^ 2 - 1) := by
  rw [← CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two L]
  exact (Nat.card_congr (Equiv.ofBijective (mkPSL L)
    ⟨mkPSL_injective, QuotientGroup.mk'_surjective _⟩)).symm

variable {F : Type} [Field F] [Finite F]

theorem card_slSub_two (k : Subfield F) :
    Nat.card (slSub 2 k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (k.subtype : k →+* F)) := by
    intro A B h
    ext i j
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) i j) h
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
  show Nat.card (Matrix.SpecialLinearGroup.map (n := Fin 2) (k.subtype : k →+* F)).range = _
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two k

theorem isPerfect_slSub_two (k : Subfield F) (hk4 : 4 ≤ Nat.card k) :
    Group.IsPerfect (slSub 2 k) := by
  have : ∃ s : Finset k, s.card = 4 := by
    have := Fintype.ofFinite k
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset k)) (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hk4)
    exact ⟨s, hs⟩
  have h1 := CFSG.LinearGroups.special_linear_dimension_two_perfect this
  exact Group.IsPerfect.range (Matrix.SpecialLinearGroup.map (n := Fin 2) (k.subtype : k →+* F))

end SubfieldGroup

theorem sl2Sub_maximal {F : Type} [Field F] [Finite F] [CharP F 2]
    {k : Subfield F} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hF : Nat.card F = Nat.card k ^ d)
    (hk4 : 4 ≤ Nat.card k) {M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hM : slSub 2 k ≤ M) (hne : ¬ M ≤ slSub 2 k) : M = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hFf⟩ := exists_card_eq_two_pow F
  obtain ⟨m₀, hm₀1, hk⟩ := exists_card_eq_two_pow k
  have hfm : f = m₀ * d := by
    have h : 2 ^ f = 2 ^ (m₀ * d) := by rw [← hFf, hF, hk, ← pow_mul]
    exact Nat.pow_right_injective (le_refl 2) h
  have hq4 : 4 ≤ 2 ^ m₀ := hk ▸ hk4
  have hJM : slSub 2 k < M := lt_of_le_not_ge hM hne
  have hJcard : Nat.card (slSub 2 k) = 2 ^ m₀ * ((2 ^ m₀) ^ 2 - 1) := by
    rw [card_slSub_two, hk]
  have hJperf := isPerfect_slSub_two k hk4
  have hJnt : Nontrivial (slSub 2 k) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hJcard]
    have h16 : 4 ^ 2 ≤ (2 ^ m₀) ^ 2 := Nat.pow_le_pow_left hq4 2
    have h15 : 15 ≤ (2 ^ m₀) ^ 2 - 1 := by omega
    have := Nat.mul_le_mul hq4 h15
    omega
  have hJns : ¬ Group.IsSolvable (slSub 2 k) := Group.IsPerfect.not_isSolvable _
  have hMns : ¬ Group.IsSolvable ↥M := fun hs =>
    hJns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJM.le))
  let Ms : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  have eM : ↥M ≃* ↥Ms := Subgroup.equivMapOfInjective M (mkPSL F) mkPSL_injective
  have hMsns : ¬ Group.IsSolvable ↥Ms := fun hs =>
    hMns (Group.isSolvable_of_surjective (f := eM.symm.toMonoidHom) eM.symm.surjective)
  have hMscard : Nat.card Ms = Nat.card M := (Nat.card_congr eM.toEquiv).symm
  have hdvd : Nat.card (slSub 2 k) ∣ Nat.card M := Subgroup.card_dvd_of_le hJM.le
  have hXcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hFf]
  have hMpos : 0 < Nat.card M := Nat.card_pos
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2)
    (f := f) hFf Ms with
    hEl | ⟨z, -, hcard, hcyc⟩ | ⟨z, -, hcard, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
    ⟨-, -, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm0, hmf, ⟨ePSL⟩⟩ |
    ⟨m, hm0, hmf, ⟨ePGL⟩⟩
  ·
    have := hEl.toIsMulCommutative
    exact (hMsns inferInstance).elim
  ·
    have := hcyc
    exact (hMsns inferInstance).elim
  ·
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, hMscard] at hcard
      omega
    have : NeZero z := ⟨hz0⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact (hMsns (Group.isSolvable_of_surjective (f := eD.symm.toMonoidHom)
      eD.symm.surjective)).elim
  ·
    have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact (hMsns (Group.isSolvable_of_surjective (f := eA.symm.toMonoidHom)
      eA.symm.surjective)).elim
  ·
    have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact (hMsns (Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom)
      eS.symm.surjective)).elim
  ·
    exfalso
    have hcard60 : Nat.card M = 60 := by
      rw [← hMscard, Nat.card_congr eA5.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup]
      simp [Nat.factorial]
    have hle : 2 ^ m₀ * ((2 ^ m₀) ^ 2 - 1) ≤ 60 :=
      Nat.le_of_dvd (by norm_num) (hJcard ▸ hcard60 ▸ hdvd)
    have hge : 60 ≤ 2 ^ m₀ * ((2 ^ m₀) ^ 2 - 1) := by
      have h16 : 4 ^ 2 ≤ (2 ^ m₀) ^ 2 := Nat.pow_le_pow_left hq4 2
      have : 4 * (4 ^ 2 - 1) ≤ 2 ^ m₀ * ((2 ^ m₀) ^ 2 - 1) :=
        Nat.mul_le_mul hq4 (Nat.sub_le_sub_right h16 1)
      simpa using this
    have heq : slSub 2 k = M :=
      Subgroup.eq_of_le_of_card_ge hJM.le (by rw [hcard60, hJcard]; omega)
    exact hJM.ne heq
  ·
    have hNsolv : Group.IsSolvable ↥N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hquot : Group.IsSolvable (↥Ms ⧸ N) := by
      let g : ↥C →* (↥Ms ⧸ N) := (QuotientGroup.mk' N).comp C.subtype
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨n, hn, c, hc, rfl⟩ :=
          Subgroup.mem_sup_of_normal_left.mp (hsup ▸ Subgroup.mem_top x)
        refine ⟨⟨c, hc⟩, ?_⟩
        show ((c : ↥Ms) : ↥Ms ⧸ N) = ((n * c : ↥Ms) : ↥Ms ⧸ N)
        rw [QuotientGroup.eq]
        have := hN.conj_mem n hn c⁻¹
        simpa [mul_assoc] using this
      have := hCcyc
      have hCsolv : Group.IsSolvable ↥C := inferInstance
      exact Group.isSolvable_of_surjective hg
    have : Group.IsSolvable ↥Ms :=
      Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
        intro x hx
        exact ⟨⟨x, (QuotientGroup.eq_one_iff x).mp hx⟩, rfl⟩)
    exact absurd this hMsns
  ·
    have hmcard : Nat.card Ms = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr ePSL.toEquiv, card_psl2_matrixGroup_charTwo, GaloisField.card 2 m hm0]
    have hkm : m₀ ∣ m := by
      refine dvd_of_card_sl2_dvd hm₀1 ?_
      rw [← hmcard, hMscard, ← hJcard]
      exact hdvd
    obtain ⟨a, rfl⟩ := hkm
    have ha : a ∣ d := by
      have : m₀ * a ∣ m₀ * d := hfm ▸ hmf
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
    rcases (Nat.dvd_prime hd).mp ha with ha1 | had
    · exfalso
      rw [ha1] at hmcard
      have : slSub 2 k = M := Subgroup.eq_of_le_of_card_ge hJM.le (by
        rw [← hMscard, hmcard, mul_one, hJcard])
      exact hJM.ne this
    · refine Subgroup.eq_top_of_card_eq M ?_
      rw [← hMscard, hmcard, hXcard, had, hfm]
  ·
    exfalso
    have hmcard : Nat.card Ms = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr ePGL.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm0,
        ← pow_mul, mul_comm m 2, pow_mul]
    have hkm : m₀ ∣ m := by
      refine dvd_of_card_sl2_dvd hm₀1 ?_
      rw [← hmcard, hMscard, ← hJcard]
      exact hdvd
    obtain ⟨a, rfl⟩ := hkm
    have h2a : 2 * a ∣ d := by
      have h1 : m₀ * (2 * a) ∣ m₀ * d := by
        calc m₀ * (2 * a) = 2 * (m₀ * a) := by ring
          _ ∣ f := hmf
          _ = m₀ * d := hfm
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) h1
    have h2 : 2 ∣ d := (Dvd.intro _ rfl).trans h2a
    exact hd2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h2).symm

end CFSG.RankThree.PartOne.SEITZRF
