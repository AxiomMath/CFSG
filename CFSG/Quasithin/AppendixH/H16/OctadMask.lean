module

public import CFSG.Quasithin.Background.HLUCode24
public import CFSG.Quasithin.AppendixH.Common.OctadBasic
public import CFSG.Quasithin.Background.H16TwoM22PfA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def oct1Basis : List ℕ := [3]

@[expose] def oct5Basis : List ℕ := [3, 12, 20, 512, 1024]

@[expose] def octV1 : Subgroup W11 := maskSub 11 oct1Basis

@[expose] def octV5 : Subgroup W11 := maskSub 11 oct5Basis

theorem oct1Basis_lt : ∀ a ∈ oct1Basis, a < 2 ^ 11 := by decide

theorem oct5Basis_lt : ∀ a ∈ oct5Basis, a < 2 ^ 11 := by decide

theorem oct1_nodup : (combos oct1Basis).Nodup := by decide

theorem oct5_nodup : (combos oct5Basis).Nodup := by decide

theorem toW_mem_maskSub_iff_of_lt {n : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ n) {m : ℕ}
    (hm : m < 2 ^ n) : toW n m ∈ maskSub n l ↔ m ∈ combos l := by
  constructor
  · rintro ⟨m', hm', e⟩
    have : m' = m := toW_inj (combos_lt hl m' hm') hm e
    rwa [← this]
  · exact toW_mem_maskSub

theorem card_octV1 : Nat.card ↥octV1 = 2 := by
  rw [octV1, card_maskSub oct1Basis_lt oct1_nodup]
  rfl

theorem card_octV5 : Nat.card ↥octV5 = 32 := by
  rw [octV5, card_maskSub oct5Basis_lt oct5_nodup]
  rfl

theorem rk_octV1 : rk ↥octV1 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, card_octV1]
  exact padicValNat.self (by norm_num)

theorem rk_octV5 : rk ↥octV5 = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, card_octV5, show (32 : ℕ) = 2 ^ 5 by norm_num, padicValNat.prime_pow]

theorem octV1_le_octV5 : octV1 ≤ octV5 := by
  rintro v ⟨m, hm, rfl⟩
  refine toW_mem_maskSub ?_
  have h : m = 0 ∨ m = 3 := by
    simpa [oct1Basis, combos] using hm
  rcases h with rfl | rfl
  · exact zero_mem_combos _
  · exact mem_combos_of_mem (by simp [oct5Basis])

theorem octV1_lt_octV5 : octV1 < octV5 := by
  refine lt_of_le_of_ne octV1_le_octV5 fun h => ?_
  have := card_octV1
  rw [h, card_octV5] at this
  omega

theorem octV5_lt_top : octV5 < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have h1 : toW 11 1 ∈ octV5 := by rw [h]; exact Subgroup.mem_top _
  rw [octV5, toW_mem_maskSub_iff_of_lt oct5Basis_lt (by norm_num)] at h1
  revert h1
  decide

@[expose] noncomputable def ko11 (t : Fin 16) : MulAut W11 :=
  rhoC11 AutPerm le_rfl ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩

theorem ko11_toW (t : Fin 16) (m : ℕ) :
    ko11 t (toW 11 m) = toW 11 (actC11 (koArr t) m) :=
  rhoC11_toW AutPerm le_rfl ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩
    (hasArr_permOfArr (koArr_ok t).1) m

theorem ko11_mem_imgCd_fixO (t : Fin 16) : ko11 t ∈ imgCd fixO :=
  ⟨⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩,
    Subgroup.mem_subgroupOf.2 ((mem_fixO_iff _).2 ⟨t, rfl⟩), rfl⟩

theorem mem_imgCd_fixO_iff (φ : MulAut W11) : φ ∈ imgCd fixO ↔ ∃ t : Fin 16, φ = ko11 t := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hγ)
    refine ⟨t, ?_⟩
    have hγt : γ = ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ := Subtype.ext ht
    rw [hγt]
    rfl
  · rintro ⟨t, rfl⟩
    exact ko11_mem_imgCd_fixO t

theorem actC11_ko_three : ∀ t : Fin 16, actC11 (koArr t) 3 = 3 := by decide +kernel

theorem actC11_ko_unit :
    ∀ t : Fin 16, ∀ j < 11, actC11 (koArr t) (2 ^ j) ^^^ 2 ^ j ∈ combos oct5Basis := by
  decide +kernel

theorem actC11_ko_xor_mem (t : Fin 16) :
    ∀ m < 2 ^ 11, actC11 (koArr t) m ^^^ m ∈ combos oct5Basis := by
  intro m hm
  have h := mem_combos_of_xorLin (xorLin_add_self (xorLin_actC11 (koArr t))) (l := oct5Basis)
    (n := 11) (fun j hj => by
      rw [Nat.xor_comm]
      exact actC11_ko_unit t j hj) m hm
  rwa [Nat.xor_comm] at h

theorem octW_inv (m : ℕ) : (toW 11 m)⁻¹ = toW 11 m :=
  CFSG.Quasithin.H.Coc.toW_inv_self 11 m

theorem ko11_mul_inv_mem (t : Fin 16) (x : W11) : ko11 t x * x⁻¹ ∈ octV5 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [ko11_toW, octW_inv, ← toW_xor]
  exact toW_mem_maskSub (actC11_ko_xor_mem t m hm)

theorem fixV_imgCd_fixO : fixV (imgCd fixO) = octV1 := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rcases fix_koRho11 v fun i => mem_fixV.1 hv _ (ko11_mem_imgCd_fixO (koT i)) with h | h
    · rw [h]
      exact octV1.one_mem
    · rw [h]
      exact toW_mem_maskSub (mem_combos_of_mem (by simp [oct1Basis]))
  · rintro v ⟨m, hm, rfl⟩ φ hφ
    obtain ⟨t, rfl⟩ := (mem_imgCd_fixO_iff φ).1 hφ
    have h : m = 0 ∨ m = 3 := by simpa [oct1Basis, combos] using hm
    rcases h with rfl | rfl
    · rw [toW_zero]
      exact map_one _
    · rw [ko11_toW, actC11_ko_three]

theorem oct5_commutators : ∀ b ∈ oct5Basis, ∃ t : Fin 16, ∃ m < 2 ^ 11,
    actC11 (koArr t) m ^^^ m = b := by
  decide +kernel

theorem commV_imgCd_fixO : CFSG.Quasithin.commV (imgCd fixO) = octV5 := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le octV5).2 ?_
    rintro _ ⟨φ, hφ, x, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_imgCd_fixO_iff φ).1 hφ
    exact ko11_mul_inv_mem t x
  · rintro _ ⟨m, hm, rfl⟩
    refine mem_of_combos (fun m => toW 11 m ∈ CFSG.Quasithin.commV (imgCd fixO)) (by
      rw [toW_zero]; exact (CFSG.Quasithin.commV (imgCd fixO)).one_mem) (fun a b ha hb => by
      rw [toW_xor]; exact (CFSG.Quasithin.commV (imgCd fixO)).mul_mem ha hb) oct5Basis (fun b hb => ?_) m hm
    obtain ⟨t, m', hm', hb'⟩ := oct5_commutators b hb
    have hgen : ko11 t (toW 11 m') * (toW 11 m')⁻¹ ∈ CFSG.Quasithin.commV (imgCd fixO) :=
      Subgroup.subset_closure ⟨ko11 t, ko11_mem_imgCd_fixO t, toW 11 m', rfl⟩
    rw [octW_inv] at hgen
    rw [← hb', toW_xor, ← ko11_toW]
    exact hgen

end CFSG.ASVolI.H16
