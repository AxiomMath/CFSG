module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepNorm
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4E9
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Five

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

open L1294 L128P in
theorem case1294Five_of_DI (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hDI : Case1294FiveDI) : Case1294Five := by
  intro G _ _ T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  classical
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := exists_gens hV₁2 hV₂4
  have haV := hs.v2.1 haV₂
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV
  have hπa : D.π a ≠ 0 := by
    intro h0
    rw [L128A.HatU.π_eq_zero_iff D haU] at h0
    have h1 : a ∈ V ⊓ zU128 V V₁ := ⟨haV, h0⟩
    rw [lemma12_8_8_three h1222 h12213 hs] at h1
    exact haV₁ h1
  obtain ⟨x, hxΓ, y, hyΓ, hx3, hy3, hxy, hx1, hy1, hxy1, hxy2, hxa, hya⟩ :=
    L1294E.exists_e9 (L128A.HatU.B_nondegenerate D) h5 hπa
  set C := centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ with hCdef
  have hCN : C ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun g hg =>
    le_normalizer_conjClosure V _ hg.1
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hmemC : ∀ γ ∈ D.img K₁, γ ^ 3 = 1 → γ (D.π a) = D.π a → γ ∈ D.img C := by
    intro γ hγ hγ3 hγa
    obtain ⟨h, hhK, hhN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    set hN : ↥(Subgroup.normalizer (u128 V V₁ : Set G)) := ⟨h, hhN⟩
    obtain ⟨e, m, hm3, hn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' 3 (by norm_num)
    have hord : orderOf ((hN ^ m : ↥(Subgroup.normalizer (u128 V V₁ : Set G))) : G) = 3 ^ e := by
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm3)
      rw [Subgroup.coe_pow, orderOf_pow' h hm0.ne', hn, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ hm0]
    have hmK : ((hN ^ m : ↥(Subgroup.normalizer (u128 V V₁ : Set G))) : G) ∈ K₁ := by
      rw [Subgroup.coe_pow]
      exact K₁.pow_mem hhK m
    have key : ∀ j : ℕ, (D.ρ hN ^ j) (D.π a) = D.π a := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, LinearEquiv.mul_apply, hγa, ih]
    have hmfix : D.ρ (hN ^ m) (D.π a) = D.π a := by
      rw [map_pow]
      exact key m
    have hmN := L1294R.normalizes_V₂ h1222 h12213 hDI hcx hs hLK hK hK4 D h5 himg haV₂ haV₁
      (hN ^ m) hmK ⟨e, hord⟩ hmfix
    have hmC : D.ρ hN ^ m ∈ D.img C := by
      rw [← map_pow]
      exact (L128A.HatU.mem_img D).2 ⟨_, mem_centralizerMod_of_mem_normalizer hs
        (hK₁G₁ hmK) hmN, (hN ^ m).2, rfl⟩
    have hpm : D.ρ hN ^ m = D.ρ hN ^ (m % 3) := by
      conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hγ3, one_pow, one_mul]
    obtain h0 | h1 | h2 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) hm3
    · rwa [hpm, h1, pow_one] at hmC
    · rw [hpm, h2] at hmC
      have : D.ρ hN = (D.ρ hN ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hγ3, one_mul]
      rw [this]
      exact (D.img C).pow_mem hmC 2
  have hxC := hmemC x (L1294E.mem_of_relIndex_le_two himg hxΓ hx3) hx3 hxa
  have hyC := hmemC y (L1294E.mem_of_relIndex_le_two himg hyΓ hy3) hy3 hya
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr : 2 ≤ CFSG.Open.pRank 3 (D.img C) := by
    rw [← pRank_top_subtype (p := 3)]
    refine Rank8.two_le_pRank_three_of (x := ⟨x, hxC⟩) (y := ⟨y, hyC⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subtype.ext (by simpa using hx3)
    · exact Subtype.ext (by simpa using hy3)
    · exact Subtype.ext (by simpa using hxy)
    · exact fun h => hx1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy1 (by simpa using congrArg Subtype.val h)
    · exact fun h => hxy2 (by simpa using congrArg Subtype.val h)
  rw [L1294.img_eq_range D hCN, ← pRank_top_subtype (p := 3)] at hpr
  have h2 := two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (D.ρ.comp (Subgroup.inclusion hCN)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hpr
  rw [pRank_top_subtype (p := 3)] at h2
  have h3 : CFSG.Open.pRank 3 C ≤ 1 := thirteen_eight h1222 h12213 hs
  omega

end CFSG.Quasithin.H13
