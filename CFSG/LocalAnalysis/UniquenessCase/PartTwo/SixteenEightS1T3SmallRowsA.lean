module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Engine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3RankOm6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixVecOm6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_exists_good_vector_omegaMinus6 (h : S16gRowCtx D V₀ V L hV)
    (h3 : 3 ∈ D.sig) (hV₀ : V₀ = ⊥)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (hL : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))))
    (hmultnot : ¬ 3 ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)))
    (hker : 3 ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  classical
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  obtain ⟨w, hw1, hwT, y, hyL, hyo, hyw⟩ := ThreeNat.exists_fix_vector_omegaMinus6 hT hL
  obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV w
  have hx0 : x.val ∉ V₀ := by
    intro hmem
    have hx1 : x = (1 : IntMod V hV) :=
      Subtype.ext (Subgroup.mem_bot.1 (by rwa [hV₀] at hmem))
    exact hw1 (by rw [← hx, hx1, map_one])
  have hxne : x.val ≠ 1 := fun h1 => hx0 (by rw [hV₀]; exact Subgroup.mem_bot.2 h1)
  have hcomm : ∀ t ∈ D.T, t * x.val = x.val * t := by
    intro t ht
    have hst : t ∈ stabTil V₀ V := hMst (D.sylowM.le ht)
    have hmem : actTil V₀ V hV ⟨t, hst⟩ ∈ barSub V₀ V hV D.T :=
      actTil_mem_barSub V₀ V hV ht hst
    have hfix' : actTil V₀ V hV ⟨t, hst⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
      rw [hx]
      exact hwT (actTil V₀ V hV ⟨t, hst⟩) hmem
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix'
    have h3' : t * x.val * t⁻¹ = x.val := by
      have hmem0 : (t * x.val * t⁻¹) * x.val⁻¹ ∈ (⊥ : Subgroup G) := by
        simpa using (le_of_eq hV₀) hfix'
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.1 hmem0)
    calc t * x.val = (t * x.val * t⁻¹) * t := by group
      _ = x.val * t := by rw [h3']
  obtain ⟨m, hmo, hmy⟩ :=
    s16g_exists_lift D h.std h.setting h.quasi hz Nat.prime_three (by norm_num) hmultnot hMst
      hyL hyo
  have hmx : (m : G) * x.val = x.val * (m : G) := by
    have hmfix : barHom V₀ V hV hMst m (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
      rw [hmy, hx]
      exact hyw
    have hfix' : actTil V₀ V hV (Subgroup.inclusion hMst m) (mkTil V₀ V hV x) =
        mkTil V₀ V hV x := hmfix
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix'
    have hmem0 : ((m : G) * x.val * (m : G)⁻¹) * x.val⁻¹ ∈ (⊥ : Subgroup G) := by
      simpa using (le_of_eq hV₀) hfix'
    have h3' : (m : G) * x.val * (m : G)⁻¹ = x.val :=
      mul_inv_eq_one.mp (Subgroup.mem_bot.1 hmem0)
    calc (m : G) * x.val = ((m : G) * x.val * (m : G)⁻¹) * (m : G) := by group
      _ = x.val * (m : G) := by rw [h3']
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1
  haveI hnorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
    rw [← ker_barHom V₀ V hV hMn hMst]
    exact MonoidHom.normal_ker _
  have hKcard : 3 ∣ Nat.card ↥((F11.CTilde D.M V₀ V).subgroupOf D.M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv]
    exact hker
  have hmK : m ∉ (F11.CTilde D.M V₀ V).subgroupOf D.M := by
    intro hm
    have h1 : m ∈ (barHom V₀ V hV hMst).ker := by
      rw [ker_barHom V₀ V hV hMn hMst]
      exact hm
    have hbar : barHom V₀ V hV hMst m = 1 := MonoidHom.mem_ker.1 h1
    rw [hmy] at hbar
    rw [hbar, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  obtain ⟨B, hBp, hBc, hBle⟩ :=
    s16g_exists_noncyclic_of_kernel (M := ↥D.M) (K := (F11.CTilde D.M V₀ V).subgroupOf D.M)
      Nat.prime_three hKcard hmo hmK
  have hBcent : B ≤ (Subgroup.centralizer ({x.val} : Set G)).comap D.M.subtype := by
    refine hBle.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hmx.symm
    · intro k hk
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hkC : (k : G) ∈ F11.CTilde D.M V₀ V := Subgroup.mem_subgroupOf.1 hk
      obtain ⟨-, hgs, hact⟩ := (mem_cTilde_iff hV hMn).1 hkC
      have hcomm' : ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ V₀ :=
        (actTil_eq_one_iff V₀ V hV ⟨_, hgs⟩).1 hact
      have h1 : (k : G) * x.val * (k : G)⁻¹ * x.val⁻¹ ∈ (⊥ : Subgroup G) := by
        simpa using (le_of_eq hV₀) (hcomm' x.val x.val_mem)
      have h2 : (k : G) * x.val * (k : G)⁻¹ = x.val :=
        mul_inv_eq_one.mp (Subgroup.mem_bot.1 h1)
      have h3 : (k : G) * x.val = x.val * (k : G) := mul_inv_eq_iff_eq_mul.mp h2
      simpa using h3.symm
  have hXp : IsPGroup 3 (B.map D.M.subtype) := hBp.map D.M.subtype
  have hXc : ¬ IsCyclic (B.map D.M.subtype) :=
    SpLift.not_isCyclic_map D.M.subtype D.M.subtype_injective hBc
  have hXM : B.map D.M.subtype ≤ D.M := Subgroup.map_subtype_le B
  have hXx : B.map D.M.subtype ≤ Subgroup.centralizer ({x.val} : Set G) := by
    rintro z ⟨b, hb, rfl⟩
    exact hBcent hb
  have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
  exact ⟨x.val, x.val_mem, hxne, hcomm,
    centralizer_le_of_noncyclic D h.std.h61 h3 hXM hXp hXc hxne hx2 hXx⟩

theorem S16gRowCtx.false_of_omegaMinus6_Z7 (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) : False := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  obtain ⟨hsimple, hmult⟩ :=
    s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, le_rfl⟩))))
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := hsimple
  have hmultnot : ¬ 3 ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) := by
    intro h3dvd
    obtain ⟨k, hk⟩ := hmult
    rw [hk] at h3dvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3dvd) (by norm_num)
  have hKnc : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    exact CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple h.quasi
      (fun a b => hc.is_comm.comm a b)
  have hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))) := by
    rw [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc, Subgroup.card_bot]
    exact odd_one
  have hrk : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3 :=
    ThreeNat.pRank_three_le_three_omegaMinus6 hT h7 hL hK
  have hker : 3 ∣ Nat.card (F11.CTilde D.M V₀ V) :=
    s16g_dvd_card_cTilde D h.std h.setting h3 hrk
  obtain ⟨I, -, hTI, hnatShape⟩ := ThreeNat.exists_stable_natural hT
  have hnat : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) (lBar V₀ V hV L) I
      (I ⊓ fixV (lBar V₀ V hV L)) 1 :=
    s16t3_shape_branch_omegaMinus hnatShape hL
  have hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) 2 := by
    simpa using ThreeNat.parab_omegaMinus hT (n := 6) (by norm_num) hL hTI hnat
  have hcase : V₀ ≠ ⊥ ∨ 3 ≤ (2 : ℕ) ∨ ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
    by_cases hV₀ : V₀ = ⊥
    · obtain ⟨v, hvV, -, hvT, hvC⟩ :=
        s16t3_exists_good_vector_omegaMinus6 h h3 hV₀ hT hL hz hmultnot hker
      exact Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩)
    · exact Or.inl hV₀
  exact h.false_of_t3Parab h3 hT hsimple hmult hP (by norm_num) hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
