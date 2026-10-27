module

public import CFSG.Quasithin.Vol2.Ch12Sec5L6a
public import CFSG.Quasithin.Vol2.Ch12Sec5Odd
public import CFSG.Quasithin.Background.E6Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 Matrix
open scoped IsMulCommutative

@[expose] def Lemma12_5_4six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G)

namespace S125L6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_of_mQuot (hV2 : IsPGroup 2 V) (hcard : Nat.card V = 2 ^ 10) {U : Subgroup G}
    (hUV : U ≤ V) (hU : E3.mQuot V U = 3) : Nat.card U = 2 ^ 7 := by
  have h1 := E3.relIndex_eq_two_pow hV2 U
  rw [hU] at h1
  have h2 := Subgroup.relIndex_mul_card (H := U) (K := V)
  rw [inf_of_le_left hUV, h1, hcard] at h2
  omega

theorem false_of_codim3 (h1222 : Stmt12_2_2) (h12210 : Stmt12_2_10)
    (hE612 : ASInputs.AS_E_6_12) (h4 : Lemma12_5_4six) (hH : Hyp125 G T L V) (F : Frame125 T L V)
    (hE : E6.HypE61 T (Subgroup.normalizer (L : Set G)) V) (hr : E3.rParam V = 3)
    {U : Subgroup G} (hUV : U ≤ V) (hU3 : E3.mQuot V U = 3)
    (hCN : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) : False := by
  have hf := S125Ex.Facts125.of h1222 hH
  have := hf.comm
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hUc : Nat.card U = 2 ^ 7 := card_of_mQuot hE.isPGroup_V hf.card hUV hU3
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hUc
    norm_num at hUc
  have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun h =>
    hCN ((le_inf h le_rfl).trans (E6.inf_centralizer_le_normalizer hE hUV hU1))
  have hne : M ⊓ Subgroup.centralizer (U : Set G) ≠ M ⊓ Subgroup.centralizer (V : Set G) := by
    intro heq
    have h1 := (hE612 G T M V U hE hU1 hUV heq hCM).2
    rw [hr] at h1
    exact absurd h1 (by decide)
  have hle : M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hUV)
  obtain ⟨g, hg, hgV⟩ : ∃ g ∈ M ⊓ Subgroup.centralizer (U : Set G),
      g ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hne (le_antisymm (fun x hx => ⟨hx.1, hc x hx⟩) hle)
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    E6.inf_centralizer_le_normalizer hE hUV hU1 hg
  have hMV : autOn M V = autOn L V := S125L6a.autOn_normalizer_eq h12210 hH.hyp F
  have ha₀ : conjAct V ⟨g, hgN⟩ ∈ autOn L V := by
    rw [← hMV]
    exact mem_autOn_iff_exists.mpr ⟨g, hgN, hg.1, rfl⟩
  set a : ↥(autOn L V) := ⟨_, ha₀⟩ with ha_def
  have ha1 : a ≠ 1 := by
    intro h
    apply hgV
    have h1 : conjAct V ⟨g, hgN⟩ = 1 := congrArg Subtype.val h
    exact A4.conjAct_eq_one_iff.1 h1
  set U' : Subgroup ↥V := U.subgroupOf V with hU'
  have hU'c : Nat.card U' = 2 ^ 7 := by
    rw [← hUc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  have hfixa : ∀ u ∈ U', (a : MulAut ↥V) u = u := by
    intro u hu
    apply Subtype.ext
    change g * (u : G) * g⁻¹ = u
    rw [Subgroup.mem_subgroupOf] at hu
    have h1 : (u : G) * g = g * u := Subgroup.mem_centralizer_iff.1 hg.2 u hu
    rw [← h1]
    group
  have hfixpow : ∀ n : ℕ, ∀ u ∈ U', ((a ^ n : ↥(autOn L V)) : MulAut ↥V) u = u := by
    intro n
    induction n with
    | zero => intro u _; rfl
    | succ n ih =>
      intro u hu
      rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply, hfixa u hu, ih u hu]
  have hU'le : ∀ b : ↥(autOn L V), (∀ u ∈ U', (b : MulAut ↥V) u = u) →
      U' ≤ fixV (V := ↥V) (Subgroup.zpowers (b : MulAut ↥V)) := fun b hb u hu =>
    S125L6a.mem_fixV_zpowers_iff.2 (hb u hu)
  have hcard128 : ∀ b : ↥(autOn L V), (∀ u ∈ U', (b : MulAut ↥V) u = u) →
      128 ≤ Nat.card (fixV (V := ↥V) (Subgroup.zpowers (b : MulAut ↥V))) := fun b hb => by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← hU'c]
    exact Subgroup.card_le_of_le (hU'le b hb)
  have hoa : orderOf a ≠ 0 := (orderOf_pos a).ne'
  by_cases h2 : 2 ∣ orderOf a
  ·
    set b := a ^ (orderOf a / 2) with hb
    have hbo : orderOf b = 2 := orderOf_pow_orderOf_div hoa h2
    have hbU := hfixpow (orderOf a / 2)
    rcases S125L6a.card_fixV_invol F b hbo with ⟨⟨c, hc⟩, h128⟩ | h64
    ·
      have hUeq : U' = fixV (V := ↥V) (Subgroup.zpowers (b : MulAut ↥V)) :=
        Subgroup.eq_of_le_of_card_ge (hU'le b hbU) (by rw [h128, hU'c]; norm_num)
      have hj := S125L5a.fixV_j1 F
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, S125L6a.fixV_conj,
        ← hUeq] at hj
      obtain ⟨l, hlV, hlL, hlc⟩ := mem_autOn_iff_exists.mp c.2
      apply hCM
      intro x hx
      have hx' : l * x * l⁻¹ ∈ Subgroup.centralizer (F.V6 : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw' : w ∈ (U'.map (c : MulAut ↥V).toMonoidHom).map V.subtype := by
          rw [hj]
          exact Subgroup.mem_sup_right hw
        obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hw'
        have hcu : (((c : MulAut ↥V) u : ↥V) : G) = l * (u : G) * l⁻¹ := by
          rw [← hlc]
          rfl
        have hu' : (u : G) ∈ U := hu
        have hxu : (u : G) * x = x * u := Subgroup.mem_centralizer_iff.1 hx u hu'
        change (((c : MulAut ↥V) u : ↥V) : G) * (l * x * l⁻¹) =
          l * x * l⁻¹ * (((c : MulAut ↥V) u : ↥V) : G)
        rw [hcu]
        calc l * (u : G) * l⁻¹ * (l * x * l⁻¹) = l * ((u : G) * x) * l⁻¹ := by group
          _ = l * (x * u) * l⁻¹ := by rw [hxu]
          _ = l * x * l⁻¹ * (l * (u : G) * l⁻¹) := by group
      have hxM : l * x * l⁻¹ ∈ M :=
        h4 G T L V F hH ((Subgroup.centralizer_le_normalizer _) hx')
      have hlM : l ∈ M := Subgroup.le_normalizer hlL
      have e : x = l⁻¹ * (l * x * l⁻¹) * l := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem hlM) hxM) hlM
    · have h1 := hcard128 b hbU
      rw [h64] at h1
      norm_num at h1
  ·
    have ho1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.1 h)
    have hp : (orderOf a).minFac.Prime := Nat.minFac_prime ho1
    have hpd : (orderOf a).minFac ∣ orderOf a := Nat.minFac_dvd _
    have hp2 : (orderOf a).minFac ≠ 2 := fun h => h2 (h ▸ hpd)
    set b := a ^ (orderOf a / (orderOf a).minFac) with hb
    have hbo : orderOf b = (orderOf a).minFac := orderOf_pow_orderOf_div hoa hpd
    have hbU := hfixpow (orderOf a / (orderOf a).minFac)
    have hlt := S125Odd.nFix_lt hp hp2 ((MulEquiv.orderOf_eq F.γ b).trans hbo)
    have hP : ∀ v : ↥V, v ∈ fixV (V := ↥V) (Subgroup.zpowers (b : MulAut ↥V)) ↔
        JonesParshall.wedgeMat ((F.γ b : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (F.e v) =
            Multiplicative.toAdd (F.e v) := by
      intro v
      rw [S125L6a.mem_fixV_zpowers_iff]
      have h1 := S125L5a.fix_iff F (F.γ b) v
      rw [MulEquiv.symm_apply_apply] at h1
      exact h1
    have heq := S125L5a.card_of_coords F (p := fun x => JonesParshall.wedgeMat
      ((F.γ b : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        x = x) hP
    rw [← S125Odd.nFix_eq] at heq
    have h1 := hcard128 b hbU
    omega

end S125L6

open S125L6

theorem lemma12_5_6_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h12210 : Stmt12_2_10) (hE63 : ASInputs.AS_E_6_3) (hE612 : ASInputs.AS_E_6_12)
    (h4 : Lemma12_5_4six) : Lemma12_5_6 := by
  intro G _ _ T L V hH hV
  obtain ⟨F⟩ := frame125Exists_of h1222 G T L V hH
  have hf := S125Ex.Facts125.of h1222 hH
  have := hf.comm
  have hyp := hH.hyp
  have hE : E6.HypE61 T (Subgroup.normalizer (L : Set G)) V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  have hm : E3.mParam (autI hV (Subgroup.normalizer (L : Set G))) = 3 :=
    S125L6a.mParam_eq h12210 hyp F hV hf.card
  obtain ⟨hr3, hs⟩ := hE63 G T (Subgroup.normalizer (L : Set G)) V hV hE (by rw [hm]; norm_num)
  rw [hm] at hr3 hs
  refine ⟨?_, hm, hs⟩
  by_contra hr
  have hr' : E3.rParam V = 3 := le_antisymm (not_lt.1 hr) (by exact_mod_cast hr3)
  obtain ⟨U, hUV, hCN, hUr⟩ :=
    E6.exists_eq_rParam' (V := V) (by rw [hr']; exact ENat.natCast_ne_top 3)
  have hU3 : E3.mQuot V U = 3 := by
    rw [hr'] at hUr
    exact_mod_cast hUr
  exact false_of_codim3 h1222 h12210 hE612 h4 hH F hE hr' hUV hU3 hCN

end CFSG.Quasithin.H13
