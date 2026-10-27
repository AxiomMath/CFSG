module

public import CFSG.RankThree.GF2n.Stroth80.Sec78Om4Count
public import CFSG.RankThree.GF2n.Stroth80.Sec78RootOrdersSp
public import CFSG.RankThree.GF2n.Stroth80.Sec57B
public import CFSG.RankThree.GF2n.Stroth80.Sec310NotQB
public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main
public import CFSG.RankThree.GF2n.Stroth80.Sec78OmegaPlusFour
public import CFSG.RankThree.GF2n.Stroth80.Sec78RootOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_charP (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) :
    CharP K 2 := by
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  exact charP_two_of_card_eq_two_pow (hK.trans he)

theorem sec7ctr_Rt_le_om4 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hA7 : Sec7AExistsStatement) (hA8 : Sec8AExistsStatement)
    (hPtsΩ : Sec5NatPointsOmegaStatement) (hPtsSp : Sec5NatPointsSpStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2)
    {r : G} (hr : Sec7A hc t r) {s : G} (hsL : s ∈ LB M Q B) (hsQ : s ∉ Q)
    (hRle : Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) :
    Rt M (LB M Q B) s ≤ Rt M (LB M Q B) t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hss5 : Sec5Hyp hc n s := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hsL, hsQ⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := by omega
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs5 (Or.inr hs.omegaNat)
  have hRM : Rt M (LB M Q B) s ≤ M := hc.Rt_le_M s
  have hZVs : Z ≤ Vt M (LB M Q B) B Z s := sec39_Z_le_Vt
  have hZVt : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hCNs : ∀ x, x ∈ hc.CN s ↔
      x ∈ Rt M (LB M Q B) s ∧ ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z := by
    intro x
    rw [Ctx.mem_CN, hV]
  have hNle : hc.CN t ≤ hc.CN s := fun x hx =>
    (hCNs x).mpr ⟨hRle (Ctx.mem_CN.mp hx).1, (Ctx.mem_CN.mp hx).2⟩
  have hNtR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hNsR : hc.CN s ≤ Rt M (LB M Q B) s := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRtNs : Rt M (LB M Q B) t ⊓ hc.CN s = hc.CN t := by
    refine le_antisymm (fun x hx => Ctx.mem_CN.mpr ⟨hx.1, ((hCNs x).mp hx.2).2⟩) ?_
    exact fun x hx => ⟨hNtR hx, hNle hx⟩
  have hLN : LB M Q B ⊓ hc.CN s = LB M Q B ⊓ hc.CN t := by
    ext x
    constructor
    · rintro ⟨hxL, hxN⟩
      exact ⟨hxL, (hRtNs ▸ (⟨le_Rt (M := M) (LB M Q B) ht hxL, hxN⟩ :
        x ∈ Rt M (LB M Q B) t ⊓ hc.CN s) : x ∈ hc.CN t)⟩
    · rintro ⟨hxL, hxN⟩
      exact ⟨hxL, hNle hxN⟩
  obtain ⟨d, hd4, hVcard, hLcard⟩ := sec7ctr_card_LB hPtsΩ hc hs hr
  have hnatom := hom
  obtain ⟨K, fK, finK, hK, b, c, hirr, hrep⟩ := hom
  haveI : CharP K 2 := sec7ctr_charP hc hK
  have hrep' := hrep
  obtain ⟨φ, hφr, hφk, -⟩ := hrep
  have hd : d = 4 := by
    have h1 := sec7ctr_pin hrep' hK hZVt hq2 hVcard
    simpa using h1.symm
  have hLcard' : Nat.card ↥(LB M Q B) = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 := by
    rw [hLcard, hd]
  have hVcard4 : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ 4 := by
    rw [hVcard, hd]
  have hRt := sec7ctr_card_om4 hNtR hirr φ hφr hφk
  rw [hK] at hRt
  set F := Nat.card Z ^ 2 * ((Nat.card Z ^ 2) ^ 2 - 1) with hF
  have hNpos : 0 < Nat.card ↥(hc.CN t) := Nat.card_pos
  have hF2 : 1 < (Nat.card Z ^ 2) ^ 2 - 1 := by
    have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
    have : 256 ≤ (Nat.card Z ^ 2) ^ 2 := by nlinarith
    omega
  have hVs4 : Nat.card ↥(Vt M (LB M Q B) B Z s) = Nat.card Z * Nat.card Z ^ 4 := by
    rw [hV, hVcard4]
  rcases h310 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen s hsL hsQ with
    hRL | ⟨K', fK', finK', hK', hfam⟩
  ·
    exfalso
    have hRtL : Rt M (LB M Q B) t = LB M Q B :=
      le_antisymm (hRle.trans hRL.le) (le_Rt (M := M) (LB M Q B) ht)
    have hNL : hc.CN t ≤ LB M Q B := fun x hx => hRtL ▸ hNtR hx
    have hLN' : LB M Q B ⊓ hc.CN t = hc.CN t := inf_eq_right.mpr hNL
    have h1 : Nat.card ↥(Rt M (LB M Q B) t) = Nat.card ↥(LB M Q B) := by rw [hRtL]
    rw [hRt, hLcard', hLN'] at h1
    have h2 : Nat.card ↥(hc.CN t) * F = Nat.card ↥(hc.CN t) * Nat.card Z ^ 2 := h1
    have h3 := Nat.eq_of_mul_eq_mul_left hNpos h2
    have h4 : Nat.card Z ^ 2 * 1 ≤ Nat.card Z ^ 2 * ((Nat.card Z ^ 2) ^ 2 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : 0 < Nat.card Z ^ 2 := by positivity
    have h6 : Nat.card Z ^ 2 * 2 ≤ Nat.card Z ^ 2 * ((Nat.card Z ^ 2) ^ 2 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [← hF] at h6
    omega
  · haveI : CharP K' 2 := sec7ctr_charP hc hK'
    rcases hfam with ⟨m', hm', hnat'⟩ | ⟨m', hm', hnat'⟩ | ⟨m', hm', hnat'⟩ |
      ⟨m', b', c', hm', hirr', hnat'⟩
    ·
      exfalso
      exact hnotQB (hV ▸ stroth310SL_of_34 h34 G M Q Z B hc n s hss5
        ⟨K', fK', finK', hK', m', hm', hnat'⟩)
    ·
      exfalso
      have hι := sec7ctr_pin hnat' hK' hZVs hq2 hVs4
      simp only [Fintype.card_sum, Fintype.card_fin] at hι
      have hm2 : m' = 2 := by omega
      subst hm2
      have h8 : Sec8Hyp hc n s := ⟨hss5, 2, le_rfl, ⟨K', fK', finK', hK', hnat'⟩⟩
      obtain ⟨r', hr'⟩ := hA8 G M Q Z B hc n s h8
      obtain ⟨m'', hm'', hVm, hLm⟩ := sec7ctr_card_LB_sp hPtsSp hc h8 hr'
      have h1 : Nat.card Z ^ (2 * m'') = Nat.card Z ^ 4 :=
        Nat.eq_of_mul_eq_mul_left (by omega) (hVm.symm.trans hVs4)
      have h2 : 2 * m'' = 4 := Nat.pow_right_injective hq2 h1
      have h3 : Nat.card ↥(LB M Q B) =
          Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 3 := by
        rw [hLm, hLN, h2]
      have hXpos : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN t) := Nat.card_pos
      have h4 : Nat.card Z ^ 3 = Nat.card Z ^ 2 :=
        Nat.eq_of_mul_eq_mul_left hXpos (h3.symm.trans hLcard')
      have h5 := Nat.pow_right_injective hq2 h4
      omega
    ·
      exfalso
      have hι := sec7ctr_pin hnat' hK' hZVs hq2 hVs4
      simp only [Fintype.card_sum, Fintype.card_fin] at hι
      have hm2 : m' = 2 := by omega
      subst hm2
      obtain ⟨φ', hφ'r, hφ'k, -⟩ := hnat'
      have hcm := card_inf_mul_card_map hRle φ' hφ'k
      rw [hRtNs, hRt] at hcm
      have h1 : Nat.card ↥(((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ') = F :=
        Nat.eq_of_mul_eq_mul_left hNpos hcm
      have hle : ((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ' ≤ φ'.range := by
        rintro _ ⟨x, _, rfl⟩
        exact ⟨x, rfl⟩
      have hdvd : Nat.card ↥(((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ') ∣
          Nat.card ↥φ'.range := Subgroup.card_dvd_of_le hle
      rw [h1, hφ'r] at hdvd
      have hKK : Nat.card K = Nat.card K' := hK.trans hK'.symm
      refine sec7ctr_not_dvd_card_omegaPlusFour hKK (by omega) hirr ?_
      rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
        CFSG.SeitzReduction.F4Pilot.ordSL_two, hK]
      exact hdvd
    ·
      have hι := sec7ctr_pin hnat' hK' hZVs hq2 hVs4
      simp only [Fintype.card_sum, Fintype.card_fin] at hι
      have hm2 : m' = 2 := by omega
      subst hm2
      have hnat'' := hnat'
      obtain ⟨φ', hφ'r, hφ'k, -⟩ := hnat'
      have hcm := card_inf_mul_card_map hRle φ' hφ'k
      rw [hRtNs, hRt] at hcm
      have h1 : Nat.card ↥(((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ') = F :=
        Nat.eq_of_mul_eq_mul_left hNpos hcm
      have hrangeF : Nat.card ↥φ'.range = F := by
        rw [hφ'r, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr',
          CFSG.SeitzReduction.F4Pilot.ordSL_two, hK']
      have hle : ((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ' ≤ φ'.range := by
        rintro _ ⟨x, _, rfl⟩
        exact ⟨x, rfl⟩
      have hmap : ((Rt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) s)).map φ' = φ'.range :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hrangeF])
      have hsurj : ∀ x ∈ Rt M (LB M Q B) s, ∃ ρ ∈ Rt M (LB M Q B) t, ρ⁻¹ * x ∈ hc.CN s := by
        intro x hx
        have hxr : φ' ⟨x, hx⟩ ∈ φ'.range := ⟨_, rfl⟩
        rw [← hmap] at hxr
        obtain ⟨ρ', hρ', hρx⟩ := Subgroup.mem_map.mp hxr
        refine ⟨(ρ' : G), Subgroup.mem_subgroupOf.mp hρ', ?_⟩
        have hk : ρ'⁻¹ * ⟨x, hx⟩ ∈ φ'.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hρx, inv_mul_cancel]
        rw [hφ'k, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hnotP : ¬ OmegaPlusNat hc s 2 := by
        rintro ⟨K'', fK'', finK'', hK'', hnatP⟩
        haveI : CharP K'' 2 := sec7ctr_charP hc hK''
        obtain ⟨φ'', hφ''r, hφ''k, -⟩ := hnatP
        have e1 := sec7ctr_card_eq_mul_range hNsR φ'' hφ''k
        have e2 := sec7ctr_card_eq_mul_range hNsR φ' hφ'k
        rw [e1] at e2
        have e3 : Nat.card ↥φ''.range = Nat.card ↥φ'.range :=
          Nat.eq_of_mul_eq_mul_left Nat.card_pos e2
        refine sec7ctr_not_dvd_card_omegaPlusFour (hK'.trans hK''.symm) (by omega) hirr' ?_
        rw [← hφ'r, ← hφ''r, e3]
      have hs_s : Sec7Hyp hc n s :=
        { toSec5 := hss5
          notPlus4 := hnotP
          orth := ⟨2, le_rfl, Or.inr ⟨K', fK', finK', hK', b', c', hirr', hnat''⟩⟩
          large := lt_of_lt_of_le hs.large (Nat.card_mono (Set.toFinite _) hNle) }
      obtain ⟨r', hr'⟩ := hA7 G M Q Z B hc n s hs_s
      obtain ⟨ρ, hρ, hν⟩ := hsurj r' hr'.mem
      have hρM : ρ ∈ M := hc.Rt_le_M t hρ
      have hr'M : r' ∈ M := hRM hr'.mem
      have hr'eq : r' = ρ * (ρ⁻¹ * r') := by group
      have hνV : ∀ v ∈ Vt M (LB M Q B) B Z s, ⁅ρ⁻¹ * r', v⁆ ∈ Z := (Ctx.mem_CN.mp hν).2
      have hBV : B ≤ Vt M (LB M Q B) B Z s := hc.B_le_Vt hsL
      have h2 := sec7ctr_conj_B_sup_Z hBV hνV
      have hBZ : conjSubgroup r' B ⊔ Z = conjSubgroup ρ B ⊔ Z := by
        calc conjSubgroup r' B ⊔ Z = conjSubgroup ρ (conjSubgroup (ρ⁻¹ * r') B) ⊔ Z := by
              rw [← conjSubgroup_mul, ← hr'eq]
          _ = conjSubgroup ρ (conjSubgroup (ρ⁻¹ * r') B ⊔ Z) := by
              rw [conjSubgroup_sup', hc.conj_Z_eq hρM]
          _ = conjSubgroup ρ (B ⊔ Z) := by rw [h2]
          _ = conjSubgroup ρ B ⊔ Z := by rw [conjSubgroup_sup', hc.conj_Z_eq hρM]
      have hLeq := hc.conj_LB_eq_of_conj_BZ hr'M hρM hBZ
      rw [hr'.gen, hc.LB_conj hr'M, hLeq]
      exact sup_le (le_Rt (M := M) (LB M Q B) ht) (hc.conj_LB_le_Rt ht hρ)

end CFSG.RankThree.GF2n.Stroth80
