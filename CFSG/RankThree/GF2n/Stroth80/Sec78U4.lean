module

public import CFSG.RankThree.GF2n.Stroth80.Sec78HypFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec78SylowConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_U4 (h34 : Stroth34Statement) (hA7 : Sec7AExistsStatement)
    (hPtsΩ : Sec5NatPointsOmegaStatement) (hZt : Sec7ZtStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    (hsQ : s ∉ Q) {h : G} (hh : h ∈ M) (hsh : s ∈ LB M Q (conjSubgroup h B)) :
    ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup h B ⊔ Z = conjSubgroup ρ B ⊔ Z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := by omega
  obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  have hc'' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hs'' : Sec7Hyp hc'' n s := sec7ctr_hyp_frame hc hs hh hsh hsQ hR hV
  have hR'' : Rt M (LB M Q (conjSubgroup h B)) s = Rt M (LB M Q B) t := by
    rw [hc.LB_conj hh, sec7ctr_Rt_conj_frame hh s, hR]
  have hV'' : Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z s =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hh, sec7ctr_Vt_conj_frame hh s, hV]
  have hCN'' : hc''.CN s = hc.CN t := by
    rw [sec7ctr_CN_conj_frame hc hh s, hc.CN_congr hR hV]
  obtain ⟨r, hr⟩ := hA7 G M Q Z B hc n t hs
  obtain ⟨r'', hr''⟩ := hA7 G M Q Z (conjSubgroup h B) hc'' n s hs''
  obtain ⟨d, hd4, hVcard, hLcard⟩ := sec7ctr_card_LB hPtsΩ hc hs hr
  obtain ⟨d'', hd4'', hVcard'', hLcard''⟩ := sec7ctr_card_LB hPtsΩ hc'' hs'' hr''
  rw [hV''] at hVcard''
  rw [hCN''] at hLcard''
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, fK, finK, hK, b, c, hirr, hrep⟩ := hom
  haveI : CharP K 2 := sec7ctr_charP hc hK
  have hrep' := hrep
  obtain ⟨φ, hφr, hφk, -⟩ := hrep
  have hd : d = 4 := by
    have h1 := sec7ctr_pin hrep' hK hZV hq2 hVcard
    simpa using h1.symm
  have hd'' : d'' = 4 := by
    have h1 := sec7ctr_pin hrep' hK hZV hq2 hVcard''
    simpa using h1.symm
  subst hd hd''
  have hNtR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  set ψ : ↥(Rt M (LB M Q B) t) →* ↥φ.range := φ.rangeRestrict with hψdef
  have hψk : ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    rw [hψdef, MonoidHom.ker_rangeRestrict]
    exact hφk
  have hψsurj : Function.Surjective ψ := φ.rangeRestrict_surjective
  set F := Nat.card Z ^ 2 * ((Nat.card Z ^ 2) ^ 2 - 1) with hF
  have hHcard : Nat.card ↥φ.range = F := by
    rw [hφr, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
      CFSG.SeitzReduction.F4Pilot.ordSL_two, hK]
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL''R : LB M Q (conjSubgroup h B) ≤ Rt M (LB M Q B) t := by
    rw [← hR'']
    exact le_Rt (M := M) (LB M Q (conjSubgroup h B)) hsh
  have hP1 : Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map ψ) =
      Nat.card Z ^ 2 := by
    have h1 := card_inf_mul_card_map hLR ψ hψk
    rw [hLcard] at h1
    have := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    simpa using this
  have hP2 : Nat.card ↥(((LB M Q (conjSubgroup h B)).subgroupOf (Rt M (LB M Q B) t)).map ψ) =
      Nat.card Z ^ 2 := by
    have h1 := card_inf_mul_card_map hL''R ψ hψk
    rw [hLcard''] at h1
    have := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    simpa using this
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hq2e : Nat.card Z ^ 2 = 2 ^ (2 * jj) := by
    rw [hZ2, ← pow_mul, mul_comm]
  have hjj : 1 ≤ jj := by
    rcases Nat.eq_zero_or_pos jj with h0 | h0
    · rw [h0, pow_zero] at hZ2
      omega
    · exact h0
  have hEven : Even ((Nat.card Z ^ 2) ^ 2) := by
    rw [hq2e, ← pow_mul]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hodd : Odd ((Nat.card Z ^ 2) ^ 2 - 1) := by
    obtain ⟨y, hy⟩ := hEven
    have h1 : 1 ≤ (Nat.card Z ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    exact ⟨y - 1, by omega⟩
  have hH : Nat.card ↥φ.range = 2 ^ (2 * jj) * ((Nat.card Z ^ 2) ^ 2 - 1) := by
    rw [hHcard, ← hq2e]
  obtain ⟨g, hg⟩ := sec7ctr_exists_conj_of_sylow hodd hH (by rw [hP1, hq2e]) (by rw [hP2, hq2e])
  obtain ⟨ρ', rfl⟩ := hψsurj g
  have hρ : (ρ' : G) ∈ Rt M (LB M Q B) t := ρ'.2
  have hρM : (ρ' : G) ∈ M := hc.Rt_le_M t hρ
  have hdec : ∀ l ∈ LB M Q (conjSubgroup h B), ∃ y ∈ LB M Q B, ∃ ν ∈ hc.CN t,
      l = ((ρ' : G) * y * (ρ' : G)⁻¹) * ν := by
    intro l hl
    have hlR : l ∈ Rt M (LB M Q B) t := hL''R hl
    have hmem : ψ ⟨l, hlR⟩ ∈ ((LB M Q (conjSubgroup h B)).subgroupOf
        (Rt M (LB M Q B) t)).map ψ :=
      Subgroup.mem_map.mpr ⟨⟨l, hlR⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have h1 := (hg (ψ ⟨l, hlR⟩)).mp hmem
    obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.mp h1
    have hk : y'⁻¹ * (ρ'⁻¹ * ⟨l, hlR⟩ * ρ') ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hyeq]
      group
    rw [hψk, Subgroup.mem_subgroupOf] at hk
    have hy'L : (y' : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hy'
    refine ⟨(y' : G), hy'L, (ρ' : G) * ((y' : G)⁻¹ * ((ρ' : G)⁻¹ * l * (ρ' : G))) * (ρ' : G)⁻¹,
      hc.CN_conj_mem ht hρ hk, ?_⟩
    group
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have h35'' := hc.CQt_conj hh h35
  have hVt : ∀ x ∈ conjSubgroup (ρ' : G) B, x ∈ Vt M (LB M Q B) B Z t := fun x hx =>
    (hc.conj_Rt_le_Vt ht hρ) (Subgroup.mem_sup_left hx)
  have hle : conjSubgroup (ρ' : G) B ⊔ Z ≤ conjSubgroup h B ⊔ Z := by
    refine sup_le (fun x hx => ?_) le_sup_right
    have hxV : x ∈ Vt M (LB M Q B) B Z t := hVt x hx
    have hxQ : x ∈ Q := hc.Vt_le_Q t hxV
    have hxC : x ∈ CQt Q Z (LB M Q (conjSubgroup h B)) := by
      refine ⟨hxQ, fun l hl => ?_⟩
      obtain ⟨y, hy, ν, hν, rfl⟩ := hdec l hl
      obtain ⟨b₀, hb₀, rfl⟩ : ∃ b₀ ∈ B, x = (ρ' : G) * b₀ * (ρ' : G)⁻¹ :=
        ⟨(ρ' : G)⁻¹ * x * (ρ' : G), mem_conjSubgroup.mp hx, by group⟩
      have hb₀C : b₀ ∈ CQt Q Z (LB M Q B) := by
        rw [h35]
        exact Subgroup.mem_sup_left hb₀
      have h2 : ⁅y, b₀⁆ ∈ Z := hb₀C.2 y hy
      have hρy : (ρ' : G) * y * (ρ' : G)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hρM (hc.LB_le_M hy)) (M.inv_mem hρM)
      have e : ⁅(ρ' : G) * y * (ρ' : G)⁻¹ * ν, (ρ' : G) * b₀ * (ρ' : G)⁻¹⁆ =
          ((ρ' : G) * y * (ρ' : G)⁻¹) * ⁅ν, (ρ' : G) * b₀ * (ρ' : G)⁻¹⁆ *
            ((ρ' : G) * y * (ρ' : G)⁻¹)⁻¹ *
          ((ρ' : G) * ⁅y, b₀⁆ * (ρ' : G)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine Z.mul_mem ?_ ?_
      · have hν' : ⁅ν, (ρ' : G) * b₀ * (ρ' : G)⁻¹⁆ ∈ Z := (Ctx.mem_CN.mp hν).2 _ (hVt _ hx)
        exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hρy) _).mp hν'
      · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hρM) _).mp h2
    rw [h35''] at hxC
    exact hxC
  have hcardeq : Nat.card ↥(conjSubgroup h B ⊔ Z) ≤ Nat.card ↥(conjSubgroup (ρ' : G) B ⊔ Z) := by
    have e1 : conjSubgroup h B ⊔ Z = conjSubgroup h (B ⊔ Z) := by
      rw [conjSubgroup_sup', hc.conj_Z_eq hh]
    have e2 : conjSubgroup (ρ' : G) B ⊔ Z = conjSubgroup (ρ' : G) (B ⊔ Z) := by
      rw [conjSubgroup_sup', hc.conj_Z_eq hρM]
    rw [e1, e2, card_conjSubgroup, card_conjSubgroup]
  exact ⟨(ρ' : G), hρ, (Subgroup.eq_of_le_of_card_ge hle hcardeq).symm⟩

end CFSG.RankThree.GF2n.Stroth80
