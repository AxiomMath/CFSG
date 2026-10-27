module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Good
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Aux
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Solv
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Torus

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z

theorem lemma319SixGoodBig_of (hT317 : Theorem317Statement) : Lemma319SixGoodBig := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA L N hstep hnc
    z hzV hzN hzL hzT hset 𝓗 hctx H' hH' e he hNat
  have he3 : 3 ≤ e := he
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := hset.hE hstep
  have hNL := hset.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hZ : quasithinOmegaOneCenter T ≤ centerOf H := by
    rcases hT317 G T hs hnab hK hT M M₀ H V hM ⟨h.toHyp315Base, Or.inr h.caseII⟩
        (hD.thompsonJ_le hnff) with ⟨hZ, -⟩ | hex
    · exact hZ
    · exact absurd hex h.not_exists_normal
  have hmp : MinParabolic H T (H ⊓ M) := hset.mp
  have hTH : T ≤ H := hmp.isSylow.1
  have hTM : T ≤ M := h.T_le.trans h.le_M
  have hTS : T ≤ H ⊓ M := le_inf hTH hTM
  set v : ↥(chiefMod L N) := chiefIota hNL ⟨z, hzN⟩ with hvdef
  have hv : v ≠ 1 := fun h1 => hzL ((chiefIota_eq_one_iff hNL ⟨z, hzN⟩).1 h1)
  have hvT : ∀ s ∈ chiefImg hHL hHN T, s v = v := by
    rintro _ ⟨x, hx, rfl⟩
    exact chiefPsi_fix hHL hHN hNL hzN x (hzT _ (Subgroup.mem_subgroupOf.mp hx))
  have hUinv : ∀ g ∈ H', ∀ u ∈ commV H', g u ∈ commV H' := fun _ hg _ hu =>
    apply_mem_commV_of_mem hg hu
  have hQ := hctx.isSylowTwoOf_block hH'
  obtain ⟨d₀, hd₀H, hd₀N, hd₀cop, hd₀fix⟩ := exists_torus_of_natBlock_cop6 he3 hUinv hNat hQ
  have hBor := BlkCtx.nat_eq_borel hctx hH' (by omega) hNat
  have hd₀M : d₀ ∈ chiefImg hHL hHN (H ⊓ M) := by
    have : d₀ ∈ H' ⊓ Subgroup.normalizer ((chiefImg hHL hHN T ⊓ H' : Subgroup (MulAut ↥(chiefMod L N))) :
        Set (MulAut ↥(chiefMod L N))) := ⟨hd₀H, hd₀N⟩
    rw [← hBor] at this
    exact this.1
  have hsolvM : Group.IsSolvable ↥(chiefImg hHL hHN (H ⊓ M)) :=
    BlkCtx.isSolvable_of_nat hctx hH' (by omega) hNat
  have hsolvS : Group.IsSolvable ↥(H ⊓ M) := isSolvable_of_chief_G6 hmp hset.UT hstep hnc hsolvM
  have hTS' : IsSylowTwoOf T (H ⊓ M) := B6.isSylowTwoOf_mono hmp.isSylow hTS inf_le_left
  have hcen := hall_centralizes hTS' hsolvS hII (fun F hFS hFcop hFperm => by
    have hFZ : F ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun z' hz' =>
        ((Subgroup.mem_centralizer_iff.mp (hZ hz').2) x (hFS hx).1).symm
    exact h6i F (fun x hx => ⟨(hFS hx).2, hFZ hx⟩) hFcop hFperm)
  obtain ⟨x, hxS, hxψ⟩ := hd₀M
  obtain ⟨n, hncop, hnψ⟩ := exists_cop6_pow_eq (chiefPsi hHL hHN) (isOfFinOrder_of_finite x)
    (by rw [hxψ]; exact hd₀cop)
  have hgS : ((x ^ n : ↥H) : G) ∈ H ⊓ M := ((H ⊓ M).subgroupOf H).pow_mem hxS n
  have hgcop : Nat.Coprime (orderOf ((x ^ n : ↥H) : G)) 6 := by
    rw [Subgroup.orderOf_coe]
    exact hncop
  have hgz : ((x ^ n : ↥H) : G) * z * ((x ^ n : ↥H) : G)⁻¹ * z⁻¹ ∈ L := by
    have := hcen _ hgS hgcop z hzV
    rw [this, mul_inv_cancel]
    exact L.one_mem
  have hfix : chiefPsi hHL hHN (x ^ n) v = v := chiefPsi_fix hHL hHN hNL hzN (x ^ n) hgz
  have hd₀v : d₀ v = v := by
    rw [← hxψ, ← hnψ]
    exact hfix
  have hodd : Odd (orderOf d₀) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hd₀cop)
  have hTP : TorusProp (chiefImg hHL hHN T) H' d₀ := ⟨hd₀H, hodd, fun w hw hqw hdw => hd₀fix w hw hqw hdw⟩
  exact hv (BlkCtx.eq_one_of_fixed_conj hctx hH' hTP hvT hd₀v)

end CFSG.Quasithin.H13.L319
