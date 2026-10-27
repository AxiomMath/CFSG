module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Good
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Three
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Aux
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Solv
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Torus
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Chief
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6TwoAux

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z

@[expose] def Six6TwoIndex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V →
      ∀ A : Subgroup G, IsMinOffender T H V A →
      ∀ L N : Subgroup G, ∀ hstep : IsChiefStep H (conjClosure V H) L N, ¬ IsCentralStep H L N →
      ∀ z : G, z ∈ V → z ∈ N → z ∉ L → (∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ L) →
      ∀ hset : Ch3z.Setting H T (H ⊓ M) (conjClosure V H) A,
      ∀ 𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N))),
      @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (hset.hE hstep)) (chiefAut H L N)
          (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
          (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) (H ⊓ M)) 𝓗 →
      ∀ H' ∈ 𝓗,
        @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (hset.hE hstep)) H'
          (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (hset.hE hstep)) H') 2 →
      ∀ y : ↥H, (y : G) ∈ M → (∃ a : ℕ, (y : G) ^ (3 ^ a) = 1) →
        (∀ w ∈ conjClosure V H, (y : G) ^ 3 * w * ((y : G) ^ 3)⁻¹ = w) →
        chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) y ∈ H' →
        chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) y ≠ 1 →
        (Subgroup.centralizer ({(y : G)} : Set G)).relIndex V ≤ 16

theorem lemma319SixGoodTwo_of (hB69 : B69Struct) (hT317 : Theorem317Statement)
    (hres : Six6TwoIndex) : Lemma319SixGoodTwo := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA L N hstep hnc
    z hzV hzN hzL hzT hset 𝓗 hctx H' hH' e he hNat
  subst he
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
  obtain ⟨-, -, -, -, -, hstep2⟩ :=
    lemma319Common_of_inputs hB69 G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl
  set v : ↥(chiefMod L N) := chiefIota hNL ⟨z, hzN⟩ with hvdef
  have hv : v ≠ 1 := fun h1 => hzL ((chiefIota_eq_one_iff hNL ⟨z, hzN⟩).1 h1)
  have hvT : ∀ s ∈ chiefImg hHL hHN T, s v = v := by
    rintro _ ⟨x, hx, rfl⟩
    exact chiefPsi_fix hHL hHN hNL hzN x (hzT _ (Subgroup.mem_subgroupOf.mp hx))
  have hUinv : ∀ g ∈ H', ∀ u ∈ commV H', g u ∈ commV H' := fun _ hg _ hu =>
    apply_mem_commV_of_mem hg hu
  have hQ := hctx.isSylowTwoOf_block hH'
  obtain ⟨d₀, hd₀H, hd₀N, hd₀3, hd₀fix⟩ := exists_torus_of_natBlock_pow (le_refl 2) Nat.prime_three
    (by norm_num) hUinv hNat hQ
  have hBor := BlkCtx.nat_eq_borel hctx hH' (le_refl 2) hNat
  have hd₀M : d₀ ∈ chiefImg hHL hHN (H ⊓ M) := by
    have : d₀ ∈ H' ⊓ Subgroup.normalizer ((chiefImg hHL hHN T ⊓ H' : Subgroup (MulAut ↥(chiefMod L N))) :
        Set (MulAut ↥(chiefMod L N))) := ⟨hd₀H, hd₀N⟩
    rw [← hBor] at this
    exact this.1
  have hodd : Odd (orderOf d₀) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hd₀3)
  have hTP : TorusProp (chiefImg hHL hHN T) H' d₀ :=
    ⟨hd₀H, hodd, fun w hw hqw hdw => hd₀fix w hw hqw hdw⟩
  have hd₀ne : d₀ v ≠ v := fun hfix => hv (BlkCtx.eq_one_of_fixed_conj hctx hH' hTP hvT hfix)
  obtain ⟨x, hxS, hxψ⟩ := hd₀M
  obtain ⟨n, a, hna, hnψ⟩ := exists_pow_threePower_eq (chiefPsi hHL hHN) (isOfFinOrder_of_finite x)
    (by rw [hxψ]; exact hd₀3)
  set g : ↥H := x ^ n with hg
  have hgψ : chiefPsi hHL hHN g = d₀ := by rw [hg, hnψ, hxψ]
  have hgS : (g : G) ∈ H ⊓ M := ((H ⊓ M).subgroupOf H).pow_mem hxS n
  have hgM : (g : G) ∈ M := hgS.2
  have hgH : (g : G) ∈ H := hgS.1
  have hg3pow : (g : G) ^ (3 ^ a) = 1 := by
    have := congrArg (fun w : ↥H => (w : G)) hna
    simpa using this
  have hg3ker : ((g ^ 3 : ↥H) : G) ∈ centralizerMod L H N := by
    refine (chiefHom_eq_one_iff hHL hHN hNL (g ^ 3)).1 ?_
    apply Subtype.ext
    show chiefPsi hHL hHN (g ^ 3) = 1
    rw [map_pow, hgψ, hd₀3]
  have hg3pow' : (((g : G)) ^ 3) ^ (3 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hg3pow, one_pow]
  have hcentU : ∀ w ∈ conjClosure V H, (g : G) ^ 3 * w * ((g : G) ^ 3)⁻¹ = w := by
    have hstepY : ∀ L' N' : Subgroup G, IsChiefStep H (conjClosure V H) L' N' →
        ∀ w ∈ N', (g : G) ^ 3 * w * ((g : G) ^ 3)⁻¹ * w⁻¹ ∈ L' := by
      intro L' N' hst w hw
      have hg3H : (g : G) ^ 3 ∈ H := H.pow_mem hgH 3
      by_cases hnc' : IsCentralStep H L' N'
      · exact hnc' _ hg3H w hw
      · have hmem : (g : G) ^ 3 ∈ centralizerMod L' H N' := by
          rw [hstep2 L' N' hst hnc', ← hstep2 L N hstep hnc]
          simpa using hg3ker
        exact hmem.2.2 w hw
    intro w hw
    have := centralizes_of_odd_series (n := 3 ^ a) (Odd.pow (by decide)) hg3pow' hconcl.elemAbelian
      hstepY hconcl.chief w hw
    exact this
  have hcentV : ∀ w ∈ V, (g : G) ^ 3 * w * ((g : G) ^ 3)⁻¹ = w := fun w hw =>
    hcentU w (le_conjClosure V H hw)
  have hyN : (g : G) ∈ Subgroup.normalizer (V : Set G) := hII hgS
  have hy3C : (g : G) ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have := hcentV w hw
    calc w * (g : G) ^ 3 = ((g : G) ^ 3 * w * ((g : G) ^ 3)⁻¹) * (g : G) ^ 3 := by rw [this]
      _ = (g : G) ^ 3 * w := by group
  have hy1 : (g : G) ∉ Subgroup.centralizer (V : Set G) := by
    intro hcen
    have hcomm := Subgroup.mem_centralizer_iff.mp hcen z hzV
    have hz1 : (g : G) * z * (g : G)⁻¹ * z⁻¹ ∈ L := by
      have e : (g : G) * z * (g : G)⁻¹ * z⁻¹ = 1 := by
        calc (g : G) * z * (g : G)⁻¹ * z⁻¹ = (z * (g : G)) * (g : G)⁻¹ * z⁻¹ := by rw [hcomm]
          _ = 1 := by group
      rw [e]
      exact L.one_mem
    apply hd₀ne
    rw [← hgψ]
    exact chiefPsi_fix hHL hHN hNL hzN g hz1
  have hXM : Subgroup.zpowers (g : G) ≤ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.zpowers_le]
    refine ⟨hgM, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hZ hw).2) (g : G) hgH).symm
  have hXN : Subgroup.zpowers (g : G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hyN
  have hAut : Nat.card (autOn (Subgroup.zpowers (g : G)) V) = 3 :=
    card_autOn_zpowers_three hyN hy3C hy1
  have hVe : IsElemAbelian 2 V := by
    have hU := hconcl.elemAbelian
    have hVU := le_conjClosure V H
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun w hw => hU.2 w (hVU hw)⟩
    have hc := congrArg Subtype.val (hU.1.is_comm.comm ⟨a, hVU a.2⟩ ⟨b, hVU b.2⟩)
    exact Subtype.ext hc
  have hyV : ∀ w ∈ V, (g : G) * w * (g : G)⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
  obtain ⟨k, hser, hk⟩ := exists_chiefSeries_index_ge hVe hyV hcentV
  have h3k : 3 ≤ k := h6iii _ hXM hXN hAut k hser
  have hidx := hres G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
    L N hstep hnc z hzV hzN hzL hzT hset 𝓗 hctx H' hH' hNat g hgM ⟨a, hg3pow⟩ hcentU
    (by rw [hgψ]; exact hd₀H) (by rw [hgψ]; intro h1; exact hd₀ne (by rw [h1]; rfl))
  have : 4 ^ 3 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) h3k
  omega

end CFSG.Quasithin.H13.L319
