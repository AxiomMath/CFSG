module

public import CFSG.Quasithin.EmptyFaithful.S153XFin
public import CFSG.Quasithin.EmptyFaithful.S153XPhi
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.S1469Sev

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.X1469 CFSG.Quasithin.ModF
open scoped commutatorElement

theorem input1469A5Fin_of_loc
    (hLoc : ∀ (G : Type) [Group G] [Finite G] (I S Iz K₁ K₂ T : Subgroup G) (r z : G),
      LocalCfg I S Iz K₁ K₂ T r z → LocalFacts I S Iz r z) : Input1469A5Fin := by
  intro G _ _ T M H u I K₁ K₂ ρ c hf hD
  have S : Setting146 G T M := c.ctx.setting
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcen : mcOf T = Subgroup.centralizer ({z} : Set G) := S.mcOf_eq_centralizer hzZ hz1'
  have hzT : z ∈ T := S146T.Z_le hzZ
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.ctx.hH c.ctx.hu.mem
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
  have hzI : z ∈ I := c.ctx.hI.1.1.1.1 hzu
  have hzc : ∀ y ∈ T, y * z = z * y := fun y hy => S146T.comm_Z_T hy hzZ
  have hrel : (T ⊓ I).relIndex T = 2 := by
    rw [hf.d]
    exact c.ctx.hu.index_two
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) :=
    normalizer_of_relIndex_two inf_le_left hrel
  have hnormal : ∀ R₀ : Subgroup G, R₀ ≤ T ⊓ I → R₀ ≠ ⊥ →
      ¬ (T ⊔ I ≤ Subgroup.normalizer (R₀ : Set G)) := by
    intro R₀ hR₀ hR₀1 hle
    obtain ⟨_, hTN', _⟩ := c.obs_a R₀ hR₀ hR₀1 (le_sup_right.trans hle)
    have hTI : T ⊓ I = T := by
      rw [← hTN']
      exact inf_eq_left.mpr (le_sup_left.trans hle)
    exact (S.tI_lt c.ctx.hI.1.1).ne hTI
  have ht : ∃ t ∈ T ⊓ I, B6.conjSub t K₁ = K₂ := by
    obtain ⟨-, -, -, -, -, htrans, -⟩ := c.blocks
    simpa using htrans 0 1
  have hmin : MinParabolic I (T ⊓ I) (I ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hcen]
    exact c.ctx.minPar
  have hcfg : A5Cfg I (T ⊓ I) (I ⊓ Subgroup.centralizer ({z} : Set G)) K₁ K₂ :=
    A5Cfg.of_blockProduct hmin c.blocks c.a5.1 c.a5.2
  have hnot : ¬ K₁ ≤ I ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [← hcen]
    exact c.not_le
  have C : LocalCfg I (T ⊓ I) (I ⊓ Subgroup.centralizer ({z} : Set G)) K₁ K₂ T ρ z :=
    ⟨hcfg, c.charTwo, hD, hnot, ht, inf_le_left, hTN, hrel, c.rho.1, c.rho.2.2.1, hnormal,
      ⟨hzT, hzI⟩, hz1', S146T.Z_sq hzZ, hzc, rfl⟩
  have L := hLoc G I (T ⊓ I) (I ⊓ Subgroup.centralizer ({z} : Set G)) K₁ K₂ T ρ z C
  have hchar : CharTwo (Subgroup.centralizer ({z} : Set G)) := by
    rw [← hcen]
    exact charTwo_of_inH' S.hyp.qtke S.hyp.sylow S.isHTM_mcOf.1
  have hY : oTwoUpper (oTwoFstarIn (Subgroup.centralizer ({z} : Set G))) ≤
      Subgroup.centralizer
        (omegaOneCenterOf (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) : Set G) := by
    rw [← hcen]
    intro x hx
    refine Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_) (hf.f hx)
    exact le_sup_left
  have hPhi := centralizerMod_le_pCoreOf_omegaOneCenter hchar hY
  have hc : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤
      pCoreOf 2 (I ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hcen]
    exact hf.c
  have he : omegaOneCenterOf (pCoreOf 2 (I ⊓ Subgroup.centralizer ({z} : Set G))) ≤
      omegaOneCenterOf (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := by
    rw [← hcen]
    exact hf.e
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hVN : ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (VZ T M : Set G) := by
    rw [← hcen, S.hyp1281.normalizer_VZ]
    exact S.isHTM_mcOf.2
  have hV15 : VZ T M ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      ∀ v ∈ VZ T M, ∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)),
        v * q * v⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
    have hZeq : ∀ x ∈ quasithinOmegaOneCenter T, x ∈ Subgroup.zpowers z := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · have := S.Z_eq_of_iff hx hzZ ⟨fun h => absurd h hx1, fun h => absurd h hz1'⟩
        rw [this]; exact Subgroup.mem_zpowers z
    have hU2 := S.lemma_14_5_15_two S.isHTM_mcOf
    have hU4 := S.lemma_14_5_15_four S.isHTM_mcOf
    have hVU : VZ T M ≤ conjClosure (VZ T M) (mcOf T) := le_conjClosure _ _
    have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
    have hcomm : ∀ a ∈ conjClosure (VZ T M) (mcOf T), ∀ b ∈ conjClosure (VZ T M) (mcOf T),
        a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hU2 ha hb
    rw [← hcen]
    refine ⟨fun v hv => ?_, fun v hv q hq => ?_⟩
    · rw [← hU4]
      have hvG : v ∈ mcOf T := by
        rw [hcen]
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        rw [Set.mem_singleton_iff.mp hy]
        exact hcomm z (hVU (hZV hzZ)) v (hVU hv)
      refine ⟨hvG, ?_, fun u hu => ?_⟩
      · rw [S.normalizer_Z]
        exact hvG
      · have h1 : v * u * v⁻¹ * u⁻¹ = 1 := by
          rw [hcomm v (hVU hv) u hu]; group
        rw [h1]; exact Subgroup.one_mem _
    · rw [← hU4] at hq
      have h1 : q * v * q⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := hq.2.2 v (hVU hv)
      have e : v * q * v⁻¹ * q⁻¹ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact (Subgroup.zpowers z).inv_mem (hZeq _ h1)
  exact fin_core C L hPhi hc he (VZ T M) hV4 hV15 hVN

end CFSG.Quasithin
