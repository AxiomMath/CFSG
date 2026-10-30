module

public import CFSG.Milestones.ASVolI.F45.Six
public import CFSG.Milestones.ASVolI.F4Sylow
public import CFSG.Milestones.ASVolI.F45.G2dHex
public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Flag

variable {W : Type} {Γ : SimpleGraph W} {G : Type} [Group G] [MulAction G W] [GraphAction G Γ]

theorem burnsideF45_g2d_le_oPPrime {B : Subgroup G} (hB : IsPGroup 2 ↥B) : B ≤ oPPrime 2 B := by
  intro g hg
  obtain ⟨k, hk⟩ := hB ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  exact Subgroup.subset_closure ⟨hg, j, hj⟩

theorem burnsideF45_g2d_oPPrime_le (B : Subgroup G) : oPPrime 2 B ≤ B :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem burnsideF45_g2d_flag_six {u w : W} (huw : Γ.Adj u w) (h3 : (Γ.neighborSet u).ncard = 3)
    (htr : ∀ a, Γ.Adj u a → ∃ g : G, g • u = u ∧ g • w = a)
    (hB : IsPGroup 2 ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w))
    (hN : ∀ g : G, g • u = u → g ∈ Subgroup.normalizer
      ((MulAction.stabilizer G u ⊓ MulAction.stabilizer G w : Subgroup G) : Set G) → g • w = w) :
    (∀ w₁ ∈ Γ.neighborSet u \ {w}, ∀ w₂ ∈ Γ.neighborSet u \ {w},
      ∃ g ∈ oPPrime 2 (MulAction.stabilizer G u ⊓ MulAction.stabilizer G w), g • w₁ = w₂) ∧
    (∀ g ∈ oPPrime 2 (MulAction.stabilizer G u ⊓ MulAction.stabilizer G w),
      ∀ w' ∈ Γ.neighborSet u \ {w}, g • w' = w' → g ∈ pCoreOf 2 (MulAction.stabilizer G u)) := by
  set B := MulAction.stabilizer G u ⊓ MulAction.stabilizer G w with hBdef
  have hker := burnsideF45_g2dKer_le_pCoreOf huw hB
  have hmap : ∀ g ∈ B, ∀ z, Γ.Adj u z → Γ.Adj u (g • z) := fun g hg z hz => by
    have := (GraphAction.adj_smul g u z).mpr hz
    rwa [MulAction.mem_stabilizer_iff.mp hg.1] at this
  have hfix3 : ∀ g ∈ B, ∀ w', Γ.Adj u w' → w' ≠ w → g • w' = w' →
      g ∈ burnsideF45_g2dKer Γ G u := by
    intro g hg w' hw' hne hgw'
    obtain ⟨w'', hw'', h1, h2⟩ := CFSG.Quasithin.D4Hex.exists_third (N := Γ.neighborSet u)
      (by rw [h3]) w w'
    have hw''N : Γ.Adj u w'' := hw''
    have hgw : g • w = w := MulAction.mem_stabilizer_iff.mp hg.2
    have hgw'' : g • w'' = w'' := by
      rcases burnsideF45_mem_three h3 huw hw' hw''N (Ne.symm hne) (Ne.symm h1) (Ne.symm h2)
        (hmap g hg w'' hw''N) with e | e | e
      · exact absurd (MulAction.injective g (e.trans hgw.symm)) h1
      · exact absurd (MulAction.injective g (e.trans hgw'.symm)) h2
      · exact e
    refine ⟨MulAction.mem_stabilizer_iff.mp hg.1, fun z hz => ?_⟩
    rcases burnsideF45_mem_three h3 huw hw' hw''N (Ne.symm hne) (Ne.symm h1) (Ne.symm h2) hz with
      rfl | rfl | rfl
    · exact hgw
    · exact hgw'
    · exact hgw''
  refine ⟨fun w₁ hw₁ w₂ hw₂ => ?_, fun g hg w' hw' hgw' =>
    hker (hfix3 g (burnsideF45_g2d_oPPrime_le B hg) w' hw'.1 hw'.2 hgw')⟩
  by_cases h12 : w₁ = w₂
  · exact ⟨1, Subgroup.one_mem _, by rw [one_smul, h12]⟩
  have hw₁N : Γ.Adj u w₁ := hw₁.1
  have hw₂N : Γ.Adj u w₂ := hw₂.1
  have hw₁w : w₁ ≠ w := hw₁.2
  have hw₂w : w₂ ≠ w := hw₂.2
  have hex : ∃ g ∈ B, g • w₁ = w₂ := by
    by_contra hcon
    push Not at hcon
    have hBK : B ≤ burnsideF45_g2dKer Γ G u := by
      intro g hg
      have hgw : g • w = w := MulAction.mem_stabilizer_iff.mp hg.2
      have hg1 : g • w₁ = w₁ := by
        rcases burnsideF45_mem_three h3 huw hw₁N hw₂N (Ne.symm hw₁w) (Ne.symm hw₂w) h12
          (hmap g hg w₁ hw₁N) with e | e | e
        · exact absurd (MulAction.injective g (e.trans hgw.symm)) hw₁w
        · exact e
        · exact absurd e (hcon g hg)
      exact hfix3 g hg w₁ hw₁N hw₁w hg1
    have hKB : burnsideF45_g2dKer Γ G u ≤ B := fun g hg =>
      ⟨MulAction.mem_stabilizer_iff.mpr hg.1, MulAction.mem_stabilizer_iff.mpr (hg.2 w huw)⟩
    have hBeq : B = burnsideF45_g2dKer Γ G u := le_antisymm hBK hKB
    obtain ⟨g, hgu, hgw⟩ := htr w₁ hw₁N
    have hgN : g ∈ Subgroup.normalizer (B : Set G) := by
      rw [hBeq]
      exact burnsideF45_g2dKer_normalizer u (MulAction.mem_stabilizer_iff.mpr hgu)
    exact hw₁w (hgw.symm.trans (hN g hgu hgN))
  obtain ⟨g, hgB, hg⟩ := hex
  exact ⟨g, burnsideF45_g2d_le_oPPrime hB hgB, hg⟩

end Flag

section Data


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF45_g2d_chart (hyp : HypF_4_4g .G2d 2 1 (⊤ : Subgroup E) M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ π : E ≃* G2Native.SmallModel K,
        (∀ e, e ∈ M₁ ↔ π e ∈ G2Native.smallLocal K (G2Native.pointParabolic K)) ∧
        (∀ e, e ∈ M₂ ↔ π e ∈ G2Native.smallLocal K (G2Native.lineParabolic K)) := by
  obtain ⟨K, fK, finK, hK, marking, h1, h2⟩ := burnsideF4gG2Two_chart_G2d hyp
  letI := fK
  refine ⟨K, fK, finK, hK, Subgroup.topEquiv.symm.trans marking.symm, fun e => ?_, fun e => ?_⟩
  · have e1 : e ∈ M₁ ↔ (⟨e, Subgroup.mem_top e⟩ : ↥(⊤ : Subgroup E)) ∈ M₁.subgroupOf ⊤ := Iff.rfl
    rw [e1, h1]
    unfold G2Native.smallImage
    rw [Subgroup.mem_map_equiv]
    rfl
  · have e1 : e ∈ M₂ ↔ (⟨e, Subgroup.mem_top e⟩ : ↥(⊤ : Subgroup E)) ∈ M₂.subgroupOf ⊤ := Iff.rfl
    rw [e1, h2]
    unfold G2Native.smallImage
    rw [Subgroup.mem_map_equiv]
    rfl

variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2d_isLie (hK : Nat.card K = 2) (π : E ≃* G2Native.SmallModel K)
    (h1 : ∀ e, e ∈ M₁ ↔ π e ∈ G2Native.smallLocal K (G2Native.pointParabolic K))
    (h2 : ∀ e, e ∈ M₂ ↔ π e ∈ G2Native.smallLocal K (G2Native.lineParabolic K)) :
    IsLieParabolics 2 ⊤ (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂) := by
  have hs := (burnsideF4h_g2_small K hK).1
  have hm := burnsideF4h_cl_isLieParabolics_map π.symm hs
  have e1 : (G2Native.smallLocal K (G2Native.pointParabolic K)).map π.symm.toMonoidHom = M₁ := by
    ext e
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, h1]
  have e2 : (G2Native.smallLocal K (G2Native.lineParabolic K)).map π.symm.toMonoidHom = M₂ := by
    ext e
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, h2]
  have e0 : (G2Native.smallLocal K (G2Native.positiveBorel K)).map π.symm.toMonoidHom =
      M₁ ⊓ M₂ := by
    rw [← hs.2.2.1, Subgroup.map_inf_eq _ _ _ π.symm.injective, e1, e2]
  rw [e0, e1, e2] at hm
  simpa only [top_inf_eq] using hm

theorem burnsideF45_g2d_borel_pGroup (hK : Nat.card K = 2) (π : E ≃* G2Native.SmallModel K)
    (h1 : ∀ e, e ∈ M₁ ↔ π e ∈ G2Native.smallLocal K (G2Native.pointParabolic K))
    (h2 : ∀ e, e ∈ M₂ ↔ π e ∈ G2Native.smallLocal K (G2Native.lineParabolic K)) :
    IsPGroup 2 ↥(M₁ ⊓ M₂) := by
  have hsl := (burnsideF4h_g2_small K hK).1.2.2.1
  have e : M₁ ⊓ M₂ =
      (G2Native.smallLocal K (G2Native.positiveBorel K)).comap π.toMonoidHom := by
    ext e
    rw [Subgroup.mem_comap, ← hsl]
    exact and_congr (h1 e) (h2 e)
  rw [e]
  exact (burnsideF4h_g2_small_sylow hK).1.comap_of_injective _ π.injective

end Data

section Normalizer

variable {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E}

theorem burnsideF45_g2d_normalizer_borel (hP : IsLieParabolics 2 ⊤ (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂))
    (hB : IsPGroup 2 ↥(M₁ ⊓ M₂)) :
    Subgroup.normalizer ((M₁ ⊓ M₂ : Subgroup E) : Set E) = M₁ ⊓ M₂ := by
  obtain ⟨⟨S, ⟨-, hSp, hSi⟩, hBS⟩, -⟩ := hP
  rw [top_inf_eq, top_inf_eq] at hBS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSi' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSi
  let T : Sylow 2 E := hSp.toSylow hSi'
  have hT : (T : Subgroup E) = S := rfl
  have hSB : S ≤ M₁ ⊓ M₂ := by
    rw [hBS]
    exact Subgroup.le_normalizer
  have heq : M₁ ⊓ M₂ = S := by
    have := T.is_maximal' hB (by rw [hT]; exact hSB)
    rwa [hT] at this
  rw [heq]
  rw [heq] at hBS
  exact hBS.symm

end Normalizer

section Six


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF45_g2d_Qu (hyp : HypF_4_4 .G2d 2 1 (⊤ : Subgroup E) M₁ M₂) (u : (incl M₁ M₂).Γ) :
    Qu 2 ⊤ (incl M₁ M₂) u = pCoreOf 2 (stv (incl M₁ M₂) u) := by
  rw [burnsideF45_Qu_eq_Qbar hyp Nat.prime_two (burnsideF45_three_le_m _) u]
  show pCoreOf 2 ((⊤ : Subgroup E).comap (toE (incl M₁ M₂)) ⊓ stv (incl M₁ M₂) u) = _
  rw [Subgroup.comap_top, top_inf_eq]

theorem burnsideF45_g2d_three (hyp : HypF_4_4 .G2d 2 1 (⊤ : Subgroup E) M₁ M₂)
    (u : (incl M₁ M₂).Γ) : ((incl M₁ M₂).graph.neighborSet u).ncard = 3 := by
  haveI := hyp.finite
  obtain ⟨hq1, hq2⟩ := burnsideF45_q_G2d hyp rfl
  have h := card_nbrs (c := incl M₁ M₂) (incl_faithful M₁ M₂) u
  rw [← Nat.card_coe_set_eq]
  show Nat.card ↥(CosetGeom.nbrs u) = 3
  rw [h]
  cases CosetGeom.vtype u <;> simp [RankTwoAmalgam.qv, hq1, hq2]

theorem burnsideF45_g2d_mem_flag (g : (incl M₁ M₂).G0) :
    g ∈ stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv ↔
      toE (incl M₁ M₂) g ∈ M₁ ⊓ M₂ :=
  and_congr (burnsideF45_mem_stv_xv_iff g) (burnsideF45_mem_stv_lv_iff' g)

theorem burnsideF45_g2d_C6 (hyp : HypF_4_4 .G2d 2 1 (⊤ : Subgroup E) M₁ M₂)
    (hP : IsLieParabolics 2 ⊤ (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) (hB : IsPGroup 2 ↥(M₁ ⊓ M₂)) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body 2 ⊤ M₁ M₂ u v := by
  haveI := hyp.finite
  have hm : 3 ≤ GLKind.G2d.m := burnsideF45_three_le_m _
  have hbij := burnsideF45_toE_bijective hyp.gen
  have hNE := burnsideF45_g2d_normalizer_borel hP hB
  have hBι : IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv) := by
    have e : stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv =
        (M₁ ⊓ M₂).comap (toE (incl M₁ M₂)) := by
      ext g
      exact burnsideF45_g2d_mem_flag g
    rw [e]
    exact hB.comap_of_injective _ hbij.1
  have hNι : ∀ g : (incl M₁ M₂).G0, g ∈ Subgroup.normalizer
      ((stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv :
        Subgroup (incl M₁ M₂).G0) : Set (incl M₁ M₂).G0) →
      g ∈ stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv := by
    intro g hg
    rw [burnsideF45_g2d_mem_flag, ← hNE, Subgroup.mem_normalizer_iff]
    intro e
    obtain ⟨g', rfl⟩ := hbij.2 e
    have := (Subgroup.mem_normalizer_iff.1 hg) g'
    rw [burnsideF45_g2d_mem_flag, burnsideF45_g2d_mem_flag, map_mul, map_mul, map_inv] at this
    exact this
  have hx : burnsideF45_C6cd 2 ⊤ M₁ M₂ (incl M₁ M₂).xv (incl M₁ M₂).lv := by
    obtain ⟨hc, hd⟩ := burnsideF45_g2d_flag_six (G := (incl M₁ M₂).G0) CosetGeom.adj_γ₀_γ₁
      (burnsideF45_g2d_three hyp _) (fun a ha => CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁ ha)
      hBι (fun g _ hg => MulAction.mem_stabilizer_iff.mp (hNι g hg).2)
    refine ⟨hc, fun g hg w hw hgw => ?_⟩
    rw [burnsideF45_g2d_Qu hyp]
    exact hd g hg w hw hgw
  have hl : burnsideF45_C6cd 2 ⊤ M₁ M₂ (incl M₁ M₂).lv (incl M₁ M₂).xv := by
    have hBι' : IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).xv) := by
      rw [inf_comm]
      exact hBι
    obtain ⟨hc, hd⟩ := burnsideF45_g2d_flag_six (G := (incl M₁ M₂).G0) CosetGeom.adj_γ₀_γ₁.symm
      (burnsideF45_g2d_three hyp _)
      (fun a ha => CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁.symm ha) hBι'
      (fun g _ hg => by
        rw [inf_comm] at hg
        exact MulAction.mem_stabilizer_iff.mp (hNι g hg).1)
    refine ⟨hc, fun g hg w hw hgw => ?_⟩
    rw [burnsideF45_g2d_Qu hyp]
    exact hd g hg w hw hgw
  exact fun u v huv => burnsideF45_C6_of_base hyp Nat.prime_two hm hP hx hl huv

end Six

end CFSG.ASVolI
