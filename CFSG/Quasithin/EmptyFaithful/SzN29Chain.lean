module

public import CFSG.Quasithin.EmptyFaithful.S143WFin
public import CFSG.Quasithin.EmptyFaithful.SzN29G94
public import CFSG.Quasithin.EmptyFaithful.S142Bridge
public import CFSG.Quasithin.EmptyFaithful.S143VFin
public import CFSG.Quasithin.EmptyFaithful.S143VQG
public import CFSG.Quasithin.EmptyFaithful.S143VTwo
public import CFSG.Quasithin.EmptyFaithful.S143VZU
public import CFSG.Quasithin.EmptyFaithful.S143WAL
public import CFSG.Quasithin.EmptyFaithful.S143WE
public import CFSG.Quasithin.EmptyFaithful.S143WNo
public import CFSG.Quasithin.EmptyFaithful.S143WT
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
open scoped commutatorElement

namespace S143V

section MainSolv

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}
variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
  (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU hg haV haZ

theorem dim_cases_of_ker_solv
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hker : Hyp1281Two.centralizerHat T M ≤ T) (hsolv : Group.IsSolvable ↥(D.img (mcOf T)))
    (h94 : SzN29.G94StmtSolv) :
    (Module.finrank (ZMod 2) D.V = 2 ∧ Nat.card (D.img (mcOf T)) = 6) ∨
      (Module.finrank (ZMod 2) D.V = 4 ∧ 18 ∣ Nat.card (D.img (mcOf T))) :=
  SzN29.dim_cases_of_hyp_solv (h.lemma_12_8_12_three hU hg D haV haZ) (h.isQuotientOfSQTK_img D)
    hsolv h94 fun _ hNΓ hNn =>
      ⟨fun h3 => no_normal_three_five h hU hg D haV haZ h35 hker hNΓ hNn (Or.inl h3),
        fun h5 => no_normal_three_five h hU hg D haV haZ h35 hker hNΓ hNn (Or.inr h5)⟩

end MainSolv

theorem concl14315_of_zu_solv {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (D : HatModel T M) (hsolv : Group.IsSolvable ↥(D.img (mcOf T))) (h94 : SzN29.G94StmtSolv) :
    S143.Concl14315 T M := by
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  have hker := centralizerHat_le_T h hZU
  rcases dim_cases_of_ker_solv h hU hg D haV haZ h35 hker hsolv h94 with ⟨-, hc6⟩ | ⟨hd4, h18⟩
  · exact (card_img_ne_six h D h35 hker hc6).elim
  · obtain ⟨hplus, hcard⟩ := plus_and_card_of_zu h hU hg D hZU haV haZ h35 hker hd4 h18
    exact concl14315_of_data h hU hZU D hd4 hplus hcard (isQ8Sq_of_plus h hZU D hd4 hplus)

end S143V

namespace S143W

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section MainSolv

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g) (D : HatModel T M)

include h hU hg in
theorem false_of_lt_solv
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hsolv : Group.IsSolvable ↥(D.img (mcOf T))) (h94 : SzN29.G94StmtSolv)
    (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M)) : False := by
  classical
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  obtain ⟨Tm⟩ := exists_tildeModel h
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := S143V.exists_zgen_sq h
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have h101 := hyp.toG101Hyp
  have hO2 : pCoreOf 2 (D.img (mcOf T)) = ⊥ := h101.g10_3_pCoreOf_eq_bot
  have hB : IsSymplectic D.B := ⟨D.B_isAlt, D.B_nondegenerate⟩
  have hΓsp : D.img (mcOf T) ≤ spSub D.B := fun γ hγ x y => h101.isometry γ hγ x y
  have hPH := pOf_le_H h hU hg
  have hPn : ∀ x ∈ mcOf T, ∀ p ∈ pOf T M g, x * p * x⁻¹ ∈ pOf T M g :=
    fun x hx p hp => pOf_normalized x hx hp
  have hPZ : ∀ p ∈ pOf T M g, ∀ z ∈ centerOf (uOfL22 T M), p * z = z * p :=
    fun p hp z hz => pOf_centralizes h hU hg hp hz
  have hPT := inf_centralizerHat_le_T h hPH hPn hPZ
  have hPQ := inf_centralizerHat_le_pCore h hPH hPn hPZ
  set Γ : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := D.img (mcOf T) with hΓ
  set Pd : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := D.img (pOf T M g) with hPd
  have hPdΓ : Pd ≤ Γ := HatModel.img_mono hPH
  have hPdn : ∀ γ ∈ Γ, ∀ n ∈ Pd, γ * n * γ⁻¹ ∈ Pd := by
    intro γ hγ n hn
    obtain ⟨x, hxH, hxN, rfl⟩ := HatModel.mem_img.mp hγ
    obtain ⟨p, hpP, hpN, rfl⟩ := HatModel.mem_img.mp hn
    have hN : x * p * x⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
      (Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem
        ((Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem hxN hpN)
        ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hxN)
    refine HatModel.mem_img.mpr ⟨x * p * x⁻¹, pOf_normalized x hxH hpP, hN, ?_⟩
    have e : (⟨x * p * x⁻¹, hN⟩ : ↥(Subgroup.normalizer (uOfL22 T M : Set G))) =
        ⟨x, hxN⟩ * ⟨p, hpN⟩ * ⟨x, hxN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hno' : ∀ N : Subgroup (D.V ≃ₗ[ZMod 2] D.V), N ≤ Pd →
      (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 3 ∧ Nat.card N ≠ 5 := by
    intro N hNP hNn
    exact ⟨fun h3 => no_normal_three_five_of_P h hU hg D haV haZ h35 hPH hPn hPT hNP hNn (Or.inl h3),
      fun h5 => no_normal_three_five_of_P h hU hg D haV haZ h35 hPH hPn hPT hNP hNn (Or.inr h5)⟩
  obtain ⟨y₀, hy₀X, hy₀H, hy₀1⟩ := exists_y₀ h hU hg D hlt
  have hy₀P : y₀ ∈ pOf T M g := le_conjClosure _ _ hy₀X
  have hy₀N : y₀ ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hy₀H
  have hX₀ : D.img (rconj (centerOf (uOfL22 T M)) g) ≠ ⊥ := by
    intro hbot
    have hmem : S143V.rhoH h D ⟨y₀, hy₀H⟩ ∈ D.img (rconj (centerOf (uOfL22 T M)) g) :=
      HatModel.mem_img.mpr ⟨y₀, hy₀X, hy₀N, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 hmem
  have hPd1 : Pd ≠ ⊥ := by
    intro hbot
    have hmem : S143V.rhoH h D ⟨y₀, hy₀H⟩ ∈ Pd := HatModel.mem_img.mpr ⟨y₀, hy₀P, hy₀N, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 hmem
  have hcases := SzN29.dim_cases_of_rank_solv hyp (h.isQuotientOfSQTK_img D) hsolv h94 hX₀
  have hdvd : Nat.card ↥Γ ∣ 720 := by
    rcases hcases with ⟨-, hc6⟩ | ⟨hd4, -⟩
    · rw [hc6]
      norm_num
    · exact (Subgroup.card_dvd_of_le hΓsp).trans
        (by rw [P4InspSp.p4inspsp_card_spSub_four hB hd4])
  have : Group.IsSolvable ↥Γ := hsolv
  have hΓ2 : ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hp
    have hp' : IsPGroup 2 ↥(N.map Γ.subtype) :=
      hp.of_equiv (N.equivMapOfInjective Γ.subtype Γ.subtype_injective)
    have h1 : N.map Γ.subtype ≤ pCoreOf 2 Γ :=
      le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le N)
        (le_normalizer_of_conj_mem fun γ hγ k hk => by
          obtain ⟨m, hm, rfl⟩ := hk
          exact ⟨⟨γ, hγ⟩ * m * ⟨γ, hγ⟩⁻¹, hN.conj_mem m hm ⟨γ, hγ⟩, by simp⟩) hp'
    rw [hO2, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h1
  have hPd1' : Pd.subgroupOf Γ ≠ ⊥ := by
    intro hbot
    apply hPd1
    have := Subgroup.map_subgroupOf_eq_of_le hPdΓ
    rw [hbot, Subgroup.map_bot] at this
    exact this.symm
  have hPdn' : (Pd.subgroupOf Γ).Normal := ⟨fun n hn γ => by
    have := hPdn (γ : D.V ≃ₗ[ZMod 2] D.V) γ.2 (n : D.V ≃ₗ[ZMod 2] D.V) hn
    exact this⟩
  have hnoΓ : ∀ N : Subgroup ↥Γ, N.Normal → N ≤ Pd.subgroupOf Γ →
      Nat.card N ≠ 3 ∧ Nat.card N ≠ 5 := by
    intro N hN hNP
    have hcard : Nat.card ↥(N.map Γ.subtype) = Nat.card N :=
      Subgroup.card_map_of_injective Γ.subtype_injective
    have := hno' (N.map Γ.subtype)
      (by
        rintro _ ⟨n, hn, rfl⟩
        exact hNP hn)
      (by
        rintro γ hγ _ ⟨m, hm, rfl⟩
        exact ⟨⟨γ, hγ⟩ * m * ⟨γ, hγ⟩⁻¹, hN.conj_mem m hm ⟨γ, hγ⟩, by simp⟩)
    rwa [hcard] at this
  obtain ⟨E₀, hE₀n, hE₀P, hE₀9⟩ :=
    exists_normal_nine_of_solvable hΓ2 hdvd hPd1' hnoΓ hPdn'
  rcases hcases with ⟨-, hc6⟩ | ⟨hd4, h18⟩
  · exfalso
    have := Subgroup.card_subgroup_dvd_card E₀
    rw [hE₀9, hc6] at this
    norm_num at this
  set E' : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := E₀.map Γ.subtype with hE'
  have hE'Γ : E' ≤ Γ := Subgroup.map_subtype_le E₀
  have hE'P : E' ≤ Pd := by
    rintro _ ⟨e, he, rfl⟩
    exact hE₀P he
  have hE'n : ∀ γ ∈ Γ, ∀ e ∈ E', γ * e * γ⁻¹ ∈ E' := by
    rintro γ hγ _ ⟨m, hm, rfl⟩
    exact ⟨⟨γ, hγ⟩ * m * ⟨γ, hγ⟩⁻¹, hE₀n.conj_mem m hm ⟨γ, hγ⟩, by simp⟩
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective Γ.subtype_injective]
    exact hE₀9
  have hnoE : ∀ N : Subgroup (D.V ≃ₗ[ZMod 2] D.V), N ≤ E' →
      (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 3 :=
    fun N hNE hNn => (hno' N (hNE.trans hE'P) hNn).1
  have hv0 : D.π a ≠ 0 := (h.hat_VZ_cases hU D haV haZ).1
  have hvS : ∀ s ∈ D.img T, s (D.π a) = D.π a := fun s hs =>
    MulAction.mem_stabilizer_iff.mp (h.img_T_le_stabilizer hU D haV haZ hs)
  have hperp := eq_one_of_fixes_perp hB hd4 hΓsp hE'Γ hE'n hE'9 hnoE
    (S143V.isSylowTwoOf_img_T h D) hv0 hvS
  have hfpf := fixedPointFree_of_card_nine hB hd4 (hE'Γ.trans hΓsp) hE'9
  obtain ⟨y, hyH, hyX, w, hzgU, hcom⟩ :=
    exists_commutator_vec h hU hg D Tm haV haZ hperp hlt hzZ hz1 hzz hall
  set rh := S143V.rhoH h D with hrh
  set K : Subgroup ↥(mcOf T) :=
    (pOf T M g).subgroupOf (mcOf T) ⊓ Subgroup.comap rh E' with hK
  have hrange : rh.range = Γ := S143V.range_rhoH h D
  have hKn : K.Normal := by
    refine ⟨fun k hk x => ⟨hPn (x : G) x.2 (k : G) hk.1, ?_⟩⟩
    have h1 : rh x ∈ Γ := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    have h2 : rh k ∈ E' := hk.2
    have h3 := hE'n _ h1 _ h2
    show rh (x * k * x⁻¹) ∈ E'
    rw [map_mul, map_mul, map_inv]
    exact h3
  have hKmap : K.map rh = E' := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · intro n hn
      obtain ⟨x, hxP, hxN, hxρ⟩ := HatModel.mem_img.mp (hE'P hn)
      have hxH : x ∈ mcOf T := hPH hxP
      refine ⟨⟨x, hxH⟩, ⟨hxP, ?_⟩, ?_⟩
      · show rh ⟨x, hxH⟩ ∈ E'
        rw [S143V.rhoH_apply h D _ hxN, hxρ]
        exact hn
      · rw [S143V.rhoH_apply h D _ hxN]
        exact hxρ
  have hker : ∀ k ∈ K, rh k = 1 → Tm.ρ k = 1 := by
    intro k hk hk1
    have hkR : (k : G) ∈ Hyp1281Two.centralizerHat T M := (S143V.mem_ker_rhoH h D k).mp hk1
    exact tilde_rho_eq_one_of_mem_pCore h Tm k (hPQ ⟨hk.1, hkR⟩)
  have hodd : Odd (Nat.card (K.map Tm.ρ)) := by
    rw [card_map_tilde_eq h Tm D hker, hKmap, hE'9]
    exact ⟨4, by norm_num⟩
  have hKZ : ∀ k ∈ K, ∀ z' : Tm.V, Tm.phi h D z' = 0 → Tm.ρ k z' = z' := by
    intro k hk z' hz'
    obtain ⟨u, huC, rfl⟩ := (Tm.phi_eq_zero_iff h D z').mp hz'
    have hku : (k : G) * (u : G) * (k : G)⁻¹ ∈ uOfL22 T M :=
      HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 k.2) u.2
    rw [Tm.ρ_c k u hku]
    congr 1
    apply Subtype.ext
    show (k : G) * (u : G) * (k : G)⁻¹ = (u : G)
    have hc : (k : G) * (u : G) = (u : G) * (k : G) := pOf_centralizes h hU hg hk.1 huC
    calc (k : G) * (u : G) * (k : G)⁻¹ = ((u : G) * (k : G)) * (k : G)⁻¹ := by rw [hc]
      _ = (u : G) := by group
  have hfix : ∀ w' : D.V, (∀ k ∈ K, rh k w' = w') → w' = 0 := by
    intro w' hw'
    refine hfpf w' fun e he => ?_
    rw [← hKmap] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact hw' k hk
  set Y : Subgroup ↥(mcOf T) := (rconj (centerOf (uOfL22 T M)) g).subgroupOf (mcOf T) with hY
  have hYZ : ∀ y' ∈ Y, ∀ z' : Tm.V, Tm.phi h D z' = 0 → Tm.ρ y' z' = z' := by
    intro y' hy' z' hz'
    obtain ⟨u, huC, rfl⟩ := (Tm.phi_eq_zero_iff h D z').mp hz'
    have hku : (y' : G) * (u : G) * (y' : G)⁻¹ ∈ uOfL22 T M :=
      HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 y'.2) u.2
    rw [Tm.ρ_c y' u hku]
    congr 1
    apply Subtype.ext
    show (y' : G) * (u : G) * (y' : G)⁻¹ = (u : G)
    have hcomm : ⁅(u : G), (y' : G)⁆ = 1 := by
      have : ⁅(u : G), (y' : G)⁆ ∈ ⁅centerOf (uOfL22 T M), rconj (centerOf (uOfL22 T M)) g⁆ :=
        Subgroup.commutator_mem_commutator huC hy'
      rw [(h.lemma_12_8_13_three hU hg).2.2] at this
      exact Subgroup.mem_bot.mp this
    have hc : (y' : G) * (u : G) = (u : G) * (y' : G) := by
      calc (y' : G) * (u : G) = ((u : G) * (y' : G) * (u : G)⁻¹ * (y' : G)⁻¹)⁻¹ * ((u : G) * (y' : G)) := by
            group
        _ = (u : G) * (y' : G) := by
            rw [show (u : G) * (y' : G) * (u : G)⁻¹ * (y' : G)⁻¹ = ⁅(u : G), (y' : G)⁆ from
              (commutatorElement_def _ _).symm, hcomm]
            group
    calc (y' : G) * (u : G) * (y' : G)⁻¹ = ((u : G) * (y' : G)) * (y' : G)⁻¹ := by rw [hc]
      _ = (u : G) := by group
  have hv : Tm.c ⟨g⁻¹ * z * g, hzgU⟩ ∈ Submodule.span (ZMod 2)
      {x : Tm.V | ∃ y' ∈ Y, ∃ w' : Tm.V, x = Tm.ρ y' w' - w'} :=
    Submodule.subset_span ⟨⟨y, hyH⟩, hyX, Tm.c w, hcom.symm⟩
  have hV : ∀ w' ∈ VZ T M, ∃ hw : w' ∈ uOfL22 T M,
      Tm.c ⟨w', hw⟩ = 0 ∨ Tm.c ⟨w', hw⟩ = Tm.c ⟨g⁻¹ * z * g, hzgU⟩ := by
    intro w' hw'
    have hw'U : w' ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hw'
    refine ⟨hw'U, ?_⟩
    obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul_of_mem_VZ hU hg hw'
    have ha'U : a' ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M (Hyp1281Two.omegaOneCenter_le_VZ T M ha')
    have hb'U : b' ∈ uOfL22 T M := by
      have : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
      exact Hyp1281Two.VZ_le_uOfL22 T M (this hb')
    have e : (⟨a' * b', hw'U⟩ : ↥(uOfL22 T M)) = ⟨a', ha'U⟩ * ⟨b', hb'U⟩ := rfl
    have hca : Tm.c ⟨a', ha'U⟩ = 0 := (Tm.c_eq_zero_iff _).mpr ha'
    rw [e, Tm.c_mul, hca, zero_add]
    rcases hall _ (mem_rconj.mp hb') with h0 | h0
    · left
      have : b' = 1 := by
        calc b' = g⁻¹ * (g * b' * g⁻¹) * g := by group
          _ = 1 := by rw [h0]; group
      have e2 : (⟨b', hb'U⟩ : ↥(uOfL22 T M)) = 1 := Subtype.ext this
      rw [e2, Tm.c_one]
    · right
      have : b' = g⁻¹ * z * g := by
        calc b' = g⁻¹ * (g * b' * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [h0]
      have e2 : (⟨b', hb'U⟩ : ↥(uOfL22 T M)) = ⟨g⁻¹ * z * g, hzgU⟩ := Subtype.ext this
      rw [e2]
  have hgen := span_orbit_eq_top h Tm (Tm.c ⟨g⁻¹ * z * g, hzgU⟩) hV
  have hker0 := ker_eq_bot_of_odd_normal Tm.ρ rh (Tm.phi h D)
    (fun θ x => Tm.phi_ρ h D θ x) K hKn hodd hKZ hfix Y hYZ _ hv hgen
  obtain ⟨-, u, huC, huN⟩ := IsConcreteLE.lt_iff_le_and_exists.mp hlt
  have huU : u ∈ uOfL22 T M := huC.1
  have hu0 : Tm.phi h D (Tm.c ⟨u, huU⟩) = 0 := by
    rw [Tm.phi_c h D, D.π_eq_zero_iff huU]
    exact huC
  exact huN ((Tm.c_eq_zero_iff _).mp (hker0 _ hu0))

end MainSolv

section TopSolv

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))

include h hU in
theorem zu_eq_v1_of_inputs_solv
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (D : HatModel T M) (hsolv : Group.IsSolvable ↥(D.img (mcOf T))) (h94 : SzN29.G94StmtSolv) :
    centerOf (uOfL22 T M) = quasithinOmegaOneCenter T := by
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  by_contra hne
  exact false_of_lt_solv h hU hg D h35 hsolv h94
    (lt_of_le_of_ne h.omegaOneCenter_le_centerOf_uOfL22 (Ne.symm hne))

end TopSolv

end S143W

theorem lemma_14_3_15_of_lemma1435_solv (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h35 : Lemma1435) (hsolv : Lemma14315Solvable) (h94 : SzN29.G94StmtSolv) :
    S143.Lemma14315 := by
  intro G _ _ T M hyp hnot hnab
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hsolvD := hsolv G T M hyp hnot hnab
  obtain ⟨D⟩ := h1281.exists_hatModel
  have h35' : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M :=
    fun K hK hidx => h35 G T M hyp hnot K hK hidx
  have hZU := S143W.zu_eq_v1_of_inputs_solv h1281 hnab h35' D (hsolvD D) h94
  exact S143V.concl14315_of_zu_solv h1281 hnab hZU h35' D (hsolvD D) h94

end CFSG.Quasithin
