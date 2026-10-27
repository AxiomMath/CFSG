module

public import CFSG.Quasithin.EmptyFaithful.SBd16B1
public import CFSG.Quasithin.EmptyFaithful.SBd16B4

public section

namespace CFSG.Quasithin.SBd14

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

section Generic

theorem le_oddCoreIn_of_normalizer {G : Type*} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ CFSG.Open.fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem exists_conj_action {G : Type*} [Group G] {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    ∃ φ : ↥H →* MulAut ↥L,
      ∀ (h : ↥H) (x : ↥L), ((φ h x : ↥L) : G) = (h : G) * (x : G) * (h : G)⁻¹ :=
  ⟨(conjAct L).comp (Subgroup.inclusion hHL), fun h x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hHL h)) x⟩

theorem normalizer_map_of_characteristic {G : Type*} [Group G] {H C : Subgroup G}
    (hHC : H ≤ Subgroup.normalizer (C : Set G)) (W : Subgroup ↥C) [W.Characteristic] :
    H ≤ Subgroup.normalizer ((W.map C.subtype : Subgroup G) : Set G) := by
  obtain ⟨φ, hφ⟩ := exists_conj_action hHC
  have key : ∀ g : ↥H, ∀ y ∈ W.map C.subtype, (g : G) * y * (g : G)⁻¹ ∈ W.map C.subtype := by
    intro g y hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hW := (inferInstance : W.Characteristic).fixed (φ g)
    have h1 : k ∈ W.comap (φ g).toMonoidHom := by rw [hW]; exact hk
    exact ⟨φ g k, Subgroup.mem_comap.mp h1, hφ g k⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key ⟨g, hg⟩ y hy, fun hy => ?_⟩
  have h := key ⟨g⁻¹, H.inv_mem hg⟩ _ hy
  have e : (g⁻¹ : G) * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
  rwa [e] at h

theorem eq_of_central_sylow_of_oddCoreIn_eq_bot {G : Type*} [Group G] [Finite G] {I C P : Subgroup G}
    (hCI : C ≤ I) (hIC : I ≤ Subgroup.normalizer (C : Set G)) (hP : IsSylowTwoOf P C)
    (hcent : P ≤ Subgroup.centralizer (C : Set G)) (hodd : oddCoreIn I = ⊥) : C = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : P ≤ C := hP.1
  have hP2 : IsPGroup 2 (P.subgroupOf C) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  let P' : Sylow 2 ↥C := hP2.toSylow hP.2.2
  have hP'coe : (P' : Subgroup ↥C) = P.subgroupOf C := rfl
  have hcentral : Subgroup.normalizer (P' : Set ↥C) ≤ Subgroup.centralizer (P' : Set ↥C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ P := by
      have : y ∈ (P' : Subgroup ↥C) := hy
      rwa [hP'coe, Subgroup.mem_subgroupOf] at this
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hy') x x.2).symm
  obtain ⟨W, hWn, hWodd, hWidx, -, hWchar, -, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P' hcentral
  have hcardWb : Nat.card ↥(W.map C.subtype) = Nat.card ↥W :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hWbC : W.map C.subtype ≤ C := Subgroup.map_subtype_le W
  have hWbn : I ≤ Subgroup.normalizer ((W.map C.subtype : Subgroup G) : Set G) :=
    normalizer_map_of_characteristic hIC W
  have hWbodd : Odd (Nat.card ↥(W.map C.subtype)) := by
    rw [hcardWb]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hWodd)
  have hle := le_oddCoreIn_of_normalizer (hWbC.trans hCI) hWbn hWbodd
  rw [hodd, le_bot_iff] at hle
  have hW1 : Nat.card ↥W = 1 := by rw [← hcardWb, hle, Subgroup.card_bot]
  have h1 := Subgroup.card_mul_index W
  rw [hW1, one_mul, hWidx] at h1
  have hcardP : Nat.card ↥(P' : Subgroup ↥C) = Nat.card ↥P := by
    rw [hP'coe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  exact (Subgroup.eq_of_le_of_card_ge hPC (by omega)).symm

theorem exists_induced_action {G P : Type*} [Group G] [Group P] {H L : Subgroup G} {ρ : ↥L →* P}
    (hsurj : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center ↥L)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (φ : ↥H →* MulAut ↥L) (Φ : ↥H →* MulAut P),
      (∀ (h : ↥H) (x : ↥L), ((φ h x : ↥L) : G) = (h : G) * (x : G) * (h : G)⁻¹) ∧
        ∀ (h : ↥H) (x : ↥L), Φ h (ρ x) = ρ (φ h x) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_conj_action hHL
  have hex : ∀ h : ↥H, ∃ α : MulAut P, ∀ x : ↥L, α (ρ x) = ρ (φ h x) :=
    fun h => exists_induced_aut hsurj hker (φ h)
  choose α hα using hex
  have hαmul : ∀ h h' : ↥H, α (h * h') = α h * α h' := by
    intro h h'
    ext p
    obtain ⟨x, rfl⟩ := hsurj p
    calc α (h * h') (ρ x) = ρ (φ (h * h') x) := hα _ x
      _ = ρ (φ h (φ h' x)) := by rw [map_mul, MulAut.mul_apply]
      _ = α h (ρ (φ h' x)) := (hα h _).symm
      _ = α h (α h' (ρ x)) := by rw [hα h' x]
      _ = (α h * α h') (ρ x) := rfl
  exact ⟨φ, MonoidHom.mk' α hαmul, hφ, hα⟩

theorem relIndex_le_index_innerAut {G P : Type*} [Group G] [Group P] {L I : Subgroup G}
    {ρ : ↥L →* P} (hsurj : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center ↥L)
    (hperf : Group.IsPerfect ↥L) (hLI : L ≤ I) (hNL : I ≤ Subgroup.normalizer (L : Set G))
    (hC : I ⊓ Subgroup.centralizer (L : Set G) ≤ L)
    (hfin : (MulAut.conj : P →* MulAut P).range.index ≠ 0) :
    L.relIndex I ≤ (MulAut.conj : P →* MulAut P).range.index := by
  classical
  obtain ⟨φ, Φ, hφ, hΦ⟩ := exists_induced_action hsurj hker hNL
  have key : L.subgroupOf I = (MulAut.conj : P →* MulAut P).range.comap Φ := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro hg
      refine ⟨ρ ⟨(g : G), hg⟩, ?_⟩
      ext p
      obtain ⟨y, rfl⟩ := hsurj p
      have e : φ g y = ⟨(g : G), hg⟩ * y * ⟨(g : G), hg⟩⁻¹ := Subtype.ext (by rw [hφ]; rfl)
      rw [hΦ, e, MulAut.conj_apply, map_mul, map_mul, map_inv]
    · rintro ⟨p, hp⟩
      obtain ⟨x₀, hx₀⟩ := exists_conj_of_induced_inner hsurj hker hperf (φ g) (Φ g) (hΦ g)
        ⟨p, hp⟩
      have hcL : (x₀ : G)⁻¹ * (g : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : (g : G) * y * (g : G)⁻¹ = (x₀ : G) * y * (x₀ : G)⁻¹ :=
          (hφ g ⟨y, hy⟩).symm.trans (congrArg (fun z : ↥L => (z : G)) (hx₀ ⟨y, hy⟩))
        calc y * ((x₀ : G)⁻¹ * (g : G)) = (x₀ : G)⁻¹ * ((x₀ : G) * y * (x₀ : G)⁻¹) * (g : G) := by
              group
          _ = (x₀ : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) := by rw [← h1]
          _ = ((x₀ : G)⁻¹ * (g : G)) * y := by group
      have hcI : (x₀ : G)⁻¹ * (g : G) ∈ I := I.mul_mem (I.inv_mem (hLI x₀.2)) g.2
      have hcL' : (x₀ : G)⁻¹ * (g : G) ∈ L := hC ⟨hcI, hcL⟩
      have : (g : G) = (x₀ : G) * ((x₀ : G)⁻¹ * (g : G)) := by group
      rw [this]
      exact L.mul_mem x₀.2 hcL'
  have h1 : L.relIndex I = (MulAut.conj : P →* MulAut P).range.relIndex Φ.range := by
    rw [Subgroup.relIndex, key, Subgroup.index_comap]
  rw [h1]
  have h2 := Subgroup.relIndex_le_of_le_right (H := (MulAut.conj : P →* MulAut P).range)
    (le_top : Φ.range ≤ ⊤) (by rwa [Subgroup.relIndex_top_right])
  rwa [Subgroup.relIndex_top_right] at h2

theorem index_innerAut_projectiveSL_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range.index = 12 := by
  classical
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨-, hunits, ⟨e, -⟩, -⟩ :=
    LinearThreeFourOuter.linear_three_four_outer_quotient_rank_two_restriction K hK _ hσ
  show Nat.card (MulAut (projectiveSL 3 K) ⧸
    LinearThreeFourOuter.innerAutGroup (projectiveSL 3 K)) = 12
  rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hunits, Nat.card_prod]
  simp

theorem relIndex_zpowers_eq_three {G : Type*} [Group G] {L : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hdL : d ∉ L) : L.relIndex (Subgroup.zpowers d) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := fun h => hdL (h ▸ L.one_mem)
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hcard : Nat.card ↥(Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hord]
  have h1 := Subgroup.relIndex_mul_card L (Subgroup.zpowers d)
  have hfin : Finite ↥(Subgroup.zpowers d) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : Nat.card ↥(L ⊓ Subgroup.zpowers d) ∣ 3 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · rw [h, hcard] at h1
    omega
  · exfalso
    apply hdL
    have heq : L ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have hle : Subgroup.zpowers d ≤ L := heq ▸ inf_le_left
    exact hle (Subgroup.mem_zpowers d)

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.V₁_le_S (r : RestHyp T Mc M V₁ V₂ Yp I L t) : V₁ ≤ Sgp153 T V₁ :=
  le_inf (r.ctx.hyp.decomp.le₁.trans r.ctx.hyp.hyp.VZ_le_T) Subgroup.le_normalizer

theorem RestHyp.S_le_I (r : RestHyp T Mc M V₁ V₂ Yp I L t) : Sgp153 T V₁ ≤ I :=
  r.ctx.facts11.sylow.1

theorem RestHyp.Yp_le_I (r : RestHyp T Mc M V₁ V₂ Yp I L t) : Yp ≤ I :=
  le_sup_left.trans r.ctx.inH.1.1

theorem RestHyp.L_le_I (r : RestHyp T Mc M V₁ V₂ Yp I L t) : L ≤ I :=
  le_of_mem_cComp r.ctx.c33.mem

theorem RestHyp.V₁_le_L (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) : V₁ ≤ L := by
  rw [r.V₁_eq_center h113]
  exact fun x hx => hx.1

theorem RestHyp.card_S (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Nat.card ↥(Sgp153 T V₁) = 1024 := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hV := hyp.elemAbelian
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.T_le.trans hyp.le_normalizer
  obtain ⟨hV', L₁, L₂, tb, hS, -, -, -⟩ := D0.model
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T hyp.isSylowTwoOf_autI
  have h1 : 8 * Nat.card ↥(T ⊓ Subgroup.centralizer (VZ T M : Set G)) = Nat.card ↥T := by
    rw [← hT8]
    exact card_autI_mul_card_inf hV hTN
  have h2 : 2 * Nat.card ↥(Sgp153 T V₁) = Nat.card ↥T := by
    have h := Subgroup.relIndex_mul_card (Sgp153 T V₁) T
    rw [inf_eq_left.2 (inf_le_left : Sgp153 T V₁ ≤ T), D0.relIndex_nS hyp] at h
    exact h
  rw [r.R_eq_Q h113, r.card_Q h113] at h1
  omega

theorem RestHyp.centralizer_I_L (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    I ⊓ Subgroup.centralizer (L : Set G) = V₁ := by
  classical
  have hSI : Sgp153 T V₁ ≤ I := r.S_le_I
  have hC : I ⊓ Subgroup.centralizer (L : Set G) ≤ I := inf_le_left
  have hIC : I ≤ Subgroup.normalizer ((I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      S153F.mem_normalizer_centralizer_of_mem_normalizer (r.hNL hg)⟩
  have hSC : Sgp153 T V₁ ⊓ (I ⊓ Subgroup.centralizer (L : Set G)) = V₁ := by
    rw [← inf_assoc, inf_eq_left.2 hSI]
    exact r.CSL_eq h113
  have hsyl : IsSylowTwoOf V₁ (I ⊓ Subgroup.centralizer (L : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal r.ctx.facts11.sylow hC hIC
    rwa [hSC] at this
  have hV₁L := r.V₁_le_L h113
  have hcent : V₁ ≤ Subgroup.centralizer ((I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc.2 v (hV₁L hv)).symm
  exact eq_of_central_sylow_of_oddCoreIn_eq_bot hC hIC hsyl hcent r.ctx.oddCore

theorem RestHyp.relIndex_L_S (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    L.relIndex (Sgp153 T V₁) = 4 := by
  have h := Subgroup.relIndex_mul_card L (Sgp153 T V₁)
  rw [inf_comm, r.card_Q h113, r.card_S h113] at h
  omega

theorem RestHyp.relIndex_L_LS (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    L.relIndex (L ⊔ Sgp153 T V₁) = 4 := by
  rw [sup_comm, A4.relIndex_sup_eq_of_le_normalizer' r.S_le_L]
  exact r.relIndex_L_S h113

theorem RestHyp.exists_d (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∃ d : G, d ∈ Yp ∧ d ^ 3 = 1 ∧ d ∉ L ∧ ∀ v ∈ V₁, v ≠ 1 → d * v * d⁻¹ ≠ v := by
  obtain ⟨d, hdYp, hd3, -, hdN, v₀, hv₀, hv₀ne⟩ := r.exists_d_V₁ h113
  have D0 := r.ctx.hyp.decomp
  refine ⟨d, hdYp, hd3, fun hdL => hv₀ne ?_, fun v hv hv1 hdv => hv₀ne ?_⟩
  · have h1 : d * v₀ = v₀ * d := Subgroup.mem_centralizer_iff.mp (r.h1 hv₀) d hdL
    rw [h1]
    group
  · have hsq : ∀ a ∈ V₁, a * a = 1 := fun a ha => r.V_sq a (D0.le₁ ha)
    have hdodd : Odd (orderOf d) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hd3)
    exact SBd7.odd_fixes_of_card_four D0.card₁ hsq hdN hdodd hv hv1 hdv v₀ hv₀

theorem RestHyp.relIndex_sup_I (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    L.relIndex I = 12 ∧ (L ⊔ Yp ⊔ Sgp153 T V₁).relIndex I = 1 := by
  classical
  obtain ⟨K, _, _, _, ρ, hK4, hmod⟩ := exists_borelModel r.ctx.c33.center_eq r.sylow r.hn2
  have hperf : Group.IsPerfect ↥L := r.ctx.c33.quasisimple.1
  have hLI : L ≤ I := r.L_le_I
  have hYpI : Yp ≤ I := r.Yp_le_I
  have hSI : Sgp153 T V₁ ≤ I := r.S_le_I
  have hC : I ⊓ Subgroup.centralizer (L : Set G) ≤ L := by
    rw [r.centralizer_I_L h113]
    exact r.V₁_le_L h113
  have h12 : (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range.index = 12 :=
    index_innerAut_projectiveSL_three hK4
  have hup : L.relIndex I ≤ 12 := by
    have := relIndex_le_index_innerAut hmod.surj hmod.ker_eq hperf hLI r.hNL hC
      (by rw [h12]; norm_num)
    rwa [h12] at this
  set N : Subgroup G := L ⊔ Yp ⊔ Sgp153 T V₁ with hN
  have hLN : L ≤ N := le_sup_left.trans le_sup_left
  have hNI : N ≤ I := sup_le (sup_le hLI hYpI) hSI
  obtain ⟨d, hdYp, hd3, hdL, -⟩ := r.exists_d h113
  have h3 : 3 ∣ L.relIndex N := by
    have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (L : Set G) :=
      Subgroup.zpowers_le.mpr (r.Yp_le_L hdYp)
    have h1 : L.relIndex (Subgroup.zpowers d ⊔ L) = 3 := by
      rw [A4.relIndex_sup_eq_of_le_normalizer' hdN]
      exact relIndex_zpowers_eq_three hd3 hdL
    have hle2 : Subgroup.zpowers d ⊔ L ≤ N :=
      sup_le ((Subgroup.zpowers_le.mpr hdYp).trans (le_sup_right.trans le_sup_left)) hLN
    have h := Subgroup.relIndex_mul_relIndex L (Subgroup.zpowers d ⊔ L) N le_sup_right hle2
    rw [h1] at h
    exact ⟨_, h.symm⟩
  have h4 : 4 ∣ L.relIndex N := by
    have h1 := r.relIndex_L_LS h113
    have hle2 : L ⊔ Sgp153 T V₁ ≤ N := sup_le hLN le_sup_right
    have h := Subgroup.relIndex_mul_relIndex L (L ⊔ Sgp153 T V₁) N le_sup_left hle2
    rw [h1] at h
    exact ⟨_, h.symm⟩
  have h12d : 12 ∣ L.relIndex N := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
    simpa using this
  have hmul := Subgroup.relIndex_mul_relIndex L N I hLN hNI
  have hane : L.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hbne : N.relIndex I ≠ 0 := Subgroup.index_ne_zero_of_finite
  have ha : 12 ≤ L.relIndex N := Nat.le_of_dvd (Nat.pos_of_ne_zero hane) h12d
  have hab : L.relIndex N ≤ L.relIndex N * N.relIndex I :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hbne)
  have hc12 : L.relIndex N * N.relIndex I ≤ 12 := hmul ▸ hup
  have ha12 : L.relIndex N = 12 := by omega
  have hb1 : N.relIndex I = 1 := by
    rw [ha12] at hc12
    have := Nat.pos_of_ne_zero hbne
    omega
  refine ⟨?_, hb1⟩
  rw [← hmul, ha12, hb1]

theorem RestHyp.relIndex_L_I (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    L.relIndex I = 12 :=
  (r.relIndex_sup_I h113).1

theorem RestHyp.I_eq_sup (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    I = L ⊔ Yp ⊔ Sgp153 T V₁ :=
  le_antisymm (Subgroup.relIndex_eq_one.mp (r.relIndex_sup_I h113).2)
    (sup_le (sup_le r.L_le_I r.Yp_le_I) r.S_le_I)

theorem RestHyp.exists_v (r : RestHyp T Mc M V₁ V₂ Yp I L t) (_h113 : StageLemma14113) :
    ∃ v ∈ V₁, v ≠ 1 ∧ ∀ s ∈ Sgp153 T V₁, s * v = v * s := by
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hV₁ne : V₁ ≠ ⊥ := by
    intro h
    have := D0.card₁
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨n, hnV, hn1, hnS⟩ :=
    SBd7.exists_central_of_normal hS2 r.V₁_le_S inf_le_right hV₁ne
  refine ⟨n, hnV, hn1, fun s hs => ?_⟩
  have h := hnS s hs
  calc s * n = (s * n * s⁻¹) * s := by group
    _ = n * s := by rw [h]

theorem RestHyp.centralizer_I_v (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {v : G}
    (hv : v ∈ V₁) (hv1 : v ≠ 1) (hS : ∀ s ∈ Sgp153 T V₁, s * v = v * s) :
    I ⊓ Subgroup.centralizer ({v} : Set G) = L ⊔ Sgp153 T V₁ := by
  classical
  have hLI : L ≤ I := r.L_le_I
  have hSI : Sgp153 T V₁ ≤ I := r.S_le_I
  have hLSI : L ⊔ Sgp153 T V₁ ≤ I := sup_le hLI hSI
  have hLS : L ⊔ Sgp153 T V₁ ≤ I ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_inf hLSI (sup_le (fun l hl => ?_) (fun s hs => ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (r.h1 hv) l hl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs)
  have hidx : (L ⊔ Sgp153 T V₁).relIndex I = 3 := by
    have h := Subgroup.relIndex_mul_relIndex L (L ⊔ Sgp153 T V₁) I le_sup_left hLSI
    rw [r.relIndex_L_LS h113, r.relIndex_L_I h113] at h
    omega
  have hmul := Subgroup.relIndex_mul_relIndex (L ⊔ Sgp153 T V₁)
    (I ⊓ Subgroup.centralizer ({v} : Set G)) I hLS inf_le_left
  rw [hidx] at hmul
  have hdvd : (I ⊓ Subgroup.centralizer ({v} : Set G)).relIndex I ∣ 3 :=
    ⟨(L ⊔ Sgp153 T V₁).relIndex (I ⊓ Subgroup.centralizer ({v} : Set G)), by rw [← hmul, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have hIC : I ≤ I ⊓ Subgroup.centralizer ({v} : Set G) := Subgroup.relIndex_eq_one.mp h1
    obtain ⟨d, hdYp, -, -, hdfix⟩ := r.exists_d h113
    have hdc : d ∈ Subgroup.centralizer ({v} : Set G) := (hIC (r.Yp_le_I hdYp)).2
    have h2 : d * v = v * d := Subgroup.mem_centralizer_singleton_iff.mp hdc
    apply hdfix v hv hv1
    rw [h2]
    group
  · have h1 : (L ⊔ Sgp153 T V₁).relIndex (I ⊓ Subgroup.centralizer ({v} : Set G)) = 1 := by
      rw [h3] at hmul
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hLS

end Main

end CFSG.Quasithin.SBd14
