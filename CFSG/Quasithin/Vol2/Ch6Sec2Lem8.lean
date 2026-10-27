module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8B
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem10
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8Res
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem amalgamHypV_ch62 (h432 : Stmt4_3_2) {H : Subgroup G} (hTH : IsSylowTwoOf T H)
    (hHM : ¬ H ≤ M) : AmalgamHypV (L ⊔ T ⊔ H) (L ⊔ T) H T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.toHyp611.isUniqueM h432
  have hQ : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    h.toHyp611.centralizer_eq
  refine
    { gen := rfl
      charTwo := ?_
      sylow₁ := h.toHyp611.isSylowIn_T
      sylow₂ := hTH
      o2_trivial := ?_
      reduced := h.module.isTwoReducedIn
      cT := ?_ }
  · obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
    have hLT : InH (P : Subgroup G) (L ⊔ T) := by
      rw [hP]
      exact ⟨le_sup_right, h.maximal.1.2.2.2⟩
    exact CFSG.Quasithin.charTwo_of_inH h.qtke.2.1 P hLT
  · by_contra hne
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T ⊔ H)
    have hle := le_of_isUniqueM_of_le_twoLocal hU (le_sup_left.trans hN)
      ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    exact hHM ((le_sup_right.trans hN).trans hle)
  · apply le_antisymm
    · have hle : ch6Q T V ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
        inf_le_inf_right _ le_sup_right
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle ?_
        (h.sylow.1.to_le inf_le_left)
      rw [hQ]
      exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
    · rw [hQ]
      have hnorm : L ⊔ T ≤ Subgroup.normalizer
          (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
        intro x hx
        have h1 : x ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
          F7.normalizer_le_normalizer_centralizer V (h.toHyp611.sup_le_normalizer hx)
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp
          (Subgroup.le_normalizer hx) y, Subgroup.mem_normalizer_iff.mp h1 y]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
        (hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem exists_isHStar_le_Gz (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    ∃ H : Subgroup G, IsHStar T M H ∧
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZ2 := h.card_omega h331 h432 h512 h614 h615
  have hV := h.toHyp611.isElemAbelian
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hTGz : T ≤ Subgroup.centralizer (Z : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  have hZO : Z ≤ pCoreOf 2 (Subgroup.centralizer (Z : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun z hz => ?_)
      (fun x hx => Subgroup.centralizer_le_normalizer _ hx) ?_
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        B2F.isElemAbelian_comm hV (hZZS hy).1 (hZZS hz).1
    · exact B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono (hZZS.trans inf_le_left) hV)
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    rw [← hZ, h0, Subgroup.card_bot] at hZ2
    omega
  have hGz : InH T (Subgroup.centralizer (Z : Set G)) :=
    ⟨hTGz, fun h0 => hZ1 (eq_bot_iff.mpr (h0 ▸ hZO))⟩
  have hGzM : ¬ Subgroup.centralizer (Z : Set G) ≤ M := h.not_centralizer_omega_le h331 h615
  obtain ⟨H, ⟨hH1, hH2, hH3⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH T H ∧ ¬ H ≤ M ∧ H ≤ Subgroup.centralizer (Z : Set G)}
    ⟨_, hGz, hGzM, le_rfl⟩
  refine ⟨H, ⟨hH1, hH2, fun Y hY hYH hYM => ?_⟩, hH3⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM, hYH.trans hH3⟩ (lt_of_le_of_ne hYH hne)

theorem isUniqueMaxOver_ch62 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    {H : Subgroup G} (hHs : IsHStar T M H) :
    IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (V : Set G)) := by
  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, -, -, h4⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  rw [← hMeq] at h4
  obtain ⟨h4a, -⟩ := h4 H hHs
  rwa [(stmt6_1_8 h432 h615 G T M L V 2 h.toHyp611Nat).2 H hHs] at h4a

theorem odd_critDist_ch62 (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) {H : Subgroup G}
    (hyp : AmalgamHypV (L ⊔ T ⊔ H) (L ⊔ T) H T V) :
    Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V) := by
  by_contra hodd
  have hV1 : V ≠ ⊥ := h.toHyp611.ne_bot
  have hev : Even (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hyp hV1
  obtain ⟨hne, hle, -, -⟩ := commutator_V_Vv_of_even hyp hV1 hev hγ hVγ
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact hev)
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hvt
  rw [Vv_smul_γ₀ hyp.normalizes, conjSub_eq_conjSubgroup_ch62] at hne hle
  have h1 : V ≤ Subgroup.normalizer (conjSubgroup V (g : G)⁻¹ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (hle.trans inf_le_right)
  have h2 : conjSubgroup V (g : G)⁻¹ ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hle.trans inf_le_left)
  exact hne (stmt6_2_3 h432 h6111 G T M L V h _ h1 h2)

end Hyp6Sec2

omit [Finite G] in
theorem conjSub_le_conjClosure_ch62 {V H : Subgroup G} {x : G} (hx : x ∈ H) :
    conjSub x V ≤ conjClosure V H := by
  intro y hy
  have := mem_conjClosure hx (mem_conjSub.mp hy)
  simpa [mul_assoc] using this

theorem conjSub_V_le_stab_of_dist_le {G₀ G₁ G₂ T : Subgroup G}
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (u : G₀) {ε : CosetGeom G₀ G₁ G₂}
    (hd : dist (u • γ₀ G₀ G₁ G₂) ε ≤ critDist G₀ G₁ G₂ V) : conjSub (u : G) V ≤ stab ε := by
  have h1 : dist (γ₀ G₀ G₁ G₂) (u⁻¹ • ε) ≤ critDist G₀ G₁ G₂ V := by
    have := dist_smul u⁻¹ (u • γ₀ G₀ G₁ G₂) ε
    rw [inv_smul_smul] at this
    rw [this]; exact hd
  have h2 := conjSub_mono (u : G) (V_le_stab_of_dist_le hyp hV h1)
  rwa [← stab_smul, smul_inv_smul] at h2

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem false_of_wframe628 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) (h627 : Stmt6_2_7) (hF : F713Two)
    {H : Subgroup G} (hyp : AmalgamHypV (L ⊔ T ⊔ H) (L ⊔ T) H T V)
    (hSQTK : CFSG.SectionRank.IsSQTKCat ↥H)
    (hUM : IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hc : E1.nParam H = 1)
    (hLie : ∀ K ∈ cComp H, ¬ IsCharTwoBigE22 H (H ⊓ Subgroup.normalizer (V : Set G)) K)
    (hb3 : 3 ≤ critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)
    (hodd : Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V))
    (hVO : V ≤ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
    {z : G} (hz1 : z ≠ 1)
    (hZz : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) (hzV : z ∈ V)
    {γ' : CosetGeom (L ⊔ T ⊔ H) (L ⊔ T) H}
    (hcrit : IsCriticalVertex (L ⊔ T ⊔ H) (L ⊔ T) H V γ')
    (hW2 : (Vv V γ' ⊓ Subgroup.normalizer (V : Set G)).relIndex (Vv V γ') = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1 : V ≠ ⊥ := h.toHyp611.ne_bot
  have hVel := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVel
  have hN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  have h₂ : H ≤ L ⊔ T ⊔ H := le_sup_right
  have hAγ₁ : Vv V (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = conjClosure V H := Vv_γ₁ h₂ hN
  have hVA : V ≤ conjClosure V H := le_conjClosure V H
  have hAel : IsElemAbelian 2 (conjClosure V H) := by
    rw [← hAγ₁]
    exact isElemAbelian_Vv_γ₁ hyp hV1 (by omega)
  have hvt : vtype γ' = true :=
    vtype_eq_true_of_odd hyp.gen (by rw [hcrit.dist_eq]; exact hodd)
  obtain ⟨w, hw⟩ := exists_smul_eq_γ₁ hvt
  have hVvγ' : Vv V γ' = conjSub (w : G) (conjClosure V H) := by rw [hw, Vv_smul hN, hAγ₁]
  have hWel : IsElemAbelian 2 (Vv V γ') := by
    rw [hVvγ']
    exact F7.isElemAbelian_conjSub hAel
  have hVγ' : V ≤ stab γ' := V_le_stab_of_dist_le hyp hV1 (le_of_eq hcrit.dist_eq)
  have hVNW : V ≤ Subgroup.normalizer (Vv V γ' : Set G) :=
    hVγ'.trans (stab_le_normalizer_Vv hN γ')
  obtain ⟨δ, hδn, hδ2, k, -, hkδ, hI⟩ := hF G (L ⊔ T ⊔ H) (L ⊔ T) H T V hyp hV1 hSQTK γ'
    hcrit hb3 hodd hUM hc hLie V (hVA.trans hAγ₁.ge) hcrit.not_le
  have hδn' : (w⁻¹ • δ) ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj (w⁻¹)).mpr hδn
    rwa [hw, inv_smul_smul] at this
  obtain ⟨k', hk', hk'δ⟩ :=
    stab_transitive_on_nbrs (γ := γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
      (show γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁.symm) hδn'
  have hk'H : ((k' : ↥(L ⊔ T ⊔ H)) : G) ∈ H := by rwa [stab_γ₁ h₂] at hk'
  have hδeq : δ = (w * k') • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by
    rw [mul_smul, hk'δ, smul_inv_smul]
  set u : ↥(L ⊔ T ⊔ H) := w * k' with hu
  have hD : Vv V δ = conjSub (u : G) V := by rw [hδeq, Vv_smul_γ₀ hN]
  set D := conjSub (u : G) V with hDdef
  rw [hD] at hδ2
  have hDW : D ≤ Vv V γ' := by
    rw [hVvγ', hDdef, hu, Subgroup.coe_mul, conjSub_mul]
    exact conjSub_mono _ (conjSub_le_conjClosure_ch62 hk'H)
  have hDH : D ≤ H := by
    have hd : dist (u • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) ≤
        critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by
      rw [← hδeq]
      have h1 := CosetGeom.dist_triangle hyp.gen δ γ' (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
      have h2 : dist δ γ' = 1 := by
        rw [CosetGeom.dist_comm]
        exact dist_eq_one_iff_adj.mpr hδn
      have h3 := hcrit.geodesic
      rw [CosetGeom.dist_comm γ' (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)] at h1
      omega
    have := conjSub_V_le_stab_of_dist_le hyp hV1 u hd
    rwa [stab_γ₁ h₂] at this
  have hD2 : (D ⊓ Subgroup.normalizer (V : Set G)).relIndex D ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    rw [Subgroup.inf_relIndex_left] at hW2
    rw [← hW2]
    exact Subgroup.relIndex_le_of_le_right hDW (by rw [hW2]; norm_num)
  have hDN : ¬ D ≤ Subgroup.normalizer (V : Set G) := by
    intro hle
    have h1 := h.commutator_conj_eq_bot h432 h627 hle
    have hVC : V ≤ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.commutator_comm] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have hVN : V ≤ Subgroup.normalizer (D : Set G) :=
      hVC.trans (Subgroup.centralizer_le_normalizer _)
    rw [inf_eq_left.mpr hVN, Subgroup.relIndex_self] at hδ2
    norm_num at hδ2
  have hVND : ¬ V ≤ Subgroup.normalizer (D : Set G) := by
    intro hle
    rw [inf_eq_left.mpr hle, Subgroup.relIndex_self] at hδ2
    norm_num at hδ2
  have e1 : conjSub (1 : G) V = V := conjSub_one V
  obtain ⟨-, hc1, -, hr1, -, -⟩ := h.pair628 h331 h432 h615 h6110 hE612 h627 (x := 1)
    (y := (u : G)) hWel hDW (by rw [e1]; exact hVNW) (by rw [e1]; exact hDN)
    (by rw [e1]; exact hD2)
  rw [e1] at hc1 hr1
  obtain ⟨-, hc2, -, -, -, -⟩ := h.pair628 h331 h432 h615 h6110 hE612 h627 (x := (u : G))
    (y := 1) hAel (by rw [e1]; exact hVA)
    (hDH.trans (le_normalizer_conjClosure V H)) (by rw [e1]; exact hVND)
    (by rw [e1, hδ2])
  rw [e1] at hc2
  have hUle1 : ⁅D ⊓ Subgroup.normalizer (V : Set G), V ⊓ Subgroup.normalizer (D : Set G)⁆ ≤
      V ⊓ Subgroup.centralizer (D : Set G) := by
    rw [← hc1]
    exact Subgroup.commutator_mono le_rfl inf_le_left
  have hUle2 : ⁅D ⊓ Subgroup.normalizer (V : Set G), V ⊓ Subgroup.normalizer (D : Set G)⁆ ≤
      D ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← hc2, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl inf_le_left
  obtain ⟨n, hn, hnC⟩ : ∃ n ∈ D ⊓ Subgroup.normalizer (V : Set G),
      n ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    have h1 : (Subgroup.centralizer (V : Set G)).relIndex
        (D ⊓ Subgroup.normalizer (V : Set G)) = 1 := Subgroup.relIndex_eq_one.mpr hcon
    rw [hr1] at h1
    norm_num at h1
  have hfix := h.card_fix_le_four h432 hn.2 hnC
  have hVNDc : Nat.card ↥(V ⊓ Subgroup.normalizer (D : Set G)) = 8 := by
    have h1 := Subgroup.relIndex_mul_card (H := V ⊓ Subgroup.normalizer (D : Set G)) (K := V)
    rw [inf_of_le_left (inf_le_left : V ⊓ Subgroup.normalizer (D : Set G) ≤ V), hδ2,
      h.natural.card_eq] at h1
    change 2 * Nat.card ↥(V ⊓ Subgroup.normalizer (D : Set G)) = 2 ^ 2 * 2 ^ 2 at h1
    have e16 : (2 : ℕ) ^ 2 * 2 ^ 2 = 16 := by norm_num
    rw [e16] at h1
    omega
  obtain ⟨e, he, hne⟩ : ∃ e ∈ V ⊓ Subgroup.normalizer (D : Set G),
      e ∉ Subgroup.centralizer ({n} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : V ⊓ Subgroup.normalizer (D : Set G) ≤ V ⊓ Subgroup.centralizer ({n} : Set G) :=
      fun e he => ⟨he.1, hcon e he⟩
    have := Subgroup.card_le_of_le hle
    omega
  set z₀ := ⁅n, e⁆ with hz₀def
  have hz₀ : z₀ ∈ ⁅D ⊓ Subgroup.normalizer (V : Set G),
      V ⊓ Subgroup.normalizer (D : Set G)⁆ := Subgroup.commutator_mem_commutator hn he
  have hz₀1 : z₀ ≠ 1 := by
    intro h0
    apply hne
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    rw [hz₀def, commutatorElement_def] at h0
    calc n * e = n * e * n⁻¹ * e⁻¹ * (e * n) := by group
      _ = e * n := by rw [h0, one_mul]
  have hz₀V : z₀ ∈ V := (hUle1 hz₀).1
  have hz₀D : z₀ ∈ D := (hUle2 hz₀).1
  have hVk : conjSub k⁻¹ V ≤ Subgroup.normalizer (D : Set G) := by
    rw [← conjSubgroup_eq_conjSub_ch62]
    refine hkδ.trans ?_
    rw [← hD]
    exact stab_le_normalizer_Vv hN δ
  have hVkC : ⁅conjSub k⁻¹ V, D⁆ = ⊥ := h.commutator_conj_conj_eq_bot h432 h627 hVk
  have hVkz : ∀ v ∈ conjSubgroup V k, v * z₀ = z₀ * v := by
    intro v hv
    rw [conjSubgroup_eq_conjSub_ch62] at hv
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVkC hv
    exact (Subgroup.mem_centralizer_iff.mp h1 z₀ hz₀D).symm
  obtain ⟨l, hlL, hlz⟩ := h.natural.exists_conj_eq hzV hz₀V hz1 hz₀1
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hlL
  set Z' := conjSub l (quasithinOmegaOneCenter T) with hZ'
  have hZ'z₀ : ∀ x ∈ Z', x = 1 ∨ x = z₀ := by
    intro x hx
    rw [hZ', mem_conjSub] at hx
    rcases hZz _ hx with h0 | h0
    · left
      have := congrArg (fun y => l * y * l⁻¹) h0
      simpa [mul_assoc] using this
    · right
      rw [← hlz]
      have := congrArg (fun y => l * y * l⁻¹) h0
      simpa [mul_assoc] using this
  have hVO' : V ≤ pCoreOf 2 (Subgroup.centralizer (Z' : Set G)) := by
    have := conjSub_mono l hVO
    rwa [conjSub_eq_of_mem_normalizer' hlV, ← pCoreOf_conjSub,
      ← CFSG.Quasithin.conjSub_centralizer] at this
  set I := V ⊔ conjSubgroup V k with hIdef
  have hIC : I ≤ Subgroup.centralizer (Z' : Set G) := by
    apply sup_le
    · intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      rcases hZ'z₀ x hx with rfl | rfl
      · group
      · exact B2F.isElemAbelian_comm hVel hz₀V hv
    · intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      rcases hZ'z₀ x hx with rfl | rfl
      · group
      · exact (hVkz v hv).symm
  have hVOI : V ≤ pCoreOf 2 I := by
    refine (le_inf hVO' (le_sup_left : V ≤ I)).trans ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hIC hx), Subgroup.le_normalizer hx⟩
  apply hI
  set P := pCoreOf 2 I with hP
  set B := conjSubgroup V k with hB
  have hBN : B ≤ Subgroup.normalizer (P : Set G) :=
    (le_sup_right : B ≤ I).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hB2 : IsPGroup 2 B := isPGroup_conjSubgroup hV2 k
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hP2
  obtain ⟨c, hc'⟩ := (IsPGroup.iff_card).mp hB2
  have hcard := card_sup_mul_card_inf_ch62 hBN
  rw [ha, hc'] at hcard
  have hdvd : Nat.card ↥(P ⊔ B) ∣ 2 ^ (a + c) := by
    rw [pow_add, ← hcard]
    exact Dvd.intro _ rfl
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hPB : IsPGroup 2 ↥(P ⊔ B) := IsPGroup.of_card hm
  exact hPB.to_le (sup_le (hVOI.trans le_sup_left) le_sup_right)

end Hyp6Sec2

theorem stmt6_2_8_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612)
    (h627 : Stmt6_2_7) (hF : F713Two) (hL : Res628Lie) : Stmt6_2_8 := by
  intro G _ _ T M L V h hVO
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.simple
  have hV1 : V ≠ ⊥ := h.toHyp611.ne_bot
  set Z := quasithinOmegaOneCenter T with hZ
  have hZV := h.omega_le_V h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Z = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hZz : ∀ w ∈ Z, w = 1 ∨ w = z := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hw1, hwz⟩ := hcon
    have hs : ({1, z, w} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hwz)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hz1, Ne.symm hw1⟩
    have hsub : (({1, z, w} : Finset G) : Set G) ⊆ (Z : Set G) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Z.one_mem
      · exact hzZ
      · exact hw
    have h3 : 3 ≤ Nat.card Z :=
      calc 3 = ({1, z, w} : Finset G).card := hs.symm
        _ = (({1, z, w} : Finset G) : Set G).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ (Z : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card Z := Nat.card_coe_set_eq _
    omega
  obtain ⟨H, hHs, hHZ⟩ := h.exists_isHStar_le_Gz h331 h432 h512 h614 h615
  have hTH : IsSylowTwoOf T H :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      hHs.1.1 le_top
  have hyp := h.amalgamHypV_ch62 h432 hTH hHs.2.1
  have hN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  have h₂ : H ≤ L ⊔ T ⊔ H := le_sup_right
  have hVH : V ≤ pCoreOf 2 H := by
    refine (le_inf hVO (h.toHyp611.le_T.trans hHs.1.1)).trans ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hHZ hx), Subgroup.le_normalizer hx⟩
  have hb2 := two_le_critDist_of_le_pCoreOf hyp hV1 hVH
  have hodd := h.odd_critDist_ch62 h432 (stmt6_1_11 h432 h6110) hyp
  have hb3 : 3 ≤ critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by obtain ⟨k, hk⟩ := hodd; omega
  have hUM := h.isUniqueMaxOver_ch62 h331 h432 h615 hHs
  have hc : E1.nParam H = 1 := h.nParam_eq_one H hHs
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥H :=
    (qtkeCore_of_cat h.nonabelian h.qtke).1 H hHs.1.2
  have hAγ₁ : Vv V (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = conjClosure V H := Vv_γ₁ h₂ hN
  have hVA : V ≤ conjClosure V H := le_conjClosure V H
  have hAel : IsElemAbelian 2 (conjClosure V H) := by
    rw [← hAγ₁]
    exact isElemAbelian_Vv_γ₁ hyp hV1 (by omega)
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV1
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  have hVvγ : Vv V γ = conjSub (g : G) (conjClosure V H) := by rw [hg, Vv_smul hN, hAγ₁]
  obtain ⟨-, ⟨γ₂, hγ₂n, hdγ₂⟩⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hUγH : conjSub (g : G) (conjClosure V H) ≤ H := by
    have := (Vv_le_pCoreOf_stab_inf hyp hV1 hγ₂n hdγ₂).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    rw [hVvγ, stab_γ₁ h₂] at this
    exact this.trans inf_le_left
  have hA₂ : ¬ conjClosure V H ≤ ballStab 1 γ := fun hle => hγ.not_le (hVA.trans hle)
  obtain ⟨α, hαn, hα2⟩ := exists_nbr_relIndex_two hyp hV1 hγ hb3 hodd hUM hc hAγ₁.ge hA₂
  have hgα : (g⁻¹ • α) ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj (g⁻¹)).mpr hαn
    rwa [hg, inv_smul_smul] at this
  obtain ⟨k, hk, hkα⟩ :=
    stab_transitive_on_nbrs (γ := γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
      (show γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁.symm) hgα
  have hkH : ((k : ↥(L ⊔ T ⊔ H)) : G) ∈ H := by rwa [stab_γ₁ h₂] at hk
  have hαy : α = (g * k) • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by
    rw [mul_smul, hkα, smul_inv_smul]
  set y : G := ((g * k : ↥(L ⊔ T ⊔ H)) : G) with hy
  have hE : Vv V α = conjSub y V := by rw [hαy, Vv_smul_γ₀ hN]
  have hEUγ : conjSub y V ≤ conjSub (g : G) (conjClosure V H) := by
    rw [hy, Subgroup.coe_mul, conjSub_mul]
    exact conjSub_mono _ (conjSub_le_conjClosure_ch62 hkH)
  have hEH : conjSub y V ≤ H := hEUγ.trans hUγH
  rw [hE] at hα2
  obtain ⟨x, hxH, hxE⟩ : ∃ x ∈ H,
      ¬ conjSub x V ≤ Subgroup.normalizer (conjSub y V : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : conjClosure V H ≤ Subgroup.normalizer (conjSub y V : Set G) :=
      conjClosure_le fun x hx v hv => hcon x hx (mul_mem_conjSub hv)
    rw [inf_eq_left.mpr hle, Subgroup.relIndex_self] at hα2
    norm_num at hα2
  have hF2 : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex
      (conjSub x V) ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    rw [Subgroup.inf_relIndex_left] at hα2
    rw [← hα2]
    exact Subgroup.relIndex_le_of_le_right (conjSub_le_conjClosure_ch62 hxH)
      (by rw [hα2]; norm_num)
  obtain ⟨hEF, -⟩ := h.pair628 h331 h432 h615 h6110 hE612 h627 hAel
    (conjSub_le_conjClosure_ch62 hxH) (hEH.trans (le_normalizer_conjClosure V H)) hxE hF2
  have hEγ₁ : ¬ conjSub y V ≤ ballStab 1 (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    intro hle
    apply hEF
    set x' : ↥(L ⊔ T ⊔ H) := ⟨x, h₂ hxH⟩ with hx'
    have hxn : x' • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
      have h1 : x' • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H = γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H :=
        smul_eq_of_mem_stab (by rw [stab_γ₁ h₂]; exact hxH)
      have := (smul_adj x').mpr (adj_γ₀_γ₁ (G₀ := L ⊔ T ⊔ H) (G₁ := L ⊔ T) (G₂ := H)).symm
      rwa [h1] at this
    have hadj : (graph (L ⊔ T ⊔ H) (L ⊔ T) H).Adj (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
        (x' • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) := hxn
    have h2 : conjSub y V ≤ stab (x' • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) :=
      hle.trans (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)
    have h3 := stab_le_normalizer_Vv hN (x' • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H)
    rw [Vv_smul_γ₀ hN] at h3
    exact h2.trans h3
  have hdαγ₁ : dist α (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by
    have hdαγ : dist α γ = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr hαn
    have h1 := CosetGeom.dist_triangle hyp.gen α γ (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
    have h2 := hγ.geodesic
    rw [CosetGeom.dist_comm γ] at h1
    by_contra hne
    apply hEγ₁
    obtain ⟨-, hVb, -⟩ := critDist_spec hyp hV1
    have hEb : conjSub y V ≤ ballStab (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V) α := by
      rw [hαy, ballStab_smul]
      exact conjSub_mono _ hVb
    refine hEb.trans fun x hx => mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ ?_
    have h3 := CosetGeom.dist_triangle hyp.gen α (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) δ
    omega
  have hyα : ((g * k)⁻¹ • α) = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hαy, inv_smul_smul]
  have hyγ : ((g * k)⁻¹ • γ) ∈ nbrs (γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj ((g * k)⁻¹)).mpr hαn.symm
    rwa [hyα] at this
  obtain ⟨z', hz', hz'γ⟩ := stab_transitive_on_nbrs (γ := γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) hyγ
    (show γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁)
  have hz'γ₀ : z' • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H :=
    smul_eq_of_mem_stab hz'
  set w : ↥(L ⊔ T ⊔ H) := z' * (g * k)⁻¹ with hw
  have hwα : w • α = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hw, mul_smul, hyα, hz'γ₀]
  have hwγ : w • γ = γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hw, mul_smul, hz'γ]
  have hwE : conjSub (w : G) (conjSub y V) = V := by
    have := Vv_smul hN w α
    rw [hwα, Vv_γ₀ hN, hE] at this
    exact this.symm
  have hcrit : IsCriticalVertex (L ⊔ T ⊔ H) (L ⊔ T) H V (w • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) :=
    { dist_eq := by rw [← hwα, CosetGeom.dist_smul]; exact hdαγ₁
      not_le := by
        intro hle
        apply hEγ₁
        rw [ballStab_smul, ← hwE] at hle
        have := conjSub_mono (w : G)⁻¹ hle
        rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
      geodesic := by
        have := CosetGeom.dist_smul w γ (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
        rw [hwγ] at this
        rw [this, CosetGeom.dist_comm]
        exact hγ.geodesic }
  have hW2 : (Vv V (w • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (Vv V (w • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)) = 2 := by
    have e1 : Vv V (w • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = conjSub (w : G) (conjClosure V H) := by
      rw [Vv_smul hN, hAγ₁]
    have e2 : Subgroup.normalizer (V : Set G) =
        conjSub (w : G) (Subgroup.normalizer (conjSub y V : Set G)) := by
      conv_lhs => rw [← hwE]
      exact CFSG.Quasithin.conjSub_normalizer _ _
    rw [e1, e2, ← conjSub_inf, relIndex_conjSub_ch62]
    exact hα2
  exact h.false_of_wframe628 h331 h432 h615 h6110 hE612 h627 hF hyp hSQTK hUM hc
    (hL G T M L V h hVO H hHs hHZ) hb3 hodd hVO hz1 hZz (hZV hzZ) hcrit hW2

theorem stmt6_2_8_and_10_of_res (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612)
    (hRes : Res627FF) (hF : F713Two) (hL : Res628Lie) : Stmt6_2_8 ∧ Stmt6_2_10 := by
  have h628 := stmt6_2_8_of h331 h432 h512 h614 h615 h6110 hE612
    (stmt6_2_7_of_res h331 h432 h615 h6110 hE612 hRes) hF hL
  exact ⟨h628, stmt6_2_10_of h331 h432 h512 h614 h615 h628⟩

end CFSG.Quasithin.H13
