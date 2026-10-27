module

public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.F8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

namespace F9

@[expose] def EH (V Vp V₁ H : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod (F8.A₁ V₁ g) (conjClosure V H) (F8.Uγ Vp H g)

@[expose] def Eγ (V Vp V₁ H : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod V₁ (F8.Uγ V H g) (conjClosure Vp H)

end F9

theorem conjSub_zpowers (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem conjClosure_eq_Vv_γ₁ (h : HypF91 T V L V₁ Vp H) :
    conjClosure V H = Vv V (F8.γ₁ T L H) :=
  (Vv_γ₁ h.amalgamHypV.le₂ h.amalgamHypV.normalizes).symm

end HypF91

namespace HypF98

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem V_ne_bot (h : HypF98 T V L V₁ Vp H) : V ≠ ⊥ :=
  fun hV => h.V₁_ne_bot (le_bot_iff.mp (hV ▸ h.V₁_le_V))

theorem V_le_pCoreOf (h : HypF98 T V L V₁ Vp H) : V ≤ pCoreOf 2 H := by
  refine h.le_pCoreOf_iff_le_centralizer.mpr fun v hv => ⟨h.V_le_H hv, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  exact isElemAbelian_comm h.F911_2
    (conjClosure_le (fun _ hk _ hz => mem_conjClosure hk (h.Vp_le_V hz)) hu)
    (le_conjClosure V H hv)

theorem three_le_b_and_odd (h : HypF98 T V L V₁ Vp H) :
    3 ≤ F8.b T V L H ∧ Odd (F8.b T V L H) := by
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  change 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V ∧ Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V)
  have hb2 : 2 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V :=
    two_le_critDist_of_le_pCoreOf hyp hV h.V_le_pCoreOf
  have hodd : Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) := by
    by_contra hnodd
    have hev := Nat.not_odd_iff_even.mp hnodd
    obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
    have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ.dist_eq]; exact hev)
    obtain ⟨⟨γ', hγ'nb, hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
    have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ γ' := SimpleGraph.Adj.symm hγ'nb
    obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
    swap
    · exfalso
      have := congrArg vtype hg1
      rw [vtype_smul, vtype_γ₁, hvt] at this
      exact absurd this (by decide)
    have hγlt : γ' ∈ ballLT (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) (F8.γ₀ T L H) := by
      show CosetGeom.dist (F8.γ₀ T L H) γ' < _
      have h1 := dist_triangle hyp.gen (F8.γ₀ T L H) (F8.γ₁ T L H) γ'
      have h2 : CosetGeom.dist (F8.γ₀ T L H) (F8.γ₁ T L H) = 1 :=
        dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
      have h3 : CosetGeom.dist (F8.γ₁ T L H) γ' + 2 = critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := hd'
      omega
    have hVP := (V_le_pCoreOf_of_dist_lt hyp hV hγlt hγ'nb).2
    have hstab : stab γ' ⊓ stab γ = conjSub (g : G) (L₁Of L V₁ ⊔ T) := by
      rw [← hg1, ← hg0, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, ← conjSub_inf,
        inf_comm, h.LT_inf_H]
    rw [hstab] at hVP
    have hirr : ∀ U : Subgroup G, conjSub (g : G) V₁ ≤ U → U ≤ conjSub (g : G) Vp →
        conjSub (g : G) (L₁Of L V₁ ⊔ T) ≤ Subgroup.normalizer (U : Set G) →
        U = conjSub (g : G) V₁ ∨ U = conjSub (g : G) Vp := by
      intro U h1 h2 h3
      have h1' : V₁ ≤ conjSub (g : G)⁻¹ U := (conjSub_le_iff _).mp h1
      have h2' : conjSub (g : G)⁻¹ U ≤ Vp := (le_conjSub_iff _).mp h2
      have h3' : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (conjSub (g : G)⁻¹ U : Set G) := by
        have := conjSub_le_normalizer (g := (g : G)⁻¹) h3
        rwa [conjSub_conjSub_inv] at this
      rcases h.irred _ h1' h2' h3' with e | e
      · left
        have := congrArg (conjSub (g : G)) e
        rwa [conjSub_inv_conjSub] at this
      · right
        have := congrArg (conjSub (g : G)) e
        rwa [conjSub_inv_conjSub] at this
    have hWN : conjSub (g : G) Vp ≤ Subgroup.normalizer (conjSub (g : G) V₁ : Set G) :=
      conjSub_le_normalizer (HypF91.le_normalizer_of_isElemAbelian_le h.elemAbelian_Vp h.V₁_le_Vp)
    have hcomm := commutator_le_of_irreducible (X := conjSub (g : G) (L₁Of L V₁ ⊔ T))
      (W := conjSub (g : G) Vp) (W₁ := conjSub (g : G) V₁)
      (P := pCoreOf 2 (conjSub (g : G) (L₁Of L V₁ ⊔ T))) (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _)
      (conjSub_le_normalizer h.L₁T_normalizes_Vp)
      (conjSub_le_normalizer (h.L₁T_le_H.trans h.H_normalizes_V₁))
      (le_normalizer_pCoreOf 2 _) (conjSub_mono _ h.V₁_le_Vp) (isPGroup_conjSub h.isPGroup_Vp)
      hWN hirr
    have hVW : ⁅V, conjSub (g : G) Vp⁆ ≤ conjSub (g : G) V₁ :=
      Subgroup.commutator_le.mpr fun v hv w hw => hcomm v (hVP hv) w hw
    obtain ⟨hne, hcl, -, -⟩ := commutator_V_Vv_of_even hyp hV hev (γ := γ) hγ.dist_eq hγ.not_le
    rw [← hg0, Vv_smul_γ₀ hyp.normalizes] at hne hcl
    have hcard : Nat.card (conjSub (g : G) V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
    have hclaim : conjSub (g : G) V₁ ≤ V := by
      have hWpV : conjSub (g : G) Vp ≤ conjSub (g : G) V := conjSub_mono _ h.Vp_le_V
      rcases eq_bot_or_eq_of_card_eq_two hcard hVW with hbot | heq
      ·
        have hVC : V ≤ Subgroup.centralizer (conjSub (g : G) Vp : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
        have hVH : V ≤ conjSub (g : G) H :=
          (hVP.trans (pCoreOf_le 2 _)).trans (conjSub_mono _ h.L₁T_le_H)
        rcases h.case_g with hi | hii
        ·
          have hconj : ⁅conjSub (g : G) V, conjSub (g : G) H ⊓
              Subgroup.centralizer (conjSub (g : G) Vp : Set G)⁆ ≤ conjSub (g : G) V₁ := by
            have := conjSub_mono (g : G) hi
            rwa [← conjSub_commutator, conjSub_inf, ← conjSub_centralizer] at this
          have h1 : ⁅conjSub (g : G) V, V⁆ ≤ conjSub (g : G) V₁ :=
            (Subgroup.commutator_mono le_rfl (le_inf hVH hVC)).trans hconj
          have h2 : ⁅V, conjSub (g : G) V⁆ ≤ conjSub (g : G) V₁ := by
            rw [Subgroup.commutator_comm]; exact h1
          rcases eq_bot_or_eq_of_card_eq_two hcard h2 with hb | he
          · exact absurd hb hne
          · calc conjSub (g : G) V₁ = ⁅V, conjSub (g : G) V⁆ := he.symm
              _ ≤ V ⊓ conjSub (g : G) V := hcl
              _ ≤ V := inf_le_left
        ·
          exfalso
          have hx' : ∃ x' ∈ V, ⁅conjSub (g : G) V, Subgroup.zpowers x'⁆ ≠ ⊥ := by
            by_contra hcon
            push Not at hcon
            apply hne
            rw [Subgroup.commutator_comm]
            refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun w hw => ?_
            refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
            have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon x hx) hw
            exact Subgroup.mem_centralizer_iff.mp this x (Subgroup.mem_zpowers x)
          obtain ⟨x', hx'V, hx'ne⟩ := hx'
          obtain ⟨x, hx⟩ : ∃ x, x = (g : G)⁻¹ * x' * (g : G) := ⟨_, rfl⟩
          have hxx' : (g : G) * x * (g : G)⁻¹ = x' := by rw [hx]; group
          have hxH : x ∈ H := by
            have := hVH hx'V
            rw [mem_conjSub] at this
            rwa [hx]
          have hxC : x ∈ Subgroup.centralizer (Vp : Set G) := by
            refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
            have hc := Subgroup.mem_centralizer_iff.mp (hVC hx'V) _ (mul_mem_conjSub (g := (g : G)) hz)
            calc z * x = (g : G)⁻¹ * (((g : G) * z * (g : G)⁻¹) * x') * (g : G) := by rw [hx]; group
              _ = (g : G)⁻¹ * (x' * ((g : G) * z * (g : G)⁻¹)) * (g : G) := by rw [hc]
              _ = x * z := by rw [hx]; group
          have hcomm2 : conjSub (g : G) ⁅V, Subgroup.zpowers x⁆ =
              ⁅conjSub (g : G) V, Subgroup.zpowers x'⁆ := by
            rw [← conjSub_commutator, conjSub_zpowers, hxx']
          have hxne : ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ := by
            intro hb
            apply hx'ne
            rw [← hcomm2, hb, conjSub_bot]
          have hle' : ⁅conjSub (g : G) V, Subgroup.zpowers x'⁆ ≤ V := by
            calc ⁅conjSub (g : G) V, Subgroup.zpowers x'⁆ ≤ ⁅conjSub (g : G) V, V⁆ :=
                  Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hx'V)
              _ = ⁅V, conjSub (g : G) V⁆ := Subgroup.commutator_comm _ _
              _ ≤ V ⊓ conjSub (g : G) V := hcl
              _ ≤ V := inf_le_left
          have hVN : V ≤ Subgroup.normalizer
              ((⁅conjSub (g : G) V, Subgroup.zpowers x'⁆ : Subgroup G) : Set G) :=
            HypF91.le_normalizer_of_isElemAbelian_le h.elemAbelian hle'
          have hnorm : conjSub (g : G)⁻¹ V ≤ Subgroup.normalizer
              ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
            have := conjSub_le_normalizer (g := (g : G)⁻¹) hVN
            rwa [← hcomm2, conjSub_conjSub_inv] at this
          have hcent := hii x ⟨hxH, hxC⟩ hxne (g : G) hnorm
          have := conjSub_mono (g : G) hcent
          rw [conjSub_inv_conjSub, ← conjSub_centralizer] at this
          exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr this)
      · calc conjSub (g : G) V₁ = ⁅V, conjSub (g : G) Vp⁆ := heq.symm
          _ ≤ ⁅V, conjSub (g : G) V⁆ := Subgroup.commutator_mono le_rfl hWpV
          _ ≤ V ⊓ conjSub (g : G) V := hcl
          _ ≤ V := inf_le_left
    have hV₁g : V₁ ≤ conjSub (g : G)⁻¹ V := by
      rw [le_conjSub_iff, inv_inv]; exact hclaim
    have h0 := h.weak_f (g : G) hV₁g
    have h0' := congrArg (conjSub (g : G)) h0
    rw [← conjSub_commutator, conjSub_bot, conjSub_inv_conjSub] at h0'
    apply hne
    rw [Subgroup.commutator_comm]
    exact h0'
  refine ⟨?_, hodd⟩
  obtain ⟨k, hk⟩ := hodd
  omega

theorem exists_F8Setup (h : HypF98 T V L V₁ Vp H) :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g := by
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  have hodd : Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) := h.three_le_b_and_odd.2
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  obtain ⟨⟨γ', hγ'nb, hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ γ' := SimpleGraph.Adj.symm hγ'nb
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)
  · exact ⟨γ, γ', g, ⟨hγ, hγ'nb, hd', hg0, hg1⟩⟩

end HypF98

section Setup

variable {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

omit [Finite G] in
theorem commutator_centralizerMod_le (W X U : Subgroup G) : ⁅U, centralizerMod W X U⁆ ≤ W := by
  refine Subgroup.commutator_le.mpr fun u hu d hd => ?_
  have := W.inv_mem ((mem_centralizerMod.mp hd).2.2 u hu)
  have e : (d * u * d⁻¹ * u⁻¹)⁻¹ = u * d * u⁻¹ * d⁻¹ := by group
  rwa [e] at this

namespace HypF98

theorem Vγ_eq_Vv (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ V H (g : G) = Vv V γ := by
  rw [F8.Uγ, h.toHypF91.conjClosure_eq_Vv_γ₁, ←
    Vv_smul h.amalgamHypV.normalizes g (F8.γ₁ T L H), s.edge₁]

omit [Finite G] in
theorem Uγ_le_Vγ (h : HypF98 T V L V₁ Vp H) :
    F8.Uγ Vp H (g : G) ≤ F8.Uγ V H (g : G) :=
  conjSub_mono _ (conjClosure_le fun _ hk _ hz => mem_conjClosure hk (h.Vp_le_V hz))

theorem F913_1 (h : HypF98 T V L V₁ Vp H) :
    stab (F8.γ₀ T L H) ⊓ stab (F8.γ₁ T L H) = L₁Of L V₁ ⊔ T := by
  rw [stab_γ₀ h.amalgamHypV.le₁, stab_γ₁ h.amalgamHypV.le₂]
  exact h.LT_inf_H

theorem F913_2 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    conjClosure V H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) ∧
      ∀ γ₂ ∈ nbrs (F8.γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = F8.b T V L H →
        F8.Uγ V H (g : G) ≤ pCoreOf 2 (stab (F8.γ₁ T L H) ⊓ stab γ₂) := by
  refine ⟨?_, fun γ₂ hγ₂ hd => ?_⟩
  · rw [h.toHypF91.conjClosure_eq_Vv_γ₁]
    exact Vv_γ₁_le_pCoreOf_stab_inf h.amalgamHypV h.V_ne_bot s.nbr s.geodesic
  · rw [h.Vγ_eq_Vv s]
    exact Vv_le_pCoreOf_stab_inf h.amalgamHypV h.V_ne_bot hγ₂ hd

theorem stab_le_normalizer_Uγ (s : F8Setup T V L H γ γ' g) (h : HypF98 T V L V₁ Vp H)
    (Y : Subgroup G) : stab γ ≤ Subgroup.normalizer (F8.Uγ Y H (g : G) : Set G) := by
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ h.amalgamHypV.le₂]
  rw [hstab]
  exact conjSub_le_normalizer (le_normalizer_conjClosure Y H)

theorem F913_3 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) {X Y : Subgroup G}
    (hX : X = Vp ∨ X = V) (hY : Y = Vp ∨ Y = V) :
    ⁅conjClosure X H, F8.Uγ Y H (g : G)⁆ ≤ conjClosure X H ⊓ F8.Uγ Y H (g : G) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  have hXV : conjClosure X H ≤ conjClosure V H := by
    rcases hX with rfl | rfl
    · exact conjClosure_le fun _ hk _ hz => mem_conjClosure hk (h.Vp_le_V hz)
    · exact le_rfl
  have hYV : F8.Uγ Y H (g : G) ≤ F8.Uγ V H (g : G) := by
    rcases hY with rfl | rfl
    · exact h.Uγ_le_Vγ
    · exact le_rfl
  obtain ⟨hVH, hγ₂⟩ := h.F913_2 s
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have h1 : conjClosure X H ≤ stab γ :=
    hXV.trans (hVH.trans ((pCoreOf_le 2 _).trans inf_le_right))
  have h2 : F8.Uγ Y H (g : G) ≤ H := by
    have := hYV.trans (hγ₂ γ₂ hγ₂nb hd)
    rw [stab_γ₁ h.amalgamHypV.le₂] at this
    exact this.trans ((pCoreOf_le 2 _).trans inf_le_left)
  refine commutator_le_inf_of_normalizes ?_ ?_
  · exact h1.trans (stab_le_normalizer_Uγ s h Y)
  · exact h2.trans (le_normalizer_conjClosure X H)

theorem F913_4 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ V H (g : G) ≤ Subgroup.normalizer (conjClosure V H : Set G) ∧
      F8.Uγ V H (g : G) ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have h2 : F8.Uγ V H (g : G) ≤ H := by
    have := (h.F913_2 s).2 γ₂ hγ₂nb hd
    rw [stab_γ₁ h.amalgamHypV.le₂] at this
    exact this.trans ((pCoreOf_le 2 _).trans inf_le_left)
  exact ⟨h2.trans (le_normalizer_conjClosure V H), h2.trans (le_normalizer_conjClosure Vp H)⟩

theorem F913_5a (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ¬ ⁅F8.Uγ Vp H (g : G), V⁆ ≤ F8.A₁ V₁ (g : G) := by
  intro hle
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  have h3 := congrArg (conjSub (g : G)) h.pCoreOf_eq_centralizerMod
  rw [← pCoreOf_conjSub, conjSub_centralizerMod] at h3
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hyp.le₂]
  have hVstab : V ≤ stab γ := V_le_stab_of_dist_le hyp hV s.critical.dist_eq.le
  have hVN : V ≤ Subgroup.normalizer (F8.A₁ V₁ (g : G) : Set G) := by
    rw [hstab] at hVstab
    exact hVstab.trans (conjSub_le_normalizer h.H_normalizes_V₁)
  have hVC : V ≤ centralizerMod (F8.A₁ V₁ (g : G)) (stab γ) (F8.Uγ Vp H (g : G)) := by
    refine fun v hv => ⟨hVstab hv, hVN hv, fun u hu => ?_⟩
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ F8.A₁ V₁ (g : G) :=
      hle (Subgroup.commutator_mem_commutator hu hv)
    have := (F8.A₁ V₁ (g : G)).inv_mem h1
    have e : (u * v * u⁻¹ * v⁻¹)⁻¹ = v * u * v⁻¹ * u⁻¹ := by group
    rwa [e] at this
  have h4 : pCoreOf 2 (stab γ) =
      centralizerMod (F8.A₁ V₁ (g : G)) (stab γ) (F8.Uγ Vp H (g : G)) := by
    rw [hstab]; exact h3
  exact s.critical.not_le ((h4 ▸ hVC).trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp γ))

theorem F913_5b (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    V₁ ⊓ F8.A₁ V₁ (g : G) = ⊥ := by
  by_contra hne
  apply F913_5a h s
  have hN := h.amalgamHypV.normalizes
  have hV₁A : V₁ ≤ F8.A₁ V₁ (g : G) := le_of_card_eq_two_of_inf_ne_bot h.card_V₁ hne
  have hcent : Vv V γ ≤ Subgroup.centralizer (V : Set G) := by
    rw [← s.edge₁, smul_γ₁, Vv_inr]
    refine iSup₂_le fun x hx => ?_
    obtain ⟨g', hg'1, hg'2⟩ := adj_inr_inl.mp hx
    rw [← hg'1, Vv0_mk hN]
    obtain ⟨x₁, hx₁, hg'e⟩ : ∃ x₁ ∈ H, (g' : G) = (g : G) * x₁ := by
      refine ⟨(g : G)⁻¹ * g', ?_, by group⟩
      have h1 := H.inv_mem (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hg'2))
      simpa using h1
    have hV₁x : V₁ ≤ conjSub x₁ V := by
      have := conjSub_mono x₁ h.V₁_le_V
      rwa [F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hx₁)] at this
    have hA : F8.A₁ V₁ (g : G) ≤ conjSub (g' : G) V := by
      rw [hg'e, conjSub_mul]
      exact conjSub_mono _ hV₁x
    have hV₁g' : V₁ ≤ conjSub (g' : G) V := hV₁A.trans hA
    have hcomm : ⁅V, conjSub (g' : G) V⁆ = ⊥ := by
      have := h.weak_f (g' : G)⁻¹ (by rwa [inv_inv])
      rwa [inv_inv] at this
    have hVc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro w hw
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hVc hv)) w hw).symm
  have h1 : ⁅F8.Uγ Vp H (g : G), V⁆ ≤ ⁅Vv V γ, V⁆ :=
    Subgroup.commutator_mono (by rw [← h.Vγ_eq_Vv s]; exact h.Uγ_le_Vγ) le_rfl
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent] at h1
  exact h1.trans bot_le

omit [Finite G] in
theorem F913_6 (V Vp V₁ H : Subgroup G) (g : G) :
    ⁅F8.Uγ Vp H g, F9.EH V Vp V₁ H g⁆ ≤ F8.A₁ V₁ g ∧
      ⁅conjClosure Vp H, F9.Eγ V Vp V₁ H g⁆ ≤ V₁ :=
  ⟨commutator_centralizerMod_le _ _ _, commutator_centralizerMod_le _ _ _⟩

theorem F913_7 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ⁅F8.DH Vp V₁ H (g : G), F8.Dγ Vp V₁ H (g : G)⁆ = ⊥ := by
  obtain ⟨h1, h2⟩ := F8.F87_6 Vp V₁ H (g : G)
  have hDH : F8.DH Vp V₁ H (g : G) ≤ conjClosure Vp H := centralizerMod_le_left _ _ _
  have hDγ : F8.Dγ Vp V₁ H (g : G) ≤ F8.Uγ Vp H (g : G) := centralizerMod_le_left _ _ _
  have a1 : ⁅F8.DH Vp V₁ H (g : G), F8.Dγ Vp V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) :=
    (Subgroup.commutator_mono le_rfl hDγ).trans (by rw [Subgroup.commutator_comm]; exact h1)
  have a2 : ⁅F8.DH Vp V₁ H (g : G), F8.Dγ Vp V₁ H (g : G)⁆ ≤ V₁ :=
    (Subgroup.commutator_mono hDH le_rfl).trans h2
  exact le_bot_iff.mp ((le_inf a2 a1).trans (h.F913_5b s).le)

theorem pCoreOf_stab_eq_centralizerMod (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    pCoreOf 2 (stab γ) =
      centralizerMod (F8.A₁ V₁ (g : G)) (stab γ) (F8.Uγ Vp H (g : G)) := by
  have h3 := congrArg (conjSub (g : G)) h.pCoreOf_eq_centralizerMod
  rw [← pCoreOf_conjSub, conjSub_centralizerMod] at h3
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ h.amalgamHypV.le₂]
  rw [hstab]; exact h3

theorem F915_1 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    conjClosure V H ⊓ ballStab 1 γ = F9.EH V Vp V₁ H (g : G) := by
  have hVH := (h.F913_2 s).1
  have hVstab : conjClosure V H ≤ stab γ := hVH.trans ((pCoreOf_le 2 _).trans inf_le_right)
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ h.amalgamHypV.le₂]
  have hN : stab γ ≤ Subgroup.normalizer (F8.A₁ V₁ (g : G) : Set G) := by
    rw [hstab]; exact conjSub_le_normalizer h.H_normalizes_V₁
  have h77 := pCoreOf_stab_eq h.amalgamHypV.toAmalgamHyp (α := γ) (β := γ')
    (mem_nbrs_symm s.nbr)
  have hA : conjClosure V H ⊓ ballStab 1 γ = conjClosure V H ⊓ pCoreOf 2 (stab γ) := by
    rw [h77]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, ?_, hx2⟩
      have := hVH hx1
      rwa [inf_comm] at this
    · rintro ⟨hx1, -, hx2⟩
      exact ⟨hx1, hx2⟩
  rw [hA, h.pCoreOf_stab_eq_centralizerMod s]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.2.1, hx2.2.2⟩
  · rintro ⟨hx1, hx2, hx3⟩
    exact ⟨hx1, hVstab hx1, hx2, hx3⟩

theorem F915_2 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ V H (g : G) ⊓ ballStab 1 (F8.γ₁ T L H) = F9.Eγ V Vp V₁ H (g : G) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have hVγ := (h.F913_2 s).2 γ₂ hγ₂nb hd
  have h2 : F8.Uγ V H (g : G) ≤ H := by
    have := hVγ
    rw [stab_γ₁ h.amalgamHypV.le₂] at this
    exact this.trans ((pCoreOf_le 2 _).trans inf_le_left)
  have h77 := pCoreOf_stab_eq h.amalgamHypV.toAmalgamHyp (α := F8.γ₁ T L H) (β := γ₂) hγ₂nb
  have hA : F8.Uγ V H (g : G) ⊓ ballStab 1 (F8.γ₁ T L H) =
      F8.Uγ V H (g : G) ⊓ pCoreOf 2 H := by
    have h77' : pCoreOf 2 H = pCoreOf 2 (H ⊓ stab γ₂) ⊓ ballStab 1 (F8.γ₁ T L H) := by
      have := h77
      rwa [stab_γ₁ h.amalgamHypV.le₂] at this
    rw [h77']
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, ?_, hx2⟩
      have := hVγ hx1
      rwa [stab_γ₁ h.amalgamHypV.le₂] at this
    · rintro ⟨hx1, -, hx2⟩
      exact ⟨hx1, hx2⟩
  rw [hA, h.pCoreOf_eq_centralizerMod]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.2.1, hx2.2.2⟩
  · rintro ⟨hx1, hx2, hx3⟩
    exact ⟨hx1, h2 hx1, hx2, hx3⟩

end HypF98

end Setup

end Fin

end CFSG.Quasithin
