module

public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

namespace F8

abbrev Geom (T L H : Subgroup G) : Type _ := CosetGeom ((L ⊔ T) ⊔ H) (L ⊔ T) H

noncomputable abbrev b (T V L H : Subgroup G) : ℕ :=
  critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V

abbrev γ₀ (T L H : Subgroup G) : Geom T L H := CosetGeom.γ₀ ((L ⊔ T) ⊔ H) (L ⊔ T) H

abbrev γ₁ (T L H : Subgroup G) : Geom T L H := CosetGeom.γ₁ ((L ⊔ T) ⊔ H) (L ⊔ T) H

end F8

structure F8Setup (T V L H : Subgroup G) (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)) :
    Prop where
  critical : IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ
  nbr : γ ∈ nbrs γ'
  geodesic : CosetGeom.dist (F8.γ₁ T L H) γ' + 2 = F8.b T V L H
  edge₀ : g • F8.γ₀ T L H = γ'
  edge₁ : g • F8.γ₁ T L H = γ

namespace F8

variable {T V L V₁ H : Subgroup G}

theorem V_ne_bot (h : HypF81 T V L V₁ H) : V ≠ ⊥ :=
  fun hV => h.V₁_ne_bot (le_bot_iff.mp (hV ▸ h.V₁_le_V))

theorem le_normalizer_of_le {V V₁ : Subgroup G} (hV : IsElemAbelian 2 V) (h : V₁ ≤ V) :
    V ≤ Subgroup.normalizer (V₁ : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ y ∈ V₁, v * y * v⁻¹ = y := fun y hy => by
    have := isElemAbelian_comm hV hv (h hy)
    rw [this]; group
  constructor
  · intro hy; rw [key y hy]; exact hy
  · intro hy
    have hm := isElemAbelian_comm hV hv (h hy)
    have e : v * y * v⁻¹ = y := by
      calc v * y * v⁻¹ = v⁻¹ * (v * (v * y * v⁻¹)) := by group
        _ = v⁻¹ * ((v * y * v⁻¹) * v) := by rw [hm]
        _ = y := by group
    rw [e] at hy
    exact hy

theorem conjClosure_eq_Vv_γ₁ [Finite G] (h : HypF81 T V L V₁ H) :
    conjClosure V H = Vv V (γ₁ T L H) :=
  (Vv_γ₁ h.amalgamHypV.le₂ h.amalgamHypV.normalizes).symm

@[expose] def Uγ (V H : Subgroup G) (g : G) : Subgroup G := conjSub g (conjClosure V H)

@[expose] def A₁ (V₁ : Subgroup G) (g : G) : Subgroup G := conjSub g V₁

@[expose] def DH (V V₁ H : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod (A₁ V₁ g) (conjClosure V H) (Uγ V H g)

@[expose] def Dγ (V V₁ H : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod V₁ (Uγ V H g) (conjClosure V H)

section Fin

variable [Finite G]

theorem three_le_b_and_odd (h : HypF81 T V L V₁ H) : 3 ≤ b T V L H ∧ Odd (b T V L H) := by
  have hyp := h.amalgamHypV
  have hV := V_ne_bot h
  change 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V ∧ Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V)
  have hb2 : 2 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V :=
    two_le_critDist_of_le_pCoreOf hyp hV h.V_le_pCoreOf_and_commutator_le.1
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
    have hγlt : γ' ∈ ballLT (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) (γ₀ T L H) := by
      show CosetGeom.dist (γ₀ T L H) γ' < _
      have h1 := dist_triangle hyp.gen (γ₀ T L H) (γ₁ T L H) γ'
      have h2 : CosetGeom.dist (γ₀ T L H) (γ₁ T L H) = 1 := dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
      have h3 : CosetGeom.dist (γ₁ T L H) γ' + 2 = critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := hd'
      omega
    have hVP := (V_le_pCoreOf_of_dist_lt hyp hV hγlt hγ'nb).2
    have hstab : stab γ' ⊓ stab γ = conjSub (g : G) (L₁Of L V₁ ⊔ T) := by
      rw [← hg1, ← hg0, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, ← conjSub_inf,
        inf_comm, h.LT_inf_H]
    rw [hstab] at hVP
    have hirr : ∀ U : Subgroup G, conjSub (g : G) V₁ ≤ U → U ≤ conjSub (g : G) V →
        conjSub (g : G) (L₁Of L V₁ ⊔ T) ≤ Subgroup.normalizer (U : Set G) →
        U = conjSub (g : G) V₁ ∨ U = conjSub (g : G) V := by
      intro U h1 h2 h3
      have h1' : V₁ ≤ conjSub (g : G)⁻¹ U := (conjSub_le_iff _).mp h1
      have h2' : conjSub (g : G)⁻¹ U ≤ V := (le_conjSub_iff _).mp h2
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
    have hWN : conjSub (g : G) V ≤ Subgroup.normalizer (conjSub (g : G) V₁ : Set G) :=
      conjSub_le_normalizer (le_normalizer_of_le h.elemAbelian h.V₁_le_V)
    have hcomm := commutator_le_of_irreducible (X := conjSub (g : G) (L₁Of L V₁ ⊔ T))
      (W := conjSub (g : G) V) (W₁ := conjSub (g : G) V₁)
      (P := pCoreOf 2 (conjSub (g : G) (L₁Of L V₁ ⊔ T))) (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _)
      (conjSub_le_normalizer h.L₁T_normalizes_V)
      (conjSub_le_normalizer (h.L₁T_le_H.trans h.H_normalizes_V₁))
      (le_normalizer_pCoreOf 2 _) (conjSub_mono _ h.V₁_le_V) (isPGroup_conjSub h.isPGroup_V) hWN
      hirr
    have hVW : ⁅V, conjSub (g : G) V⁆ ≤ conjSub (g : G) V₁ :=
      Subgroup.commutator_le.mpr fun v hv w hw => hcomm v (hVP hv) w hw
    obtain ⟨hne, hcl, -, -⟩ := commutator_V_Vv_of_even hyp hV hev (γ := γ) hγ.dist_eq hγ.not_le
    rw [← hg0, Vv_smul_γ₀ hyp.normalizes] at hne hcl
    have hne0 : V ⊓ conjSub (g : G) V₁ ≠ ⊥ := by
      intro hbot
      apply hne
      exact le_bot_iff.mp ((le_inf (hcl.trans inf_le_left) hVW).trans hbot.le)
    have hne1 : V₁ ⊓ conjSub (g : G)⁻¹ V ≠ ⊥ := by
      intro hbot
      apply hne0
      have := congrArg (conjSub (g : G)) hbot
      rw [conjSub_inf, conjSub_inv_conjSub, conjSub_bot, inf_comm] at this
      exact this
    have h0 := h.weak_a (g : G) hne1
    have h0' := congrArg (conjSub (g : G)) h0
    rw [← conjSub_commutator, conjSub_bot, conjSub_inv_conjSub] at h0'
    apply hne
    rw [Subgroup.commutator_comm]
    exact h0'
  refine ⟨?_, hodd⟩
  obtain ⟨k, hk⟩ := hodd
  omega

theorem isElemAbelian_conjClosure (h : HypF81 T V L V₁ H) : IsElemAbelian 2 (conjClosure V H) := by
  have hb : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := (three_le_b_and_odd h).1
  rw [conjClosure_eq_Vv_γ₁ h]
  exact isElemAbelian_Vv_γ₁ h.amalgamHypV (V_ne_bot h) (by omega)

theorem exists_F8Setup (h : HypF81 T V L V₁ H) :
    ∃ (γ γ' : Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g := by
  have hyp := h.amalgamHypV
  have hV := V_ne_bot h
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := (three_le_b_and_odd h).1
  have hodd : Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) := (three_le_b_and_odd h).2
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

section Setup

variable {γ γ' : Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem Uγ_eq_Vv (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    Uγ V H (g : G) = Vv V γ := by
  rw [Uγ, conjClosure_eq_Vv_γ₁ h, ← Vv_smul h.amalgamHypV.normalizes g (γ₁ T L H), s.edge₁]

theorem F87_1 (h : HypF81 T V L V₁ H) :
    stab (γ₀ T L H) ⊓ stab (γ₁ T L H) = L₁Of L V₁ ⊔ T := by
  rw [stab_γ₀ h.amalgamHypV.le₁, stab_γ₁ h.amalgamHypV.le₂]
  exact h.LT_inf_H

theorem F87_2 (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    conjClosure V H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) ∧
      ∀ γ₂ ∈ nbrs (γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = b T V L H →
        Uγ V H (g : G) ≤ pCoreOf 2 (stab (γ₁ T L H) ⊓ stab γ₂) := by
  refine ⟨?_, fun γ₂ hγ₂ hd => ?_⟩
  · rw [conjClosure_eq_Vv_γ₁ h]
    exact Vv_γ₁_le_pCoreOf_stab_inf h.amalgamHypV (V_ne_bot h) s.nbr s.geodesic
  · rw [Uγ_eq_Vv h s]
    exact Vv_le_pCoreOf_stab_inf h.amalgamHypV (V_ne_bot h) hγ₂ hd

theorem F87_3 (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    ⁅conjClosure V H, Uγ V H (g : G)⁆ ≤ conjClosure V H ⊓ Uγ V H (g : G) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := (three_le_b_and_odd h).1
  rw [Uγ_eq_Vv h s, conjClosure_eq_Vv_γ₁ h]
  exact commutator_Vv_γ₁_Vv_le h.amalgamHypV (V_ne_bot h) s.critical.geodesic (by omega)

theorem F87_4 (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    Uγ V H (g : G) ≤ Subgroup.normalizer (conjClosure V H : Set G) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := (three_le_b_and_odd h).1
  obtain ⟨-, ⟨γ₂, hγ₂, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  refine ((F87_2 h s).2 γ₂ hγ₂ hd).trans ((pCoreOf_le 2 _).trans (inf_le_left.trans ?_))
  rw [stab_γ₁ h.amalgamHypV.le₂]
  exact le_normalizer_conjClosure V H

theorem F87_5a (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    ¬ ⁅Uγ V H (g : G), V⁆ ≤ A₁ V₁ (g : G) := by
  intro hle
  have hyp := h.amalgamHypV
  have hV := V_ne_bot h
  have h3 := congrArg (conjSub (g : G)) h.F82_3
  rw [← pCoreOf_conjSub, conjSub_centralizerMod] at h3
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hyp.le₂]
  have hVstab : V ≤ stab γ := V_le_stab_of_dist_le hyp hV s.critical.dist_eq.le
  have hVN : V ≤ Subgroup.normalizer (A₁ V₁ (g : G) : Set G) := by
    rw [hstab] at hVstab
    exact hVstab.trans (conjSub_le_normalizer h.H_normalizes_V₁)
  have hVC : V ≤ centralizerMod (A₁ V₁ (g : G)) (stab γ) (Uγ V H (g : G)) := by
    refine fun v hv => ⟨hVstab hv, hVN hv, fun u hu => ?_⟩
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ A₁ V₁ (g : G) := hle (Subgroup.commutator_mem_commutator hu hv)
    have := (A₁ V₁ (g : G)).inv_mem h1
    have e : (u * v * u⁻¹ * v⁻¹)⁻¹ = v * u * v⁻¹ * u⁻¹ := by group
    rwa [e] at this
  have h4 : pCoreOf 2 (stab γ) =
      centralizerMod (A₁ V₁ (g : G)) (stab γ) (Uγ V H (g : G)) := by
    rw [hstab]; exact h3
  exact s.critical.not_le ((h4 ▸ hVC).trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp γ))

theorem F87_5b (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    V₁ ⊓ A₁ V₁ (g : G) = ⊥ := by
  by_contra hne
  apply F87_5a h s
  have hN := h.amalgamHypV.normalizes
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
    have hA : A₁ V₁ (g : G) ≤ conjSub (g' : G) V := by
      rw [hg'e, conjSub_mul]
      exact conjSub_mono _ hV₁x
    have hne' : V₁ ⊓ conjSub (g' : G) V ≠ ⊥ := fun hbot =>
      hne (le_bot_iff.mp ((inf_le_inf_left V₁ hA).trans hbot.le))
    have hcomm : ⁅V, conjSub (g' : G) V⁆ = ⊥ := by
      have := h.weak_a (g' : G)⁻¹ (by rwa [inv_inv])
      rwa [inv_inv] at this
    have hVc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hVc hv)) w hw).symm
  rw [Uγ_eq_Vv h s, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent]
  exact bot_le

omit [Finite G] in
theorem F87_6 (V V₁ H : Subgroup G) (g : G) :
    ⁅Uγ V H g, DH V V₁ H g⁆ ≤ A₁ V₁ g ∧ ⁅conjClosure V H, Dγ V V₁ H g⁆ ≤ V₁ := by
  have key : ∀ {W X U : Subgroup G} {d u : G}, d ∈ centralizerMod W X U → u ∈ U →
      u * d * u⁻¹ * d⁻¹ ∈ W := by
    intro W X U d u hd hu
    have := W.inv_mem ((mem_centralizerMod.mp hd).2.2 u hu)
    have e : (d * u * d⁻¹ * u⁻¹)⁻¹ = u * d * u⁻¹ * d⁻¹ := by group
    rwa [e] at this
  exact ⟨Subgroup.commutator_le.mpr fun u hu d hd => key hd hu,
    Subgroup.commutator_le.mpr fun u hu d hd => key hd hu⟩

theorem F87_7 (h : HypF81 T V L V₁ H) (s : F8Setup T V L H γ γ' g) :
    ⁅DH V V₁ H (g : G), Dγ V V₁ H (g : G)⁆ = ⊥ := by
  obtain ⟨h1, h2⟩ := F87_6 V V₁ H (g : G)
  have hDH : DH V V₁ H (g : G) ≤ conjClosure V H := centralizerMod_le_left _ _ _
  have hDγ : Dγ V V₁ H (g : G) ≤ Uγ V H (g : G) := centralizerMod_le_left _ _ _
  have a1 : ⁅DH V V₁ H (g : G), Dγ V V₁ H (g : G)⁆ ≤ A₁ V₁ (g : G) :=
    (Subgroup.commutator_mono le_rfl hDγ).trans (by rw [Subgroup.commutator_comm]; exact h1)
  have a2 : ⁅DH V V₁ H (g : G), Dγ V V₁ H (g : G)⁆ ≤ V₁ :=
    (Subgroup.commutator_mono hDH le_rfl).trans h2
  exact le_bot_iff.mp ((le_inf a2 a1).trans (F87_5b h s).le)

end Setup

end Fin

end F8

end CFSG.Quasithin
