module

public import CFSG.Quasithin.Recognition.SzVBOdd
public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G] in
theorem Vv_inl_le_Vv_γ₁ {G₀ G₁ G₂ V : Subgroup G} {x : ↥G₀ ⧸ G₁.subgroupOf G₀}
    (hx : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)) :
    Vv V (Sum.inl x : CosetGeom G₀ G₁ G₂) ≤ Vv V (γ₁ G₀ G₁ G₂) := by
  rw [show Vv V (γ₁ G₀ G₁ G₂) = ⨆ (x : ↥G₀ ⧸ G₁.subgroupOf G₀)
    (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)), Vv0 V x from Vv_inr _]
  exact le_iSup₂_of_le (f := fun (x : ↥G₀ ⧸ G₁.subgroupOf G₀)
    (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)) => Vv0 V x) x hx le_rfl

theorem three_le_critDist_of_comm (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hab : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥) :
    3 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hV := F112J2.V_ne_bot h
  have h2 := F112J2.two_le_critDist_of_setting hRO h
  by_contra hlt
  have hb : critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) = 2 := by omega
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hd1 : CosetGeom.dist (γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) γ = 1 := by
    have := hγ.geodesic
    omega
  have hadj := dist_eq_one_iff_adj.mp hd1
  have hev : Even (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) := by
    rw [hb]; exact even_two
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ.dist_eq]; exact hev)
  have hne := (commutator_V_Vv_of_even hyp hV hev hγ.dist_eq hγ.not_le).1
  have hVle : conjClosure Zs L2 ≤ vBeta K1 L2 S Zs :=
    le_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
  have hVγ : Vv (conjClosure Zs L2) γ ≤ vBeta K1 L2 S Zs := by
    rcases γ with x | y
    · have := Vv_inl_le_Vv_γ₁ (V := conjClosure Zs L2) hadj
      rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at this
    · simp [vtype] at hvt
  exact hne (le_bot_iff.mp ((Subgroup.commutator_mono hVle hVγ).trans hab.le))

theorem odd_critDist_false_of_amalgam {G₀ G₁ G₂ T V : Subgroup G} {z : G}
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hb : 3 ≤ critDist G₀ G₁ G₂ V)
    (hodd : Odd (critDist G₀ G₁ G₂ V)) (hK : KleinData G₂ V z) (hB : BenderLocalFacts G₂ T V) :
    False := by
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hvt
  have hN := hyp.normalizes
  have hW : Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := Vv_γ₁ hyp.le₂ hN
  have hVγ : Vv V (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) (conjClosure V G₂) := by
    rw [Vv_smul hN, hW]
  have hstab : stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ := by
    rw [stab_smul, stab_γ₁ hyp.le₂]
  obtain ⟨⟨γ', hγ', hd'⟩, ⟨γ₂, hγ₂, hd₂⟩⟩ :=
    exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hWP : conjClosure V G₂ ≤ conjSub (g : G) G₂ := by
    have := Vv_γ₁_le_pCoreOf_stab_inf hyp hV hγ' hd'
    rw [hW] at this
    rw [← hstab]
    exact this.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
  have hW'P : conjSub (g : G) (conjClosure V G₂) ≤ G₂ := by
    have := Vv_le_pCoreOf_stab_inf hyp hV hγ₂ hd₂
    rw [hVγ] at this
    have h2 := this.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    rwa [stab_γ₁ hyp.le₂] at h2
  have hcomm := commutator_Vv_γ₁_Vv_le hyp hV hγ.geodesic (by omega)
  rw [hW, hVγ] at hcomm
  have hquad := (quadratic_Vv_γ₁_Vv hyp hV hγ.geodesic hb hodd).2.2.1
  rw [hW, hVγ] at hquad
  have hWab := isElemAbelian_Vv_γ₁ hyp hV (by omega)
  rw [hW] at hWab
  refine odd_case_false hK hB hWab hWP hW'P hcomm hquad ?_
  have hnV : ¬ V ≤ pCoreOf 2 (conjSub (g : G) G₂) := by
    intro hle
    apply hγ.not_le
    rw [← hstab] at hle
    exact hle.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp _)
  obtain ⟨v, hv, hvn⟩ := IsConcreteLE.not_le_iff_exists.mp hnV
  have hVP : V ≤ conjSub (g : G) G₂ := by
    have hVstab : V ≤ stab (g • γ₁ G₀ G₁ G₂) := V_le_stab_of_dist_le hyp hV hγ.dist_eq.le
    rwa [hstab] at hVstab
  have hy : (g : G)⁻¹ * v * g ∈ G₂ := mem_conjSub.mp (hVP hv)
  refine ⟨v, le_conjClosure V G₂ hv, hy, fun hker => hvn ?_⟩
  have hvv : v * v = 1 := by
    have := isElemAbelian_pow_eq_one hyp.elemAbelian hv
    rwa [pow_two] at this
  have hyy : (⟨(g : G)⁻¹ * v * g, hy⟩ : ↥G₂) * ⟨(g : G)⁻¹ * v * g, hy⟩ = 1 := by
    refine Subtype.ext ?_
    show (g : G)⁻¹ * v * g * ((g : G)⁻¹ * v * g) = 1
    calc (g : G)⁻¹ * v * g * ((g : G)⁻¹ * v * g) = (g : G)⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hvv]; group
  have hin := hB.ker_inv_le _ hyy hker
  have hmem : v ∈ conjSub (g : G) (pCoreOf 2 G₂) := mem_conjSub.mpr hin
  rwa [← pCoreOf_conjSub] at hmem

theorem odd_critDist_false (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hab : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥)
    (hB : BenderLocalFacts (K1 ⊔ S) S (conjClosure Zs L2))
    (hodd : Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2))) : False := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hb := three_le_critDist_of_comm hRO h hab
  have hZ : Zs ≠ ⊥ := by
    intro hZ
    have := h.card_Z
    rw [hZ, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hPc : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
    sup_le h.K1_cent_Z (F112J2.S_le_centralizer_Z h)
  have hK : KleinData (K1 ⊔ S) (conjClosure Zs L2) z :=
    { V_le := h.V_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      elemAbelian := hyp.elemAbelian
      card_eq := h.V_card
      z_mem := le_conjClosure Zs L2 hz
      z_ne_one := hz1'
      z_cent := fun x hx => ((Subgroup.mem_centralizer_iff.mp (hPc hx)) z hz).symm }
  exact odd_critDist_false_of_amalgam hyp (F112J2.V_ne_bot h) hb hodd hK hB

end CFSG.Quasithin.SzVB
