module

public import CFSG.Quasithin.Background.F9Fourteen

public section

namespace CFSG.Quasithin.RonanF914

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

variable {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

omit [Finite G] in
theorem commutator_eq_one_of_comm {x u : G} (hc : u * x = x * u) : x * u * x⁻¹ * u⁻¹ = 1 := by
  rw [← hc]; group

theorem exists_decomp (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hb : F8.b T V L H = 3) : ∃ k ∈ H, ∃ l ∈ L, ∃ t ∈ H, (g : G) = k * l * t := by
  have hyp := h.amalgamHypV
  have h1 : CosetGeom.dist (F8.γ₁ T L H) γ' = 1 := by
    have := s.geodesic
    omega
  have hγ'nb : γ' ∈ nbrs (F8.γ₁ T L H) := dist_eq_one_iff_adj.mp h1
  have hγ₀nb : F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) :=
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm
  obtain ⟨k, hk, hk0⟩ := stab_transitive_on_nbrs hγ₀nb hγ'nb
  have hkH : (k : G) ∈ H := by rwa [stab_γ₁ hyp.le₂] at hk
  have hkg : (k⁻¹ * g) • F8.γ₀ T L H = F8.γ₀ T L H := by
    rw [mul_smul, s.edge₀, ← hk0, inv_smul_smul]
  have hmem : ((k⁻¹ * g : ↥((L ⊔ T) ⊔ H)) : G) ∈ L ⊔ T := by
    have := mem_stab_of_smul_eq hkg
    rwa [stab_γ₀ hyp.le₁] at this
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T h.normalizes_L
  obtain ⟨l, hl, t, ht, hlt⟩ : ((k⁻¹ * g : ↥((L ⊔ T) ⊔ H)) : G) ∈ (L : Set G) * T := by
    rw [← hmul]; exact hmem
  refine ⟨k, hkH, l, hl, t, h.T_le_H ht, ?_⟩
  have hlt' : l * t = ((k⁻¹ * g : ↥((L ⊔ T) ⊔ H)) : G) := hlt
  have e : (g : G) = (k : G) * (l * t) := by
    rw [hlt']
    simp
  rw [e, mul_assoc]

theorem UH_Uγ_le_conjSub (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hb : F8.b T V L H = 3) :
    ∃ k ∈ H, conjClosure Vp H ≤ conjSub k (conjClosure (conjClosure Vp H) L) ∧
      F8.Uγ Vp H (g : G) ≤ conjSub k (conjClosure (conjClosure Vp H) L) := by
  obtain ⟨k, hk, l, hl, t, ht, hg⟩ := exists_decomp h s hb
  refine ⟨k, hk, ?_, ?_⟩
  · calc conjClosure Vp H = conjSub k (conjClosure Vp H) :=
          (F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hk)).symm
      _ ≤ conjSub k (conjClosure (conjClosure Vp H) L) := conjSub_mono k (le_conjClosure _ L)
  · unfold F8.Uγ
    rw [hg, conjSub_mul, conjSub_mul,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H ht)]
    exact conjSub_mono k (HypF91.conjSub_le_conjClosure hl)

theorem UH_le_stab_γ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    conjClosure Vp H ≤ stab γ :=
  (conjClosure_mono h.Vp_le_V le_rfl).trans
    ((h.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right))

theorem Vγ_le_H (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ V H (g : G) ≤ H := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have := (h.F913_2 s).2 γ₂ hγ₂nb hd
  rw [stab_γ₁ h.amalgamHypV.le₂] at this
  exact this.trans ((pCoreOf_le 2 _).trans inf_le_left)

theorem Uγ_le_H (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F8.Uγ Vp H (g : G) ≤ H :=
  h.Uγ_le_Vγ.trans (Vγ_le_H h s)

theorem V_le_stab_γ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) : V ≤ stab γ :=
  V_le_stab_of_dist_le h.amalgamHypV h.V_ne_bot s.critical.dist_eq.le

theorem stab_le_normalizer_A₁ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    stab γ ≤ Subgroup.normalizer (F8.A₁ V₁ (g : G) : Set G) := by
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ h.amalgamHypV.le₂]
  rw [hstab]
  exact conjSub_le_normalizer h.H_normalizes_V₁

theorem UH_le_pCore_γ_of_UL_comm (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hb : F8.b T V L H = 3)
    (hab : ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x) :
    ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = ⊥ ∧ conjClosure Vp H ≤ pCoreOf 2 (stab γ) ∧
      F8.Uγ Vp H (g : G) ≤ pCoreOf 2 H := by
  have hcomm : ⁅conjClosure Vp H, F8.Uγ Vp H (g : G)⁆ = ⊥ := by
    obtain ⟨k, hk, h1, h2⟩ := UH_Uγ_le_conjSub h s hb
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' := mem_conjSub.mp (h1 hx)
    have hy' := mem_conjSub.mp (h2 hy)
    have := hab _ hy' _ hx'
    calc y * x = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by rw [this]
      _ = x * y := by group
  have hcomm' : ⁅F8.Uγ Vp H (g : G), conjClosure Vp H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hcomm
  refine ⟨hcomm, ?_, ?_⟩
  · rw [h.pCoreOf_stab_eq_centralizerMod s]
    intro x hx
    refine ⟨UH_le_stab_γ h s hx, stab_le_normalizer_A₁ h s (UH_le_stab_γ h s hx),
      fun u hu => ?_⟩
    have hc : u * x = x * u :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx) u hu
    rw [commutator_eq_one_of_comm hc]
    exact (F8.A₁ V₁ (g : G)).one_mem
  · rw [h.pCoreOf_eq_centralizerMod]
    intro y hy
    refine ⟨Uγ_le_H h s hy, h.H_normalizes_V₁ (Uγ_le_H h s hy), fun u hu => ?_⟩
    have hc : u * y = y * u :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hy) u hu
    rw [commutator_eq_one_of_comm hc]
    exact V₁.one_mem

theorem Uγ_le_H_inf_centralizer_Vp (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hb : F8.b T V L H = 3)
    (hab : ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x) :
    F8.Uγ Vp H (g : G) ≤ H ⊓ Subgroup.centralizer (Vp : Set G) := by
  have hcomm := (UH_le_pCore_γ_of_UL_comm h s hb hab).1
  have hcomm' : ⁅F8.Uγ Vp H (g : G), conjClosure Vp H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hcomm
  intro y hy
  have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hy
  exact ⟨Uγ_le_H h s hy, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_iff.mp hyC z (le_conjClosure Vp H hz)⟩

theorem not_V_le_pCore_γ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ¬ V ≤ pCoreOf 2 (stab γ) := fun hle =>
  s.critical.not_le (hle.trans (pCoreOf_stab_le_ballStab_one h.amalgamHypV.toAmalgamHyp γ))

theorem V_le_pCore_γ_of_le_centralizer_Uγ (h : HypF98 T V L V₁ Vp H)
    (s : F8Setup T V L H γ γ' g) (hV : V ≤ Subgroup.centralizer (F8.Uγ Vp H (g : G) : Set G)) :
    V ≤ pCoreOf 2 (stab γ) := by
  rw [h.pCoreOf_stab_eq_centralizerMod s]
  intro v hv
  refine ⟨V_le_stab_γ h s hv, stab_le_normalizer_A₁ h s (V_le_stab_γ h s hv), fun u hu => ?_⟩
  have hc : u * v = v * u := Subgroup.mem_centralizer_iff.mp (hV hv) u hu
  rw [commutator_eq_one_of_comm hc]
  exact (F8.A₁ V₁ (g : G)).one_mem

theorem not_V_le_centralizer_Uγ (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ¬ V ≤ Subgroup.centralizer (F8.Uγ Vp H (g : G) : Set G) := fun hV =>
  not_V_le_pCore_γ h s (V_le_pCore_γ_of_le_centralizer_Uγ h s hV)

theorem exists_conj_Vp_not_centralizer (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ∃ k ∈ H, ∃ x ∈ conjSub ((g : G) * k) Vp, ∃ v ∈ V, v * x ≠ x * v := by
  by_contra hcon
  push Not at hcon
  refine not_V_le_centralizer_Uγ h s fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hUC : F8.Uγ Vp H (g : G) ≤ Subgroup.centralizer (V : Set G) := by
    unfold F8.Uγ
    rw [conjSub_le_iff]
    refine conjClosure_le fun k hk z hz => ?_
    rw [mem_conjSub, inv_inv, Subgroup.mem_centralizer_iff]
    intro v' hv'
    have hx : (g : G) * (k * z * k⁻¹) * (g : G)⁻¹ ∈ conjSub ((g : G) * k) Vp := by
      have := mul_mem_conjSub (g := (g : G) * k) hz
      have e : (g : G) * k * z * ((g : G) * k)⁻¹ = (g : G) * (k * z * k⁻¹) * (g : G)⁻¹ := by
        group
      rwa [e] at this
    exact hcon k hk _ hx v' hv'
  exact (Subgroup.mem_centralizer_iff.mp (hUC hu) v hv).symm

theorem F914_1_of_eq_of_centralizer (h : HypF98 T V L V₁ Vp H) (hb : F8.b T V L H = 3)
    (hC : H ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G)) :
    ¬ ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x := by
  intro hab
  obtain ⟨γ, γ', g, s⟩ := h.exists_F8Setup
  refine not_V_le_centralizer_Uγ h s fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hC (Uγ_le_H_inf_centralizer_Vp h s hb hab hu)) v hv).symm

theorem F914_1_of_eq_of_case_g_ii (h : HypF98 T V L V₁ Vp H) (hb : F8.b T V L H = 3)
    (hii : ∀ x ∈ H ⊓ Subgroup.centralizer (Vp : Set G), ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ →
      ∀ g : G, conjSub g⁻¹ V ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) →
        conjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G)) :
    ¬ ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x := by
  intro hab
  obtain ⟨γ, γ', g, s⟩ := h.exists_F8Setup
  obtain ⟨k, hk, x, hx, v, hv, hvx⟩ := exists_conj_Vp_not_centralizer h s
  have hxU : x ∈ F8.Uγ Vp H (g : G) := by
    have : conjSub ((g : G) * k) Vp ≤ F8.Uγ Vp H (g : G) := by
      unfold F8.Uγ
      rw [conjSub_mul]
      exact conjSub_mono _ (HypF91.conjSub_le_conjClosure hk)
    exact this hx
  have hxHC := Uγ_le_H_inf_centralizer_Vp h s hb hab hxU
  have hcommle : ⁅V, Subgroup.zpowers x⁆ ≤ F8.Uγ Vp H (g : G) := by
    refine Subgroup.commutator_le.mpr fun v' hv' y hy => ?_
    have hyU : y ∈ F8.Uγ Vp H (g : G) := Subgroup.zpowers_le.mpr hxU hy
    have hN : v' ∈ Subgroup.normalizer (F8.Uγ Vp H (g : G) : Set G) :=
      HypF98.stab_le_normalizer_Uγ s h Vp (V_le_stab_γ h s hv')
    rw [commutatorElement_def]
    have h1 : v' * y * v'⁻¹ ∈ F8.Uγ Vp H (g : G) := (Subgroup.mem_normalizer_iff.mp hN y).mp hyU
    exact (F8.Uγ Vp H (g : G)).mul_mem h1 ((F8.Uγ Vp H (g : G)).inv_mem hyU)
  have hne : ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ := by
    intro hbot
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hv
    exact hvx (Subgroup.mem_centralizer_iff.mp this x (Subgroup.mem_zpowers x)).symm
  have hVδ : conjSub ((g : G) * k) V ≤ F8.Uγ V H (g : G) := by
    unfold F8.Uγ
    rw [conjSub_mul]
    exact conjSub_mono _ (HypF91.conjSub_le_conjClosure hk)
  have hVγab : IsElemAbelian 2 (F8.Uγ V H (g : G)) := isElemAbelian_conjSub h.F911_2
  have hcentr : conjSub ((g : G) * k) V ≤
      Subgroup.centralizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact isElemAbelian_comm hVγab (h.Uγ_le_Vγ (hcommle hu)) (hVδ hw)
  have hnorm : conjSub (((g : G) * k)⁻¹)⁻¹ V ≤
      Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    rw [inv_inv]
    exact hcentr.trans (Subgroup.centralizer_le_normalizer _)
  have hcent := hii x hxHC hne ((g : G) * k)⁻¹ hnorm
  rw [inv_inv] at hcent
  have hxV : x ∈ conjSub ((g : G) * k) V := conjSub_mono _ h.Vp_le_V hx
  exact hvx (Subgroup.mem_centralizer_iff.mp (hcent hxV) v hv)

theorem F914_1' (h : HypF98 T V L V₁ Vp H)
    (hcond : V ≤ conjClosure Vp H ∨
      H ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G) ∨
      (∀ x ∈ H ⊓ Subgroup.centralizer (Vp : Set G), ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ →
        ∀ g : G, conjSub g⁻¹ V ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) →
          conjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G))) :
    (∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x) ↔ 3 < F8.b T V L H := by
  constructor
  · intro hab
    by_contra hnot
    have hb3 := h.three_le_b_and_odd.1
    have hb : F8.b T V L H = 3 := by omega
    rcases hcond with hVU | hC | hii
    · exact h.F914_1_of_eq hb hVU hab
    · exact F914_1_of_eq_of_centralizer h hb hC hab
    · exact F914_1_of_eq_of_case_g_ii h hb hii hab
  · intro hb x hx y hy
    exact isElemAbelian_comm (h.F914_1_of_lt hb) hx hy

end CFSG.Quasithin.RonanF914
