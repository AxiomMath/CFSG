module

public import CFSG.Quasithin.EmptyFaithful.T1531Close
public import CFSG.Quasithin.EmptyFaithful.T1531Gold2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Stage68

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem commutator_mem_pCoreOf_Y (h1 : Case157One T Mc M) {a b : G} (ha : a ∈ Y153 Mc M)
    (hb : b ∈ Y153 Mc M) : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (Y153 Mc M) := by
  obtain ⟨e⟩ := h1.2
  have hcomm : ∀ x y : OTwoQuot (Y153 Mc M), x * y = y * x := fun x y => by
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hq : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥(Y153 Mc M)) :
      OTwoQuot (Y153 Mc M)) = 1 := by
    have := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]
    group
  have hmem := (QuotientGroup.eq_one_iff _).1 hq
  exact ⟨_, hmem, rfl⟩

omit [Finite G] in
theorem Y_le_normalizer_NY (h1 : Case157One T Mc M) (L : LineData153 T M V₁ V₂ E) :
    Y153 Mc M ≤
      Subgroup.normalizer ((Y153 Mc M ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G) := by
  have key : ∀ y ∈ Y153 Mc M, ∀ n ∈ Y153 Mc M ⊓ Subgroup.normalizer (E : Set G),
      y * n * y⁻¹ ∈ Y153 Mc M ⊓ Subgroup.normalizer (E : Set G) := by
    intro y hy n hn
    refine ⟨(Y153 Mc M).mul_mem ((Y153 Mc M).mul_mem hy hn.1) ((Y153 Mc M).inv_mem hy), ?_⟩
    have hc : y * n * y⁻¹ * n⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
      have := commutator_mem_pCoreOf_Y h1 hy hn.1
      rw [h1.1] at this
      exact this.2
    have hcN : y * n * y⁻¹ * n⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le L.le_V hc)
    have e : y * n * y⁻¹ = (y * n * y⁻¹ * n⁻¹) * n := by group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem hcN hn.2
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key y hy x hx
  · intro hx
    have h0 := key y⁻¹ ((Y153 Mc M).inv_mem hy) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [inv_inv, e] at h0
    exact h0

omit [Finite G] in
theorem Y_le_normalizer_YE (h1 : Case157One T Mc M) (L : LineData153 T M V₁ V₂ E) :
    Y153 Mc M ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
  (Y_le_normalizer_NY h1 L).trans (normalizer_le_normalizer_oTwoUpper _)

theorem YF_le_Y (c : Ctx153 G T Mc M V₁ V₂ t) (gl : GoldLine153 T V₁ E s) :
    YF153 Mc M E s ≤ Y153 Mc M := by
  have h1 : YE153 Mc M E ≤ Y153 Mc M := (oTwoUpper_le _).trans inf_le_left
  have h2 : conjSubgroup (Y153 Mc M) s = Y153 Mc M :=
    conjSubgroup_eq_of_mem_normalizer (le_normalizer_Y153 Mc M (c.hyp.T_le gl.s_mem.1))
  calc YF153 Mc M E s ≤ conjSubgroup (Y153 Mc M) s := E3.conjSubgroup_mono_left s h1
    _ = Y153 Mc M := h2

theorem G0_le_normalizer_YE (c : Ctx153 G T Mc M V₁ V₂ t) (r49 : Res15349 T Mc M V₁)
    (L : LineData153 T M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G) := by
  have hY := Y_le_normalizer_YE r49.case_one L
  have hTE := TE153_le_normalizer_YE153 (E := E) c
  refine sup_le (sup_le ((YF_le_Y c gl).trans hY) hTE) (sup_le ?_ hTE)
  exact ((oTwoUpper_le _).trans (Subgroup.centralizer_le_normalizer _)).trans r67.YE_normal

theorem V_le_pCoreOf_G0 (c : Ctx153 G T Mc M V₁ V₂ t) (r49 : Res15349 T Mc M V₁)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG0 := G0_le_normalizer_YE c r49 L r67 gl
  have hVTE : VZ T M ≤ TE153 T E :=
    le_inf c.hyp.VZ_le_T (HypF91.le_normalizer_of_isElemAbelian_le c.hyp.elemAbelian L.le_V)
  have hVG0 : VZ T M ≤ G0_153 T Mc M E s :=
    hVTE.trans (le_sup_right.trans (le_sup_right (a := G1_153 T Mc M E s)))
  have hYEM : YE153 Mc M E ≤ M := ((oTwoUpper_le _).trans inf_le_left).trans (Y153_le Mc M)
  have hVYE : VZ T M ≤ YE153 Mc M E := by
    have hVN : VZ T M ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
      hVTE.trans (TE153_le_normalizer_YE153 (E := E) c)
    have hcomm : ⁅VZ T M, YE153 Mc M E⁆ ≤ YE153 Mc M E := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have h1 : v * y * v⁻¹ ∈ YE153 Mc M E := (Subgroup.mem_normalizer_iff.mp (hVN hv) y).mp hy
      have e : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact (YE153 Mc M E).mul_mem h1 ((YE153 Mc M E).inv_mem hy)
    rw [← r66.V_comm]
    exact hcomm
  have hVP : VZ T M ≤ pCoreOf 2 (YE153 Mc M E) :=
    le_pCoreOf_of_le_normalizer 2 hVYE (hYEM.trans c.hyp.le_normalizer)
      (B2F.isPGroup_of_isElemAbelian c.hyp.elemAbelian)
  have hP : pCoreOf 2 (YE153 Mc M E) ≤ YE153 Mc M E := pCoreOf_le 2 _
  have hGP : G0_153 T Mc M E s ≤ Subgroup.normalizer (pCoreOf 2 (YE153 Mc M E) : Set G) :=
    hG0.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hX : G0_153 T Mc M E s ⊓ pCoreOf 2 (YE153 Mc M E) ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨(G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).mul_mem hg hx1)
        ((G0_153 T Mc M E s).inv_mem hg), (Subgroup.mem_normalizer_iff.mp (hGP hg) x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hGP hg) x).mpr hx2⟩
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e]
      exact (G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).mul_mem
        ((G0_153 T Mc M E s).inv_mem hg) hx1) hg
  exact fun v hv => hX ⟨hVG0 hv, hVP hv⟩

end Stage68

structure Res15368Rest {G : Type} [Group G] (T Mc M E : Subgroup G) (s : G) : Prop where
  pCore_le_centralizer : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G)
  sylow_of_inM : ∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀
  triple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)
  pCore_eq : pCoreOf 2 (G0_153 T Mc M E s) =
    (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype

@[expose] def Stage15368Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s → Res15368Rest T Mc M E s

theorem stage15368B_of_rest (i : Stage15368Rest) : Stage15368B := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl
  have hr := i G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl
  exact ⟨G0_le_normalizer_YE c r49 L r67 gl, V_le_pCoreOf_G0 c r49 L r66 r67 gl,
    hr.pCore_le_centralizer, hr.sylow_of_inM, hr.triple, hr.pCore_eq⟩

end CFSG.Quasithin
