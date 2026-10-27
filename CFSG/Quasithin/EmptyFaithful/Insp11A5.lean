module

public import CFSG.Quasithin.EmptyFaithful.Insp11Defs
public import CFSG.Quasithin.EmptyFaithful.Insp10Defs
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.T1531In66b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section M

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem conj_V₁_cases_of_mem_M (c : Ctx153 G T Mc M V₁ V₂ t) {g : G} (hg : g ∈ M) :
    (∀ v ∈ V₁, g * v * g⁻¹ ∈ V₁) ∨ (∀ v ∈ V₁, g * v * g⁻¹ ∈ V₂) := by
  obtain ⟨q, -, -, -, hqO, hq⟩ := c.decomp.definite
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer hg
  have hφ : conjAct (VZ T M) ⟨g, hgN⟩ ∈ orthogonalGroupOf q := by
    rw [← hqO]
    exact mem_autOn_of_mem hgN hg
  have key : ∀ v ∈ V₁, g * v * g⁻¹ ∈ V₁ ∨ g * v * g⁻¹ ∈ V₂ := by
    intro v hv
    by_cases hv1 : v = 1
    · left
      rw [hv1]
      simp
    · have hvV : v ∈ VZ T M := c.decomp.le₁ hv
      have h1 : q ⟨v, hvV⟩ = 1 := (hq v hvV).mpr ⟨Or.inl hv, hv1⟩
      have h2 := hφ ⟨v, hvV⟩
      have hcoe : ((conjAct (VZ T M) ⟨g, hgN⟩ ⟨v, hvV⟩ : ↥(VZ T M)) : G) = g * v * g⁻¹ :=
        conjAct_apply_coe''' _ _ _
      have hmem : g * v * g⁻¹ ∈ VZ T M := by
        have := (conjAct (VZ T M) ⟨g, hgN⟩ ⟨v, hvV⟩ : ↥(VZ T M)).2
        rwa [hcoe] at this
      have heq : conjAct (VZ T M) ⟨g, hgN⟩ ⟨v, hvV⟩ = ⟨g * v * g⁻¹, hmem⟩ := Subtype.ext hcoe
      rw [heq, h1] at h2
      exact ((hq _ hmem).mp h2).1
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, haV, ha⟩, ⟨b, hbV, hb⟩⟩ := hcon
  have ha2 : g * a * g⁻¹ ∈ V₂ := (key a haV).resolve_left ha
  have hb1 : g * b * g⁻¹ ∈ V₁ := (key b hbV).resolve_right hb
  have hab : a * b ∈ V₁ := V₁.mul_mem haV hbV
  rcases key _ hab with h | h
  · apply ha
    have e : g * a * g⁻¹ = (g * (a * b) * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
    rw [e]
    exact V₁.mul_mem h (V₁.inv_mem hb1)
  · apply hb
    have e : g * b * g⁻¹ = (g * a * g⁻¹)⁻¹ * (g * (a * b) * g⁻¹) := by group
    rw [e]
    exact V₂.mul_mem (V₂.inv_mem ha2) h

end M

theorem inspectA5Quot153_of_geom (hG : A5HatGeom153) : InspectA5Quot153 := by
  intro G _ _ T Mc M V₁ V₂ E t s conf _hconc _hlist _hS3 hO2 _hYFX _hQV _hcomm hHat hcard
  obtain ⟨c, r45, r46, r49, L, r66, r67, gl, r68⟩ := conf
  have hT := isSylowTwoOf_TE_G0 c L r66 r67 gl r68
  have hQ := pPrimeCore_G0_eq c r67 r68
  have hnP : ¬ thompsonJ (TE153 T E) ≤
      (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype := by
    intro hJ
    have hJ' : thompsonJ (TE153 T E) ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
      rwa [r68.pCore_eq]
    have hJX := B6.thompsonJ_le_of_sylow_of_le hT hJ' (le_normalizer_pCoreOf 2 _)
    have hXE : XE153 E ≤ pCoreOf 2 (G0_153 T Mc M E s) :=
      (XE_le_thompsonJ c L r66 r67 gl r68).trans hJX
    exact not_isPGroup_XE r67 ((pCoreOf_isPGroup 2 _).to_le hXE)
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := c.hyp.isHv_of_inM' c.hyp.inM
  have hN : ∀ x ∈ thompsonJ (G0_153 T Mc M E s), x ∈ Subgroup.normalizer (VZ T M : Set G) →
      (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁) ∨ (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₂) :=
    fun x _ hx => conj_V₁_cases_of_mem_M c (hHv.ge hx)
  exact hG G (G0_153 T Mc M E s) (V0_153 T Mc M E s) (thompsonJ (G0_153 T Mc M E s))
    (thompsonJ (TE153 T E)) (VZ T M) V₁ V₂ (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
    (V0_le_G0 r68) V0_normal (isElemAbelian_V0 c r68) hcard hQ hHat (B6.thompsonJ_le _) hO2
    V_le_V0 c.decomp.le₁ c.decomp.le₂ c.decomp.inf c.decomp.sup c.decomp.card₁ c.decomp.card₂
    ((B6.thompsonJ_le _).trans hT.1) (hT.2.1.to_le (B6.thompsonJ_le _)) hnP
    ((thompsonJ_TE_le_R r67).trans inf_le_right) hN

end CFSG.Quasithin
