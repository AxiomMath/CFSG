module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzSkel
public import CFSG.Quasithin.Vol2.Ch12Sec6P31a
public import CFSG.Quasithin.Background.F918C0

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31

section Setting

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

def UVp (V₁ Vp H : Subgroup G) : Subgroup ↥(UT V₁ Vp H) :=
  (tildeOf V₁ Vp).comap (UT V₁ Vp H).subtype

theorem exp_two_UT (h : HypF91 T V L V₁ Vp H) (w : ↥(UT V₁ Vp H)) : w * w = 1 := by
  have h2 := h.isElemAbelian_tilde.2 w.1 w.2
  apply Subtype.ext
  simpa [sq] using h2

theorem thetaH_mem_UVp (h : HypF91 T V L V₁ Vp H) {x : ↥H} (hx : (x : G) ∈ L₁Of L V₁ ⊔ T)
    {u : ↥(UT V₁ Vp H)} (hu : u ∈ UVp V₁ Vp H) : thetaH h x u ∈ UVp V₁ Vp H := by
  show ((thetaH h x u : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) ∈ tildeOf V₁ Vp
  rw [thetaH_apply]
  exact secMk_conj_mem_secImg (A := N1 V₁) (B := V₁) (X := Vp) (a := ⟨x, le_N1 h x.2⟩)
    (h.L₁T_normalizes_Vp hx) hu

theorem tildeOf_self_eq_bot (V₁ : Subgroup G) : tildeOf V₁ V₁ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_secImg.1 hy
  rw [Subgroup.mem_bot]
  exact secMk_eq_one_iff.2 ha

theorem uvp_irred (h : HypF91 T V L V₁ Vp H) (U' : Subgroup ↥(UT V₁ Vp H))
    (hU'U : U' ≤ UVp V₁ Vp H)
    (hinv : ∀ x : ↥H, (x : G) ∈ L₁Of L V₁ ⊔ T → ∀ u ∈ U', thetaH h x u ∈ U') :
    U' = ⊥ ∨ U' = UVp V₁ Vp H := by
  let Y' : Subgroup (SecQuot (N1 V₁) V₁) := U'.map (UT V₁ Vp H).subtype
  let X : Subgroup G := secPre (N1 V₁) V₁ Y'
  have hV₁X : V₁ ≤ X := le_secPre Subgroup.le_normalizer Y'
  have hY'le : Y' ≤ tildeOf V₁ Vp := by
    rintro _ ⟨u, hu, rfl⟩
    exact hU'U hu
  have hXVp : X ≤ Vp := secPre_le h.V₁_lt_Vp.le hY'le
  have hX : ∀ g : ↥H, (g : G) ∈ L₁Of L V₁ ⊔ T → ∀ y ∈ X, (g : G) * y * (g : G)⁻¹ ∈ X := by
    intro g hg y hy
    obtain ⟨a, rfl, ha⟩ := mem_secPre.1 hy
    obtain ⟨u, hu, hua⟩ := ha
    refine mem_secPre.2 ⟨⟨(g : G) * (a : G) * (g : G)⁻¹, ?_⟩, rfl, ?_⟩
    · exact (N1 V₁).mul_mem ((N1 V₁).mul_mem (le_N1 h g.2) a.2) ((N1 V₁).inv_mem (le_N1 h g.2))
    · refine ⟨thetaH h g u, hinv g hg u hu, ?_⟩
      have hua' : ((u : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) = secMk (N1 V₁) V₁ a := hua
      rw [Subgroup.subtype_apply, thetaH_apply, hua']
      show secMk (N1 V₁) V₁ ⟨g, le_N1 h g.2⟩ * secMk (N1 V₁) V₁ a *
          (secMk (N1 V₁) V₁ ⟨g, le_N1 h g.2⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
  have hnorm : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    have hgH : g ∈ H := h.L₁T_le_H hg
    have hginv : g⁻¹ ∈ L₁Of L V₁ ⊔ T := Subgroup.inv_mem _ hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hX ⟨g, hgH⟩ hg y hy
    · intro hy
      have := hX ⟨g⁻¹, H.inv_mem hgH⟩ hginv _ hy
      simpa [mul_assoc] using this
  rcases h.irred X hV₁X hXVp hnorm with hX1 | hX2
  · left
    have h1 : Y' = secImg (N1 V₁) V₁ X := (secImg_secPre Y').symm
    rw [hX1] at h1
    have h2 : Y' = ⊥ := h1.trans (tildeOf_self_eq_bot V₁)
    rw [eq_bot_iff]
    intro u hu
    have : ((u : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) ∈ Y' := ⟨u, hu, rfl⟩
    rw [h2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  · right
    refine le_antisymm hU'U ?_
    intro u hu
    have h1 : Y' = secImg (N1 V₁) V₁ X := (secImg_secPre Y').symm
    rw [hX2] at h1
    have : ((u : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) ∈ Y' := by
      rw [h1]
      exact hu
    obtain ⟨u', hu', hu'u⟩ := this
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'

theorem fixed_eq_one_of_odd_normal (h : HypF91 T V L V₁ Vp H) (E : Subgroup (HStar H)) [E.Normal]
    (hodd : Odd (Nat.card E)) (hE1 : ∃ e ∈ E, e ≠ 1)
    (hES : E ≤ star H (L₁Of L V₁ ⊔ T)) {w : ↥(UT V₁ Vp H)}
    (hw : ∀ e ∈ E, psiH h e w = w) : w = 1 := by
  letI : CommGroup ↥(UT V₁ Vp H) := commGroupOfElemAbelian h.isElemAbelian_tilde
  refine fixed_eq_one_of_normal_odd (exp_two_UT h) (psiH h) (psiH_injective h) E hodd hE1
    (star H (L₁Of L V₁ ⊔ T)) hES (UVp V₁ Vp H) ?_ ?_ ?_ hw
  ·
    intro s hs u hu
    obtain ⟨a, ha, rfl⟩ := hs
    exact thetaH_mem_UVp h (Subgroup.mem_subgroupOf.1 ha) hu
  · intro U' hU'U hinv
    refine uvp_irred h U' hU'U (fun x hx u hu => ?_)
    rw [← psiH_mk]
    exact hinv _ (mk_mem_star (h := x) hx) u hu
  · intro D hUD hinvD
    refine eq_top_of_le h D (fun w hw => hUD hw) (fun x s hs => ?_)
    rw [← psiH_mk]
    exact hinvD _ s hs

end Setting

end CFSG.Quasithin.H13.P31Sz
