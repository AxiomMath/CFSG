module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCT6Lin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.PU.L3YC

section Normalizer

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ Subgroup.centralizer (L : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hg l).mp hl
    have := hx _ hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

end Normalizer

theorem pu_t6 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1) :
    ¬ Subgroup.centralizer ({c₀} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  classical
  obtain ⟨Vc, Vn, hlabel, -, hVcCQ, -, hF2U⟩ :=
    pu_f1_f2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  obtain ⟨hsw1, hsw2⟩ := szN3_conj_V_swap hyp hD ht'T ht'S
  have hVn4 : Nat.card ↥Vn = 4 := by
    rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hD.card₂
    · exact hD.card₁
  have hsw : B6.conjSub t' Vc = Vn := by
    rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsw1
    · exact hsw2
  have hGL : L ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun l hl => Subgroup.le_normalizer hl) hSL
  have hQeq : c134Q (L ⊔ Sgp153 T V₁) L = ⁅pCoreOf 2 L, L⁆ :=
    MS93.commutator_eq_blockU le_sup_left hGL hperf
  have hNQ : Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (c134Q (L ⊔ Sgp153 T V₁) L : Set G) := by
    rw [hQeq]
    exact MS93.le_normalizer_commutator_of
      (normalizer_le_normalizer_pCoreOf 2 L) le_rfl
  have hNV : ∀ g ∈ Subgroup.normalizer (L : Set G), g ∈ Subgroup.normalizer (Vc : Set G) := by
    intro g hg
    rw [hVcCQ, c134CQ]
    exact mem_normalizer_inf (hNQ hg) (normalizer_le_normalizer_centralizer L hg)
  have hcVc : c₀ ∈ Vc := hVcCQ ▸ hc₀
  have hconj : ∀ A B : Subgroup G, B6.conjSub t' A = B → ∀ x ∈ A, t' * x * t'⁻¹ ∈ B := by
    intro A B h x hx
    rw [← h, B6.mem_conjSub]
    have e : t'⁻¹ * (t' * x * t'⁻¹) * t' = x := by group
    rw [e]
    exact hx
  have hu₀Vn : t' * c₀ * t'⁻¹ ∈ Vn := hconj _ _ hsw c₀ hcVc
  obtain ⟨n, F, iF, fF, α, hFc, hα, hE2, -, -, hnat, -, -, -⟩ := h4.1
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  obtain ⟨y, hyL, hya, w, hwW, hwn⟩ :=
    exists_fix_not_normalizing hF α hα.1 hnat hF2U hVn4 hu₀Vn
  intro hle
  have hcent : t'⁻¹ * y * t' ∈ Subgroup.centralizer ({c₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have e : t'⁻¹ * y * t' * h * (t'⁻¹ * y * t')⁻¹ = h := by
      calc t'⁻¹ * y * t' * h * (t'⁻¹ * y * t')⁻¹
          = t'⁻¹ * (y * (t' * h * t'⁻¹) * y⁻¹) * t' := by group
        _ = h := by rw [hya]; group
    calc h * (t'⁻¹ * y * t') = (t'⁻¹ * y * t' * h * (t'⁻¹ * y * t')⁻¹) * (t'⁻¹ * y * t') := by
          rw [e]
      _ = t'⁻¹ * y * t' * h := by group
  have hN := hNV _ (hle hcent)
  have hwc : t'⁻¹ * w * t' ∈ Vc := by
    have : w ∈ B6.conjSub t' Vc := hsw ▸ hwW
    exact (B6.mem_conjSub).mp this
  have h1 : t'⁻¹ * y * t' * (t'⁻¹ * w * t') * (t'⁻¹ * y * t')⁻¹ ∈ Vc :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp hwc
  have h2 : t' * (t'⁻¹ * y * t' * (t'⁻¹ * w * t') * (t'⁻¹ * y * t')⁻¹) * t'⁻¹ ∈ Vn :=
    hconj _ _ hsw _ h1
  apply hwn
  have e : t' * (t'⁻¹ * y * t' * (t'⁻¹ * w * t') * (t'⁻¹ * y * t')⁻¹) * t'⁻¹ = y * w * y⁻¹ := by
    group
  rwa [e] at h2

end Stellmacher.PU.L3YC

end CFSG.Quasithin
