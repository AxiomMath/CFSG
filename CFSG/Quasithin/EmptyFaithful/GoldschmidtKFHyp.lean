module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSigma
public import CFSG.Quasithin.EmptyFaithful.SBd18OutProof

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

structure KFHyp {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G)
    (X : Subgroup G) (τ f : G) : Prop where
  r : SBd14.RestHyp T Mc M V₁ V₂ Yp I L t
  hI : I = Subgroup.normalizer (V₁ : Set G)
  hCv : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I
  hTI : ∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G)
  hCIL : I ⊓ Subgroup.centralizer (L : Set G) = V₁
  hidx : L.relIndex I = 12
  hIsup : I = L ⊔ Yp ⊔ Sgp153 T V₁
  hXY : X ≤ Yp
  hX3 : IsPGroup 3 ↥X
  hXidx : ¬ 3 ∣ X.relIndex Yp
  hreg : Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥
  hτS : τ ∈ Sgp153 T V₁
  hfS : f ∈ Sgp153 T V₁
  hτN : τ ∈ Subgroup.normalizer (X : Set G)
  hfN : f ∈ Subgroup.normalizer (X : Set G)
  hττ : τ * τ = 1
  hff : f * f = 1
  hτf : τ * f = f * τ
  hτ1 : τ ≠ 1
  hf1 : f ≠ 1
  hτf' : τ ≠ f
  hcl : ∀ s ∈ Sgp153 T V₁ ⊓ Subgroup.normalizer (X : Set G), s = 1 ∨ s = τ ∨ s = f ∨ s = τ * f
  hinv : ∀ x ∈ X, f * x * f⁻¹ = x⁻¹
  hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f)
  hmove : ∃ v ∈ V₁, τ * v ≠ v * τ
  hσL : τ * f ∉ L
  hcl' : Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers (τ * f)
  ht₀ : ∃ t₀ ∈ T ⊓ Subgroup.normalizer (X : Set G),
    t₀ * τ * t₀⁻¹ = τ * f ∧ t₀ * (τ * f) * t₀⁻¹ = τ
  hNV : ∀ g : G, g⁻¹ * τ * g ∉ V₁
  hNz : ∀ z : G, z ≠ 1 → z * z = 1 → (∀ g ∈ T, g * z = z * g) → ∀ g : G, g⁻¹ * τ * g ≠ z
  hcore : ∃ Lτ Lf : Subgroup G, SBd14.CoreProps L V₁ I Lτ τ ∧ SBd14.CoreProps L V₁ I Lf f ∧
    ((Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 168 ∧ Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 60) ∨
      (Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 60 ∧ Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 168))

namespace KFHyp

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem sigma_mem (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : τ * f ∈ Sgp153 T V₁ :=
  Subgroup.mul_mem _ h.hτS h.hfS

theorem sigma_sq (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : (τ * f) * (τ * f) = 1 := by
  calc τ * f * (τ * f) = τ * (f * τ) * f := by group
    _ = τ * (τ * f) * f := by rw [← h.hτf]
    _ = (τ * τ) * (f * f) := by group
    _ = 1 := by rw [h.hττ, h.hff, one_mul]

theorem L_le_I (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : L ≤ I := by
  rw [h.hIsup]
  exact le_sup_of_le_left le_sup_left

theorem sigma_mem_I (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : τ * f ∈ I :=
  h.r.S_le_I h.sigma_mem

theorem sigma_ne_one (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : τ * f ≠ 1 :=
  fun h1 => h.hσL (h1 ▸ L.one_mem)

theorem sigma_structure (h113 : StageLemma14113) (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card ↥F = 9 ∧
      (∀ x ∈ F, (τ * f) * x = x * (τ * f)) ∧
      (∀ l ∈ L, (τ * f) * l = l * (τ * f) → Odd (orderOf l) → l ∈ F) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({τ * f} : Set G)) :=
  h.r.exists_sigma_structure h113 (fun _ _ _ _ hK => SBd18.outFacts hK) h.hτS h.hττ h.hmove
    h.sigma_mem h.sigma_sq h.hcent h.hσL

end KFHyp

end CFSG.Quasithin.SBd19F
