module

public import CFSG.Timmesfeld.RankTwo.ModelD43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {K : Type} [Field K] {σ : K →+* K}

set_option quotPrecheck false in
local notation "𝕏" => (twistedDatum σ).rootGroup

theorem d43Lift_single_zero : d43Lift (Pi.single (ng 0) 1) = Pi.single (nd 2) 1 :=
  ofFn_injective' (by decide +kernel)

theorem d43Lift_neg_single_zero : d43Lift (-Pi.single (ng 0) 1) = -Pi.single (nd 2) 1 :=
  ofFn_injective' (by decide +kernel)

theorem d43Lift_single_one : d43Lift (Pi.single (ng 1) 1) = (1 : ℤ) • Pi.single (nd 0) 1 :=
  ofFn_injective' (by decide +kernel)

theorem d43Lift_neg_single_one :
    d43Lift (-Pi.single (ng 1) 1) = (-1 : ℤ) • Pi.single (nd 0) 1 :=
  ofFn_injective' (by decide +kernel)

theorem exists_hom_range {H L G : Type*} [Group H] [Group L] [Group G] {φ : H →* L}
    (hinj : Function.Injective φ) (f : H →* G) :
    ∃ θ : φ.range →* G, ∀ a, θ ⟨φ a, a, rfl⟩ = f a := by
  refine ⟨f.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom, fun a => ?_⟩
  have e : (⟨φ a, a, rfl⟩ : φ.range) = MonoidHom.ofInjective hinj a :=
    Subtype.ext (MonoidHom.ofInjective_apply hinj).symm
  rw [MonoidHom.comp_apply, e, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

variable (hσ : ∀ c, σ (σ (σ c)) = c) {G : Type*} [Group G]
  (ψS : (Fin (Tag.rank .G2) → ℤ) → K → G) (ψL : (Fin (Tag.rank .G2) → ℤ) → fixedField σ → G)

theorem d43_extendsToHom_long (fL : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* G)
    (hup : ∀ c, fL (sl2Upper c) = ψL (Pi.single (ng 0) 1) c)
    (hlo : ∀ c, fL (sl2Lower c) = ψL (-Pi.single (ng 0) 1) c) :
    ExtendsToHom 𝕏 {Pi.single (ng 0) 1, -Pi.single (ng 0) 1} (d43PhiOf hσ ψS ψL) := by
  obtain ⟨θ, hθ⟩ := exists_hom_range (slLong_injective hσ) fL
  refine ⟨(slLong σ hσ).range, θ, fun γ hγ x => ?_⟩
  have hx := (mem_twistedRootGroup σ).1 x.2
  rcases hγ with rfl | rfl
  · have hr : IsRoot .G2 (Pi.single (ng 0) 1) := isRoot_single .G2 _
    have hl : d43Long (Pi.single (ng 0) 1) := by decide
    obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ hr hl _).1 hx
    have e : (x : twistedGroup σ) = slLong σ hσ (sl2Upper c) := Subtype.ext (by
      rw [slLong_val, slLongE_upper, ← hc, d43XLg, d43Lift_single_zero])
    refine ⟨⟨sl2Upper c, e.symm⟩, ?_⟩
    rw [d43PhiOf_long hσ ψS ψL hr hl c x hc.symm, ← hup c, ← hθ (sl2Upper c)]
    exact congrArg θ (Subtype.ext e)
  · have hr : IsRoot .G2 (-Pi.single (ng 0) 1) := isRoot_neg_single .G2 _
    have hl : d43Long (-Pi.single (ng 0) 1) := by decide
    obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ hr hl _).1 hx
    have e : (x : twistedGroup σ) = slLong σ hσ (sl2Lower c) := Subtype.ext (by
      rw [slLong_val, slLongE_lower, ← hc, d43XLg, d43Lift_neg_single_zero])
    refine ⟨⟨sl2Lower c, e.symm⟩, ?_⟩
    rw [d43PhiOf_long hσ ψS ψL hr hl c x hc.symm, ← hlo c, ← hθ (sl2Lower c)]
    exact congrArg θ (Subtype.ext e)

theorem d43_extendsToHom_short (fS : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hup : ∀ c, fS (sl2Upper c) = ψS (Pi.single (ng 1) 1) c)
    (hlo : ∀ c, fS (sl2Lower c) = ψS (-Pi.single (ng 1) 1) c) :
    ExtendsToHom 𝕏 {Pi.single (ng 1) 1, -Pi.single (ng 1) 1} (d43PhiOf hσ ψS ψL) := by
  obtain ⟨θ, hθ⟩ := exists_hom_range (slShort_injective hσ) fS
  refine ⟨(slShort σ hσ).range, θ, fun γ hγ x => ?_⟩
  have hx := (mem_twistedRootGroup σ).1 x.2
  rcases hγ with rfl | rfl
  · have hr : IsRoot .G2 (Pi.single (ng 1) 1) := isRoot_single .G2 _
    have hs : ¬d43Long (Pi.single (ng 1) 1) := by decide
    obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ hr hs _).1 hx
    have e : (x : twistedGroup σ) = slShort σ hσ (sl2Upper c) := Subtype.ext (by
      rw [slShort_upper, ← hc, d43XSh, d43Lift_single_one, xOrbit_smul_single σ (Or.inl rfl)])
    refine ⟨⟨sl2Upper c, e.symm⟩, ?_⟩
    rw [d43PhiOf_short hσ ψS ψL hr hs c x hc.symm, ← hup c, ← hθ (sl2Upper c)]
    exact congrArg θ (Subtype.ext e)
  · have hr : IsRoot .G2 (-Pi.single (ng 1) 1) := isRoot_neg_single .G2 _
    have hs : ¬d43Long (-Pi.single (ng 1) 1) := by decide
    obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ hr hs _).1 hx
    have e : (x : twistedGroup σ) = slShort σ hσ (sl2Lower c) := Subtype.ext (by
      rw [slShort_lower, ← hc, d43XSh, d43Lift_neg_single_one,
        xOrbit_smul_single σ (Or.inr rfl)])
    refine ⟨⟨sl2Lower c, e.symm⟩, ?_⟩
    rw [d43PhiOf_short hσ ψS ψL hr hs c x hc.symm, ← hlo c, ← hθ (sl2Lower c)]
    exact congrArg θ (Subtype.ext e)

theorem d43_extendsToHom_rankOne (fL : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* G)
    (hLu : ∀ c, fL (sl2Upper c) = ψL (Pi.single (ng 0) 1) c)
    (hLl : ∀ c, fL (sl2Lower c) = ψL (-Pi.single (ng 0) 1) c)
    (fS : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hSu : ∀ c, fS (sl2Upper c) = ψS (Pi.single (ng 1) 1) c)
    (hSl : ∀ c, fS (sl2Lower c) = ψS (-Pi.single (ng 1) 1) c) :
    ∀ i : Fin (Tag.rank .G2), ExtendsToHom 𝕏 {Pi.single i 1, -Pi.single i 1} (d43PhiOf hσ ψS ψL)
  | ⟨0, _⟩ => d43_extendsToHom_long hσ ψS ψL fL hLu hLl
  | ⟨1, _⟩ => d43_extendsToHom_short hσ ψS ψL fS hSu hSl

theorem range_d43PhiOf_short {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ) :
    Set.range (d43PhiOf hσ ψS ψL γ) = Set.range (ψS γ) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ hγ hs _).1 ((mem_twistedRootGroup σ).1 x.2)
    exact ⟨c, (d43PhiOf_short hσ ψS ψL hγ hs c x hc.symm).symm⟩
  · rintro ⟨c, rfl⟩
    have h := d43XSh_mem hσ hγ hs c
    exact ⟨⟨⟨_, twistedRootSubgroupD4_le_twistedGroup σ hγ h⟩, (mem_twistedRootGroup σ).2 h⟩,
      d43PhiOf_short hσ ψS ψL hγ hs c _ rfl⟩

theorem range_d43PhiOf_long {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ) :
    Set.range (d43PhiOf hσ ψS ψL γ) = Set.range (ψL γ) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ hγ hl _).1 ((mem_twistedRootGroup σ).1 x.2)
    exact ⟨c, (d43PhiOf_long hσ ψS ψL hγ hl c x hc.symm).symm⟩
  · rintro ⟨c, rfl⟩
    have h := d43XLg_mem hσ hγ hl c
    exact ⟨⟨⟨_, twistedRootSubgroupD4_le_twistedGroup σ hγ h⟩, (mem_twistedRootGroup σ).2 h⟩,
      d43PhiOf_long hσ ψS ψL hγ hl c _ rfl⟩

theorem iUnion_range_d43PhiOf :
    ⋃ γ ∈ (twistedDatum σ).roots, Set.range (d43PhiOf hσ ψS ψL γ) =
      (⋃ γ ∈ {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ ¬d43Long γ}, Set.range (ψS γ)) ∪
        ⋃ γ ∈ {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ d43Long γ}, Set.range (ψL γ) := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    have hγ' : IsRoot .G2 γ := by rwa [twistedDatum_roots] at hγ
    by_cases hl : d43Long γ
    · rw [range_d43PhiOf_long hσ ψS ψL hγ' hl] at hg
      exact Or.inr ⟨γ, ⟨hγ', hl⟩, hg⟩
    · rw [range_d43PhiOf_short hσ ψS ψL hγ' hl] at hg
      exact Or.inl ⟨γ, ⟨hγ', hl⟩, hg⟩
  · rintro (⟨γ, ⟨hγ, hl⟩, hg⟩ | ⟨γ, ⟨hγ, hl⟩, hg⟩)
    · refine ⟨γ, by rw [twistedDatum_roots]; exact hγ, ?_⟩
      rwa [range_d43PhiOf_short hσ ψS ψL hγ hl]
    · refine ⟨γ, by rw [twistedDatum_roots]; exact hγ, ?_⟩
      rwa [range_d43PhiOf_long hσ ψS ψL hγ hl]

end CFSG.Timmesfeld.RankTwo
