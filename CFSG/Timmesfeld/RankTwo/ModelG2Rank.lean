module

public import CFSG.Timmesfeld.RankTwo.ModelG2
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.G2)

set_option quotPrecheck false in
local notation "𝕏" => (g2Datum K).rootGroup

theorem g2_extendsToHom_rankOne {G : Type*} [Group G] (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    (i : Fin (Tag.rank .G2)) (f : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hup : ∀ c, f (sl2Upper c) = ψ (Pi.single i 1) c)
    (hlo : ∀ c, f (sl2Lower c) = ψ (-Pi.single i 1) c) :
    ExtendsToHom 𝕏 {Pi.single i 1, -Pi.single i 1} (g2PhiOf ψ) := by
  obtain ⟨φ, hinj, hφu, hφl⟩ := g2_exists_sl2_hom (K := K) i
  have hθ : ∀ a, (f.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom) ⟨φ a, a, rfl⟩ = f a :=
    fun a => by
      have e : (⟨φ a, a, rfl⟩ : φ.range) = MonoidHom.ofInjective hinj a :=
        Subtype.ext (MonoidHom.ofInjective_apply hinj).symm
      rw [MonoidHom.comp_apply, e, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨φ.range, f.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom, fun γ hγ x => ?_⟩
  obtain ⟨x, hx⟩ := x
  rcases hγ with rfl | rfl
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single .G2 i) x).1 hx
    have e : 𝕩 (Pi.single i 1) c = φ (sl2Upper c) := by rw [xPar_simple, hφu]
    refine ⟨⟨sl2Upper c, e.symm⟩, ?_⟩
    rw [g2PhiOf_xPar ψ (isRoot_single .G2 i) c, ← hup c, ← hθ (sl2Upper c)]
    exact congrArg _ (Subtype.ext e)
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single .G2 i) x).1 hx
    have e : 𝕩 (-Pi.single i 1) c = φ (sl2Lower c) := by rw [xPar_neg_simple, hφl]
    refine ⟨⟨sl2Lower c, e.symm⟩, ?_⟩
    rw [g2PhiOf_xPar ψ (isRoot_neg_single .G2 i) c, ← hlo c, ← hθ (sl2Lower c)]
    exact congrArg _ (Subtype.ext e)

theorem range_g2PhiOf {G : Type*} [Group G] (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) :
    Set.range (g2PhiOf ψ γ) = Set.range (ψ γ) := by
  ext g
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    exact ⟨c, (g2PhiOf_xPar ψ hγ c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨𝕩 γ c, xPar_mem hγ c⟩, g2PhiOf_xPar ψ hγ c⟩

theorem iUnion_range_g2PhiOf {G : Type*} [Group G] (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G) :
    ⋃ γ ∈ (g2Datum K).roots, Set.range (g2PhiOf ψ γ) = ⋃ γ ∈ (g2Datum K).roots, Set.range (ψ γ) :=
  Set.iUnion₂_congr fun _ hγ => range_g2PhiOf ψ (mem_adjDatum_roots.1 hγ)

end CFSG.Timmesfeld.RankTwo
