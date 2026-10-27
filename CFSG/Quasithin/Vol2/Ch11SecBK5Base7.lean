module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base6
public import CFSG.Quasithin.Background.HNPrime

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2.KGNat
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V X : Subgroup G} [IsMulCommutative ↥V]
  {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M] {LM : LinModel D K M}
  {π : D.Gam →* ↥(autOn L V)} {f : ↥V → M}


abbrev cZ (L V : Subgroup G) : Subgroup ↥V := (Subgroup.centralizer (L : Set G)).subgroupOf V

theorem nPrime_autOn_eq_map
    (hf : IsCoord LM (autOn L V) (cZ L V) π f)
    (hfaith : ∀ γ, (∀ x, LM.lin γ x = x) → π γ = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, L⁆ = V)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    E3.nPrime (autOn X V) =
      E3.nPrime (((autOn X V).subgroupOf (normZH (autOn L V) (cZ L V))).map (psiZ hf)) := by
  have hinj := psiZ_injective hf hfaith autOn_fix_cent (commV_autOn_eq_top hLV hcomm)
  rw [nPrime_map_of_injective hinj, ← nPrime_map_of_injective (Subgroup.subtype_injective _),
    Subgroup.map_subgroupOf_eq_of_le (autOn_le_normZH hXN)]

theorem map_autOn_le (hf : IsCoord LM (autOn L V) (cZ L V) π f) (hLX : L ≤ X) :
    ((autOn L V).subgroupOf (normZH (autOn L V) (cZ L V))).map (psiZ hf) ≤
      ((autOn X V).subgroupOf (normZH (autOn L V) (cZ L V))).map (psiZ hf) :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _
    (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hLX) : autOn L V ≤ autOn X V))

theorem map_le_normalizer (hf : IsCoord LM (autOn L V) (cZ L V) π f)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ((autOn X V).subgroupOf (normZH (autOn L V) (cZ L V))).map (psiZ hf) ≤
      Subgroup.normalizer (((autOn L V).subgroupOf (normZH (autOn L V) (cZ L V))).map
        (psiZ hf) : Set (MulAut (Multiplicative M))) := by
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : (τ : MulAut ↥V) ∈ autOn X V := hτ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' : (σ : MulAut ↥V) ∈ autOn L V := hσ
    refine ⟨τ * σ * τ⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change ((τ : MulAut ↥V) * σ * (τ : MulAut ↥V)⁻¹) ∈ autOn L V
    exact ((autOn_le_normZH hXN hτ').2 σ).mp hσ'
  · rintro ⟨σ, hσ, hσy⟩
    have hσ' : (σ : MulAut ↥V) ∈ autOn L V := hσ
    refine ⟨τ⁻¹ * σ * τ, ?_, ?_⟩
    · change ((τ : MulAut ↥V)⁻¹ * σ * (τ : MulAut ↥V)) ∈ autOn L V
      have h1 := (((normZH (autOn L V) (cZ L V)).inv_mem (autOn_le_normZH hXN hτ')).2 σ).mp hσ'
      simpa using h1
    · rw [map_mul, map_mul, map_inv, hσy]
      group

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
