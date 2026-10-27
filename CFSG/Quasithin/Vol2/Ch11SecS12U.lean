module

public import CFSG.Quasithin.Vol2.Ch11SecS12T
public import CFSG.Quasithin.Vol2.Ch11SecS12O
public import CFSG.Quasithin.Vol2.Ch11SecS12R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open hiding StatedSL
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem head_of_adjoint (hF : Nat.card F = 4) {Γ V Z L X : Subgroup G}
    (hΓV : Γ ≤ Subgroup.normalizer (V : Set G)) (hLΓ : L ≤ Γ)
    (hXL : ∀ y ∈ X, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (α : ↥Γ →* PGL3 F) (hα : Function.Surjective α)
    (hS0 : QuasithinUnique.IsSylowTwoOf (S0P F) ⊤) {j₀ : Fin 2}
    (hαL : (L.subgroupOf Γ).map α = Ptheta F j₀)
    (α₀ : ↥L →* ↥(StatedSL 2 F)) (hα₀ : Function.Surjective α₀)
    (hker : α₀.ker = (pCoreOf 2 L).subgroupOf L)
    {γx : ↥Γ} (hγxX : (γx : G) ∈ X) (hγ3 : α γx ^ 3 = 1) (hγ1 : α γx ≠ 1)
    (α₂ : ↥Γ →* PGL3 F) (hα₂ : Function.Surjective α₂) (hk : α₂.ker = α.ker)
    (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F))
    (hβsl : ∀ v, (Multiplicative.toAdd (β v)).trace = 0)
    (hβon : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → ∃ v, Multiplicative.toAdd (β v) = M)
    (hβker : ∀ v, β v = 1 ↔ (v : G) ∈ Z)
    (hact : ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * γ⁻¹ → ∀ g : GL (Fin 3) F,
      ProjGenLinGroup.mk g = α₂ γ → Multiplicative.toAdd (β v) =
        (g : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β u) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {J : Subgroup G} (hJ : ⁅V, pCoreOf 2 L⁆ ⊔ Z ≤ J) (hJV : J ≤ V)
    (hxJ : ∀ v ∈ V, (γx : G) * v * (γx : G)⁻¹ * v⁻¹ ∈ J) : J = V := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_ker_eq α α₂ hα hα₂ hk.symm
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hA : (L.subgroupOf Γ).map α₂ = (Ptheta F j₀).map φ.toMonoidHom := by
    rw [← hαL, Subgroup.map_map]
    congr 1
    ext γ
    exact hφ γ
  have h1 : (L.subgroupOf Γ).map α₂ ≠ ⊥ := by
    rw [hA, Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
    exact Ptheta_ne_bot hF j₀
  have hp : ⁅(L.subgroupOf Γ).map α₂, (L.subgroupOf Γ).map α₂⁆ = (L.subgroupOf Γ).map α₂ := by
    rw [hA, ← Subgroup.map_commutator, Ptheta_perfect hF j₀]
  have hc : (L.subgroupOf Γ).map α₂ ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ := by
    rw [hA, ← map_commutator_top φ]
    exact fun h => Ptheta_ne_commutator hF j₀ (Subgroup.map_injective hinj h)
  have hSA : (S0P F).map φ.toMonoidHom ≤
      Subgroup.normalizer (((L.subgroupOf Γ).map α₂ : Subgroup (PGL3 F)) : Set (PGL3 F)) := by
    rw [hA, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans (normalizer_S0P_le j₀))
  obtain ⟨c, j₁, -, hcj⟩ := exists_conj_Ptheta hF (isSylowTwoOf_map φ hS0) hSA h1 hp hc
  obtain ⟨α₃, hα₃⟩ : ∃ α₃ : ↥Γ →* PGL3 F, α₃ = (MulAut.conj c).toMonoidHom.comp α₂ := ⟨_, rfl⟩
  have hα₃L : (L.subgroupOf Γ).map α₃ = Ptheta F j₁ := by
    rw [hα₃, ← Subgroup.map_map]
    exact hcj
  obtain ⟨c₀, hc₀⟩ := ProjGenLinGroup.mk_surjective c
  have hact₃ : ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * γ⁻¹ → ∀ g : GL (Fin 3) F,
      ProjGenLinGroup.mk g = α₃ γ → Multiplicative.toAdd (conjβ c₀ β v) =
        (g : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (conjβ c₀ β u) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    fun γ u v huv g hg => conjβ_rel c₀ β α₂ hact γ u v huv g (by rw [hg, hα₃, hc₀]; rfl)
  have hO := pCoreOf_le_map hF hLΓ α₃ (by rw [hα₃L]; exact Ptheta_perfect hF j₁)
    (by rw [hα₃L]; exact Ptheta_ne_bot hF j₁) α₀ hα₀ hker
  rw [hα₃L] at hO
  have hQ : ∀ p ∈ pCoreOf 2 (Ptheta F j₁), ∃ q ∈ pCoreOf 2 L, ∀ h : GL (Fin 3) F,
      ProjGenLinGroup.mk h = p → ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
        Multiplicative.toAdd (conjβ c₀ β w) = (h : Matrix (Fin 3) (Fin 3) F) *
          Multiplicative.toAdd (conjβ c₀ β v) *
            ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := hO hp
    exact ⟨q, Subgroup.mem_subgroupOf.mp hq, fun h hh v w hvw => hact₃ q v w hvw h hh⟩
  have hsc := map_mem_sectionCentralizer α₃ hLΓ (mem_normalizer_of_comm hXL hγxX) (hXL _ hγxX)
  rw [hα₃L] at hsc
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (α₃ γx)
  have h₂γ : α₂ γx = φ (α γx) := hφ γx
  have hg3 : ProjGenLinGroup.mk g ^ 3 = 1 := by
    rw [hg, hα₃, MonoidHom.comp_apply, ← map_pow, h₂γ, ← map_pow, hγ3, map_one, map_one]
  have hg1 : ProjGenLinGroup.mk g ≠ 1 := by
    rw [hg, hα₃, MonoidHom.comp_apply, h₂γ]
    intro h
    exact hγ1 (φ.map_eq_one_iff.mp ((MulAut.conj c).map_eq_one_iff.mp h))
  refine eq_of_head_Ptheta (conjβ c₀ β) hF (trace_conjβ c₀ β hβsl) (conjβ_surj c₀ β hβon)
    (fun v => (conjβ_eq_one_iff c₀ β v).trans (hβker v))
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (hLΓ.trans hΓV)) hQ (hΓV γx.2)
    (by rw [hg]; exact hsc.2.1) (by rw [hg]; exact hsc) hg3 hg1
    (fun v w hvw => hact₃ γx v w hvw g hg) hJ hJV hxJ

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
