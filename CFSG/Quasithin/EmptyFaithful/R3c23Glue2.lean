module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def PairOutputOfAction : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V] {Hg : Type} [Group Hg] [Finite Hg], SQTKGroup Hg →
    (∀ v : V, v ^ 2 = 1) → ∀ (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg),
    CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) →
    (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal →
    ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg →
    CFSG.pCore 2 Hg ≤ ρ.ker →
    (∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom) →
    (∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg)) →
    ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker → IsFFModule ρ.range →
    Lin2Cover ↥(K₁.map ρ) →
    PairOutput ρ.range (K₁.map ρ) ((K₁.map (MulAut.conj t).toMonoidHom).map ρ)

section Action

variable {G : Type} [Group G] {V H : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def actV (hHN : H ≤ Subgroup.normalizer (V : Set G)) :
    ↥H →* MulAut (IntMod V hV) :=
  (convI hV).comp (Subgroup.inclusion hHN)

theorem actV_apply_val (hHN : H ≤ Subgroup.normalizer (V : Set G)) (h : ↥H) (v : IntMod V hV) :
    (actV hV hHN h v).val = (h : G) * v.val * (h : G)⁻¹ :=
  convI_apply_val hV (Subgroup.inclusion hHN h) v

theorem actV_eq_one_iff (hHN : H ≤ Subgroup.normalizer (V : Set G)) (h : ↥H) :
    actV hV hHN h = 1 ↔ (h : G) ∈ Subgroup.centralizer (V : Set G) :=
  convI_eq_one_iff hV (Subgroup.inclusion hHN h)

theorem map_actV (hHN : H ≤ Subgroup.normalizer (V : Set G)) {K : Subgroup G} (hKH : K ≤ H) :
    (K.subgroupOf H).map (actV hV hHN) = autI hV K := by
  ext φ
  rw [Subgroup.mem_map, mem_autI]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Subgroup.inclusion hHN x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨(g : G), hKH hg⟩ , Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem range_actV (hHN : H ≤ Subgroup.normalizer (V : Set G)) :
    (actV hV hHN).range = autI hV H := by
  rw [← Subgroup.map_top, ← Subgroup.subgroupOf_self H, map_actV hV hHN le_rfl]

end Action

end R3c23

end CFSG.Quasithin
