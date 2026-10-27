module

public import CFSG.Quasithin.Background.CentSecConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiTorus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section ChiefAux

variable {Y : Type} [CommGroup Y]

theorem chief_perfect_fixes {X : Subgroup (MulAut Y)} (hX : commutator ↥X = ⊤) {w : Y}
    (hw : ∀ x ∈ X, x w * w⁻¹ ∈ fixV X) : ∀ x ∈ X, x w = w := by
  let φ : ↥X →* Y :=
    { toFun := fun x => (x : MulAut Y) w * w⁻¹
      map_one' := by simp
      map_mul' := fun x₁ x₂ => by
        have h2 : (x₁ : MulAut Y) ((x₂ : MulAut Y) w * w⁻¹) = (x₂ : MulAut Y) w * w⁻¹ :=
          hw x₂ x₂.2 x₁ x₁.2
        rw [map_mul, map_inv] at h2
        have h3 : (x₁ : MulAut Y) ((x₂ : MulAut Y) w) =
            (x₂ : MulAut Y) w * w⁻¹ * (x₁ : MulAut Y) w := by
          rw [← mul_inv_eq_iff_eq_mul]
          exact h2
        show (x₁ : MulAut Y) ((x₂ : MulAut Y) w) * w⁻¹ = _
        rw [h3]
        ac_rfl }
  have hker : commutator ↥X ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hX] at hker
  intro x hx
  have := hker (Subgroup.mem_top (⟨x, hx⟩ : ↥X))
  rw [MonoidHom.mem_ker] at this
  exact mul_inv_eq_one.1 this

theorem chief_quasi_normal_le_center_or_eq_top {H : Type*} [Group H]
    (hH : CFSG.Open.IsQuasisimple H) {N : Subgroup H} (hN : N.Normal) :
    N ≤ Subgroup.center H ∨ N = ⊤ := by
  obtain ⟨hp, hs⟩ := hH
  have := hN.map (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center H))) with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have hsup : N ⊔ Subgroup.center H = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center H)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center H, Subgroup.center H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup H).map (QuotientGroup.mk' N) =
        (Subgroup.center H).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator H ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem chief_commutator_self {G : Type*} [Group G] {A : Subgroup G} (hA : commutator ↥A = ⊤) :
    ⁅A, A⁆ = A :=
  Subgroup.isPerfect_iff.1 ⟨hA⟩

theorem chief_centSec_conj_mem {I J : Subgroup Y} {g c : MulAut Y} (hgI : g ∈ stabSub I)
    (hgJ : g ∈ stabSub J) (hc : c ∈ centSec I J) : g * c * g⁻¹ ∈ centSec I J :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hgI hgJ hc

theorem chief_comm_mem_centSec {I J : Subgroup Y} {x a : MulAut Y} (hxI : x ∈ stabSub I)
    (hxJ : x ∈ stabSub J) (ha : a ∈ centSec I J) : ⁅x, a⁆ ∈ centSec I J := by
  rw [commutatorElement_def]
  exact (centSec I J).mul_mem (chief_centSec_conj_mem hxI hxJ ha) ((centSec I J).inv_mem ha)

theorem chief_faithful_aux {X A : Subgroup (MulAut Y)} {I J : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥X) (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y)))
    (hnt : ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) :
    ∀ a ∈ A ⊓ centSec I J, ∀ x ∈ X, a * x = x * a := by
  set N : Subgroup ↥X := (centSec I J).subgroupOf X with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := chief_centSec_conj_mem (hXI g.2) (hXJ g.2) hn
    simpa using this⟩
  rcases chief_quasi_normal_le_center_or_eq_top hq hNn with hZ | htop
  · have hcomm : ⁅X, A ⊓ centSec I J⁆ ≤ Subgroup.centralizer (X : Set (MulAut Y)) := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      have h1 : ⁅x, a⁆ ∈ X := by
        have h0 : a * x⁻¹ * a⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.1 (hAX ha.1) x⁻¹).1 (X.inv_mem hx)
        have := X.mul_mem hx h0
        simpa [commutatorElement_def, mul_assoc] using this
      have h2 : ⁅x, a⁆ ∈ centSec I J := chief_comm_mem_centSec (hXI hx) (hXJ hx) ha.2
      have h3 : (⟨⁅x, a⁆, h1⟩ : ↥X) ∈ N := Subgroup.mem_subgroupOf.2 h2
      have h4 := hZ h3
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h4 ⟨y, hy⟩)
    have hrot : ⁅⁅X, X⁆, A ⊓ centSec I J⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hcomm
      · rw [Subgroup.commutator_comm (A ⊓ centSec I J) X,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hcomm
    rw [chief_commutator_self hq.1] at hrot
    intro a ha x hx
    have : ⁅x, a⁆ ∈ ⁅X, A ⊓ centSec I J⁆ := Subgroup.commutator_mem_commutator hx ha
    rw [hrot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · exfalso
    obtain ⟨x, hx, w, hw, hne⟩ := hnt
    have : (⟨x, hx⟩ : ↥X) ∈ N := htop ▸ Subgroup.mem_top _
    exact hne ((Subgroup.mem_subgroupOf.1 this).2 w hw)

end ChiefAux

end CFSG.Quasithin
