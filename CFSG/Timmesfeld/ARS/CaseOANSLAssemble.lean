module

public import CFSG.Timmesfeld.ARS.CaseOANSLCenter

public section

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

namespace CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOANSL

open ExclNS (memberRoots memberRoots_subset weylAction_mem_memberRoots neg_mem_memberRoots
  map_rootGroup_mem opposite_map_rootGroup)

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)}

section Lift

@[expose] noncomputable def liftEquiv (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) :
    CompBar Δ₁ ≃* ↥(gen Δ₁) :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem liftEquiv_mk (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) (v : ↥(gen Δ₁)) :
    liftEquiv hZ (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v) = v := rfl

theorem mk_liftEquiv (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) (x : CompBar Δ₁) :
    QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) (liftEquiv hZ x) = x := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [liftEquiv_mk]

theorem map_liftEquiv_quotMap (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) {X : Subgroup G}
    (hX : X ≤ gen Δ₁) :
    ((quotMap (gen Δ₁) X).map (liftEquiv hZ).toMonoidHom).map (gen Δ₁).subtype = X := by
  rw [quotMap, Subgroup.map_map, Subgroup.map_map]
  have e : (((gen Δ₁).subtype.comp (liftEquiv hZ).toMonoidHom).comp
      (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)))) = (gen Δ₁).subtype := by
    ext v
    rfl
  rw [e, Subgroup.subgroupOf_map_subtype, inf_of_le_left hX]

@[expose] noncomputable def liftHom {K : Type*} [Group K] (hZ : Subgroup.center ↥(gen Δ₁) = ⊥)
    (Ψ : K →* CompBar Δ₁) : K →* G :=
  (gen Δ₁).subtype.comp ((liftEquiv hZ).toMonoidHom.comp Ψ)

theorem liftHom_mem {K : Type*} [Group K] (hZ : Subgroup.center ↥(gen Δ₁) = ⊥)
    (Ψ : K →* CompBar Δ₁) (k : K) : liftHom hZ Ψ k ∈ gen Δ₁ :=
  ((liftEquiv hZ).toMonoidHom.comp Ψ k).2

theorem map_liftHom {K : Type*} [Group K] (hZ : Subgroup.center ↥(gen Δ₁) = ⊥)
    (Ψ : K →* CompBar Δ₁) {Y : Subgroup K} {X : Subgroup G} (hX : X ≤ gen Δ₁)
    (hXY : quotMap (gen Δ₁) X = Y.map Ψ) : Y.map (liftHom hZ Ψ) = X := by
  rw [← map_liftEquiv_quotMap hZ hX, hXY, liftHom, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem range_liftHom {K : Type*} [Group K] (hZ : Subgroup.center ↥(gen Δ₁) = ⊥)
    {Ψ : K →* CompBar Δ₁} (hΨ : Function.Surjective Ψ) : (liftHom hZ Ψ).range = gen Δ₁ := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨k, rfl⟩
    exact liftHom_mem hZ Ψ k
  · obtain ⟨k, hk⟩ := hΨ ((liftEquiv hZ).symm ⟨x, hx⟩)
    refine ⟨k, ?_⟩
    simp [liftHom, hk]

end Lift

section Data

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2)
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne

theorem exists_frame_data (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) :
    ∃ hn : 3 ≤ F.D.rank, ∃ B C X₀ Y₀ : Subgroup G,
      (F.D.cartan = Spin.cartanB F.D.rank ∨ F.D.cartan = Symplectic.cartanC F.D.rank) ∧
      Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ memberRoots F ∧
      B ∈ lambdaStar R A A₀ ∧ C ∈ lambdaStar R A A₀ ∧ ⁅A₀, C⁆ ∈ lambdaStar R A₀ A ∧
      Opposite B ⁅A₀, C⁆ ∧ X₀ ∈ Δ₁ ∧ Y₀ ∈ Δ₁ ∧ Opposite X₀ Y₀ ∧
      quotMap (gen Δ₁) X₀ =
        (F.D.rootGroup (Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1)).map F.Ψ ∧
      quotMap (gen Δ₁) Y₀ =
        (F.D.rootGroup (-Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1)).map F.Ψ ∧
      EdgeRel R P₂ B Q₂ ⁅A₀, C⁆ ∧ EdgeRel R B X₀ ⁅A₀, C⁆ Y₀ ∧
      ∀ β ∈ F.D.roots, β ⟨0, by omega⟩ = 0 →
        (F.D.rootGroup β).map F.Ψ ≤ stabBar₁ Δ₁ B ∧ (F.D.rootGroup β).map F.Ψ ≤ stabBar₁ Δ₁ C := by
  have := h.finite
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  obtain ⟨hCt, hn, -, B₀, hB₀, h0₀, hns₀, hT₀⟩ :=
    exists_attach h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F
  obtain ⟨P⟩ : Nonempty (ExclNS.EpsCoords F.D.cartan) := by
    rcases hCt with hCt | hCt
    · exact ⟨hCt ▸ ExclNS.epsB F.D.rank⟩
    · exact ⟨hCt ▸ ExclNS.epsC F.D.rank⟩
  obtain ⟨g, hg, hgQ⟩ :=
    exists_conjSub_commuting_of_mem₂ h hA hAne hA₀ hΔ₂ hB₀.mem hP₂ hQ₂
  set B := conjSub B₀ g with hBdef
  have hB : LowMember₁ R A A₀ Δ₁ F B := hB₀.conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne hg
  have hS : lowSet₁ R A A₀ Δ₁ F B = lowSet₁ R A A₀ Δ₁ F B₀ :=
    lowSet₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne F B₀ hg
  have hstab : stabBar₁ Δ₁ B = stabBar₁ Δ₁ B₀ :=
    stabBar₁_conjSub_of_mem_gen₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne B₀ hg
  have h0 : -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ lowSet₁ R A A₀ Δ₁ F B := hS ▸ h0₀
  have hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar₁ Δ₁ B :=
    fun s hs => hstab ▸ hns₀ s hs
  have hT : (⨆ i, F.H i).map F.Ψ ≤ stabBar₁ Δ₁ B := hstab ▸ hT₀
  obtain ⟨-, -, -, C, hC, hsBC, hBCA, hCP₂, hsCQ₂, hCX₀, hsCY₀, -, -, -, hCJ⟩ :=
    hB.exists_highest h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne P (by omega) hns hT h0 hP₂ hQ₂ hPQ₂
      hgen₂ hgQ
  have hα₀O : Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1 ∈ memberRoots F := by
    have := neg_mem_memberRoots F h0.1
    rwa [neg_neg] at this
  obtain ⟨X₀, hX₀, hX₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hα₀O
  obtain ⟨Y₀, hY₀, hY₀q⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ h0.1
  have hBY₀ := hB.mem_lambdaSet_of_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hY₀ hY₀q
  have hsBX₀ := hB.special_of_neg_mem_lowSet h hA hAne hA₀ hΔ₁ h0 hX₀ hX₀q
  have hopp₀ : Opposite X₀ Y₀ := by
    refine opposite_of_quot₁ h hA hAne hA₀ hΔ₁ hX₀ hY₀ ?_
    rw [hX₀q, hY₀q]
    exact opposite_map_rootGroup F hα₀O
  obtain ⟨hBQ₂, hsPB⟩ := CaseOA.natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hB.mem hgQ
  obtain ⟨hF', -, -, hFlevi⟩ := CaseD4.commutator_props h hA hA₀ hC
  have hBF' : Opposite B ⁅A₀, C⁆ := CaseOA.opposite_of_extremal h hA hA₀ hB.mem hC hsBC hBCA
  have e0 : EdgeRel R P₂ B Q₂ ⁅A₀, C⁆ := CaseOA.edgeRel_of_extremal h hA hAne hA₀ (hl₂ hP₂)
    (hl₂ hQ₂) hPQ₂ hB.mem hC hBQ₂ hsPB.symm hCP₂ hsCQ₂ hsBC hBCA
  have e2 : EdgeRel R X₀ B Y₀ ⁅A₀, C⁆ := CaseOA.edgeRel_of_extremal h hA hAne hA₀ (hl₁ hX₀)
    (hl₁ hY₀) hopp₀ hB.mem hC hBY₀ hsBX₀ (hCX₀ X₀ hX₀ hX₀q) (hsCY₀ Y₀ hY₀ hY₀q) hsBC hBCA
  refine ⟨hn, B, C, X₀, Y₀, hCt, hα₀O, hB.mem, hC, hF', hBF', hX₀, hY₀, hopp₀, hX₀q, hY₀q, e0,
    e2.symm, fun β hβ hβ0 => ⟨hB.map_rootGroup_le_of_apply_zero (by omega) hns hT hβ hβ0,
      hCJ β hβ hβ0⟩⟩

theorem conjSub_liftHom_eq (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) {K : Type*} [Group K]
    (Ψ : K →* CompBar Δ₁) {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) {k : K}
    (hk : Ψ k ∈ stabBar₁ Δ₁ D) : conjSub D (liftHom hZ Ψ k) = D := by
  refine conjSub_eq_self_iff.2 ((mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hD
    (liftEquiv hZ (Ψ k))).1 ?_)
  rw [mk_liftEquiv]
  exact hk

theorem commute_liftHom_of_mem (hZ : Subgroup.center ↥(gen Δ₁) = ⊥) {K : Type*} [Group K]
    (Ψ : K →* CompBar Δ₁) {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) {X : Subgroup G}
    (hX : X ∈ Δ₁) {Y : Subgroup K} (hXY : quotMap (gen Δ₁) X = Y.map Ψ)
    (hle : Y.map Ψ ≤ stabBar₁ Δ₁ D) {y : K} (hy : y ∈ Y) :
    ∀ d ∈ D, Commute (liftHom hZ Ψ y) d := by
  have hXD := (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hD hX).2
    (hXY ▸ hle)
  have hyX : liftHom hZ Ψ y ∈ X := by
    rw [← map_liftHom hZ Ψ (le_gen hX) hXY]
    exact ⟨y, hy, rfl⟩
  exact fun d hd => hXD _ hyX d hd

end Data

end CaseOANSL

end CFSG.Timmesfeld.ARS
