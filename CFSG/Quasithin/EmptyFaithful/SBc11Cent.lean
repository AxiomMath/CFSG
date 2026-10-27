module

public import CFSG.Quasithin.EmptyFaithful.SBc11Ctx
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc11

section Center

variable {X Y : Type} [Group X] [Group Y]

theorem center_le_ker_of_center_eq_bot (ψ : X →* Y) (hψs : Function.Surjective ψ)
    (hcen : Subgroup.center Y = ⊥) : Subgroup.center X ≤ ψ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hz' : ψ z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hψs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hcen] at hz'
  exact hz'

end Center

section Generic

variable {G : Type} [Group G]

theorem centralizer_le_centralizer_blockU {L UI : Subgroup G} (hshort : IsShort2 L)
    (hperf : ⁅L, L⁆ = L) (hUIc : ∀ x ∈ UI, ∀ y ∈ UI, x * y = y * x) (hUI2 : IsPGroup 2 ↥UI)
    (hLUI : L ≤ Subgroup.normalizer (UI : Set G)) (hUIL : UI ≤ Subgroup.normalizer (L : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (UI : Set G)) :
    L ⊓ Subgroup.centralizer (UI : Set G) ≤ Subgroup.centralizer (blockU L : Set G) := by
  have hWUI : ⁅UI, L⁆ ≤ UI := Subgroup.le_normalizer_iff_commutator_le_left.mp hLUI
  have hWL : ⁅UI, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hUIL
  have hLW : L ≤ Subgroup.normalizer ((⁅UI, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hLUI hg) (Subgroup.le_normalizer hg)
  have hW2 : IsPGroup 2 ↥(⁅UI, L⁆ : Subgroup G) := hUI2.to_le hWUI
  have hWQ : ⁅UI, L⁆ ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hWL hLW hW2
  have hWW : ⁅⁅UI, L⁆, L⁆ = ⁅UI, L⁆ := SBd5.commutator_commutator_eq_self hperf hLUI hUIc
  have hWU : ⁅UI, L⁆ ≤ blockU L := by
    calc ⁅UI, L⁆ = ⁅⁅UI, L⁆, L⁆ := hWW.symm
      _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono_left hWQ
  have hWbot : ⁅UI, L⁆ ≠ ⊥ := fun h => hnt (by
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hZLc : blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have hLZ : L ≤ Subgroup.normalizer ((blockZ L : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    have : ⁅blockZ L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZLc
    rw [Subgroup.commutator_comm, this]
    exact bot_le
  have hLN : L ≤ Subgroup.normalizer ((⁅UI, L⁆ ⊔ blockZ L : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hLW hg),
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hLZ hg)]
  have hN : ⁅UI, L⁆ ⊔ blockZ L = blockU L := by
    rcases hshort.2.2.2.2.2 (⁅UI, L⁆ ⊔ blockZ L) le_sup_right
        (sup_le hWU inf_le_left) hLN with h | h
    · exfalso
      apply hWbot
      have hWZ : ⁅UI, L⁆ ≤ blockZ L := h ▸ le_sup_left
      have h0 : ⁅⁅UI, L⁆, L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hWZ.trans hZLc)
      rw [← hWW]
      exact h0
    · exact h
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  have hK : blockU L ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hN]
    refine sup_le (fun w hw => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hx.2 w (hWUI hw)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp (hZLc hz) y hx.1
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (hK hh) x (Set.mem_singleton x)).symm

end Generic

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem centralizer_UI_eq_pCoreOf_of_ker_eq_bot (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(Star153 T I L)}
    (hψ1 : ∀ l : ↥L, ψ (QuotientGroup.mk l) = 1 ↔ (l : G) ∈ Subgroup.centralizer (UI153 T I : Set G))
    (hψk : ψ.ker = ⊥) :
    L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L := by
  apply le_antisymm
  · rintro l ⟨hl, hlc⟩
    have h1 : ψ (QuotientGroup.mk ⟨l, hl⟩) = 1 := (hψ1 ⟨l, hl⟩).2 hlc
    have h2 : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := h1
    rw [hψk, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h2
    exact (CFSG.QuasithinUnique.AppC.mem_pCore_iff_mem_blockQ (⟨l, hl⟩ : ↥L)).1 h2
  · exact le_inf (pCoreOf_le 2 L) (ctx_star c).2.1

theorem centralizer_UI_eq_pCoreOf_of_simple (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L := by
  obtain ⟨ψ, -, -, hψ1⟩ := exists_star_hom c
  have hnt := (ctx_star c).2.2
  refine centralizer_UI_eq_pCoreOf_of_ker_eq_bot c hψ1 ?_
  rcases hs.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact h
  · exfalso
    apply hnt
    intro l hl
    have h2 : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by
      rw [h]
      trivial
    exact (hψ1 ⟨l, hl⟩).1 h2

theorem centralizer_UI_eq_pCoreOf_of_altBlock (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (h : IsAltBlockType L 6) : L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L := by
  obtain ⟨-, α, hαs, hαk, -⟩ := h
  refine centralizer_UI_eq_pCoreOf_of_simple c ?_
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))

theorem centralizer_UI_eq_pCoreOf_of_g2Block (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (h : IsG2Block L) : L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L := by
  obtain ⟨-, hpsu, -⟩ := h
  exact centralizer_UI_eq_pCoreOf_of_simple c
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hpsu).2

end Ctx

end SBc11

end CFSG.Quasithin
