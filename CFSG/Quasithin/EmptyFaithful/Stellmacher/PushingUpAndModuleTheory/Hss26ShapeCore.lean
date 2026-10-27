module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18A5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SitSigma

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CosetGeom
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conjClosure_eq_conjJoin (Z X : Subgroup G) :
    CFSG.Quasithin.conjClosure Z X = F53Push.conjJoin X Z := by
  apply le_antisymm
  · refine CFSG.Quasithin.conjClosure_le fun h hh z hz => ?_
    refine F53Push.cj_le_conjJoin (J := Z) hh ?_
    rw [F53Push.mem_cj]
    simpa [mul_assoc] using hz
  · refine F53Push.conjJoin_le fun g hg x hx => ?_
    rw [F53Push.mem_cj] at hx
    have := CFSG.Quasithin.mem_conjClosure (Z := Z) (H := X) hg hx
    simpa [mul_assoc] using this

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

theorem Zv_le_omegaOneCenter (hA : F53Amalgam H M S) (h : SitSigma δ μ X) :
    Zv μ ≤ quasithinOmegaOneCenter (Qv μ ⊓ X) := by
  intro z hz
  refine Subgroup.subset_closure ⟨⟨h.R_le_P (h.zle hz), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2 y hy.1))
  · have := (isElemAbelian_Zv hA μ).2 z hz
    exact this

theorem pushHyp (hA : F53Amalgam H M S) (h : SitSigma δ μ X) :
    PushHyp X (Qv μ ⊓ X) (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X) := by
  have hTodd : ¬ 2 ∣ (Qv μ ⊓ X).relIndex X := h.sylow.2.2
  obtain ⟨hle, hel⟩ := CFSG.Quasithin.conjClosure_le_centerOf_pCoreOf_of_sylowIn
    (inf_le_right : Qv μ ⊓ X ≤ X) h.sylow.2.1 hTodd (h.centralizer_le_R hA)
    (Z := quasithinOmegaOneCenter (Qv μ ⊓ X)) le_rfl
  refine ⟨h.sylow, CFSG.Quasithin.le_normalizer_conjClosure _ _, hel, hle.trans inf_le_left, ?_⟩
  exact h.centralizer_eq_R hA (CFSG.Quasithin.le_normalizer_conjClosure _ _)
    ((h.Zv_le_omegaOneCenter hA).trans (CFSG.Quasithin.le_conjClosure _ _)) hle

theorem Zv_le_conjClosure (hA : F53Amalgam H M S) (h : SitSigma δ μ X) :
    Zv μ ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X :=
  (h.Zv_le_omegaOneCenter hA).trans (CFSG.Quasithin.le_conjClosure _ _)

theorem noCharNormal (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G)) :
    NoCharNormal (Qv μ ⊓ X) X := by
  intro C hCP hC0 hCchar hXC
  have : (C.subgroupOf (Qv μ ⊓ X)).Characteristic := hCchar
  have hK : X ≤ Subgroup.normalizer
      (((C.subgroupOf (Qv μ ⊓ X)).map (Qv μ ⊓ X).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.map_subgroupOf_eq_of_le hCP]; exact hXC
  have := h.eq_bot_of_characteristic hA hPn (C.subgroupOf (Qv μ ⊓ X)) hK
  apply hC0
  rw [← Subgroup.map_subgroupOf_eq_of_le hCP, this, Subgroup.map_bot]

theorem pCore_eq (h : SitSigma δ μ X) (hRQ : pCoreOf 2 X ≤ Qv δ) :
    pCoreOf 2 X = (Qv μ ⊓ X) ⊓ Qv δ :=
  le_antisymm (le_inf (h.R_le_P) hRQ)
    (fun _ hx => h.inf_Qv_le_R ⟨hx.1.2, hx.2⟩)

theorem edge_le_normalizer_core (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hRQ : pCoreOf 2 X ≤ Qv δ) :
    stab δ ⊓ stab μ ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
  rw [h.pCore_eq hRQ]
  intro g hg
  have h1 := hPn hg.2
  have h2 : g ∈ Subgroup.normalizer (Qv δ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) hg.1
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro x
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩,
    fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

theorem odd_relIndex_normalizer_core (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hRQ : pCoreOf 2 X ≤ Qv δ) :
    Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ stab μ).relIndex (stab μ)) := by
  have hS := sylow_stab_inf_right hA h.adj
  have hle : stab δ ⊓ stab μ ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ stab μ :=
    le_inf (h.edge_le_normalizer_core hPn hRQ) inf_le_right
  have hdvd := Subgroup.relIndex_dvd_of_le_left (stab μ) hle
  have hodd : ¬ 2 ∣ (Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ stab μ).relIndex (stab μ) :=
    fun hd => hS.2.2 (hd.trans hdvd)
  exact Nat.odd_iff.mpr (by omega)

theorem false_of_cor (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    {Z : Subgroup G} (hZ : Zv μ ≤ Z) (hC : Cor42Concl X Z (stab μ)) : False := by
  have hμ : μ ∈ nbrs δ := h.adj
  have hSgm : stab μ ≤ Subgroup.normalizer (conjJoinOf (stab μ) Z : Set G) :=
    F53Push.le_normalizer_conjJoin (stab μ) Z
  have hSgd : stab δ ≤ Subgroup.normalizer (conjJoinOf (stab μ) Z : Set G) := by
    rw [← h.gen]
    exact sup_le hC.2 (inf_le_right.trans hSgm)
  have hle : conjJoinOf (stab μ) Z ≤ stab δ ⊓ stab μ :=
    hC.1.trans ((h.R_le_P).trans (h.P_le_edge hA))
  have hbot := eq_bot_of_normalizes_both hA hμ hle hSgd hSgm
  have : Zv μ ≤ ⊥ := hbot ▸ (hZ.trans (F53Push.le_conjJoin (X := stab μ) (J := Z)))
  exact Zv_ne_bot hA μ (le_bot_iff.mp this)

theorem false_of_S3 (hBau : BaumannS3 G) (hA : F53Amalgam H M S)
    (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hRQ : pCoreOf 2 X ≤ Qv δ) (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) : False := by
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  exact h.false_of_cor hA (h.Zv_le_conjClosure hA)
    (cor42S3P G _ _ _ (stab μ) hPH he hnc (hBau _ _ _ hPH he hnc) hPn
      (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
      (h.odd_relIndex_normalizer_core hA hPn hRQ))

theorem false_of_A5 (hBau : BaumannA5 G)
    (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hRQ : pCoreOf 2 X ≤ Qv δ)
    (he : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5)))) : False := by
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hP0 : Qv μ ⊓ X ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ X := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  have hJ := not_le_core_of_noCharNormal hPH hP0 hnc
  have hnat := hss18A5_holds G _ _ _ hPH he hJ
  exact h.false_of_cor hA (h.Zv_le_conjClosure hA)
    (cor42A5P G _ _ _ (stab μ) hPH he hnat hnc (hBau _ _ _ hPH he hnat hnc) hPn
      (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
      (h.odd_relIndex_normalizer_core hA hPn hRQ))

end SitSigma

end CFSG.Quasithin.F53
