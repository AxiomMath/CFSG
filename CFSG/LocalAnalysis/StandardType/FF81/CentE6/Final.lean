module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.StandardType.FS81.HoltSimpleControl
public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Frame
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadTransport
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GFuse
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GQuotient
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GLift
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GFuseClass
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GCenLe
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XHolt
import CFSG.LocalAnalysis.StandardType.FF81.E6Position
import CFSG.LocalAnalysis.StandardType.FF81.PCoreE6

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.SeitzReduction CFSG.StandardType.GGSixE6Two
open CFSG.StandardType.FrameRoute.FS81 (HoltSimpleControl holtSimpleControl_holds)

theorem centralizer_le_of_e6Data
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (hchar : IsCharTwoType G) {n : ℕ} {b : G}
    {L : Subgroup G} (hA : HypA G n b L) {K : ℕ → Subgroup G} {t : G}
    (hup : Upstream n b L K t) (hYd : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t)
    (h5 : n = 5) (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ)))
    (hpos : ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = ⨆ i : Fin (n + 2), K (i : ℕ) ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L ∧ sTheta.map φ = K 0)
    (hQL : ((CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype ⊓ L = ⊥ ∧
      (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype ⊔ L =
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))))
    (h95 : ((CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G))).map
        (Subgroup.centralizer ({t} : Set G)).subtype =
      (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype))
    (hHolt : HoltSimpleControl) :
    Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ) := by
  classical
  set Y : Subgroup G := ⨆ i : Fin (n + 2), K (i : ℕ) with hY
  obtain ⟨φ, hφ, hrange, ht, hb, hL, -⟩ := hpos
  subst ht hb hL
  have F : E6Frame G n (φ zE) (lE.map φ) K (φ (xr (highRoot .E6))) :=
    ⟨hnonab, hchar, hA, hup, hYd, h5, hlab⟩
  set H : Subgroup G := Subgroup.centralizer ({φ (xr (highRoot .E6))} : Set G) with hH
  set Q : Subgroup G := (CFSG.pCore 2 ↥(H ⊓ Y)).map (H ⊓ Y).subtype with hQ
  have hQ' : Q = pCoreOf 2 (H ⊓ φ.range) := by
    rw [hrange]
    rfl
  have hQL' : Q ⊓ lE.map φ = ⊥ ∧ Q ⊔ lE.map φ = H ⊓ φ.range := by
    rw [hrange]
    exact hQL
  obtain ⟨eL, π, b', R0, c, hc⟩ := exists_radGeom_of_embedding φ hφ hQ' hQL'
  have hconj : ∃ y ∈ Y, y * φ zE * y⁻¹ = b' := by
    refine ⟨φ c, ?_, hc⟩
    rw [← hrange]
    exact ⟨c, rfl⟩
  have hfuse := exists_conj_of_isConj_mem_of_frame F R0 hconj
  have hQnorm : pCoreOf 2 H = Q := h95
  have hcen := centralizer_pair_le_sup F R0 hconj hQL.2 hQnorm
  let R : RadSetting (φ (xr (highRoot .E6))) Q (lE.map φ) eL π b' := ⟨R0, hfuse, hcen⟩
  have hN : (Q.subgroupOf H).Normal := by
    rw [← hQnorm]
    unfold pCoreOf
    rw [CFSG.subgroupOf_map_subtype_eq]
    exact CFSG.pCore_normal (p := 2) (G := ↥H)
  obtain ⟨S, hSL, hSe⟩ := exists_cubeSetting_quotient (hN := hN) R.toRadGeom
  have hC : ∀ c : ↥H ⧸ Q.subgroupOf H, c * S.z = S.z * c → c ∈ S.L :=
    fun c hz => mem_L_of_centralizes_z (hN := hN) R S hSL hSe c hz
  have htop : S.L = ⊤ := eq_top_of_cubeSetting hHolt S hC
  intro h hh
  have hmem : (QuotientGroup.mk ⟨h, hh⟩ : ↥H ⧸ Q.subgroupOf H) ∈ S.L := by
    rw [htop]
    trivial
  obtain ⟨l, hl⟩ := (hSL _).1 hmem
  have hq := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hl)
  have hq' : (l : G)⁻¹ * h ∈ Q := by simpa using hq
  have hmem2 : h ∈ Q ⊔ lE.map φ := by
    have h' : h = (l : G) * ((l : G)⁻¹ * h) := by group
    rw [h']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right l.2) (Subgroup.mem_sup_left hq')
  rw [hQL.2] at hmem2
  exact hmem2.2

theorem centralizer_le_of_e6Data_holds
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (hchar : IsCharTwoType G) {n : ℕ} {b : G}
    {L : Subgroup G} (hA : HypA G n b L) {K : ℕ → Subgroup G} {t : G}
    (hup : Upstream n b L K t) (hYd : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t)
    (h5 : n = 5) (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ)))
    (hpos : ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = ⨆ i : Fin (n + 2), K (i : ℕ) ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L ∧ sTheta.map φ = K 0)
    (hQL : ((CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype ⊓ L = ⊥ ∧
      (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype ⊔ L =
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))))
    (h95 : ((CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G))).map
        (Subgroup.centralizer ({t} : Set G)).subtype =
      (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))).map
        (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)).subtype)) :
    Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ) :=
  centralizer_le_of_e6Data hnonab hchar hA hup hYd h5 hlab hpos hQL h95 holtSimpleControl_holds

theorem centralizerE6_holds :
    CentralizerE6 := by
  intro G _ _ _ hnonab hchar n b L hA K t hup hYd h5 hlab
  have hpos := exists_e6Position_of_yData hA hup hYd h5 hlab
  have hQL :
      pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)) ⊓ L = ⊥ ∧
        pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ)) ⊔ L =
          Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    obtain ⟨φ, hφ, hrange, ht, -, hL, -⟩ := hpos
    rw [← ht, ← hL, ← hrange]
    exact pCoreOf_inf_eq_bot_and_sup_eq_of_embedding φ hφ
  exact centralizer_le_of_e6Data_holds hnonab hchar hA hup hYd h5 hlab hpos hQL
    (pCore_centralizer_eq_in_Y_of_e6 G hnonab hchar n b L hA K t hup hYd h5 hlab)

end CFSG.StandardType.FF81.CentE6
