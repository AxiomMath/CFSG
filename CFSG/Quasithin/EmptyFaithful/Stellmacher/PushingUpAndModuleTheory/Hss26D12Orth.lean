module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Core

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CFSG.Quasithin.F53Mod CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem le_of_isSylowTwoOf_of_le {B K U : Subgroup G} (hB : IsSylowTwoOf B U) (hBK : B ≤ K)
    (hKU : K ≤ U) (hK : IsPGroup 2 ↥K) : K ≤ B := by
  have h1 := Subgroup.relIndex_mul_relIndex B K U hBK hKU
  have hodd : ¬ 2 ∣ B.relIndex U := hB.2.2
  obtain ⟨k, hk⟩ := hK.index (B.subgroupOf K)
  have hk' : B.relIndex K = 2 ^ k := hk
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd ((dvd_pow_self 2 hk0).trans (hk' ▸ Dvd.intro _ h1))
  rw [hk0, pow_zero] at hk'
  exact Subgroup.relIndex_eq_one.mp hk'

omit [Finite G] in
theorem mem_normalizer_centralizer {g : G} {W : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ Subgroup.centralizer (W : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro g hg x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set G)).inv_mem hg) w).mp hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (W : Set G)).inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem normalizer_le_normalizer_baum (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer ((baum R : Subgroup G) : Set G) := by
  intro g hg
  have hJ := normalizer_le_normalizer_thompsonJ R hg
  have hW := A4.normalizer_le_normalizer_omegaOneCenterOf _ hJ
  have hC := mem_normalizer_centralizer hW
  unfold baum
  exact mem_normalizer_inf_of hg hC

namespace SitSigma

variable {δ μ : Geo H M} {U : Subgroup G}

theorem sitSigma_of_pu4 {U₀ : Subgroup G} (hA : F53Amalgam H M S)
    (hb : 1 < bMin H M) (h : SitSigma δ μ U) (hQ : Qv μ ≤ U) (hU₀ : U₀ ≤ U)
    (hsyl : IsSylowTwoOf (baum (Qv μ ⊓ U)) U₀) (hUS : U₀ ⊔ (Qv μ ⊓ U) = U) :
    SitSigma δ μ U₀ ∧ Qv μ ⊓ U₀ = baum (Qv μ) := by
  have hP : Qv μ ⊓ U = Qv μ := inf_eq_left.mpr hQ
  have hQE : Qv μ ≤ stab δ ⊓ stab μ := by
    have := h.P_le_edge hA
    rwa [hP] at this
  rw [hP] at hsyl hUS
  set B := baum (Qv μ) with hBdef
  have hBQ : B ≤ Qv μ := inf_le_left
  have hBU₀ : B ≤ U₀ := hsyl.1
  have hK2 : IsPGroup 2 ↥(Qv μ ⊓ U₀) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab μ)).to_le inf_le_left
  have hKB : Qv μ ⊓ U₀ ≤ B := le_of_isSylowTwoOf_of_le hsyl (le_inf hBQ hBU₀) inf_le_right hK2
  have hKeq : Qv μ ⊓ U₀ = B := le_antisymm hKB (le_inf hBQ hBU₀)
  have hZB : Zv μ ≤ B := by
    intro z hz
    refine ⟨Zv_le_Qv hA μ hz, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hwJ := (omegaOneCenterOf_le_inf (thompsonJ (Qv μ)) hw).1
    have hwQ : w ∈ Qv μ := F53Push.thompsonJ_le_self (Qv μ) hwJ
    exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2 w hwQ
  have hZδ : Zv μ ≤ Qv δ := by
    refine Zv_le_Qv_of_dist_lt ?_
    have : CosetGeom.dist μ δ = 1 := dist_eq_one_iff_adj.mpr h.adj.symm
    have := bMin_le_bAt μ
    omega
  refine ⟨⟨h.adj, hU₀.trans h.le_stab, ?_, ?_, ?_⟩, hKeq⟩
  · rw [hKeq]; exact hsyl
  · exact fun z hz => pCoreOf_inf_le (hU₀.trans h.le_stab) ⟨hZδ hz, hBU₀ (hZB hz)⟩
  · refine le_antisymm (sup_le (hU₀.trans h.le_stab) inf_le_left) ?_
    have hU : U ≤ U₀ ⊔ (stab δ ⊓ stab μ) := by
      rw [← hUS]
      exact sup_le_sup_left hQE _
    calc stab δ = U ⊔ (stab δ ⊓ stab μ) := h.gen.symm
      _ ≤ U₀ ⊔ (stab δ ⊓ stab μ) := sup_le hU le_sup_right

omit [Finite G] in
theorem relIndex_pCoreOf_eq (U : Subgroup G) :
    (pCoreOf 2 U).relIndex U = Nat.card (OTwoQuot U) := by
  have h : (pCoreOf 2 U).subgroupOf U = CFSG.Open.pCore 2 ↥U := by
    unfold pCoreOf
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  unfold Subgroup.relIndex
  rw [h]
  rfl

theorem not_Qv_le_of_orth (hA : F53Amalgam H M S) (h : SitSigma δ μ U) (hQ : Qv μ ≤ U)
    (hR : pCoreOf 2 U ≤ Qv δ) (hq5 : Nonempty (OTwoQuot U ≃* Perm (Fin 5))) :
    ¬ Qv δ ≤ Qv μ := by
  intro hle
  have hP : Qv μ ⊓ U = Qv μ := inf_eq_left.mpr hQ
  have hRδ : pCoreOf 2 U = Qv δ := le_antisymm hR
    (fun x hx => h.inf_Qv_le_R ⟨hQ (hle hx), hx⟩)
  have hRQ : pCoreOf 2 U ≤ Qv μ := by
    have := h.R_le_P
    rwa [hP] at this
  have hcard : Nat.card (OTwoQuot U) = 120 := by
    obtain ⟨e⟩ := hq5
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 U) (Qv μ) U hRQ hQ
  rw [relIndex_pCoreOf_eq, hcard] at hmul
  have hodd : ¬ 2 ∣ (Qv μ).relIndex U := by
    have := h.sylow.2.2
    rwa [hP] at this
  have hQ2 : IsPGroup 2 ↥(Qv μ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab μ)
  obtain ⟨k, hk⟩ := hQ2.index ((pCoreOf 2 U).subgroupOf (Qv μ))
  have hk' : (pCoreOf 2 U).relIndex (Qv μ) = 2 ^ k := hk
  rw [hk'] at hmul
  have h8 : (pCoreOf 2 U).relIndex (Qv μ) = 8 := by
    have hk7 : k < 7 := by
      by_contra hk7
      have h1 : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk7)
      have h2 : 2 ^ k ≤ 120 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
      omega
    rw [hk']
    interval_cases k <;> omega
  rw [hRδ] at h8
  obtain ⟨hv, hE3, hEμ2⟩ : vtype δ = false ∧ _ ∧ (Qv μ).relIndex (stab δ ⊓ stab μ) = 2 := by
    have hQE := relIndex_Qv_inf_mul hA h.adj
    cases hvδ : vtype δ with
    | true =>
      have h2 := relIndex_Qv_inf_true hA h.adj hvδ
      have hQμE : Qv μ ≤ stab δ ⊓ stab μ := by
        have := h.P_le_edge hA
        rwa [hP] at this
      have hQδE : Qv δ ≤ Qv μ := hle
      have := Subgroup.relIndex_mul_relIndex (Qv δ) (Qv μ) (stab δ ⊓ stab μ) hQδE hQμE
      have hpos : (Qv μ).relIndex (stab δ ⊓ stab μ) ≠ 0 := relIndex_ne_zero_fin _ _
      rw [h2, h8] at this
      omega
    | false => exact ⟨rfl, trivial, (relIndex_edge_stab_true hA h.adj hvδ).2.2⟩
  have hQμE : Qv μ ≤ stab δ ⊓ stab μ := by
    have := h.P_le_edge hA
    rwa [hP] at this
  have := Subgroup.relIndex_mul_relIndex (Qv δ) (Qv μ) (stab δ ⊓ stab μ) hle hQμE
  rw [relIndex_Qv_inf_false hA h.adj hv, h8, hEμ2] at this
  omega

theorem false_of_orth (hA : F53Amalgam H M S) (hb : 1 < bMin H M) (h : SitSigma δ μ U)
    (hQ : Qv μ ≤ U) (hR : pCoreOf 2 U ≤ Qv δ)
    (hq5 : Nonempty (OTwoQuot U ≃* Perm (Fin 5)))
    (hO : IsOrthSec U (zZero U (conjJoinOf U (quasithinOmegaOneCenter (Qv μ))))
      (conjJoinOf U (quasithinOmegaOneCenter (Qv μ)))) : False := by
  have hPn := SitSigma.stab_le_normalizer_of_le hQ
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hP0 : Qv μ ⊓ U ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ U := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  have hJ := not_le_core_of_noCharNormal hPH hP0 hnc
  have hZ : conjJoinOf U (quasithinOmegaOneCenter (Qv μ)) =
      CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U := by
    rw [inf_eq_left.mpr hQ, conjClosure_eq_conjJoin]
    rfl
  rw [hZ] at hO
  obtain ⟨U₀, hU₀U, hsyl, hquot, hUS⟩ := pu4_orthogonal hPH hq5 inf_le_left hO hJ
  obtain ⟨h₀, hKeq⟩ := h.sitSigma_of_pu4 hA hb hQ hU₀U hsyl hUS
  have hPn₀ : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ U₀ : Subgroup G) : Set G) := by
    rw [hKeq]
    exact fun g hg => normalizer_le_normalizer_baum (Qv μ)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ) hg)
  by_cases hR₀ : pCoreOf 2 U₀ ≤ Qv δ
  · exact h₀.false_of_S3 (baumannS3_holds G) hA hPn₀ hR₀ hquot
  · exact h₀.false_of_D12 (baumannS3_holds G) hA hPn₀ hR₀
      (h.not_Qv_le_of_orth hA hQ hR hq5) hquot

end SitSigma

end CFSG.Quasithin.F53
