module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Reduction
public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

structure SitSigma (δ μ : Geo H M) (U : Subgroup G) : Prop where
  adj : (graph (H ⊔ M) H M).Adj δ μ
  le_stab : U ≤ stab δ
  sylow : IsSylowTwoOf (Qv μ ⊓ U) U
  zle : Zv μ ≤ pCoreOf 2 U
  gen : U ⊔ (stab δ ⊓ stab μ) = stab δ

theorem false_of_odd_normalizes_gen (hA : F53Amalgam H M S) {δ μ : Geo H M} (hμ : μ ∈ nbrs δ)
    {U P : Subgroup G} (hP : IsSylowTwoOf P U) (hPμ : P ≤ stab μ)
    (hgen : U ⊔ (stab δ ⊓ stab μ) = stab δ)
    (hodd : ∀ u ∈ U, Odd (orderOf u) → u ∈ Subgroup.normalizer (Zv μ : Set G)) : False := by
  have hδ : δ ∈ nbrs μ := SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj δ μ from hμ)
  have hNμ : stab μ ≤ Subgroup.normalizer (Zv μ : Set G) := stab_le_normalizer_Zv hA μ
  have hres : oTwoRes U ≤ Subgroup.normalizer (Zv μ : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxU, m, hm, hxm⟩
    refine hodd x hxU ?_
    have hd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
    exact Odd.of_dvd_nat hm hd
  have hUN : U ≤ Subgroup.normalizer (Zv μ : Set G) :=
    (le_oTwoRes_sup_of_isSylowTwoOf hP).trans (sup_le hres (hPμ.trans hNμ))
  have hS : stab δ ⊓ stab μ ≤ Subgroup.normalizer (Zv μ : Set G) := inf_le_right.trans hNμ
  have hδN : stab δ ≤ Subgroup.normalizer (Zv μ : Set G) := by
    rw [← hgen]; exact sup_le hUN hS
  have hZ : Zv μ ≤ stab δ ⊓ stab μ :=
    le_inf ((Zv_le_Qv hA μ).trans (Qv_le_stab_of_mem_nbrs hA hδ))
      ((Zv_le_Qv hA μ).trans (pCoreOf_le 2 _))
  exact Zv_ne_bot hA μ (eq_bot_of_normalizes_both hA hμ hZ hδN hNμ)

namespace SitSigma

variable {δ μ : Geo H M} {U : Subgroup G}

theorem R_le_P (h : SitSigma δ μ U) : pCoreOf 2 U ≤ Qv μ ⊓ U :=
  isSylowTwoOf_pCoreOf_le h.sylow

theorem P_le_edge (hA : F53Amalgam H M S) (h : SitSigma δ μ U) :
    Qv μ ⊓ U ≤ stab δ ⊓ stab μ := by
  have hμ : μ ∈ nbrs δ := h.adj
  have hδ : δ ∈ nbrs μ := SimpleGraph.Adj.symm h.adj
  exact le_inf (inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA hδ))
    (inf_le_left.trans (pCoreOf_le 2 _))

theorem inf_Qv_le_R (h : SitSigma δ μ U) : U ⊓ Qv δ ≤ pCoreOf 2 U := by
  have h1 : pCoreOf 2 (stab δ) ⊓ U ≤ pCoreOf 2 U := pCoreOf_inf_le h.le_stab
  rw [inf_comm]
  exact h1

theorem false_of_odd_normalizes (hA : F53Amalgam H M S) (h : SitSigma δ μ U)
    (hodd : ∀ u ∈ U, Odd (orderOf u) → u ∈ Subgroup.normalizer (Zv μ : Set G)) : False :=
  false_of_odd_normalizes_gen hA h.adj h.sylow
    (inf_le_left.trans (pCoreOf_le 2 _)) h.gen hodd

theorem le_R_of_centralizes (hA : F53Amalgam H M S) (h : SitSigma δ μ U) {D : Subgroup G}
    (hDU : D ≤ U) (hDn : U ≤ Subgroup.normalizer (D : Set G))
    (hDc : ∀ d ∈ D, ∀ z ∈ Zv μ, d * z = z * d) : D ≤ pCoreOf 2 U := by
  by_contra hD
  refine h.false_of_odd_normalizes hA fun u hu huo => ?_
  obtain ⟨d, hd, e, he, rfl⟩ := odd_mem_of_normal hA h.le_stab hDU hDn hD u hu huo
  have he' : e ∈ Qv μ := (h.R_le_P (h.inf_Qv_le_R he)).1
  have hecen : e ∈ Subgroup.centralizer (Zv μ : Set G) := Subgroup.mem_centralizer_iff.mpr fun z hz =>
    ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2 e he').symm)
  have hdcen : d ∈ Subgroup.centralizer (Zv μ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => (hDc d hd z hz).symm
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.mul_mem _ hdcen hecen)

omit [Finite G] in
theorem normalizer_inf_centralizer {Y : Subgroup G} (hY : U ≤ Subgroup.normalizer (Y : Set G)) :
    U ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  intro x hx
  have key : ∀ x ∈ U, ∀ d ∈ U ⊓ Subgroup.centralizer (Y : Set G),
      x * d * x⁻¹ ∈ U ⊓ Subgroup.centralizer (Y : Set G) := by
    intro x hx d hd
    refine ⟨U.mul_mem (U.mul_mem hx hd.1) (U.inv_mem hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : x⁻¹ * y * x ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hY (U.inv_mem hx)) y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hd.2 _ hy'
    calc y * (x * d * x⁻¹) = x * ((x⁻¹ * y * x) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * d * x⁻¹ * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key x hx d, fun hd => ?_⟩
  have := key x⁻¹ (U.inv_mem hx) _ hd
  simpa [mul_assoc] using this

theorem centralizer_le_R (hA : F53Amalgam H M S) (h : SitSigma δ μ U) :
    U ⊓ Subgroup.centralizer (pCoreOf 2 U : Set G) ≤ pCoreOf 2 U := by
  refine le_R_of_centralizes hA h inf_le_left
    (normalizer_inf_centralizer (le_normalizer_pCoreOf 2 U)) fun d hd z hz => ?_
  exact ((Subgroup.mem_centralizer_iff.mp hd.2 z (h.zle hz))).symm

theorem centralizer_le_R_of_Y (hA : F53Amalgam H M S) (h : SitSigma δ μ U) {Y : Subgroup G}
    (hY : U ≤ Subgroup.normalizer (Y : Set G)) (hZY : Zv μ ≤ Y) :
    U ⊓ Subgroup.centralizer (Y : Set G) ≤ pCoreOf 2 U := by
  refine le_R_of_centralizes hA h inf_le_left (normalizer_inf_centralizer hY) fun d hd z hz => ?_
  exact ((Subgroup.mem_centralizer_iff.mp hd.2 z (hZY hz))).symm

theorem centralizer_eq_R (hA : F53Amalgam H M S) (h : SitSigma δ μ U) {Y : Subgroup G}
    (hY : U ≤ Subgroup.normalizer (Y : Set G)) (hZY : Zv μ ≤ Y)
    (hYR : Y ≤ centerOf (pCoreOf 2 U)) :
    U ⊓ Subgroup.centralizer (Y : Set G) = pCoreOf 2 U := by
  refine le_antisymm (h.centralizer_le_R_of_Y hA hY hZY) (le_inf (pCoreOf_le 2 U) fun x hx => ?_)
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hYR hy).2 x hx).symm

theorem eq_bot_of_characteristic (hA : F53Amalgam H M S) (h : SitSigma δ μ U)
    (hP : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ U : Subgroup G) : Set G))
    (K : Subgroup ↥(Qv μ ⊓ U)) [K.Characteristic]
    (hK : U ≤ Subgroup.normalizer ((K.map (Qv μ ⊓ U).subtype : Subgroup G) : Set G)) : K = ⊥ := by
  have hμC : stab μ ≤ Subgroup.normalizer ((K.map (Qv μ ⊓ U).subtype : Subgroup G) : Set G) :=
    hP.trans (normalizer_le_normalizer_map_of_characteristic K)
  have hδC : stab δ ≤ Subgroup.normalizer ((K.map (Qv μ ⊓ U).subtype : Subgroup G) : Set G) := by
    rw [← h.gen]; exact sup_le hK (inf_le_right.trans hμC)
  have hle : (K.map (Qv μ ⊓ U).subtype : Subgroup G) ≤ stab δ ⊓ stab μ :=
    (Subgroup.map_subtype_le K).trans (h.P_le_edge hA)
  have := eq_bot_of_normalizes_both hA h.adj hle hδC hμC
  exact (Subgroup.map_eq_bot_iff_of_injective K (Subgroup.subtype_injective _)).mp this

end SitSigma

end F53

end CFSG.Quasithin
