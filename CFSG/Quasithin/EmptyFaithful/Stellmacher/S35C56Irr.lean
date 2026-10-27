module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem _root_.CFSG.Quasithin.F53Mod.IsOrthSec.eq_or_eq_of_oTwoRes {F E N : Subgroup G}
    (h : IsOrthSec F E N) {U : Subgroup G} (hEU : E ≤ U) (hUN : U ≤ N)
    (hU : oTwoRes F ≤ Subgroup.normalizer (U : Set G)) : U = E ∨ U = N := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  have hinv : ∀ k ∈ oTwoRes F, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hU hk)) u).mp hu
  obtain ⟨Y, hY, hYm⟩ := (hsd.invariant_iff_sub (oTwoRes_le F) hEU hUN).mp hinv
  rw [S43.map_oTwoRes_eq_alt hθs] at hY
  have hLX : E ≤ N := hEU.trans hUN
  rcases S43.orth_irred_alt5 Y hY with rfl | rfl
  · left
    refine le_antisymm (fun u hu => ?_) hEU
    have hu' : (QuotientGroup.mk' (E.subgroupOf N)) ⟨u, hUN hu⟩ ∈
        (U.subgroupOf N).map (QuotientGroup.mk' (E.subgroupOf N)) :=
      ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [← hYm, Subgroup.map_bot, Subgroup.mem_bot] at hu'
    have := (QuotientGroup.eq_one_iff _).mp hu'
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine le_antisymm hUN (fun x hx => ?_)
    have hx' : (QuotientGroup.mk (⟨x, hx⟩ : ↥N) : ↥N ⧸ E.subgroupOf N) ∈
        (U.subgroupOf N).map (QuotientGroup.mk' (E.subgroupOf N)) := by
      rw [← hYm, Subgroup.map_top_of_surjective _ hsd.surj]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hx'
    have h1 : (x : G) * (c : G)⁻¹ ∈ E := mk_eq_iff_mem.mp hcx
    have h2 : x = (x * (c : G)⁻¹) * (c : G) := by group
    rw [h2]
    exact U.mul_mem (hEU h1) (Subgroup.mem_subgroupOf.mp hc)

theorem _root_.CFSG.Quasithin.F53Mod.IsOrthSec.comm_pCore {F E N : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (h : IsOrthSec F E N) (hEN : E ≤ N) :
    ∀ q ∈ pCoreOf 2 F, ∀ x ∈ N, q * x * q⁻¹ * x⁻¹ ∈ E := by
  have hc := IsModelSec.cSecIn_eq_pCoreOf h hq
  have hFE : F ≤ Subgroup.normalizer (E : Set G) := (IsModelSec.isSec h hEN).normL
  intro q hq' x hx
  rw [← hc, mem_cSecIn_iff hFE] at hq'
  exact hq'.2 x hx

theorem quot_five (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin 5)) :=
  quot_stab_five hS.glob.amalg hδ

theorem exists_arc (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ∃ l ∈ nbrs δ, ∃ δ' ∈ nbrs l, δ' ≠ δ := by
  obtain ⟨l, hl⟩ := CosetGeom.exists_adj δ
  have hl' : l ∈ nbrs δ := hl
  have hlt : vtype l = true := Std.vtype_nbr_S5 hδ hl'
  obtain ⟨β, δ₁, δ₂, h, h1, h2, h3⟩ := Std.nbrs_S3 hS hlt
  have hδl : δ ∈ nbrs l := Std.mem_nbrs_symm.mp hl'
  rw [h] at hδl
  refine ⟨l, hl', ?_⟩
  rcases hδl with rfl | rfl | rfl
  · exact ⟨δ₁, by rw [h]; simp, h1.symm⟩
  · exact ⟨β, by rw [h]; simp, h1⟩
  · exact ⟨β, by rw [h]; simp, h2⟩

theorem card_Vn (hS : Sit H M S) (hI : CaseI H M) {δ : Geo H M} (hδ : vtype δ = false) :
    Nat.card (Vn δ) = 32 := by
  obtain ⟨l, hl, δ', hδ', hne⟩ := exists_arc hS hδ
  exact (hI δ l δ' hδ hl (Std.mem_nbrs_symm.mp hδ') hne).2

theorem Cb_eq_Zv (hS : Sit H M S) (hI : CaseI H M) {δ : Geo H M} (hδ : vtype δ = false) :
    S34.Cb δ = Zv δ := by
  have hCV : S34.Cb δ ≤ Vn δ := inf_le_left
  have h16 := IsOrthSec.relIndex_eq (hS.orth δ hδ)
  have hmul := Subgroup.relIndex_mul_card (S34.Cb δ) (Vn δ)
  rw [inf_eq_left.mpr hCV, h16, card_Vn hS hI hδ] at hmul
  have hC2 : Nat.card (S34.Cb δ) = 2 := by omega
  have hle := S34.Zv_le_Cb hS.glob hδ
  have hZ := hS.cardZ5 δ hδ
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hC2, hZ]

theorem orthZ (hS : Sit H M S) (hI : CaseI H M) {δ : Geo H M} (hδ : vtype δ = false) :
    IsOrthSec (stab δ) (Zv δ) (Vn δ) := by
  rw [← Cb_eq_Zv hS hI hδ]
  exact hS.orth δ hδ

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
