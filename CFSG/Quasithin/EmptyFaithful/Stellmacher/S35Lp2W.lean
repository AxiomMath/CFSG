module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpFin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

theorem image_alt (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 γ') (hU : UC γ') {ρ : Geo H M} (hρ : dist ρ β = 2)
    {v : G} (hv : v ∈ Vn ρ) (hvs : v ∈ stab γ') :
    c.θ ⟨v, hvs⟩ ∈ alternatingGroup (Fin 5) := by
  by_cases hQ : Vn ρ ≤ Qv γ'
  · rw [(c.ker_iff hS (back_vtype_γ hp hb) ⟨v, hvs⟩).mpr (hQ hv)]
    exact (alternatingGroup (Fin 5)).one_mem
  · have hρv : vtype ρ = false := by
      obtain ⟨l, hl, hρl, -⟩ := Std.dist_eq_two_iff.mp hρ
      rw [← hp.vδ]
      exact Std.vtype_eq_of_nbrs hρl (Std.mem_nbrs_symm.mp hl)
    have h1 := dist_triangle rfl ρ β γ'
    have h2 := back_dist_γ hp hb
    have h3 : bMin H M ≤ dist ρ γ' + 1 := by
      by_contra hlt
      exact hQ (Std.Vn_le_Qv_dist hS (by omega))
    have hpρ : S34.PD ρ γ' := ⟨hρv, back_vtype_γ hp hb, by omega, hQ⟩
    have hns := not_swap_of_neg hS hneg hpρ c hU hv hvs
    have hv2 : v ^ 2 = 1 := isElemAbelian_pow_eq_one (Std.Vn_isElemAbelian hS ρ) hv
    have hsq : c.θ ⟨v, hvs⟩ * c.θ ⟨v, hvs⟩ = 1 := by
      rw [← map_mul]
      have : (⟨v, hvs⟩ * ⟨v, hvs⟩ : ↥(stab γ')) = 1 := Subtype.ext (by simpa [pow_two] using hv2)
      rw [this, map_one]
    exact even_of_not_swap hsq hns

theorem π_Zv_α' (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ')
    (c : Chart2 γ') {a : G} (ha : a ∈ Zv α') (ha1 : a ≠ 1) (haV : a ∈ Vn γ') :
    c.π ⟨a, haV⟩ = vp (fixPt (c.Dl m)) := by
  have hml : m ∈ nbrs γ' := Std.mem_nbrs_symm.mp hb.2.1
  have hγ := back_vtype_γ hp hb
  have hz0m : a ∈ Zv m := Std.Zv_le_Zv_of_nbr hS hp.vδ' hb.1 ha
  have h1 : c.π ⟨a, haV⟩ ∈ c.img (Zv m) := (c.mem_img_iff').mpr ⟨⟨a, haV⟩, hz0m, rfl⟩
  rw [c.img_Zv_nbr hS hγ hml, mem_zpowers_iff_of_mul_self (vp_mul_self _)] at h1
  rcases h1 with h1 | h1
  · exfalso
    have haC : a ∈ Cb γ' := (c.π_eq_one ⟨a, haV⟩).mp h1
    have hZα : Zv α' ≤ Cb γ' :=
      (le_zpowers_of_card_two (hS.cardZ5 α' hp.vδ') ha ha1).trans
        (Subgroup.zpowers_le.mpr haC)
    have hZm : Zv m ≤ Cb γ' := by
      rw [← (back_Zv_m hS hp hb).1]
      exact sup_le (Zv_le_Cb' hS hγ) hZα
    exact not_Zv_nbr_le_Cb hS hγ hml hZm
  · exact h1

theorem Wb_le_stab_inf (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 γ') (hU : UC γ') (hZα : Zv α' ≤ Vn β) :
    Wb β ≤ stab γ' ⊓ stab m := by
  have hml : m ∈ nbrs γ' := Std.mem_nbrs_symm.mp hb.2.1
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hml
  have hfix : IsFixPt (c.Dl m) (fixPt (c.Dl m)) := isFixPt_fixPt hD
  have hγ := back_vtype_γ hp hb
  have hWs := Wb_le_stab_γ hS hp hb
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (F53.Zv_ne_bot hS.glob.amalg α')
  have hz0m : (a : G) ∈ Zv m := Std.Zv_le_Zv_of_nbr hS hp.vδ' hb.1 a.2
  have hz0V : (a : G) ∈ Vn γ' := Std.Zv_le_Vn hml hz0m
  have hπ : c.π ⟨(a : G), hz0V⟩ = vp (fixPt (c.Dl m)) :=
    π_Zv_α' hS hp hb c a.2 (fun h => ha (Subtype.ext h)) hz0V
  have hW1 : ∀ w ∈ Wb β, ∀ hws : w ∈ stab γ', c.θ ⟨w, hws⟩ (fixPt (c.Dl m)) =
      fixPt (c.Dl m) := by
    intro w hw hws
    have hcomm : w * (a : G) = (a : G) * w :=
      (comm_of_commutator_eq_bot (Std.comm_Vn_Wb hS β) (hZα a.2) hw).symm
    have h1 := (c.comm_mem_iff ⟨w, hws⟩ ⟨(a : G), hz0V⟩).mp (by
      show w * (a : G) * w⁻¹ * (a : G)⁻¹ ∈ Cb γ'
      rw [hcomm]
      simp)
    rw [hπ] at h1
    exact (act_vp_eq_iff _ _).mp h1
  have hρ : ∀ ρ : Geo H M, dist ρ β = 2 → Vn ρ ≤ c.preθ (c.Dl m) := by
    intro ρ hρ v hv
    have hvW : v ∈ Wb β := Std.Vn_le_Wb hρ hv
    have hvs : v ∈ stab γ' := hWs hvW
    refine (c.mem_preθ_iff ⟨v, hvs⟩).mpr ?_
    have hv2 : v ^ 2 = 1 := isElemAbelian_pow_eq_one (Std.Vn_isElemAbelian hS ρ) hv
    have hsq : c.θ ⟨v, hvs⟩ * c.θ ⟨v, hvs⟩ = 1 := by
      rw [← map_mul]
      have : (⟨v, hvs⟩ * ⟨v, hvs⟩ : ↥(stab γ')) = 1 := Subtype.ext (by simpa [pow_two] using hv2)
      rw [this, map_one]
    exact mem_of_even_sq_fix hD hfix (image_alt hS hneg hp hb c hU hρ hv hvs) hsq
      (hW1 v hvW hvs)
  rw [← c.preθ_Dl hS hγ hml]
  exact Std.Wb_le hρ

theorem Wb_le_Qm (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 γ') (hU : UC γ') (hZα : Zv α' ≤ Vn β) :
    Wb β ≤ Qv m := by
  have hin := Wb_le_stab_inf hS hneg hp hb c hU hZα
  have hγ := back_vtype_γ hp hb
  intro w hw
  rw [← F53.centralizer_Zv_eq_Qv_of_bAt hS.glob.amalg
    (hS.glob.crit m (back_vtype_m hp hb))]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hin hw)).2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← (back_Zv_m hS hp hb).1] at hz
  have key : Zv γ' ⊔ Zv α' ≤ Subgroup.centralizer ({w} : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact (central_comm hS hγ hz (Subgroup.mem_inf.mp (hin hw)).1)
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact (comm_of_commutator_eq_bot (Std.comm_Vn_Wb hS β) (hZα hz) hw).symm
  have := Subgroup.mem_centralizer_iff.mp (key hz) w (Set.mem_singleton w)
  exact this.symm

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
