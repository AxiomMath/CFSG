module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L192Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.L192

open S35.Std S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem first_two (h16 : Claim16a H M) (hTT : ClaimTT H M)
    (h9 : Claim9T H M) (h3 : Claim3 H M) (h8b : Claim8b H M) {β α' m γ' : Geo H M}
    (hL : Lam β α') (hB : Back H M β α' m γ') :
    Zv α' ≤ Wb β ∧ (Wb β ⊓ stab α').relIndex (Wb β) = 2 := by
  have hT := hTT β α' m γ' hL.1 hB (h16 β α' hL)
  have h1 := h9 β α' m γ' hL.1 hB hT
  have hle : Wb β ⊓ stab m ≤ Wb β ⊓ stab α' := fun w hw =>
    ⟨hw.1, h3 β α' m γ' hL.1 hB hw⟩
  have h2 : (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 := by
    have hd := Subgroup.relIndex_dvd_of_le_left (Wb β) hle
    have hpos : 0 < (Wb β ⊓ stab m).relIndex (Wb β) :=
      Nat.pos_of_ne_zero (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
    exact (Nat.le_of_dvd hpos hd).trans h1
  exact h8b β α' hL.1 (h16 β α' hL) h2

theorem lem192_II (hS : Sit H M S) (h7 : 7 ≤ bMin H M) (h16 : Claim16a H M)
    (hTT : ClaimTT H M) (h9 : Claim9T H M) (h3 : Claim3 H M) (h8b : Claim8b H M)
    (hSym : Claim10Sym H M) : Lem192 H M := by
  intro β α' m γ' hL hB
  obtain ⟨hZW, hidx⟩ := first_two h16 hTT h9 h3 h8b hL hB
  refine ⟨hZW, hidx, fun l hl => ?_⟩
  by_contra hnot
  have hβ : vtype β = false := hL.1.vδ
  have hα' : vtype α' = false := hL.1.vδ'
  obtain ⟨hm, hγ, h1, h2⟩ := hB
  have hmS : vtype m = true := vtype_nbr_S5 hα' hm
  have hγS : vtype γ' = false := vtype_nbr_S3 hmS hγ
  have hmγ : m ∈ nbrs γ' := mem_nbrs_symm.mp hγ
  have hb := hL.1.dist_eq
  have hab := Std.Wb_comm_of_b7 hS h7 β
  have hWlW : Wl l ≤ Wb β := by
    rw [Std.Wb_eq_iSup_Wl hS hβ]
    exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl.1 le_rfl
  have hnQ : ¬ Wl l ≤ Qv γ' := fun hQ => hnot fun w hw =>
    mem_stab_of_cent hS hmS (mem_nbrs_symm.mp hm) (Std.Qv_le_stab hS hmγ (hQ hw)) fun z hz =>
      hab w (hWlW hw) z (hZW hz)
  obtain ⟨δ, hδl, hδQ⟩ : ∃ δ ∈ nbrs l, ¬ Vn δ ≤ Qv γ' := by
    by_contra hh
    push Not at hh
    exact hnQ (Std.Wl_le hh)
  have hlS : vtype l = true := vtype_nbr_S5 hβ hl.1
  have hδS : vtype δ = false := vtype_nbr_S3 hlS hδl
  have hδβ : δ ≠ β := by
    rintro rfl
    exact hδQ ((Std.geodesic_facts hS hb h1 h2).1.trans inf_le_right)
  have hdlβ : dist l β = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hl.1
  have hdδl : dist δ l = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hδl
  have t1 := CosetGeom.dist_triangle rfl δ l β
  have t2 := CosetGeom.dist_triangle rfl δ β γ'
  have hge : bMin H M ≤ dist δ γ' + 1 := by
    by_contra hlt
    exact hδQ (Std.Vn_le_Qv_dist hS (by omega))
  have hPD : S34.PD δ γ' := ⟨hδS, hγS, by omega, hδQ⟩
  have hnc : ∃ x ∈ Vn α', ∃ z ∈ Zv δ, x * z ≠ z * x := by
    by_contra hcon
    push Not at hcon
    apply hl.2
    intro x hx
    have hxs : x ∈ stab β := (Std.PD_Vn_le_stab hS hL.1).2 hx
    have hZl : Zv β ⊔ Zv δ = Zv l := (Std.Zv_ne hS hlS (mem_nbrs_symm.mp hl.1) hδl hδβ.symm).2.1
    have hcent : ∀ z ∈ Zv l, x * z = z * x := by
      intro z hz
      rw [← hZl] at hz
      have hle : Zv β ⊔ Zv δ ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          subst hg
          exact comm_of_mem_Zv hS hβ hy hxs
        · rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          subst hg
          exact hcon g hx y hy
      exact Subgroup.mem_centralizer_iff.mp (hle hz) x rfl
    exact mem_normalizer_of_comm hcent
  have hd2 : dist γ' α' ≤ 2 := by
    have := CosetGeom.dist_triangle rfl γ' m α'
    have e1 : dist γ' m = 1 := dist_eq_one_iff_adj.mpr hmγ
    have e2 : dist m α' = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hm
    omega
  have hZδV : ¬ Zv δ ≤ Vn γ' := fun hle => by
    obtain ⟨x, hx, z, hz, hne⟩ := hnc
    exact hne (Std.Vn_commute_dist hS (by omega) z (hle hz) x hx).symm
  have hLam : Lam δ γ' := ⟨hPD, hZδV⟩
  have hLam' : Lam γ' δ := hSym δ γ' hLam
  obtain ⟨m2, γ2, hB2⟩ := back_of_PD hS hLam'.1
  have hZW2 : Zv δ ≤ Wb γ' := (first_two h16 hTT h9 h3 h8b hLam' hB2).1
  have hne : α' ≠ γ' := by
    rintro rfl
    omega
  have hVW : Vn α' ≤ Wb γ' :=
    Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨m, hmγ, mem_nbrs_symm.mp hm, hne⟩)
  obtain ⟨x, hx, z, hz, hne'⟩ := hnc
  exact hne' (Std.Wb_comm_of_b7 hS h7 γ' x (hVW hx) z (hZW2 hz))

end S35.L192

end F53.Stellmacher

end CFSG.Quasithin
