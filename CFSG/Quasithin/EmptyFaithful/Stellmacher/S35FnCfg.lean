module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

variable {β α' m γ' : Geo H M}

omit [Finite G] in
theorem vtype_m (hL : Lam β α') (hB : Back H M β α' m γ') : vtype m = true :=
  Std.vtype_nbr_S5 hL.1.vδ' hB.1

omit [Finite G] in
theorem vtype_γ' (hL : Lam β α') (hB : Back H M β α' m γ') : vtype γ' = false :=
  Std.vtype_nbr_S3 (vtype_m hL hB) hB.2.1

omit [Finite G] in
theorem dist_m (hL : Lam β α') (hB : Back H M β α' m γ') : dist β m + 2 = bMin H M := by
  have h1 := hL.1.dist_eq
  have h2 := hB.2.2.1
  omega

omit [Finite G] in
theorem dist_γ' (hL : Lam β α') (hB : Back H M β α' m γ') : dist β γ' + 3 = bMin H M := by
  have h1 := dist_m hL hB
  have h2 := hB.2.2.2
  omega

theorem Zα'_le_Zm (hS : Sit H M S) (hL : Lam β α') (hB : Back H M β α' m γ') :
    Zv α' ≤ Zv m :=
  Std.Zv_le_Zv_of_nbr hS hL.1.vδ' hB.1

theorem Zγ'_le_Zm (hS : Sit H M S) (hL : Lam β α') (hB : Back H M β α' m γ') :
    Zv γ' ≤ Zv m :=
  Std.Zv_le_Zv_of_nbr hS (vtype_γ' hL hB) (Std.mem_nbrs_symm.mp hB.2.1)

omit [Finite G] in
theorem Zm_le_Vα' (hB : Back H M β α' m γ') : Zv m ≤ Vn α' :=
  Std.Zv_le_Vn hB.1

theorem Zm_le_Kb (hS : Sit H M S) (hL : Lam β α') (hB : Back H M β α' m γ') : Zv m ≤ Kb β := by
  have hd := dist_m hL hB
  have hb5 := hS.b5
  refine le_inf ?_ ?_
  · refine Std.Zv_le_Qv_dist ?_
    rw [CosetGeom.dist_comm]
    omega
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    refine Std.comm_iSup (p := fun μ => μ ∈ nbrs β) Zv (Zv m) ?_ v hv z hz
    intro l' hl' a ha b hb
    have h1 : dist l' m < bMin H M := by
      have := dist_le_dist_nbr hl' m
      rw [CosetGeom.dist_comm m l', CosetGeom.dist_comm m β] at this
      omega
    have hc := (F53.Zv_le_centerOf_Qv hS.glob.amalg m) hb
    have ha' : a ∈ Qv m := Std.Zv_le_Qv_dist h1 ha
    exact Subgroup.mem_centralizer_iff.mp hc.2 a ha'

theorem Wb_le_stab_γ' (hS : Sit H M S) (hL : Lam β α') (hB : Back H M β α' m γ') :
    Wb β ≤ stab γ' := by
  refine Std.Wb_le fun ρ hρ => Std.Vn_le_stab_dist hS ?_
  have h1 := dist_triangle rfl ρ β γ'
  have h2 := dist_γ' hL hB
  omega

theorem Vα'_comm_Vγ' (hS : Sit H M S) (_hL : Lam β α') (hB : Back H M β α' m γ') :
    ∀ a ∈ Vn α', ∀ b ∈ Vn γ', a * b = b * a := by
  refine Std.Vn_commute_dist hS ?_
  have h1 := dist_triangle rfl α' m γ'
  have h2 : dist α' m = 1 := by
    exact dist_eq_one_iff_adj.mpr hB.1
  have h3 : dist m γ' = 1 := dist_eq_one_iff_adj.mpr hB.2.1
  have := hS.b5
  omega

theorem Vα'_le_stab_β (hS : Sit H M S) (hL : Lam β α') : Vn α' ≤ stab β :=
  (Std.PD_Vn_le_stab hS hL.1).2

theorem Zα'_le_stab_of_dist (hS : Sit H M S) (hL : Lam β α') {ρ : Geo H M} (hρ : dist β ρ ≤ 2) :
    Zv α' ≤ stab ρ := by
  refine Std.Zv_le_stab_dist_S5 hS hL.1.vδ' ?_
  have h1 := dist_triangle rfl α' β ρ
  have h2 := hL.1.dist_eq
  rw [CosetGeom.dist_comm α' β] at h1
  omega

theorem mem_Zv_of_cent (hS : Sit H M S) (hL : Lam β α') {l : Geo H M} (hl : l ∈ nbrs β)
    (hn : ¬ Vn α' ≤ Subgroup.normalizer (Zv l : Set G)) {g : G} (hg : g ∈ Zv l)
    (hc : ∀ x ∈ Vn α', x * g = g * x) : g ∈ Zv β := by
  by_contra hgβ
  have hβ := hL.1.vδ
  have hle : Zv β ≤ Zv l := Std.Zv_le_Zv_of_nbr hS hβ hl
  have hl3 : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have h2 : Nat.card (Zv β) = 2 := hS.cardZ5 β hβ
  have h4 : Nat.card (Zv l) = 4 := hS.cardZ3 l hl3
  set K : Subgroup G := Zv β ⊔ Subgroup.zpowers g with hK
  have hKl : K ≤ Zv l := sup_le hle ((Subgroup.zpowers_le).mpr hg)
  have hgK : g ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hβK : Zv β ≤ K := le_sup_left
  have hdvd1 : Nat.card (Zv β) ∣ Nat.card K := Subgroup.card_dvd_of_le hβK
  have hdvd2 : Nat.card K ∣ Nat.card (Zv l) := Subgroup.card_dvd_of_le hKl
  have hKeq : K = Zv l := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hle4 : Nat.card K ≤ 4 := h4 ▸ Nat.le_of_dvd Nat.card_pos hdvd2
    have hK2 : Nat.card K ≠ 2 := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge hβK (by omega)
      exact hgβ (this ▸ hgK)
    have : Nat.card K = 4 := by
      rw [h2] at hdvd1
      obtain ⟨k, hk⟩ := hdvd1
      omega
    exact Subgroup.eq_of_le_of_card_ge hKl (by omega)
  apply hn
  intro x hx
  have hcen : Zv l ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hKeq]
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxs : x ∈ stab β := Vα'_le_stab_β hS hL hx
      have := (Std.Zv_central hS hβ) hz
      have h5 := Subgroup.mem_centralizer_iff.mp this.2 x hxs
      exact h5.symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (hc x hx).symm
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcen hh)

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
