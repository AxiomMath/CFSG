module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF3
import all CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open Equiv (Perm)

set_option linter.unusedSectionVars false

section Ball

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Bball (α : Geo H M) : Subgroup G := ⨆ e : {e : Geo H M // dist α e ≤ 2}, Zv e.1

theorem Zv_le_Bball {α e : Geo H M} (h : dist α e ≤ 2) : Zv e ≤ Bball α :=
  le_iSup (fun e : {e : Geo H M // dist α e ≤ 2} => Zv e.1) ⟨e, h⟩

theorem Bball_le {α : Geo H M} {X : Subgroup G} (h : ∀ e, dist α e ≤ 2 → Zv e ≤ X) :
    Bball α ≤ X :=
  iSup_le fun e => h e.1 e.2

theorem Vn_le_Bball (α : Geo H M) : Vn α ≤ Bball α :=
  iSup₂_le fun μ hμ => Zv_le_Bball (by
    have : dist α μ = 1 := dist_eq_one_iff_adj.mpr hμ
    omega)

variable (hA : F53Amalgam H M S)

include hA in
theorem dist_ball_le {α e : Geo H M} (h : dist α e ≤ 2) (x : Geo H M) :
    dist e x ≤ 2 + dist α x := by
  have := dist_triangle hA.amalgam.gen e α x
  rw [CosetGeom.dist_comm e α] at this
  omega

include hA in
theorem Bball_le_Qv {α μ : Geo H M} (h : ∀ e, dist α e ≤ 2 → dist e μ < bMin H M) :
    Bball α ≤ Qv μ :=
  Bball_le fun e he => Zv_le_Qv_of_dist_lt' (h e he)

include hA in
theorem Bball_le_stab {α μ : Geo H M} (h : ∀ e, dist α e ≤ 2 → dist e μ ≤ bMin H M) :
    Bball α ≤ stab μ :=
  Bball_le fun e he => Zv_le_stab_of_dist_le' hA (h e he)

include hA in
theorem Zv_le_centralizer_Bball {α μ : Geo H M}
    (h : ∀ e, dist α e ≤ 2 → dist e μ < bMin H M) :
    Zv μ ≤ Subgroup.centralizer (Bball α : Set G) := by
  have h1 := Bball_le_Qv hA h
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2) b (h1 hb)

theorem VuModule.Zbar_eq {u μ : Geo H M} (V : VuModule u μ) (δ : Geo H M) :
    V.Zbar δ = ((Zv δ).subgroupOf (stab u)).map V.Ψ := by
  rfl

end Ball

section Algebra

variable {G : Type} [Group G]

theorem le_normalizer_of_le_centerOf {R X : Subgroup G} (h : R ≤ centerOf X) :
    X ≤ Subgroup.normalizer (R : Set G) := by
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact ((Subgroup.mem_centralizer_iff.mp (h hr).2) x hx).symm

theorem le_sup_of_le_sup_not_le {L N R : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hL : Nat.card L = 2) (hR : R ≤ L ⊔ N)
    (hRN : ¬ R ≤ N) : L ≤ R ⊔ N := by
  obtain ⟨r, hr, hrN⟩ := IsConcreteLE.not_le_iff_exists.mp hRN
  obtain ⟨l, hl, n, hn, hrln⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN r (hR hr)
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hrN
    rw [hrln, one_mul]
    exact hn
  have hzl : Subgroup.zpowers l ≤ L := (Subgroup.zpowers_le).mpr hl
  have hzne : Subgroup.zpowers l ≠ ⊥ := by
    intro h
    apply hl1
    have : l ∈ Subgroup.zpowers l := Subgroup.mem_zpowers l
    rw [h] at this
    exact this
  have heq := eq_of_le_of_ne_bot_of_card_eq_two hzl hL hzne
  rw [← heq, Subgroup.zpowers_le]
  have : l = r * n⁻¹ := by rw [hrln]; group
  rw [this]
  exact (R ⊔ N).mul_mem (Subgroup.mem_sup_left hr) ((R ⊔ N).inv_mem (Subgroup.mem_sup_right hn))

end Algebra

section Standing

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
  {α β α' u c c' : Geo H M} {y : ↥(H ⊔ M)}
  (hc : IsCritData α β α') (hv : vtype α = true)
  (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb4 : 4 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β))
  (P : StepFPts α β α' u c c' y)

include hA h27 h28 h113a hc hv hcomm hb4 hn P

theorem D1_path : ∃ δ₂ ε : Geo H M, δ₂ ∈ nbrs u ∧ ε ∈ nbrs δ₂ ∧
    dist α δ₂ + 2 = bMin H M ∧ dist α ε + 3 = bMin H M := by
  have h1 := P.u_crit.dist_eq'
  rw [CosetGeom.dist_comm] at h1
  obtain ⟨δ₂, hδ₂, hd2⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := u)
    (d := bMin H M - 2) (by omega)
  obtain ⟨ε, hε, hdε⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := δ₂)
    (d := bMin H M - 3) (by omega)
  exact ⟨δ₂, ε, hδ₂, hε, by omega, by omega⟩

theorem D1_R_le : ⁅Zv α, Zv α'⁆ ≤ Zv u ∧ ⁅Zv α, Zv α'⁆ ≤ Zv α' ∧ ⁅Zv α, Zv α'⁆ ≤ Zv α := by
  have hb3 : 3 ≤ bMin H M := by omega
  have hcp : IsCritPair₁ α' α :=
    ⟨not_le_Qv_of_comm_ne hA hcomm, by rw [CosetGeom.dist_comm]; exact hc.dist_eq⟩
  have h := (comm_eq_line hA h28 h113a (by omega) P.α'_type (bAt_eq_bMin hA h27 hc hv hn α')
    hcp (comm_symm_ne_bot hcomm) P.u_crit).1
  have hLv := tabE_Lv_le_inf hA h27 h28 h113a hc hv hcomm hb3 hn P.α'_type P.u_crit.adj
  have h' : ⁅Zv α, Zv α'⁆ = Lv α' u := by rw [Subgroup.commutator_comm]; exact h
  refine ⟨h' ▸ hLv.trans inf_le_right, h' ▸ hLv.trans inf_le_left, ?_⟩
  exact commutator_le_left_of_le_normalizer
    ((Zv_le_stab_pair hA hc hcomm).1.trans (stab_le_normalizer_Zv hA α))

variable {δ₂ ε : Geo H M}

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_R_le_Zδ₂ (hδ₂ : δ₂ ∈ nbrs u) (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) :
    ⁅Zv α, Zv α'⁆ ≤ Zv δ₂ := by
  obtain ⟨hRu, hRα', -⟩ := D1_R_le hA h27 h28 h113a hc hv hcomm hb4 hn P
  have hRst : ⁅Zv α, Zv α'⁆ ≤ stab u ⊓ stab δ₂ :=
    le_inf (hR.trans inf_le_left) (hRu.trans ((Zv_le_Qv hA u).trans
      (Qv_le_stab_of_mem_nbrs hA hδ₂)))
  have hsq : ∀ x ∈ ⁅Zv α, Zv α'⁆, x ^ 2 = 1 := fun x hx =>
    isElemAbelian_pow_eq_one (isElemAbelian_Zv hA α') (hRα' hx)
  have hmem : ⁅Zv α, Zv α'⁆ ≤ quasithinOmegaOneCenter (stab u ⊓ stab δ₂) := by
    intro r hr
    refine Subgroup.subset_closure ⟨⟨hRst hr, ?_⟩, hsq r hr⟩
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hR hr).2) x hx.1
  exact hmem.trans (omegaOneCenter_le_Zv hA hδ₂).2.2

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Zδ₂_le (hδ₂ : δ₂ ∈ nbrs u) (hε : ε ∈ nbrs δ₂) (hdε : dist α ε + 3 = bMin H M)
    (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) :
    Zv δ₂ ≤ (Zv δ₂ ⊓ Zv ε) ⊔ ⁅Zv α, Zv α'⁆ := by
  have hb3 : 3 ≤ bMin H M := by omega
  have hvδ : vtype δ₂ = true := tabE_vtype_of_adj_false hδ₂ P.u_type
  have hu' : u ∈ nbrs δ₂ := mem_nbrs_symm' hδ₂
  have hεu : ε ≠ u := by
    rintro rfl
    have h1 := P.u_crit.dist_eq'
    rw [CosetGeom.dist_comm] at h1
    omega
  obtain ⟨hRu, -, -⟩ := D1_R_le hA h27 h28 h113a hc hv hcomm hb4 hn P
  have hRδ := D1_R_le_Zδ₂ hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hR
  have hZu := tabE_Zv_inf_Zv hA h27 h28 h113a hc hv hcomm hb3 hn hvδ hu'
  have hZε := tabE_Zv_inf_Zv hA h27 h28 h113a hc hv hcomm hb3 hn hvδ hε
  have hline := tabE_Lv_ne_and_sup hA h27 h28 h113a hc hv hcomm hb3 hn hvδ hε hu' hεu
  have hZ0 := tabE_Z0v_sup hA h27 h28 h113a hc hv hcomm hb3 hn δ₂ hvδ
  have hRLN : ⁅Zv α, Zv α'⁆ ≤ Lv δ₂ u ⊔ Nv δ₂ := (le_inf hRδ hRu).trans hZu.le
  have hNc : Nv δ₂ ≤ centerOf (stab δ₂) := inf_le_right
  have hRnN : ¬ ⁅Zv α, Zv α'⁆ ≤ Nv δ₂ := by
    intro hRN
    apply hcomm
    have hRN' : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab δ₂) := hRN.trans hNc
    exact eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj u δ₂ from hδ₂)
      (le_inf (hR.trans inf_le_left) (hRN'.trans inf_le_left))
      (le_normalizer_of_le_centerOf hR) (le_normalizer_of_le_centerOf hRN')
  have hLZ : Lv δ₂ u ≤ Zv δ₂ :=
    (tabE_Lv_le_inf hA h27 h28 h113a hc hv hcomm hb3 hn hvδ hu').trans inf_le_left
  have hZst : Zv δ₂ ≤ stab δ₂ := (Zv_le_Qv hA δ₂).trans (pCoreOf_le 2 (stab δ₂))
  have hL : Lv δ₂ u ≤ ⁅Zv α, Zv α'⁆ ⊔ Nv δ₂ :=
    le_sup_of_le_sup_not_le
      (hLZ.trans (hZst.trans (le_normalizer_of_le_centerOf hNc)))
      (tabE_card_Lv hA h27 h28 h113a hc hv hcomm hb3 hn hvδ hu') hRLN hRnN
  have hN1 : Nv δ₂ ≤ Zv δ₂ ⊓ Zv ε := le_sup_right.trans hZε.symm.le
  have key : (Lv δ₂ ε ⊔ Lv δ₂ u) ⊔ Nv δ₂ ≤ (Zv δ₂ ⊓ Zv ε) ⊔ ⁅Zv α, Zv α'⁆ := by
    refine sup_le (sup_le ?_ ?_) (hN1.trans le_sup_left)
    · exact (le_sup_left.trans hZε.symm.le).trans le_sup_left
    · exact hL.trans (sup_le le_sup_right (hN1.trans le_sup_left))
  calc Zv δ₂ = (Lv δ₂ ε ⊔ Lv δ₂ u) ⊔ Nv δ₂ := by rw [hline, hZ0]
    _ ≤ _ := key

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Zδ₂_le_centralizer (hδ₂ : δ₂ ∈ nbrs u) (hε : ε ∈ nbrs δ₂)
    (hdε : dist α ε + 3 = bMin H M) (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) :
    Zv δ₂ ≤ Subgroup.centralizer (Bball α : Set G) := by
  have hdαβ : dist α β = 1 := dist_eq_one_iff_adj.mpr hc.adj
  have hZε : Zv ε ≤ Subgroup.centralizer (Bball α : Set G) :=
    Zv_le_centralizer_Bball hA fun e he => by
      have := dist_ball_le hA he ε
      omega
  have hZα : Zv α ≤ Subgroup.centralizer (Bball α : Set G) :=
    Zv_le_centralizer_Bball hA fun e he => by
      have := dist_ball_le hA he α
      rw [CosetGeom.dist_self] at this
      omega
  obtain ⟨-, -, hRα⟩ := D1_R_le hA h27 h28 h113a hc hv hcomm hb4 hn P
  exact (D1_Zδ₂_le hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hdε hR).trans
    (sup_le (inf_le_right.trans hZε) (hRα.trans hZα))

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Bball_le_Qv (hδ₂ : δ₂ ∈ nbrs u) (hε : ε ∈ nbrs δ₂) (hd2 : dist α δ₂ + 2 = bMin H M)
    (hdε : dist α ε + 3 = bMin H M) (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) :
    Bball α ≤ Qv δ₂ := by
  have hst : Bball α ≤ stab δ₂ := Bball_le_stab hA fun e he => by
    have := dist_ball_le hA he δ₂
    omega
  have hcen : Bball α ≤ Subgroup.centralizer (Zv δ₂ : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (D1_Zδ₂_le_centralizer hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hdε hR)
  rw [← centralizer_Zv_eq_Qv_all hA h27 hc hv hn δ₂]
  exact le_inf hst hcen

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Bball_le_stab (hδ₂ : δ₂ ∈ nbrs u) (hε : ε ∈ nbrs δ₂) (hd2 : dist α δ₂ + 2 = bMin H M)
    (hdε : dist α ε + 3 = bMin H M) (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) :
    Bball α ≤ stab u :=
  (D1_Bball_le_Qv hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hd2 hdε hR).trans
    (Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hδ₂))

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Bball_isPGroup (hδ₂ : δ₂ ∈ nbrs u) (hε : ε ∈ nbrs δ₂)
    (hd2 : dist α δ₂ + 2 = bMin H M) (hdε : dist α ε + 3 = bMin H M)
    (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) : IsPGroup 2 (Bball α) :=
  (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ₂)).to_le
    (D1_Bball_le_Qv hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hd2 hdε hR)

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Bball_cent_R₁ : ∀ g ∈ Bball α, ∀ r ∈ ⁅Zv β, Zv c'⁆, g * r = r * g := by
  have hdαβ : dist α β = 1 := dist_eq_one_iff_adj.mpr hc.adj
  have hZβ : Zv β ≤ Subgroup.centralizer (Bball α : Set G) :=
    Zv_le_centralizer_Bball hA fun e he => by
      have := dist_ball_le hA he β
      omega
  intro g hg r hr
  exact Subgroup.mem_centralizer_iff.mp (hZβ (P.R₁_le hr).1) g hg

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_Zc_le : Zv c ≤ Bball α :=
  Zv_le_Bball (by
    have : dist α c = 1 := dist_eq_one_iff_adj.mpr P.c_nbr
    omega)

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_nbr_le {ν : Geo H M} (hν : ν ∈ nbrs c) : Zv ν ≤ Bball α :=
  Zv_le_Bball (by
    have h1 : dist α c = 1 := dist_eq_one_iff_adj.mpr P.c_nbr
    have h2 : dist c ν = 1 := dist_eq_one_iff_adj.mpr hν
    have := dist_triangle hA.amalgam.gen α c ν
    omega)

include hA h27 h28 h113a hc hv hcomm hb4 hn P in
theorem D1_final
    (hdec : ∀ ν ∈ nbrs c, ∀ x ∈ Zv ν, ∃ a ∈ Zv c, ∃ q ∈ Qv u, x = a * q) : False := by
  obtain ⟨-, hZuc⟩ := P.Zc_le_stab_u hA
  obtain ⟨ν, hν, hsup⟩ := exists_nbr_sup_eq_stab_of_vtype_false hA P.c_type hZuc
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab u)).to_le (Zv_le_Qv hA u))
    P.uc_pair.1
  have hZuN : Zv u ≤ Subgroup.normalizer ((Zv c ⊔ Zv ν : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj (fun z hz a ha => ?_) (fun z hz b hb => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA c (hZuc hz)) a).mp ha)
    · obtain ⟨a, ha, q, hq, rfl⟩ := hdec ν hν b hb
      have hzq : q * z = z * q :=
        (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA u hz).2) q hq
      have hzq' : z * q * z⁻¹ = q := by rw [← hzq]; group
      have e : z * (a * q) * z⁻¹ = (z * a * z⁻¹) * (a⁻¹ * (a * q)) := by
        calc z * (a * q) * z⁻¹ = (z * a * z⁻¹) * (z * q * z⁻¹) := by group
          _ = (z * a * z⁻¹) * q := by rw [hzq']
          _ = _ := by group
      rw [e]
      refine (Zv c ⊔ Zv ν).mul_mem (Subgroup.mem_sup_left ?_)
        ((Zv c ⊔ Zv ν).mul_mem (Subgroup.mem_sup_left ((Zv c).inv_mem ha)) (Subgroup.mem_sup_right hb))
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA c (hZuc hz)) a).mp ha
  have hN2 : stab c ⊓ stab ν ≤ Subgroup.normalizer ((Zv c ⊔ Zv ν : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer (inf_le_left.trans (stab_le_normalizer_Zv hA c))
      (inf_le_right.trans (stab_le_normalizer_Zv hA ν))
  have hN : stab c ≤ Subgroup.normalizer ((Zv c ⊔ Zv ν : Subgroup G) : Set G) :=
    hsup.symm.le.trans (sup_le hZuN hN2)
  exact Zv_not_central_all hA h27 hc hv hn ν
    (h27 (by omega) c ν hν (bAt_eq_bMin hA h27 hc hv hn c) hN)

variable (h113c : Hss113cAt H M) (heven : Even (bMin H M))

include hA h27 h28 h113a hc hv hcomm hb4 hn P h113c heven in
theorem stepF_D1 (hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) : False := by
  have hb2 : 2 ≤ bMin H M := by omega
  obtain ⟨V⟩ := stepF_VuModule hA h113c P
  obtain ⟨δ₂, ε, hδ₂, hε, hd2, hdε⟩ := D1_path hA h27 h28 h113a hc hv hcomm hb4 hn P
  have hBu := D1_Bball_le_stab hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hd2 hdε hR
  have hB2 := D1_Bball_isPGroup hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hd2 hdε hR
  have hBR := D1_Bball_cent_R₁ hA h27 h28 h113a hc hv hcomm hb4 hn P
  have hZc := D1_Zc_le hA h27 h28 h113a hc hv hcomm hb4 hn P
  have hQ : Qv u ≤ stab α' := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' P.u_crit.adj)
  have hAR : ∀ a ∈ Zv (y • β), ∀ x ∈ Zv u, a * x * a⁻¹ * x⁻¹ ∈ ⁅Zv β, Zv c'⁆ := by
    intro a ha x hx
    rw [← P.star_comm]
    exact Subgroup.commutator_mem_commutator ha hx
  have hcases := (stepF_offender_cases hA h27 h113a hc hv hn P V).2.2.2
  simp only [VuModule.Zbar_eq] at hcases
  rcases D1_cases V hQ hAR hcases hBu hB2 hBR with hle | ⟨hM, h3⟩
  · exact P.c_not_le (hZc.trans hle)
  ·
    have hidx : (Vn α ⊓ stab α').relIndex (Vn α) ≤ 2 :=
      relIndex_inf_le_two_of_three fun x hx y hy =>
        h3 x (Vn_le_Bball α hx) y (Vn_le_Bball α hy)
    have hH3 := H3_of_index_two hA hc hv hcomm hb2 heven hidx
    have hvδ : vtype δ₂ = true := tabE_vtype_of_adj_false hδ₂ P.u_type
    have hεu : u ≠ ε := by
      rintro rfl
      have h1 := P.u_crit.dist_eq'
      rw [CosetGeom.dist_comm] at h1
      omega
    have hW := claim3'_transport hA h28 hc hv hcomm hb2 hH3 δ₂ hvδ u (mem_nbrs_symm' hδ₂) ε hε hεu
    have hCB : Zv ε ⊔ Zv δ₂ ≤ Subgroup.centralizer (Bball α : Set G) :=
      sup_le (Zv_le_centralizer_Bball hA fun e he => by
        have := dist_ball_le hA he ε
        omega)
        (D1_Zδ₂_le_centralizer hA h27 h28 h113a hc hv hcomm hb4 hn P hδ₂ hε hdε hR)
    have hW' : Zv u ⊓ (Zv ε ⊔ Zv δ₂) ≤ fixSecIn (Bball α) (Nu u) (Zv u) := by
      intro x hx
      refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
      have h1 : a * x = x * a := Subgroup.mem_centralizer_iff.mp (hCB hx.2) a ha
      have : a * x * a⁻¹ * x⁻¹ = 1 := by rw [h1]; group
      rw [this]
      exact (Nu u).one_mem
    have hidx2 : (fixSecIn (Bball α) (Nu u) (Zv u)).relIndex (Zv u) ≤ 2 :=
      le_trans (Subgroup.relIndex_le_of_le_left hW' Subgroup.index_ne_zero_of_finite) hW
    have h2 := D1_two_elements V hM inf_le_left hBu hidx2
    obtain ⟨z0, hz0, hz0Q⟩ := IsConcreteLE.not_le_iff_exists.mp P.cu_pair.1
    have hz0B : z0 ∈ Bball α := hZc hz0
    have hΨz0 : V.Ψ ⟨z0, hBu hz0B⟩ ≠ 1 := fun h => hz0Q ((V.ker _).mp h)
    have hdec : ∀ b ∈ Bball α, ∃ a ∈ Zv c, ∃ q ∈ Qv u, b = a * q := by
      intro b hb
      rcases h2 b hb z0 hz0B with h | h | h
      · exact ⟨1, (Zv c).one_mem, b, (V.ker ⟨b, hBu hb⟩).mp h, by simp⟩
      · exact absurd h hΨz0
      · refine ⟨z0, hz0, z0⁻¹ * b, ?_, by simp⟩
        have h1 : V.Ψ (⟨z0, hBu hz0B⟩⁻¹ * ⟨b, hBu hb⟩) = 1 := by
          rw [map_mul, map_inv, h, inv_mul_cancel]
        exact (V.ker _).mp h1
    exact D1_final hA h27 h28 h113a hc hv hcomm hb4 hn P fun ν hν x hx =>
      hdec x (D1_nbr_le hA h27 h28 h113a hc hv hcomm hb4 hn P hν hx)

end Standing

end F53.Stellmacher

end CFSG.Quasithin
