module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepDEF0
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Lines
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Off
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open Equiv (Perm)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

set_option linter.unusedSectionVars false

section Standing

variable {α β α' : Geo H M}

theorem commutator_Zv_Qv_le (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb2 : 2 ≤ bMin H M) : ⁅Zv α, Qv β⁆ ≤ Zv α' := by
  have hline := (comm_eq_line hA h28 h113a hb2 hv hc.bAt_eq ⟨hc.not_le, hc.dist_eq⟩ hcomm hc).1
  have h1 : ⁅Zv α, Qv β⁆ = ⁅Zv α, Zv α'⁆ := hline.symm
  rw [h1, Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer
    ((Zv_le_stab_pair hA hc hcomm).2.trans (stab_le_normalizer_Zv hA α'))

theorem le_Qv_of_comm_eq_bot (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {δ μ : Geo H M} (hle : Zv δ ≤ stab μ) (h : ⁅Zv δ, Zv μ⁆ = ⊥) : Zv δ ≤ Qv μ := by
  rw [← centralizer_Zv_eq_Qv_all hA h27 hc hv hn μ]
  refine le_inf hle ?_
  rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h

theorem comm_ne_bot_of_not_le_Qv (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {δ μ : Geo H M} (hle : Zv δ ≤ stab μ) (hnle : ¬ Zv δ ≤ Qv μ) : ⁅Zv δ, Zv μ⁆ ≠ ⊥ :=
  fun h => hnle (le_Qv_of_comm_eq_bot hA h27 hc hv hn hle h)

theorem isCritPair₁_symm_of_comm_ne (hA : F53Amalgam H M S) {δ μ : Geo H M}
    (hcp : IsCritPair₁ δ μ) (hne : ⁅Zv δ, Zv μ⁆ ≠ ⊥) :
    IsCritPair₁ μ δ ∧ ⁅Zv μ, Zv δ⁆ ≠ ⊥ := by
  refine ⟨⟨not_le_Qv_of_comm_ne hA hne, by rw [CosetGeom.dist_comm]; exact hcp.2⟩, ?_⟩
  rwa [Subgroup.commutator_comm]

theorem Y_le_centralizer_R₁ (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    (hb2 : 2 ≤ bMin H M) {c' : Geo H M} (hc'n : c' ∈ nbrs α') :
    Zv α ⊔ Qv c' ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) := by
  have hR := R₁_le_inf hA hc hc'n
  have hZαQβ : Zv α ≤ Qv β := Zv_le_Qv_of_mem_nbrs hc.adj hb2
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β (hR hr).1).2) x
      (hZαQβ hx)).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA c' (hR hr).2).2) x hx).symm

theorem Y_le_stab (hA : F53Amalgam H M S) (hc : IsCritData α β α') {c' : Geo H M}
    (hc'n : c' ∈ nbrs α') : Zv α ⊔ Qv c' ≤ stab α' :=
  sup_le (Zv_le_stab_of_dist_le' hA (by rw [hc.dist_eq]))
    (Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hc'n))

theorem exists_Y_smul_eq (hA : F53Amalgam H M S) (hc : IsCritData α β α')
    {c' : Geo H M} (hc'n : c' ∈ nbrs α') (hstab : stab α' = Zv α ⊔ (stab α' ⊓ stab c'))
    (hedge : stab α' ⊓ stab c' = Qv α' ⊔ Qv c') {ν : Geo H M} (hνn : ν ∈ nbrs α') :
    ∃ y : ↥(H ⊔ M), (y : G) ∈ Zv α ⊔ Qv c' ∧ y • c' = ν := by
  have hYst := Y_le_stab hA hc hc'n
  have hYN : Zv α ⊔ Qv c' ≤ Subgroup.normalizer (Qv α' : Set G) :=
    hYst.trans (le_normalizer_pCoreOf 2 (stab α'))
  have hstab' : stab α' ≤ (Zv α ⊔ Qv c') ⊔ Qv α' := by
    rw [hstab, hedge]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le (le_sup_right) (le_sup_of_le_left le_sup_right))
  obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hc'n hνn
  obtain ⟨y, hy, q, hq, hyq⟩ := exists_mul_of_mem_sup_of_le_normalizer hYN (g : G) (hstab' hg)
  have hqc' : q ∈ stab c' := Qv_le_stab_of_mem_nbrs hA hc'n hq
  refine ⟨⟨y, stab_le α' (hYst hy)⟩, hy, ?_⟩
  have hg' : g = ⟨y, stab_le α' (hYst hy)⟩ * ⟨q, stab_le c' hqc'⟩ := Subtype.ext hyq
  rw [← hgν, hg', mul_smul, smul_eq_of_mem_stab (g := ⟨q, stab_le c' hqc'⟩) hqc']

omit [Finite G] in
theorem isCritPair₁_smul (g : ↥(H ⊔ M)) {δ δ' : Geo H M} (h : IsCritPair₁ δ δ') :
    IsCritPair₁ (g • δ) (g • δ') := by
  refine ⟨?_, by rw [CosetGeom.dist_smul]; exact h.2⟩
  rw [Zv_smul, Qv_smul]
  intro hle
  exact h.1 ((conjSub_le_conjSub_iff' (g : G)).mp hle)

theorem vtype_false_of_nbr {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hv : vtype δ = true) :
    vtype μ = false := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from h)
  revert this; cases hμ : vtype μ <;> simp [hv]

structure StepFPts (α β α' u c c' : Geo H M) (y : ↥(H ⊔ M)) : Prop where
  u_crit : IsCritData α' u α
  α'_type : vtype α' = true
  u_type : vtype u = false
  c_type : vtype c = false
  c'_type : vtype c' = false
  β_type : vtype β = false
  c_nbr : c ∈ nbrs α
  c_ne : c ≠ β
  c_not_le : ¬ Zv c ≤ stab α'
  c_dist : dist c α' = bMin H M + 1
  cu_dist : dist c u = bMin H M
  cu_pair : IsCritPair₁ c u
  cu_comm : ⁅Zv c, Zv u⁆ ≠ ⊥
  uc_pair : IsCritPair₁ u c
  c'_nbr : c' ∈ nbrs α'
  c'_ne : c' ≠ u
  c'_not_le : ¬ Zv c' ≤ stab α
  c'_dist : dist c' α = bMin H M + 1
  c'_not_le_Qβ : ¬ Zv c' ≤ Qv β
  βc'_pair : IsCritPair₁ β c'
  R₁_ne : ⁅Zv β, Zv c'⁆ ≠ ⊥
  R₁_le : ⁅Zv β, Zv c'⁆ ≤ Zv β ⊓ Zv c'
  R₁_le_Zv_nbr : ∀ ν ∈ nbrs α', ⁅Zv β, Zv c'⁆ ≤ Zv ν
  stab_eq : stab α' = Zv α ⊔ (stab α' ⊓ stab c')
  edge_eq : stab α' ⊓ stab c' = Qv α' ⊔ Qv c'
  y_mem : (y : G) ∈ Zv α ⊔ Qv c'
  y_smul : y • c' = u
  y_stab : (y : G) ∈ stab α'
  y_cent : ∀ r ∈ ⁅Zv β, Zv c'⁆, (y : G) * r = r * (y : G)
  star_pair : IsCritPair₁ (y • β) u
  star_comm : ⁅Zv (y • β), Zv u⁆ = ⁅Zv β, Zv c'⁆
  star_le_Qα' : Zv (y • β) ≤ Qv α'
  R₁_le_star : ⁅Zv β, Zv c'⁆ ≤ Zv (y • β) ⊓ Zv u

theorem stepF_points (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M)
    (h113a : Hss113aAt H M) (hc : IsCritData α β α') (hv : vtype α = true)
    (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb4 : 4 ≤ bMin H M) (heven : Even (bMin H M))
    (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∃ (u c c' : Geo H M) (y : ↥(H ⊔ M)), StepFPts α β α' u c c' y := by
  have hb3 : 3 ≤ bMin H M := by omega
  have hb2 : 2 ≤ bMin H M := by omega
  have hRle := commutator_Zv_Qv_le hA h28 h113a hc hv hcomm hb2
  obtain ⟨u, hu, c', hc'n, hc'ne, hnle, hcp, hne, hR, hst, hed, hRν⟩ :=
    exists_c'_R₁_of_even hA h27 h28 hc hv hcomm hb3 hn heven hRle
  obtain ⟨c, hcn, hcβ⟩ := exists_nbr_ne hA α hc.adj
  obtain ⟨y, hy, hyc'⟩ := exists_Y_smul_eq hA hc hc'n hst hed hu.adj
  have hvα' : vtype α' = true := vtype_alpha'_of_even hA hc hv heven
  have hcomm' : ⁅Zv α', Zv α⁆ ≠ ⊥ := comm_symm_ne_bot hcomm
  have hn' : ¬ Zv u ≤ centerOf (stab u) := Zv_not_central_all hA h27 hc hv hn u
  have hcdist : dist c α' = bMin H M + 1 :=
    dist_nbr_alpha'_of_even hA h27 hc hv hcomm hb3 hn heven c hcn hcβ
  have hcnle : ¬ Zv c ≤ stab α' :=
    not_le_stab_alpha'_of_even hA h27 hc hv hcomm hb3 hn heven c hcn hcβ
  have hcu : dist c u = bMin H M := by
    have h1 := dist_triangle hA.amalgam.gen c α u
    have h2 := dist_triangle hA.amalgam.gen c u α'
    have hcα : dist c α = 1 :=
      dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj c α from mem_nbrs_symm' hcn)
    have huα' : dist u α' = 1 :=
      dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj u α' from mem_nbrs_symm' hu.adj)
    have h3 := hu.dist_eq'
    rw [CosetGeom.dist_comm α u] at h1
    omega
  have hQuα' : Qv u ≤ stab α' := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hu.adj)
  have hcQ : ¬ Zv c ≤ Qv u := fun h => hcnle (h.trans hQuα')
  have hcpair : IsCritPair₁ c u := ⟨hcQ, hcu⟩
  have hccomm : ⁅Zv c, Zv u⁆ ≠ ⊥ :=
    comm_ne_bot_of_not_le_Qv hA h27 hc hv hn (Zv_le_stab_of_dist_le' hA hcu.le) hcQ
  have hc'nle : ¬ Zv c' ≤ stab α :=
    not_le_stab_alpha'_of_even hA h27 hu hvα' hcomm' hb3 hn' heven c' hc'n hc'ne
  have hc'dist : dist c' α = bMin H M + 1 :=
    dist_nbr_alpha'_of_even hA h27 hu hvα' hcomm' hb3 hn' heven c' hc'n hc'ne
  have hYc := Y_le_centralizer_R₁ hA hc hb2 hc'n
  have hystab : (y : G) ∈ stab α' := Y_le_stab hA hc hc'n hy
  have hyα' : y • α' = α' := smul_eq_of_mem_stab hystab
  have hycent : ∀ r ∈ ⁅Zv β, Zv c'⁆, (y : G) * r = r * (y : G) := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp (hYc hy) r hr).symm
  have hyN : (y : G) ∈ Subgroup.normalizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hYc hy)
  have hfix : conjSub (y : G) ⁅Zv β, Zv c'⁆ = ⁅Zv β, Zv c'⁆ := conjSub_eq_of_mem_normalizer hyN
  refine ⟨u, c, c', y, ?_⟩
  have hstarcomm : ⁅Zv (y • β), Zv u⁆ = ⁅Zv β, Zv c'⁆ := by
    rw [← hyc', Zv_smul, Zv_smul, conjSub_commutator, hfix]
  have hβQ : Zv β ≤ Qv α' := Zv_le_Qv_of_dist_lt' (by have := hc.dist_eq'; omega)
  have hstarQ : Zv (y • β) ≤ Qv α' := by
    rw [Zv_smul]
    calc conjSub (y : G) (Zv β) ≤ conjSub (y : G) (Qv α') := conjSub_mono _ hβQ
      _ = Qv (y • α') := (Qv_smul y α').symm
      _ = Qv α' := by rw [hyα']
  refine ⟨hu, hvα', vtype_false_of_nbr hu.adj hvα', vtype_false_of_nbr hcn hv,
    vtype_false_of_nbr hc'n hvα', vtype_false_of_nbr hc.adj hv, hcn, hcβ, hcnle, hcdist, hcu,
    hcpair, hccomm, (isCritPair₁_symm_of_comm_ne hA hcpair hccomm).1, hc'n, hc'ne, hc'nle, hc'dist,
    hnle, hcp, hne, hR, hRν, hst, hed, hy, hyc', hystab, hycent, ?_, hstarcomm, hstarQ, ?_⟩
  · rw [← hyc']
    exact isCritPair₁_smul y hcp
  · calc ⁅Zv β, Zv c'⁆ = conjSub (y : G) ⁅Zv β, Zv c'⁆ := hfix.symm
      _ ≤ conjSub (y : G) (Zv β ⊓ Zv c') := conjSub_mono _ hR
      _ = Zv (y • β) ⊓ Zv u := by rw [conjSub_inf, ← Zv_smul, ← Zv_smul, hyc']

end Standing

section Model

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Nu (δ : Geo H M) : Subgroup G :=
  Zv δ ⊓ Subgroup.centralizer (oTwoRes (stab δ) : Set G)

theorem Vu_model (hA : F53Amalgam H M S) {u μ : Geo H M} (hμ : μ ∈ nbrs u)
    (hv : vtype u = false)
    (hmod : IsNatSec (stab u) (Nu u) (Zv u) ∨ IsOrthSec (stab u) (Nu u) (Zv u)) :
    ∃ M5 : Model 5, (M5 = nat ∨ M5 = orth) ∧
      ∃ (_ : ((Nu u).subgroupOf (Zv u)).Normal) (Ψ : ↥(stab u) →* Perm (Fin 5))
        (β : M5.W →* ↥(Zv u) ⧸ (Nu u).subgroupOf (Zv u)),
        Function.Surjective Ψ ∧ (∀ x : ↥(stab u), Ψ x = 1 ↔ (x : G) ∈ Qv u) ∧
        SecData M5 (stab u) (Nu u) (Zv u) Ψ β ∧
        ((stab u ⊓ stab μ).subgroupOf (stab u)).map Ψ = S5Syl := by
  have key : ∀ M5 : Model 5, IsModelSec M5 (stab u) (Nu u) (Zv u) →
      ∃ (_ : ((Nu u).subgroupOf (Zv u)).Normal) (Ψ : ↥(stab u) →* Perm (Fin 5))
        (β : M5.W →* ↥(Zv u) ⧸ (Nu u).subgroupOf (Zv u)),
        Function.Surjective Ψ ∧ (∀ x : ↥(stab u), Ψ x = 1 ↔ (x : G) ∈ Qv u) ∧
        SecData M5 (stab u) (Nu u) (Zv u) Ψ β ∧
        ((stab u ⊓ stab μ).subgroupOf (stab u)).map Ψ = S5Syl := by
    intro M5 h
    have hcq := h.cSecIn_eq_pCoreOf (quot_stab_five hA hv)
    obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
    obtain ⟨Ψ, β', hΨs, hΨk, hsd', hPS, -⟩ :=
      SecData.exists_normalized hθs hθk hsd (sylow_stab_inf_left hA hμ)
    refine ⟨hn, Ψ, β', hΨs, fun x => ?_, hsd', hPS⟩
    have := mem_cSecIn_iff_of_ker hΨk x.2
    rw [hcq] at this
    exact this
  rcases hmod with h | h
  · exact ⟨nat, Or.inl rfl, key nat h⟩
  · exact ⟨orth, Or.inr rfl, key orth h⟩

end Model

section Finite

open Equiv in
theorem tabF_orth_swap : ∀ t : Perm (Fin 5), t ∈ S5SylF → t ≠ 1 → t ^ 2 = 1 →
    Perm.sign t ≠ 1 →
    ∃ u : orth.W, ∃ d ∈ S5SylF, orth.act d (orth.act t u * u⁻¹) ≠ orth.act t u * u⁻¹ := by
  decide +kernel

theorem tabF_nat_T : ∃ b ∈ S5TF, ∃ u : nat.W, ∃ d ∈ S5SylF,
    nat.act d (nat.act b u * u⁻¹) ≠ nat.act b u * u⁻¹ := by
  decide +kernel

theorem tabF_orth_fix : ∀ w : orth.W, (∀ σ : Perm (Fin 5), orth.act σ w = w) → w = 1 := by
  decide +kernel

theorem tabF_nat_fix : ∀ w : nat.W, (∀ σ : Perm (Fin 5), nat.act σ w = w) → w = 1 := by
  decide +kernel

theorem tabF_nontriv : (∃ w : orth.W, w ≠ 1) ∧ (∃ w : nat.W, w ≠ 1) := by decide +kernel

open Equiv in
theorem tabF_swap_that : ∀ x ∈ S5SylF, x * x = 1 → Perm.sign x ≠ 1 →
    (x = swap 0 2 ∨ x = swap 1 3) ∧
      ∀ y ∈ S5SylF, y * y = 1 → (x * y) * (x * y) = 1 → y ∈ S5ThatF := by
  decide +kernel

theorem fixW_top_eq_bot (M5 : Model 5) (hM5 : M5 = nat ∨ M5 = orth) : fixW M5 ⊤ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  rcases hM5 with rfl | rfl
  · exact tabF_nat_fix w fun σ => hw σ (Subgroup.mem_top σ)
  · exact tabF_orth_fix w fun σ => hw σ (Subgroup.mem_top σ)

theorem exists_ne_one (M5 : Model 5) (hM5 : M5 = nat ∨ M5 = orth) : ∃ w : M5.W, w ≠ 1 := by
  rcases hM5 with rfl | rfl
  · exact tabF_nontriv.2
  · exact tabF_nontriv.1

theorem card_S5That : Nat.card S5That = 4 := by
  have h : S5ThatF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

theorem offender_core (M5 : Model 5) (hM5 : M5 = nat ∨ M5 = orth) {B : Subgroup (Perm (Fin 5))}
    (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1) (hoff : (fixW M5 B).index ≤ Nat.card B) :
    (fixW M5 B).index = Nat.card B ∧
      ((M5 = nat ∧ Nat.card B = 4 ∧ B ≤ alternatingGroup (Fin 5)) ∨
        (M5 = orth ∧ ((∃ t : Perm (Fin 5), t.IsSwap ∧ B = Subgroup.zpowers t) ∨
          (Nat.card B = 4 ∧ ¬ B ≤ alternatingGroup (Fin 5))))) := by
  obtain ⟨h1, h2⟩ := offender_dichotomy M5 (exists_ne_one M5 hM5) (fixW_top_eq_bot M5 hM5) hne
    hexp hoff
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨hiso, hb⟩ | ⟨hiso, h4, hA5⟩
  · rcases hM5 with rfl | rfl
    · exact absurd hiso nat_not_iso_orth
    · exact Or.inr ⟨rfl, hb⟩
  · rcases hM5 with rfl | rfl
    · exact Or.inl ⟨rfl, h4, hA5⟩
    · exact absurd hiso orth_not_iso_nat

theorem offender_cases_syl (M5 : Model 5) (hM5 : M5 = nat ∨ M5 = orth)
    {B : Subgroup (Perm (Fin 5))} (hBS : B ≤ S5Syl) (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1)
    (hoff : (fixW M5 B).index ≤ Nat.card B) :
    (fixW M5 B).index = Nat.card B ∧
      ((M5 = nat ∧ B = S5T) ∨
        (M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧ B = Subgroup.zpowers t) ∨
        (M5 = orth ∧ B = S5That)) := by
  obtain ⟨h1, h2⟩ := offender_core M5 hM5 hne hexp hoff
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨hM, h4, hA5⟩ | ⟨hM, ⟨t, ht, rfl⟩ | ⟨h4, hA5⟩⟩
  · refine Or.inl ⟨hM, ?_⟩
    exact Subgroup.eq_of_le_of_card_ge (le_inf hBS hA5) (by rw [card_S5T, h4])
  · exact Or.inr (Or.inl ⟨hM, t, ht, hBS (Subgroup.mem_zpowers t), rfl⟩)
  · refine Or.inr (Or.inr ⟨hM, ?_⟩)
    obtain ⟨x, hxB, hx⟩ : ∃ x ∈ B, ¬ x ∈ alternatingGroup (Fin 5) := by
      by_contra hcon
      push Not at hcon
      exact hA5 hcon
    rw [Equiv.Perm.mem_alternatingGroup] at hx
    have hxS : x ∈ S5SylF := (mem_S5Syl_iff x).mp (hBS hxB)
    obtain ⟨-, hy⟩ := tabF_swap_that x hxS (hexp x hxB) hx
    have hle : B ≤ S5That := by
      intro y hyB
      rw [mem_S5That_iff]
      exact hy y ((mem_S5Syl_iff y).mp (hBS hyB)) (hexp y hyB) (hexp _ (B.mul_mem hxB hyB))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_S5That, h4])

open Equiv in
theorem witness_of_cases (M5 : Model 5) {B : Subgroup (Perm (Fin 5))}
    (hcase : (M5 = nat ∧ B = S5T) ∨
        (M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧ B = Subgroup.zpowers t) ∨
        (M5 = orth ∧ B = S5That)) :
    ∃ b ∈ B, ∃ u : M5.W, ∃ d ∈ S5Syl,
      M5.act d (M5.act b u * u⁻¹) ≠ M5.act b u * u⁻¹ := by
  have horth : ∀ t : Perm (Fin 5), t.IsSwap → t ∈ S5Syl → t ∈ B →
      ∃ b ∈ B, ∃ u : orth.W, ∃ d ∈ S5Syl,
        orth.act d (orth.act b u * u⁻¹) ≠ orth.act b u * u⁻¹ := by
    intro t ht htS htB
    obtain ⟨h1, h2, h3⟩ := (isSwap_iff t).mp ht
    obtain ⟨u, d, hd, hne⟩ := tabF_orth_swap t ((mem_S5Syl_iff t).mp htS) h1 h2 h3
    exact ⟨t, htB, u, d, (mem_S5Syl_iff d).mpr hd, hne⟩
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, t, ht, htS, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨b, hb, u, d, hd, hne⟩ := tabF_nat_T
    exact ⟨b, (mem_S5T_iff b).mpr hb, u, d, (mem_S5Syl_iff d).mpr hd, hne⟩
  · exact horth t ht htS (Subgroup.mem_zpowers t)
  · refine horth (swap 0 2) ⟨0, 2, by decide, rfl⟩ ((mem_S5Syl_iff _).mpr (by decide +kernel)) ?_
    rw [mem_S5That_iff]
    decide +kernel

end Finite

section Offender

structure VuModule (u μ : Geo H M) where
  M5 : Model 5
  isModel : M5 = nat ∨ M5 = orth
  norm : ((Nu u).subgroupOf (Zv u)).Normal
  Ψ : ↥(stab u) →* Perm (Fin 5)
  β : M5.W →* ↥(Zv u) ⧸ (Nu u).subgroupOf (Zv u)
  surj : Function.Surjective Ψ
  ker : ∀ x : ↥(stab u), Ψ x = 1 ↔ (x : G) ∈ Qv u
  secData : SecData M5 (stab u) (Nu u) (Zv u) Ψ β
  sylow : ((stab u ⊓ stab μ).subgroupOf (stab u)).map Ψ = S5Syl

def VuModule.Zbar {u μ : Geo H M} (V : VuModule u μ) (δ : Geo H M) : Subgroup (Perm (Fin 5)) :=
  ((Zv δ).subgroupOf (stab u)).map V.Ψ

theorem nonempty_VuModule (hA : F53Amalgam H M S) {u μ : Geo H M} (hμ : μ ∈ nbrs u)
    (hv : vtype u = false)
    (hmod : IsNatSec (stab u) (Nu u) (Zv u) ∨ IsOrthSec (stab u) (Nu u) (Zv u)) :
    Nonempty (VuModule u μ) := by
  obtain ⟨M5, hM, hn, Ψ, β, h1, h2, h3, h4⟩ := Vu_model hA hμ hv hmod
  exact ⟨⟨M5, hM, hn, Ψ, β, h1, h2, h3, h4⟩⟩

variable {α β α' : Geo H M}

theorem Zv_inf_centralizer_eq_Qv (hA : F53Amalgam H M S) (h27 : Hss27At H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {u δ : Geo H M} (hle : Zv u ≤ stab δ) :
    Zv u ⊓ Subgroup.centralizer (Zv δ : Set G) = Zv u ⊓ Qv δ := by
  have h := centralizer_Zv_eq_Qv_all hA h27 hc hv hn δ
  ext x
  constructor
  · rintro ⟨hxu, hxc⟩
    refine ⟨hxu, ?_⟩
    rw [← h]
    exact ⟨hle hxu, hxc⟩
  · rintro ⟨hxu, hxQ⟩
    refine ⟨hxu, ?_⟩
    rw [← h] at hxQ
    exact hxQ.2

theorem F1a_relIndex (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {u δ : Geo H M} (hcp : IsCritPair₁ u δ) (hne : ⁅Zv u, Zv δ⁆ ≠ ⊥) :
    (Zv u ⊓ Subgroup.centralizer (Zv δ : Set G)).relIndex (Zv u) =
      (Zv δ ⊓ Qv u).relIndex (Zv δ) := by
  rw [Zv_inf_centralizer_eq_Qv hA h27 hc hv hn (Zv_le_stab_of_dist_le' hA hcp.2.le)]
  exact h113a u δ hcp hne

theorem F1a_card (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {u δ μ : Geo H M} (hcp : IsCritPair₁ u δ) (hne : ⁅Zv u, Zv δ⁆ ≠ ⊥) (hδ : Zv δ ≤ stab u)
    (V : VuModule u μ) :
    (Zv u ⊓ Subgroup.centralizer (Zv δ : Set G)).relIndex (Zv u) = Nat.card (V.Zbar δ) := by
  rw [F1a_relIndex hA h27 h113a hc hv hn hcp hne, VuModule.Zbar,
    card_map_subgroupOf_eq V.Ψ V.ker hδ, Subgroup.inf_relIndex_left]

theorem fixW_index_le {u μ : Geo H M} (V : VuModule u μ) (hLX : Nu u ≤ Zv u) {δ : Geo H M}
    (hδ : Zv δ ≤ stab u) :
    (fixW V.M5 (V.Zbar δ)).index ≤
      (Zv u ⊓ Subgroup.centralizer (Zv δ : Set G)).relIndex (Zv u) := by
  have := V.norm
  have h1 := V.secData.relIndex_fixSecIn hLX hδ
  have hle : Zv u ⊓ Subgroup.centralizer (Zv δ : Set G) ≤ fixSecIn (Zv δ) (Nu u) (Zv u) := by
    intro x hx
    refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hx.2 a ha
    rw [this]
    simp
  rw [VuModule.Zbar, ← h1]
  exact Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite

theorem offender_cases (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    {u δ μ : Geo H M} (hcp : IsCritPair₁ u δ) (hne : ⁅Zv u, Zv δ⁆ ≠ ⊥) (hδu : Zv δ ≤ stab u)
    (hδμ : Zv δ ≤ stab μ) (hδQ : ¬ Zv δ ≤ Qv u) (V : VuModule u μ) :
    V.Zbar δ ≤ S5Syl ∧ V.Zbar δ ≠ ⊥ ∧
      (fixW V.M5 (V.Zbar δ)).index = Nat.card (V.Zbar δ) ∧
      ((V.M5 = nat ∧ V.Zbar δ = S5T) ∨
        (V.M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧ V.Zbar δ = Subgroup.zpowers t) ∨
        (V.M5 = orth ∧ V.Zbar δ = S5That)) := by
  have hLX : Nu u ≤ Zv u := inf_le_left
  have hBS : V.Zbar δ ≤ S5Syl := by
    rw [VuModule.Zbar, ← V.sylow]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.2, hδμ hx⟩
  have hbot : V.Zbar δ ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp hδQ
    have hmem : V.Ψ ⟨z, hδu hz⟩ ∈ V.Zbar δ := ⟨⟨z, hδu hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hzQ ((V.ker _).mp hmem)
  have hexp : ∀ x ∈ V.Zbar δ, x * x = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz2 : (z : G) ^ 2 = 1 :=
      isElemAbelian_pow_eq_one (isElemAbelian_Zv hA δ) (Subgroup.mem_subgroupOf.mp hz)
    rw [← map_mul]
    have : z * z = 1 := Subtype.ext (by simpa [pow_two] using hz2)
    rw [this, map_one]
  have hoff : (fixW V.M5 (V.Zbar δ)).index ≤ Nat.card (V.Zbar δ) := by
    rw [← F1a_card hA h27 h113a hc hv hn hcp hne hδu V]
    exact fixW_index_le V hLX hδu
  obtain ⟨h1, h2⟩ := offender_cases_syl V.M5 V.isModel hBS hbot hexp hoff
  exact ⟨hBS, hbot, h1, h2⟩

end Offender

section Assembly

variable {α β α' u c c' : Geo H M} {y : ↥(H ⊔ M)}

theorem StepFPts.star_le_stab_u (hA : F53Amalgam H M S) (P : StepFPts α β α' u c c' y) :
    Zv (y • β) ≤ stab u :=
  P.star_le_Qα'.trans (Qv_le_stab_of_mem_nbrs hA P.u_crit.adj)

theorem StepFPts.star_le_stab_α' (P : StepFPts α β α' u c c' y) : Zv (y • β) ≤ stab α' :=
  P.star_le_Qα'.trans (pCoreOf_le 2 (stab α'))

theorem StepFPts.uStar (hA : F53Amalgam H M S) (P : StepFPts α β α' u c c' y) :
    IsCritPair₁ u (y • β) ∧ ⁅Zv u, Zv (y • β)⁆ ≠ ⊥ := by
  have hne : ⁅Zv (y • β), Zv u⁆ ≠ ⊥ := by rw [P.star_comm]; exact P.R₁_ne
  exact isCritPair₁_symm_of_comm_ne hA P.star_pair hne

theorem stepF_VuModule (hA : F53Amalgam H M S) (h113c : Hss113cAt H M)
    (P : StepFPts α β α' u c c' y) : Nonempty (VuModule u α') := by
  obtain ⟨hcp, hne⟩ := P.uStar hA
  exact nonempty_VuModule hA (mem_nbrs_symm' P.u_crit.adj) P.u_type
    (h113c u (y • β) hcp hne P.u_type)

theorem stepF_offender_cases (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hv : vtype α = true) (hn : ¬ Zv β ≤ centerOf (stab β))
    (P : StepFPts α β α' u c c' y) (V : VuModule u α') :
    V.Zbar (y • β) ≤ S5Syl ∧ V.Zbar (y • β) ≠ ⊥ ∧
      (fixW V.M5 (V.Zbar (y • β))).index = Nat.card (V.Zbar (y • β)) ∧
      ((V.M5 = nat ∧ V.Zbar (y • β) = S5T) ∨
        (V.M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧
          V.Zbar (y • β) = Subgroup.zpowers t) ∨
        (V.M5 = orth ∧ V.Zbar (y • β) = S5That)) := by
  obtain ⟨hcp, hne⟩ := P.uStar hA
  exact offender_cases hA h27 h113a hc hv hn hcp hne (P.star_le_stab_u hA) P.star_le_stab_α'
    P.star_pair.1 V

theorem StepFPts.Zc_le_stab_u (hA : F53Amalgam H M S) (P : StepFPts α β α' u c c' y) :
    Zv c ≤ stab u ∧ Zv u ≤ stab c :=
  ⟨Zv_le_stab_of_dist_le' hA P.cu_dist.le,
    Zv_le_stab_of_dist_le' hA (by rw [CosetGeom.dist_comm]; exact P.cu_dist.le)⟩

theorem StepFPts.Zc_le_Qβ (hA : F53Amalgam H M S) (hb4 : 4 ≤ bMin H M)
    (hc : IsCritData α β α') (P : StepFPts α β α' u c c' y) : Zv c ≤ Qv β := by
  have h1 := dist_triangle hA.amalgam.gen c α β
  have hcα : dist c α = 1 :=
    dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj c α from mem_nbrs_symm' P.c_nbr)
  have hαβ : dist α β = 1 := dist_eq_one_iff_adj.mpr hc.adj
  exact Zv_le_Qv_of_dist_lt' (by omega)

end Assembly

end F53.Stellmacher

end CFSG.Quasithin
