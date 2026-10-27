module

public import CFSG.Quasithin.MS93.S46Stmt
public import CFSG.Quasithin.MS93.S46Type
public import CFSG.Quasithin.MS93.S46Aux
public import CFSG.Quasithin.MS93.S46FFGrp
public import CFSG.Quasithin.MS93.S46Ker
public import CFSG.Quasithin.MS93.S46Gen

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))
include h hφ hC

omit [Fintype F] hφ hC in
theorem stab_le_normalizer_centerOf_vv (α : Vtx (puAmalgam h.le)) :
    stab _ α ≤ Subgroup.normalizer (centerOf (Vv (puAmalgam h.le) α) : Set _) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← PU.centerOf_map (MulAut.conj g).injective,
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h α hg)]

omit [Fintype F] hφ hC in
theorem zm_le_centerOf_vv (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) : ZM (puAmalgam h.le) α ≤ centerOf (Vv _ α) :=
  le_inf (zm_le_vv h hα) ((zm_le_centralizer_qv _ h.hyp20 hα).trans
    (Subgroup.centralizer_le (vv_le_qv h hb hα)))

theorem centerOf_vv_le_bloc_of_commutator_le (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤ ZM _ α) :
    centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hKρ : ZM (puAmalgam h.le) α' ≤ Qv _ (geo _ α α' 1) :=
    zm_le_qv_geo_one _ h.hyp20 hb0 hc
  have hKQ : ¬ ZM (puAmalgam h.le) α' ≤ Qv _ α := hc'.2.2
  have hL := commutator_ltil_le_of_commutator_le h hfull hc.1 hβ
    (stab_le_normalizer_centerOf_vv h α) (stab_le_normalizer_zm _ α) hN hKρ hKQ
  intro x hx
  rw [mem_bloc_iff h hb hc.1]
  exact ⟨hx.1, fun l hl => hL (Subgroup.commutator_mem_commutator hx hl)⟩

theorem commutator_centerOf_zm_le (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h20
  set γ := geo (puAmalgam h.le) α α' 2
  set ε := geo (puAmalgam h.le) α α' 3
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hNγ : centerOf (Vv (puAmalgam h.le) α) ≤ Qv _ γ :=
    centerOf_vv_le_qv h20 hC hb hc.1 hγ (dist_geo_crit hb4 hc (by omega))
  have hγε : (puAmalgam h.le).treeGraph.Adj γ ε := adj_geo_crit hb4 hc (by omega)
  have hεα' : (puAmalgam h.le).treeGraph.Adj ε α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [geo_four hb4 hc] at this
  have hNs : centerOf (Vv (puAmalgam h.le) α) ≤ stab _ α' :=
    hNγ.trans ((qv_le_qv _ h20 hγ hγε).trans (qv_le_stab_of_adj _ hεα'))
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hNs]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hNs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α')) |>.trans' (by
        rw [Subgroup.commutator_comm])
  · have h1 : ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤ centerOf (Vv _ α) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZs.trans (stab_le_normalizer_centerOf_vv h α)) |>.trans' (by
          rw [Subgroup.commutator_comm])
    exact h1.trans (inf_le_left.trans ((vv_le_qv h hb hc.1).trans
      (zm_le_centralizer_qv _ h20 hc.1 |> fun h' => Subgroup.le_centralizer_iff.mp h')))

theorem centerOf_vv_le_bloc_of_not_typeII (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hnot : ¬ ((Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F)) :
    centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hnot' : ¬ ((Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α') = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α' α) = Fintype.card F) := by
    rw [← relIndex_zm_comm h hφ hC hc, critR, Subgroup.commutator_comm, ← critR]
    exact hnot
  have hR := uloc_inf_centralizer_eq_critR h hφ hC hc' hnot'
  refine centerOf_vv_le_bloc_of_commutator_le h hφ hC hb hc ?_
  refine (commutator_centerOf_zm_le h hφ hC hb4 hc).trans ?_
  rw [hR, critR, Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc).trans (stab_le_normalizer_zm _ α)) |>.trans'
      (by rw [Subgroup.commutator_comm])

theorem commutator_zm_qv_le_centerOf (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅ZM (puAmalgam h.le) α', Qv _ (geo _ α' α 1)⁆ ≤ centerOf (Vv _ α) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hII : (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F := by
    by_contra hnot
    exact hN (centerOf_vv_le_bloc_of_not_typeII h hφ hC hb4 hc hnot)
  have hII' : (Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α') = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α' α) = Fintype.card F := by
    rw [← relIndex_zm_comm h hφ hC hc, critR, Subgroup.commutator_comm, ← critR]
    exact hII
  set N := centerOf (Vv (puAmalgam h.le) α) with hNdef
  set ε := geo (puAmalgam h.le) α' α 1 with hεdef
  set γ := geo (puAmalgam h.le) α α' 2
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hεeq : ε = geo (puAmalgam h.le) α α' 3 := geo_rev_one hb4 hc
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' ε := adj_geo_one_of_isCritical _ hb0 hc'
  have hγε : (puAmalgam h.le).treeGraph.Adj γ ε := by
    rw [hεeq]; exact adj_geo_crit hb4 hc (by omega)
  have hNγ : N ≤ Qv _ γ := centerOf_vv_le_qv h20 hC hb hc.1 hγ (dist_geo_crit hb4 hc (by omega))
  have hNε : N ≤ Qv _ ε := hNγ.trans (qv_le_qv _ h20 hγ hγε)
  have hNs : N ≤ stab _ α' := hNε.trans (qv_le_stab_of_adj _ hα'ε.symm)
  have hUN : ⁅Uloc h.le L α', N⁆ = ⁅N, ZM _ α'⁆ := by
    rw [Subgroup.commutator_comm N, commutator_zm_eq_uloc h hfull hα' hNs]
  have hRle : critR (puAmalgam h.le) α' α ≤ ⁅Uloc h.le L α', N⁆ := by
    rw [critR, commutator_zm_eq_uloc h hfull hα' ((zm_le_stab_right _ h20 hb0 hC hc))]
    exact Subgroup.commutator_mono le_rfl (zm_le_centerOf_vv h hb hc.1)
  have hle : ⁅Uloc h.le L α', N⁆ ≤ Uloc h.le L α' ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
    rw [hUN]; exact commutator_centerOf_zm_le h hφ hC hb4 hc
  rcases commutator_uloc_eq_of_le h hφ hα' hα'ε hNε hII'.2
      (card_uloc_inf_centralizer_typeII h hφ hC hc' hII') hRle hle with heq | heq
  · exfalso
    apply hN
    refine centerOf_vv_le_bloc_of_commutator_le h hφ hC hb hc ?_
    rw [← hUN, heq, critR, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ α)) |>.trans'
        (by rw [Subgroup.commutator_comm])
  ·
    obtain ⟨d, hd, hcard⟩ := card_commutator_uloc_le h hφ hα' hα'ε (le_refl (Qv _ ε))
    have hsub : ⁅Uloc h.le L α', N⁆ ≤ ⁅Uloc h.le L α', Qv _ ε⁆ :=
      Subgroup.commutator_mono le_rfl hNε
    have hcardN : Nat.card ↥⁅Uloc h.le L α', N⁆ = Fintype.card F ^ 2 := by
      rw [heq]; exact card_uloc_inf_centralizer_typeII h hφ hC hc' hII'
    have hfinS : Finite ↥(stab (puAmalgam h.le) α') := finite_stab h hα'
    have hUε : ⁅Uloc h.le L α', Qv (puAmalgam h.le) ε⁆ ≤ Uloc h.le L α' :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp ((qv_le_stab_of_adj _ hα'ε.symm).trans
        (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'))
    have hfinT : Finite ↥⁅Uloc h.le L α', Qv (puAmalgam h.le) ε⁆ :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        (hUε.trans (puTrans_le_stab h.le _ α')))
    have hq1 : 0 < Fintype.card F := Fintype.card_pos
    have heq2 : ⁅Uloc h.le L α', N⁆ = ⁅Uloc h.le L α', Qv _ ε⁆ := by
      refine Subgroup.eq_of_le_of_card_ge hsub ?_
      rw [hcard, hcardN]
      exact Nat.pow_le_pow_right hq1 hd
    rw [commutator_zm_eq_uloc h hfull hα' (qv_le_stab_of_adj _ hα'ε.symm), ← heq2, hUN]
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans
        (stab_le_normalizer_centerOf_vv h α)) |>.trans' (by rw [Subgroup.commutator_comm])

theorem commutator_vv_inf_qv_le_centerOf (hb4 : critDist (puAmalgam h.le) = 4)
    {α δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α δ)
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α ⊓ Qv _ (geo _ α δ 2), ZM _ δ⁆ ≤ centerOf (Vv _ α) := by
  have h20 := h.hyp20
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α δ 2) := isMVtx_geo_two' hb4 hc
  have hγε : (puAmalgam h.le).treeGraph.Adj (geo _ α δ 2) (geo _ δ α 1) := by
    rw [geo_rev_one hb4 hc]; exact adj_geo_crit hb4 hc (by omega)
  refine (Subgroup.commutator_mono (inf_le_right.trans (qv_le_qv _ h20 hγ hγε)) le_rfl).trans ?_
  rw [Subgroup.commutator_comm]
  exact commutator_zm_qv_le_centerOf h hφ hC hb4 hc hN

end Basic

section GroupAux

variable {𝔾 : Type} [Group 𝔾]

theorem relIndex_le_of_le_sup {S H K Q : Subgroup 𝔾} [Finite ↥S] (hHS : H ≤ S) (hKS : K ≤ S)
    (hQS : Q ≤ S) (hQn : S ≤ Subgroup.normalizer (Q : Set 𝔾)) (hHK : H ≤ K ⊔ Q) :
    Q.relIndex H ≤ Q.relIndex K := by
  have hQn' : (Q.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQS).2 hQn
  rw [← Subgroup.relIndex_subgroupOf hHS, ← Subgroup.relIndex_subgroupOf hKS,
    ← Subgroup.relIndex_sup_right (H := K.subgroupOf S) (K := Q.subgroupOf S)]
  refine Subgroup.relIndex_le_of_le_right ?_ (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  intro x hx
  have hx' : (x : 𝔾) ∈ K ⊔ Q := hHK (Subgroup.mem_subgroupOf.mp hx)
  rw [← Subgroup.subgroupOf_sup hKS hQS]
  exact Subgroup.mem_subgroupOf.mpr hx'

theorem sq_mem_commutator_of_iSup {ι : Type*} {Z : ι → Subgroup 𝔾}
    (hZ : ∀ i, ∀ z ∈ Z i, z ^ 2 = 1) {a : 𝔾} (ha : a ∈ ⨆ i, Z i) :
    a ^ 2 ∈ ⁅⨆ i, Z i, ⨆ i, Z i⁆ := by
  have hmem : ∀ x ∈ Subgroup.closure (⋃ i, (Z i : Set 𝔾)), x ∈ ⨆ i, Z i := fun x hx => by
    rw [Subgroup.iSup_eq_closure]; exact hx
  rw [Subgroup.iSup_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rw [hZ i z hi]
    exact Subgroup.one_mem _
  | one => simp
  | mul a b haV hbV iha ihb =>
    have haV' : a ∈ ⨆ i, Z i := hmem a haV
    have hbV' : b ∈ ⨆ i, Z i := hmem b hbV
    have e : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
      simp only [commutatorElement_def, sq]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ iha
      (Subgroup.commutator_mem_commutator ((⨆ i, Z i).inv_mem haV') hbV')) ihb
  | inv a _ iha =>
    rw [inv_pow]
    exact Subgroup.inv_mem _ iha

theorem sq_eq_one_of_mem_commutator {V : Subgroup 𝔾} (hVc : ⁅V, V⁆ ≤ centerOf V)
    (hsq : ∀ a ∈ V, a ^ 2 ∈ ⁅V, V⁆) {k : 𝔾} (hk : k ∈ ⁅V, V⁆) : k ^ 2 = 1 := by
  have hcen : ∀ c ∈ ⁅V, V⁆, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
    (Subgroup.mem_centralizer_iff.mp (hVc hc).2 v hv).symm
  rw [Subgroup.commutator_def] at hk
  induction hk using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    have hab : ⁅a, b⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator ha hb
    have hcab := hcen _ hab
    have ha2 : a ^ 2 * b = b * a ^ 2 := hcen _ (hsq a ha) b hb
    have key : ⁅a, b⁆ ^ 2 = ⁅a ^ 2, b⁆ := by
      have h1 : a * ⁅a, b⁆ = ⁅a, b⁆ * a := (hcab a ha).symm
      calc ⁅a, b⁆ ^ 2 = ⁅a, b⁆ * a * (b * a⁻¹ * b⁻¹) := by
            simp only [sq, commutatorElement_def]; group
        _ = a * ⁅a, b⁆ * (b * a⁻¹ * b⁻¹) := by rw [h1]
        _ = ⁅a ^ 2, b⁆ := by simp only [sq, commutatorElement_def]; group
    rw [key, commutatorElement_def, ha2]
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ ⁅V, V⁆ := by rw [Subgroup.commutator_def]; exact hx
    have hy' : y ∈ ⁅V, V⁆ := by rw [Subgroup.commutator_def]; exact hy
    have hxy : x * y = y * x := hcen x hx' y (hVc hy').1
    rw [(Commute.mul_pow hxy 2), ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

end GroupAux

section CritGen

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def critGen (α γ : Vtx X) : Subgroup X.Universal :=
  ⨆ δ ∈ {δ : Vtx X | IsCritical X α δ ∧ geo X α δ 2 = γ}, ZM X δ

variable {X}

theorem critGen_le_vv (hb4 : critDist X = 4) (α γ : Vtx X) : critGen X α γ ≤ Vv X γ := by
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨hc, hγ⟩ := hδ
  have hd : X.treeGraph.dist γ δ ≤ 2 := by
    rw [← hγ, dist_geo_crit_right hb4 hc (by omega)]
  have hδM : IsMVtx X δ := by
    have h4 := (isMVtx_geo_crit hb4 hc (i := 4) le_rfl).mpr (by decide)
    rwa [geo_four hb4 hc] at h4
  have : Zv X δ ≤ Vv X γ := le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx X |
    X.treeGraph.dist γ μ ≤ 2}) => Zv X μ) δ hd le_rfl
  rwa [zv_of_isMVtx X hδM] at this

theorem vv_le_critGen_sup (h : Hyp20 X) (hC : CentHyp X) (hb4 : critDist X = 4)
    {α γ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist α γ = 2) :
    Vv X γ ≤ critGen X α γ ⊔ Qv X α := by
  have hb0 : 0 < critDist X := by omega
  refine iSup₂_le fun x hx => ?_
  have hx' : X.treeGraph.dist γ x ≤ 2 := hx
  have htri := dist_triangle X α γ x
  by_cases hxM : IsMVtx X x
  · rw [zv_of_isMVtx X hxM]
    by_cases h3 : X.treeGraph.dist α x ≤ 3
    · exact (zm_le_qv_of_dist_le_three hb4 hxM (by rw [tdist_comm]; exact h3)).trans
        le_sup_right
    · have h4 : X.treeGraph.dist α x = 4 := by omega
      have hgeo : γ = geo X α x 2 := eq_geo_of_dist X hd (by omega)
      by_cases hZ : ZM X x ≤ Qv X α
      · exact hZ.trans le_sup_right
      · have hc : IsCritical X x α := ⟨hxM, by rw [tdist_comm, h4, hb4], hZ⟩
        have hc' := ms22_iii X h hb0 hC hc
        exact (le_iSup₂_of_le (f := fun δ (_ : δ ∈ {δ : Vtx X | IsCritical X α δ ∧
          geo X α δ 2 = γ}) => ZM X δ) x ⟨hc', hgeo.symm⟩ le_rfl).trans le_sup_left
  · rw [zv_of_not_isMVtx X hxM]
    have hodd : ¬ Even (X.treeGraph.dist γ x) := by rw [even_dist_iff]; tauto
    have h1 : X.treeGraph.dist γ x = 1 := by
      rcases (by omega : X.treeGraph.dist γ x = 0 ∨ X.treeGraph.dist γ x = 1 ∨
          X.treeGraph.dist γ x = 2) with e | e | e
      · exact absurd (by rw [e]; exact ⟨0, rfl⟩) hodd
      · exact e
      · exact absurd (by rw [e]; exact ⟨1, rfl⟩) hodd
    have hadj : X.treeGraph.Adj γ x := SimpleGraph.dist_eq_one_iff_adj.mp h1
    exact ((zh_le_zm X hadj).trans (zm_le_qv_of_dist_le_three hb4 hγ
      (by rw [tdist_comm, hd]; omega))).trans le_sup_right

end CritGen

section CritGenPU

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))
include h hφ hC

theorem commutator_critGen_le (hb4 : critDist (puAmalgam h.le) = 4)
    {α γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hd : (puAmalgam h.le).treeGraph.dist α γ = 2)
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α ⊓ Qv _ γ, critGen _ α γ⁆ ≤ centerOf (Vv _ α) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  set β := geo (puAmalgam h.le) α γ 1
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one _ (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := γ) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist α γ ≤ 1 + 1)] at this
  have hWs : critGen (puAmalgam h.le) α γ ≤ stab _ α :=
    (critGen_le_vv hb4 α γ).trans ((vv_le_qv h hb hγ).trans
      ((qv_le_qv _ h.hyp20 hγ hβγ.symm).trans (qv_le_stab_of_adj _ hαβ.symm)))
  rw [Subgroup.commutator_comm, critGen, iSup_subtype']
  refine commutator_iSup_le_of (fun δ => ?_) ?_
  · obtain ⟨δ, hc, hgeo⟩ := δ
    rw [Subgroup.commutator_comm]
    have := commutator_vv_inf_qv_le_centerOf h hφ hC hb4 hc hN
    rwa [hgeo] at this
  · rw [← iSup_subtype' (f := fun δ (_ : δ ∈ {δ : Vtx (puAmalgam h.le) |
      IsCritical (puAmalgam h.le) α δ ∧ geo (puAmalgam h.le) α δ 2 = γ}) =>
        ZM (puAmalgam h.le) δ), ← critGen]
    exact hWs.trans (stab_le_normalizer_centerOf_vv h α)

omit hφ hC in
theorem sq_mem_commutator_vv (hb0 : 0 < critDist (puAmalgam h.le)) {γ : Vtx (puAmalgam h.le)}
    {a : (puAmalgam h.le).Universal} (ha : a ∈ Vv (puAmalgam h.le) γ) :
    a ^ 2 ∈ ⁅Vv (puAmalgam h.le) γ, Vv (puAmalgam h.le) γ⁆ := by
  have h20 := h.hyp20
  have hV : Vv (puAmalgam h.le) γ =
      ⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2},
        Zv (puAmalgam h.le) ρ := by
    rw [show Vv (puAmalgam h.le) γ = Vi (puAmalgam h.le) γ 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  have hZ2 : ∀ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2},
      ∀ z ∈ Zv (puAmalgam h.le) ρ, z ^ 2 = 1 := by
    intro ρ z hz
    by_cases hρ : IsMVtx (puAmalgam h.le) ρ.1
    · rw [zv_of_isMVtx _ hρ] at hz
      exact (isElemAbelian_zm _ h20 hb0 hρ).2 z hz
    · rw [zv_of_not_isMVtx _ hρ] at hz
      obtain ⟨δ, hδ⟩ := exists_adj (puAmalgam h.le) ρ.1
      have hδM : IsMVtx (puAmalgam h.le) δ := by have := isMVtx_iff_of_adj _ hδ; tauto
      exact (isElemAbelian_zm _ h20 hb0 hδM).2 z (zh_le_zm _ hδ.symm hz)
  have hsq := sq_mem_commutator_of_iSup hZ2 (hV ▸ ha)
  rwa [← hV] at hsq

omit hφ hC in
theorem sq_mem_centerOf_vv (h39 : S39) (hfull : IsSL3Full M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    {a : (puAmalgam h.le).Universal} (ha : a ∈ Vv (puAmalgam h.le) γ) :
    a ^ 2 ∈ centerOf (Vv (puAmalgam h.le) γ) :=
  h39 G M T L h hb4 hfull γ hγ (sq_mem_commutator_vv h (by omega) ha)

theorem exists_offender_centerOf (h39 : S39) (h43 : S43) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α)
    (hNγ : ¬ centerOf (Vv (puAmalgam h.le) (geo _ α α' 2)) ≤ Bloc h.le L (geo _ α α' 2)) :
    (∃ As, IsOffenderOn (puAmalgam h.le) α (centerOf (Vv _ α)) As) ∨
      (∃ As, IsOffenderOn (puAmalgam h.le) (geo _ α α' 2)
        (centerOf (Vv _ (geo _ α α' 2))) As) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hd' : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hd
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hVαγ : ¬ Vv (puAmalgam h.le) α ≤ Qv _ γ := by
    have := h43 G M T L h hmin hb hfull α α' hc
    rwa [geo_rev_two hb4 hc] at this
  have hW₂ : ¬ critGen (puAmalgam h.le) γ α ≤ Qv _ γ := fun hle =>
    hVαγ ((vv_le_critGen_sup h20 hC hb4 hc.1 hd').trans (sup_le hle le_rfl))
  obtain ⟨μ, hcμ, hgeoμ⟩ : ∃ μ, IsCritical (puAmalgam h.le) γ μ ∧
      geo (puAmalgam h.le) γ μ 2 = α := by
    by_contra hno
    apply hW₂
    refine iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim
  have hVγα : ¬ Vv (puAmalgam h.le) γ ≤ Qv _ α := by
    have := h43 G M T L h hmin hb hfull γ μ hcμ
    rwa [geo_rev_two hb4 hcμ, hgeoμ] at this
  have hW₁ : ¬ critGen (puAmalgam h.le) α γ ≤ Qv _ α := fun hle =>
    hVγα ((vv_le_critGen_sup h20 hC hb4 hγ hd).trans (sup_le hle le_rfl))
  have hsqγ : ∀ a ∈ Vv (puAmalgam h.le) γ, a ^ 2 ∈ Qv _ α := fun a ha =>
    centerOf_vv_le_qv h20 hC hb hγ hc.1 hd' (sq_mem_centerOf_vv h h39 hfull hb4 hγ ha)
  have hcomγ : ∀ a ∈ Vv (puAmalgam h.le) γ, ∀ b ∈ Vv (puAmalgam h.le) γ, ⁅a, b⁆ ∈ Qv _ α :=
    fun a ha b hb' => centerOf_vv_le_qv h20 hC hb hγ hc.1 hd'
      (h39 G M T L h hb4 hfull γ hγ (Subgroup.commutator_mem_commutator ha hb'))
  have hsqα : ∀ a ∈ Vv (puAmalgam h.le) α, a ^ 2 ∈ Qv _ γ := fun a ha =>
    centerOf_vv_le_qv h20 hC hb hc.1 hγ hd (sq_mem_centerOf_vv h h39 hfull hb4 hc.1 ha)
  have hcomα : ∀ a ∈ Vv (puAmalgam h.le) α, ∀ b ∈ Vv (puAmalgam h.le) α, ⁅a, b⁆ ∈ Qv _ γ :=
    fun a ha b hb' => centerOf_vv_le_qv h20 hC hb hc.1 hγ hd
      (h39 G M T L h hb4 hfull α hc.1 (Subgroup.commutator_mem_commutator ha hb'))
  have hfinα := finite_stab h hc.1
  have hfinγ := finite_stab h hγ
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβs' : Qv (puAmalgam h.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hVγβ : Vv (puAmalgam h.le) γ ≤ Qv _ β :=
    (vv_le_qv h hb hγ).trans (qv_le_qv _ h20 hγ hβγ.symm)
  have hVαβ : Vv (puAmalgam h.le) α ≤ Qv _ β :=
    (vv_le_qv h hb hc.1).trans (qv_le_qv _ h20 hc.1 hαβ)
  have hb1 : (Qv (puAmalgam h.le) α).relIndex (Vv _ γ) ≤
      (Qv (puAmalgam h.le) α).relIndex (critGen _ α γ) :=
    relIndex_le_of_le_sup (S := stab _ α) (hVγβ.trans hβs)
      (((critGen_le_vv hb4 α γ).trans hVγβ).trans hβs) (qv_le_stab _ α)
      (stab_le_normalizer_qv _ α) (vv_le_critGen_sup h20 hC hb4 hγ hd)
  have ha1 : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) γ).relIndex (critGen _ γ α) :=
    relIndex_le_of_le_sup (S := stab _ γ) (hVαβ.trans hβs')
      (((critGen_le_vv hb4 γ α).trans hVαβ).trans hβs') (qv_le_stab _ γ)
      (stab_le_normalizer_qv _ γ) (vv_le_critGen_sup h20 hC hb4 hc.1 hd')
  by_cases hab : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) α).relIndex (Vv _ γ)
  · left
    refine ⟨critGen _ α γ, ⟨β, hαβ, (critGen_le_vv hb4 α γ).trans hVγβ⟩, hW₁,
      fun a ha => hsqγ a (critGen_le_vv hb4 α γ ha),
      fun a ha b hb' => hcomγ a (critGen_le_vv hb4 α γ ha) b (critGen_le_vv hb4 α γ hb'),
      Vv _ α ⊓ Qv _ γ, le_inf inf_le_left (centerOf_vv_le_qv h20 hC hb hc.1 hγ hd),
      inf_le_left, commutator_critGen_le h hφ hC hb4 hγ hd hNα, ?_⟩
    rw [Subgroup.inf_relIndex_left]
    exact hab.trans hb1
  · right
    refine ⟨critGen _ γ α, ⟨β, hβγ.symm, (critGen_le_vv hb4 γ α).trans hVαβ⟩, hW₂,
      fun a ha => hsqα a (critGen_le_vv hb4 γ α ha),
      fun a ha b hb' => hcomα a (critGen_le_vv hb4 γ α ha) b (critGen_le_vv hb4 γ α hb'),
      Vv _ γ ⊓ Qv _ α, le_inf inf_le_left (centerOf_vv_le_qv h20 hC hb hγ hc.1 hd'),
      inf_le_left, commutator_critGen_le h hφ hC hb4 hc.1 hd' hNγ, ?_⟩
    rw [Subgroup.inf_relIndex_left]
    exact (le_of_lt (not_le.mp hab)).trans ha1

omit hC in
theorem false_of_offender_centerOf (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (h39 : S39) (hb4 : critDist (puAmalgam h.le) = 4) {x : Vtx (puAmalgam h.le)}
    (hx : IsMVtx _ x) {As : Subgroup (puAmalgam h.le).Universal}
    (hA : IsOffenderOn (puAmalgam h.le) x (centerOf (Vv _ x)) As)
    (hD : ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Dloc h.le L x)
    (hne : ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≠ ⊥) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, hF⟩ := hφ.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hx
  have hfinS : Finite ↥(stab (puAmalgam h.le) x) := finite_stab h hx
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ x := (vv_le_qv h hb hx).trans (qv_le_stab _ x)
  have hfinV : Finite ↥(Vv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  set V := Vv (puAmalgam h.le) x with hVdef
  set K' := ⁅V, V⁆ with hK'def
  have h39x : K' ≤ centerOf V := h39 G M T L h hb4 hfull x hx
  have hK'V : K' ≤ V := h39x.trans inf_le_left
  have hK's : K' ≤ stab (puAmalgam h.le) x := hK'V.trans hVs
  have hVn := stab_le_normalizer_vv h x
  have hK'n : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (K' : Set _) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [hK'def, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hVn hg)]
  have hfinKQ : Finite ↥(K' ⊔ Qv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hK's (qv_le_stab _ x)))
  have hLK : ⁅K', Ltil h.le L x⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have := hD.trans (le_of_eq (h.puTrans_Dq hx))
    exact this.trans inf_le_right
  obtain ⟨K'', -, hK''K', hK''n, hidx, hK'X⟩ :=
    exists_inv_index_two (X := stab (puAmalgam h.le) x) (L := Ltil h.le L x)
      (Q := Qv (puAmalgam h.le) x) (K₀ := ⊥) (K' := K')
      (fun k hk k' hk' => (Subgroup.mem_centralizer_iff.mp (h39x hk).2 k' (hK'V hk')).symm)
      (fun k hk => sq_eq_one_of_mem_commutator h39x
        (fun a ha => sq_mem_commutator_vv h hb0 ha) hk)
      (isPGroup_qv_of_isMVtx h hx) bot_le (fun hle => hne (le_bot_iff.mp hle))
      (stab_eq_ltil_sup_qv h hfull hx)
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)
      hK'n (stab_le_normalizer_qv _ x) hLK
  have hK''V : V ≤ Subgroup.normalizer (K'' : Set _) := hVs.trans hK''n
  set Ut := vvPerp (X := puAmalgam h.le) x K'' with hUtdef
  have hUt : ∀ v, v ∈ Ut ↔ v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ K'' := fun v => mem_vvPerp_iff hK''V
  have hNU : centerOf V ≤ Ut := by
    intro v hv
    rw [hUt]
    refine ⟨hv.1, fun w hw => ?_⟩
    have : ⁅v, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hv.2 w hw).symm
    rw [this]; exact Subgroup.one_mem _
  have hUtV : Ut ≤ V := vvPerp_le x K''
  have hUtn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (Ut : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ stab (puAmalgam h.le) x, ∀ v ∈ Ut, y * v * y⁻¹ ∈ Ut := by
      intro y hy v hv
      rw [hUt] at hv ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn hy) v).mp hv.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hy)) w).mp hw
      have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hK''n hy) _).mp (hv.2 _ hw')
    intro v
    constructor
    · exact key g hg v
    · intro hv
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
      simpa [mul_assoc] using this
  obtain ⟨⟨ρ, hxρ, hAρ⟩, hAQ, hA2, hAc, C₀, -, hC₀V, hC₀A, hC₀i⟩ := hA
  have hAs : As ≤ stab (puAmalgam h.le) x := hAρ.trans (qv_le_stab_of_adj _ hxρ.symm)
  have hker := toSL3_eq_one_iff_mem_qv h hφ hx hψ
  have hVL := sd_group h14 hSQ hsq hF (X := stab (puAmalgam h.le) x) (V := V) (K' := K')
    (K'' := K'') (Ut := Ut) (Bh := ⊥) (A := As) (Lg := Ltil h.le L x) (C₀ := C₀ ⊔ Ut)
    (toSL3 ψ) (toSL3_surjective hψs) (pow_two_pow_eq_one_of_toSL3_eq_one h hφ hx hψ)
    hVn hK'V (h39x.trans inf_le_right) le_rfl hK''K' hK''n hidx hK'X hUt bot_le
    (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)
    (ltil_le_stab h x) (ltil_perfect h hx) (by rw [Subgroup.commutator_bot_left]; exact bot_le)
    hAs
    (fun a ha => by
      rw [← map_pow]
      exact (hker _).mpr (by simpa using hA2 a ha))
    (fun a b ha hb' => by
      have h1 : toSL3 ψ ⁅a, b⁆ = 1 := (hker _).mpr (by
        have := hAc a ha b hb'
        simpa [commutatorElement_def] using this)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1)
    (by
      obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
      exact ⟨⟨a, hAs haA⟩, haA, fun h1 => haQ ((hker _).mp h1)⟩)
    (by rw [bot_sup_eq]; exact le_sup_right) (sup_le hC₀V hUtV)
    (by
      rw [bot_sup_eq]
      exact S4A.commutator_sup_le_of (hC₀A.trans hNU)
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAs.trans hUtn))
        (hC₀V.trans (hVs.trans hUtn)) (hUtV.trans (hVs.trans hUtn)))
    (by
      have h1 : (C₀ ⊔ Ut).relIndex V ≤ C₀.relIndex V :=
        Subgroup.relIndex_le_of_le_left le_sup_left (by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      have h2 := card_natImage_eq_relIndex h hφ hx hψ hAs
      exact h1.trans (hC₀i.trans h2.ge))
  have hcrit := commutator_vv_le_of_ltil h hfull hb hx (K := K'') hK''n hVL
  have : K'' = K' := le_antisymm hK''K' hcrit
  rw [this, Subgroup.relIndex_self] at hidx
  omega

omit [Fintype F] hφ hC in
theorem not_centerOf_le_bloc_of_smul {α y : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hy : IsMVtx _ y) (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ¬ centerOf (Vv (puAmalgam h.le) y) ≤ Bloc h.le L y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hy
  rw [show Vv (puAmalgam h.le) (g • α) = Vi _ (g • α) 2 from rfl, vi_smul,
    PU.centerOf_map (MulAut.conj g).injective, bloc_smul h g α, map_conj_le_map_conj_iff]
  exact hN

omit hφ in
theorem commutator_vv_ne_bot (h43 : S43) (hmin : PUMin M T L) (hfull : IsSL3Full M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≠ ⊥ := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  intro hbot
  obtain ⟨x', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hx
  apply h43 _ M T L h hmin hb hfull x x' hc
  rw [geo_rev_two hb4 hc]
  have habel : Vv (puAmalgam h.le) x ≤ centerOf (Vv _ x) :=
    le_inf le_rfl ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot)
  exact habel.trans (centerOf_vv_le_qv h.hyp20 hC hb hx (isMVtx_geo_two' hb4 hc)
    (dist_geo_crit hb4 hc (by omega)))

theorem commutator_commutator_zm_eq_bot (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α)
    {ρ μ : Vtx (puAmalgam h.le)} (hαρ : (puAmalgam h.le).treeGraph.Adj α ρ)
    (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ) (hμα : μ ≠ α)
    (hnorm : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer ((ZM _ μ ⊔ centerOf (Vv _ α) : Subgroup _) : Set _)) :
    ⁅⁅ZM (puAmalgam h.le) μ, Vv _ α⁆, ZM _ α'⁆ = ⊥ := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set N := centerOf (Vv (puAmalgam h.le) α)
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hdαμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := dist_eq_two_of_adj_adj _ hαρ hρμ hμα.symm
  have hμM : IsMVtx (puAmalgam h.le) μ := by
    have h1 := (isMVtx_iff_of_adj _ hαρ).mp hc.1
    have h2 := isMVtx_iff_of_adj _ hρμ
    tauto
  have hZμV : ZM (puAmalgam h.le) μ ≤ Vv _ α := by
    have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
        Zv (puAmalgam h.le) x) μ (show _ ≤ 2 by omega) le_rfl
    rwa [zv_of_isMVtx _ hμM] at this
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hNn := stab_le_normalizer_centerOf_vv h α
  have hμγ : ¬ ZM (puAmalgam h.le) μ ≤ Qv _ γ := by
    intro hle
    apply hnorm
    have h1 : ⁅ZM (puAmalgam h.le) μ, ZM _ α'⁆ ≤ N :=
      (Subgroup.commutator_mono (le_inf hZμV hle) le_rfl).trans
        (commutator_vv_inf_qv_le_centerOf h hφ hC hb4 hc hNα)
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of (h1.trans le_sup_right) ?_ ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hNn)).trans
        le_sup_right |>.trans' (by rw [Subgroup.commutator_comm])
    · exact le_sup_left.trans Subgroup.le_normalizer
    · exact le_sup_right.trans Subgroup.le_normalizer
  have hdγμ : (puAmalgam h.le).treeGraph.dist γ μ = 4 := by
    have htri := dist_triangle (puAmalgam h.le) γ α μ
    rw [tdist_comm _ γ α, hdαγ, hdαμ] at htri
    by_contra hne
    exact hμγ (zm_le_qv_of_dist_le_three hb4 hμM (by rw [tdist_comm]; omega))
  have hcμ : IsCritical (puAmalgam h.le) μ γ :=
    ⟨hμM, by rw [tdist_comm, hdγμ, hb4], hμγ⟩
  have hcγ := ms22_iii _ h20 hb0 hC hcμ
  have hgeoρ : geo (puAmalgam h.le) μ γ 1 = ρ := by
    symm
    refine eq_geo_one _ hρμ.symm ?_
    have h1 := dist_triangle (puAmalgam h.le) ρ α γ
    have h2 := dist_triangle (puAmalgam h.le) μ ρ γ
    rw [tdist_comm _ ρ α, dist_eq_one_of_adj _ hαρ, hdαγ] at h1
    rw [dist_eq_one_of_adj _ hρμ.symm, tdist_comm _ μ γ, hdγμ] at h2
    rw [tdist_comm _ μ γ, hdγμ]
    omega
  have hNγ' := not_centerOf_le_bloc_of_smul h hc.1 hγ hNα
  have h4 := commutator_zm_qv_le_centerOf h hφ hC hb4 hcγ hNγ'
  rw [show geo (puAmalgam h.le) μ γ 1 = ρ from hgeoρ] at h4
  have h5 : ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ centerOf (Vv _ γ) :=
    (Subgroup.commutator_mono le_rfl ((vv_le_qv h hb hc.1).trans
      (qv_le_qv _ h20 hc.1 hαρ))).trans h4
  have hZα'V : ZM (puAmalgam h.le) α' ≤ Vv _ γ := by
    have hα' := hc.isMVtx_right _ h20
    have : Zv (puAmalgam h.le) α' ≤ Vv _ γ := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist γ x ≤ 2}) =>
        Zv (puAmalgam h.le) x) α' (show _ ≤ 2 by rw [dist_geo_crit_right hb4 hc (by omega)])
        le_rfl
    rwa [zv_of_isMVtx _ hα'] at this
  rw [← le_bot_iff]
  refine (Subgroup.commutator_mono h5 hZα'V).trans ?_
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact inf_le_right

theorem commutator_vv_le_dloc_of_not (hb4 : critDist (puAmalgam h.le) = 4)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ Dloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h20 hα
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  set N := centerOf (Vv (puAmalgam h.le) α) with hNdef
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hNn := stab_le_normalizer_centerOf_vv h α
  have hDn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZβ : ZM (puAmalgam h.le) α' ≤ Qv _ β := zm_le_qv_geo_one _ h20 hb0 hc
  have hZQ : ¬ ZM (puAmalgam h.le) α' ≤ Qv _ α := (ms22_iii _ h20 hb0 hC hc).2.2
  have hZV : ∀ μ, (puAmalgam h.le).treeGraph.Adj β μ → ZM (puAmalgam h.le) μ ≤ Vv _ α := by
    intro μ hβμ
    by_cases hμα : μ = α
    · rw [hμα]; exact zm_le_vv h hα
    · have hμM : IsMVtx (puAmalgam h.le) μ := by
        have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
        have h2 := isMVtx_iff_of_adj _ hβμ
        tauto
      have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
        {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
          Zv (puAmalgam h.le) x) μ
          (show _ ≤ 2 by rw [dist_eq_two_of_adj_adj _ hαβ hβμ (Ne.symm hμα)]) le_rfl
      rwa [zv_of_isMVtx _ hμM] at this
  by_contra hD
  obtain ⟨μ, hβμ, hμ⟩ : ∃ μ, (puAmalgam h.le).treeGraph.Adj β μ ∧
      ¬ ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ Dloc h.le L α := by
    by_contra hno
    apply hD
    have hall : ∀ ρ, (puAmalgam h.le).treeGraph.Adj α ρ → ∀ μ',
        (puAmalgam h.le).treeGraph.Adj ρ μ' → ⁅ZM (puAmalgam h.le) μ', Vv _ α⁆ ≤ Dloc h.le L α := by
      intro ρ hρ μ' hμ'
      obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαβ hρ
      have hμ0 : (puAmalgam h.le).treeGraph.Adj β (g⁻¹ • μ') := by
        have := (adj_smul _ g⁻¹ ρ μ').mpr hμ'
        rwa [← hgρ, inv_smul_smul] at this
      have h1 : ⁅ZM (puAmalgam h.le) (g⁻¹ • μ'), Vv _ α⁆ ≤ Dloc h.le L α := by
        by_contra h'
        exact hno ⟨_, hμ0, h'⟩
      have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
      rwa [Subgroup.map_commutator, ← zm_smul, smul_inv_smul,
        map_conj_eq_of_mem_normalizer (hVn hg), map_conj_eq_of_mem_normalizer (hDn hg)] at h2
    have hVD : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set _) :=
      hVs.trans hDn
    have hsub : Vv (puAmalgam h.le) α ≤ vvPerp (X := puAmalgam h.le) α (Dloc h.le L α) := by
      rw [vv_eq_iSup_vv hα]
      refine iSup₂_le fun ρ hρ => ?_
      have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
      rw [vv_eq_iSup_of_not_isMVtx hρH]
      refine iSup₂_le fun μ' hμ' => fun z hz => ?_
      rw [mem_vvPerp_iff hVD]
      have hμ'V : ZM (puAmalgam h.le) μ' ≤ Vv _ α := by
        rw [vv_eq_iSup_vv hα]
        exact (zm_le_vv_of_adj hμ' (by have := isMVtx_iff_of_adj _ hμ'; tauto)).trans
          (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
            Vv (puAmalgam h.le) ρ) ρ hρ le_rfl)
      exact ⟨hμ'V hz, fun w hw => hall ρ hρ μ' hμ' (Subgroup.commutator_mem_commutator hz hw)⟩
    rw [Subgroup.commutator_le]
    intro v hv w hw
    exact ((mem_vvPerp_iff hVD).mp (hsub hv)).2 w hw
  have hμα : μ ≠ α := by
    rintro rfl
    apply hμ
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le (vv_le_qv h hb hα)))]
    exact bot_le
  set X₁ := ZM (puAmalgam h.le) μ ⊔ N with hX₁
  set X₂ := ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ with hX₂
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβμs : Qv (puAmalgam h.le) β ≤ stab _ μ := qv_le_stab_of_adj _ hβμ
  have hTX₁ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (X₁ : Set _) :=
    (le_inf (hβμs.trans (stab_le_normalizer_zm _ μ)) (hβs.trans hNn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hTX₂ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (X₂ : Set _) := by
    refine le_normalizer_of_map_conj_le fun t ht => ?_
    rw [hX₂, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (hβμs.trans (stab_le_normalizer_zm _ μ) ht), map_conj_eq_of_mem_normalizer (hVn (hβs ht))]
  have hgen : stab (puAmalgam h.le) α =
      (⨆ g ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj g).toMonoidHom) ⊔
        Qv _ β := by
    have hcl : conjCl (stab (puAmalgam h.le) α) (ZM _ α') =
        ⨆ g ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj g).toMonoidHom := rfl
    rw [← hcl]
    apply le_antisymm
    · calc stab (puAmalgam h.le) α = Ltil h.le L α ⊔ Qv _ β :=
            stab_eq_ltil_sup_qv_adj h hfull hα hαβ
        _ ≤ conjCl (stab (puAmalgam h.le) α) (ZM _ α') ⊔ Qv _ β :=
            sup_le_sup_right (ltil_le_of_normal h hfull hα hαβ (conjCl_le_of_le hZs)
              (le_normalizer_conjCl _ _) (le_conjCl _ _) hZβ hZQ) _
    · exact sup_le (conjCl_le_of_le hZs) hβs
  have hX₁g : ∀ g ∈ stab (puAmalgam h.le) α,
      X₁.map (MulAut.conj g).toMonoidHom = ZM (puAmalgam h.le) (g • μ) ⊔ N := by
    intro g hg
    rw [hX₁, Subgroup.map_sup, ← zm_smul, map_conj_eq_of_mem_normalizer (hNn hg)]
  have hX₂g : ∀ g ∈ stab (puAmalgam h.le) α,
      X₂.map (MulAut.conj g).toMonoidHom = ⁅ZM (puAmalgam h.le) (g • μ), Vv _ α⁆ := by
    intro g hg
    rw [hX₂, Subgroup.map_commutator, ← zm_smul, map_conj_eq_of_mem_normalizer (hVn hg)]
  have hcore : ∀ g ∈ stab (puAmalgam h.le) α,
      ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer ((X₁.map (MulAut.conj g).toMonoidHom :
        Subgroup _) : Set _) → ⁅X₂.map (MulAut.conj g).toMonoidHom, ZM _ α'⁆ = ⊥ := by
    intro g hg hng
    rw [hX₁g g hg] at hng
    rw [hX₂g g hg]
    have hgβ : (puAmalgam h.le).treeGraph.Adj α (g • β) := by
      have := (adj_smul _ g α β).mpr hαβ
      rwa [(mem_stab _).mp hg] at this
    have hgμ : (puAmalgam h.le).treeGraph.Adj (g • β) (g • μ) := (adj_smul _ g β μ).mpr hβμ
    have hgμα : g • μ ≠ α := by
      intro he
      apply hμα
      have : g • μ = g • α := by rw [he, (mem_stab _).mp hg]
      exact smul_left_cancel g this
    exact commutator_commutator_zm_eq_bot h hφ hC hb4 hc hNα hgβ hgμ hgμα hng
  by_cases hX₁n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (X₁ : Set _)
  ·
    apply hμ
    suffices hcen : ZM (puAmalgam h.le) μ ≤ Subgroup.centralizer (Vv _ α : Set _) by
      rw [hX₂, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hcen]
      exact bot_le
    rw [vv_eq_iSup_vv hα]
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun ρ hρ => ?_
    rw [← Subgroup.le_centralizer_iff]
    obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαβ hρ
    have hgμ : (puAmalgam h.le).treeGraph.Adj ρ (g • μ) := by
      rw [← hgρ]; exact (adj_smul _ g β μ).mpr hβμ
    have hgμM : IsMVtx (puAmalgam h.le) (g • μ) := by
      have h1 := (isMVtx_iff_of_adj _ hρ).mp hα
      have h2 := isMVtx_iff_of_adj _ hgμ
      tauto
    have h1 : ZM (puAmalgam h.le) μ ≤ Vv _ ρ ⊔ N := by
      have h0 : ZM (puAmalgam h.le) μ ≤ X₁.map (MulAut.conj g).toMonoidHom := by
        rw [map_conj_eq_of_mem_normalizer (hX₁n hg)]; exact le_sup_left
      rw [hX₁g g hg] at h0
      exact h0.trans (sup_le_sup_right (zm_le_vv_of_adj hgμ hgμM) _)
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    have hVρab := vv_le_centralizer_of_not_isMVtx h20 hb hρH
    have hVρα : Vv (puAmalgam h.le) ρ ≤ Vv _ α := by
      rw [vv_eq_iSup_vv hα]
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
        Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
    refine h1.trans (sup_le ?_ ?_)
    · exact (Subgroup.le_centralizer_iff.mp hVρab)
    · exact inf_le_right.trans (Subgroup.centralizer_le hVρα)
  · by_cases hX₂n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (X₂ : Set _)
    · obtain ⟨g, hg, hng, -⟩ := ms21_vii _ hgen hTX₁ hX₁n hTX₁ hX₁n
      have hc0 := hcore g hg hng
      rw [map_conj_eq_of_mem_normalizer (hX₂n hg)] at hc0
      apply hμ
      have hL := commutator_ltil_le_of_commutator_le h hfull hα hαβ (A := X₂) (B := ⊥) hX₂n
        (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge) hc0.le hZβ hZQ
      have hX₂Q : X₂ ≤ Qv (puAmalgam h.le) α := by
        rw [hX₂, Subgroup.commutator_comm]
        exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (((hZV μ hβμ).trans hVs).trans hVn)).trans (vv_le_qv h hb hα)
      exact le_dloc_of_commutator_le h hα hX₂Q (hL.trans bot_le)
    · obtain ⟨g, hg, hng, hng₂⟩ := ms21_vii _ hgen hTX₁ hX₁n hTX₂ hX₂n
      apply hng₂
      exact le_normalizer_of_le_centralizer (by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hcore g hg hng)

omit hC in
theorem sqtkGroup_SL3 (hSQ : SQTKQuot) : SQTKGroup (SL3 F) :=
  hSQ ↥M (SL3 F) h.sqtk (toSL3 φ) (toSL3_surjective hφ.2.1) isQuasisimple_SL3

end CritGenPU

theorem i461_of (h32 : S32) (h39 : S39) (h43 : S43) (h14 : MS14AS) (hSQ : SQTKQuot) : I461 := by
  intro G _ _ M T L F _ _ φ c α hα
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hC := centHyp_of_S32 h32 h
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hsq := sqtkGroup_SL3 h hφ hSQ
  by_contra hN
  have hNall : ∀ y : Vtx (puAmalgam h.le), IsMVtx _ y →
      ¬ centerOf (Vv (puAmalgam h.le) y) ≤ Bloc h.le L y :=
    fun y hy => not_centerOf_le_bloc_of_smul h hα hy hN
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hα
  have hγ := isMVtx_geo_two' hb4 hc
  rcases exists_offender_centerOf h hφ hC h39 h43 hmin hb4 hc (hNall α hα) (hNall _ hγ) with
    ⟨A, hA⟩ | ⟨A, hA⟩
  · exact false_of_offender_centerOf h hφ h14 hSQ hsq h39 hb4 hα hA
      (commutator_vv_le_dloc_of_not h hφ hC hb4 hα (hNall α hα))
      (commutator_vv_ne_bot h hC h43 hmin hfull hb4 hα)
  · exact false_of_offender_centerOf h hφ h14 hSQ hsq h39 hb4 hγ hA
      (commutator_vv_le_dloc_of_not h hφ hC hb4 hγ (hNall _ hγ))
      (commutator_vv_ne_bot h hC h43 hmin hfull hb4 hγ)


end CFSG.Quasithin.MS93.S46
