module

public import CFSG.Quasithin.MS93.S4A432T
public import CFSG.Quasithin.MS93.S4A432S
public import CFSG.Quasithin.MS93.S4A433

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Axis

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem usup_le_commutator_uloc_of_card {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hUZ : Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β)
    (hUq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2)
    {S : Subgroup (puAmalgam h.le).Universal} (hSβ : S ≤ Qv (puAmalgam h.le) β)
    (hS : Nat.card F < (Qv (puAmalgam h.le) α).relIndex S) :
    Usup (puAmalgam h.le) α β ≤ ⁅Uloc h.le L α, S⁆ := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hQs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hSs : S ≤ stab (puAmalgam h.le) α := hSβ.trans hQs
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hW : commN (natImage ψ (Qv (puAmalgam h.le) β)) ≤ fixN (natImage ψ (Qv _ β)) := by
    intro x hx
    obtain ⟨u, rfl⟩ := natVec_surjective hψ x
    have hu : (u : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L α, Qv (puAmalgam h.le) β⁆ :=
      (mem_commutator_iff_natVec hψ hQs u).mpr hx
    rw [← usup_eq_commutator_uloc h hfull hα hαβ] at hu
    have huC : (u : (puAmalgam h.le).Universal) ∈
        Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) :=
      ((zh_inf_uloc h hfull hα hαβ).le ⟨hUZ hu, u.2⟩).2
    exact (mem_centralizer_iff_natVec hψ hQs u).mp huC
  have hC2 : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h hfull hα hαβ, card_commutator_eq hψ hQs,
      Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  have hF2 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have h1 := Submodule.finrank_mono hW
    have h3 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) ≠ 3 := by
      intro h3
      have htop : fixN (natImage ψ (Qv (puAmalgam h.le) β)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
      have hbot : commN (natImage ψ (Qv (puAmalgam h.le) β)) = ⊥ := by
        rw [eq_bot_iff]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, hg, x, rfl⟩
        have : x ∈ fixN (natImage ψ (Qv (puAmalgam h.le) β)) := htop ▸ Submodule.mem_top
        rw [mem_fixN] at this
        rw [this g hg, sub_self]
        exact Submodule.zero_mem _
      rw [hbot, finrank_bot] at hC2
      omega
    have h4 := Submodule.finrank_le (fixN (natImage ψ (Qv (puAmalgam h.le) β)))
    rw [Module.finrank_fin_fun] at h4
    omega
  have hSA : natImage ψ S ≤ natImage ψ (Qv (puAmalgam h.le) β) := natImage_mono hSβ
  have hcardS := S46.card_natImage_eq_relIndex h hφ hα hψ hSs
  have hfixS : Module.finrank F (fixN (natImage ψ S)) = 2 := by
    have h2 := Submodule.finrank_mono (fixN_anti hSA)
    rw [hF2] at h2
    have h3 : Module.finrank F (fixN (natImage ψ S)) ≠ 3 := by
      intro h3
      have htop : fixN (natImage ψ S) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
      have hbot : natImage ψ S = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        exact eq_one_of_mulVec_eq_self fun v =>
          (htop ▸ Submodule.mem_top : v ∈ fixN (natImage ψ S)) g hg
      rw [hbot, Subgroup.card_bot] at hcardS
      omega
    have h4 := Submodule.finrank_le (fixN (natImage ψ S))
    rw [Module.finrank_fin_fun] at h4
    omega
  have hle := card_le_card_commN_of_finrank_fixN hfixS
  rw [hcardS] at hle
  have hcommS : commN (natImage ψ S) = commN (natImage ψ (Qv (puAmalgam h.le) β)) := by
    have hmono := commN_mono hSA
    refine Submodule.eq_of_le_of_finrank_eq hmono ?_
    rw [hC2]
    have h1 := Submodule.finrank_mono hmono
    rw [hC2] at h1
    by_contra hne
    have h2 : Module.finrank F (commN (natImage ψ S)) ≤ 1 := by omega
    have h3 : Nat.card ↥(commN (natImage ψ S)) ≤ Nat.card F := by
      rw [Module.natCard_eq_pow_finrank (K := F)]
      calc Nat.card F ^ Module.finrank F (commN (natImage ψ S)) ≤ Nat.card F ^ 1 :=
            Nat.pow_le_pow_right (by omega) h2
        _ = Nat.card F := pow_one _
    omega
  intro u hu
  have hUn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  rw [usup_eq_commutator_uloc h hfull hα hαβ] at hu
  have huU : u ∈ Uloc h.le L α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hUn) hu
  have h1 := (mem_commutator_iff_natVec hψ hQs ⟨u, huU⟩).mp hu
  rw [← hcommS] at h1
  exact (mem_commutator_iff_natVec hψ hSs ⟨u, huU⟩).mpr h1

end Axis

section Gen

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem vv_le_iSup_nablaSet_sup_bloc (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Vv (puAmalgam h.le) α ≤
      (⨆ δ ∈ nablaSet h.le L α, ZM (puAmalgam h.le) δ) ⊔ Bloc h.le L α := by
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 := hρ
  have hZB : ZM (puAmalgam h.le) α ≤ Bloc h.le L α := zm_le_bloc h hb hα
  rcases isMVtx_of_dist_le_two h hα hρ' with hρM | hadj
  · by_cases hρα : ρ = α
    · subst hρα
      rw [zv_of_isMVtx _ hα]
      exact hZB.trans le_sup_right
    · have hd : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by
        have hne : (puAmalgam h.le).treeGraph.dist α ρ ≠ 0 :=
          fun h0 => hρα ((dist_eq_zero_iff _).mp h0).symm
        have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) := by
          rw [even_dist_iff]
          tauto
        obtain ⟨k, hk⟩ := hev
        omega
      by_cases hn : ρ ∈ nablaSet h.le L α
      · rw [zv_of_isMVtx _ hρM]
        exact (le_iSup₂_of_le (f := fun δ (_ : δ ∈ nablaSet h.le L α) => ZM (puAmalgam h.le) δ)
          ρ hn le_rfl).trans le_sup_left
      · have : Zv (puAmalgam h.le) ρ ≤ Bloc h.le L α := by
          by_contra hcon
          exact hn ⟨hd, hcon⟩
        exact this.trans le_sup_right
  · have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
      rw [← isMVtx_iff_of_adj _ hadj]
      exact hα
    rw [zv_of_not_isMVtx _ hρH]
    exact ((zh_le_zm _ hadj).trans hZB).trans le_sup_right

theorem conjCl_le_iSup_nablaSet {α δ : Vtx (puAmalgam h.le)} (hδ : δ ∈ nablaSet h.le L α) :
    conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ) ≤
      ⨆ μ ∈ nablaSet h.le L α, ZM (puAmalgam h.le) μ := by
  refine iSup₂_le fun g hg => ?_
  rw [← zm_smul]
  have hgα : g • α = α := (mem_stab _).mp hg
  have hgδ : g • δ ∈ nablaSet h.le L α := by
    rw [← hgα]
    exact (mem_nablaSet_smul h g α δ).mpr hδ
  exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ nablaSet h.le L α) => ZM (puAmalgam h.le) μ)
    (g • δ) hgδ le_rfl

end Gen

section Facts

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le)) (h42 : S42) (h431A : S431A)
  (h431B : S431B)
include h hfull hH hC h42 h431A h431B

theorem commutator_vv_qv_le_zm_of_star {α₀ α₀' μ : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α₀ α₀') (hμ : IsMVtx _ μ) :
    ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) μ :=
  commutator_vv_qv_le_zm h hH.2.1 (fun _ _ hδ hδρ =>
    (concl433_edge h hfull h42 h431A h431B hH hC hs hδ hδρ).1) hμ

theorem linear_of_kindAt (h17 : MS17i) (hb : 4 < critDist (puAmalgam h.le))
    {α₀ α₀' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α₀ α₀')
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) (hk : KindAt h.le L F false μ)
    {ν ρ : Vtx (puAmalgam h.le)} (hμν : (puAmalgam h.le).treeGraph.Adj μ ν)
    (hνρ : (puAmalgam h.le).treeGraph.Adj ν ρ) {x : (puAmalgam h.le).Universal}
    (hxρ : x ∈ ZM (puAmalgam h.le) ρ) (hxV : x ∈ Vv (puAmalgam h.le) μ)
    (hxB : x ∉ Bloc h.le L μ) {y₀ : (puAmalgam h.le).Universal}
    (hy₀ : y₀ ∈ Qv (puAmalgam h.le) μ) (hxy₀ : ⁅x, y₀⁆ ∉ Dloc h.le L μ) :
    ∃ U' : Subgroup (puAmalgam h.le).Universal, x ∈ U' ∧ U' ≤ Vv (puAmalgam h.le) μ ∧
      Uloc h.le L μ ≤ U' ∧
      stab (puAmalgam h.le) μ ≤ Subgroup.normalizer (U' : Set (puAmalgam h.le).Universal) ∧
      ∀ y ∈ Qv (puAmalgam h.le) μ, (∀ u ∈ U', ⁅u, y⁆ ∈ Dloc h.le L μ) ∨
        (∀ u ∈ U', ⁅u, y⁆ ∈ Dloc h.le L μ → u ∈ Bloc h.le L μ) := by
  obtain ⟨ψ, hψs, hψ, hPK⟩ := hk
  exact linear_of_sameType h hfull h17 hH.2.1 hμ hH.2.2 (isC1_of_star h hH h431A hs hμ)
    (vv_comm_eq_bot h hb hμ) (commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hμ)
    hψs hψ hPK hμν hνρ hxρ hxV hxB hy₀ hxy₀

omit h42 h431B in
theorem not_critR0_le_bloc {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hk : KindAt h.le L F false α) : ¬ critR0 (puAmalgam h.le) α α' ≤ Bloc h.le L α := by
  intro hle
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  obtain ⟨ψ, -, hψ, hPK⟩ := hk
  obtain ⟨-, -, -, -, -, -, -, hPiB, -, -, -⟩ :=
    isC1_normal h hfull hH.2.1 hα (isC1_of_star h hH h431A hs hα)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  apply hc'.2.2
  intro c hc
  have hfix : ∀ v : Fin 3 → F,
      ((toSL3 ψ ⟨c, hZ's hc⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    obtain ⟨p, rfl⟩ := secVec_surjective hPK v
    have hsp : c * p * c⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (hPn (hZ's hc)) _).mp p.2
    rw [← secVec_conj hPK ⟨c, hZ's hc⟩ p ⟨_, hsp⟩ rfl]
    have hK : (⟨_, hsp⟩ * p⁻¹ : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α)) ∈ (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α).subgroupOf _ := by
      rw [Subgroup.mem_subgroupOf, ← hPiB]
      have e : ((⟨_, hsp⟩ * p⁻¹ : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) =
          ⁅(p : (puAmalgam h.le).Universal), c⁆⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      refine ⟨Subgroup.mul_mem _ hsp (Subgroup.inv_mem _ p.2), ?_⟩
      rw [e]
      exact Subgroup.inv_mem _ (hle (Subgroup.commutator_mem_commutator (hPV p.2) hc))
    have h0 := (secVec_eq_zero_iff hPK _).mpr (Subgroup.mem_subgroupOf.mp hK)
    rw [secVec_mul, secVec_inv, add_neg_eq_zero] at h0
    exact h0
  have h1 := eq_one_of_mulVec_eq_self hfix
  exact (S46.toSL3_eq_one_iff_mem_qv h hH.2.2 hα hψ ⟨c, hZ's hc⟩).mp h1

theorem critR0_le_of_normal {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    {U' : Subgroup (puAmalgam h.le).Universal}
    (hU'n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (U' : Set (puAmalgam h.le).Universal))
    (hU'V : U' ≤ Vv (puAmalgam h.le) α) (hUU' : Uloc h.le L α ≤ U')
    (hU'B : ¬ U' ≤ Bloc h.le L α) : critR0 (puAmalgam h.le) α α' ≤ U' := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb := hH.2.1
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hcα := isC1_of_star h hH h431A hs hα
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hUn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  have hZs : ZM (puAmalgam h.le) α ≤ stab _ α := (zm_le_vv h hα).trans hVs
  obtain ⟨-, -, -, hT⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hc'.1
    (adj_geo_one_of_isCritical _ hb0 hc')
  have hBle := bloc_le_of_star h hfull hC hH.2.2 hb hs hcα hT.le
  have hR : ⁅ZM (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ Uloc h.le L α := by
    rw [zm_eq_uloc_sup_zloc h hfull hα]
    refine S4A.commutator_sup_le_of ?_ ?_ ((uloc_le_zm h hfull hα).trans (hZs.trans hUn))
      ((zloc_le_zm h hfull hα).trans (hZs.trans hUn))
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hUn)
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        ((zloc_le_centralizer_stab h hfull hα).trans (Subgroup.centralizer_le hZ's))]
      exact bot_le
  have hBZ : ⁅Bloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ U' := by
    refine (Subgroup.commutator_mono hBle le_rfl).trans ?_
    refine S4A.commutator_sup_le_of ?_ (hR.trans hUU') ((inf_le_left.trans hVs).trans hU'n)
      (hZs.trans hU'n)
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_]
    · exact bot_le
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hc'.1 hz) v hv.2).symm
  have hV := (isC1_bloc h hfull hb hα hcα).2.2 U' hU'n hU'V hU'B
  rw [critR0, ← hV]
  exact S4A.commutator_sup_le_of
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hU'n)) hBZ
    (Subgroup.le_normalizer) ((bloc_le_vv h α).trans (hVs.trans hU'n))

theorem commutator_zm_le_dloc_of_centralizes (h17 : MS17i) (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hk : KindAt h.le L F false α) {δ : Vtx (puAmalgam h.le)} (hδ : δ ∈ nablaSet h.le L α)
    {Y : Subgroup (puAmalgam h.le).Universal} (hYQ : Y ≤ Qv (puAmalgam h.le) α)
    (hYR : ∀ y ∈ Y, ∀ r ∈ critR0 (puAmalgam h.le) α α', ⁅r, y⁆ = 1) :
    ⁅ZM (puAmalgam h.le) δ, Y⁆ ≤ Dloc h.le L α := by
  have hα := hs.1.1
  have hb2 := hH.2.1
  obtain ⟨hδM, hZδV⟩ := zm_le_vv_of_mem_nablaSet h hα hδ
  have hZδB : ¬ ZM (puAmalgam h.le) δ ≤ Bloc h.le L α := by
    have := hδ.2
    rwa [zv_of_isMVtx _ hδM] at this
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb2 hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hR0B := not_critR0_le_bloc h hfull hH hC h431A hs hk
  have hαν : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α δ 1) :=
    adj_geo_one _ (by rw [hδ.1]; omega)
  have hνδ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ 1) δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by rw [hδ.1]; omega)
    rwa [geo_of_le _ (show (puAmalgam h.le).treeGraph.dist α δ ≤ 1 + 1 by rw [hδ.1])] at this
  rw [Subgroup.commutator_le]
  intro z hz y hy
  refine commutator_mem_of_forall_not_mem (vv_comm_eq_bot h hb hα)
    (hVn (qv_le_stab _ α (hYQ hy))) hZδV hZδB
    (fun a ha haB => ?_) z hz
  by_cases hQ : ∀ y' ∈ Qv (puAmalgam h.le) α, ⁅a, y'⁆ ∈ Dloc h.le L α
  · exact hQ y (hYQ hy)
  · push Not at hQ
    obtain ⟨y₀, hy₀, hay₀⟩ := hQ
    obtain ⟨U', haU, hU'V, hUU', hU'n, hdich⟩ := linear_of_kindAt h hfull hH hC h42 h431A h431B
      h17 hb hs hα hk hαν hνδ ha (hZδV ha) haB hy₀ hay₀
    rcases hdich y (hYQ hy) with h1 | h1
    · exact h1 a haU
    · exfalso
      obtain ⟨r, hr, hrB⟩ := Set.not_subset.mp hR0B
      have hrU := critR0_le_of_normal h hfull hH hC h42 h431A h431B hs hU'n hU'V hUU'
        (fun hle => haB (hle haU)) hr
      exact hrB (h1 r hrU (by rw [hYR y hy r hr]; exact Subgroup.one_mem _))

theorem false_of_kindAt_far (h17 : MS17i) (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F false μ)
    (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
    (hfar : Fintype.card F <
      (Qv (puAmalgam h.le) α).relIndex (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))) :
    False := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 := hH.2.1
  have hα := hs.1.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hs.1.2.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  set γ' := geo (puAmalgam h.le) α' α 2 with hγ'def
  have hγ' : IsMVtx (puAmalgam h.le) γ' := isMVtx_geo_two _ h20 hb0 hc'
  have hγ'eq : γ' = geo (puAmalgam h.le) α α' (critDist (puAmalgam h.le) - 2) := by
    rw [hγ'def, ← geo_symm _ (show critDist (puAmalgam h.le) - 2 ≤
      (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
    congr 1
    omega
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set ε := geo (puAmalgam h.le) α α' 3 with hεdef
  have hγ : IsMVtx (puAmalgam h.le) γ := isMVtx_geo_two _ h20 hb0 hs.1
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hs.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo _ (i := 1) (by omega)
  have hγε : (puAmalgam h.le).treeGraph.Adj γ ε := adj_geo _ (i := 2) (by omega)
  have hdγ'β : (puAmalgam h.le).treeGraph.dist γ' β = critDist (puAmalgam h.le) - 3 := by
    rw [hγ'eq, tdist_comm, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdγ'γ : (puAmalgam h.le).treeGraph.dist γ' γ = critDist (puAmalgam h.le) - 4 := by
    rw [hγ'eq, tdist_comm, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdγ'ε : (puAmalgam h.le).treeGraph.dist γ' ε = critDist (puAmalgam h.le) - 5 := by
    rw [hγ'eq, tdist_comm, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α = 2 := by
    rw [tdist_comm, hγdef, dist_geo _ (by omega)]
  have hVβ : Vv (puAmalgam h.le) γ' ≤ Qv _ β := vv_le_qv_of_dist h hγ' (by omega)
  have hVγ : Vv (puAmalgam h.le) γ' ≤ Qv _ γ := vv_le_qv_of_dist h hγ' (by omega)
  obtain ⟨hUZ, hUq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hα hαβ
  rw [← Nat.card_eq_fintype_card] at hUq hfar
  have hU := usup_le_commutator_uloc_of_card h hfull hα hαβ hH.2.2 hUZ hUq hVβ hfar
  have hαnab : α ∈ nablaSet h.le L γ := mem_nablaSet_geo_two h hfull hC hb2 hs.1
  have hZαV : ZM (puAmalgam h.le) α ≤ Vv _ γ := by
    rw [← zv_of_isMVtx _ hα]
    exact zv_le_vv h hdγα.le
  have hZαB : ¬ ZM (puAmalgam h.le) α ≤ Bloc h.le L γ := by
    have := hαnab.2
    rwa [zv_of_isMVtx _ hα] at this
  have hBn : stab (puAmalgam h.le) γ ≤
      Subgroup.normalizer (Bloc h.le L γ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) γ
  obtain ⟨g, hgγ, hgβ⟩ := exists_smul_edge_of_isMVtx _ hγ hβγ.symm hγ hγε
  have hg : g ∈ stab (puAmalgam h.le) γ := (mem_stab _).mpr hgγ
  have hεgα : (puAmalgam h.le).treeGraph.Adj ε (g • α) := by
    rw [← hgβ]
    exact (adj_smul _ g β α).mpr hαβ.symm
  have hgαM : IsMVtx (puAmalgam h.le) (g • α) := (isMVtx_smul _ g α).mpr hα
  have hVgα : Vv (puAmalgam h.le) γ' ≤ Qv _ (g • α) := by
    refine vv_le_qv_of_dist h hγ' ?_
    have := dist_triangle (puAmalgam h.le) γ' ε (g • α)
    rw [hdγ'ε, dist_eq_one_of_adj _ hεgα] at this
    omega
  have hZD : ⁅ZM (puAmalgam h.le) α, Vv (puAmalgam h.le) γ'⁆ ≤ Dloc h.le L γ := by
    rw [Subgroup.commutator_le]
    intro z hz y hy
    have hyQ : y ∈ Qv (puAmalgam h.le) γ := hVγ hy
    refine commutator_mem_of_forall_not_mem (vv_comm_eq_bot h hb hγ)
      (stab_le_normalizer_vv h γ (qv_le_stab _ γ hyQ)) hZαV hZαB (fun a ha haB => ?_) z hz
    by_cases hQ : ∀ y' ∈ Qv (puAmalgam h.le) γ, ⁅a, y'⁆ ∈ Dloc h.le L γ
    · exact hQ y hyQ
    · push Not at hQ
      obtain ⟨y₀, hy₀, hay₀⟩ := hQ
      obtain ⟨U', haU, -, -, hU'n, hdich⟩ := linear_of_kindAt h hfull hH hC h42 h431A h431B
        h17 hb hs hγ (hk γ hγ) hβγ.symm hαβ.symm ha (hZαV ha) haB hy₀ hay₀
      rcases hdich y hyQ with h1 | h1
      · exact h1 a haU
      · exfalso
        have hu0U : g * a * g⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp (hU'n hg) a).mp haU
        have hu0B : g * a * g⁻¹ ∉ Bloc h.le L γ := by
          intro hmem
          apply haB
          have := (Subgroup.mem_normalizer_iff.mp (hBn (Subgroup.inv_mem _ hg)) _).mp hmem
          simpa [mul_assoc] using this
        have hu0Z : g * a * g⁻¹ ∈ ZM (puAmalgam h.le) (g • α) := by
          rw [zm_smul]
          exact ⟨a, ha, rfl⟩
        have hcomm : ⁅g * a * g⁻¹, y⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hgαM hu0Z) y
            (hVgα hy)).symm
        exact hu0B (h1 _ hu0U (by rw [hcomm]; exact Subgroup.one_mem _))
  apply not_commutator_zm_qv_le_dloc_of_star h hH hfull h431A hs hCH hγ hαnab
  have hQ : ⁅ZM (puAmalgam h.le) α, Qv (puAmalgam h.le) γ⁆ ≤ Usup (puAmalgam h.le) α β := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hγ hβγ.symm)
  exact hQ.trans (hU.trans ((Subgroup.commutator_mono (uloc_le_zm h hfull hα) le_rfl).trans hZD))

theorem false_of_kindAt_near (h17 : MS17i) (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F false μ)
    (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
    (hnear : (Qv (puAmalgam h.le) α).relIndex
      (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) ≤ Fintype.card F) :
    False := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 := hH.2.1
  have hα := hs.1.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hs.1.2.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  set γ' := geo (puAmalgam h.le) α' α 2 with hγ'def
  set ν' := geo (puAmalgam h.le) α' α 1 with hν'def
  have hγ' : IsMVtx (puAmalgam h.le) γ' := isMVtx_geo_two _ h20 hb0 hc'
  have hα'ν' : (puAmalgam h.le).treeGraph.Adj α' ν' := adj_geo_one_of_isCritical _ hb0 hc'
  have hν'γ' : (puAmalgam h.le).treeGraph.Adj ν' γ' := adj_geo _ (i := 1) (by omega)
  have hν'eq : geo (puAmalgam h.le) γ' α' 1 = ν' := by
    symm
    refine eq_geo_one _ hν'γ'.symm ?_
    rw [tdist_comm _ ν' α', hν'def, dist_geo _ (by omega), tdist_comm, hγ'def,
      dist_geo _ (by omega)]
  have hα'nab : α' ∈ nablaSet h.le L γ' := mem_nablaSet_geo_two h hfull hC hb2 hc'
  have hcα := isC1_of_star h hH h431A hs hα
  have hVα : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb2 hα).trans (qv_le_stab _ α)
  have hVγ's : Vv (puAmalgam h.le) α ≤ stab _ γ' := hs.2.trans (qv_le_stab _ γ')
  have hDn : stab (puAmalgam h.le) γ' ≤
      Subgroup.normalizer (Dloc h.le L γ' : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ'
  have hZ'V : ZM (puAmalgam h.le) α' ≤ Vv _ γ' := by
    rw [← zv_of_isMVtx _ hc'.1]
    exact zv_le_vv h (by rw [tdist_comm, hγ'def, dist_geo _ (by omega)])
  have hR0 : critR0 (puAmalgam h.le) α α' = ⁅ZM (puAmalgam h.le) α', Qv (puAmalgam h.le) γ'⁆ := by
    rw [(h431A G M T L h F inferInstance inferInstance φ hH α α' hs).1,
      commutator_zm_qv_eq_of_star h hH h431B hs hγ' hα'nab, hν'eq]
  have hR0D : ¬ critR0 (puAmalgam h.le) α α' ≤ Dloc h.le L γ' := by
    rw [hR0]
    exact not_commutator_zm_qv_le_dloc_of_star h hH hfull h431A hs hCH hγ' hα'nab
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ ∈ nablaSet h.le L α,
      ¬ ⁅ZM (puAmalgam h.le) δ, ZM (puAmalgam h.le) α'⁆ ≤ Dloc h.le L γ' := by
    by_contra hall
    push Not at hall
    apply hR0D
    set N := ⨆ μ ∈ nablaSet h.le L α, ZM (puAmalgam h.le) μ with hNdef
    have hNV : N ≤ Vv (puAmalgam h.le) α :=
      iSup₂_le fun μ hμ => (zm_le_vv_of_mem_nablaSet h hα hμ).2
    have hNZ : ⁅N, ZM (puAmalgam h.le) α'⁆ ≤ Dloc h.le L γ' := by
      have heq : N = ⨆ μ : {μ // μ ∈ nablaSet h.le L α}, ZM (puAmalgam h.le) (μ : Vtx _) := by
        rw [hNdef, iSup_subtype']
      rw [heq]
      refine commutator_iSup_le_of (fun μ => hall μ μ.2) ?_
      rw [← heq]
      exact (hNV.trans hVγ's).trans hDn
    obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ ∈ nablaSet h.le L α := by
      by_contra hne
      push Not at hne
      apply (isC1_bloc h hfull hb2 hα hcα).2.1
      refine le_antisymm (bloc_le_vv h α) ((vv_le_iSup_nablaSet_sup_bloc h hb2 hα).trans ?_)
      refine sup_le (iSup₂_le fun μ hμ => absurd hμ (hne μ)) le_rfl
    have hZN : ZM (puAmalgam h.le) α ≤ N :=
      (zm_le_conjCl_zm h hδ₀.1).trans (conjCl_le_iSup_nablaSet h hδ₀)
    obtain ⟨-, -, -, hT⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hc'.1 hα'ν'
    have hBle := bloc_le_of_star h hfull hC hH.2.2 hb2 hs hcα hT.le
    have hBZ : ⁅Bloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Dloc h.le L γ' := by
      refine (Subgroup.commutator_mono hBle le_rfl).trans ?_
      refine S4A.commutator_sup_le_of ?_ ((Subgroup.commutator_mono hZN le_rfl).trans hNZ)
        ((inf_le_left.trans hVγ's).trans hDn) (((zm_le_vv h hα).trans hVγ's).trans hDn)
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_]
      · exact bot_le
      · intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hc'.1 hz) v hv.2).symm
    rw [critR0]
    refine (Subgroup.commutator_mono (vv_le_iSup_nablaSet_sup_bloc h hb2 hα) le_rfl).trans ?_
    exact S4A.commutator_sup_le_of hNZ hBZ ((hNV.trans hVγ's).trans hDn)
      ((bloc_le_vv h α).trans (hVγ's.trans hDn))
  obtain ⟨hδM, hZδV⟩ := zm_le_vv_of_mem_nablaSet h hα hδ
  obtain ⟨z, hz, c, hc, hzc⟩ : ∃ z ∈ ZM (puAmalgam h.le) δ, ∃ c ∈ ZM (puAmalgam h.le) α',
      ⁅z, c⁆ ∉ Dloc h.le L γ' := by
    by_contra hall
    push Not at hall
    exact hδD ((Subgroup.commutator_le).mpr hall)
  have hzQ : z ∈ Qv (puAmalgam h.le) γ' := hs.2 (hZδV hz)
  have hcz : ⁅c, z⁆ ∉ Dloc h.le L γ' := by
    intro hmem
    apply hzc
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hmem
  have hZ'B : ¬ ZM (puAmalgam h.le) α' ≤ Bloc h.le L γ' := by
    have := hα'nab.2
    rwa [zv_of_isMVtx _ hc'.1] at this
  have hVγ'ab := vv_comm_eq_bot h hb hγ'
  obtain ⟨x', hx', hx'B, hx'z⟩ := exists_not_mem_commutator_not_mem hVγ'ab
    (stab_le_normalizer_vv h γ' (qv_le_stab _ γ' hzQ)) hZ'V hZ'B hc hcz
  obtain ⟨U', hx'U, hU'V, -, hU'n, hdich⟩ := linear_of_kindAt h hfull hH hC h42 h431A h431B h17
    hb hs hγ' (hk γ' hγ') hν'γ'.symm hα'ν'.symm hx' (hZ'V hx') hx'B hzQ hx'z
  have hker : ∀ u ∈ U', ⁅u, z⁆ ∈ Dloc h.le L γ' → u ∈ Bloc h.le L γ' := by
    rcases hdich z hzQ with h1 | h1
    · exact absurd (h1 x' hx'U) hx'z
    · exact h1
  have hfin : Finite ↥(stab (puAmalgam h.le) α) := finite_stab h hα
  have hfinγ' : Finite ↥(stab (puAmalgam h.le) γ') := finite_stab h hγ'
  have hVγ'st : Vv (puAmalgam h.le) γ' ≤ stab _ γ' := (vv_le_qv h hb2 hγ').trans (qv_le_stab _ γ')
  have hfinV : Finite ↥(Vv (puAmalgam h.le) γ') :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVγ'st)
  have hfinU' : Finite ↥U' := Finite.of_injective _ (Subgroup.inclusion_injective hU'V)
  have hzn : z ∈ Subgroup.normalizer (Vv (puAmalgam h.le) γ' : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_vv h γ' (qv_le_stab _ γ' hzQ)
  have hcommV : ∀ a ∈ Vv (puAmalgam h.le) γ', ∀ b ∈ Vv (puAmalgam h.le) γ', a * b = b * a := by
    intro a ha b hb'
    have := Subgroup.commutator_mem_commutator ha hb'
    rw [hVγ'ab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  let f : ↥(U' ⊓ Qv (puAmalgam h.le) α) →* (puAmalgam h.le).Universal :=
    { toFun := fun u => ⁅(u : (puAmalgam h.le).Universal), z⁆
      map_one' := by simp
      map_mul' := fun u v => by
        have hu : (u : (puAmalgam h.le).Universal) ∈ Vv (puAmalgam h.le) γ' := hU'V u.2.1
        have hv : (v : (puAmalgam h.le).Universal) ∈ Vv (puAmalgam h.le) γ' := hU'V v.2.1
        have hcu := commutatorElement_mem_of_normalizer hu hzn
        have hcv := commutatorElement_mem_of_normalizer hv hzn
        simp only [Subgroup.coe_mul]
        rw [commutatorElement_mul_left_of_comm (hcommV _ hu _ hcv)]
        exact hcommV _ hcv _ hcu }
  have hfu : ∀ u, f u = ⁅((u : ↥(U' ⊓ Qv (puAmalgam h.le) α)) : (puAmalgam h.le).Universal), z⁆ :=
    fun _ => rfl
  set Y := Vv (puAmalgam h.le) γ' ⊓ Qv (puAmalgam h.le) α with hYdef
  have hrange : f.range ≤ ⁅ZM (puAmalgam h.le) δ, Y⁆ := by
    rintro _ ⟨u, rfl⟩
    rw [hfu, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hz ⟨hU'V u.2.1, u.2.2⟩)
  have hkerB : f.ker ≤ (Bloc h.le L γ').subgroupOf (U' ⊓ Qv (puAmalgam h.le) α) := by
    intro u hu
    rw [MonoidHom.mem_ker, hfu] at hu
    rw [Subgroup.mem_subgroupOf]
    exact hker _ u.2.1 (by rw [hu]; exact Subgroup.one_mem _)
  have hfinA : Finite ↥(U' ⊓ Qv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans hU'V))
  have hidx : (Bloc h.le L γ').relIndex (U' ⊓ Qv (puAmalgam h.le) α) ≤ Nat.card f.range := by
    rw [← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hkerB)
  have hcγ' := isC1_of_star h hH h431A hs hγ'
  have hU'B : U' ⊔ Bloc h.le L γ' = Vv (puAmalgam h.le) γ' :=
    (isC1_bloc h hfull hb2 hγ' hcγ').2.2 U' hU'n hU'V (fun hle => hx'B (hle hx'U))
  have hBn' : stab (puAmalgam h.le) γ' ≤
      Subgroup.normalizer (Bloc h.le L γ' : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) γ'
  have hU'B3 : (Bloc h.le L γ').relIndex U' = Fintype.card F ^ 3 := by
    rw [← relIndex_sup_of_le_normalizer ((hU'V.trans hVγ'st).trans hBn'), hU'B,
      relIndex_bloc_vv h hfull hb2 hγ' hcγ']
  have hU'Q : (Qv (puAmalgam h.le) α).relIndex U' ≤ Fintype.card F :=
    (Subgroup.relIndex_le_of_le_right hU'V
      (show ((Qv (puAmalgam h.le) α).subgroupOf (Vv (puAmalgam h.le) γ')).index ≠ 0 from
        Subgroup.index_ne_zero_of_finite)).trans hnear
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hsq : Fintype.card F ^ 2 ≤ (Bloc h.le L γ').relIndex (U' ⊓ Qv (puAmalgam h.le) α) := by
    have h1 := Subgroup.relIndex_inf_mul_relIndex (Bloc h.le L γ') (Qv (puAmalgam h.le) α) U'
    have h2 : (Bloc h.le L γ').relIndex U' ≤
        (Bloc h.le L γ' ⊓ Qv (puAmalgam h.le) α).relIndex U' :=
      Subgroup.relIndex_le_of_le_left inf_le_left
        (show ((Bloc h.le L γ' ⊓ Qv (puAmalgam h.le) α).subgroupOf U').index ≠ 0 from
          Subgroup.index_ne_zero_of_finite)
    rw [inf_comm (Qv (puAmalgam h.le) α) U'] at h1
    have h3 : Fintype.card F ^ 2 * Fintype.card F ≤
        (Bloc h.le L γ').relIndex (U' ⊓ Qv (puAmalgam h.le) α) * Fintype.card F := by
      calc Fintype.card F ^ 2 * Fintype.card F = Fintype.card F ^ 3 := by ring
        _ = (Bloc h.le L γ').relIndex U' := hU'B3.symm
        _ ≤ _ := h2
        _ = _ := h1.symm
        _ ≤ _ := Nat.mul_le_mul_left _ hU'Q
    exact Nat.le_of_mul_le_mul_right h3 hq
  have hYs : ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ ≤ stab _ α :=
    (Subgroup.commutator_mono (hZδV.trans hVα) (qv_le_stab _ α)).trans
      (Subgroup.commutator_le_self _)
  have hfinC : Finite ↥⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hYs)
  have hανδ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ 1) δ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by rw [hδ.1]; omega)
    rwa [geo_of_le _ (show (puAmalgam h.le).treeGraph.dist α δ ≤ 1 + 1 by rw [hδ.1])] at this
  have hcardQ : Nat.card ↥⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ =
      Fintype.card F ^ 2 := by
    rw [commutator_zm_qv_eq_of_star h hH h431B hs hα hδ,
      card_usup_of_star h hC hH.2.2 hb2 hs hδM hανδ.symm, Nat.card_eq_fintype_card]
  have hYle : ⁅ZM (puAmalgam h.le) δ, Y⁆ ≤ ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ :=
    Subgroup.commutator_mono le_rfl inf_le_right
  have hfinY : Finite ↥⁅ZM (puAmalgam h.le) δ, Y⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hYle)
  have heq : ⁅ZM (puAmalgam h.le) δ, Y⁆ = ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ :=
    Subgroup.eq_of_le_of_card_ge hYle (by
      rw [hcardQ]
      exact hsq.trans (hidx.trans (Subgroup.card_le_of_le hrange)))
  have hR0Z : critR0 (puAmalgam h.le) α α' ≤ Vv (puAmalgam h.le) γ' := by
    rw [(h431A G M T L h F inferInstance inferInstance φ hH α α' hs).1]
    have hν'H : ¬ IsMVtx (puAmalgam h.le) ν' := by
      rw [← isMVtx_iff_of_adj _ hα'ν']
      exact hc'.1
    refine (concl433_edge h hfull h42 h431A h431B hH hC hs hc'.1 hα'ν').1.trans ?_
    rw [← zv_of_not_isMVtx _ hν'H]
    exact zv_le_vv h (by rw [dist_eq_one_of_adj _ hν'γ'.symm]; omega)
  have hYD := commutator_zm_le_dloc_of_centralizes h hfull hH hC h42 h431A h431B h17 hb hs
    (hk α hα) hδ (Y := Y) inf_le_right (fun y hy r hr => by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcommV _ (hR0Z hr) _ hy.1)
  exact not_commutator_zm_qv_le_dloc_of_star h hH hfull h431A hs hCH hα hδ (heq ▸ hYD)

theorem false_of_kindAt_false (h17 : MS17i) (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F false μ)
    (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ) : False := by
  by_cases hnear : (Qv (puAmalgam h.le) α).relIndex
      (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) ≤ Fintype.card F
  · exact false_of_kindAt_near h hfull hH hC h42 h431A h431B h17 hb hs hk hCH hnear
  · exact false_of_kindAt_far h hfull hH hC h42 h431A h431B h17 hb hs hk hCH (not_le.mp hnear)

end Facts

end CFSG.Quasithin.MS93.S4A
