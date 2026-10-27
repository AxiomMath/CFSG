module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem Zv_not_le_of_bad (hG : Glob H M S) (hp : PD δ δ') {α : Geo H M} (hα : α ∈ nbrs δ)
    (hbad : ¬ Zv α ≤ Qv δ') {γ : Geo H M} (hγ : γ ∈ nbrs α) (hγδ : γ ≠ δ) :
    ¬ Zv γ ≤ Qv δ' := by
  intro hle
  have hαv : vtype α = true := vtype_true_of_mem_nbrs_false hα hp.vδ
  have hδα : δ ∈ nbrs α := mem_nbrs_comm hα
  have hsup := (EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot hG.amalg
    hαv (hG.crit α hαv) hδα hγ hγδ.symm (hG.central δ hp.vδ)).1
  exact hbad (hsup ▸ sup_le (pd_Zv_le_Qv hG hp).1 hle)

theorem Vn_le_Qv_of_dist_succ_lt {x y : Geo H M} (h : dist x y + 1 < bMin H M) : Vn x ≤ Qv y :=
  iSup₂_le fun μ hμ => Zv_le_Qv_of_dist_lt_bMin
    (lt_of_le_of_lt (by
      have := dist_le_dist_nbr hμ y
      have e1 : dist μ y = dist y μ := CosetGeom.dist_comm _ _
      have e2 : dist y x = dist x y := CosetGeom.dist_comm _ _
      omega) h)

theorem Vn_commute {x y : Geo H M} (hA : F53Amalgam H M S) (h : dist x y + 2 < bMin H M) :
    ∀ a ∈ Vn x, ∀ b ∈ Vn y, a * b = b * a := by
  have key : ∀ μ ∈ nbrs x, ∀ μ' ∈ nbrs y, ∀ a ∈ Zv μ, ∀ b ∈ Zv μ', a * b = b * a := by
    intro μ hμ μ' hμ' a ha b hb
    have hd : dist μ μ' < bMin H M := by
      have h1 := dist_le_dist_nbr hμ μ'
      have h2 := dist_le_dist_nbr hμ' x
      have e1 : dist μ' x = dist x μ' := CosetGeom.dist_comm _ _
      have e2 : dist μ μ' = dist μ' μ := CosetGeom.dist_comm _ _
      omega
    have h3 : ⁅Zv μ, Zv μ'⁆ = ⊥ :=
      comm_Zv_eq_bot_of_le_Qv hA (Zv_le_Qv_of_dist_lt_bMin hd)
    have h4 := Subgroup.commutator_mem_commutator ha hb
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  intro a ha b hb
  have step1 : ∀ μ ∈ nbrs x, ∀ a ∈ Zv μ, ∀ b ∈ Vn y, a * b = b * a := by
    intro μ hμ a ha b hb
    have : Vn y ≤ Subgroup.centralizer ({a} : Set G) :=
      iSup₂_le fun μ' hμ' c hc => by
        simpa [Subgroup.mem_centralizer_iff, eq_comm] using key μ hμ μ' hμ' a ha c hc
    have := this hb
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at this
    exact this
  have : Vn x ≤ Subgroup.centralizer ({b} : Set G) :=
    iSup₂_le fun μ hμ c hc => by
      simpa [Subgroup.mem_centralizer_iff] using (step1 μ hμ c hc b hb).symm
  have := this ha
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at this
  exact this.symm

theorem mem_stab_of_comm (hG : Glob H M S) {ℓ ν : Geo H M} (hℓ : vtype ℓ = true)
    (hν : ν ∈ nbrs ℓ) {x : G} (hxℓ : x ∈ stab ℓ) (hx : ∀ z ∈ Zv ν, z * x = x * z) :
    x ∈ stab ν := by
  let g : ↥(H ⊔ M) := ⟨x, stab_le ℓ hxℓ⟩
  have hgν : g • ν ∈ nbrs ℓ := smul_mem_nbrs hxℓ hν
  have hZ : Zv (g • ν) = Zv ν := by
    rw [Zv_smul]
    exact conjSub_eq_self_of_comm hx
  by_cases heq : g • ν = ν
  · exact mem_stab_of_smul_eq heq
  · exfalso
    have hinf := (EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot hG.amalg
      hℓ (hG.crit ℓ hℓ) hν hgν (Ne.symm heq)
      (hG.central ν (vtype_false_of_mem_nbrs_true hν hℓ))).2
    rw [← hZ, inf_idem] at hinf
    exact Zv_ne_bot hG.amalg _ hinf

theorem geo115 (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    (hb5 : 5 ≤ bMin H M) {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ')
    {γ : Geo H M} (hγ : γ ∈ nbrs α) (hγδ : γ ≠ δ) :
    ∃ ε : Geo H M, ε ∈ nbrs δ' ∧ Vn γ ≤ Qv ε ∧ ¬ Vn γ ≤ Qv δ' := by
  have hA := hG.amalg
  have hαv : vtype α = true := vtype_true_of_mem_nbrs_false hα hp.vδ
  have hδα : δ ∈ nbrs α := mem_nbrs_comm hα
  have hγα : α ∈ nbrs γ := mem_nbrs_comm hγ
  have hγv : vtype γ = false := vtype_false_of_mem_nbrs_true hγ hαv
  have hdist : dist α δ' = bMin H M := by
    have h1 := dist_le_dist_nbr hα δ'
    have e1 : dist δ' α = dist α δ' := CosetGeom.dist_comm _ _
    have e2 : dist δ' δ = dist δ δ' := CosetGeom.dist_comm _ _
    have := hp.dist_eq
    by_contra hne
    exact hbad (Zv_le_Qv_of_dist_lt_bMin (by omega))
  have hc : IsCritData α δ δ' :=
    ⟨hδα, hG.crit α hαv, hdist, hp.dist_eq, hbad⟩
  let P := critPathOf hc
  have hodd := hG.odd
  set ε := P.p (bMin H M - 1) with hεdef
  set ε2 := P.p (bMin H M - 2) with hε2def
  have hεδ' : ε ∈ nbrs δ' := by
    have := P.isGeodesic.mem_nbrs_pred (i := bMin H M - 1) (by omega)
    rwa [show bMin H M - 1 + 1 = bMin H M by omega, P.p_b] at this
  have hε2ε : ε2 ∈ nbrs ε := by
    have := P.isGeodesic.mem_nbrs_pred (i := bMin H M - 2) (by omega)
    rwa [show bMin H M - 2 + 1 = bMin H M - 1 by omega] at this
  have hεv : vtype ε = true :=
    ((P.vtype_iff hA (j := bMin H M - 1) (by omega)).mpr (by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩)).trans hαv
  have hε2v : vtype ε2 = false := vtype_false_of_mem_nbrs_true hε2ε hεv
  have hd2 : dist ε2 δ' = 2 := by
    have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
    rwa [P.p_b, show bMin H M - (bMin H M - 2) = 2 by omega] at this
  have hdγε2 : dist γ ε2 ≤ bMin H M - 1 := by
    have h1 := dist_le_dist_nbr hγ ε2
    have h2 : dist α ε2 = bMin H M - 2 := P.dist_start (j := bMin H M - 2) (by omega)
    have e1 : dist γ ε2 = dist ε2 γ := CosetGeom.dist_comm _ _
    have e2 : dist ε2 α = dist α ε2 := CosetGeom.dist_comm _ _
    omega
  have hdγδ : dist γ δ ≤ 2 := by
    have h1 := dist_le_dist_nbr hγ δ
    have h2 : dist α δ = 1 := dist_eq_one_iff_adj.mpr hδα
    have e1 : dist γ δ = dist δ γ := CosetGeom.dist_comm _ _
    have e2 : dist δ α = dist α δ := CosetGeom.dist_comm _ _
    omega
  have hZδ' : Zv δ' ≤ Vn δ := (c3_comm_eq hG hirr h15 hng hp).1
  have hi : ∀ a ∈ Vn γ, ∀ z ∈ Zv δ', z * a = a * z := fun a ha z hz =>
    (Vn_commute hA (by omega) a ha z (hZδ' hz)).symm
  have hii : Vn γ ≤ Qv ε2 := by
    by_cases hlt : dist γ ε2 + 1 < bMin H M
    · exact Vn_le_Qv_of_dist_succ_lt hlt
    · by_contra hnot
      have hpd : PD γ ε2 := ⟨hγv, hε2v, by omega, hnot⟩
      have hZγ : Zv γ ≤ Vn ε2 := (c3_comm_eq hG hirr h15 hng hpd).2.1
      exact Zv_not_le_of_bad hG hp hα hbad hγ hγδ
        (hZγ.trans (Vn_le_Qv_of_dist_succ_lt (by omega)))
  refine ⟨ε, hεδ', fun x hx => ?_, fun hle => hbad
    ((Zv_le_Vn_of_mem_nbrs hγα).trans hle)⟩
  have hx2 : x ∈ stab ε2 := pCoreOf_le 2 _ (hii hx)
  have hxε : x ∈ stab ε := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_comm hε2ε) (hii hx)
  have hxδ' : x ∈ stab δ' := mem_stab_of_comm hG hεv (mem_nbrs_comm hεδ') hxε (hi x hx)
  refine mem_Qv_of_fixes_two_nbrs hA hεv hε2ε (mem_nbrs_comm hεδ') ?_ hxε hx2 hxδ'
  intro h
  rw [h, CosetGeom.dist_self] at hd2
  omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
