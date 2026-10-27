module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Geo
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3b
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Index

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

omit [Finite G] in
theorem cii_vtype_true {δ μ : Geo H M} (h : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    vtype μ = true := by
  have h' := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hμ)
  rw [h] at h'
  cases hv : vtype μ
  · exact absurd hv.symm h'
  · rfl

omit [Finite G] in
theorem cii_vtype_false {δ μ : Geo H M} (h : vtype δ = true) (hμ : μ ∈ nbrs δ) :
    vtype μ = false := by
  have h' := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hμ)
  rw [h] at h'
  cases hv : vtype μ
  · rfl
  · exact absurd hv.symm h'

omit [Finite G] in
theorem cii_nbrs_symm {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) : δ ∈ nbrs μ :=
  (show (graph (H ⊔ M) H M).Adj δ μ from hμ).symm

theorem cii_relIndex_Qv_le (hG : Glob H M S) {δ ν : Geo H M} (hν : ν ∈ nbrs δ)
    (hνs : vtype ν = true) {K : Subgroup G} (hK : K ≤ stab δ) {n : ℕ}
    (h4 : (K ⊓ Qv δ).relIndex K ≤ n) : (K ⊓ Qv ν).relIndex K ≤ 2 * n := by
  have hA := hG.amalg
  have hQ2 : (Qv ν).relIndex (stab δ ⊓ stab ν) = 2 :=
    EmptyFaithful.Stellmacher.OrdinaryProofs.relIndex_Qv_inf hA hν hνs
  have hle1 : K ⊓ Qv δ ≤ K ⊓ stab ν :=
    inf_le_inf_left _ (Qv_le_stab_of_mem_nbrs hA hν)
  have h5 : (K ⊓ stab ν).relIndex K ≤ n :=
    (Subgroup.relIndex_le_of_le_left hle1 Subgroup.index_ne_zero_of_finite).trans h4
  have hle2 : K ⊓ Qv ν ≤ K ⊓ stab ν := inf_le_inf_left _ (pCoreOf_le 2 _)
  have hmul := Subgroup.relIndex_mul_relIndex (K ⊓ Qv ν) (K ⊓ stab ν) K hle2 inf_le_left
  have h6 : (K ⊓ Qv ν).relIndex (K ⊓ stab ν) ≤ 2 := by
    have e : K ⊓ Qv ν = Qv ν ⊓ (K ⊓ stab ν) := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hk, hq⟩
        exact ⟨hq, hk, pCoreOf_le 2 (stab ν) hq⟩
      · rintro ⟨hq, hk, -⟩
        exact ⟨hk, hq⟩
    rw [e, Subgroup.inf_relIndex_right, ← hQ2]
    exact Subgroup.relIndex_le_of_le_right (inf_le_inf_right _ hK)
      Subgroup.index_ne_zero_of_finite
  rw [← hmul]
  exact Nat.mul_le_mul h6 h5

theorem cii_a (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ')
    {γ : Geo H M} (hγ : γ ∈ nbrs α) {ε : Geo H M} (hε : ε ∈ nbrs δ')
    (hVε : Vn γ ≤ Qv ε) (hW : ¬ Vn γ ≤ Vn δ ⊔ Qv δ') :
    (Vn γ ⊓ Qv δ').relIndex (Vn γ) = 4 ∧
      16 ≤ (fixSecIn (Vn γ) (Cb δ') (Vn δ')).relIndex (Vn δ') := by
  have hA := hG.amalg
  have hp' : PD δ' δ := hp.symm' (case3_data hG hirr h15 hng hp).2.1
  have hZαA : Zv α ≤ Vn δ := Zv_le_Vn_nbr hα
  have hZαA' : Zv α ≤ Vn γ := Zv_le_Vn_nbr (cii_nbrs_symm hγ)
  have hKX : Vn γ ≤ stab δ' ⊓ stab ε := by
    have := Qv_le_inf hA (cii_nbrs_symm hε)
    rw [inf_comm] at this
    exact hVε.trans this
  have hKe : IsElemAbelian 2 (Vn γ) := isElemAbelian_Vn' hG γ
  have h4 : (Vn γ ⊓ Qv δ').relIndex (Vn γ) = 4 := by
    have h2 : IsPGroup 2 (Zv α) := fun x =>
      ⟨1, Subtype.ext (by
        have := (isElemAbelian_Vn' hG δ).2 x.1 (hZαA x.2)
        simpa using this)⟩
    have hE4 : ((Zv α ⊔ Vn γ) ⊓ Qv δ').relIndex (Zv α ⊔ Vn γ) ≤ 4 := by
      rw [sup_eq_right.mpr hZαA']
      exact klein_le_four (quot_stab_five hA hp.vδ') (hKX.trans inf_le_left) hKe
    have := relIndex_two_four_of_not_le (X := stab δ') (Q := Qv δ') (A := Zv α) (C := Vn γ)
      (le_normalizer_pCoreOf 2 _) (hZαA.trans (pd_Vn_le_stab hG hp).1)
      (hKX.trans inf_le_left) h2 hE4 hbad (fun h => hbad ((le_inf le_rfl hZαA').trans h))
      (fun h => hW (h.trans (sup_le_sup_right hZαA _)))
    exact this.2.1
  refine ⟨h4, ?_⟩
  refine c3_index_That hG hirr h15 hng hp' hε hKX hKe h4 ?_
  obtain ⟨x, hxZ, hxQ⟩ := Set.not_subset.mp hbad
  refine ⟨x, hZαA' hxZ, fun hx => ?_⟩
  have hxs : x ∈ stab δ' := (pd_Vn_le_stab hG hp).1 (hZαA hxZ)
  have hsq : x ^ 2 ∈ pCoreOf 2 (stab δ') := by
    rw [(isElemAbelian_Vn' hG δ).2 x (hZαA hxZ)]
    exact one_mem _
  have h1 := NG.rk_gt hG hirr hng hp.vδ' hxs ⟨hx, hxQ, Or.inl hsq⟩
  have h2 := (c3_rk_le_four hG hirr h15 hng hp).2 x (hZαA hxZ)
  omega

theorem cii_bc (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ')
    {γ : Geo H M} (hγ : γ ∈ nbrs α) (hγδ : γ ≠ δ)
    (hKX : Vn γ ≤ stab δ')
    (h16 : 16 ≤ (fixSecIn (Vn γ) (Cb δ') (Vn δ')).relIndex (Vn δ')) :
    ∃ f ∈ Vn δ' ⊓ Qv α, OverIn (stab γ) f := by
  have hA := hG.amalg
  have hvα : vtype α = true := cii_vtype_true hp.vδ hα
  have hvγ : vtype γ = false := cii_vtype_false hvα hγ
  have hBs : Vn δ' ≤ stab δ := (pd_Vn_le_stab hG hp).2
  have hBe : IsElemAbelian 2 (Vn δ') := isElemAbelian_Vn' hG δ'
  have hb : Vn δ' ⊓ Qv γ ≤ fixSecIn (Vn γ) (Cb δ') (Vn δ') := by
    intro y hy
    refine Subgroup.subset_closure ⟨hy.1, fun t ht => ?_⟩
    rcases aon_Vn hG hvγ hy.2 with h0 | h1
    · have hm := Subgroup.commutator_mem_commutator ht (Subgroup.mem_zpowers y)
      rw [h0] at hm
      have : t * y * t⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp hm
      rw [this]
      exact (Cb δ').one_mem
    · exfalso
      refine Zv_not_le_of_bad hG hp hα hbad hγ hγδ ?_
      rw [← h1]
      refine Subgroup.commutator_le.mpr fun t ht u hu => ?_
      have huB : u ∈ Vn δ' := Subgroup.zpowers_le.mpr hy.1 hu
      have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ' (hKX ht)) u).mp huB
      have hB' : t * u * t⁻¹ * u⁻¹ ∈ Vn δ' := (Vn δ').mul_mem this ((Vn δ').inv_mem huB)
      exact pairVn_le_Qv hG δ' hB'
  have h1 : (Vn δ' ⊓ Qv α).relIndex (Vn δ') ≤ 4 := by
    have := cii_relIndex_Qv_le hG hα hvα hBs (n := 2)
      (c3_idx_two hG hirr h15 hng hp).2.le
    simpa using this
  have h2 : (Vn δ' ⊓ Qv α ⊓ Qv γ).relIndex (Vn δ' ⊓ Qv α) ≤ 4 :=
    klein_le_four (X := stab γ) (quot_stab_five hA hvγ)
      (inf_le_right.trans (Qv_le_stab_of_mem_nbrs hA hγ))
      (isElemAbelian_mono hBe inf_le_left)
  have hne : ∀ H₁ L : Subgroup G, H₁.relIndex L ≠ 0 := fun _ _ =>
    Subgroup.index_ne_zero_of_finite
  have hchain : (fixSecIn (Vn γ) (Cb δ') (Vn δ')).relIndex (Vn δ') ≤
      (Vn δ' ⊓ Qv α ⊓ Qv γ).relIndex (Vn δ') := by
    refine (Subgroup.relIndex_le_of_le_left hb (hne _ _)).trans ?_
    refine Subgroup.relIndex_le_of_le_left ?_ (hne _ _)
    exact inf_le_inf_right _ inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (Vn δ' ⊓ Qv α ⊓ Qv γ) (Vn δ' ⊓ Qv α) (Vn δ')
    inf_le_left inf_le_left
  have h4 : (Vn δ' ⊓ Qv α ⊓ Qv γ).relIndex (Vn δ' ⊓ Qv α) = 4 := by
    rw [← hmul] at hchain
    have := h16.trans hchain
    set a := (Vn δ' ⊓ Qv α ⊓ Qv γ).relIndex (Vn δ' ⊓ Qv α)
    set c := (Vn δ' ⊓ Qv α).relIndex (Vn δ')
    nlinarith
  exact klein_exists_over (X := stab γ) (K := Vn δ' ⊓ Qv α) (quot_stab_five hA hvγ)
    (inf_le_right.trans (Qv_le_stab_of_mem_nbrs hA hγ))
    (isElemAbelian_mono hBe inf_le_left) h4

omit [Finite G] in
theorem cii_sup_comm {V Z P₁ P₂ : Subgroup G} {y : G} (hV : IsMulCommutative V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hP₁ : P₁ ≤ V) (hP₂ : P₂ ≤ V)
    (h₁ : ∀ a ∈ P₁, y * a * y⁻¹ * a⁻¹ ∈ Z) (h₂ : ∀ a ∈ P₂, y * a * y⁻¹ * a⁻¹ ∈ Z) :
    ∀ a ∈ P₁ ⊔ P₂, y * a * y⁻¹ * a⁻¹ ∈ Z := by
  let A₀ : Subgroup G := ((Z.subgroupOf V).comap (yCommHom hV hy)).map V.subtype
  have hmem : ∀ a ∈ V, y * a * y⁻¹ * a⁻¹ ∈ Z → a ∈ A₀ := fun a ha h =>
    ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr (by rw [coe_yCommHom]; exact h), rfl⟩
  have hle : P₁ ⊔ P₂ ≤ A₀ := sup_le (fun a ha => hmem a (hP₁ ha) (h₁ a ha))
    (fun a ha => hmem a (hP₂ ha) (h₂ a ha))
  intro a ha
  obtain ⟨x, hx, rfl⟩ := hle ha
  have := Subgroup.mem_subgroupOf.mp hx
  rwa [coe_yCommHom] at this

theorem cii_d (hG : Glob H M S) (hp : PD δ δ') {α : Geo H M} (hα : α ∈ nbrs δ)
    (hbad : ¬ Zv α ≤ Qv δ') {γ : Geo H M} (hγ : γ ∈ nbrs α) (hc3 : Nat.card (Zv δ) = 4)
    (h4 : (Vn γ ⊓ Qv δ').relIndex (Vn γ) = 4) {f : G} (hf : f ∈ Vn δ' ⊓ Qv α) :
    rk γ f ≤ 8 := by
  have hA := hG.amalg
  have hvα : vtype α = true := cii_vtype_true hp.vδ hα
  have hvγ : vtype γ = false := cii_vtype_false hvα hγ
  have hfs : f ∈ stab γ := Qv_le_stab_of_mem_nbrs hA hγ hf.2
  have hZαA' : Zv α ≤ Vn γ := Zv_le_Vn_nbr (cii_nbrs_symm hγ)
  have hVe : IsElemAbelian 2 (Vn γ) := isElemAbelian_Vn' hG γ
  have hfN : f ∈ Subgroup.normalizer (Vn γ : Set G) := stab_le_normalizer_Vn γ hfs
  have h₁ : ∀ a ∈ Vn γ ⊓ Qv δ', f * a * f⁻¹ * a⁻¹ ∈ Zv δ' ⊓ Vn γ := fun a ha =>
    ⟨comm_Vn_Qv_le hG hp.vδ' (Subgroup.commutator_mem_commutator hf.1 ha.2),
      comm_mem_of_normalizer hfN ha.1⟩
  have h₂ : ∀ a ∈ Zv α, f * a * f⁻¹ * a⁻¹ ∈ Zv δ' ⊓ Vn γ := fun a ha => by
    have hc := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α ha).2 f hf.2
    rw [hc]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact (Zv δ' ⊓ Vn γ).one_mem
  have hcomm := cii_sup_comm hVe.1 hfN inf_le_left hZαA' h₁ h₂
  have hcb : f ∈ Subgroup.normalizer (Cb γ : Set G) := stab_le_normalizer_Cb γ hfs
  have h := secIdx_le_of_comm (V := Vn γ) (C := Cb γ) (A₀ := (Vn γ ⊓ Qv δ') ⊔ Zv α)
    (Z := Zv δ' ⊓ Vn γ) (y := f) hVe hfN hcb (Cb_le_Vn γ) (sup_le inf_le_left hZαA')
    inf_le_right hcomm
  have hidx : ((Vn γ ⊓ Qv δ') ⊔ Zv α).relIndex (Vn γ) ≤ 2 := by
    have hm := Subgroup.relIndex_mul_relIndex (Vn γ ⊓ Qv δ') ((Vn γ ⊓ Qv δ') ⊔ Zv α) (Vn γ)
      le_sup_left (sup_le inf_le_left hZαA')
    rw [h4] at hm
    have h1 : (Vn γ ⊓ Qv δ').relIndex ((Vn γ ⊓ Qv δ') ⊔ Zv α) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      exact hbad ((le_sup_right.trans hle).trans inf_le_right)
    have h0 : (Vn γ ⊓ Qv δ').relIndex ((Vn γ ⊓ Qv δ') ⊔ Zv α) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    by_contra hc
    have := Nat.mul_le_mul (show 2 ≤ (Vn γ ⊓ Qv δ').relIndex ((Vn γ ⊓ Qv δ') ⊔ Zv α) by omega)
      (show 3 ≤ ((Vn γ ⊓ Qv δ') ⊔ Zv α).relIndex (Vn γ) by omega)
    omega
  have hZc : (Zv δ' ⊓ Vn γ ⊓ Cb γ).relIndex (Zv δ' ⊓ Vn γ) ≤ 4 := by
    have h1 := Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card (H := Zv δ' ⊓ Vn γ ⊓ Cb γ)
      (K := Zv δ' ⊓ Vn γ))
    have h2 : Nat.card (Zv δ' ⊓ Vn γ : Subgroup G) ≤ Nat.card (Zv δ') :=
      Subgroup.card_le_of_le inf_le_left
    rw [← card_Zv_eq_of_vtype hG hp.vδ hp.vδ', hc3] at h2
    exact h1.trans h2
  unfold rk
  calc _ ≤ _ := h
    _ ≤ 2 * 4 := Nat.mul_le_mul hidx hZc

theorem case_ii_false (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    (hb5 : 5 ≤ bMin H M) {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ')
    {γ : Geo H M} (hγ : γ ∈ nbrs α) (hγδ : γ ≠ δ) (hW : ¬ Vn γ ≤ Vn δ ⊔ Qv δ') : False := by
  have hA := hG.amalg
  have hvα : vtype α = true := cii_vtype_true hp.vδ hα
  have hvγ : vtype γ = false := cii_vtype_false hvα hγ
  obtain ⟨ε, hε, hVε, -⟩ := geo115 hG hirr h15 hng hp hb5 hα hbad hγ hγδ
  obtain ⟨h4, h16⟩ := cii_a hG hirr h15 hng hp hα hbad hγ hε hVε hW
  have hKX : Vn γ ≤ stab δ' :=
    hVε.trans ((Qv_le_inf hA (cii_nbrs_symm hε)).trans inf_le_right)
  obtain ⟨f, hf, hov⟩ := cii_bc hG hirr h15 hng hp hα hbad hγ hγδ hKX h16
  have hfs : f ∈ stab γ := Qv_le_stab_of_mem_nbrs hA hγ hf.2
  have h8 := cii_d hG hp hα hbad hγ (c3_card_Zv hG hirr h15 hng hp) h4 hf
  have h9 := NG.rk_gt hG hirr hng hvγ hfs hov
  omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
