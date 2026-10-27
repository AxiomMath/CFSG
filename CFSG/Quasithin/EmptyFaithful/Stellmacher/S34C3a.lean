module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Case2

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
theorem c3_stab_le_normalizer_Cb (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Cb δ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (normalizer_le_normalizer_centralizer _ (le_normalizer_oTwoRes _ hg)) x
  constructor
  · intro hx
    exact ⟨h1.mp hx.1, h2.mp hx.2⟩
  · intro hx
    exact ⟨h1.mpr hx.1, h2.mpr hx.2⟩

theorem c3_comm_le_Vn (hG : Glob H M S) (hp : PD δ δ') :
    ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ ≤ Vn δ := by
  rw [Subgroup.commutator_le]
  intro a ha y hy
  have h1 : y * a⁻¹ * y⁻¹ ∈ Vn δ :=
    (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Vn δ ((pd_Vn_le_stab hG hp).2 hy)) a⁻¹).mp ((Vn δ).inv_mem ha.1)
  have e : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
  show a * y * a⁻¹ * y⁻¹ ∈ Vn δ
  rw [e]
  exact (Vn δ).mul_mem ha.1 h1

theorem c3_comm_eq (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') :
    Zv δ' ≤ Vn δ ∧ Zv δ ≤ Vn δ' ∧ ⁅Vn δ ⊓ Qv δ', Vn δ'⁆ = Zv δ' ∧
      ⁅Vn δ' ⊓ Qv δ, Vn δ⁆ = Zv δ := by
  obtain ⟨h1, hB, h3⟩ := case3_data hG hirr h15 hng hp
  have e1 := comm_A0_eq_Zv hG hp h1
  have hp' := hp.symm' hB
  have e2 := comm_A0_eq_Zv hG hp' h3
  refine ⟨?_, ?_, e1, e2⟩
  · rw [← e1]; exact c3_comm_le_Vn hG hp
  · rw [← e2]; exact c3_comm_le_Vn hG hp'

theorem c3_rk_le (hG : Glob H M S) (hp : PD δ δ') (hZ : Zv δ' ≤ Vn δ) {y : G}
    (hy : y ∈ Vn δ') :
    rk δ y ≤ (Vn δ ⊓ Qv δ').relIndex (Vn δ) * (Zv δ ⊓ Zv δ').relIndex (Zv δ') := by
  have hys : y ∈ stab δ := (pd_Vn_le_stab hG hp).2 hy
  have h := secIdx_le_of_comm (V := Vn δ) (C := Cb δ) (A₀ := Vn δ ⊓ Qv δ') (Z := Zv δ')
    (y := y) (isElemAbelian_Vn' hG δ) (stab_le_normalizer_Vn δ hys)
    (c3_stab_le_normalizer_Cb δ hys) (Cb_le_Vn δ) inf_le_left hZ (fun a ha =>
      comm_Vn_Qv_le hG hp.vδ' (Subgroup.commutator_mem_commutator hy ha.2))
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  have hle : Zv δ ⊓ Zv δ' ≤ Zv δ' ⊓ Cb δ :=
    le_inf inf_le_right (inf_le_left.trans (Zv_le_Cb hG hp.vδ))
  exact Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite

theorem c3_relIndex_Qv_le_eight (hG : Glob H M S) {δ ν : Geo H M} (hδ : vtype δ = false)
    (hν : ν ∈ nbrs δ) {K : Subgroup G} (hK : K ≤ stab δ) (hKe : IsElemAbelian 2 K) :
    (K ⊓ Qv ν).relIndex K ≤ 8 := by
  have hA := hG.amalg
  have h4 : (K ⊓ Qv δ).relIndex K ≤ 4 := klein_le_four (quot_stab_five hA hδ) hK hKe
  have hνs : vtype ν = true := by
    have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ ν from hν)
    cases h : vtype ν
    · rw [h] at this; exact absurd hδ this
    · rfl
  have hQ2 : (Qv ν).relIndex (stab δ ⊓ stab ν) = 2 :=
    EmptyFaithful.Stellmacher.OrdinaryProofs.relIndex_Qv_inf hA hν hνs
  have hle1 : K ⊓ Qv δ ≤ K ⊓ stab ν :=
    inf_le_inf_left _ (Qv_le_stab_of_mem_nbrs hA hν)
  have h5 : (K ⊓ stab ν).relIndex K ≤ 4 :=
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
  calc _ ≤ 2 * 4 := Nat.mul_le_mul h6 h5
    _ = 8 := by norm_num

theorem c3_Zv_inf_le_two (hG : Glob H M S) (hirr : IrrSecSec) (_h15 : Hss15Sec)
    (hng : NG H M) (hp : PD δ δ') {ν : Geo H M} (hν : ν ∈ nbrs δ) :
    (Zv ν ⊓ Qv δ').relIndex (Zv ν) ≤ 2 := by
  have hA := hG.amalg
  have hZA : Zv ν ≤ Vn δ := Zv_le_Vn_of_mem_nbrs hν
  have hKX : Zv ν ≤ stab δ' := hZA.trans (pd_Vn_le_stab hG hp).1
  have hKe : IsElemAbelian 2 (Zv ν) := isElemAbelian_mono (isElemAbelian_Vn' hG δ) hZA
  have hrk : ∀ g ∈ Zv ν, rk δ' g ≤ 8 := by
    intro g hg
    have hgs : g ∈ stab δ' := hKX hg
    have h := secIdx_le_of_comm (V := Vn δ') (C := Cb δ') (A₀ := Vn δ' ⊓ Qv ν)
      (Z := ⊥) (y := g) (isElemAbelian_Vn' hG δ') (stab_le_normalizer_Vn δ' hgs)
      (c3_stab_le_normalizer_Cb δ' hgs) (Cb_le_Vn δ') inf_le_left bot_le (fun a ha => by
        have hc := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ν hg).2 a ha.2
        refine Subgroup.mem_bot.mpr ?_
        rw [← hc]
        group)
    have h8 := c3_relIndex_Qv_le_eight hG hp.vδ hν (pd_Vn_le_stab hG hp).2
      (isElemAbelian_Vn' hG δ')
    have h1 : (⊥ ⊓ Cb δ').relIndex (⊥ : Subgroup G) = 1 := by
      rw [bot_inf_eq]; exact Subgroup.relIndex_self _
    unfold rk
    rw [h1, mul_one] at h
    exact h.trans h8
  refine klein_le_two (X := stab δ') (K := Zv ν) (quot_stab_five hA hp.vδ') hKX hKe
    (fun g hg hgo => ?_)
  by_contra hgQ
  have hsq : g ^ 2 ∈ pCoreOf 2 (stab δ') := by
    rw [hKe.2 g hg]; exact one_mem _
  have h1 := NG.rk_gt hG hirr hng hp.vδ' (hKX hg) ⟨hgo, hgQ, Or.inl hsq⟩
  have h2 := hrk g hg
  omega

theorem c3_relIndex_le_two_of_card {E K : Subgroup G} (hEK : E ≤ K)
    (h : Nat.card K ≤ 2 * Nat.card E) : E.relIndex K ≤ 2 := by
  have hm := Subgroup.relIndex_mul_card E K
  rw [inf_eq_left.mpr hEK] at hm
  have hpos : 0 < Nat.card E := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (hm.le.trans h) hpos

theorem c3_E_le_two (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') :
    (Zv δ ⊓ Zv δ').relIndex (Zv δ) ≤ 2 ∧ (Zv δ ⊓ Zv δ').relIndex (Zv δ') ≤ 2 := by
  have hA := hG.amalg
  have hB0 := (case3_data hG hirr h15 hng hp).2.2
  have hex : ∃ ν ∈ nbrs δ, ∃ y ∈ Vn δ' ⊓ Qv δ, ⁅Zv ν, Subgroup.zpowers y⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hB0
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    unfold Vn
    refine iSup₂_le fun ν hν z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h0 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon ν hν y hy) hz
    exact Subgroup.mem_centralizer_iff.mp h0 y (Subgroup.mem_zpowers y)
  obtain ⟨ν, hν, y, hy, hne⟩ := hex
  have hyδ : y ∈ stab δ := pCoreOf_le 2 (stab δ) hy.2
  have hyν : y ∈ stab ν := Qv_le_stab_of_mem_nbrs hA hν hy.2
  have hyQ : y ∉ Qv ν := fun h => hne ((aon_edge hG hp.vδ hν ⟨hyν, hyδ⟩).1 h)
  have hcomm : ⁅Zv ν, Subgroup.zpowers y⁆ = Zv δ := (aon_edge hG hp.vδ hν ⟨hyν, hyδ⟩).2 hyQ
  have hZνA : Zv ν ≤ Vn δ := Zv_le_Vn_of_mem_nbrs hν
  have hcard := card_comm_le (V := Zv ν) (A₀ := Zv ν ⊓ Qv δ') (Z := Zv δ ⊓ Zv δ') (y := y)
    (isElemAbelian_mono (isElemAbelian_Vn' hG δ) hZνA) (stab_le_normalizer_Zv hA ν hyν)
    inf_le_left (inf_le_left.trans (Zv_le_Zv_nbr hG hp.vδ hν)) (fun a ha => by
      refine ⟨?_, ?_⟩
      · have h1 := comm_Vn_Qv_le hG hp.vδ (Subgroup.commutator_mem_commutator (hZνA ha.1) hy.2)
        have e : y * a * y⁻¹ * a⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ h1
      · exact comm_Vn_Qv_le hG hp.vδ' (Subgroup.commutator_mem_commutator hy.1 ha.2))
  rw [hcomm] at hcard
  have h91 := c3_Zv_inf_le_two hG hirr h15 hng hp hν
  have hc : Nat.card (Zv δ) ≤ 2 * Nat.card ↥(Zv δ ⊓ Zv δ') :=
    hcard.trans (Nat.mul_le_mul_right _ h91)
  refine ⟨c3_relIndex_le_two_of_card inf_le_left hc, ?_⟩
  refine c3_relIndex_le_two_of_card inf_le_right ?_
  rw [← card_Zv_eq_of_vtype hG hp.vδ hp.vδ']
  exact hc

theorem c3_idx_aux (hG : Glob H M S) (hirr : IrrSecSec) (hng : NG H M) (hp : PD δ δ')
    (hZ' : Zv δ' ≤ Vn δ) (hB : ¬ Vn δ' ≤ Qv δ) (hE : (Zv δ ⊓ Zv δ').relIndex (Zv δ') ≤ 2) :
    (Vn δ' ⊓ Qv δ).relIndex (Vn δ') = 2 := by
  have hbd : ∀ y ∈ Vn δ', rk δ y ≤ 8 := fun y hy =>
    (c3_rk_le hG hp hZ' hy).trans (calc _ ≤ 4 * 2 := Nat.mul_le_mul (pd_relIndex hG hp).2 hE
      _ = 8 := by norm_num)
  have hle : (Vn δ' ⊓ pCoreOf 2 (stab δ)).relIndex (Vn δ') ≤ 2 := by
    refine klein_le_two (X := stab δ) (K := Vn δ') (quot_stab_five hG.amalg hp.vδ)
      (pd_Vn_le_stab hG hp).2 (isElemAbelian_Vn' hG δ') (fun g hg hgo => ?_)
    by_contra hgQ
    have hsq : g ^ 2 ∈ pCoreOf 2 (stab δ) := by
      rw [(isElemAbelian_Vn' hG δ').2 g hg]; exact one_mem _
    have h1 := NG.rk_gt hG hirr hng hp.vδ ((pd_Vn_le_stab hG hp).2 hg) ⟨hgo, hgQ, Or.inl hsq⟩
    have h2 := hbd g hg
    omega
  have h0 : (Vn δ' ⊓ Qv δ).relIndex (Vn δ') ≠ 1 := fun h =>
    hB ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
  have h0' : (Vn δ' ⊓ Qv δ).relIndex (Vn δ') ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle' : (Vn δ' ⊓ Qv δ).relIndex (Vn δ') ≤ 2 := hle
  omega

theorem c3_idx_two (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') :
    (Vn δ ⊓ Qv δ').relIndex (Vn δ) = 2 ∧ (Vn δ' ⊓ Qv δ).relIndex (Vn δ') = 2 := by
  obtain ⟨hZ'A, hZB, -, -⟩ := c3_comm_eq hG hirr h15 hng hp
  obtain ⟨hE1, hE2⟩ := c3_E_le_two hG hirr h15 hng hp
  have hB := (case3_data hG hirr h15 hng hp).2.1
  refine ⟨?_, c3_idx_aux hG hirr hng hp hZ'A hB hE2⟩
  exact c3_idx_aux hG hirr hng (hp.symm' hB) hZB hp.not_le (by rwa [inf_comm])

theorem c3_rk_le_four (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') :
    (∀ y ∈ Vn δ', rk δ y ≤ 4) ∧ (∀ x ∈ Vn δ, rk δ' x ≤ 4) := by
  obtain ⟨hZ'A, hZB, -, -⟩ := c3_comm_eq hG hirr h15 hng hp
  obtain ⟨hE1, hE2⟩ := c3_E_le_two hG hirr h15 hng hp
  obtain ⟨hi1, hi2⟩ := c3_idx_two hG hirr h15 hng hp
  have hB := (case3_data hG hirr h15 hng hp).2.1
  have hE1' : (Zv δ' ⊓ Zv δ).relIndex (Zv δ) ≤ 2 := by rwa [inf_comm]
  refine ⟨fun y hy => (c3_rk_le hG hp hZ'A hy).trans ?_, fun x hx =>
    (c3_rk_le hG (hp.symm' hB) hZB hx).trans ?_⟩
  · rw [hi1]; omega
  · rw [hi2]; omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
