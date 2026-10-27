module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

variable {W : Type} [CommGroup W] [Finite W]

private theorem odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hpg
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite W] in
private theorem comm_of_mem {p : ℕ} {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite W] in
private theorem mem_normalizer_of_mem {p : ℕ} {E D : Subgroup (MulAut W)}
    (hE : IsElemAbelian p E) (hDA : D ≤ E) {x : MulAut W} (hxE : x ∈ E) :
    x ∈ normalizer (D : Set (MulAut W)) := by
  have hconj : ∀ y ∈ E, x * y * x⁻¹ = y := by
    intro y hy
    rw [comm_of_mem hE hxE hy, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hconj y (hDA hy)]
    exact hy
  · intro hy
    have hyE : y ∈ E := by
      have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [h1]
      exact E.mul_mem (E.mul_mem (E.inv_mem hxE) (hDA hy)) hxE
    rwa [hconj y hyE] at hy

omit [Finite W] in
private theorem hypPart_stable_of_mem_normalizer {E D : Subgroup (MulAut W)}
    {x : MulAut W} (hnormE : x ∈ normalizer (E : Set (MulAut W)))
    (hnormD : x ∈ normalizer (D : Set (MulAut W))) :
    ∀ m ∈ hypPart E D, x m ∈ hypPart E D := by
  intro m hm
  refine ⟨?_, ?_⟩
  · have hm' : m ∈ commV E := by
      rw [commV_eq_commSub]
      exact hm.1
    have h := commV_apply_mem_of_mem_normalizer hnormE hm'
    rwa [commV_eq_commSub] at h
  · exact fixV_apply_mem_of_mem_normalizer hnormD hm.2

private theorem hypPart_inf_fixV_zpowers_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E D : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {x : MulAut W} (hsup : D ⊔ Subgroup.zpowers x = E) :
    hypPart E D ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
  have hodd := odd_card_of_isElemAbelian (W := W) hp hp2 hE
  have hbot : commSub ⊤ E ⊓ fixV E = ⊥ := by
    have h := (coprime_decomp (P := E) hodd hW (W := (⊤ : Subgroup W))
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    simpa using h
  have h1 : fixV D ⊓ fixV (Subgroup.zpowers x) = fixV E := by
    rw [← FixVLat.fixV_sup_eq D (Subgroup.zpowers x), hsup]
  unfold hypPart
  rw [inf_assoc, h1]
  exact hbot

omit [Finite W] in
private theorem sup_eq_of_hyperplane_of_not_le {p : ℕ} (hp : p.Prime)
    {A D B : Subgroup (MulAut W)} (hD : D ∈ hyperplanes p A) (hBA : B ≤ A)
    (hBD : ¬ B ≤ D) : D ⊔ B = A := by
  obtain ⟨hDA, hDi⟩ := hD
  have hle : D ⊔ B ≤ A := sup_le hDA hBA
  have h1 := Subgroup.relIndex_mul_relIndex D (D ⊔ B) A le_sup_left hle
  rw [hDi] at h1
  have hdvd : (D ⊔ B).relIndex A ∣ p := ⟨D.relIndex (D ⊔ B), by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h)
  · exfalso
    rw [h] at h1
    have h2 : D.relIndex (D ⊔ B) = 1 := by
      have := hp.pos
      nlinarith
    exact hBD (le_trans le_sup_right (Subgroup.relIndex_eq_one.1 h2))

private theorem hypPart_decomposition (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) :
    iSupIndep (fun D : hyperplanes p E => hypPart E D) ∧
      (⨆ D : hyperplanes p E, hypPart E D) = commSub ⊤ E := by
  have hodd := odd_card_of_isElemAbelian (W := W) hp hp2 hE
  have hU : StableUnder E (commSub ⊤ E) := by
    intro x hx u hu
    rw [← commV_eq_commSub] at hu ⊢
    exact commV_apply_mem_of_mem hx hu
  have hAU : commSub (commSub ⊤ E) E = commSub ⊤ E := by
    have h := commV_eq_commSub_commV (P := E) (S := E) hW hodd le_rfl
    rw [commV_eq_commSub] at h
    exact h.symm
  exact CFSG.LocalAnalysis.WeakClosure81.inf_fixV_hyperplane_decomposition hW hp hp2 E hE
    hU hAU

private theorem hypPart_le_commSub_zpowers (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U : Subgroup (MulAut W)} (hU : IsElemAbelian p U) {x : MulAut W}
    (hxU : x ∈ U) (hx : orderOf x = p) {D : Subgroup (MulAut W)} (hD : D ∈ hypSupp p U)
    (hxD : x ∉ D) : hypPart U D ≤ commSub ⊤ (Subgroup.zpowers x) := by
  have hDU : D ≤ U := hD.1.1
  have hsup : D ⊔ Subgroup.zpowers x = U :=
    sup_eq_of_hyperplane_of_not_le hp hD.1 (Subgroup.zpowers_le.mpr hxU)
      (fun hle => hxD (hle (Subgroup.mem_zpowers x)))
  have hfix : hypPart U D ⊓ fixV (Subgroup.zpowers x) = ⊥ :=
    hypPart_inf_fixV_zpowers_eq_bot hW hp hp2 hU hsup
  have hodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hx]
    exact hp.odd_of_ne_two hp2
  have hnormU : x ∈ normalizer (U : Set (MulAut W)) := Subgroup.le_normalizer hxU
  have hnormD : x ∈ normalizer (D : Set (MulAut W)) := mem_normalizer_of_mem hU hDU hxU
  have hzpU : Subgroup.zpowers x ≤ normalizer (U : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hnormU
  have hzpD : Subgroup.zpowers x ≤ normalizer (D : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hnormD
  have hstab : ∀ y ∈ Subgroup.zpowers x, ∀ m ∈ hypPart U D, y m ∈ hypPart U D :=
    fun y hy => hypPart_stable_of_mem_normalizer (hzpU hy) (hzpD hy)
  have hdec := coprime_decomp (P := Subgroup.zpowers x) hodd hW hstab
  have hM : commSub (hypPart U D) (Subgroup.zpowers x) = hypPart U D := by
    have h := hdec.1
    rwa [hfix, sup_bot_eq] at h
  rw [← hM]
  exact commSub_mono le_top le_rfl

theorem le_rk_commSub_of_conj_hyperplanes (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U : Subgroup (MulAut W)} (hU : IsElemAbelian p U) {x : MulAut W}
    (hxU : x ∈ U) (hx : orderOf x = p) {k : ℕ}
    (h : ∀ D₀ : Subgroup (MulAut W), D₀ ≤ U → D₀.relIndex U = p →
      k ≤ {D : Subgroup (MulAut W) | x ∉ D ∧
        ∃ g ∈ normalizer (U : Set (MulAut W)), D = D₀.map (MulAut.conj g).toMonoidHom}.ncard) :
    k * dParam p ≤ rk ↥(commSub ⊤ (zpowers x)) := by
  classical
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hU1 : U ≠ ⊥ := by
    intro h0
    have hxbot : x ∈ (⊥ : Subgroup (MulAut W)) := by simpa [h0] using hxU
    exact hxne (Subgroup.mem_bot.mp hxbot)
  obtain ⟨D₀, hD₀⟩ := hypSupp_nonempty hW hp hp2 hU hU1
  set s : Set (Subgroup (MulAut W)) :=
    {D : Subgroup (MulAut W) | x ∉ D ∧ ∃ g ∈ normalizer (U : Set (MulAut W)),
      D = D₀.map (MulAut.conj g).toMonoidHom}
  have hk : k ≤ s.ncard := h D₀ hD₀.1.1 hD₀.1.2
  have hs_sub : s ⊆ hypSupp p U := by
    rintro D ⟨hxD, g, hg, rfl⟩
    exact map_conj_mem_hypSupp hg hD₀
  have hsfin : s.Finite := (finite_hyperplanes p U).subset (fun D hD => (hs_sub hD).1)
  have hsfin_mem : ∀ D ∈ hsfin.toFinset, D ∈ s := fun D hD => hsfin.mem_toFinset.mp hD
  have hsum_ge : dParam p * s.ncard ≤ ∑ D ∈ hsfin.toFinset, rk ↥(hypPart U D) := by
    have hconst : dParam p * s.ncard = ∑ D ∈ hsfin.toFinset, dParam p := by
      rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card s hsfin, mul_comm]
    rw [hconst]
    exact Finset.sum_le_sum fun D hD =>
      dParam_le_rk_hypPart hW hp hp2 hU (hs_sub (hsfin_mem D hD))
  have hsum_le : ∑ D ∈ hsfin.toFinset, rk ↥(hypPart U D) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers x)) := by
    obtain ⟨hind, -⟩ := hypPart_decomposition hW hp hp2 hU
    set f : ↥(hsfin.toFinset) → hyperplanes p U := fun D => ⟨D.1, (hs_sub (hsfin_mem D.1 D.2)).1⟩
      with hf
    set T' : Finset (hyperplanes p U) := hsfin.toFinset.attach.image f with hT'
    have hf_inj : ∀ x ∈ hsfin.toFinset.attach, ∀ y ∈ hsfin.toFinset.attach,
        f x = f y → x = y := by
      intro x _ y _ hxy
      exact Subtype.ext (congrArg (fun z : hyperplanes p U => z.1) hxy)
    have hsum := rk_iSup_biSup_eq_sum (S := fun D : hyperplanes p U => hypPart U D) hind T'
    have hcard : ∑ D ∈ T', rk ↥(hypPart U D.1) = ∑ D ∈ hsfin.toFinset, rk ↥(hypPart U D) := by
      rw [hT', Finset.sum_image hf_inj]
      exact Finset.sum_attach hsfin.toFinset (fun D => rk ↥(hypPart U D))
    have hle : (⨆ i ∈ T', hypPart U i.1) ≤ commSub ⊤ (Subgroup.zpowers x) := by
      refine iSup_le fun i => iSup_le fun hi => ?_
      have hi_s : i.1 ∈ s := by
        rw [hT'] at hi
        rcases Finset.mem_image.mp hi with ⟨D, -, rfl⟩
        exact hsfin_mem D.1 D.2
      exact hypPart_le_commSub_zpowers hW hp hp2 hU hxU hx (hs_sub hi_s) hi_s.1
    calc ∑ D ∈ hsfin.toFinset, rk ↥(hypPart U D)
        = ∑ D ∈ T', rk ↥(hypPart U D.1) := hcard.symm
      _ = rk ↥(⨆ i ∈ T', hypPart U i.1) := hsum.symm
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := rk_mono hle
  calc k * dParam p ≤ s.ncard * dParam p := Nat.mul_le_mul_right _ hk
    _ = dParam p * s.ncard := Nat.mul_comm _ _
    _ ≤ ∑ D ∈ hsfin.toFinset, rk ↥(hypPart U D) := hsum_ge
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := hsum_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
