module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Frobenius
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Orbits
public import CFSG.Quasithin.Background.D2Y2
public import CFSG.LieType.SeitzGeneration.HyperAnisoBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {W : Type} [CommGroup W] [Finite W]

abbrev hypPart (E D : Subgroup (MulAut W)) : Subgroup W := commSub ⊤ E ⊓ fixV D

@[expose] def hypSupp (p : ℕ) (E : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {D | D ∈ hyperplanes p E ∧ hypPart E D ≠ ⊥}

omit [Finite W] in
private theorem h74_comm {p : ℕ} {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem h74_odd_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hpg
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem h74_finite_subgroup (M : Type*) [Group M] [Finite M] : Finite (Subgroup M) :=
  Finite.of_injective (fun H : Subgroup M => (H : Set M)) SetLike.coe_injective

omit [Finite W] in
private theorem h74_map_conj_eq {E : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) :
    E.map (MulAut.conj n).toMonoidHom = E := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
    simpa [MulAut.conj_apply] using h
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * x * n, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp
        ((normalizer (E : Set (MulAut W))).inv_mem hn) x).mp hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

omit [Finite W] in
private theorem h74_map_hypPart_conj {E D : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) :
    (hypPart E D).map n.toMonoidHom = hypPart E (D.map (MulAut.conj n).toMonoidHom) := by
  have hEimg := h74_map_conj_eq (E := E) hn
  have hU : (commSub ⊤ E).map n.toMonoidHom = commSub ⊤ E := by
    have h := commV_map_conj_eq E n
    rw [hEimg, commV_eq_commSub] at h
    exact h.symm
  unfold hypPart
  rw [Subgroup.map_inf _ _ _ n.injective, hU, ← CFSG.Quasithin.fixV_map_conj_eq D n]

private theorem h74_hypPart_decomposition (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) :
    iSupIndep (fun D : hyperplanes p E => hypPart E D) ∧
      (⨆ D : hyperplanes p E, hypPart E D) = commSub ⊤ E := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd := h74_odd_card (W := W) hp hp2 hE
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

theorem hypSupp_nonempty (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) :
    (hypSupp p E).Nonempty := by
  classical
  obtain ⟨-, hsup⟩ := h74_hypPart_decomposition hW hp hp2 hE
  have hUne : commSub ⊤ E ≠ ⊥ := by
    intro h0
    apply hE1
    have hfix : (⊤ : Subgroup W) ≤ fixV E := commSub_eq_bot_iff.mp h0
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    exact MulEquiv.ext fun w => hfix (Subgroup.mem_top w) e he
  by_contra hne
  have hz : ∀ D : hyperplanes p E, hypPart E D = ⊥ := by
    intro D
    by_contra hD
    exact hne ⟨D.1, D.2, hD⟩
  have hbot : (⨆ D : hyperplanes p E, hypPart E D) = ⊥ := iSup_eq_bot.mpr hz
  rw [hsup] at hbot
  exact hUne hbot

omit [Finite W] in
theorem map_conj_mem_hypSupp {p : ℕ} {E D : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) (hD : D ∈ hypSupp p E) :
    D.map (MulAut.conj n).toMonoidHom ∈ hypSupp p E := by
  obtain ⟨⟨hDE, hDr⟩, hDne⟩ := hD
  have hEimg := h74_map_conj_eq hn
  have hmap := h74_map_hypPart_conj (E := E) (D := D) hn
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hEimg ▸ Subgroup.map_mono hDE
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj n).toMonoidHom)
      D E (MulAut.conj n).injective
    rw [hEimg, hDr] at h
    exact h
  · rw [← hmap]
    intro hbot
    exact hDne ((Subgroup.map_eq_bot_iff_of_injective _ n.injective).1 hbot)

omit [Finite W] in
theorem rk_hypPart_map_conj {E D : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) :
    rk ↥(hypPart E (D.map (MulAut.conj n).toMonoidHom)) = rk ↥(hypPart E D) := by
  rw [← h74_map_hypPart_conj (E := E) (D := D) hn]
  unfold rk
  rw [Subgroup.card_map_of_injective n.injective]

omit [Finite W] in
private theorem h74_exists_complement {p : ℕ} (hp : p.Prime) {E D : Subgroup (MulAut W)}
    (hE : IsElemAbelian p E) (hD : D ∈ hyperplanes p E) :
    ∃ x : MulAut W, x ∈ E ∧ x ∉ D ∧ orderOf x = p ∧ D ⊔ Subgroup.zpowers x = E := by
  obtain ⟨hDA, hDr⟩ := hD
  have hDEne : D ≠ E := by
    intro h
    rw [h, Subgroup.relIndex_self] at hDr
    exact hp.ne_one hDr.symm
  obtain ⟨x, hxE, hxD⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hDA hDEne)
  have hsup : D ⊔ Subgroup.zpowers x = E :=
    CFSG.LieType.SeitzGeneration.HyperBlocks.sup_zpowers_eq hp hDA hDr hxE hxD
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 x hxE)
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h)
        (fun h1 => hxD (by rw [h1]; exact D.one_mem))
    · exact h
  exact ⟨x, hxE, hxD, hxord, hsup⟩

omit [Finite W] in
private theorem h74_mem_normalizer_of_mem {p : ℕ} {E D : Subgroup (MulAut W)}
    (hE : IsElemAbelian p E) (hDA : D ≤ E) {x : MulAut W} (hxE : x ∈ E) :
    x ∈ normalizer (D : Set (MulAut W)) := by
  have hconj : ∀ y ∈ E, x * y * x⁻¹ = y := by
    intro y hy
    rw [h74_comm hE hxE hy, mul_inv_cancel_right]
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
private theorem h74_hypPart_stable_of_mem_normalizer {E D : Subgroup (MulAut W)}
    {x : MulAut W} (hnormE : x ∈ normalizer (E : Set (MulAut W)))
    (hnormD : x ∈ normalizer (D : Set (MulAut W))) :
    ∀ m ∈ hypPart E D, x m ∈ hypPart E D := by
  intro m hm
  refine ⟨?_, ?_⟩
  · have hm' : m ∈ commV E := by
      rw [commV_eq_commSub]
      exact hm.1
    have h := commV_apply_mem_of_mem_normalizer hnormE hm'
    rw [commV_eq_commSub] at h
    exact h
  · exact fixV_apply_mem_of_mem_normalizer hnormD hm.2

private theorem h74_hypPart_inf_fixV_zpowers_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E D : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {x : MulAut W} (hsup : D ⊔ Subgroup.zpowers x = E) :
    hypPart E D ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd := h74_odd_card (W := W) hp hp2 hE
  have hbot : commSub ⊤ E ⊓ fixV E = ⊥ := by
    have h := (coprime_decomp (P := E) hodd hW (W := (⊤ : Subgroup W))
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    simpa using h
  have h1 : fixV D ⊓ fixV (Subgroup.zpowers x) = fixV E := by
    rw [← FixVLat.fixV_sup_eq D (Subgroup.zpowers x), hsup]
  unfold hypPart
  rw [inf_assoc, h1]
  exact hbot

theorem dParam_le_rk_hypPart (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E D : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (hD : D ∈ hypSupp p E) :
    dParam p ≤ rk ↥(hypPart E D) := by
  obtain ⟨hDA, -⟩ := hD.1
  obtain ⟨x, hxE, -, hxord, hsup⟩ := h74_exists_complement hp hE hD.1
  have hnormD := h74_mem_normalizer_of_mem hE hDA hxE
  have hMx := h74_hypPart_stable_of_mem_normalizer (Subgroup.le_normalizer hxE) hnormD
  have hfix := h74_hypPart_inf_fixV_zpowers_eq_bot hW hp hp2 hE hsup
  have hdvd := dParam_dvd_rk hW hp hp2 hxord hMx hfix
  have hrk : 0 < rk ↥(hypPart E D) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hD.2 ((rk_eq_zero_iff hW).mp h0)
  exact Nat.le_of_dvd hrk hdvd

omit [Finite W] in
private theorem h74_inv_inverts {E : Subgroup (MulAut W)} {g : MulAut W}
    (hinv : ∀ x ∈ E, g * x * g⁻¹ = x⁻¹) :
    ∀ x ∈ E, g⁻¹ * x * g = x⁻¹ := by
  intro x hx
  have h1 : x = g * x⁻¹ * g⁻¹ := by
    have h' := congrArg (fun y => y⁻¹) (hinv x hx)
    simpa [mul_assoc] using h'.symm
  calc g⁻¹ * x * g = g⁻¹ * (g * x⁻¹ * g⁻¹) * g := congrArg (fun y => g⁻¹ * y * g) h1
    _ = x⁻¹ := by group

theorem dihedralDeg_le_rk_hypPart (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E D : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (hD : D ∈ hypSupp p E)
    {g : MulAut W} (hinv : ∀ x ∈ E, g * x * g⁻¹ = x⁻¹) :
    WeakClosure81.dihedralDeg p ≤ rk ↥(hypPart E D) := by
  obtain ⟨hDA, -⟩ := hD.1
  obtain ⟨x, hxE, -, hxord, hsup⟩ := h74_exists_complement hp hE hD.1
  have hnormDx := h74_mem_normalizer_of_mem hE hDA hxE
  have hMx := h74_hypPart_stable_of_mem_normalizer (Subgroup.le_normalizer hxE) hnormDx
  have hginv := h74_inv_inverts hinv
  have hgnormE : g ∈ normalizer (E : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hinv y hy]
      exact E.inv_mem hy
    · intro hy
      have h := hginv (g * y * g⁻¹) hy
      have h1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [h1] at h
      rw [h]
      exact E.inv_mem hy
  have hgnormD : g ∈ normalizer (D : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hinv y (hDA hy)]
      exact D.inv_mem hy
    · intro hy
      have h := hginv (g * y * g⁻¹) (hDA hy)
      have h1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [h1] at h
      rw [h]
      exact D.inv_mem hy
  have hMg := h74_hypPart_stable_of_mem_normalizer hgnormE hgnormD
  have hfix := h74_hypPart_inf_fixV_zpowers_eq_bot hW hp hp2 hE hsup
  exact dihedralDeg_le_rk hW hp hp2 hxord hD.2 hMx hMg hfix (hinv x hxE)

theorem sum_rk_hypPart_le (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (T : Finset (Subgroup (MulAut W)))
    (hT : ∀ D ∈ T, D ∈ hyperplanes p E) :
    ∑ D ∈ T, rk ↥(hypPart E D) ≤ rk ↥(commSub ⊤ E) := by
  classical
  obtain ⟨hind, hsup⟩ := h74_hypPart_decomposition hW hp hp2 hE
  set f : ↥T → hyperplanes p E := fun D => ⟨D.1, hT D.1 D.2⟩ with hf
  set T' : Finset (hyperplanes p E) := T.attach.image f with hT'
  have hf_inj : ∀ x ∈ T.attach, ∀ y ∈ T.attach, f x = f y → x = y := by
    intro x _ y _ h
    exact Subtype.ext (congrArg (fun z : hyperplanes p E => z.1) h)
  have hsum := rk_iSup_biSup_eq_sum (S := fun D : hyperplanes p E => hypPart E D) hind T'
  have hcard : ∑ D ∈ T', rk ↥(hypPart E D.1) = ∑ D ∈ T, rk ↥(hypPart E D) := by
    rw [hT', Finset.sum_image hf_inj]
    exact Finset.sum_attach T (fun D => rk ↥(hypPart E D))
  have hle : (⨆ i ∈ T', hypPart E i.1) ≤ commSub ⊤ E := by
    rw [← hsup]
    refine iSup_le fun i => iSup_le fun _ => ?_
    exact le_iSup (fun D : hyperplanes p E => hypPart E D) i
  calc ∑ D ∈ T, rk ↥(hypPart E D) = ∑ D ∈ T', rk ↥(hypPart E D.1) := hcard.symm
    _ = rk ↥(⨆ i ∈ T', hypPart E i.1) := hsum.symm
    _ ≤ rk ↥(commSub ⊤ E) := rk_mono hle

theorem finite_hyperplanes (p : ℕ) (E : Subgroup (MulAut W)) : (hyperplanes p E).Finite := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  have : Finite (Subgroup (MulAut W)) := h74_finite_subgroup (MulAut W)
  exact Set.toFinite _

theorem mul_ncard_hypSupp_le (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) {c : ℕ}
    (hc : ∀ D ∈ hypSupp p E, c ≤ rk ↥(hypPart E D)) :
    c * (hypSupp p E).ncard ≤ rk ↥(commSub ⊤ E) := by
  classical
  set s := hypSupp p E with hs
  have hfin : s.Finite := (finite_hyperplanes p E).subset (fun D hD => hD.1)
  have hmem : ∀ D ∈ hfin.toFinset, D ∈ s := fun D hD => hfin.mem_toFinset.mp hD
  have hsub : ∀ D ∈ hfin.toFinset, D ∈ hyperplanes p E := fun D hD => (hmem D hD).1
  have h1 : c * s.ncard = ∑ D ∈ hfin.toFinset, c := by
    rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card s hfin, mul_comm]
  have h2 : ∑ D ∈ hfin.toFinset, c ≤ ∑ D ∈ hfin.toFinset, rk ↥(hypPart E D) :=
    Finset.sum_le_sum fun D hD => hc D (hmem D hD)
  have h3 := sum_rk_hypPart_le hW hp hp2 hE hfin.toFinset hsub
  calc c * s.ncard = ∑ D ∈ hfin.toFinset, c := h1
    _ ≤ ∑ D ∈ hfin.toFinset, rk ↥(hypPart E D) := h2
    _ ≤ rk ↥(commSub ⊤ E) := h3

theorem le_ncard_hypSupp (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E N : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hN : N ≤ normalizer (E : Set (MulAut W))) {c : ℕ}
    (horb : ∀ D ∈ hyperplanes p E, c ≤ (hypOrbit N D).ncard) :
    c ≤ (hypSupp p E).ncard := by
  obtain ⟨D, hD⟩ := hypSupp_nonempty hW hp hp2 hE hE1
  have hsub : hypOrbit N D ⊆ hypSupp p E := by
    rintro D' ⟨n, hnN, rfl⟩
    exact map_conj_mem_hypSupp (hN hnN) hD
  have hfin : (hypSupp p E).Finite := (finite_hyperplanes p E).subset (fun D hD => hD.1)
  calc c ≤ (hypOrbit N D).ncard := horb D hD.1
    _ ≤ (hypSupp p E).ncard := Set.ncard_le_ncard hsub hfin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
