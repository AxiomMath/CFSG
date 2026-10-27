module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Summand
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.DParam
import CFSG.Quasithin.Background.B1Coprime
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {W : Type} [CommGroup W] [Finite W]

private theorem odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hpg
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite W] in
private theorem hypPart_stable_of_mem_normalizer {E D : Subgroup (MulAut W)} {x : MulAut W}
    (hnormE : x ∈ normalizer (E : Set (MulAut W)))
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

omit [Finite W] in
private theorem stableUnder_hypPart_of_center {H : Subgroup (MulAut W)}
    {D : Subgroup (MulAut W)} (hD : D ≤ (center ↥H).map H.subtype) :
    StableUnder H (hypPart ((center ↥H).map H.subtype) D) := by
  intro h hh m hm
  have hcentral : ∀ z ∈ (center ↥H).map H.subtype, h * z * h⁻¹ = z := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : (⟨h, hh⟩ : ↥H) * c = c * ⟨h, hh⟩ :=
      Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
    have hval : h * H.subtype c = H.subtype c * h := by
      simpa using congrArg Subtype.val hcomm
    rw [hval]
    group
  have hnormE : h ∈ normalizer (((center ↥H).map H.subtype) : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, hcentral y hy] using hy
    · intro z hz
      exact ⟨z, hz, by simp [MulAut.conj_apply, hcentral z hz]⟩
  have hnormD : h ∈ normalizer (D : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, hcentral y (hD hy)] using hy
    · intro z hz
      exact ⟨z, hz, by simp [MulAut.conj_apply, hcentral z (hD hz)]⟩
  exact hypPart_stable_of_mem_normalizer hnormE hnormD m hm

private theorem hypPart_decomposition (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) :
    iSupIndep (fun D : hyperplanes p E => hypPart E D) ∧
      (⨆ D : hyperplanes p E, hypPart E D) = commSub ⊤ E := by
  have hodd := odd_card_of_isElemAbelian (W := W) hp hp2 hE
  have hU : StableUnder E (commSub ⊤ E) := by
    intro x hx u hu
    exact mem_commSub_of_mem_normalizer (Subgroup.le_normalizer hx) hu
  have hAU : commSub (commSub ⊤ E) E = commSub ⊤ E := by
    have h := commV_eq_commSub_commV (P := E) (S := E) hW hodd le_rfl
    rw [commV_eq_commSub] at h
    exact h.symm
  exact CFSG.LocalAnalysis.WeakClosure81.inf_fixV_hyperplane_decomposition hW hp hp2 E hE hU hAU

omit [Finite W] in
private theorem iSupIndep_commSub_of_le {p : ℕ} {E : Subgroup (MulAut W)} {x : MulAut W}
    (hdec : iSupIndep (fun D : hyperplanes p E => hypPart E D))
    (hNle : ∀ D : hyperplanes p E,
      commSub (hypPart E D) (Subgroup.zpowers x) ≤ hypPart E D) :
    iSupIndep (fun D : hyperplanes p E => commSub (hypPart E D) (Subgroup.zpowers x)) := by
  rw [iSupIndep_def] at hdec ⊢
  intro i
  refine (hdec i).mono (hNle i) ?_
  exact iSup₂_mono fun j _ => hNle j

private theorem rk_iSup_commSub_eq_sum {p : ℕ} {E : Subgroup (MulAut W)} {x : MulAut W}
    (hdec : iSupIndep (fun D : hyperplanes p E =>
      commSub (hypPart E D) (Subgroup.zpowers x)))
    (T : Finset (Subgroup (MulAut W))) (hT : ∀ D ∈ T, D ∈ hyperplanes p E) :
    rk ↥(⨆ D ∈ T, commSub (hypPart E D) (Subgroup.zpowers x)) =
      ∑ D ∈ T, rk ↥(commSub (hypPart E D) (Subgroup.zpowers x)) := by
  classical
  have hmap : (T.subtype (fun D => D ∈ hyperplanes p E)).map
      (Function.Embedding.subtype (fun D => D ∈ hyperplanes p E)) = T := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hT]
  have hsup : (⨆ D ∈ T, commSub (hypPart E D) (Subgroup.zpowers x)) =
      ⨆ D ∈ T.subtype (fun D => D ∈ hyperplanes p E),
        commSub (hypPart E D) (Subgroup.zpowers x) := by
    conv_lhs => rw [← hmap]
    rw [← Finset.sup_eq_iSup, Finset.sup_map, Finset.sup_eq_iSup]
    rfl
  have hsum : (∑ D ∈ T, rk ↥(commSub (hypPart E D) (Subgroup.zpowers x))) =
      ∑ D ∈ T.subtype (fun D => D ∈ hyperplanes p E),
        rk ↥(commSub (hypPart E D) (Subgroup.zpowers x)) := by
    conv_lhs => rw [← hmap]
    rw [Finset.sum_map]
    rfl
  rw [hsup, hsum,
    rk_iSup_biSup_eq_sum (fun D : hyperplanes p E =>
      commSub (hypPart E D) (Subgroup.zpowers x)) hdec
      (T.subtype (fun D => D ∈ hyperplanes p E))]

private theorem mul_ncard_hypSupp_le_of_commSub (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {x : MulAut W} {c : ℕ}
    (hNle : ∀ D : hyperplanes p E,
      commSub (hypPart E D) (Subgroup.zpowers x) ≤ hypPart E D)
    (hc : ∀ D ∈ hypSupp p E,
      c ≤ rk ↥(commSub (hypPart E D) (Subgroup.zpowers x))) :
    c * (hypSupp p E).ncard ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := by
  classical
  set s := hypSupp p E with hs
  have hfin : s.Finite := (finite_hyperplanes p E).subset (fun D hD => hD.1)
  have hmem : ∀ D ∈ hfin.toFinset, D ∈ s := fun D hD => hfin.mem_toFinset.mp hD
  have hsub : ∀ D ∈ hfin.toFinset, D ∈ hyperplanes p E := fun D hD => (hmem D hD).1
  obtain ⟨hdec, -⟩ := hypPart_decomposition hW hp hp2 hE
  have hNind := iSupIndep_commSub_of_le hdec hNle
  have hsum := rk_iSup_commSub_eq_sum hNind hfin.toFinset hsub
  have hle : (⨆ D ∈ hfin.toFinset,
      commSub (hypPart E D) (Subgroup.zpowers x)) ≤ commSub ⊤ (Subgroup.zpowers x) :=
    iSup₂_le fun D _ => commSub_mono le_top le_rfl
  have h1 : c * s.ncard = ∑ D ∈ hfin.toFinset, c := by
    rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card s hfin, mul_comm]
  have h2 : ∑ D ∈ hfin.toFinset, c ≤
      ∑ D ∈ hfin.toFinset, rk ↥(commSub (hypPart E D) (Subgroup.zpowers x)) :=
    Finset.sum_le_sum fun D hD => hc D (hmem D hD)
  calc c * s.ncard = ∑ D ∈ hfin.toFinset, c := h1
    _ ≤ ∑ D ∈ hfin.toFinset, rk ↥(commSub (hypPart E D) (Subgroup.zpowers x)) := h2
    _ = rk ↥(⨆ D ∈ hfin.toFinset,
        commSub (hypPart E D) (Subgroup.zpowers x)) := hsum.symm
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := rk_mono hle

private theorem mem_all_hypSupp_eq_one (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) {z : MulAut W}
    (hzE : z ∈ E) (hz : ∀ D, D ∈ hypSupp p E → z ∈ D) : z = 1 := by
  classical
  have hodd := odd_card_of_isElemAbelian (W := W) hp hp2 hE
  obtain ⟨-, hsup⟩ := hypPart_decomposition hW hp hp2 hE
  have hfixU : commSub ⊤ E ≤ fixV (Subgroup.zpowers z) := by
    rw [← hsup]
    refine iSup_le fun D => ?_
    by_cases hD : hypPart E (D : Subgroup (MulAut W)) = ⊥
    · rw [hD]
      exact bot_le
    · have hDsupp : (D : Subgroup (MulAut W)) ∈ hypSupp p E := ⟨D.2, hD⟩
      have hzp : Subgroup.zpowers z ≤ (D : Subgroup (MulAut W)) :=
        Subgroup.zpowers_le.mpr (hz D hDsupp)
      intro m hm s hs
      exact hm.2 s (hzp hs)
  have hfixZ : fixV E ≤ fixV (Subgroup.zpowers z) :=
    CFSG.Quasithin.B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hzE)
  have hWdecomp : (⊤ : Subgroup W) = fixV E ⊔ commSub ⊤ E := by
    have h := (CFSG.Quasithin.B1.coprime_decomp hW hodd (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).1
    simpa using h.symm
  have htop : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers z) := by
    rw [hWdecomp]
    exact sup_le hfixZ hfixU
  apply MulEquiv.ext
  intro w
  have hw : w ∈ fixV (Subgroup.zpowers z) := htop (Subgroup.mem_top w)
  simpa using hw z (Subgroup.mem_zpowers z)

private theorem exists_not_mem_hypSupp_of_mem_ne_one (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    {z : MulAut W} (hzE : z ∈ E) (hz1 : z ≠ 1) :
    ∃ D, D ∈ hypSupp p E ∧ z ∉ D := by
  by_contra h
  push Not at h
  exact hz1 (mem_all_hypSupp_eq_one hW hp hp2 hE hzE h)

omit [Finite W] in
private theorem card_hyperplane_eq {p e : ℕ} (hp : p.Prime) {E : Subgroup (MulAut W)}
    (hEcard : Nat.card E = p ^ e) (he : 1 ≤ e) {D : Subgroup (MulAut W)}
    (hD : D ∈ hyperplanes p E) : Nat.card D = p ^ (e - 1) := by
  obtain ⟨hDE, hDr⟩ := hD
  have hmul := Subgroup.relIndex_mul_card D E
  rw [inf_eq_left.mpr hDE, hDr, hEcard] at hmul
  have hpow : p ^ e = p ^ (e - 1) * p := by
    conv_lhs => rw [← Nat.sub_add_cancel he]
    rw [pow_succ]
  rw [hpow, mul_comm (p ^ (e - 1)) p] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

private theorem card_quotient_eq {p e N : ℕ} {H : Subgroup (MulAut W)}
    (hHcard : Nat.card ↥H = p ^ (e + 2 * N))
    (hZcard : Nat.card (center ↥H) = p ^ e)
    {D : Subgroup ↥H} [D.Normal] (hDZ : D ≤ center ↥H)
    (hDidx : D.relIndex (center ↥H) = p) :
    Nat.card (↥H ⧸ D) = p ^ (1 + 2 * N) := by
  have hDcard : p * Nat.card D = p ^ e := by
    have h := Subgroup.relIndex_mul_card D (center ↥H)
    rw [inf_eq_left.mpr hDZ, hDidx, hZcard] at h
    exact h
  have hquot : Nat.card ↥H = Nat.card (↥H ⧸ D) * Nat.card D :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup D
  have hEq : Nat.card (↥H ⧸ D) * Nat.card D = (p * p ^ (2 * N)) * Nat.card D := by
    calc Nat.card (↥H ⧸ D) * Nat.card D = Nat.card ↥H := hquot.symm
      _ = p ^ (e + 2 * N) := hHcard
      _ = p ^ e * p ^ (2 * N) := by rw [pow_add]
      _ = (p * Nat.card D) * p ^ (2 * N) := by rw [hDcard]
      _ = (p * p ^ (2 * N)) * Nat.card D := by ring
  have hQ : Nat.card (↥H ⧸ D) = p * p ^ (2 * N) :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card ↥D) hEq
  have hfinal : p * p ^ (2 * N) = p ^ (1 + 2 * N) := by
    rw [show 1 + 2 * N = 2 * N + 1 by ring, pow_succ, mul_comm]
  rwa [hfinal] at hQ

private theorem two_le_ncard_hypSupp_of_two_le_e (hW : ∀ w : W, w ^ 2 = 1) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 2 ≤ e) {E : Subgroup (MulAut W)}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ e) :
    2 ≤ (hypSupp p E).ncard := by
  classical
  have hE1 : E ≠ ⊥ := by
    intro h
    have h1 : Nat.card E = 1 := by simp [h]
    rw [hEcard] at h1
    have hp2le : 2 ≤ p := hp.two_le
    have h1p : 1 < p ^ e := by
      calc 1 < p := by omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.one_lt.le (by omega)
    omega
  obtain ⟨D₀, hD₀⟩ := hypSupp_nonempty hW hp hp2 hE hE1
  have hD₀card : Nat.card D₀ = p ^ (e - 1) :=
    card_hyperplane_eq hp hEcard (by omega) hD₀.1
  have hD₀big : 2 ≤ Nat.card D₀ := by
    rw [hD₀card]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (e - 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hD₀ne : D₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD₀big
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD₀ne
  let z : MulAut W := (a : ↥D₀)
  have hzD₀ : z ∈ D₀ := a.2
  have hz1 : z ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext h)
  have hzE : z ∈ E := hD₀.1.1 hzD₀
  obtain ⟨D₁, hD₁, hzD₁⟩ := exists_not_mem_hypSupp_of_mem_ne_one hW hp hp2 hE hzE hz1
  have hne : D₀ ≠ D₁ := by
    intro h
    exact hzD₁ (h ▸ hzD₀)
  have hpair : ({D₀, D₁} : Set (Subgroup (MulAut W))).ncard = 2 :=
    Set.ncard_pair hne
  have hsub : ({D₀, D₁} : Set (Subgroup (MulAut W))) ⊆ hypSupp p E := by
    intro D hD
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact hD₀
    · exact hD₁
  have hfin : (hypSupp p E).Finite :=
    (finite_hyperplanes p E).subset (fun D hD => hD.1)
  calc 2 = ({D₀, D₁} : Set (Subgroup (MulAut W))).ncard := hpair.symm
    _ ≤ (hypSupp p E).ncard := Set.ncard_le_ncard hsub hfin

private theorem one_le_e_of_three_lt_pow {p e : ℕ} (h3 : 3 < p ^ e) : 1 ≤ e := by
  rcases Nat.eq_zero_or_pos e with h | h
  · rw [h, pow_zero] at h3
    omega
  · exact h

private theorem two_le_e_of_three_lt_three_pow {e : ℕ} (h3 : 3 < 3 ^ e) : 2 ≤ e := by
  rcases e with _ | _ | e
  · norm_num at h3
  · norm_num at h3
  · omega

private theorem sixteen_le_mul_ncard {p N k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (_hN : 0 < N)
    (hk1 : 1 ≤ k) (hk3 : p = 3 → 2 ≤ k) (hN3 : p = 3 → 2 ≤ N) :
    16 ≤ (p - 1) * p ^ (N - 1) * dParam p * k := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h1 : 1 ≤ p ^ (N - 1) := Nat.one_le_pow _ _ (by omega)
  rcases odd_prime_cases hp hp2 with h | h | h | h11
  · subst h
    have hk : 2 ≤ k := hk3 rfl
    have hN2 : 2 ≤ N := hN3 rfl
    rw [dParam_eq_of_small.1]
    have hpow : 3 ≤ 3 ^ (N - 1) := by
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 16 ≤ (3 - 1) * 3 * 2 * 2 := by norm_num
      _ ≤ (3 - 1) * 3 ^ (N - 1) * 2 * k := by gcongr
  · subst h
    rw [dParam_eq_of_small.2.1]
    calc 16 ≤ (5 - 1) * 1 * 4 * 1 := by norm_num
      _ ≤ (5 - 1) * 5 ^ (N - 1) * 4 * k := by gcongr
  · subst h
    rw [dParam_eq_of_small.2.2.1]
    calc 16 ≤ (7 - 1) * 1 * 3 * 1 := by norm_num
      _ ≤ (7 - 1) * 7 ^ (N - 1) * 3 * k := by gcongr
  · have hd : 2 ≤ dParam p := two_le_dParam hp hp2
    have hp1' : 10 ≤ p - 1 := by omega
    calc 16 ≤ (p - 1) * 1 * 2 * 1 := by nlinarith
      _ ≤ (p - 1) * p ^ (N - 1) * dParam p * k := by gcongr

private theorem hypPart_bounds (hW : ∀ w : W, w ^ 2 = 1) {p e N : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H : Subgroup (MulAut W)} (hH : IsSpecialType p e N ↥H) (heN : e ≤ N)
    (h3 : 3 < p ^ e) {D : Subgroup (MulAut W)}
    (hD : D ∈ hypSupp p ((center ↥H).map H.subtype)) :
    p ^ N * dParam p ≤ rk ↥(hypPart ((center ↥H).map H.subtype) D) ∧
      ∀ x ∈ H, orderOf x = p → x ∉ (center ↥H).map H.subtype →
        (p - 1) * p ^ (N - 1) * dParam p ≤
          rk ↥(commSub (hypPart ((center ↥H).map H.subtype) D) (Subgroup.zpowers x)) := by
  classical
  have he1 : 1 ≤ e := one_le_e_of_three_lt_pow h3
  have hN : 0 < N := lt_of_lt_of_le he1 heN
  have hEcard : Nat.card ((center ↥H).map H.subtype) = p ^ e := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hH.2.2.1]
  have hE : IsElemAbelian p ((center ↥H).map H.subtype) := by
    have hc : IsElemAbelian p (center ↥H) :=
      ⟨inferInstance, fun x _ => hH.1 x⟩
    exact CFSG.Open.IsElemAbelian.map hc H.subtype
  set D' : Subgroup ↥H := D.comap H.subtype with hD'def
  have hmapD : D'.map H.subtype = D := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      exact hz
    · intro y hy
      have hyE : y ∈ (center ↥H).map H.subtype := hD.1.1 hy
      obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hyE
      exact ⟨c, hy, rfl⟩
  have hD'sub : D' ≤ center ↥H := by
    intro x hx
    have hx' : H.subtype x ∈ (center ↥H).map H.subtype := hD.1.1 hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx'
    have hcx' : c = x := Subtype.ext (by simpa using hcx)
    rw [hcx'] at hc
    exact hc
  have hD'idx : D'.relIndex (center ↥H) = p := by
    have h := Subgroup.relIndex_map_map_of_injective (f := H.subtype) D' (center ↥H)
      H.subtype_injective
    rw [hmapD] at h
    exact h.symm.trans hD.1.2
  have hD'norm : D'.Normal := Subgroup.normal_of_le_center hD'sub
  have : D'.Normal := hD'norm
  have hD'card : Nat.card (↥H ⧸ D') = p ^ (1 + 2 * N) :=
    card_quotient_eq hH.2.1 hH.2.2.1 hD'sub hD'idx
  have hext : CFSG.IsExtraspecialPGroup p (↥H ⧸ D') := hH.2.2.2 D' hD'sub hD'idx
  set M : Subgroup W := hypPart ((center ↥H).map H.subtype) D with hMdef
  have hM1 : M ≠ ⊥ := hD.2
  have hMD : M ≤ fixV (D'.map H.subtype) := by
    rw [hmapD, hMdef]
    exact inf_le_right
  have hfree : M ⊓ fixV ((center ↥H).map H.subtype) = ⊥ := by
    have hbot := commSub_inf_fixV_eq_bot hW hp hp2 hE
    rw [hMdef]
    exact le_bot_iff.mp ((inf_le_inf_right (fixV _) inf_le_left).trans (le_of_eq hbot))
  have hMstab : StableUnder H M := by
    rw [hMdef]
    exact stableUnder_hypPart_of_center hD.1.1
  exact summand_bounds hW hp hp2 hN D' hD'sub hD'idx hext hH.1 hD'card hMstab hMD hfree hM1

theorem sixteen_le_rk_commSub_of_isSpecialType (hW : ∀ w : W, w ^ 2 = 1) {p e N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup (MulAut W)} (hH : IsSpecialType p e N ↥H)
    (heN : e ≤ N) (h3 : 3 < p ^ e) {x : MulAut W} (hxH : x ∈ H) (hx : orderOf x = p) :
    16 ≤ rk ↥(commSub ⊤ (zpowers x)) := by
  classical
  have he1 : 1 ≤ e := one_le_e_of_three_lt_pow h3
  have hN : 0 < N := lt_of_lt_of_le he1 heN
  have hEcard : Nat.card ((center ↥H).map H.subtype) = p ^ e := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hH.2.2.1]
  have hE : IsElemAbelian p ((center ↥H).map H.subtype) := by
    have hc : IsElemAbelian p (center ↥H) :=
      ⟨inferInstance, fun y _ => hH.1 y⟩
    exact CFSG.Open.IsElemAbelian.map hc H.subtype
  have hE1 : ((center ↥H).map H.subtype) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ((center ↥H).map H.subtype) = 1 := by simp [h]
    rw [hEcard] at h1
    have hp2le : 2 ≤ p := hp.two_le
    have h1lt : 1 < p ^ e := by
      calc 1 < p := by omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.one_lt.le (by omega)
    omega
  have hN3 : p = 3 → 2 ≤ N := by
    intro hp3
    have h3' : 3 < 3 ^ e := by rwa [hp3] at h3
    have he2 : 2 ≤ e := two_le_e_of_three_lt_three_pow h3'
    omega
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    have hp2le : 2 ≤ p := hp.two_le
    omega
  by_cases hxE : x ∈ (center ↥H).map H.subtype
  · obtain ⟨D, hD, hxD⟩ :=
      exists_not_mem_hypSupp_of_mem_ne_one hW hp hp2 hE hxE hx1
    have hb := hypPart_bounds hW hp hp2 hH heN h3 hD
    have hsup : D ⊔ Subgroup.zpowers x = (center ↥H).map H.subtype :=
      CFSG.LieType.SeitzGeneration.HyperBlocks.sup_zpowers_eq hp hD.1.1 hD.1.2 hxE hxD
    have hfix : fixV D ⊓ fixV (Subgroup.zpowers x) =
        fixV ((center ↥H).map H.subtype) := by
      rw [← FixVLat.fixV_sup_eq, hsup]
    have hbot : hypPart ((center ↥H).map H.subtype) D ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
      unfold hypPart
      rw [inf_assoc, hfix]
      exact commSub_inf_fixV_eq_bot hW hp hp2 hE
    have hMstabX : ∀ y ∈ Subgroup.zpowers x,
        ∀ m ∈ hypPart ((center ↥H).map H.subtype) D,
          y m ∈ hypPart ((center ↥H).map H.subtype) D := by
      intro y hy
      exact stableUnder_hypPart_of_center hD.1.1 y (Subgroup.zpowers_le.mpr hxH hy)
    have hYodd : Odd (Nat.card (Subgroup.zpowers x)) := by
      rw [Nat.card_zpowers, hx]
      exact hp.odd_of_ne_two hp2
    have hcomm : commSub (hypPart ((center ↥H).map H.subtype) D) (Subgroup.zpowers x) =
        hypPart ((center ↥H).map H.subtype) D := by
      have h := (CFSG.Quasithin.B1.coprime_decomp hW hYodd
        (M := hypPart ((center ↥H).map H.subtype) D) hMstabX).1
      rw [hbot, bot_sup_eq] at h
      exact h
    have hle : rk ↥(commSub (hypPart ((center ↥H).map H.subtype) D)
        (Subgroup.zpowers x)) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) :=
      rk_mono (commSub_mono le_top le_rfl)
    have h16 : 16 ≤ p ^ N * dParam p := sixteen_le_pow_mul_dParam hp hp2 hN hN3
    calc 16 ≤ p ^ N * dParam p := h16
      _ ≤ rk ↥(hypPart ((center ↥H).map H.subtype) D) := hb.1
      _ = rk ↥(commSub (hypPart ((center ↥H).map H.subtype) D)
            (Subgroup.zpowers x)) := by rw [hcomm]
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := hle
  · have hb : ∀ D ∈ hypSupp p ((center ↥H).map H.subtype),
        (p - 1) * p ^ (N - 1) * dParam p ≤
          rk ↥(commSub (hypPart ((center ↥H).map H.subtype) D) (Subgroup.zpowers x)) :=
      fun D hD => (hypPart_bounds hW hp hp2 hH heN h3 hD).2 x hxH hx hxE
    have hNle : ∀ D : hyperplanes p ((center ↥H).map H.subtype),
        commSub (hypPart ((center ↥H).map H.subtype) D) (Subgroup.zpowers x) ≤
          hypPart ((center ↥H).map H.subtype) D := by
      intro D
      exact commSub_le_of_invariant (fun y hy =>
        stableUnder_hypPart_of_center D.2.1 y (Subgroup.zpowers_le.mpr hxH hy))
    have hcount := mul_ncard_hypSupp_le_of_commSub hW hp hp2 hE (x := x) hNle hb
    have hfin : (hypSupp p ((center ↥H).map H.subtype)).Finite :=
      (finite_hyperplanes p ((center ↥H).map H.subtype)).subset (fun D hD => hD.1)
    have hk1 : 1 ≤ (hypSupp p ((center ↥H).map H.subtype)).ncard := by
      obtain ⟨D₀, hD₀⟩ := hypSupp_nonempty hW hp hp2 hE hE1
      have h1 : ({D₀} : Set (Subgroup (MulAut W))).ncard = 1 := Set.ncard_singleton _
      have hsub : ({D₀} : Set (Subgroup (MulAut W))) ⊆
          hypSupp p ((center ↥H).map H.subtype) := by
        intro D hD
        rw [Set.mem_singleton_iff] at hD
        rwa [hD]
      calc 1 = ({D₀} : Set (Subgroup (MulAut W))).ncard := h1.symm
        _ ≤ (hypSupp p ((center ↥H).map H.subtype)).ncard := Set.ncard_le_ncard hsub hfin
    have hk3 : p = 3 → 2 ≤ (hypSupp p ((center ↥H).map H.subtype)).ncard := by
      intro hp3
      have h3' : 3 < 3 ^ e := by rwa [hp3] at h3
      have he2 : 2 ≤ e := two_le_e_of_three_lt_three_pow h3'
      exact two_le_ncard_hypSupp_of_two_le_e hW hp hp2 he2 hE hEcard
    have h16 : 16 ≤ (p - 1) * p ^ (N - 1) * dParam p *
        (hypSupp p ((center ↥H).map H.subtype)).ncard :=
      sixteen_le_mul_ncard hp hp2 hN hk1 hk3 hN3
    calc 16 ≤ (p - 1) * p ^ (N - 1) * dParam p *
          (hypSupp p ((center ↥H).map H.subtype)).ncard := h16
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := hcount

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
