module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectTransfer
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_im_iSup_ne {U C : Subgroup W} {k : ℕ} {J : Fin k → Subgroup W}
    (hJU : ∀ i, J i ≤ U) (i : Fin k) :
    w1369_im U C (⨆ (j : Fin k) (_ : j ≠ i), J j) =
      ⨆ (j : Fin k) (_ : j ≠ i), w1369_im U C (J j) := by
  rw [iSup_subtype' (p := fun j : Fin k => j ≠ i) (f := fun j _ => J j),
    iSup_subtype' (p := fun j : Fin k => j ≠ i)
      (f := fun j _ => w1369_im U C (J j))]
  exact w1369_im_iSup (fun x : {j : Fin k // j ≠ i} => hJU x.1)

theorem w1369_hind_im {U C : Subgroup W} {k : ℕ} {J : Fin k → Subgroup W}
    (hCJ : ∀ i, C ≤ J i) (hJU : ∀ i, J i ≤ U)
    (hind : ∀ i, J i ⊓ (C ⊔ ⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ C) :
    ∀ i, w1369_im U C (J i) ⊓ (⨆ (j : Fin k) (_ : j ≠ i), w1369_im U C (J j)) = ⊥ := by
  intro i
  apply le_bot_iff.mp
  have hCU : C ≤ U := (hCJ i).trans (hJU i)
  have hU' : (⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ U := iSup₂_le fun j _ => hJU j
  have hpre : w1369_pre U C (w1369_im U C (J i) ⊓
      (⨆ (j : Fin k) (_ : j ≠ i), w1369_im U C (J j))) ≤ C := by
    rw [w1369_pre_inf, w1369_pre_im (hCJ i) (hJU i),
      ← w1369_im_iSup_ne hJU i, w1369_pre_im' hCU hU', sup_comm]
    exact hind i
  calc w1369_im U C (J i) ⊓ (⨆ (j : Fin k) (_ : j ≠ i), w1369_im U C (J j))
      = w1369_im U C (w1369_pre U C (w1369_im U C (J i) ⊓
          (⨆ (j : Fin k) (_ : j ≠ i), w1369_im U C (J j)))) :=
        (w1369_im_pre U C _).symm
    _ ≤ w1369_im U C C := w1369_im_mono hpre
    _ = ⊥ := w1369_im_C U C

theorem w1369_alt_irr {U C : Subgroup W} (hCU : C ≤ U) {Λ X : Subgroup (MulAut W)}
    (hΛ : StabPair Λ U C) (hX : StabPair X U C)
    (h : ∀ N : Subgroup (Sect U C), StableUnder (secSub U C Λ) N →
      StableUnder (secSub U C X) N → N = ⊥ ∨ N = ⊤) :
    ∀ M : Subgroup W, C ≤ M → M ≤ U → StableUnder Λ M → StableUnder X M → M = C ∨ M = U := by
  intro M hCM hMU hΛM hXM
  rcases h _ (w1369_stable_im hΛ hΛM) (w1369_stable_im hX hXM) with h0 | h1
  · left
    rw [← w1369_pre_im hCM hMU, h0, w1369_pre_bot hCU]
  · right
    rw [← w1369_pre_im hCM hMU, h1, ← w1369_im_top U C, w1369_pre_im hCU le_rfl]

theorem w1369_alt_notcent {U C : Subgroup W} (hCU : C ≤ U) {Λ X : Subgroup (MulAut W)}
    (hΛ : StabPair Λ U C) (hX : StabPair X U C)
    (h : ∀ N : Subgroup (Sect U C), StableUnder (secSub U C Λ) N → N ≠ ⊥ →
      ∃ x ∈ secSub U C X, ∃ n ∈ N, x n ≠ n) :
    ∀ M : Subgroup W, C < M → M ≤ U → StableUnder Λ M → ¬ commSub M X ≤ C := by
  intro M hCM hMU hΛM hle
  have hCU : C ≤ U := (le_of_lt hCM).trans hMU
  have hNstable : StableUnder (secSub U C Λ) (w1369_im U C M) := w1369_stable_im hΛ hΛM
  have hNne : w1369_im U C M ≠ ⊥ := by
    intro hbot
    have hpre := w1369_pre_im (le_of_lt hCM) hMU
    rw [hbot, w1369_pre_bot hCU] at hpre
    exact (not_le_of_gt hCM) (le_of_eq hpre.symm)
  obtain ⟨x, hx, n, hnN, hxn⟩ := h (w1369_im U C M) hNstable hNne
  obtain ⟨a, ha, hax⟩ := (w1369_mem_secSub_iff hX).mp hx
  rw [w1369_im, Subgroup.mem_map] at hnN
  obtain ⟨m, hm, hmn⟩ := hnN
  have hmM : (m : W) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have hmem : a (m : W) * (m : W)⁻¹ ∈ commSub M X :=
    Subgroup.subset_closure ⟨a, ha, (m : W), hmM, rfl⟩
  have hCmem : a (m : W) * (m : W)⁻¹ ∈ C := hle hmem
  apply hxn
  rw [← hax, ← hmn, QuotientGroup.mk'_apply, secAut_mk]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simpa [div_eq_mul_inv] using hCmem

private theorem w1369_secAut_eq_secHom {U C : Subgroup W} {X : Subgroup (MulAut W)}
    (hXU : X ≤ stabSub U) (hXC : X ≤ stabSub C) {a : MulAut W} (ha : a ∈ X) :
    secAut U C a (fun u hu => (mem_stabSub.mp (hXU ha) u).2 hu)
        (fun z hz => (mem_stabSub.mp (hXC ha) z).2 hz) =
      B5.secHom X hXU hXC ⟨a, ha⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H v =>
    rw [secAut_mk, B5.secHom_mk]

theorem w1369_alt_odd {U C : Subgroup W} {X : Subgroup (MulAut W)} (hX : StabPair X U C)
    (h : ∃ x ∈ secSub U C X, orderOf x = 7 ∧ ∀ q : Sect U C, x q = q → q = 1) :
    ∃ x ∈ X, Odd (orderOf x) ∧ ∀ u ∈ U, x u * u⁻¹ ∈ C → u ∈ C := by
  obtain ⟨xbar, hxbar, hxbar7, hfix⟩ := h
  obtain ⟨a, ha, haeq⟩ := (w1369_mem_secSub_iff hX).mp hxbar
  have hXU : X ≤ stabSub U := fun g hg => by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by simpa using inv_mem_of_forall_mem g (hX g hg).1 (g u) hu,
      (hX g hg).1 u⟩
  have hXC : X ≤ stabSub C := fun g hg => by
    rw [mem_stabSub]
    intro z
    exact ⟨fun hz => by simpa using inv_mem_of_forall_mem g (hX g hg).2 (g z) hz,
      (hX g hg).2 z⟩
  let n := orderOf a
  have hn : n ≠ 0 := (orderOf_pos a).ne'
  have hpow : xbar ^ n = 1 := by
    rw [← haeq, w1369_secAut_eq_secHom hXU hXC ha, ← map_pow]
    have hpowx : (⟨a, ha⟩ : ↥X) ^ n = 1 := by
      apply Subtype.ext
      change a ^ n = (1 : MulAut W)
      rw [pow_orderOf_eq_one a]
    rw [hpowx, map_one]
  have h7n : 7 ∣ n := by
    have hdvd : orderOf xbar ∣ n := orderOf_dvd_of_pow_eq_one hpow
    rwa [hxbar7] at hdvd
  let m := ordCompl[7] n
  have hm_pos : 0 < m := Nat.ordCompl_pos 7 hn
  have hm_dvd : m ∣ n := Nat.ordCompl_dvd n 7
  have hcop : Nat.Coprime m 7 :=
    (Nat.coprime_ordCompl (by norm_num : Nat.Prime 7) hn).symm
  have hnm : ordProj[7] n * m = n := Nat.ordProj_mul_ordCompl_eq_self n 7
  have hdiv : n / m = ordProj[7] n := by
    conv_lhs => rw [← hnm]
    exact Nat.mul_div_left _ hm_pos
  have hord : orderOf (a ^ m) = ordProj[7] n := by
    rw [orderOf_pow_of_dvd hm_pos.ne' hm_dvd]
    exact hdiv
  have hodd : Odd (orderOf (a ^ m)) := by
    rw [hord]
    exact Odd.pow (show Odd 7 by norm_num)
  refine ⟨a ^ m, X.pow_mem ha m, hodd, ?_⟩
  intro u hu huC
  have hsq : secAut U C (a ^ m) (hX (a ^ m) (X.pow_mem ha m)).1
      (hX (a ^ m) (X.pow_mem ha m)).2 (QuotientGroup.mk ⟨u, hu⟩) =
      QuotientGroup.mk ⟨u, hu⟩ := by
    rw [secAut_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using huC
  have hfq : (xbar ^ m) (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
    rw [← haeq, w1369_secAut_eq_secHom hXU hXC ha, ← map_pow,
      show (⟨a, ha⟩ : ↥X) ^ m = ⟨a ^ m, X.pow_mem ha m⟩ from Subtype.ext rfl]
    rw [← w1369_secAut_eq_secHom hXU hXC (X.pow_mem ha m)]
    exact hsq
  have hmem : xbar ∈ Subgroup.zpowers (xbar ^ m) := by
    rw [mem_zpowers_pow_iff, hxbar7]
    exact hcop
  have hxq : xbar (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
    have hqmem : QuotientGroup.mk ⟨u, hu⟩ ∈ fixV (Subgroup.zpowers (xbar ^ m)) :=
      (mem_fixV_zpowers (xbar ^ m) (QuotientGroup.mk ⟨u, hu⟩)).mpr hfq
    exact hqmem xbar hmem
  have hq1 : ((⟨u, hu⟩ : ↥U) : Sect U C) = 1 := hfix _ hxq
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := C.subgroupOf U) (⟨u, hu⟩ : ↥U)).mp hq1)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
