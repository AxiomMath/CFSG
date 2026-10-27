module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4F
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4FAux1
import CFSG.Quasithin.Background.F918J3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

private theorem f5_rk_eq_three_of_three_summands (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {R : Subgroup W} {I : Fin 3 → Subgroup W}
    (hcard : Nat.card ↥R = 2 ^ 9) (hInd : iSupIndep I)
    (hsup : (⊥ ⊔ ⨆ i, I i) = R)
    (hiso : ∀ i, CFSG.Quasithin.H.Pair.IsoMod K (I 0) (I i)) :
    ∀ i, rk ↥(I i) = 3 := by
  have hRrk : rk ↥R = 9 := by
    have h2 : 2 ^ 9 = 2 ^ rk ↥R := by
      rw [← hcard]
      exact card_eq_two_pow hW R
    exact ((Nat.pow_right_injective (by norm_num : 2 ≤ 2)) h2).symm
  have hIR : (⨆ i : Fin 3, I i) = R := by rw [← hsup, bot_sup_eq]
  have hsumR : rk ↥R = rk ↥(I 0) + rk ↥(I 1) + rk ↥(I 2) := by
    have h1 := rk_iSup_biSup_eq_sum I hInd Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset (Fin 3)), I i) = R := by
      rw [show (⨆ i ∈ (Finset.univ : Finset (Fin 3)), I i) = ⨆ i, I i from
        iSup_congr fun i => iSup_pos (Finset.mem_univ i), hIR]
    rw [h2, Fin.sum_univ_three] at h1
    exact h1
  have hrkEq : ∀ i, rk ↥(I i) = rk ↥(I 0) := by
    intro i
    obtain ⟨e, -⟩ := hiso i
    unfold rk
    rw [(Nat.card_congr e.toEquiv).symm]
  have hrk0 : rk ↥(I 0) = 3 := by
    have h1 := hrkEq 1
    have h2 := hrkEq 2
    rw [h1, h2, hRrk] at hsumR
    omega
  exact fun i => (hrkEq i).trans hrk0

omit [Finite W] in
private theorem f5_exists_moved_on_summands {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    {I : Fin 3 → Subgroup W} (hL3 : IsL3 ↥K 1) (hirr : IsIrrOn (K ⊔ K') R ⊥)
    (hKnt : ¬ ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r = r)
    {s : MulAut W} (hs : s ∈ K) (hs2 : orderOf s = 2)
    (hIstable : ∀ i, StableUnder K (I i))
    (hiso : ∀ i, CFSG.Quasithin.H.Pair.IsoMod K (I 0) (I i))
    (hsup : (⊥ ⊔ ⨆ i, I i) = R) :
    ∀ i, ∃ m ∈ I i, s m ≠ m := by
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    omega
  have hKRstable : StableUnder K R :=
    fun k hk r hr => hirr.2.1 k (Subgroup.mem_sup_left hk) r hr
  have hKR : K ≤ stabSub R := f4f_le_stabSub hKRstable
  have hKnotCent : ¬ K ≤ centSub R := by
    intro hle
    exact hKnt fun k hk r hr => mem_centSub.mp (hle hk) r hr
  have hfaithR : K ⊓ centSub R = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup (s134b_isSimpleGroup_of_isL3 hL3) hKR hKnotCent
  have hsNotCent : s ∉ centSub R := by
    intro hsc
    have hmem : s ∈ K ⊓ centSub R := ⟨hs, hsc⟩
    rw [hfaithR, Subgroup.mem_bot] at hmem
    exact hs1 hmem
  have key : ∀ {A B : Subgroup W}, CFSG.Quasithin.H.Pair.IsoMod K A B →
      StableUnder K A → (∀ a ∈ A, s a = a) → ∀ b ∈ B, s b = b := by
    intro A B hAB hKA hA b hb
    obtain ⟨e, he⟩ := hAB
    let a : ↥A := e.symm ⟨b, hb⟩
    have hmem : s (a : W) ∈ A := hKA s hs (a : W) a.2
    have h1 : (e ⟨s (a : W), hmem⟩ : W) = s (e a) := he s hs a hmem
    have h2 : (⟨s (a : W), hmem⟩ : ↥A) = a := Subtype.ext (hA (a : W) a.2)
    have h3 : (e a : W) = b := congrArg Subtype.val (MulEquiv.apply_symm_apply e ⟨b, hb⟩)
    rw [h2] at h1
    rw [← h3]
    exact h1.symm
  intro i
  by_contra h
  push Not at h
  have hI0 : ∀ a ∈ I 0, s a = a :=
    key (CFSG.Quasithin.H.Pair.IsoMod.symm (hIstable 0) (hiso i)) (hIstable i) h
  have hAll : ∀ j, ∀ m ∈ I j, s m = m := fun j =>
    key (hiso j) (hIstable 0) hI0
  have hRfix : R ≤ fixV (Subgroup.zpowers s) := by
    rw [← hsup, bot_sup_eq]
    exact iSup_le fun j => fun m hm => mem_fixV_zpowers_iff.mpr (hAll j m hm)
  exact hsNotCent (mem_centSub.mpr fun r hr => mem_fixV_zpowers_iff.mp (hRfix hr))

theorem rk_commSub_zpowers_eq_one (hW : ∀ w : W, w ^ 2 = 1) {s : MulAut W} (hs : s ^ 2 = 1)
    {M : Subgroup W} (hM : ∀ m ∈ M, s m ∈ M) (hrk : rk ↥M = 3) (hnt : ∃ m ∈ M, s m ≠ m) :
    rk ↥(commSub M (Subgroup.zpowers s)) = 1 := by
  have hss : ∀ u : W, s (s u) = u := fun u => by
    rw [← MulAut.mul_apply, (by simpa [pow_two] using hs : s * s = 1), MulAut.one_apply]
  have hsM : s ∈ stabSub M := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 : s (s u) ∈ M := hM (s u) hu
      rwa [hss u] at h1
    · exact hM u
  have hstab : ∀ x ∈ Subgroup.zpowers s, ∀ w ∈ M, x w ∈ M := by
    intro x hx w hw
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr hsM hx) w).mpr hw
  have hle : commSub M (Subgroup.zpowers s) ≤ M ⊓ fixV (Subgroup.zpowers s) :=
    commSub_zpowers_le_inf_fixV hW hs hstab
  have hadd : rk ↥(commSub M (Subgroup.zpowers s)) +
      rk ↥(M ⊓ fixV (Subgroup.zpowers s)) = rk ↥M := rk_commSub_add_rk_inf_fixV hstab
  have hmono : rk ↥(commSub M (Subgroup.zpowers s)) ≤ rk ↥(M ⊓ fixV (Subgroup.zpowers s)) :=
    rk_mono hle
  have hne : commSub M (Subgroup.zpowers s) ≠ ⊥ := by
    intro hbot
    obtain ⟨m, hm, hsm⟩ := hnt
    have hmem : s m * m⁻¹ ∈ commSub M (Subgroup.zpowers s) :=
      Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, m, hm, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hsm hmem
  have hpos : 0 < rk ↥(commSub M (Subgroup.zpowers s)) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hne ((rk_eq_zero_iff hW).mp h0)
  rw [hrk] at hadd
  omega

private theorem f5_rk_commSub_eq_three {K : Subgroup (MulAut W)} {R : Subgroup W}
    {I : Fin 3 → Subgroup W} {s : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hs : s ∈ K)
    (hs2 : s ^ 2 = 1) (hIstable : ∀ i, StableUnder K (I i))
    (hrkI : ∀ i, rk ↥(I i) = 3) (hnt : ∀ i, ∃ m ∈ I i, s m ≠ m)
    (hInd : iSupIndep I) (hsup : (⊥ ⊔ ⨆ i, I i) = R) :
    rk ↥(commSub R (Subgroup.zpowers s)) = 3 := by
  have hIinv : ∀ i, ∀ x ∈ Subgroup.zpowers s, ∀ u ∈ I i, x u ∈ I i := by
    intro i x hx u hu
    exact hIstable i x (Subgroup.zpowers_le.mpr hs hx) u hu
  have hc0 : rk ↥(commSub (I 0) (Subgroup.zpowers s)) = 1 :=
    rk_commSub_zpowers_eq_one hW hs2
      (fun m hm => hIinv 0 s (Subgroup.mem_zpowers s) m hm) (hrkI 0) (hnt 0)
  have hc1 : rk ↥(commSub (I 1) (Subgroup.zpowers s)) = 1 :=
    rk_commSub_zpowers_eq_one hW hs2
      (fun m hm => hIinv 1 s (Subgroup.mem_zpowers s) m hm) (hrkI 1) (hnt 1)
  have hc2 : rk ↥(commSub (I 2) (Subgroup.zpowers s)) = 1 :=
    rk_commSub_zpowers_eq_one hW hs2
      (fun m hm => hIinv 2 s (Subgroup.mem_zpowers s) m hm) (hrkI 2) (hnt 2)
  have hIR : (⨆ i : Fin 3, I i) = R := by rw [← hsup, bot_sup_eq]
  have h1 := rk_commSub_iSup I hInd hIinv
  rw [hIR, Fin.sum_univ_three, hc0, hc1, hc2] at h1
  exact h1

theorem rk_commSub_zpowers_eq_three (hW : ∀ w : W, w ^ 2 = 1) {K K' : Subgroup (MulAut W)}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hL3 : IsL3 ↥K 1) (hL3' : IsL3 ↥K' 1)
    {R : Subgroup W} (hcard : Nat.card ↥R = 2 ^ 9) (hirr : IsIrrOn (K ⊔ K') R ⊥)
    (hKnt : ¬ ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r = r)
    (hK'nt : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r)
    {s : MulAut W} (hs : s ∈ K) (hs2 : orderOf s = 2) :
    rk ↥(commSub R (Subgroup.zpowers s)) = 3 := by
  obtain ⟨I, hBN, hind, hsup, hiso⟩ :=
    s134b_three_summands hW hKK' hL3 hL3' hcard hirr hKnt hK'nt
  have hIstable : ∀ i, StableUnder K (I i) := by
    intro i
    obtain ⟨F, hF, hFfin, hFcard, hReal⟩ := hBN i
    obtain ⟨π, hπ⟩ := hReal
    intro k hk u hu
    exact (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).U_inv ⟨k, hk⟩ u hu
  have hInd : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff_inf_le]
    simpa [bot_sup_eq] using hind i
  have hs2' : s ^ 2 = 1 := by
    rw [← hs2]
    exact pow_orderOf_eq_one s
  have hrkI := f5_rk_eq_three_of_three_summands hW hcard hInd hsup hiso
  have hnt := f5_exists_moved_on_summands hL3 hirr hKnt hs hs2 hIstable hiso hsup
  exact f5_rk_commSub_eq_three hW hs hs2' hIstable hrkI hnt hInd hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
