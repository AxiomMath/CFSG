module

public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private noncomputable instance s16e_d5_fintypeMulAut [Finite W] : Fintype (MulAut W) := by
  haveI : Fintype W := Fintype.ofFinite W
  haveI : DecidableEq W := Classical.decEq W
  exact Fintype.ofInjective (fun f : MulAut W => (f : W → W))
    (fun _ _ h => MulEquiv.ext (congrFun h))

private lemma s16e_d5_card_L {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) : Nat.card ↥L = 9 := by
  obtain ⟨e⟩ := hL
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := Fin 2 → ZMod 3)), Nat.card_pi]
  simp [ZMod.card]

private lemma s16e_d5_mul_comm {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (x y : ↥L) : x * y = y * x := by
  obtain ⟨e⟩ := hL
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private lemma s16e_d5_mul_comm_coe {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) {x y : MulAut W} (hx : x ∈ L) (hy : y ∈ L) :
    x * y = y * x :=
  congrArg Subtype.val (s16e_d5_mul_comm hL ⟨x, hx⟩ ⟨y, hy⟩)

private lemma s16e_d5_zpowers_eq_of_card_three {K : Subgroup (MulAut W)}
    (hcK : Nat.card ↥K = 3) {x : MulAut W} (hx : x ∈ K) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = K := by
  have hx3 : x ^ 3 = 1 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hcK]
      exact Subgroup.orderOf_dvd_natCard K hx
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) ?_
  rw [Nat.card_zpowers, hxord, hcK]

theorem s16e_d5_fixV_L_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) : fixV L = ⊥ := by
  have hodd : Odd (Nat.card ↥L) := by
    rw [s16e_d5_card_L hL]
    norm_num
  have h := Asc81c.fixV_inf_commSub_eq_bot' hW hodd (Y := L)
  rw [hWL, inf_top_eq] at h
  exact h

theorem s16e_d5_rk_fixV_zpowers (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx3 : x ^ 3 = 1)
    (hrk8 : rk ↥(⊤ : Subgroup W) = 8) (hrk6 : rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6) :
    rk ↥(fixV (Subgroup.zpowers x)) = 2 := by
  have hYdvd : Nat.card ↥(Subgroup.zpowers x) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx3
  have hYodd : Odd (Nat.card ↥(Subgroup.zpowers x)) :=
    Odd.of_dvd_nat (by decide : Odd 3) hYdvd
  have hdec := Asc81c.card_fixV_mul_card_commSub hW hYodd (Y := Subgroup.zpowers x)
  rw [card_eq_two_pow hW (fixV (Subgroup.zpowers x)),
    card_eq_two_pow hW (commSub ⊤ (Subgroup.zpowers x)), hrk6, ← pow_add] at hdec
  have hWcard : Nat.card W = 2 ^ 8 := by
    rw [← Subgroup.card_top, card_eq_two_pow hW (⊤ : Subgroup W), hrk8]
  rw [hWcard] at hdec
  have h : rk ↥(fixV (Subgroup.zpowers x)) + 6 = 8 :=
    Nat.pow_right_injective (le_refl 2) hdec
  omega

theorem s16e_d5_le_commSub (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hfixL : fixV L = ⊥) {K K' : Subgroup (MulAut W)}
    (hK : K ≤ L) (hK' : K' ≤ L) (hcK : Nat.card ↥K = 3) (hcK' : Nat.card ↥K' = 3) (hne : K ≠ K')
    {x : MulAut W} (hx : x ∈ K) (hx1 : x ≠ 1) : fixV K' ≤ commSub ⊤ (Subgroup.zpowers x) := by
  have hzp : Subgroup.zpowers x = K := s16e_d5_zpowers_eq_of_card_three hcK hx hx1
  have hsup_le : K ⊔ K' ≤ L := sup_le hK hK'
  have hlt : K < K ⊔ K' := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hne
    have hK'le : K' ≤ K := by
      have h : K' ≤ K ⊔ K' := le_sup_right
      rwa [← heq] at h
    have hK'eq : K' = K := Subgroup.eq_of_le_of_card_ge hK'le (by rw [hcK', hcK])
    exact hK'eq.symm
  have hcard_sup : Nat.card ↥(K ⊔ K') = 9 := by
    have hdvd9 : Nat.card ↥(K ⊔ K') ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 from by norm_num, ← s16e_d5_card_L hL]
      exact Subgroup.card_dvd_of_le hsup_le
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
    have hltc : 3 < Nat.card ↥(K ⊔ K') := by
      rw [← hcK]
      exact Subgroup.card_lt_of_lt hlt
    interval_cases k
    · rw [hk] at hltc; norm_num at hltc
    · rw [hk] at hltc; norm_num at hltc
    · rw [hk]; norm_num
  have hsup_eq : K ⊔ K' = L := by
    refine Subgroup.eq_of_le_of_card_ge hsup_le ?_
    rw [s16e_d5_card_L hL, hcard_sup]
  have hinf : fixV K' ⊓ fixV K = ⊥ := by
    have hle : fixV K' ⊓ fixV K ≤ fixV L := by
      intro w hw
      intro y hy
      have hy' : y ∈ K ⊔ K' := by
        rw [hsup_eq]
        exact hy
      have hstab : K ⊔ K' ≤ MulAction.stabilizer (MulAut W) w :=
        sup_le
          (fun y hy => by
            rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
            exact hw.2 y hy)
          (fun y hy => by
            rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
            exact hw.1 y hy)
      have h1 := hstab hy'
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1
    rw [hfixL] at hle
    exact le_bot_iff.1 hle
  have hYodd : Odd (Nat.card ↥(Subgroup.zpowers x)) := by
    rw [hzp, hcK]
    norm_num
  have hM : ∀ y ∈ Subgroup.zpowers x, ∀ m ∈ fixV K', y m ∈ fixV K' := by
    intro y hy m hm
    rw [mem_fixV] at hm ⊢
    intro k' hk'
    have hyK : y ∈ K := by
      rw [← hzp]
      exact hy
    have hcomm : k' * y = y * k' := s16e_d5_mul_comm_coe hL (hK' hk') (hK hyK)
    calc k' (y m) = (k' * y) m := by rw [MulAut.mul_apply]
      _ = (y * k') m := by rw [hcomm]
      _ = y (k' m) := by rw [MulAut.mul_apply]
      _ = y m := by rw [hm k' hk']
  obtain ⟨hdec1, -⟩ := B1.coprime_decomp hW hYodd (M := fixV K') hM
  have hinf' : fixV K' ⊓ fixV (Subgroup.zpowers x) = ⊥ := by rw [hzp, hinf]
  rw [hinf', bot_sup_eq] at hdec1
  calc fixV K' = commSub (fixV K') (Subgroup.zpowers x) := hdec1.symm
    _ ≤ commSub ⊤ (Subgroup.zpowers x) := commSub_mono le_top le_rfl

theorem s16e_d5_Z_indep (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hfixL : fixV L = ⊥) {K : Fin 4 → Subgroup (MulAut W)}
    (hK : ∀ i, K i ≤ L) (hcK : ∀ i, Nat.card ↥(K i) = 3) (hinj : Function.Injective K) :
    iSupIndep (fun i => fixV (K i)) := by
  rw [iSupIndep_def]
  intro i
  have hne_bot : K i ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(K i) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcK i] at h1
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne_bot
  have hxK : (a : MulAut W) ∈ K i := a.2
  have hx1 : (a : MulAut W) ≠ 1 := fun h => ha (Subtype.ext h)
  have hzp : Subgroup.zpowers (a : MulAut W) = K i :=
    s16e_d5_zpowers_eq_of_card_three (hcK i) hxK hx1
  have hle : (⨆ (j) (_ : j ≠ i), fixV (K j)) ≤
      commSub ⊤ (Subgroup.zpowers (a : MulAut W)) := by
    refine iSup₂_le ?_
    intro j hj
    exact s16e_d5_le_commSub hW hL hfixL (hK i) (hK j) (hcK i) (hcK j)
      (fun h => hj (hinj h).symm) hxK hx1
  have hdisj : Disjoint (fixV (K i)) (commSub ⊤ (Subgroup.zpowers (a : MulAut W))) := by
    rw [disjoint_iff]
    have hfx : fixV (K i) = fixV (Subgroup.zpowers (a : MulAut W)) := by rw [hzp]
    rw [hfx]
    have hYodd : Odd (Nat.card ↥(Subgroup.zpowers (a : MulAut W))) := by
      rw [hzp, hcK i]
      norm_num
    exact Asc81c.fixV_inf_commSub_eq_bot' hW hYodd (Y := Subgroup.zpowers (a : MulAut W))
  exact Disjoint.mono_right hle hdisj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
