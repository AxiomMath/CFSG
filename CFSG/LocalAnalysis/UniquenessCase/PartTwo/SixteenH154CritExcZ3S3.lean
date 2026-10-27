module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_mem_fixV_zpowers_iff {W : Type} [CommGroup W] (g : MulAut W) (v : W) :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h x hx => ?_⟩
  exact MulAction.mem_stabilizer_iff.mp
    ((Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)) hx)

private theorem s16h_card_eq_one_or_64_of_dvd_and_mod {N : ℕ} (hdvd : N ∣ 64)
    (hmod : 9 ∣ N - 1) : N = 1 ∨ N = 64 := by
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  have hdvd' : N ∣ 2 ^ 6 := by rw [← h64]; exact hdvd
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  subst hj
  interval_cases j
  · left; norm_num
  · exact absurd hmod (by norm_num)
  · exact absurd hmod (by norm_num)
  · exact absurd hmod (by norm_num)
  · exact absurd hmod (by norm_num)
  · exact absurd hmod (by norm_num)
  · right; norm_num

private theorem s16h_fixV_zpowers_eq_bot_of_mem {W : Type} [CommGroup W] [Finite W]
    {l x : MulAut W} (hl : orderOf l = 3) (hfpf : ∀ w : W, l w = w → w = 1)
    {S : Subgroup (MulAut W)} (hS3 : IsPGroup 3 S)
    (hS : ∀ y ∈ S, y ^ 3 = 1 → y ∈ Subgroup.zpowers l)
    (hx : x ∈ S) (hx1 : x ≠ 1) : fixV (Subgroup.zpowers x) = ⊥ := by
  obtain ⟨k, hk⟩ := hS3 ⟨x, hx⟩
  have hcoe : orderOf x = orderOf (⟨x, hx⟩ : ↥S) :=
    Subgroup.orderOf_coe (H := S) (⟨x, hx⟩ : ↥S)
  have hdvd : orderOf x ∣ 3 ^ k := by
    rw [hcoe]
    exact orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at ha
      exact absurd (orderOf_eq_one_iff.mp ha) hx1
    · exact h
  set y : MulAut W := x ^ (3 ^ (a - 1)) with hy
  have hyS : y ∈ S := S.pow_mem hx _
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← pow_mul, show 3 ^ (a - 1) * 3 = 3 ^ a by
      rw [← pow_succ, Nat.sub_add_cancel ha1], ← ha, pow_orderOf_eq_one]
  have hy_l : y ∈ Subgroup.zpowers l := hS y hyS hy3
  have hy_dvd : orderOf y ∣ 3 := hl ▸ orderOf_dvd_of_mem_zpowers hy_l
  have hy_ne : y ≠ 1 := by
    intro hy1
    have hdvd' : orderOf x ∣ 3 ^ (a - 1) := by
      rw [orderOf_dvd_iff_pow_eq_one, ← hy]
      exact hy1
    rw [ha] at hdvd'
    have hlt : 3 ^ (a - 1) < 3 ^ a := by
      rw [← Nat.sub_add_cancel ha1]
      exact Nat.pow_lt_pow_succ (by norm_num : 1 < 3)
    exact absurd (Nat.le_of_dvd (by positivity) hdvd') (not_le.mpr hlt)
  have hy_ord_ne : orderOf y ≠ 1 := by simpa [orderOf_eq_one_iff] using hy_ne
  have hy_ord : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hy_dvd with h | h
    · exact absurd h hy_ord_ne
    · exact h
  have hzy : Subgroup.zpowers y = Subgroup.zpowers l := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy_l) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hy_ord, hl]
  have hly : l ∈ Subgroup.zpowers y := hzy ▸ Subgroup.mem_zpowers l
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hvx : x v = v := (s16h_mem_fixV_zpowers_iff x v).mp hv
  have hvy : y v = v := by
    have hpow : ∀ n : ℕ, (x ^ n) v = v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hvx]
    rw [hy]
    exact hpow _
  have hlv : l v = v :=
    smul_eq_self_of_mem_zpowers hly (show y • v = v from hvy)
  exact hfpf v hlv

theorem s16h_le_zpowers_of_torus {W : Type} [CommGroup W] [Finite W] (hcard : Nat.card W = 64)
    {l : MulAut W} (hl : orderOf l = 3) (hfpf : ∀ w : W, l w = w → w = 1)
    {S D : Subgroup (MulAut W)} (hS3 : IsPGroup 3 S) (hS : ∀ y ∈ S, y ^ 3 = 1 → y ∈ zpowers l)
    (hD : IsElemAbelian 3 D) (hD27 : 27 ≤ Nat.card ↥D)
    (hDS : D ≤ normalizer (S : Set (MulAut W))) : S ≤ zpowers l := by
  have hfix : ∀ x ∈ S, x ≠ 1 → fixV (Subgroup.zpowers x) = ⊥ :=
    fun x hx hx1 => s16h_fixV_zpowers_eq_bot_of_mem hl hfpf hS3 hS hx hx1
  have hSdvd63 : Nat.card ↥S ∣ 63 := by
    have hU : ∀ x ∈ S, ∀ u ∈ (⊤ : Subgroup W), x u ∈ (⊤ : Subgroup W) := by simp
    have hR : ∀ x ∈ S, x ≠ 1 →
        Nat.card ↥((⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers x)) = 1 := by
      intro x hx hx1
      rw [top_inf_eq, hfix x hx hx1, Subgroup.card_bot]
    have h := s16h_card_dvd_sub_of_fix_card (R := S) (U := (⊤ : Subgroup W)) (c := 1) hU hR
    simpa [Subgroup.card_top, hcard] using h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3) (G := ↥S)).mp (hS3 : IsPGroup 3 ↥S)
  have hSdvd9 : Nat.card ↥S ∣ 9 := by
    have hcop : Nat.Coprime (3 ^ k) 7 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero]; norm_num
      · rw [Nat.coprime_pow_left_iff hkpos 3 7]; norm_num
    have h2 : 3 ^ k ∣ 3 ^ 2 * 7 := by
      rw [← hk]
      simpa [show (3 : ℕ) ^ 2 * 7 = 63 by norm_num] using hSdvd63
    have h1 : 3 ^ k ∣ 3 ^ 2 := hcop.dvd_of_dvd_mul_right h2
    rw [hk]
    simpa using h1
  rcases eq_or_ne (Nat.card ↥S) 9 with hS9 | hS9
  · exfalso
    have hScyc : IsCyclic ↥S := by
      by_contra hnc
      have hexp : Monoid.exponent ↥S = 3 :=
        (not_isCyclic_iff_exponent_eq_prime Nat.prime_three (by rw [hS9]; norm_num)).mp hnc
      have hle : S ≤ Subgroup.zpowers l := fun y hy =>
        hS y hy (by
          have h3 : (⟨y, hy⟩ : ↥S) ^ 3 = 1 := by
            rw [← hexp]
            exact Monoid.pow_exponent_eq_one _
          simpa using h3)
      have hcard_le := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hl, hS9] at hcard_le
      omega
    have haut : Nat.card (MulAut ↥S) = 6 := by
      rw [IsCyclic.card_mulAut, hS9, show (9 : ℕ) = 3 ^ 2 by norm_num,
        Nat.totient_prime_pow Nat.prime_three (by norm_num : 0 < 2)]
      norm_num
    let ψ : ↥D →* Subgroup.normalizer (S : Set (MulAut W)) :=
      { toFun := fun d => ⟨(d : MulAut W), hDS d.2⟩
        map_one' := by ext; rfl
        map_mul' := fun a b => by ext; rfl }
    let φ : ↥D →* MulAut ↥S := (Subgroup.normalizerMonoidHom (H := S)).comp ψ
    have hker_iff : ∀ d : ↥D,
        d ∈ φ.ker ↔ (d : MulAut W) ∈ Subgroup.centralizer (S : Set (MulAut W)) := by
      intro d
      rw [MonoidHom.mem_ker]
      change (Subgroup.normalizerMonoidHom (H := S)) (ψ d) = 1 ↔
        (d : MulAut W) ∈ Subgroup.centralizer (S : Set (MulAut W))
      constructor
      · intro hd
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
          Subgroup.mem_subgroupOf] at hd
        change (d : MulAut W) ∈ Subgroup.centralizer (S : Set (MulAut W)) at hd
        exact hd
      · intro hd
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        change (d : MulAut W) ∈ Subgroup.centralizer (S : Set (MulAut W))
        exact hd
    set E : Subgroup (MulAut W) := D ⊓ Subgroup.centralizer (S : Set (MulAut W)) with hEdef
    have hEleD : E ≤ D := by rw [hEdef]; exact inf_le_left
    have hEcen : E ≤ Subgroup.centralizer (S : Set (MulAut W)) := by
      rw [hEdef]; exact inf_le_right
    have hEeq : E = (φ.ker).map D.subtype := by
      rw [hEdef]
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map]
        refine ⟨⟨x, (Subgroup.mem_inf.mp hx).1⟩, ?_, rfl⟩
        exact (hker_iff ⟨x, (Subgroup.mem_inf.mp hx).1⟩).mpr (Subgroup.mem_inf.mp hx).2
      · rintro ⟨d, hd, rfl⟩
        exact Subgroup.mem_inf.mpr ⟨d.2, (hker_iff d).mp hd⟩
    have hEcard : Nat.card ↥E = Nat.card φ.ker := by
      rw [hEeq]
      exact Subgroup.card_subtype D φ.ker
    have hrangeD : Nat.card φ.range ∣ Nat.card ↥D := Subgroup.card_range_dvd φ
    have hrangeAut : Nat.card φ.range ∣ Nat.card (MulAut ↥S) := by
      have h := Subgroup.card_dvd_of_le (show φ.range ≤ (⊤ : Subgroup (MulAut ↥S)) from le_top)
      simpa [Subgroup.card_top] using h
    have hrange6 : Nat.card φ.range ∣ 6 := by rw [haut] at hrangeAut; exact hrangeAut
    have hDpgroup : IsPGroup 3 ↥D := fun x =>
      ⟨1, Subtype.ext (by simpa using hD.2 x.1 x.2)⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := ↥D)).mp hDpgroup
    have hrange3pow : Nat.card φ.range ∣ 3 ^ m := by rw [← hm]; exact hrangeD
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hrange3pow
    have hrange_dvd3 : Nat.card φ.range ∣ 3 := by
      have hrj : 3 ^ j ∣ 6 := by rw [← hj]; exact hrange6
      have hjle1 : j ≤ 1 := by
        by_contra h
        have hj2 : 2 ≤ j := by omega
        have h9dvd : 9 ∣ 3 ^ j := by
          have h := pow_dvd_pow 3 hj2
          simpa using h
        exact absurd (dvd_trans h9dvd hrj) (by norm_num)
      exact hj.symm ▸ pow_dvd_pow 3 hjle1
    have hprod : 27 ≤ Nat.card φ.ker * Nat.card φ.range := by
      rw [Subgroup.card_ker_mul_card_range φ]
      exact hD27
    have hker_ge : 9 ≤ Nat.card φ.ker := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hrange_dvd3 with h1 | h3
      · rw [h1, mul_one] at hprod; omega
      · rw [h3] at hprod; omega
    have hcardE : 3 ^ 2 ≤ Nat.card ↥E := by
      rw [hEcard]; simpa using hker_ge
    have hEabel : IsElemAbelian 3 E := by
      refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => hD.2 x (hEleD hx)⟩
      apply Subtype.ext
      simpa using hD.1.is_comm.comm ⟨a.1, hEleD a.2⟩ ⟨b.1, hEleD b.2⟩
    have hEfix : ∀ x ∈ E, x ≠ 1 → fixV (Subgroup.zpowers x) = ⊥ := by
      intro h hhE hh1
      set U : Subgroup W := fixV (Subgroup.zpowers h) with hUdef
      have hUinv : ∀ x ∈ S, ∀ u ∈ U, x u ∈ U := by
        intro x hxS u hu
        rw [hUdef] at hu ⊢
        rw [s16h_mem_fixV_zpowers_iff] at hu ⊢
        have hcomm : h * x = x * h :=
          ((Subgroup.mem_centralizer_iff.mp (hEcen hhE)) x hxS).symm
        rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hu]
      have hUmod : 9 ∣ Nat.card ↥U - 1 := by
        have hR : ∀ x ∈ S, x ≠ 1 → Nat.card ↥(U ⊓ fixV (Subgroup.zpowers x)) = 1 := by
          intro x hxS hx1
          have hle : U ⊓ fixV (Subgroup.zpowers x) ≤ (⊥ : Subgroup W) := by
            rw [hfix x hxS hx1]
            exact inf_le_right
          rw [le_bot_iff.mp hle, Subgroup.card_bot]
        have h := s16h_card_dvd_sub_of_fix_card (R := S) (U := U) (c := 1) hUinv hR
        rw [hS9] at h
        exact h
      have hUdvd : Nat.card ↥U ∣ 64 := by
        have h := Subgroup.card_dvd_of_le (show U ≤ (⊤ : Subgroup W) from le_top)
        simpa [Subgroup.card_top, hcard] using h
      rcases s16h_card_eq_one_or_64_of_dvd_and_mod hUdvd hUmod with hU1 | hU64
      · exact Subgroup.eq_bot_of_card_eq U hU1
      · exfalso
        have hUtop : U = ⊤ := Subgroup.eq_top_of_card_eq U (hU64.trans hcard.symm)
        apply hh1
        ext v
        have hv : v ∈ fixV (Subgroup.zpowers h) := by
          rw [← hUdef, hUtop]; exact Subgroup.mem_top v
        exact (s16h_mem_fixV_zpowers_iff h v).mp hv
    have hbot_top : (⊥ : Subgroup W) = ⊤ :=
      s16h_eq_top_of_fixV_le (p := 3) Nat.prime_three (by rw [hcard]; norm_num)
        hEabel hcardE (F := ⊥) (fun x hxE hx1 => by rw [hEfix x hxE hx1])
    have hW1 : Nat.card W = 1 := by
      have h := congrArg (fun H : Subgroup W => Nat.card ↥H) hbot_top
      have h' : (1 : ℕ) = Nat.card W := by
        simpa [Subgroup.card_bot, Subgroup.card_top] using h
      omega
    omega
  · have hSdvd3 : Nat.card ↥S ∣ 3 := by
      have hk2 : k ≤ 2 := by
        have h : 3 ^ k ∣ 3 ^ 2 := by
          have h' : 3 ^ k ∣ 9 := by rw [← hk]; exact hSdvd9
          simpa using h'
        exact (Nat.pow_dvd_pow_iff_le_right (show 1 < 3 by norm_num)).mp h
      have hklt : k < 2 := by
        rcases lt_or_ge k 2 with h | h
        · exact h
        · exfalso
          have hk2' : k = 2 := by omega
          exact hS9 (by rw [hk, hk2']; norm_num)
      rw [hk]
      exact pow_dvd_pow 3 (show k ≤ 1 by omega)
    intro y hy
    refine hS y hy ?_
    have hdvd : orderOf (⟨y, hy⟩ : ↥S) ∣ Nat.card ↥S := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans hdvd hSdvd3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
