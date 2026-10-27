module

public import CFSG.Quasithin.Background.SmithB45Exc3A7Nine
public import CFSG.Quasithin.Background.SmithB45Exc3A7Gen
public import CFSG.Quasithin.Background.SmithB45Dich
public import CFSG.Quasithin.Background.SmithB42HatA6Off
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Main
public import CFSG.Quasithin.Background.SmithB45Exc3A7Out

public section

namespace CFSG.Quasithin

namespace B45Exc3A7

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_inverts {L : Subgroup (MulAut W)} (hcard : Nat.card W = 2 ^ 12)
    {A : Subgroup (MulAut W)} (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAe : IsElemAbelian2 A) (hA8 : Nat.card A ≤ 8) (hidx : (fixV A).index ≤ Nat.card A ^ 2)
    {zL : ↥L} (hcen : Subgroup.center ↥L = Subgroup.zpowers zL) (h3 : (zL : MulAut W) ^ 3 = 1)
    (hz1 : (zL : MulAut W) ≠ 1) (hfp : ∀ v : W, (zL : MulAut W) v = v → v = 1)
    {t : MulAut W} (htA : t ∈ A) (htz : t * zL ≠ zL * t) : False := by
  classical
  set z : MulAut W := (zL : MulAut W) with hzdef
  have ht2 : t * z = z * z * t :=
    (HatA6.conj_z_cases hcen h3 hz1 (hAN htA)).resolve_left htz
  have htz' : ∀ v, t (z v) = z (z (t v)) := fun v => congrArg (fun y : MulAut W => y v) ht2
  set B₀ := A ⊓ Subgroup.centralizer ({z} : Set (MulAut W)) with hB₀
  have hB₀B : B₀ ≤ A := inf_le_left
  have hbt : ∀ b ∈ A, b ∉ B₀ → b * t ∈ B₀ := by
    intro b hb hb0
    have hbz : b * z = z * z * b := by
      rcases HatA6.conj_z_cases hcen h3 hz1 (hAN hb) with h | h
      · exact absurd ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 h⟩ hb0
      · exact h
    refine ⟨A.mul_mem hb htA, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hz3 : z * z * z = 1 := by rw [← pow_three']; exact h3
    calc b * t * z = b * (t * z) := by group
      _ = b * (z * z * t) := by rw [ht2]
      _ = (b * z) * z * t := by group
      _ = (z * z * b) * z * t := by rw [hbz]
      _ = z * z * (b * z) * t := by group
      _ = z * z * (z * z * b) * t := by rw [hbz]
      _ = z * (z * z * z) * b * t := by group
      _ = z * (b * t) := by rw [hz3]; group
  have hcardB₀ : Nat.card A ≤ 2 * Nat.card B₀ := by
    let f : ↥A → ↥B₀ ⊕ ↥B₀ := fun b =>
      if hb : (b : MulAut W) ∈ B₀ then Sum.inl ⟨b, hb⟩
      else Sum.inr ⟨b * t, hbt b b.2 hb⟩
    have hf : Function.Injective f := by
      intro b b' h
      by_cases h1 : (b : MulAut W) ∈ B₀ <;> by_cases h2 : (b' : MulAut W) ∈ B₀
      · simp only [f, h1, h2, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext h
      · simp [f, h1, h2] at h
      · simp [f, h1, h2] at h
      · simp only [f, h1, h2, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (mul_right_cancel h)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  have hfixA : fixV A = fixV B₀ ⊓ fixV (Subgroup.zpowers t) := by
    ext v
    constructor
    · intro hv
      exact ⟨fun b hb => hv b (hB₀B hb), (HatA6.mem_fixV_zpowers_iff).2 (hv t htA)⟩
    · rintro ⟨hv0, hvt⟩ b hb
      have hvt' : t v = v := (HatA6.mem_fixV_zpowers_iff).1 hvt
      by_cases hb0 : b ∈ B₀
      · exact hv0 b hb0
      · have ht22 : t * t = 1 := by rw [← pow_two]; exact hAe.2 t htA
        have h1 := hv0 _ (hbt b hb hb0)
        calc b v = (b * t * t) v := by rw [mul_assoc, ht22, mul_one]
          _ = (b * t) (t v) := rfl
          _ = v := by rw [hvt', h1]
  have hzU : ∀ u ∈ fixV B₀, z u ∈ fixV B₀ := by
    intro u hu b hb
    have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
    have := congrArg (fun y : MulAut W => y u) hbz
    change b (z u) = z (b u) at this
    rw [this, hu b hb]
  have hdesc := HatA6.card_sq_le_of_semilinear hfp htz' hzU
  rw [← hfixA] at hdesc
  have e1 := (fixV A).card_mul_index
  have hc0 : Nat.card (fixV B₀) ≤ 2 ^ 12 := hcard ▸ Subgroup.card_le_card_group _
  have h1 : 2 ^ 12 ≤ Nat.card (fixV A) * Nat.card A ^ 2 := by
    rw [← hcard, ← e1]
    exact Nat.mul_le_mul_left _ hidx
  have hc64 : Nat.card (fixV A) ≤ 64 := by nlinarith
  have hA8' : 8 ≤ Nat.card A := by nlinarith
  have hc64' : 64 ≤ Nat.card (fixV A) := by
    have : Nat.card A = 8 := le_antisymm hA8 hA8'
    rw [this] at h1
    omega
  have htop : fixV B₀ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hcard]
    nlinarith
  have hB₀1 : Nat.card B₀ = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    exact (htop ▸ Subgroup.mem_top v : v ∈ fixV B₀) b hb
  omega

end B45Exc3A7

namespace B45Exc

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Bridge.ThreeA7Excl B45Exc3A7

theorem threeA7Exclusion2F_holds : ThreeA7Exclusion2F := by
  intro W _ _ hW L E hq hirr he hZ hEN hE hel
  classical
  obtain ⟨e⟩ := he
  have hperf : Group.IsPerfect ↥L := hq.1
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hV : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := by
    have : Group.IsPerfect ↥L := hperf
    have hcov := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 7) (by norm_num)
      (by norm_num) (redHom L e) (redHom_surjective L e) (by rw [hker])
      (by rw [hker]; exact hZodd)).2 (Or.inr rfl)
    rw [hker] at hcov
    rcases hcov with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hZ
    · exact h
  have hL7560 : Nat.card ↥L = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L),
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin, hZ3]
    decide
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ3]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set zL : ↥L := (zc : ↥L) with hzL
  have hzW : orderOf (zL : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hz3 : (zL : MulAut W) ^ 3 = 1 := by
    rw [← hzW]
    exact pow_orderOf_eq_one _
  have hz1 : (zL : MulAut W) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzW
    omega
  have hcen : Subgroup.center ↥L = Subgroup.zpowers zL := by
    have hle : Subgroup.zpowers zL ≤ Subgroup.center ↥L := Subgroup.zpowers_le.2 zc.2
    have hord : orderOf zL = 3 := by
      rw [hzL, Subgroup.orderOf_coe, hzc]
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZ3, Nat.card_zpowers, hord]
  have hzcomm : ∀ l : ↥L, (l : MulAut W) * (zL : MulAut W) = (zL : MulAut W) * l := by
    intro l
    have := Subgroup.mem_center_iff.1 zc.2 l
    exact congrArg Subtype.val this
  have hzf : ∀ w : W, (zL : MulAut W) w = w → w = 1 := by
    have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers (zL : MulAut W)),
        g u ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := by
      intro g hg u hu
      rw [mem_fixV_zpowers] at hu ⊢
      have := congrArg (fun m : MulAut W => m u) (hzcomm ⟨g, hg⟩)
      simp only [MulAut.mul_apply] at this
      rw [← this, hu]
    rcases hirr.2 _ hinv with h | h
    · intro w hw
      have hmem : w ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := mem_fixV_zpowers.2 hw
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hz1
      ext w
      have hmem : w ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := by rw [h]; trivial
      exact mem_fixV_zpowers.1 hmem
  have hker1 : ∀ g : ↥L, redHom L e g = 1 → g ∈ Subgroup.center ↥L := fun g hg =>
    (redHom_eq_one_iff L e g).1 hg
  have hZ3' : ∀ g ∈ Subgroup.center ↥L, g ^ 3 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨g, hg⟩)
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x, y, hx5, hx1, hyx⟩ :=
    exists_fusion_pair_alt7 (redHom L e) (redHom_surjective L e) hker1 hZ3'
  have hx5' : (x : MulAut W) ^ 5 = 1 := by simpa using congrArg Subtype.val hx5
  have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hyx' : (y : MulAut W) * (x : MulAut W) * (y : MulAut W)⁻¹ = (x : MulAut W) ^ 2 := by
    simpa using congrArg Subtype.val hyx
  have hbig := card_gt_of_fusion hW hx5' hx1' hyx' (hzcomm x).symm (hzcomm y).symm hz3 hzf
  have h27 : (Nat.card ↥L).factorization 3 = 3 := by
    rw [hL7560, show (7560 : ℕ) = 3 ^ 3 * 280 from rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have h9 := card_mod_nine_of hperf h27 hcen hz3 hz1 hzf
  by_contra hcon
  push Not at hcon
  have hidx : (fixV E).index ≤ Nat.card E ^ 2 := by
    have hmul := Subgroup.card_mul_index (fixV E)
    have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card E ^ 2 * Nat.card (fixV E) < (fixV E).index * Nat.card (fixV E) :=
      Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [mul_comm ((fixV E).index)] at this
    omega
  obtain ⟨r, hr1, hr2⟩ := exists_card_le_index_pow hW hperf hirr hL hEN hE hel e
  have h12 : Nat.card W ≤ 2 ^ 12 := by
    calc Nat.card W ≤ (fixV E).index ^ r := hr1
      _ ≤ (Nat.card E ^ 2) ^ r := Nat.pow_le_pow_left hidx r
      _ = (Nat.card E ^ r) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ 6) ^ 2 := Nat.pow_le_pow_left hr2 2
      _ = 2 ^ 12 := by norm_num
  have hk := card_eq_two_pow_rk hV
  have hcard : Nat.card W = 2 ^ 12 := by
    rw [hk] at h12 hbig h9 ⊢
    have hk12 : rk W ≤ 12 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h12
    have hk6 : 6 < rk W := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hbig
    revert h9
    interval_cases rk W <;> norm_num
  have hZ3L := hZ3
  by_cases hcomm : ∀ b ∈ E, b * (zL : MulAut W) = (zL : MulAut W) * b
  · have hEL : E ≤ L := fun b hb =>
      mem_of_commute_center hW hperf hirr hEN hel e hZ3L hcen hb (hcomm b hb)
    rcases card_le_of_le hW hperf hirr hL hEN hel hEL hE e with ⟨h2, hb⟩ | ⟨h4, hb⟩
    · rw [h2] at hidx
      have : (fixV E).index ^ 3 ≤ (2 ^ 2) ^ 3 := Nat.pow_le_pow_left hidx 3
      rw [hcard] at hb
      norm_num at this
      omega
    · rw [h4] at hidx
      have : (fixV E).index ^ 2 ≤ (4 ^ 2) ^ 2 := Nat.pow_le_pow_left hidx 2
      rw [hcard] at hb
      norm_num at this
      omega
  · push Not at hcomm
    obtain ⟨t, htE, htz⟩ := hcomm
    set E₀ := E ⊓ Subgroup.centralizer ({(zL : MulAut W)} : Set (MulAut W)) with hE₀
    have hE₀L : E₀ ≤ L := fun b hb =>
      mem_of_commute_center hW hperf hirr hEN hel e hZ3L hcen hb.1
        (Subgroup.mem_centralizer_singleton_iff.1 hb.2)
    have hE₀e : IsElemAbelian2 E₀ :=
      ⟨fun a ha b hb => hel.1 a ha.1 b hb.1, fun a ha => hel.2 a ha.1⟩
    have hE₀N : E₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun b hb => hEN hb.1
    have hE₀4 : Nat.card E₀ ≤ 4 := by
      by_cases hE₀1 : E₀ = ⊥
      · rw [hE₀1, Subgroup.card_bot]
        norm_num
      · rcases card_le_of_le hW hperf hirr hL hE₀N hE₀e hE₀L hE₀1 e with ⟨h2, -⟩ | ⟨h4, -⟩
        · omega
        · omega
    have hE8 : Nat.card E ≤ 8 := by
      have hz2 : ∀ b ∈ E, b ∉ E₀ → b * t ∈ E₀ := by
        intro b hb hb0
        have hbz : b * (zL : MulAut W) = (zL : MulAut W) * (zL : MulAut W) * b := by
          rcases HatA6.conj_z_cases hcen hz3 hz1 (hEN hb) with h | h
          · exact absurd ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 h⟩ hb0
          · exact h
        have htz2 : t * (zL : MulAut W) = (zL : MulAut W) * (zL : MulAut W) * t :=
          (HatA6.conj_z_cases hcen hz3 hz1 (hEN htE)).resolve_left htz
        refine ⟨E.mul_mem hb htE, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have hz33 : (zL : MulAut W) * zL * zL = 1 := by rw [← pow_three']; exact hz3
        calc b * t * zL = b * (t * zL) := by group
          _ = b * (zL * zL * t) := by rw [htz2]
          _ = (b * zL) * zL * t := by group
          _ = (zL * zL * b) * zL * t := by rw [hbz]
          _ = zL * zL * (b * zL) * t := by group
          _ = zL * zL * (zL * zL * b) * t := by rw [hbz]
          _ = zL * (zL * zL * zL) * b * t := by group
          _ = zL * (b * t) := by rw [hz33]; group
      let f : ↥E → ↥E₀ ⊕ ↥E₀ := fun b =>
        if hb : (b : MulAut W) ∈ E₀ then Sum.inl ⟨b, hb⟩
        else Sum.inr ⟨b * t, hz2 b b.2 hb⟩
      have hf : Function.Injective f := by
        intro b b' h
        by_cases h1 : (b : MulAut W) ∈ E₀ <;> by_cases h2 : (b' : MulAut W) ∈ E₀
        · simp only [f, h1, h2, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
          exact Subtype.ext h
        · simp [f, h1, h2] at h
        · simp [f, h1, h2] at h
        · simp only [f, h1, h2, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
          exact Subtype.ext (mul_right_cancel h)
      have := Nat.card_le_card_of_injective f hf
      rw [Nat.card_sum, ← two_mul] at this
      omega
    exact false_of_inverts hcard hEN hel hE8 hidx hcen hz3 hz1 hzf htE htz

end B45Exc

end CFSG.Quasithin
