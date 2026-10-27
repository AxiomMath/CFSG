module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Rk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ1
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]

private def s16e_z7_fixSub (x : MulAut W) : Subgroup W :=
  x.toMonoidHom.eqLocus (MonoidHom.id W)

private lemma s16e_z7_mem_fixSub {x : MulAut W} {v : W} :
    v ∈ s16e_z7_fixSub x ↔ x v = v := Iff.rfl

private def s16e_z7_fixPoint (w : W) : Subgroup (MulAut W) where
  carrier := {g | g w = w}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show (a * b) w = w
    rw [MulAut.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    show a⁻¹ w = w
    calc a⁻¹ w = a⁻¹ (a w) := by rw [ha]
      _ = (a⁻¹ * a) w := by rw [MulAut.mul_apply]
      _ = w := by rw [inv_mul_cancel, MulAut.one_apply]

private def s16e_z7_norm3 (c : MulAut W) (w : W) : W := w * c w * c (c w)

private lemma s16e_z7_mul_self (hW : ∀ w : W, w ^ 2 = 1) (w : W) : w * w = 1 := by
  have := hW w
  rwa [pow_two] at this

private lemma s16e_z7_norm3_fixed {c : MulAut W} (hc3 : c ^ 3 = 1) (w : W) :
    c (s16e_z7_norm3 c w) = s16e_z7_norm3 c w := by
  have hc : ∀ v, c (c (c v)) = v := by
    intro v
    have := congrArg (fun f : MulAut W => f v) hc3
    simpa [pow_three, MulAut.mul_apply] using this
  simp [s16e_z7_norm3, map_mul, hc, mul_assoc, mul_comm, mul_left_comm]

private lemma s16e_z7_norm3_mul (hW : ∀ w : W, w ^ 2 = 1) (a b : MulAut W)
    (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (w : W) :
    s16e_z7_norm3 a w * s16e_z7_norm3 b w * s16e_z7_norm3 (a * b) w
        * s16e_z7_norm3 (a * b * b) w
      = w * s16e_z7_norm3 a (s16e_z7_norm3 b w) := by
  have hab' : ∀ v, a (b v) = b (a v) := by
    intro v
    have := congrArg (fun f : MulAut W => f v) hab
    simpa [MulAut.mul_apply] using this
  have ha3' : ∀ v, a (a (a v)) = v := by
    intro v
    have := congrArg (fun f : MulAut W => f v) ha3
    simpa [pow_three, MulAut.mul_apply] using this
  have hb3' : ∀ v, b (b (b v)) = v := by
    intro v
    have := congrArg (fun f : MulAut W => f v) hb3
    simpa [pow_three, MulAut.mul_apply] using this
  simp [s16e_z7_norm3, MulAut.mul_apply, map_mul, hab', ha3', hb3', mul_assoc, mul_comm,
    mul_left_comm]
  try rw [← mul_assoc, s16e_z7_mul_self hW w, one_mul]

private lemma s16e_z7_fixSub_eq_one [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {ℓ : MulAut W} (hℓ7 : ℓ ^ 7 = 1)
    (hfpf : ∀ w : W, ℓ w = w → w = 1) {x : MulAut W} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxℓ : x * ℓ = ℓ * x) : ∀ v : W, x v = v → v = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : CFSG.OddStandard.HigherRank.G2Three.Sec1.IsE 6 W := by
    refine ⟨⟨IsMulCommutative.of_comm (fun u v => Subtype.ext (mul_comm u.1 v.1)),
      fun u _ => hW u⟩, ?_⟩
    rw [hcard]
  have hVinv : ∀ u ∈ s16e_z7_fixSub x, ℓ u ∈ s16e_z7_fixSub x := by
    intro u hu
    rw [s16e_z7_mem_fixSub] at hu ⊢
    calc x (ℓ u) = (x * ℓ) u := by rw [MulAut.mul_apply]
      _ = (ℓ * x) u := by rw [hxℓ]
      _ = ℓ (x u) := by rw [MulAut.mul_apply]
      _ = ℓ u := by rw [hu]
  have hcases :=
    CFSG.OddStandard.HigherRank.YamadaG23.y7c_card_invariant_cases hE hℓ7 hfpf hVinv
  have hmod : Nat.card (s16e_z7_fixSub x) % 3 = 1 := by
    have h := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime
      (K := W) x (p := 3) hx3
    rw [Nat.ModEq] at h
    have hfx : Nat.card {u : W // x u = u} = Nat.card (s16e_z7_fixSub x) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => s16e_z7_mem_fixSub)
    rw [hfx, hcard] at h
    norm_num at h
    omega
  intro v hv
  rcases hcases with h1 | h8 | h64
  · have hbot : s16e_z7_fixSub x = ⊥ := Subgroup.card_eq_one.mp h1
    have hvV : v ∈ s16e_z7_fixSub x := s16e_z7_mem_fixSub.mpr hv
    rw [hbot] at hvV
    exact Subgroup.mem_bot.mp hvV
  · exfalso
    rw [h8] at hmod
    norm_num at hmod
  · exfalso
    have htop : s16e_z7_fixSub x = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h64, hcard]; norm_num)
    have hxeq : x = 1 := by
      ext u
      have hu : u ∈ s16e_z7_fixSub x := htop ▸ Subgroup.mem_top u
      rwa [s16e_z7_mem_fixSub] at hu
    exact hx1 hxeq

private lemma s16e_z7_norm3_eq_one [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {ℓ : MulAut W} (hℓ7 : ℓ ^ 7 = 1)
    (hfpf : ∀ w : W, ℓ w = w → w = 1) {x : MulAut W} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxℓ : x * ℓ = ℓ * x) : ∀ w : W, s16e_z7_norm3 x w = 1 := by
  intro w
  exact s16e_z7_fixSub_eq_one hW hcard hℓ7 hfpf hx3 hx1 hxℓ _
    (s16e_z7_norm3_fixed hx3 w)

theorem s16e_pRank_three_lt_three_of_z7 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsCyclicOrd ↥L 7)
    (hWL : commSub ⊤ L = ⊤) : CFSG.Open.pRank 3 A < 3 := by
  by_contra hge
  rw [not_lt] at hge
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ℓ, hℓ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top L).mp hL.1
  have hℓL : ℓ ∈ L := hℓ ▸ Subgroup.mem_zpowers ℓ
  have hoddL : Odd (Nat.card L) := by
    rw [hL.2]
    norm_num
  have hfixbot : fixV L = ⊥ := by
    have h := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hoddL
    rw [hWL, inf_top_eq] at h
    exact h
  have hℓ7 : ℓ ^ 7 = 1 := by
    have hord : orderOf ℓ = 7 := by
      rw [← Nat.card_zpowers ℓ, hℓ, hL.2]
    rw [← hord]
    exact pow_orderOf_eq_one ℓ
  have hfpf : ∀ w : W, ℓ w = w → w = 1 := by
    intro w hw
    have hmem : w ∈ fixV L := by
      rw [mem_fixV]
      intro g hg
      have hle : L ≤ s16e_z7_fixPoint w := by
        rw [← hℓ]
        exact Subgroup.zpowers_le.mpr hw
      exact hle hg
    rw [hfixbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨E, hEA, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := A) (k := 3) hge
  haveI hEcomm : IsMulCommutative E := hEelem.1
  let N : Subgroup (MulAut W) := Subgroup.normalizer (L : Set (MulAut W))
  have hEN : E ≤ N := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hLn g (hEA hg)
  let φ : E →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  haveI : IsCyclic ↥L := hL.1
  have hφmul : Nat.card (MulAut ↥L) = 6 := by
    rw [IsCyclic.card_mulAut, hL.2, Nat.totient_prime Nat.prime_seven]
  have hφrange_dvd6 : Nat.card φ.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hφmul] at h
  have hφrange_dvd27 : Nat.card φ.range ∣ 27 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hEcard] at h
    exact ⟨Nat.card φ.ker, by rw [mul_comm]; exact h.symm⟩
  have hker : 9 ≤ Nat.card φ.ker := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hEcard] at h
    have hdvd : Nat.card φ.range ∣ 3 := by
      have h3 : Nat.gcd 27 6 = 3 := by norm_num
      have := Nat.dvd_gcd hφrange_dvd27 hφrange_dvd6
      rwa [h3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · rw [h1, mul_one] at h
      omega
    · rw [h3] at h
      omega
  let K : Subgroup (MulAut W) := φ.ker.map E.subtype
  have hKcard : 9 ≤ Nat.card K := by
    rw [show Nat.card K = Nat.card φ.ker from
      Subgroup.card_map_of_injective E.subtype_injective]
    exact hker
  have hKle : K ≤ E := Subgroup.map_subtype_le _
  have hKelem : ∀ x ∈ K, x ^ 3 = 1 := fun x hx => hEelem.2 x (hKle hx)
  have hKℓ : ∀ x ∈ K, (x : MulAut W) * ℓ = ℓ * (x : MulAut W) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change (y : MulAut W) * ℓ = ℓ * (y : MulAut W)
    have hy1 : L.normalizerMonoidHom (Subgroup.inclusion hEN y) = 1 := by
      simpa [φ] using MonoidHom.mem_ker.mp hy
    have hh : (L.normalizerMonoidHom (Subgroup.inclusion hEN y)) ⟨ℓ, hℓL⟩ = ⟨ℓ, hℓL⟩ := by
      rw [hy1]
      rfl
    have hcoe : (((L.normalizerMonoidHom (Subgroup.inclusion hEN y)) ⟨ℓ, hℓL⟩ : ↥L) :
        MulAut W) = ℓ := congrArg Subtype.val hh
    have happ := Subgroup.normalizerMonoidHom_apply_apply_coe L
      (Subgroup.inclusion hEN y) ⟨ℓ, hℓL⟩
    rw [show ((Subgroup.inclusion hEN y : N) : MulAut W) = (y : MulAut W) from rfl,
      hcoe] at happ
    calc (y : MulAut W) * ℓ = ((y : MulAut W) * ℓ * (y : MulAut W)⁻¹) * (y : MulAut W) := by
          group
      _ = ℓ * (y : MulAut W) := by rw [happ.symm]
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha1⟩ := exists_ne (1 : K)
  have ha3 : (a : MulAut W) ^ 3 = 1 := hKelem (a : MulAut W) a.2
  have ha3K : a ^ 3 = 1 := Subtype.ext ha3
  have hord : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha3K
    have hne1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf a) hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hnotle : ¬ (⊤ : Subgroup K) ≤ Subgroup.zpowers a := by
    intro hle
    have htop : Subgroup.zpowers a = ⊤ := top_unique hle
    have hcard3 : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, hord]
    have hK3 : Nat.card K = 3 := by
      have h := congrArg (fun H : Subgroup K => Nat.card ↥H) htop
      rw [Subgroup.card_top, hcard3] at h
      exact h.symm
    omega
  obtain ⟨b, -, hb_notin⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hb1 : b ≠ 1 := by
    intro h
    exact hb_notin (by rw [h]; exact Subgroup.one_mem _)
  set aW : MulAut W := (a : MulAut W)
  set bW : MulAut W := (b : MulAut W)
  have haW3 : aW ^ 3 = 1 := by simpa [aW] using ha3
  have hbW3 : bW ^ 3 = 1 := by simpa [bW] using hKelem b b.2
  have habW : aW * bW = bW * aW := by
    have h := Subgroup.mul_comm_of_mem_isMulCommutative (H := E) (a := (a : MulAut W))
      (b := (b : MulAut W)) (hKle a.2) (hKle b.2)
    simpa [aW, bW] using h
  have habW3 : (aW * bW) ^ 3 = 1 := by
    have h := hKelem (a * b) (K.mul_mem a.2 b.2)
    simpa [aW, bW] using h
  have habbW3 : (aW * bW * bW) ^ 3 = 1 := by
    have h := hKelem (a * b * b) (K.mul_mem (K.mul_mem a.2 b.2) b.2)
    simpa [aW, bW] using h
  have haW1 : aW ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext (by simpa [aW] using h))
  have hbW1 : bW ≠ 1 := by
    intro h
    exact hb1 (Subtype.ext (by simpa [bW] using h))
  have habW1 : aW * bW ≠ 1 := by
    intro h
    have hK : a * b = 1 := Subtype.ext (by simpa [aW, bW] using h)
    have hb_eq : b = a⁻¹ := eq_inv_of_mul_eq_one_right hK
    exact hb_notin (by
      rw [hb_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have habbW1 : aW * bW * bW ≠ 1 := by
    intro h
    have hK : a * b * b = 1 := Subtype.ext (by simpa [aW, bW] using h)
    have hb2 : b * b = a⁻¹ := by
      rw [mul_assoc] at hK
      exact eq_inv_of_mul_eq_one_right hK
    have hb2mem : b * b ∈ Subgroup.zpowers a := by
      rw [hb2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
    have hb3 : b ^ 3 = 1 := Subtype.ext (hKelem (b : MulAut W) b.2)
    have hbmul : b * (b * b) = 1 := by
      simpa [pow_three, mul_assoc] using hb3
    have hb_eq : b = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hbmul
    apply hb_notin
    rw [hb_eq]
    exact Subgroup.inv_mem _ hb2mem
  have haWℓ : aW * ℓ = ℓ * aW := by simpa [aW] using hKℓ a a.2
  have hbWℓ : bW * ℓ = ℓ * bW := by simpa [bW] using hKℓ b b.2
  have habWℓ : (aW * bW) * ℓ = ℓ * (aW * bW) := by
    have h := hKℓ (a * b) (K.mul_mem a.2 b.2)
    simpa [aW, bW] using h
  have habbWℓ : (aW * bW * bW) * ℓ = ℓ * (aW * bW * bW) := by
    have h := hKℓ (a * b * b) (K.mul_mem (K.mul_mem a.2 b.2) b.2)
    simpa [aW, bW] using h
  have hna : ∀ w, s16e_z7_norm3 aW w = 1 :=
    s16e_z7_norm3_eq_one hW hcard hℓ7 hfpf haW3 haW1 haWℓ
  have hnb : ∀ w, s16e_z7_norm3 bW w = 1 :=
    s16e_z7_norm3_eq_one hW hcard hℓ7 hfpf hbW3 hbW1 hbWℓ
  have hnab : ∀ w, s16e_z7_norm3 (aW * bW) w = 1 :=
    s16e_z7_norm3_eq_one hW hcard hℓ7 hfpf habW3 habW1 habWℓ
  have hnabb : ∀ w, s16e_z7_norm3 (aW * bW * bW) w = 1 :=
    s16e_z7_norm3_eq_one hW hcard hℓ7 hfpf habbW3 habbW1 habbWℓ
  have hall : ∀ w : W, w = 1 := by
    intro w
    have h := s16e_z7_norm3_mul hW aW bW habW haW3 hbW3 w
    rw [hna w, hnb w, hnab w, hnabb w] at h
    have h1 : s16e_z7_norm3 aW 1 = 1 := by simp [s16e_z7_norm3]
    rw [h1] at h
    simpa using h.symm
  have hsub : Subsingleton W := ⟨fun x y => (hall x).trans (hall y).symm⟩
  have hcard1 : Nat.card W = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  rw [hcard] at hcard1
  norm_num at hcard1

end Generic

section Case

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_false_of_z7 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hZ : IsElemAbelianOfRank 7 1 ↥(lBar V₀ V hV L))
    (hrk : rk ↥(wTil V₀ V hV L) = 6) : False := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  have hrkV : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← hwT]
    exact hrk
  have hsig := s16e_sig_eq_three_of_rk_le_eight D hx h4 h61 h127 hset.hyp16 hV (by omega)
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  have hm3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 h3
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hT, hrkV]
  have hc7 : Nat.card ↥(lBar V₀ V hV L) = 7 := by
    simpa using s16c167_card_isElemAbelianOfRank hZ
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 7 := ⟨isCyclic_of_prime_card hc7, hc7⟩
  have hlt := s16e_pRank_three_lt_three_of_z7 hT hcard
    (A := Mbar D.M V₀ V hV) (L := lBar V₀ V hV L)
    (barSub_mono V₀ V hV hset.hyp151.le)
    (fun g hg => lBar_conj_eq_of_s15_eq_one hs hg) hcyc hwT
  omega

end Case

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
