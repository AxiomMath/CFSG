module

public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.RankThree.PartTwo.KFacts.KS12Even
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_center_of_mem_thetaQuotCentralizer {L : Subgroup G} {x : L}
    (hx : (x : G) ∈ Sec4.thetaQuotCentralizer L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) x ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) q
  obtain ⟨t, ht, hte⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp hx).2 l l.2
  have h1 : l⁻¹ * (x * l * x⁻¹) ∈ aschbacherSolvableCore 3 L := by
    have : t = l⁻¹ * (x * l * x⁻¹) := Subtype.ext hte
    rw [← this]
    exact ht
  have h2 : π (x * l * x⁻¹) = π l := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr h1).symm
  rw [map_mul, map_mul, map_inv] at h2
  calc π l * π x = (π x * π l * (π x)⁻¹) * π x := by rw [h2]
    _ = π x * π l := by group

theorem exists_fixed_lift {L D : Subgroup G} (hD : IsPGroup 3 D)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) {l : G}
    (hfix : ∀ d ∈ D, l⁻¹ * (d * l * d⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    ∃ n ∈ inSubgroup (aschbacherSolvableCore 3) L, ∀ d ∈ D, d * (l * n) * d⁻¹ = l * n := by
  have hN3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [show Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 L) from
        Subgroup.card_map_of_injective L.subtype_injective]
    exact three_not_dvd_card_aschbacherSolvableCore
  refine exists_fixed_mem_coset hD hN3 l fun d hd n hn => ?_
  refine ⟨l⁻¹ * (d * l * d⁻¹) * (d * n * d⁻¹), Subgroup.mul_mem _ (hfix d hd)
    (conj_mem_inSubgroup_theta (hDL hd) hn), by group⟩

theorem exists_two_subgroup_of_centralizes {L D : Subgroup G} (hD : IsPGroup 3 D)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) {t : L} (hDt : ∀ d ∈ D, d * (t : G) = t * d)
    (ht2 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 L) t) = 2) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ D ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  set Y : Subgroup L := (Subgroup.zpowers (π t)).comap π with hY
  set Y' : Subgroup G := Y.map L.subtype with hY'
  have hYcard : Nat.card Y = Nat.card N * Nat.card (Subgroup.zpowers (π t)) :=
    QuotientGroup.card_preimage_mk N (Subgroup.zpowers (π t) : Set (L ⧸ N))
  have hY'card : Nat.card Y' = Nat.card N * 2 := by
    rw [hY', Subgroup.card_map_of_injective L.subtype_injective, hYcard, Nat.card_zpowers, ht2]
  have hcop : Nat.Coprime 3 (Nat.card Y') := by
    rw [hY'card]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      three_not_dvd_card_aschbacherSolvableCore) (by norm_num)
  have h2 : 2 ∣ Nat.card Y' := by
    rw [hY'card]
    exact Dvd.dvd.mul_left (dvd_refl 2) _
  have hDY : D ≤ Subgroup.normalizer (Y' : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hy₀)
    have hdy : d * (y₀ : G) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hDL hd) _).mp y₀.2
    refine ⟨⟨_, hdy⟩, Subgroup.mem_comap.mpr ⟨k, ?_⟩, rfl⟩
    have h1 : ((t ^ k)⁻¹ * y₀ : L) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, map_zpow,
        ← hπ, hk, inv_mul_cancel]
    have h2 : d * (((t ^ k)⁻¹ * y₀ : L) : G) * d⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
      conj_mem_inSubgroup_theta (hDL hd) ⟨_, h1, rfl⟩
    have hdtk : d * ((t : G) ^ k) * d⁻¹ = (t : G) ^ k := by
      have hc : Commute d (t : G) := hDt d hd
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    obtain ⟨m, hm, hme⟩ := h2
    have hm' : (t ^ k)⁻¹ * (⟨_, hdy⟩ : L) = m := by
      apply Subtype.ext
      change (((t ^ k)⁻¹ * (⟨_, hdy⟩ : L) : L) : G) = L.subtype m
      rw [hme]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      calc ((t : G) ^ k)⁻¹ * (d * y₀ * d⁻¹)
          = (d * (t : G) ^ k * d⁻¹)⁻¹ * (d * y₀ * d⁻¹) := by rw [hdtk]
        _ = d * (((t : G) ^ k)⁻¹ * y₀) * d⁻¹ := by group
    have h3 : π (⟨_, hdy⟩ : L) = π (t ^ k) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have he : (⟨_, hdy⟩ : L)⁻¹ * t ^ k = m⁻¹ := by
        rw [← hm']
        group
      rw [he]
      exact N.inv_mem hm
    rw [h3, map_zpow]
  have hD3 : IsPGroup 3 D := hD
  obtain ⟨S, hSD, hS0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two D Y' hD3 hDY hcop h2
  exact ⟨_, hS0, S.isPGroup'.map Y'.subtype, hSD⟩

omit [Finite G] in
theorem inf_zpowers_eq_bot_of_not_mem {D : Subgroup G} {w : G} (hw3 : orderOf w = 3)
    (hwD : w ∉ D) : D ⊓ Subgroup.zpowers w = ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
  have : Fact (Nat.card (Subgroup.zpowers w)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (D.subgroupOf (Subgroup.zpowers w)) with h | h
  · rw [eq_bot_iff]
    intro y ⟨hyD, hyw⟩
    have hy : (⟨y, hyw⟩ : Subgroup.zpowers w) ∈ D.subgroupOf (Subgroup.zpowers w) := hyD
    rw [h] at hy
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hy))
  · exfalso
    have hd : (⟨w, Subgroup.mem_zpowers w⟩ : Subgroup.zpowers w) ∈
        D.subgroupOf (Subgroup.zpowers w) := by rw [h]; trivial
    exact hwD hd

theorem false_of_le_E81 (hFE : partTwoF G = partTwoE G) {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27) {U : Subgroup G}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hDU : D ≤ Subgroup.normalizer (U : Set G)) {w : G}
    (hw : w ∈ Subgroup.centralizer (D : Set G)) (hw3 : orderOf w = 3) (hwD : w ∉ D) : False := by
  obtain ⟨hFcard, hFc, hFe⟩ := card_sup_zpowers_of_disjoint hw hD.1 hD.2 hw3
    (inf_zpowers_eq_bot_of_not_mem hw3 hwD)
  have hDE : D ∈ partTwoE G := ⟨hD, hD27, U, hU, hU2, hDU⟩
  obtain ⟨M, hFM, hM⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B)
    (show CFSG.Assembly.IsElemAbelian 3 (D ⊔ Subgroup.zpowers w) from ⟨hFc, hFe⟩)
  have hMF : M ∈ partTwoF G :=
    ⟨hM.1, fun B hB hMB => (hM.2 hB hMB).antisymm hMB, D, hDE, le_sup_left.trans hFM⟩
  rw [hFE] at hMF
  have hdvd := Subgroup.card_dvd_of_le hFM
  rw [hFcard, hD27, hMF.2.1] at hdvd
  norm_num at hdvd

theorem exists_pow_orderOf_three {L : Subgroup G} {y : L}
    (hy : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 L) y) = 3) :
    ∃ m : ℕ, ¬ 3 ∣ m ∧ orderOf (y ^ m) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  obtain ⟨k, m, hm, hym, -⟩ := exists_threePart y
  refine ⟨m, hm, orderOf_eq_prime ?_ ?_⟩
  ·
    have h3 := pow_orderOf_eq_one (π y)
    rw [hy] at h3
    have h1 : π ((y ^ m) ^ 3) = 1 := by
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, h3, one_pow]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 : ((⟨_, h1⟩ : aschbacherSolvableCore 3 L) : L) ^ 3 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    have hdvd : orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime (orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L)) 3 := by
      have hd := orderOf_dvd_natCard (⟨_, h1⟩ : aschbacherSolvableCore 3 L)
      exact Nat.Coprime.coprime_dvd_left hd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          three_not_dvd_card_aschbacherSolvableCore).symm
    have h1' : orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
    rw [orderOf_eq_one_iff] at h1'
    exact congrArg Subtype.val h1'
  · intro h1
    have h2 : π y ^ m = 1 := by rw [← map_pow, h1, map_one]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at h3
    exact hm h3

theorem false_of_E27_le_thetaQuotCentralizer (hFE : partTwoF G = partTwoE G) {L : Subgroup G}
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (hDC : D ≤ Sec4.thetaQuotCentralizer L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hD3 : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hD.2 x x.2)⟩
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    hDC.trans (thetaQuotCentralizer_le_normalizer' L)
  have hfix : ∀ l : L, ∀ d ∈ D, (l : G)⁻¹ * (d * l * d⁻¹) ∈
      inSubgroup (aschbacherSolvableCore 3) L := fun l d hd =>
    (Sec6.mem_thetaQuotCentralizer_iff.mp (hDC hd)).2 l l.2
  obtain ⟨xb, hxb3, hxbZ⟩ := KFacts.exists_orderOf_three_not_mem_center hperf hZ
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N xb
  obtain ⟨n, hn, hn'⟩ := exists_fixed_lift hD3 hDL (hfix l)
  have hy : (l : G) * n ∈ L := L.mul_mem l.2 (Subgroup.map_subtype_le _ hn)
  set y : L := ⟨_, hy⟩ with hydef
  have hπy : π y = π l := by
    obtain ⟨n', hn'N, rfl⟩ := hn
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : y⁻¹ * l = n'⁻¹ := Subtype.ext (by simp [hydef])
    rw [this]
    exact N.inv_mem hn'N
  obtain ⟨m, hm, hym⟩ := exists_pow_orderOf_three (y := y) (by rw [hπy]; exact hxb3)
  have hπym : π (y ^ m) ∉ Subgroup.center (L ⧸ N) := by
    intro hc
    apply hxbZ
    obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
    have hxb : π l = (π (y ^ m)) ^ r := by
      have h3 := pow_orderOf_eq_one (π l)
      rw [hxb3] at h3
      rw [map_pow, hπy, ← pow_mul, pow_eq_pow_mod (m * r) h3, hr, pow_one]
    rw [hxb]
    exact Subgroup.pow_mem _ hc r
  set w : G := ((y ^ m : L) : G) with hw
  have hwL : w ∈ L := (y ^ m).2
  have hwc : w ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : d * (y : G) * d⁻¹ = y := hn' d hd
    have hc : Commute d (y : G) := by
      change d * y = y * d
      calc d * (y : G) = (d * y * d⁻¹) * d := by group
        _ = y * d := by rw [h1]
    have := (hc.pow_right m).eq
    rw [hw, Subgroup.coe_pow]
    exact this
  have hw3 : orderOf w = 3 := by rw [hw, Subgroup.orderOf_coe]; exact hym
  have hwD : w ∉ D := fun hwD => hπym (mk_mem_center_of_mem_thetaQuotCentralizer (hDC hwD))
  obtain ⟨tb, htb⟩ := exists_prime_orderOf_dvd_card' (G := L ⧸ N) 2 hev
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk'_surjective N tb
  obtain ⟨n₂, hn₂, hn₂'⟩ := exists_fixed_lift hD3 hDL (hfix t₀)
  have ht : (t₀ : G) * n₂ ∈ L := L.mul_mem t₀.2 (Subgroup.map_subtype_le _ hn₂)
  set t : L := ⟨_, ht⟩ with htdef
  have hπt : π t = π t₀ := by
    obtain ⟨n', hn'N, rfl⟩ := hn₂
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : t⁻¹ * t₀ = n'⁻¹ := Subtype.ext (by simp [htdef])
    rw [this]
    exact N.inv_mem hn'N
  have hDt : ∀ d ∈ D, d * (t : G) = t * d := fun d hd => by
    have h1 : d * (t : G) * d⁻¹ = t := hn₂' d hd
    calc d * (t : G) = (d * t * d⁻¹) * d := by group
      _ = t * d := by rw [h1]
  obtain ⟨U, hU0, hU2, hDU⟩ := exists_two_subgroup_of_centralizes hD3 hDL hDt
    (by rw [hπt]; exact htb)
  exact false_of_le_E81 hFE hD hD27 hU0 hU2 hDU hwc hw3 hwD

end CFSG.RankThree.PartTwo.Sec12
