module

public import CFSG.LocalAnalysis.StandardType.FS81.D6CentAux
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvSylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem d6Cent_three_mem_zpowers {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) {z : G}
    (hz : z ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))
    {a : ℕ} (hz3 : z ^ 3 ^ a = 1) :
    z ∈ Subgroup.zpowers b₀ := by
  obtain ⟨hA, hE, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨hb₀ord, hKC, hKn, hKz, -, hA2, -, -⟩ := hA
  have hb₀Z : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) := b₀_mem_inf_centralizer hKC
  have hcomm : Commute z b₀ :=
    (Subgroup.mem_centralizer_iff.mp hz.1 b₀ (by simp)).symm
  have hHZ : Subgroup.zpowers z ⊔ Subgroup.zpowers b₀ ≤
      Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hz) (Subgroup.zpowers_le.mpr hb₀Z)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀ord]; exact pow_orderOf_eq_one b₀
  have hb₀2 : b₀ ^ 2 = b₀⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', show 2 + 1 = 3 by norm_num]
    exact hb₀3
  have hHp : IsPGroup 3 ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers b₀) := by
    have h := isPGroup_sup_zpowers_of_commute (x := z) (y := b₀) hcomm hz3
      (j := 1) (by simpa using hb₀3)
    simpa using h
  have hHcyc : IsCyclic ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers b₀) :=
    hA2 _ (hHZ.trans inf_le_right) hHp
  classical
  have hex : ∃ c, z ^ 3 ^ c = 1 := ⟨a, hz3⟩
  set c := Nat.find hex with hcdef
  have hdc : z ^ 3 ^ c = 1 := Nat.find_spec hex
  have hmin : ∀ d < c, z ^ 3 ^ d ≠ 1 := fun d hd => Nat.find_min hex hd
  by_cases hc0 : c = 0
  · have hz1 : z = 1 := by simpa [hc0] using hdc
    rw [hz1]
    exact Subgroup.one_mem _
  have hcpos : 1 ≤ c := Nat.pos_of_ne_zero hc0
  by_cases hc1 : c = 1
  · have hz3' : z ^ 3 = 1 := by simpa [hc1] using hdc
    exact mem_zpowers_of_isCyclic_sup hb₀ord hHcyc (Subgroup.mem_zpowers z) hz3'
  have hc2 : 2 ≤ c := by omega
  set e := z ^ 3 ^ (c - 1) with hedef
  have he3 : e ^ 3 = 1 := by
    rw [hedef, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hcpos, hdc]
  have he1 : e ≠ 1 := by
    intro h
    rw [hedef] at h
    exact hmin (c - 1) (by omega) h
  have he_mem : e ∈ Subgroup.zpowers b₀ :=
    mem_zpowers_of_isCyclic_sup hb₀ord hHcyc
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _) he3
  have hev : e = b₀ ∨ e = b₀⁻¹ :=
    CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hb₀ord he_mem he1
  have hcube : ∃ w : G, w ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) ∧ w ^ 3 = b₀ := by
    have hstep : 3 ^ (c - 2) * 3 = 3 ^ (c - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rcases hev with h | h
    · refine ⟨z ^ 3 ^ (c - 2), ⟨Subgroup.pow_mem _ hz.1 _, Subgroup.pow_mem _ hz.2 _⟩, ?_⟩
      have heq : z ^ 3 ^ (c - 1) = b₀ := hedef.symm.trans h
      calc (z ^ 3 ^ (c - 2)) ^ 3 = z ^ (3 ^ (c - 2) * 3) := by rw [pow_mul]
        _ = z ^ 3 ^ (c - 1) := by rw [hstep]
        _ = b₀ := heq
    · refine ⟨(z ^ 3 ^ (c - 2)) ^ 2,
        ⟨Subgroup.pow_mem _ (Subgroup.pow_mem _ hz.1 _) 2,
          Subgroup.pow_mem _ (Subgroup.pow_mem _ hz.2 _) 2⟩, ?_⟩
      have hu : (z ^ 3 ^ (c - 2)) ^ 3 = e := by
        rw [← pow_mul, hstep, ← hedef]
      have h6 : ((z ^ 3 ^ (c - 2)) ^ 2) ^ 3 = ((z ^ 3 ^ (c - 2)) ^ 3) ^ 2 := by
        calc ((z ^ 3 ^ (c - 2)) ^ 2) ^ 3 = (z ^ 3 ^ (c - 2)) ^ (2 * 3) := by rw [pow_mul]
          _ = (z ^ 3 ^ (c - 2)) ^ (3 * 2) := by rw [show 2 * 3 = 3 * 2 by norm_num]
          _ = ((z ^ 3 ^ (c - 2)) ^ 3) ^ 2 := by rw [pow_mul]
      rw [h6, hu, h, ← hb₀2]
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hb₀3, one_mul]
  exact absurd hcube (d6NoCube hstd hB hrec)

theorem exists_cent_D6_aux {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.D6 B b₀) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) ∧
      R ≤ Subgroup.centralizer (K : Set G) ∧
      (∀ x ∈ Subgroup.centralizer ({b₀} : Set G), x ^ 3 = 1 → x ∈ Subgroup.zpowers b₀ ⊔ K) ∧
      ∀ c ∈ Subgroup.centralizer (E : Set G), ¬ 3 ∣ orderOf c → c ∈ R := by
  obtain ⟨hA, hE, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨hb₀ord, hKC, hKn, hKz, -, hA2, -, -⟩ := hA
  obtain ⟨hrow, hdisj, hsupE, hmaxA, hcardA, hCK⟩ := hstd.2.2
  obtain ⟨hEC, hEel, hEmax⟩ := hE
  obtain ⟨hAK, hAel, hAmax⟩ := hmaxA
  let C := Subgroup.centralizer ({b₀} : Set G)
  let Z₀ := C ⊓ Subgroup.centralizer (K : Set G)
  let T : Subgroup G := Subgroup.zpowers b₀ ⊔ K
  let N : Subgroup ↥Z₀ := (Subgroup.zpowers b₀).subgroupOf Z₀
  have hb₀Z : b₀ ∈ Z₀ := b₀_mem_inf_centralizer hKC
  have hNcenter : N ≤ Subgroup.center ↥Z₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : (x : G) ∈ Subgroup.zpowers b₀ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx'
    show (y : G) * (x : G) = (x : G) * (y : G)
    rw [← hi]
    exact (show Commute (y : G) b₀ from
      (Subgroup.mem_centralizer_iff.mp y.2.1 b₀ (by simp)).symm).zpow_right i
  haveI hNnormal : N.Normal := Subgroup.normal_of_le_center hNcenter
  have hNcard : Nat.card N = 3 := by
    have e := Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hb₀Z)
    calc Nat.card N = Nat.card ↥(Subgroup.zpowers b₀) := Nat.card_congr e.toEquiv
      _ = orderOf b₀ := Nat.card_zpowers b₀
      _ = 3 := hb₀ord
  have hNexp : ∀ w ∈ N, w ^ 3 = 1 := by
    intro w hw
    have h := pow_card_eq_one' (G := ↥N) (x := ⟨w, hw⟩)
    rw [hNcard] at h
    simpa using congrArg Subtype.val h
  have hthree : ∀ z : ↥Z₀, z ^ 3 ^ 2 = 1 → z ∈ N := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact d6Cent_three_mem_zpowers (a := 2) hstd hB hrec z.2 (by
      have h := congrArg Subtype.val hz
      simpa [show (3 : ℕ) ^ 2 = 9 by norm_num] using h)
  have hidx : ¬ 3 ∣ N.index := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card (↥Z₀ ⧸ N) := by
      rwa [← Subgroup.index_eq_card]
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    obtain ⟨y, hyx⟩ := QuotientGroup.mk'_surjective N x
    have hy3N : y ^ 3 ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have hq : (QuotientGroup.mk' N) (y ^ 3) = 1 := by
        rw [map_pow, hyx, ← hxord]
        exact pow_orderOf_eq_one x
      simpa using hq
    have h1 : (y ^ 3) ^ 3 = 1 := hNexp (y ^ 3) hy3N
    have hy9 : (y : G) ^ 9 = 1 := by
      have h2 : ((y : G) ^ 3) ^ 3 = 1 := by simpa using congrArg Subtype.val h1
      have h9 : (y : G) ^ 9 = ((y : G) ^ 3) ^ 3 := by
        rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
      rw [h9]
      exact h2
    have hyN : y ∈ N := hthree y (by
      apply Subtype.ext
      simpa [show (3 : ℕ) ^ 2 = 9 by norm_num] using hy9)
    have hyq : (QuotientGroup.mk' N) y = 1 := (QuotientGroup.eq_one_iff y).mpr hyN
    rw [hyq] at hyx
    have hx1 : x = 1 := hyx.symm
    rw [hx1, orderOf_one] at hxord
    norm_num at hxord
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr hidx
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  let R : Subgroup G := H.map Z₀.subtype
  have hRZ : R ≤ Z₀ := Subgroup.map_subtype_le H
  have hRC : R ≤ C := hRZ.trans inf_le_left
  have hRCK : R ≤ Subgroup.centralizer (K : Set G) := hRZ.trans inf_le_right
  have hRcard : Nat.card R = Nat.card H :=
    Subgroup.card_map_of_injective (f := Z₀.subtype) Z₀.subtype_injective
  have hHcard : Nat.card H = N.index := hH.card_right
  have hR3 : ¬ 3 ∣ Nat.card R := by rw [hRcard, hHcard]; exact hidx
  have hNHbot : N ⊓ H = ⊥ := disjoint_iff.mp hH.disjoint
  have hdecomp : ∀ z : ↥Z₀, ∃ n ∈ N, ∃ h ∈ H, z = n * h := by
    intro z
    have hz : z ∈ N ⊔ H := by rw [hH.sup_eq_top]; trivial
    obtain ⟨n, hnN, h, hhH, hnh⟩ := Subgroup.mem_sup_of_normal_left.mp hz
    exact ⟨n, hnN, h, hhH, hnh.symm⟩
  have hRT : ∀ r ∈ R, ∀ t ∈ T, r * t = t * r :=
    commute_zpowers_sup_K_of_le_inf hRZ
  have hRNbot : R ⊓ Subgroup.zpowers b₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxR, hxN⟩ := hx
    obtain ⟨h, hhH, hhx⟩ := Subgroup.mem_map.mp hxR
    have hxZ : x ∈ Z₀ := hRZ hxR
    have hxH : (⟨x, hxZ⟩ : ↥Z₀) ∈ H := by
      have hh : h = ⟨x, hxZ⟩ := Subtype.ext hhx
      rwa [hh] at hhH
    have hxN' : (⟨x, hxZ⟩ : ↥Z₀) ∈ N := Subgroup.mem_subgroupOf.mpr hxN
    have hb : (⟨x, hxZ⟩ : ↥Z₀) ∈ N ⊓ H := ⟨hxN', hxH⟩
    rw [hNHbot] at hb
    simpa using hb
  have hKCK : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hcenter : (⟨a, ha.1⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp ha.2 (b : K) b.2
    rw [hKz] at hcenter
    simpa using hcenter
  have hRTbot : R ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR := hx.1
    have hxT : x ∈ Subgroup.zpowers b₀ ⊔ K := hx.2
    have hcommT : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← hi]
      exact (show Commute b₀ b from
        Subgroup.mem_centralizer_iff.mp (hKC hb) b₀ (by simp)).zpow_left i
    obtain ⟨r, hr, a, ha, hxra⟩ := fs81Sp_mem_sup_of_commute hcommT hxT
    have hrCK : r ∈ Subgroup.centralizer (K : Set G) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hr
      rw [← hi]
      exact (Subgroup.centralizer (K : Set G)).zpow_mem hb₀Z.2 i
    have haCK : a ∈ Subgroup.centralizer (K : Set G) := by
      have haeq : a = r⁻¹ * x := by rw [hxra]; group
      rw [haeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hrCK) (hRZ hxR).2
    have ha_bot : a ∈ (⊥ : Subgroup G) := by
      rw [← hKCK]
      exact ⟨ha, haCK⟩
    have ha1 : a = 1 := by simpa using ha_bot
    have hxr : x ∈ Subgroup.zpowers b₀ := by rw [hxra, ha1, mul_one]; exact hr
    have hxinf : x ∈ R ⊓ Subgroup.zpowers b₀ := ⟨hxR, hxr⟩
    rw [hRNbot] at hxinf
    simpa using hxinf
  have hRmem : ∀ z : G, z ∈ Z₀ → ¬ 3 ∣ orderOf z → z ∈ R := by
    intro z hzZ hz3
    let z' : ↥Z₀ := ⟨z, hzZ⟩
    obtain ⟨n, hnN, h, hhH, hznh⟩ := hdecomp z'
    have hzcoee : z = (n : G) * (h : G) := by
      have := congrArg Subtype.val hznh
      simpa using this
    have hnzp : (n : G) ∈ Subgroup.zpowers b₀ := Subgroup.mem_subgroupOf.mp hnN
    have hhR : (h : G) ∈ R := Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
    have hcomm : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ R, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← hi]
      exact (show Commute b₀ b from
        Subgroup.mem_centralizer_iff.mp (hRZ hb).1 b₀ (by simp)).zpow_left i
    have hdisj : Subgroup.zpowers b₀ ⊓ R = ⊥ := by rw [inf_comm]; exact hRNbot
    have hn3 : (n : G) ^ 3 = 1 := by
      have h := hNexp n hnN
      simpa using congrArg Subtype.val h
    have hmul : ((n : G) * (h : G)) ^ orderOf z = 1 := by
      rw [← hzcoee]
      exact pow_orderOf_eq_one z
    have hn1 : (n : G) = 1 :=
      eq_one_of_commute_mul_pow_eq_one hcomm hdisj hnzp hhR hmul hn3
        (Nat.prime_three.coprime_iff_not_dvd.mpr hz3).symm
    rw [hzcoee, hn1, one_mul]
    exact hhR
  have hRnormal : (R.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRC]
    have hCnorm : C ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
    have hconj : ∀ c ∈ C, ∀ x ∈ R, c * x * c⁻¹ ∈ R := by
      intro c hc x hx
      have hxZ : x ∈ Z₀ := hRZ hx
      have hcxZ : c * x * c⁻¹ ∈ Z₀ := by
        refine ⟨?_, ?_⟩
        · exact C.mul_mem (C.mul_mem hc hxZ.1) (C.inv_mem hc)
        · refine Subgroup.mem_centralizer_iff.mpr ?_
          intro k hk
          have hk' : c⁻¹ * k * c ∈ K := by
            simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCnorm hc)) k).mp hk
          have hxk : x * (c⁻¹ * k * c) * x⁻¹ = c⁻¹ * k * c := by
            have hcomm := Subgroup.mem_centralizer_iff.mp hxZ.2 (c⁻¹ * k * c) hk'
            have := congrArg (· * x⁻¹) hcomm
            simpa [mul_assoc] using this.symm
          have hconjk : (c * x * c⁻¹) * k * (c * x * c⁻¹)⁻¹ = k := by
            have hstep : (c * x * c⁻¹) * k * (c * x * c⁻¹)⁻¹ =
                c * (x * (c⁻¹ * k * c) * x⁻¹) * c⁻¹ := by group
            rw [hstep, hxk]
            group
          have h2 : (c * x * c⁻¹) * k = k * (c * x * c⁻¹) := by
            have := congrArg (· * (c * x * c⁻¹)) hconjk
            simpa [mul_assoc] using this
          exact h2.symm
      apply hRmem _ hcxZ
      have hord : orderOf (c * x * c⁻¹) = orderOf x := by
        rw [show c * x * c⁻¹ = (MulAut.conj c) x by rw [MulAut.conj_apply]]
        exact MulEquiv.orderOf_eq (MulAut.conj c) x
      rw [hord]
      exact fun h3 => hR3 (h3.trans (Subgroup.orderOf_dvd_natCard R hx))
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj c hc x, fun hx => by
      have h2 := hconj c⁻¹ (C.inv_mem hc) (c * x * c⁻¹) hx
      rwa [show c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x by group] at h2⟩
  have hCeq : C = R ⊔ T := by
    apply le_antisymm
    · intro c hc
      obtain ⟨k, hkK, hk⟩ := exists_inner_D6 hstd hB hrec hc
      have hkC : k ∈ C := hKC hkK
      have hzC : k⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hkC) hc
      have hzK : k⁻¹ * c ∈ Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : (k⁻¹ * c) * a * (k⁻¹ * c)⁻¹ = a := by
          have hstep : (k⁻¹ * c) * a * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * a * c⁻¹) * k := by
            group
          rw [hstep, hk a ha]
          group
        have h2 : (k⁻¹ * c) * a = a * (k⁻¹ * c) := by
          have := congrArg (· * (k⁻¹ * c)) h1
          simpa [mul_assoc] using this
        exact h2.symm
      let z : ↥Z₀ := ⟨k⁻¹ * c, hzC, hzK⟩
      obtain ⟨n, hnN, h, hhH, hznh⟩ := hdecomp z
      have hzcoee : k⁻¹ * c = (n : G) * (h : G) := by
        have := congrArg Subtype.val hznh
        simpa using this
      have hhR : (h : G) ∈ R := Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
      have hnzp : (n : G) ∈ Subgroup.zpowers b₀ := Subgroup.mem_subgroupOf.mp hnN
      have hknT : k * (n : G) ∈ T :=
        Subgroup.mul_mem T (Subgroup.mem_sup_right hkK) (Subgroup.mem_sup_left hnzp)
      have heq : c = (k * (n : G)) * (h : G) := by
        calc c = k * (k⁻¹ * c) := by group
          _ = k * ((n : G) * (h : G)) := by rw [hzcoee]
          _ = (k * (n : G)) * (h : G) := by group
      rw [heq]
      exact Subgroup.mul_mem (R ⊔ T) (Subgroup.mem_sup_right hknT)
        (Subgroup.mem_sup_left hhR)
    · exact sup_le (hRZ.trans inf_le_left)
        (sup_le (Subgroup.zpowers_le.mpr hb₀Z.1) hKC)
  have h3elem : ∀ x ∈ C, x ^ 3 = 1 → x ∈ T := by
    intro x hx hx3
    obtain ⟨k, hkK, hk⟩ := exists_inner_D6 hstd hB hrec hx
    have hkC : k ∈ C := hKC hkK
    have hzC : k⁻¹ * x ∈ C := C.mul_mem (C.inv_mem hkC) hx
    have hzK : k⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : (k⁻¹ * x) * a * (k⁻¹ * x)⁻¹ = a := by
        have hstep : (k⁻¹ * x) * a * (k⁻¹ * x)⁻¹ = k⁻¹ * (x * a * x⁻¹) * k := by
          group
        rw [hstep, hk a ha]
        group
      have h2 : (k⁻¹ * x) * a = a * (k⁻¹ * x) := by
        have := congrArg (· * (k⁻¹ * x)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    let z : ↥Z₀ := ⟨k⁻¹ * x, hzC, hzK⟩
    obtain ⟨n, hnN, h, hhH, hznh⟩ := hdecomp z
    have hzcoee : k⁻¹ * x = (n : G) * (h : G) := by
      have := congrArg Subtype.val hznh
      simpa using this
    have hhR : (h : G) ∈ R := Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
    have hnzp : (n : G) ∈ Subgroup.zpowers b₀ := Subgroup.mem_subgroupOf.mp hnN
    have hknT : k * (n : G) ∈ T :=
      Subgroup.mul_mem T (Subgroup.mem_sup_right hkK) (Subgroup.mem_sup_left hnzp)
    have heq : x = (h : G) * (k * (n : G)) := by
      calc x = k * (k⁻¹ * x) := by group
        _ = k * ((n : G) * (h : G)) := by rw [hzcoee]
        _ = (h : G) * (k * (n : G)) := by rw [hRT (h : G) hhR (k * (n : G)) hknT]; group
    have hr1 : (h : G) = 1 := by
      refine eq_one_of_commute_mul_pow_eq_one (H := R) (N := T) (m := 3) (k := Nat.card R)
        (fun r hr t ht => hRT r hr t ht) hRTbot hhR hknT ?_ ?_ ?_
      · rw [← heq]; exact hx3
      · have hdvd : orderOf (h : G) ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hhR
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      · exact Nat.prime_three.coprime_iff_not_dvd.mpr hR3
    rw [heq, hr1, one_mul]
    exact hknT
  have h3prime : ∀ c ∈ Subgroup.centralizer (E : Set G), ¬ 3 ∣ orderOf c → c ∈ R := by
    intro c hcE hc3
    have hcC : c ∈ C :=
      Subgroup.mem_centralizer_iff.mpr (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.mem_centralizer_iff.mp hcE b₀ hb₀E)
    obtain ⟨k, hkK, hk⟩ := exists_inner_D6 hstd hB hrec hcC
    have hkC : k ∈ C := hKC hkK
    have hzC : k⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hkC) hcC
    have hzK : k⁻¹ * c ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : (k⁻¹ * c) * a * (k⁻¹ * c)⁻¹ = a := by
        have hstep : (k⁻¹ * c) * a * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * a * c⁻¹) * k := by
          group
        rw [hstep, hk a ha]
        group
      have h2 : (k⁻¹ * c) * a = a * (k⁻¹ * c) := by
        have := congrArg (· * (k⁻¹ * c)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    let z : ↥Z₀ := ⟨k⁻¹ * c, hzC, hzK⟩
    obtain ⟨n, hnN, h, hhH, hznh⟩ := hdecomp z
    have hzcoee : k⁻¹ * c = (n : G) * (h : G) := by
      have := congrArg Subtype.val hznh
      simpa using this
    have hhR : (h : G) ∈ R := Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
    have hnzp : (n : G) ∈ Subgroup.zpowers b₀ := Subgroup.mem_subgroupOf.mp hnN
    have hkA : k ∈ E ⊓ K := by
      refine ⟨?_, hkK⟩
      have hkcent : k ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro a ha
        have h1 : c * a * c⁻¹ = a := by
          have := congrArg (· * c⁻¹) (Subgroup.mem_centralizer_iff.mp hcE a ha.1)
          simpa [mul_assoc] using this.symm
        have h2 : c * a * c⁻¹ = k * a * k⁻¹ := hk a ha.2
        rw [h1] at h2
        have h3 := congrArg (· * k) h2
        simpa [mul_assoc] using h3
      have hmem : k ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K :=
        ⟨hkcent, hkK⟩
      rw [hCK] at hmem
      exact hmem.1
    have hnk : (n : G) * k = k * (n : G) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hnzp
      rw [← hi]
      exact (show Commute b₀ k from Subgroup.mem_centralizer_iff.mp (hKC hkK) b₀ (by simp)
        ).zpow_left i
    have hyE : (n : G) * k ∈ E :=
      E.mul_mem (Subgroup.zpowers_le.mpr hb₀E hnzp) hkA.1
    have hy3 : ((n : G) * k) ^ 3 = 1 := hEel.2 _ hyE
    have heq : c = ((n : G) * k) * (h : G) := by
      calc c = k * (k⁻¹ * c) := by group
        _ = k * ((n : G) * (h : G)) := by rw [hzcoee]
        _ = (k * (n : G)) * (h : G) := by group
        _ = ((n : G) * k) * (h : G) := by rw [hnk]
    have hy1 : (n : G) * k = 1 := by
      have hyT : (n : G) * k ∈ T :=
        Subgroup.mul_mem T (Subgroup.mem_sup_left hnzp) (Subgroup.mem_sup_right hkK)
      refine eq_one_of_commute_mul_pow_eq_one (H := T) (N := R) (m := orderOf c) (k := 3)
        (fun t ht r hr => (hRT r hr t ht).symm) ?_ hyT hhR ?_ hy3 ?_
      · rw [inf_comm]; exact hRTbot
      · rw [← heq]; exact pow_orderOf_eq_one c
      · exact (Nat.prime_three.coprime_iff_not_dvd.mpr hc3).symm
    rw [heq, hy1, one_mul]
    exact hhR
  exact ⟨R, hRC, hRnormal, hR3, hCeq, hRCK, h3elem, h3prime⟩

end CFSG.StandardType.FrameRoute.FS81
