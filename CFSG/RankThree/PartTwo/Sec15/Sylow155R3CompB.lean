module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.RankThree.PartTwo.Sec14.Ronan148JFix

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

variable {Q : Type} [Group Q] [Finite Q] {c d : Q} {A B₀ K : Subgroup Q}

private theorem eq_of_le_of_ne_bot_of_prime_card {H K : Subgroup Q} (hK : (Nat.card K).Prime)
    (hle : H ≤ K) (hH : H ≠ ⊥) : H = K := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rcases (Nat.dvd_prime hK).mp (Subgroup.card_dvd_of_le hle) with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq H h) hH
  · exact h.ge

private theorem mem_of_mem_zpowers_of_orderOf_three {J : Subgroup Q} {y : Q}
    (hd : orderOf d = 3) (hy : y ∈ Subgroup.zpowers d) (hy1 : y ≠ 1) (hyJ : y ∈ J) : d ∈ J := by
  have hp : (Nat.card (Subgroup.zpowers d)).Prime := by
    rw [Nat.card_zpowers, hd]
    exact Nat.prime_three
  have h := eq_of_le_of_ne_bot_of_prime_card hp (Subgroup.zpowers_le.2 hy) (by simpa using hy1)
  refine Subgroup.zpowers_le.2 hyJ ?_
  rw [h]
  exact Subgroup.mem_zpowers d

private theorem card_zpowers_sup_zpowers_eq_nine (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hcd : c ∉ Subgroup.zpowers d) (hcomm : c * d = d * c) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup Q) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h => hcd (by rw [h]; exact Subgroup.one_mem _)
  have hcard_c : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hcard_d : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hdisj : Subgroup.zpowers c ⊓ Subgroup.zpowers d = ⊥ := by
    by_contra hne
    have heq := eq_of_le_of_ne_bot_of_prime_card (hcard_c ▸ Nat.prime_three) inf_le_left hne
    exact hcd ((heq.symm.le.trans inf_le_right) (Subgroup.mem_zpowers c))
  have hcommute : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ Subgroup.zpowers d, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact Commute.zpow_zpow (show Commute c d from hcomm) i j
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcommute hdisj, hcard_c, hcard_d]

namespace Res3QComp

private theorem orderOf_d (h : Res3QComp c d A B₀ K) : orderOf d = 3 := by
  rw [← Nat.card_zpowers, ← h.K_center, Subgroup.card_map_of_injective K.subtype_injective]
  exact h.K_cover.1

private theorem orderOf_c (h : Res3QComp c d A B₀ K) : orderOf c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime h.c_pow fun h1 => h.c_notMem ?_
  rw [h1]
  exact K.one_mem

private theorem c_mem_centralizer (h : Res3QComp c d A B₀ K) :
    c ∈ Subgroup.centralizer (B₀ : Set Q) :=
  Subgroup.mem_centralizer_iff.2 fun b hb =>
    Subgroup.mem_centralizer_iff.1 h.c_cent b (h.B₀_le hb)

private theorem d_mem_K (h : Res3QComp c d A B₀ K) : d ∈ K :=
  h.B₀_le h.d_mem

end Res3QComp

theorem Res3QBase.mem_normalizer_of_isComponent (_h : Res3QBase c d A B₀ K)
    (huniq : ∀ J₁ J₂ : Subgroup Q, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ → J₁ ≠ K →
      J₂ ≠ K → J₁ = J₂)
    (hnK : ∀ x ∈ Subgroup.centralizer (B₀ : Set Q), x ∈ Subgroup.normalizer (K : Set Q))
    {J : Subgroup Q} (hJ : CFSG.IsComponent J) {x : Q}
    (hx : x ∈ Subgroup.centralizer (B₀ : Set Q)) : x ∈ Subgroup.normalizer (J : Set Q) := by
  by_cases hJK : J = K
  · rw [hJK]
    exact hnK x hx
  · have hxK := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hnK x hx)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    have hJ' : CFSG.IsComponent (J.map (MulAut.conj x).toMonoidHom) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent (MulAut.conj x) hJ
    refine huniq _ _ hJ' hJ (fun hEq => hJK ?_) hJK
    exact Subgroup.map_injective (MulAut.conj x).injective (hEq.trans hxK.symm)

theorem Res3QBase.exists_mem_inf (h : Res3QBase c d A B₀ K)
    (hle : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K → J ≤ Subgroup.centralizer (K : Set Q))
    (huniq : ∀ J₁ J₂ : Subgroup Q, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ → J₁ ≠ K →
      J₂ ≠ K → J₁ = J₂)
    (h8 : ∀ x ∈ Subgroup.centralizer (K : Set Q), Commute x c → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hnK : ∀ x ∈ Subgroup.centralizer (B₀ : Set Q), x ∈ Subgroup.normalizer (K : Set Q))
    (h3J : ∀ J : Subgroup Q, CFSG.IsComponent J → 3 ∣ Nat.card J)
    {J : Subgroup Q} (hJ : CFSG.IsComponent J) (hJK : J ≠ K) :
    ∃ u ∈ J, u ≠ 1 ∧ u ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcN : c ∈ Subgroup.normalizer (J : Set Q) :=
    h.mem_normalizer_of_isComponent huniq hnK hJ h.toRes3QComp.c_mem_centralizer
  have hP : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.toRes3QComp.orderOf_c, pow_one])
  obtain ⟨u, huJ, hu1, hu3, huc⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148J.exists_pow_eq_one_mem_centralizer hP
      (Subgroup.zpowers_le.2 hcN) (h3J J hJ)
  refine ⟨u, huJ, hu1, h8 u (hle J hJ hJK huJ) ?_ hu3⟩
  exact (Subgroup.mem_centralizer_iff.1 huc c (Subgroup.mem_zpowers c)).symm

theorem Res3QBase.d_mem_of_isComponent (h : Res3QBase c d A B₀ K)
    (hle : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K → J ≤ Subgroup.centralizer (K : Set Q))
    (huniq : ∀ J₁ J₂ : Subgroup Q, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ → J₁ ≠ K →
      J₂ ≠ K → J₁ = J₂)
    (hcen : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K →
      ∀ z ∈ (Subgroup.center ↥J).map J.subtype, z ^ 3 = 1 → z ∈ Subgroup.zpowers d)
    (h6 : A ⊓ Subgroup.centralizer (K : Set Q) = Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (h8 : ∀ x ∈ Subgroup.centralizer (K : Set Q), Commute x c → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hnK : ∀ x ∈ Subgroup.centralizer (B₀ : Set Q), x ∈ Subgroup.normalizer (K : Set Q))
    (h3J : ∀ J : Subgroup Q, CFSG.IsComponent J → 3 ∣ Nat.card J)
    {J : Subgroup Q} (hJ : CFSG.IsComponent J) (hJK : J ≠ K) : d ∈ J := by
  by_contra hdJ
  have hord : orderOf d = 3 := h.toRes3QComp.orderOf_d
  have hd3 : d ^ 3 = 1 := hord ▸ pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hord; exact absurd hord (by decide)
  have hdK : d ∈ K := h.toRes3QComp.d_mem_K
  have hcd : c ∉ Subgroup.zpowers d := fun hc => h.c_notMem (Subgroup.zpowers_le.2 hdK hc)
  have hcomm : c * d = d * c := Subgroup.mem_center_iff.1 h.d_center c
  obtain ⟨e, heJ, he1, heD⟩ := h.exists_mem_inf hle huniq h8 hnK h3J hJ hJK
  have hed : e ∉ Subgroup.zpowers d := fun hed =>
    hdJ (mem_of_mem_zpowers_of_orderOf_three hord hed he1 heJ)
  obtain ⟨w, hwA, hwe⟩ := h.wsym e heD hed
  have hK' : CFSG.IsComponent (K.map w.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent w
      ⟨h.K_quasi, h.K_subnormal⟩
  by_cases hwK : K.map w.toMonoidHom = K
  ·
    have hwJ : J.map w.toMonoidHom = J := by
      refine huniq _ _ (CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent w hJ)
        hJ (fun hEq => hJK ?_) hJK
      exact Subgroup.map_injective w.injective (hEq.trans hwK.symm)
    have hweJ : w e ∈ J := hwJ ▸ Subgroup.mem_map_of_mem w.toMonoidHom heJ
    have heD' : e ∈ A ⊓ Subgroup.centralizer (K : Set Q) := h6 ▸ heD
    have hweD : w e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [← h6]
      refine ⟨hwA e heD'.1, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have hk' : k ∈ K.map w.toMonoidHom := by
        rw [hwK]
        exact hk
      obtain ⟨k', hk'K, rfl⟩ := Subgroup.mem_map.1 hk'
      have hcomm' := Subgroup.mem_centralizer_iff.1 heD'.2 k' hk'K
      change w k' * w e = w e * w k'
      rw [← map_mul, ← map_mul, hcomm']
    set D := Subgroup.zpowers c ⊔ Subgroup.zpowers d
    have hDcard : Nat.card D = 9 :=
      card_zpowers_sup_zpowers_eq_nine h.c_pow hd3 hd1 hcd hcomm
    have hIdvd : Nat.card (D ⊓ J : Subgroup Q) ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ J ≤ D)
      rwa [hDcard] at this
    have heI : e ∈ D ⊓ J := ⟨heD, heJ⟩
    have hdD : d ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    have hIcard : Nat.card (D ⊓ J : Subgroup Q) = 3 := by
      obtain ⟨m, hm, hmn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hIdvd
      interval_cases m
      · exfalso
        have hbot : D ⊓ J = ⊥ := Subgroup.eq_bot_of_card_eq _ (hmn.trans (pow_zero 3))
        have heB : e ∈ (⊥ : Subgroup Q) := by
          rw [← hbot]
          exact heI
        exact he1 (Subgroup.mem_bot.1 heB)
      · exact hmn.trans (pow_one 3)
      · exfalso
        have hDJ : D ⊓ J = D :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hDcard, hmn]; norm_num)
        have hdI : d ∈ D ⊓ J := by
          rw [hDJ]
          exact hdD
        exact hdJ hdI.2
    have hIe : Subgroup.zpowers e = D ⊓ J :=
      eq_of_le_of_ne_bot_of_prime_card (by rw [hIcard]; exact Nat.prime_three)
        (Subgroup.zpowers_le.2 heI) (by simpa using he1)
    exact hwe (hIe ▸ (⟨hweD, hweJ⟩ : w e ∈ D ⊓ J))
  ·
    have hwKJ : K.map w.toMonoidHom = J := huniq _ _ hK' hJ hwK hJK
    have hwdJ : w d ∈ J := hwKJ ▸ Subgroup.mem_map_of_mem w.toMonoidHom hdK
    have hwd_central : ∀ q : Q, q * w d = w d * q := fun q => by
      have hq := congrArg w (Subgroup.mem_center_iff.1 h.d_center (w.symm q))
      simpa [map_mul] using hq
    have hwd_cen : w d ∈ (Subgroup.center ↥J).map J.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨w d, hwdJ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      exact fun g => Subtype.ext (hwd_central g)
    have hwd3 : w d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
    have hwd1 : w d ≠ 1 := fun h1 => hd1 (w.injective (by rw [h1, map_one]))
    exact hdJ (mem_of_mem_zpowers_of_orderOf_three hord (hcen J hJ hJK (w d) hwd_cen hwd3)
      hwd1 hwdJ)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
