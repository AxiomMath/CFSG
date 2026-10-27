module

public import CFSG.RankThree.PartTwo.Sec10.Item104

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section General

variable {G : Type} [Group G]

theorem conj_eq_of_sq_conj_eq {y x : G} {k : ℕ} (hy : y ^ 3 ^ k = 1)
    (h2 : y ^ 2 * x * (y ^ 2)⁻¹ = x) : y * x * y⁻¹ = x := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow ⟨1, rfl⟩
  have hyy : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ y (3 ^ k), hy, one_mul]
  have hc : Commute (y ^ 2) x := mul_inv_eq_iff_eq_mul.mp h2
  rw [hyy, (hc.pow_left (m + 1)).eq, mul_inv_cancel_right]

theorem conj_eq_of_mem_normalizer_zpowers {y d : G} {k : ℕ} (hy : y ^ 3 ^ k = 1)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) : y * d * y⁻¹ = d := by
  have h1 : y * d * y⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hyN d).mp (Subgroup.mem_zpowers d)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
  rcases zpow_cases_of_pow_three hd3 i with h | h | h <;> rw [h] at hi
  · exact absurd (conj_eq_one_iff.mp hi.symm) hd1
  · exact hi.symm
  · apply conj_eq_of_sq_conj_eq hy
    calc y ^ 2 * d * (y ^ 2)⁻¹ = y * (y * d * y⁻¹) * y⁻¹ := by rw [sq]; group
      _ = y * d ^ 2 * y⁻¹ := by rw [← hi]
      _ = (y * d * y⁻¹) ^ 2 := conj_pow.symm
      _ = d := by
          rw [← hi, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ d 3, hd3, one_mul]

theorem conj_pow_iterate_eq {y c δ : G} (hc : y * c * y⁻¹ = c * δ) (hδ : y * δ * y⁻¹ = δ)
    (t : ℕ) : y ^ t * c * (y ^ t)⁻¹ = c * δ ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc y ^ (t + 1) * c * (y ^ (t + 1))⁻¹ = y * (y ^ t * c * (y ^ t)⁻¹) * y⁻¹ := by
          rw [pow_succ' y t]
          group
      _ = (y * c * y⁻¹) * (y * δ * y⁻¹) ^ t := by
          rw [ih, conj_pow]
          group
      _ = c * δ ^ (t + 1) := by rw [hc, hδ, pow_succ' δ t, mul_assoc]

theorem exists_pow_eq_mul_of_mem_sup {c d v : G} (hc3 : c ^ 3 = 1) (hcd : c * d = d * c)
    (hv : v ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (hvd : v ∉ Subgroup.zpowers d) :
    ∃ m : ℕ, ∃ δ ∈ Subgroup.zpowers d, v ^ m = c * δ := by
  have hdc : ∀ x ∈ Subgroup.zpowers d, x * c = c * x := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute d c from hcd.symm) j)).eq
  obtain ⟨i, δ, hδ, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers hdc hv
  rcases zpow_cases_of_pow_three hc3 i with h | h | h <;> rw [h] at hvd ⊢
  · rw [one_mul] at hvd
    exact absurd hδ hvd
  · exact ⟨1, δ, hδ, pow_one _⟩
  · refine ⟨2, δ ^ 2, Subgroup.pow_mem _ hδ 2, ?_⟩
    have hcδ : Commute (c ^ 2) δ := ((show Commute c δ from (hdc δ hδ).symm).pow_left 2)
    rw [hcδ.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ c 3, hc3, one_mul]

theorem exists_mem_normalizer_not_mem_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem isSylowOf_top_of_forall_pow [Finite G] {p : ℕ} [Fact p.Prime] {R M : Subgroup G}
    (hR : IsSylowOf p R M)
    (hN : ∀ y ∈ Subgroup.normalizer (R : Set G), ∀ k : ℕ, y ^ p ^ k = 1 → y ∈ M) :
    IsSylowOf p R ⊤ := by
  obtain ⟨S, hRS⟩ := hR.isPGroup.exists_le_sylow
  have hRS' : R = S := by
    by_contra hne
    obtain ⟨y, hyS, hyR, hyN⟩ :=
      exists_mem_normalizer_not_mem_of_lt_of_isPGroup S.isPGroup' (lt_of_le_of_ne hRS hne)
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hyS⟩
    have hyM := hN y hyN k (by simpa using congrArg Subtype.val hk)
    have hQ : R ⊔ Subgroup.zpowers y = R :=
      hR.eq_of_le le_sup_left (sup_le hR.le (Subgroup.zpowers_le.mpr hyM))
        (S.isPGroup'.to_le (sup_le hRS (Subgroup.zpowers_le.mpr hyS)))
    exact hyR (hQ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hR.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, hRS']
  exact S.not_dvd_index

end General

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem Sec10Std.exists_conj_eq_of_card_eq_three (h : Sec10Std G A c L a R) {P Q : Subgroup G}
    (hPL : P ≤ L) (hQL : Q ≤ L) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) :
    ∃ x ∈ L, Q = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  exact exists_conj_eq_of_card_eq_three_of_quot
    (fun P Q hP hQ => KFacts.exists_conj_eq_of_card_eq_three_of_mulEquiv_psl2_27 e hP hQ)
    hPL hQL hP hQ

theorem Sec10Std.exists_conj_d_mem (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdo : orderOf d = 3) {y g : G}
    (hy : y ∈ sec10D c R L ⊓ L) (hg : g * y * g⁻¹ ∈ sec10D c R L) (hgL : g * y * g⁻¹ ∉ L) :
    ∃ g' : G, g' * d * g'⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧ g' * d * g'⁻¹ ∉ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdRL := h.d_mem_inf hdL
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  set u := g * y * g⁻¹ with hu
  have hu3 : u ^ 3 = 1 := h.isElemAbelian_D.2 u hg
  have hy3 : y ^ 3 = 1 := by
    have h1 := hu3
    rw [hu, conj_pow, conj_eq_one_iff] at h1
    exact h1
  have hy1 : y ≠ 1 := by
    intro hy1
    apply hgL
    rw [hu, hy1, mul_one, mul_inv_cancel]
    exact L.one_mem
  obtain ⟨n, -, hn⟩ := h.exists_conj_eq_of_card_eq_three (P := Subgroup.zpowers d)
    (Q := Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hdRL.2) (Subgroup.zpowers_le.mpr hy.2)
    (by rw [Nat.card_zpowers, hdo]) (by rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1])
  have hnd : n * d * n⁻¹ ∈ Subgroup.zpowers y := by
    rw [hn]
    exact ⟨d, Subgroup.mem_zpowers d, rfl⟩
  set g₁ := g * n with hg₁
  have hu1 : g₁ * d * g₁⁻¹ ∈ Subgroup.zpowers u := by
    rw [hu, ← map_conj_zpowers]
    refine ⟨n * d * n⁻¹, hnd, ?_⟩
    change g * (n * d * n⁻¹) * g⁻¹ = g₁ * d * g₁⁻¹
    rw [hg₁]
    group
  have hu1D : g₁ * d * g₁⁻¹ ∈ Subgroup.zpowers c ⊔ (R ⊓ L) := Subgroup.zpowers_le.mpr hg hu1
  have hu1ne : g₁ * d * g₁⁻¹ ≠ 1 := fun h1 => hd1 (conj_eq_one_iff.mp h1)
  have hu1L : g₁ * d * g₁⁻¹ ∉ L := fun h1 =>
    hu1ne ((Subgroup.disjoint_def.mp (disjoint_zpowers_of_pow_three hu3 hgL)) h1 hu1)
  obtain ⟨k, r, hr, hkr⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun x hx => h.commute_c_of_mem_inf hx) hu1D
  by_cases hr1 : r = 1
  · refine ⟨g₁, ?_, hu1L⟩
    rw [hkr, hr1, mul_one]
    exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k)
  ·
    have hr3 : r ^ 3 = 1 := h.isElemAbelian_inf.2 r hr
    obtain ⟨m, hmL, hm⟩ := h.exists_conj_eq_of_card_eq_three (P := Subgroup.zpowers r)
      (Q := Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hr.2) (Subgroup.zpowers_le.mpr hdRL.2)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hr3 hr1]) (by rw [Nat.card_zpowers, hdo])
    have hmr : m * r * m⁻¹ ∈ Subgroup.zpowers d := by
      rw [hm]
      exact ⟨r, Subgroup.mem_zpowers r, rfl⟩
    have hmc : m * c * m⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hmL),
        mul_inv_cancel_right]
    refine ⟨m * g₁, ?_, ?_⟩
    · have e1 : m * g₁ * d * (m * g₁)⁻¹ = (m * c * m⁻¹) ^ k * (m * r * m⁻¹) := by
        rw [conj_zpow]
        calc m * g₁ * d * (m * g₁)⁻¹ = m * (g₁ * d * g₁⁻¹) * m⁻¹ := by group
          _ = m * (c ^ k * r) * m⁻¹ := by rw [hkr]
          _ = m * c ^ k * m⁻¹ * (m * r * m⁻¹) := by group
      rw [e1, hmc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
        (Subgroup.mem_sup_right hmr)
    · intro h1
      apply hu1L
      have e2 : g₁ * d * g₁⁻¹ = m⁻¹ * (m * g₁ * d * (m * g₁)⁻¹) * m := by group
      rw [e2]
      exact L.mul_mem (L.mul_mem (L.inv_mem hmL) h1) hmL

theorem Sec10Std.conj_c_mem_sup (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hdo : orderOf d = 3)
    {y : G} (hyN : y ∈ Subgroup.normalizer (R : Set G)) :
    y * c * y⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, -, -⟩ := rank3II_10_2 h45 h97 G A c L a R h
  have hcA := h.mem_A
  have hcR : c ∈ R := h.A_le_R hcA
  have hc3 : c ^ 3 = 1 := h.pow_three hcA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hRc : ∀ r ∈ R, r * c = c * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hr)
  set z := y * c * y⁻¹ with hz
  have hzR : z ∈ R := (Subgroup.mem_normalizer_iff.mp hyN c).mp hcR
  have hz3 : z ^ 3 = 1 := by rw [hz, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hzc : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    have hr' : y⁻¹ * r * y ∈ R := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) r).mp hr
      simpa using h1
    have h1 := hRc _ hr'
    calc r * z = y * ((y⁻¹ * r * y) * c) * y⁻¹ := by rw [hz]; group
      _ = y * (c * (y⁻¹ * r * y)) * y⁻¹ := by rw [h1]
      _ = z * r := by rw [hz]; group
  have hΩeq : Subgroup.closure {x | x ∈ R ∧ x ^ 3 = 1} =
      Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) := by
    rw [hΩ, sec10D, hcl, ← sup_assoc, sup_comm (Subgroup.zpowers a), sup_assoc]
  have hTR : Subgroup.closure ({e, a} : Set G) ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact heRL.1
    · exact h.A_le_R h.a_mem
  have hzΩ : z ∈ Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) := by
    rw [← hΩeq]
    exact Subgroup.subset_closure ⟨hzR, hz3⟩
  obtain ⟨k, w, hw, hzw⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun x hx => hRc x (hTR hx)) hzΩ
  have hwC : w ∈ Subgroup.centralizer (Subgroup.closure ({e, a} : Set G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxR := hTR hx
    have hw' : w = c ^ (-k) * z := by rw [hzw]; group
    have hxc : x * c ^ (-k) = c ^ (-k) * x :=
      ((show Commute x c from hRc x hxR).zpow_right (-k)).eq
    rw [hw', ← mul_assoc, hxc, mul_assoc, hzc x hxR, ← mul_assoc]
  have hwx : w ∈ Subgroup.zpowers
      (KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2) := by
    rw [← hW.inf_centralizer_eq]
    exact Subgroup.mem_inf.mpr ⟨hw, hwC⟩
  have hdx : d ∈ Subgroup.zpowers
      (KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2) := by
    rw [← hW.inf_centralizer_eq]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hcl]
      exact Subgroup.mem_sup_right (h.d_mem_inf hdL)
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact h.d_commute_of_mem_R h45 hdL (hTR hx)
  obtain ⟨h01, h12, h02⟩ := KFacts.commute_eConj_two hW.pow_t hW.comm
  have hx3 : (KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2) ^ 3 = 1 := by
    rw [(h02.mul_left h12).mul_pow, h01.mul_pow,
      KFacts.eConj_pow_three hW.pow_e, KFacts.eConj_pow_three hW.pow_e,
      KFacts.eConj_pow_three hW.pow_e, one_mul, one_mul]
  have hx1 : KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2 ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hdx
    exact hd1 hdx
  have hxd : KFacts.eConj e a 0 * KFacts.eConj e a 1 * KFacts.eConj e a 2 ∈
      Subgroup.zpowers d :=
    KFacts.mem_zpowers_of_mem_zpowers_of_ne_one' (orderOf_eq_prime hx3 hx1) hdx hd1
  rw [hzw]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
    (Subgroup.mem_sup_right (Subgroup.zpowers_le.mpr hxd hwx))

theorem Sec10Std.mem_normalizer_zpowers_c_of_pow (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hdo : orderOf d = 3)
    (h103 : ∀ g : G, g * c * g⁻¹ ∉ L) {g₂ : G}
    (hv : g₂ * d * g₂⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (hvL : g₂ * d * g₂⁻¹ ∉ L)
    {y : G} {k : ℕ} (hyN : y ∈ Subgroup.normalizer (R : Set G)) (hy : y ^ 3 ^ k = 1) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, -, -⟩ := rank3II_10_2 h45 h97 G A c L a R h
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := h.pow_three hcA
  have hdA := h.d_mem_A hdL
  have hdRL := h.d_mem_inf hdL
  have hd3 : d ^ 3 = 1 := h.pow_three hdA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hdLe : Subgroup.zpowers d ≤ L := Subgroup.zpowers_le.mpr hdRL.2
  have hcd : c * d = d * c := h.comm hcA hdA
  have hyd : y ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    normalizer_le_normalizer_zpowers_of_omega
      (commutator_commutator_omega_eq h hdL hdo hΩ heRL hW hcl) hyN
  have hyd' : y * d * y⁻¹ = d := conj_eq_of_mem_normalizer_zpowers hy hd3 hd1 hyd
  have hyδ : ∀ δ ∈ Subgroup.zpowers d, y * δ * y⁻¹ = δ := by
    intro δ hδ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← conj_zpow, hyd']
  have hdc : ∀ x ∈ Subgroup.zpowers d, x * c = c * x := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute d c from hcd.symm) j)).eq
  obtain ⟨i, δ, hδ, hiδ⟩ := exists_zpow_mul_of_mem_sup_zpowers hdc
    (h.conj_c_mem_sup h45 h97 hdL hdo hyN)
  apply mem_normalizer_zpowers_of_conj_mem
  rcases zpow_cases_of_pow_three hc3 i with hi | hi | hi <;> rw [hi] at hiδ
  ·
    rw [one_mul] at hiδ
    have h1 : y * c * y⁻¹ ∈ Subgroup.zpowers d := by
      rw [hiδ]
      exact hδ
    exact absurd (hdLe h1) (h103 y)
  · by_cases hδ1 : δ = 1
    · rw [hiδ, hδ1, mul_one]
      exact Subgroup.mem_zpowers c
    ·
      exfalso
      have hδd : Subgroup.zpowers δ = Subgroup.zpowers d := zpowers_eq_of_mem_of_ne_one hdo hδ hδ1
      have hiter := conj_pow_iterate_eq hiδ (hyδ δ hδ)
      have hvd : g₂ * d * g₂⁻¹ ∉ Subgroup.zpowers d := fun h1 => hvL (hdLe h1)
      obtain ⟨m, δ', hδ', hm⟩ := exists_pow_eq_mul_of_mem_sup hc3 hcd hv hvd
      have hδ'δ : δ' ∈ Subgroup.zpowers δ := by
        rw [hδd]
        exact hδ'
      obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hδ'δ)
      have h1 : y ^ t * c * (y ^ t)⁻¹ = g₂ * d ^ m * g₂⁻¹ := by
        rw [hiter t, ht, ← hm, conj_pow]
      apply h103 (g₂⁻¹ * y ^ t)
      have h2 : g₂⁻¹ * y ^ t * c * (g₂⁻¹ * y ^ t)⁻¹ = d ^ m := by
        calc g₂⁻¹ * y ^ t * c * (g₂⁻¹ * y ^ t)⁻¹ = g₂⁻¹ * (y ^ t * c * (y ^ t)⁻¹) * g₂ := by
              group
          _ = d ^ m := by rw [h1]; group
      rw [h2]
      exact L.pow_mem hdRL.2 m
  ·
    have h2 : y ^ 2 * c * (y ^ 2)⁻¹ = c := by
      have hcδ : Commute (c ^ 2) δ := ((show Commute c δ from (hdc δ hδ).symm).pow_left 2)
      have hδ3 : δ ^ 3 = 1 := h.pow_three ((Subgroup.zpowers_le.mpr hdA) hδ)
      have hδδ : δ ^ 2 * δ = 1 := by
        rw [← pow_succ]
        exact hδ3
      calc y ^ 2 * c * (y ^ 2)⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by rw [sq]; group
        _ = y * (c ^ 2 * δ) * y⁻¹ := by rw [hiδ]
        _ = (y * c * y⁻¹) ^ 2 * (y * δ * y⁻¹) := by
            rw [conj_pow]
            group
        _ = (c ^ 2 * δ) ^ 2 * δ := by rw [hiδ, hyδ δ hδ]
        _ = c := by
            rw [hcδ.mul_pow, ← pow_mul, mul_assoc, hδδ, mul_one,
              show 2 * 2 = 3 + 1 by norm_num, pow_succ c 3, hc3, one_mul]
    rw [conj_eq_of_sq_conj_eq hy h2]
    exact Subgroup.mem_zpowers c

end Std

theorem rank3II_10_5 (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
      (R : Subgroup G), Sec10Std G A c L a R →
        ∀ y ∈ sec10D c R L ⊓ L, ∀ g : G, g * y * g⁻¹ ∈ sec10D c R L →
          g * y * g⁻¹ ∈ sec10D c R L ⊓ L := by
  intro G _ _ A c L a R h y hy g hg
  refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
  by_contra hgL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdL, hdo, -⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  have h103 := rank3II_10_3 h45 h97 G A c L a R h
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, -, -⟩ := rank3II_10_2 h45 h97 G A c L a R h
  obtain ⟨g₂, hv, hvL⟩ := h.exists_conj_d_mem hdL hdo hy hg hgL
  have hRsyl : IsSylowOf 3 R ⊤ := isSylowOf_top_of_forall_pow h.isSylowOf
    fun y hyN k hy => h.mem_normalizer_zpowers_c_of_pow h45 h97 hdL hdo h103 hv hvL hyN hy
  have hcA := h.mem_A
  have hRc : ∀ r ∈ R, r * c = c * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hr)
  have hZ : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer (R : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr hRc
    · exact Subgroup.mem_centralizer_iff.mpr fun r hr => h.d_commute_of_mem_R h45 hdL hr
  obtain ⟨P, hPR⟩ : ∃ P : Sylow 3 G, (P : Subgroup G) = R :=
    ⟨Sylow.ofCard R (by rw [hRsyl.card_eq, Subgroup.card_top]), Sylow.coe_ofCard _ _⟩
  subst hPR
  obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P d g₂⁻¹
    (hZ (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))) (by rw [inv_inv]; exact hZ hv)
  rw [inv_inv] at hn
  apply hvL
  have hn' : n⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    normalizer_le_normalizer_zpowers_of_omega
      (commutator_commutator_omega_eq h hdL hdo hΩ heRL hW hcl) (Subgroup.inv_mem _ hnN)
  have h1 : n⁻¹ * d * n⁻¹⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hn' d).mp (Subgroup.mem_zpowers d)
  rw [inv_inv] at h1
  rw [hn]
  exact Subgroup.zpowers_le.mpr (h.d_mem_inf hdL).2 h1

end CFSG.RankThree.PartTwo.Sec10
