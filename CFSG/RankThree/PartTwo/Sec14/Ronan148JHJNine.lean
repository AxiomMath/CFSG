module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJExcl
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo Equiv

@[expose] def NoNine3 (W : Type*) [Group W] : Prop :=
  9 ∣ Nat.card W ∧ ∀ x : W, x ^ 9 = 1 → x ^ 3 = 1

theorem noNine_congr {W W' : Type*} [Group W] [Group W'] (e : W ≃* W') (h : NoNine3 W) :
    NoNine3 W' := by
  refine ⟨Nat.card_congr e.toEquiv ▸ h.1, fun x hx => ?_⟩
  have h1 : (e.symm x) ^ 9 = 1 := by rw [← map_pow, hx, map_one]
  have h2 := h.2 _ h1
  have h3 : e ((e.symm x) ^ 3) = 1 := by rw [h2, map_one]
  rwa [map_pow, MulEquiv.apply_symm_apply] at h3

theorem noNine_alternating_five_sq :
    NoNine3 (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have key : ∀ y : alternatingGroup (Fin 5), y ^ 9 = 1 → y ^ 3 = 1 := by
    intro y hy
    have h1 : orderOf y ∣ Nat.gcd 9 60 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (h60 ▸ orderOf_dvd_natCard y)
    exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using h1)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Nat.card_prod, h60]
    norm_num
  · have h1 : x.1 ^ 9 = 1 := by simpa using congrArg Prod.fst hx
    have h2 : x.2 ^ 9 = 1 := by simpa using congrArg Prod.snd hx
    exact Prod.ext (by simpa using key _ h1) (by simpa using key _ h2)

theorem perm_seven_pow_three_of_pow_nine :
    ∀ σ : Perm (Fin 7), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  intro σ hσ
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro b hb
  have h9 : b ∣ 9 := (Perm.dvd_of_mem_cycleType hb).trans (orderOf_dvd_of_pow_eq_one hσ)
  have h2 := Perm.two_le_of_mem_cycleType hb
  have h7 : b ≤ 7 := (Perm.le_card_support_of_mem_cycleType hb).trans
    ((Finset.card_le_univ _).trans (by simp))
  have hb9 : b ≤ 9 := Nat.le_of_dvd (by norm_num) h9
  interval_cases b <;> simp_all

theorem noNine_alternatingGroup_seven : NoNine3 (alternatingGroup (Fin 7)) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  · apply Subtype.ext
    have h1 : (x : Perm (Fin 7)) ^ 9 = 1 := by simpa using congrArg Subtype.val hx
    simpa using perm_seven_pow_three_of_pow_nine _ h1

variable {Γ : Type} [Group Γ]

theorem pow_three_eq_one_of_pow_three_pow {Z : Subgroup Γ}
    (hexp : ∀ x ∈ Z, x ^ 9 = 1 → x ^ 3 = 1) {x : Γ} (hx : x ∈ Z) :
    ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  intro m
  induction m with
  | zero =>
    intro h
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | succ m ih =>
    intro h
    rcases m with _ | m
    · simpa using h
    · apply ih
      have hy : x ^ 3 ^ m ∈ Z := Subgroup.pow_mem _ hx _
      have h9 : (x ^ 3 ^ m) ^ 9 = 1 := by
        rw [← pow_mul, show 3 ^ m * 9 = 3 ^ (m + 1 + 1) by ring]
        exact h
      have := hexp _ hy h9
      rwa [← pow_mul, show 3 ^ m * 3 = 3 ^ (m + 1) by ring] at this

theorem false_of_exp_three_of_le [Finite Γ] {Aq C E Z : Subgroup Γ}
    (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (Aq : Set Γ) → w ^ 3 = 1 → w ∈ Aq)
    (hC3 : Nat.card C = 3) (hAeq : C ⊔ E = Aq)
    (hEZ : E ≤ Subgroup.centralizer (Z : Set Γ)) (hAZ : Aq ⊓ Z ≤ C)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Γ)) (h9 : 9 ∣ Nat.card Z)
    (hexp : ∀ x ∈ Z, x ^ 9 = 1 → x ^ 3 = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hkZ, hk1, hk3, hkA⟩ :=
    exists_pow_eq_one_mem_centralizer hAp hAN (dvd_trans (by norm_num) h9)
  have hkC : k ∈ C := hAZ ⟨hF3 k hkA hk3, hkZ⟩
  have hCk : Subgroup.zpowers k = C := zpowers_eq_of_card_three hC3 hkC hk1
  have hcomm : ∀ y ∈ Z, y ^ 3 = 1 → y * k = k * y → y ∈ Subgroup.zpowers k := by
    intro y hy hy3 hyk
    have hle : Aq ≤ Subgroup.centralizer ({y} : Set Γ) := by
      rw [← hAeq]
      refine sup_le ?_ fun e he => ?_
      · rw [← hCk, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hyk.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hEZ he) y hy).symm
    have hyA : y ∈ Subgroup.centralizer (Aq : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    have := hAZ ⟨hF3 y hyA hy3, hy⟩
    rwa [← hCk] at this
  set k' : ↥Z := ⟨k, hkZ⟩ with hk'
  have hk'3 : k' ^ 3 = 1 := Subtype.ext (by simpa [hk'] using hk3)
  have hk'1 : k' ≠ 1 := fun h => hk1 (by simpa [hk'] using congrArg Subtype.val h)
  have hk'ord : orderOf k' = 3 := orderOf_eq_prime hk'3 hk'1
  have hk'p : IsPGroup 3 (Subgroup.zpowers k') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk'ord, pow_one])
  obtain ⟨P, hPk⟩ := hk'p.exists_le_sylow
  have hk'P : k' ∈ (P : Subgroup ↥Z) := hPk (Subgroup.mem_zpowers k')
  have hP9 : 3 ^ 2 ∣ Nat.card (P : Subgroup ↥Z) :=
    P.pow_dvd_card_of_pow_dvd_card (by simpa using h9)
  have hPexp : ∀ y ∈ (P : Subgroup ↥Z), ((y : Γ)) ^ 3 = 1 := by
    intro y hy
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨y, hy⟩
    refine pow_three_eq_one_of_pow_three_pow hexp y.2 m ?_
    simpa using congrArg (fun t : ↥(P : Subgroup ↥Z) => ((t : ↥Z) : Γ)) hm
  obtain ⟨y, hyP, hyk, hyn⟩ : ∃ y ∈ (P : Subgroup ↥Z), y * k' = k' * y ∧
      y ∉ Subgroup.zpowers k' := by
    by_cases hc : ∀ p ∈ (P : Subgroup ↥Z), p * k' = k' * p
    · have hnot : ¬ (P : Subgroup ↥Z) ≤ Subgroup.zpowers k' := fun hle => by
        have h1 := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, hk'ord] at h1
        have h2 := Nat.le_of_dvd Nat.card_pos hP9
        omega
      obtain ⟨y, hyP, hyn⟩ := Set.not_subset.mp hnot
      exact ⟨y, hyP, hc y hyP, hyn⟩
    · push Not at hc
      obtain ⟨p0, hp0P, hp0⟩ := hc
      haveI : Nontrivial ↥(P : Subgroup ↥Z) :=
        ⟨⟨⟨k', hk'P⟩, 1, fun h => hk'1 (congrArg Subtype.val h)⟩⟩
      haveI := P.isPGroup'.center_nontrivial
      obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup ↥Z))
      set zP : ↥(P : Subgroup ↥Z) := (z : ↥(P : Subgroup ↥Z)) with hzP
      have hzc : ∀ q : ↥(P : Subgroup ↥Z), q * zP = zP * q := fun q =>
        (Subgroup.mem_center_iff.mp z.2) q
      refine ⟨(zP : ↥Z), zP.2, ?_, fun hzk => ?_⟩
      · exact (congrArg Subtype.val (hzc ⟨k', hk'P⟩)).symm
      ·
        apply hp0
        have hz3 : (zP : ↥Z) ^ 3 = 1 := Subtype.ext (by simpa using hPexp _ zP.2)
        have hzne : (zP : ↥Z) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
        have hcard : Nat.card (Subgroup.zpowers k') = 3 := by rw [Nat.card_zpowers, hk'ord]
        have hzz : Subgroup.zpowers (zP : ↥Z) = Subgroup.zpowers k' :=
          zpowers_eq_of_card_three hcard hzk hzne
        have hkz : k' ∈ Subgroup.zpowers (zP : ↥Z) := hzz ▸ Subgroup.mem_zpowers k'
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkz
        have hc' := hzc ⟨p0, hp0P⟩
        have hcn : (⟨p0, hp0P⟩ : ↥(P : Subgroup ↥Z)) * zP ^ n = zP ^ n * ⟨p0, hp0P⟩ :=
          (Commute.zpow_right hc' n).eq
        have := congrArg Subtype.val hcn
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at this
        rw [hn] at this
        exact this
  have hy3 : ((y : Γ)) ^ 3 = 1 := hPexp y hyP
  have hyk' : (y : Γ) * k = k * y := by simpa [hk'] using congrArg Subtype.val hyk
  have hyz := hcomm (y : Γ) y.2 hy3 hyk'
  apply hyn
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyz
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [hk'] using hn)⟩

theorem noNine_subgroup {Z : Subgroup Γ} (h : NoNine3 ↥Z) :
    9 ∣ Nat.card Z ∧ ∀ x ∈ Z, x ^ 9 = 1 → x ^ 3 = 1 := by
  refine ⟨h.1, fun x hx h9 => ?_⟩
  have h1 : (⟨x, hx⟩ : ↥Z) ^ 9 = 1 := Subtype.ext (by simpa using h9)
  simpa using congrArg Subtype.val (h.2 _ h1)

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
