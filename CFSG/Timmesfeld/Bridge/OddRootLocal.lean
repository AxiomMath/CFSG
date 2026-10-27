module

import CFSG.Timmesfeld.Bridge.OddLocalRoot
public import CFSG.Timmesfeld.Bridge.OddRootDefs

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp
  CFSG.Timmesfeld.Bridge.OddLocal CFSG.BenderSuzuki

variable {G : Type} [Group G] {D : Set G}

structure IsRootCompl (D : Set G) (d x : G) (C S : Subgroup G) : Prop where
  le : C ≤ rootGen D d x
  inf : C ⊓ Qof D d x = ⊥
  sup : C ⊔ Qof D d x = rootGen D d x
  S_le : S ≤ C
  S_root : ∀ s ∈ S, s ≠ 1 → s ∈ rootSet D d
  S_sylow : ∀ T : Subgroup G, S ≤ T → T ≤ C → IsPGroup 2 T → T = S

structure GoodCompl (D : Set G) (d x : G) (C S : Subgroup G) : Prop
    extends IsRootCompl D d x C S where
  x_mem : x ∈ C

theorem Qof_le_rootGen (d x : G) : Qof D d x ≤ rootGen D d x := by
  rintro g ⟨q, -, rfl⟩
  exact q.2

theorem isPGroup_Qof (d x : G) : IsPGroup 2 (Qof D d x) :=
  (CFSG.pCore_isPGroup (p := 2) (G := rootGen D d x)).map (rootGen D d x).subtype

theorem conj_mem_Qof (d x : G) {g q : G} (hg : g ∈ rootGen D d x) (hq : q ∈ Qof D d x) :
    g * q * g⁻¹ ∈ Qof D d x := by
  obtain ⟨q', hq', rfl⟩ := hq
  exact ⟨⟨g, hg⟩ * q' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem q' hq' ⟨g, hg⟩, rfl⟩

theorem rootGroup_le_rootGen (d x : G) : rootGroup D d ≤ rootGen D d x := by
  rw [rootGroup, Subgroup.closure_le]
  exact fun e he => mem_rootGen_of_mem he

theorem Wof_le_rootGroup (d x : G) : Wof D d x ≤ rootGroup D d :=
  inf_le_left

theorem Wof_le_Qof (d x : G) : Wof D d x ≤ Qof D d x :=
  inf_le_right

private theorem commute_of_mem_D_of_mem_pCore {X : Subgroup G} {P : Subgroup X} [P.Normal]
    (hD : IsOddTransp D) (hP : IsPGroup 2 P) {s z : G} (hsX : s ∈ X) (hzX : z ∈ X)
    (hsD : s ∈ D) (hzD : z ∈ D) (hsP : (⟨s, hsX⟩ : X) ∈ P) : Commute s z := by
  have hC : IsOddTransp (((↑) : X → G) ⁻¹' D) := IsOddTransp.preimage hD X
  have hcomm : Commute (⟨s, hsX⟩ : X) (⟨z, hzX⟩ : X) := by
    refine (commute_iff_of_mem_pCore (C := ((↑) : X → G) ⁻¹' D) hC hP
      (a := ⟨s, hsX⟩) hsD (b := ⟨z, hzX⟩) hzD).mp ?_
    have h1 : QuotientGroup.mk' P (⟨s, hsX⟩ : X) = 1 :=
      (QuotientGroup.eq_one_iff (N := P) _).mpr hsP
    rw [h1]
    exact Commute.one_left _
  simpa using hcomm.map X.subtype

theorem commute_of_mem_D_of_mem_Qof (hD : IsOddTransp D) {d x s : G} (hx : x ∈ D) (hs : s ∈ D)
    (hsQ : s ∈ Qof D d x) : ∀ y ∈ rootGen D d x, Commute s y := by
  have hsX : s ∈ rootGen D d x := Qof_le_rootGen d x hsQ
  obtain ⟨s', hs'P, hs'⟩ := hsQ
  have hmem : (⟨s, hsX⟩ : rootGen D d x) ∈ CFSG.pCore 2 (rootGen D d x) := by
    rw [show (⟨s, hsX⟩ : rootGen D d x) = s' from Subtype.ext hs'.symm]
    exact hs'P
  have hP := CFSG.pCore_isPGroup (p := 2) (G := rootGen D d x)
  have hxcomm : Commute s x :=
    commute_of_mem_D_of_mem_pCore hD hP hsX (mem_rootGen_left d x) hs hx hmem
  have hecomm : ∀ e ∈ rootSet D d, Commute s e := by
    intro e he
    exact commute_of_mem_D_of_mem_pCore hD hP hsX (mem_rootGen_of_mem he) hs he.1 hmem
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    rcases Set.mem_insert_iff.mp hz with h | hz
    · rw [h]; exact hxcomm
    · exact hecomm z hz
  | one => exact Commute.one_right s
  | mul a b ha hb iha ihb => exact iha.mul_right ihb
  | inv a ha iha => exact iha.inv_right

theorem not_mem_Qof_of_mem_rootSet (hD : IsOddTransp D) {d x s : G} (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hs : s ∈ rootSet D d) : s ∉ Qof D d x := by
  intro hsQ
  have h := commute_of_mem_D_of_mem_Qof hD hx hs.1 hsQ x (mem_rootGen_left d x)
  exact hdx ((hs.2 x hx).mp h)

theorem not_mem_Qof_self (hD : IsOddTransp D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) : d ∉ Qof D d x :=
  not_mem_Qof_of_mem_rootSet hD hx hdx (mem_rootSet_self hd)

private theorem mk_eq_of_mul_mem_Qof (hD : IsOddTransp D) {d x s t : G}
    (hsX : s ∈ rootGen D d x) (htX : t ∈ rootGen D d x) (ht : t ∈ D)
    (hst : s * t ∈ Qof D d x) :
    QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) =
      QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x) := by
  have hstX : s * t ∈ rootGen D d x := Qof_le_rootGen d x hst
  obtain ⟨q, hqP, hq⟩ := hst
  have hmem : (⟨s * t, hstX⟩ : rootGen D d x) ∈ CFSG.pCore 2 (rootGen D d x) := by
    rw [show (⟨s * t, hstX⟩ : rootGen D d x) = q from Subtype.ext hq.symm]
    exact hqP
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s * t, hstX⟩ : _) = 1 :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 (rootGen D d x)) _).mpr hmem
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : _) *
      QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : _) = 1 := by
    rw [← map_mul]
    simpa using h1
  have ht2 : QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : _) *
      QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : _) = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : rootGen D d x) * ⟨t, htX⟩ = 1 from
      Subtype.ext (by simpa using hD.mul_self_eq_one ht), map_one]
  calc QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x)
      = QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) * 1 := by
        rw [mul_one]
    _ = QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) *
          (QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x) *
           QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x)) := by
        rw [ht2, mul_one]
    _ = (QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨s, hsX⟩ : rootGen D d x) *
          QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x)) *
          QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x) := by
        group
    _ = QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x)) (⟨t, htX⟩ : rootGen D d x) := by
        rw [h2, one_mul]

theorem commute_of_mul_mem_Qof (hD : IsOddTransp D) {d x s t : G}
    (hsX : s ∈ rootGen D d x) (htX : t ∈ rootGen D d x) (hs : s ∈ D) (ht : t ∈ D)
    (hst : s * t ∈ Qof D d x) : Commute s t := by
  have hC : IsOddTransp (((↑) : rootGen D d x → G) ⁻¹' D) := IsOddTransp.preimage hD _
  have h := (commute_iff_of_mem_pCore (C := ((↑) : rootGen D d x → G) ⁻¹' D) hC
    (CFSG.pCore_isPGroup (p := 2) (G := rootGen D d x)) (a := ⟨s, hsX⟩) hs
    (b := ⟨t, htX⟩) ht)
  rw [mk_eq_of_mul_mem_Qof hD hsX htX ht hst] at h
  exact (h.mp (Commute.refl _)).map (rootGen D d x).subtype

theorem commute_iff_of_mul_mem_Qof (hD : IsOddTransp D) {d x s t z : G}
    (hsX : s ∈ rootGen D d x) (htX : t ∈ rootGen D d x) (hzX : z ∈ rootGen D d x)
    (hs : s ∈ D) (ht : t ∈ D) (hz : z ∈ D) (hst : s * t ∈ Qof D d x) :
    Commute z s ↔ Commute z t := by
  have hC : IsOddTransp (((↑) : rootGen D d x → G) ⁻¹' D) := IsOddTransp.preimage hD _
  have hP := CFSG.pCore_isPGroup (p := 2) (G := rootGen D d x)
  have h1 := (commute_iff_of_mem_pCore (C := ((↑) : rootGen D d x → G) ⁻¹' D) hC hP
    (a := ⟨z, hzX⟩) hz (b := ⟨s, hsX⟩) hs)
  have h2 := (commute_iff_of_mem_pCore (C := ((↑) : rootGen D d x → G) ⁻¹' D) hC hP
    (a := ⟨z, hzX⟩) hz (b := ⟨t, htX⟩) ht)
  rw [mk_eq_of_mul_mem_Qof hD hsX htX ht hst] at h1
  have e1 : Commute z s ↔ Commute (⟨z, hzX⟩ : rootGen D d x) ⟨s, hsX⟩ :=
    ⟨fun h => Subtype.ext (by simpa using h.eq), fun h => h.map (rootGen D d x).subtype⟩
  have e2 : Commute z t ↔ Commute (⟨z, hzX⟩ : rootGen D d x) ⟨t, htX⟩ :=
    ⟨fun h => Subtype.ext (by simpa using h.eq), fun h => h.map (rootGen D d x).subtype⟩
  exact e1.trans ((h1.symm.trans h2).trans e2.symm)

private theorem mul_self_mul_mem_Qof (hD : IsOddTransp D) {d x s t : G} (hs : s ∈ D)
    (ht : t ∈ D) (hst : s * t ∈ Qof D d x) : (s * t) * (s * t) = 1 := by
  rcases hD.2 s hs t ht with h2 | hodd
  · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · have h0 : s * t = 1 := orderOf_eq_one_iff.mp h1
      rw [h0, one_mul]
    · rw [← pow_two, ← h1]; exact pow_orderOf_eq_one _
  · obtain ⟨k, hk⟩ := isPGroup_Qof d x ⟨_, hst⟩
    have hk' : (s * t) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    rcases i with _ | i
    · have h0 : s * t = 1 := by
        rw [pow_zero] at hi
        exact orderOf_eq_one_iff.mp hi
      rw [h0, one_mul]
    · rw [hi, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.not_odd_iff_even])

theorem orderOf_mul_mul_eq_four (hD : IsOddTransp D) (hN : IsNormalSet D) {d x c c' : G}
    (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hc : c ∈ D)
    (hcX : c ∈ rootGen D d x) (hdc : ¬ Commute d c) (hc' : c' ∈ D)
    (hc'X : c' ∈ rootGen D d x) (hne : c' ≠ c) (hq : c' * c ∈ Qof D d x) :
    orderOf (c' * c * d) = 4 := by
  have hdX : d ∈ rootGen D d x := mem_rootGen_of_mem (mem_rootSet_self hd)
  have hq2 : (c' * c) * (c' * c) = 1 := mul_self_mul_mem_Qof hD hc' hc hq
  have hqinv : (c' * c)⁻¹ = c' * c := inv_eq_of_mul_eq_one_right hq2
  have hq_comm : Commute c' c := commute_of_mul_mem_Qof hD hc'X hcX hc' hc hq
  have hsq : (c' * c * d) ^ 2 ∈ Qof D d x := by
    have hqd : (c' * c * d) ^ 2 = (c' * c) * (d * (c' * c) * d) := by
      rw [pow_two]; group
    rw [hqd]
    exact (Qof D d x).mul_mem hq (by
      have h := conj_mem_Qof d x hdX hq
      rwa [hD.inv_eq hd] at h)
  have hw2 : ((c' * c * d) ^ 2) * ((c' * c * d) ^ 2) = 1 := by
    have hd'D : (c' * c) * d * (c' * c) ∈ D := by
      have h := hN (c' * c) d hd
      rwa [hqinv] at h
    have hconj : d * ((c' * c * d) ^ 2) * d⁻¹ = d * ((c' * c) * d * (c' * c)) := by
      rw [pow_two]; group
    have hord : orderOf ((c' * c * d) ^ 2) = orderOf (d * ((c' * c) * d * (c' * c))) := by
      rw [← hconj, orderOf_conj_eq]
    obtain ⟨k, hk⟩ := isPGroup_Qof d x ⟨_, hsq⟩
    have hk' : ((c' * c * d) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf (d * ((c' * c) * d * (c' * c))) ∣ 2 := by
      rcases hD.2 d hd _ hd'D with h | hodd
      · exact h
      · rw [← hord] at hodd
        have hdvd' : orderOf ((c' * c * d) ^ 2) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
        have h1 : orderOf ((c' * c * d) ^ 2) = 1 := by
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
          rcases i with _ | i
          · simpa using hi
          · rw [hi, pow_succ] at hodd
            exact absurd hodd (by simp [Nat.not_odd_iff_even])
        rw [← hord, h1]
        exact one_dvd 2
    rw [← hord] at hdvd
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have h4 : (c' * c * d) ^ 4 = 1 := by
    have h42 : (c' * c * d) ^ 4 = ((c' * c * d) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [h42]
    simpa [pow_two] using hw2
  have hne1 : orderOf (c' * c * d) ≠ 1 := by
    intro h1
    have h : c' * c * d = 1 := orderOf_eq_one_iff.mp h1
    have hdQ : d ∈ Qof D d x := by
      have h2 : d = c' * c := by
        calc d = (c' * c)⁻¹ * (c' * c * d) := by group
          _ = (c' * c)⁻¹ := by rw [h, mul_one]
          _ = c' * c := hqinv
      exact h2.symm ▸ hq
    exact not_mem_Qof_self hD hd hx hdx hdQ
  have hne2 : orderOf (c' * c * d) ≠ 2 := by
    intro h2
    have hsq1 : (c' * c * d) * (c' * c * d) = 1 := by
      rw [← pow_two, ← h2]; exact pow_orderOf_eq_one _
    have hcomm : Commute d (c' * c) := by
      have h' : (d * (c' * c)) * (d * (c' * c)) = 1 := by
        calc (d * (c' * c)) * (d * (c' * c))
            = (c' * c)⁻¹ * ((c' * c * d) * (c' * c * d)) * (c' * c) := by
                group
          _ = 1 := by rw [hsq1]; simp
      exact (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) hq2).mpr
        (by simpa [pow_two] using h')
    exact hdc ((hD.commute_mul_iff hc' hc hd hne hq_comm).mp hcomm).2
  have hdvd4 : orderOf (c' * c * d) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hdvd4' : orderOf (c' * c * d) ∣ 2 ^ 2 := by simpa using hdvd4
  obtain ⟨i, hi_le, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd4'
  rcases i with _ | i
  · exact absurd (by simpa using hi) hne1
  rcases i with _ | i
  · exact absurd (by simpa using hi) hne2
  · have : i = 0 := by omega
    subst this
    simpa using hi

theorem isTriangle_of_mul_mem_Qof (hD : IsOddTransp D) {d x c c' : G} (hd : d ∈ D)
    (hc : c ∈ D) (hdc : ¬ Commute d c) (hc' : c' ∈ D) (hcX : c ∈ rootGen D d x)
    (hc'X : c' ∈ rootGen D d x) (hne : c' ≠ c) (hq : c' * c ∈ Qof D d x) :
    IsTriangle D c' d c := by
  have hdX : d ∈ rootGen D d x := mem_rootGen_of_mem (mem_rootSet_self hd)
  refine ⟨hc', hc, hd, hne, commute_of_mul_mem_Qof hD hc'X hcX hc' hc hq, ?_,
    fun h => hdc h.symm⟩
  intro hconj
  exact hdc ((commute_iff_of_mul_mem_Qof hD hc'X hcX hdX hc' hc hd hq).mp hconj.symm)

theorem not_isThirdKind_of_mul_mem_Qof (hD : IsOddTransp D) {d x c c' y : G}
    (hc' : c' ∈ D) (hc : c ∈ D) (hy : y ∈ D) (hyX : y ∈ rootGen D d x)
    (hq : c' * c ∈ Qof D d x) : ¬ IsThirdKind c' y c := by
  rintro ⟨m, hm_odd, hm1, hord⟩
  have hq2 : (c' * c) * (c' * c) = 1 := mul_self_mul_mem_Qof hD hc' hc hq
  have hqinv : (c' * c)⁻¹ = c' * c := inv_eq_of_mul_eq_one_right hq2
  have hsq : (c' * c * y) ^ 2 ∈ Qof D d x := by
    have h1 : (c' * c * y) ^ 2 = (c' * c) * (y * (c' * c) * y) := by
      rw [pow_two]; group
    rw [h1]
    exact (Qof D d x).mul_mem hq (by
      have h := conj_mem_Qof d x hyX hq
      rwa [hD.inv_eq hy] at h)
  obtain ⟨k, hk⟩ := isPGroup_Qof d x ⟨_, hsq⟩
  have hk' : ((c' * c * y) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf (c' * c * y) ∣ 2 ^ (k + 1) := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ'], pow_mul]
    exact hk'
  rw [hord, pow_succ'] at hdvd
  have hm_dvd : m ∣ 2 ^ k := (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm_dvd
  rcases i with _ | i
  · rw [hi] at hm1; exact absurd hm1 (by norm_num)
  · rw [hi, pow_succ] at hm_odd
    exact absurd hm_odd (by simp [Nat.not_odd_iff_even])

end CFSG.Timmesfeld.Bridge.OddRoot
