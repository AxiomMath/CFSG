module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Type
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {S : Type} [Group S] [Finite S] {c : S} {L : Subgroup S}

theorem LocalDatum.card_dvd_centralizer (h : LocalDatum S c L) :
    Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ Nat.card (Subgroup.centralizer ({c} : Set S)) :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.le_centralizer)

theorem LocalDatum.card_dvd (h : LocalDatum S c L) :
    Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ Nat.card S :=
  h.card_dvd_centralizer.trans (Subgroup.card_subgroup_dvd_card _)

theorem LocalDatum.twentySeven_dvd (h : LocalDatum S c L) : 27 ∣ Nat.card S :=
  (IsType198.twentySeven_dvd h.quasisimple h.type).trans h.card_dvd

private theorem commutator_eq_one_of_comm {x y : S} (hxy : x * y = y * x) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  rw [hxy]
  group

theorem LocalDatum.le_of_commutator_le (h : LocalDatum S c L) {H : Subgroup S}
    (hH : ∀ x ∈ Subgroup.centralizer ({c} : Set S), ∀ y ∈ Subgroup.centralizer ({c} : Set S),
      x * y * x⁻¹ * y⁻¹ ∈ H) : L ≤ H := by
  haveI := h.perfect
  calc L = ⁅L, L⁆ := (Subgroup.commutator_eq_self (H := L)).symm
    _ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact hH a (h.le_centralizer ha) b (h.le_centralizer hb)

private theorem LocalDatum.ne_one (h : LocalDatum S c L) : c ≠ 1 := by
  rintro rfl
  have := h.orderOf_eq
  rw [orderOf_one] at this
  omega

private theorem LocalDatum.centralizer_ne_top (hS : IsSimpleGroup S) (h : LocalDatum S c L) :
    Subgroup.centralizer ({c} : Set S) ≠ ⊤ := by
  haveI := hS
  intro htop
  have hcen : c ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({c} : Set S) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hne : Subgroup.center S ≠ ⊥ := fun hb => h.ne_one (by simpa [hb] using hcen)
  have htopc : Subgroup.center S = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S)).resolve_left hne
  haveI : IsMulCommutative S := Subgroup.center_eq_top_iff.mp htopc
  have hL : L ≤ ⊥ :=
    h.le_of_commutator_le (H := ⊥) fun x _ y _ =>
      Subgroup.mem_bot.mpr (commutator_eq_one_of_comm (mul_comm' x y))
  exact h.ne_one (Subgroup.mem_bot.mp (hL h.mem))

theorem LocalDatum.five_mul_le (hS : IsSimpleGroup S) (h : LocalDatum S c L) :
    5 * Nat.card (L ⧸ aschbacherSolvableCore 3 L) ≤ Nat.card S := by
  haveI := hS
  have hT : 7560 ≤ Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
    IsType198.le_card h.quasisimple h.type
  have hTS : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ≤ Nat.card S :=
    Nat.le_of_dvd Nat.card_pos h.card_dvd
  have hcore : (Subgroup.centralizer ({c} : Set S)).normalCore = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.centralizer ({c} : Set S)).normalCore with
      hb | ht
    · exact hb
    · exact absurd (top_le_iff.mp (ht ▸ Subgroup.normalCore_le _)) (h.centralizer_ne_top hS)
  have hfact : Nat.card S ≤ Nat.factorial (Subgroup.centralizer ({c} : Set S)).index := by
    have := Subgroup.index_normalCore_le_factorial_index (Subgroup.centralizer ({c} : Set S))
    rwa [hcore, Subgroup.index_bot] at this
  have hindex : 5 ≤ (Subgroup.centralizer ({c} : Set S)).index := by
    by_contra hlt
    push Not at hlt
    have h4 : Nat.factorial (Subgroup.centralizer ({c} : Set S)).index ≤ Nat.factorial 4 :=
      Nat.factorial_le (by omega)
    have h24 : Nat.factorial 4 = 24 := by decide
    omega
  have hTH : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ≤
      Nat.card (Subgroup.centralizer ({c} : Set S)) :=
    Nat.le_of_dvd Nat.card_pos h.card_dvd_centralizer
  calc 5 * Nat.card (L ⧸ aschbacherSolvableCore 3 L)
      ≤ (Subgroup.centralizer ({c} : Set S)).index *
          Nat.card (Subgroup.centralizer ({c} : Set S)) := Nat.mul_le_mul hindex hTH
    _ = Nat.card S := Subgroup.index_mul_card _

private theorem exists_lift (L : Subgroup S) (Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L))
    (hQ : IsPGroup 3 Q) :
    ∃ P : Subgroup S, P ≤ L ∧ IsPGroup 3 P ∧ Nonempty (P ≃* Q) := by
  have hker : Nat.Coprime 3
      (Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  obtain ⟨lift, hlift, ⟨e⟩⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3 Nat.prime_three
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (QuotientGroup.mk'_surjective _) hker Q hQ
  exact ⟨lift.map L.subtype, Subgroup.map_subtype_le lift, hlift.map L.subtype,
    ⟨(lift.equivMapOfInjective L.subtype L.subtype_injective).symm.trans e⟩⟩

theorem LocalDatum.exists_elemAbelian (h : LocalDatum S c L) :
    ∃ B : Subgroup S, B ≤ L ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  obtain ⟨E, hE, hE9⟩ := IsType198.exists_elemAbelian h.quasisimple h.type
  obtain ⟨P, hPL, -, ⟨e⟩⟩ := exists_lift L E hE.isPGroup
  exact ⟨P, hPL,
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 3 E P e.symm hE,
    (Nat.card_congr e.toEquiv).trans hE9⟩

theorem LocalDatum.exists_nonabelian (h : LocalDatum S c L) :
    ∃ P : Subgroup S, P ≤ L ∧ IsPGroup 3 P ∧ ¬ IsMulCommutative P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (L ⧸ aschbacherSolvableCore 3 L)) := inferInstance
  obtain ⟨P, hPL, hP, ⟨e⟩⟩ := exists_lift L (Q : Subgroup _) Q.isPGroup'
  refine ⟨P, hPL, hP, fun hcomm => IsType198.not_isMulCommutative_sylow h.quasisimple h.type Q ?_⟩
  rw [isMulCommutative_iff] at hcomm ⊢
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hcomm _ _

private theorem exists_prime_of_coprime_thirty {m : ℕ} (h7 : 7 ≤ m) (h2 : m % 2 = 1)
    (h3 : m % 3 ≠ 0) (h5 : m % 5 ≠ 0) : ∃ r, r.Prime ∧ 7 ≤ r ∧ r ∣ m := by
  have hm1 : m ≠ 1 := by omega
  have hp : m.minFac.Prime := Nat.minFac_prime hm1
  have hd : m.minFac ∣ m := Nat.minFac_dvd m
  refine ⟨m.minFac, hp, ?_, hd⟩
  by_contra hlt
  push Not at hlt
  have h2le := hp.two_le
  generalize m.minFac = r at hp hd hlt h2le
  interval_cases r
  · omega
  · omega
  · exact absurd hp (by norm_num)
  · omega
  · exact absurd hp (by norm_num)

private theorem exists_prime_dvd_aux {j : ℕ} (hj : 1 ≤ j) :
    ∃ r, r.Prime ∧ 7 ≤ r ∧ r ∣ 3 * (j * (j + 1)) + 1 := by
  apply exists_prime_of_coprime_thirty
  · have : 2 ≤ j * (j + 1) := by nlinarith
    omega
  · obtain ⟨t, ht⟩ := Nat.even_mul_succ_self j
    rw [ht]
    omega
  · omega
  · have key : ∀ r : ℕ, r < 5 → (3 * (r * (r + 1)) + 1) % 5 ≠ 0 := by decide
    have hj5 : j ≡ j % 5 [MOD 5] := (Nat.mod_modEq j 5).symm
    have hmod : 3 * (j * (j + 1)) + 1 ≡ 3 * ((j % 5) * ((j % 5) + 1)) + 1 [MOD 5] :=
      ((hj5.mul (hj5.add_right 1)).mul_left 3).add_right 1
    rw [hmod]
    exact key _ (Nat.mod_lt _ (by norm_num))

private theorem card_M22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  have h3 := Nat.card_congr e.toEquiv
  omega

theorem IsType198Card.exists_prime (N : ℕ) (hN : IsType198Card N) :
    ∃ r, r.Prime ∧ 7 ≤ r ∧ r ∣ N := by
  rcases hN with ⟨p, k, hp, hk, h3, rfl⟩ | ⟨p, k, hp, hk, h3, h2, rfl⟩ | rfl | rfl
  · obtain ⟨q, hq⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hq] at h3 ⊢
    have hq2 : 2 ≤ q := hq ▸ hp.two_le.trans (Nat.le_self_pow (by omega) p)
    obtain ⟨j, rfl⟩ : ∃ j, q = 3 * j + 1 := ⟨q / 3, by omega⟩
    obtain ⟨r, hr, hr7, hrd⟩ := exists_prime_dvd_aux (j := j) (by omega)
    refine ⟨r, hr, hr7, ?_⟩
    have hsub : (3 * j + 1) ^ 3 - 1 = 9 * j * (3 * (j * (j + 1)) + 1) := by
      have : (3 * j + 1) ^ 3 = 9 * j * (3 * (j * (j + 1)) + 1) + 1 := by ring
      omega
    rw [hsub]
    exact (hrd.mul_left (9 * j)).mul_left _
  · obtain ⟨q, hq⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hq] at h2 h3 ⊢
    obtain ⟨j, rfl⟩ : ∃ j, q = 3 * j + 2 := ⟨q / 3, by omega⟩
    obtain ⟨r, hr, hr7, hrd⟩ := exists_prime_dvd_aux (j := j) (by omega)
    refine ⟨r, hr, hr7, ?_⟩
    have hadd : (3 * j + 2) ^ 3 + 1 = 9 * (j + 1) * (3 * (j * (j + 1)) + 1) := by ring
    rw [hadd]
    exact (hrd.mul_left (9 * (j + 1))).mul_left _
  · exact ⟨7, by norm_num, le_refl _, by norm_num⟩
  · rw [card_M22]
    exact ⟨7, by norm_num, le_refl _, by norm_num⟩

theorem IsType198Card.le (N : ℕ) (hN : IsType198Card N) : 7560 ≤ N := by
  rcases hN with ⟨p, k, hp, hk, h3, hN⟩ | ⟨p, k, hp, hk, h3, h2, hN⟩ | hN | hN
  · have hq2 : 2 ≤ p ^ k := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hqdef] at hq2 h3 hN
    have hq4 : 4 ≤ q := by omega
    have h1 : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    have h4 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have h5 : 63 ≤ q ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h4) h5
    omega
  · obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hqdef] at h2 h3 hN
    have hq5 : 5 ≤ q := by omega
    have h1 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
    have h4 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
      omega
    have h5 : 126 ≤ q ^ 3 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h4) h5
    omega
  · omega
  · rw [hN, card_M22]
    norm_num

theorem noLocalDatum_of_not_dvd (h : ¬ 27 ∣ Nat.card S) : NoLocalDatum S :=
  fun _ _ hLD => h hLD.twentySeven_dvd

theorem noLocalDatum_of_card (hS : IsSimpleGroup S)
    (h : ∀ N, IsType198Card N → N ∣ Nat.card S → 5 * N ≤ Nat.card S → False) :
    NoLocalDatum S := fun _ _ hLD =>
  h _ (IsType198.card_cases hLD.quasisimple hLD.type) hLD.card_dvd (hLD.five_mul_le hS)

theorem noLocalDatum_of_centralizer (h : ∀ c : S, orderOf c = 3 → ∀ N, IsType198Card N →
    ¬ N ∣ Nat.card (Subgroup.centralizer ({c} : Set S))) : NoLocalDatum S :=
  fun c _ hLD =>
    h c hLD.orderOf_eq _ (IsType198.card_cases hLD.quasisimple hLD.type) hLD.card_dvd_centralizer

theorem noLocalDatum_of_primes (h : ∀ r, r.Prime → r ∣ Nat.card S → r ≤ 5) : NoLocalDatum S := by
  intro c L hLD
  obtain ⟨r, hr, hr7, hrd⟩ :=
    IsType198Card.exists_prime _ (IsType198.card_cases hLD.quasisimple hLD.type)
  have := h r hr (hrd.trans hLD.card_dvd)
  omega

end CFSG.RankThree.PartTwo.Sec19.SimsC198
