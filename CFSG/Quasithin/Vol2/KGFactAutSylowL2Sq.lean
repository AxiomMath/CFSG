module

public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SteinbergBR.OddSylow
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)

open DihedralGroup in
theorem dihedral_normalizer_sylow_le {m : ℕ} [NeZero m] (P : Sylow 2 (DihedralGroup m)) :
    Subgroup.normalizer (P : Set (DihedralGroup m)) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ g ∈ Subgroup.normalizer (P : Set (DihedralGroup m)), (∃ a : ℕ, g ^ 2 ^ a = 1) →
      g ∈ P := by
    rintro g hg ⟨a, ha⟩
    have hK : IsPGroup 2 (Subgroup.zpowers g) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set (DihedralGroup m)) :=
      (Subgroup.zpowers_le).mpr hg
    have heq := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' hK hle) le_sup_left
    show g ∈ (P : Subgroup (DihedralGroup m))
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  obtain ⟨i, hi⟩ : ∃ i : ZMod m, sr i ∈ P := by
    by_contra hne
    have hle : (P : Subgroup (DihedralGroup m)) ≤ Subgroup.zpowers (r 1) := by
      intro x hx
      cases x with
      | r j =>
        exact Subgroup.mem_zpowers_iff.mpr
          ⟨(j.val : ℤ), by rw [zpow_natCast, r_one_pow, ZMod.natCast_zmod_val]⟩
      | sr j => exact absurd ⟨j, hx⟩ hne
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, orderOf_r_one, P.card_eq_multiplicity, DihedralGroup.nat_card,
      Nat.factorization_mul two_ne_zero (NeZero.ne m), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, add_comm] at h1
    exact Nat.pow_succ_factorization_not_dvd (NeZero.ne m) Nat.prime_two h1
  have hrot : ∀ k : ZMod m, r k ∈ Subgroup.normalizer (P : Set (DihedralGroup m)) → r k ∈ P := by
    intro k hk
    refine key _ hk ?_
    have h1 : r k * sr i * (r k)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hk (sr i)).mp hi
    have h2 : sr i * (r k * sr i * (r k)⁻¹) ∈ P := P.mul_mem hi h1
    have h3 : sr i * (r k * sr i * (r k)⁻¹) = (r k ^ 2)⁻¹ := by
      simp only [r_mul_sr, sr_mul_r, sr_mul_sr, inv_r, sq, r_mul_r]
      congr 1
      ring
    rw [h3] at h2
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨_, h2⟩
    refine ⟨a + 1, ?_⟩
    have ha' : ((r k ^ 2)⁻¹) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    rw [inv_pow, inv_eq_one] at ha'
    rw [pow_succ', pow_mul]
    exact ha'
  intro g hg
  cases g with
  | r k => exact hrot k hg
  | sr k =>
    have hiN : sr i ∈ Subgroup.normalizer (P : Set (DihedralGroup m)) := Subgroup.le_normalizer hi
    have h1 := Subgroup.mul_mem _ hg hiN
    rw [sr_mul_sr] at h1
    have h3 : sr k = r (i - k) * sr i := by
      rw [r_mul_sr]
      congr 1
      ring
    rw [h3]
    exact P.mul_mem (hrot _ h1) hi

theorem normalizer_sylow_le_of_dihedral {C : Type*} [Group C] {m : ℕ} [NeZero m]
    (e : C ≃* DihedralGroup m) (P : Sylow 2 C) : Subgroup.normalizer (P : Set C) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_eq_of_injective P (f := e.toMonoidHom) e.injective
  have hmem : ∀ x : C, x ∈ (P : Subgroup C) ↔ e x ∈ (Q : Subgroup (DihedralGroup m)) := by
    intro x
    rw [← hQ]
    rfl
  intro g hg
  rw [hmem]
  apply dihedral_normalizer_sylow_le Q
  have hg' := Subgroup.mem_normalizer_iff.mp hg
  refine Subgroup.mem_normalizer_iff.mpr fun d => ?_
  obtain ⟨c, rfl⟩ := e.surjective d
  rw [← hmem, ← map_inv, ← map_mul, ← map_mul, ← hmem]
  exact hg' c

theorem psl2_normalizer_sylow_le {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (h8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7)
    (S : Sylow 2 (PSL2 K)) : Subgroup.normalizer (S : Set (PSL2 K)) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, ⟨eS⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd S
  have hcardS : Nat.card S = 2 * 2 ^ m :=
    (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have h8G : 2 ^ 3 ∣ Nat.card (PSL2 K) := by
    rw [CFSG.GorensteinWalter.psl2_card_formula K hodd]
    rcases h8 with h8 | h8
    · obtain ⟨t, ht⟩ : ∃ t, Nat.card K = 8 * t + 1 := ⟨Nat.card K / 8, by omega⟩
      rw [ht]
      have h1 : (8 * t + 1) ^ 2 - 1 = 16 * (t * (4 * t + 1)) := by
        have h : (8 * t + 1) ^ 2 = 16 * (t * (4 * t + 1)) + 1 := by ring
        omega
      rw [h1, show (8 * t + 1) * (16 * (t * (4 * t + 1))) =
        2 * (2 ^ 3 * ((8 * t + 1) * (t * (4 * t + 1)))) by ring, Nat.mul_div_cancel_left _ two_pos]
      exact dvd_mul_right _ _
    · obtain ⟨t, ht⟩ : ∃ t, Nat.card K = 8 * t + 7 := ⟨Nat.card K / 8, by omega⟩
      rw [ht]
      have h1 : (8 * t + 7) ^ 2 - 1 = 16 * (4 * t ^ 2 + 7 * t + 3) := by
        have h : (8 * t + 7) ^ 2 = 16 * (4 * t ^ 2 + 7 * t + 3) + 1 := by ring
        omega
      rw [h1, show (8 * t + 7) * (16 * (4 * t ^ 2 + 7 * t + 3)) =
        2 * (2 ^ 3 * ((8 * t + 7) * (4 * t ^ 2 + 7 * t + 3))) by ring,
        Nat.mul_div_cancel_left _ two_pos]
      exact dvd_mul_right _ _
  have hm2 : 2 ≤ m := by
    have h1 : 2 ^ 3 ∣ Nat.card S := by
      rw [S.card_eq_multiplicity]
      exact Nat.pow_dvd_pow 2
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h8G)
    rw [hcardS] at h1
    by_contra hlt
    interval_cases m <;> norm_num at h1
  set P : Subgroup (PSL2 K) := (S : Subgroup (PSL2 K)) with hP
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hZ : Nat.card (Subgroup.center ↥P) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr eS).toEquiv).trans
      (CFSG.Walter.card_center_dihedralGroup h4 (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥P)).mp hZ
  set u : PSL2 K := (((y : ↥P)) : PSL2 K) with hu
  have hu1 : u ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have huP : u ∈ P := (y : ↥P).2
  have hucomm : ∀ q ∈ P, q * u = u * q := by
    intro q hq
    have := Subgroup.mem_center_iff.mp y.2 ⟨q, hq⟩
    exact congrArg Subtype.val this
  have hu2 : u * u = 1 := by
    by_contra hne
    have hyy : y * y ≠ 1 := fun h => hne (congrArg (fun z : ↥(Subgroup.center ↥P) =>
      ((z : ↥P) : PSL2 K)) h)
    have h1 : y * y = y := hyu _ hyy
    apply hy1
    exact mul_left_cancel (h1.trans (mul_one y).symm)
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hPC : P ≤ Subgroup.centralizer ({u} : Set (PSL2 K)) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hucomm q hq)
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set (PSL2 K)),
      n ∈ Subgroup.centralizer ({u} : Set (PSL2 K)) := by
    intro n hn
    have hn' := Subgroup.mem_normalizer_iff.mp hn
    have hv : n * u * n⁻¹ ∈ P := (hn' u).mp huP
    have hconj : ∀ q ∈ P, n⁻¹ * q * n ∈ P := fun q hq =>
      (hn' (n⁻¹ * q * n)).mpr (by simpa [mul_assoc] using hq)
    have hvc : ∀ q ∈ P, q * (n * u * n⁻¹) = (n * u * n⁻¹) * q := by
      intro q hq
      have h1 := hucomm _ (hconj q hq)
      calc q * (n * u * n⁻¹) = n * ((n⁻¹ * q * n) * u) * n⁻¹ := by group
        _ = n * (u * (n⁻¹ * q * n)) * n⁻¹ := by rw [h1]
        _ = (n * u * n⁻¹) * q := by group
    let c : ↥(Subgroup.center ↥P) :=
      ⟨⟨n * u * n⁻¹, hv⟩, Subgroup.mem_center_iff.mpr fun q => Subtype.ext (hvc q q.2)⟩
    have hc1 : c ≠ 1 := by
      intro h
      have h1 := congrArg (fun z : ↥(Subgroup.center ↥P) => ((z : ↥P) : PSL2 K)) h
      apply hu1
      have h2 : n * u * n⁻¹ = 1 := h1
      calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
        _ = 1 := by rw [h2]; group
    have hvu : n * u * n⁻¹ = u := congrArg (fun z : ↥(Subgroup.center ↥P) =>
      ((z : ↥P) : PSL2 K)) (hyu c hc1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * u = n * u * n⁻¹ * n := by group
      _ = u * n := by rw [hvu]
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    rcases h8 with h | h
    · exact ⟨1, by unfold Int.ModEq; omega, Or.inl rfl⟩
    · exact ⟨-1, by unfold Int.ModEq; omega, Or.inr rfl⟩
  obtain ⟨m', hm', ⟨eC⟩⟩ :=
    CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hodd hε hε1 hord
  have : NeZero m' := by
    refine ⟨fun h0 => ?_⟩
    obtain ⟨p, f, hp, -, hf, hq⟩ := hodd
    have h2 : 2 ≤ Nat.card K := by
      rw [hq]
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    rw [h0] at hm'
    rcases hε1 with rfl | rfl <;> omega
  let S' : Sylow 2 (Subgroup.centralizer ({u} : Set (PSL2 K))) := S.subtype hPC
  have hS'mem : ∀ x : Subgroup.centralizer ({u} : Set (PSL2 K)),
      x ∈ (S' : Subgroup _) ↔ (x : PSL2 K) ∈ P := fun x => by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  intro n hn
  have hnC := hNC n hn
  have hn' : (⟨n, hnC⟩ : Subgroup.centralizer ({u} : Set (PSL2 K))) ∈
      Subgroup.normalizer (S' : Set (Subgroup.centralizer ({u} : Set (PSL2 K)))) := by
    refine Subgroup.mem_normalizer_iff.mpr fun c => ?_
    rw [hS'mem, hS'mem]
    exact Subgroup.mem_normalizer_iff.mp hn c
  exact (hS'mem _).mp (normalizer_sylow_le_of_dihedral eC S' hn')

theorem autSylowSelfNorm_of_psl2 {p f : ℕ} {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 p f) (hp2 : p ≠ 2)
    (hf : f = 1 ∨ f = 2) (h8 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) : AutSylowSelfNorm Q := by
  obtain ⟨⟨hp, hf1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : Q ≃* PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hK⟩
  let S₀ : Sylow 2 (PSL2 K) := default
  have hS₀ : Subgroup.normalizer (S₀ : Set (PSL2 K)) = S₀ :=
    le_antisymm (psl2_normalizer_sylow_le hodd (by rw [hK]; exact h8) S₀) Subgroup.le_normalizer
  have hout : IsPGroup 2 (Outer Q) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp K hK).2 Q
      ⟨e'⟩
    have h4 : Nat.card (Outer Q) ∣ 2 ^ 2 := by
      refine h.trans ((Nat.mul_dvd_mul_left f (Nat.gcd_dvd_left 2 _)).trans ?_)
      rcases hf with rfl | rfl <;> norm_num
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    exact IsPGroup.of_card hi
  have hZ : Subgroup.center Q = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [Nat.card_congr (Subgroup.centerCongr e').toEquiv,
      CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.card_bot]
  exact autSylowSelfNorm_of hZ (exists_selfNormalizing_of_equiv e' S₀ hS₀) hout

theorem factAutSylowL2Sq_holds : FactAutSylowL2Sq := by
  intro p hp hp3 Q _ _ hQ
  refine autSylowSelfNorm_of_psl2 hQ (by omega) (Or.inr rfl) (Or.inl ?_)
  have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8 <;> simp [Nat.pow_mod, h8]

theorem factAutOddL2pPlus_holds : FactAutOddL2pPlus := by
  intro p hp h8 Q _ _ hQ
  refine (autSylowSelfNorm_of_psl2 hQ ?_ (Or.inl rfl) (by rw [pow_one]; exact h8)).autOddNormCent
  rintro rfl
  omega

theorem factL2pSylowFour_holds : FactL2pSylowFour := by
  intro p hp h8 Q _ _ hQ S hS
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, hK⟩
  obtain ⟨w, hw, hwodd⟩ : ∃ w, Nat.card Q = 4 * w ∧ w % 2 = 1 := by
    have hc : Nat.card Q = p * (p ^ 2 - 1) / 2 := by
      rw [Nat.card_congr (e.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
        CFSG.GorensteinWalter.psl2_card_formula K hodd, hK, pow_one]
    rw [hc]
    have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rcases h8 with h8 | h8
    · obtain ⟨t, rfl⟩ : ∃ t, p = 8 * t + 3 := ⟨p / 8, by omega⟩
      refine ⟨(8 * t + 3) * (8 * t ^ 2 + 6 * t + 1), ?_, ?_⟩
      · have h1 : (8 * t + 3) ^ 2 - 1 = 8 * (8 * t ^ 2 + 6 * t + 1) := by
          have h : (8 * t + 3) ^ 2 = 8 * (8 * t ^ 2 + 6 * t + 1) + 1 := by ring
          omega
        rw [h1, show (8 * t + 3) * (8 * (8 * t ^ 2 + 6 * t + 1)) =
          2 * (4 * ((8 * t + 3) * (8 * t ^ 2 + 6 * t + 1))) by ring,
          Nat.mul_div_cancel_left _ two_pos]
      · exact Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨⟨4 * t + 1, by ring⟩, ⟨4 * t ^ 2 + 3 * t, by ring⟩⟩)
    · obtain ⟨t, rfl⟩ : ∃ t, p = 8 * t + 5 := ⟨p / 8, by omega⟩
      refine ⟨(8 * t + 5) * (8 * t ^ 2 + 10 * t + 3), ?_, ?_⟩
      · have h1 : (8 * t + 5) ^ 2 - 1 = 8 * (8 * t ^ 2 + 10 * t + 3) := by
          have h : (8 * t + 5) ^ 2 = 8 * (8 * t ^ 2 + 10 * t + 3) + 1 := by ring
          omega
        rw [h1, show (8 * t + 5) * (8 * (8 * t ^ 2 + 10 * t + 3)) =
          2 * (4 * ((8 * t + 5) * (8 * t ^ 2 + 10 * t + 3))) by ring,
          Nat.mul_div_cancel_left _ two_pos]
      · exact Nat.odd_iff.mp
          (Nat.odd_mul.mpr ⟨⟨4 * t + 2, by ring⟩, ⟨4 * t ^ 2 + 5 * t + 1, by ring⟩⟩)
  obtain ⟨hP, hi⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have hmul := Subgroup.card_mul_index S
  rw [ha, hw] at hmul
  have hw0 : w ≠ 0 := by
    rintro rfl
    omega
  have hidx0 : S.index ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hmul
    omega
  have hv : (2 ^ a * S.index).factorization 2 = (4 * w).factorization 2 := by rw [hmul]
  rw [Nat.factorization_mul (by positivity) hidx0, Nat.factorization_mul (by norm_num) hw0,
    Finsupp.add_apply, Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hi,
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ w),
    show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same] at hv
  rw [ha]
  have : a = 2 := by omega
  rw [this]
  norm_num

end CFSG.Quasithin.H13.KGAutSyl
