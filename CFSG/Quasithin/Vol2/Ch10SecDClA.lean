module

public import CFSG.Quasithin.Vol2.Ch10SecD33E
public import CFSG.Quasithin.Vol2.Ch10SecD33F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_noncomm_alt5 : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    fun h => by
      have h' := congrArg Subtype.val h
      revert h'
      decide⟩

theorem isQuasisimple_of_mulEquiv_alt5 {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 5)) : CFSG.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := exists_noncomm_alt5
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    have := congrArg e h
    simpa using this
  have : Nontrivial Q := ⟨⟨a * b, b * a, hab⟩⟩
  have hs : IsSimpleGroup Q :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hZ : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hP : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  have hmk : ∀ x y : Q, (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) = QuotientGroup.mk y →
      x = y := fun x y hxy => by
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot] at hxy
    exact inv_mul_eq_one.mp hxy
  have : Nontrivial (Q ⧸ Subgroup.center Q) :=
    ⟨⟨QuotientGroup.mk (a * b), QuotientGroup.mk (b * a), fun h => hab (hmk _ _ h)⟩⟩
  refine ⟨hP, IsSimpleGroup.isSimpleGroup_of_surjective (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _), QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
  exact hmk _ _ h

theorem nonempty_alt5_of_card_sixty {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 60) : Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 Q) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hQ, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup Q).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hQ] at hP
      omega
  have hcard : Nat.card (Sylow 5 Q) = 6 := by
    have hmod := card_sylow_modEq_one 5 Q
    have hdvd : Nat.card (Sylow 5 Q) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup Q).index_eq_card, show Nat.card (Q ⧸ (P : Subgroup Q)) = 12 by
        have := (P : Subgroup Q).card_mul_index
        rw [hP, hQ, (P : Subgroup Q).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 Q) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 Q) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 Q) <;> simp_all
  have hfaithful : FaithfulSMul Q (Sylow 5 Q) := by
    let φ := MulAction.toPermHom Q (Sylow 5 Q)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 Q) => σ P) hg)
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 Q) inferInstance hcard hQ

omit [Finite G] in
theorem card_quot_dvd_of_le {K H : Subgroup G} (hKH : K ≤ H) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card H :=
  (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)).symm).trans
    (Subgroup.card_dvd_of_le hKH)

theorem nonempty_alt5_of_type {K : Subgroup G} (hns : ¬ Group.IsSolvable ↥K) {a : ℕ}
    (hdvd : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 2 ^ a * 225)
    (htype : (∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ m ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* PSL(2, ZMod p))) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
  rcases htype with ⟨m, hm0, hmev, F, _, _, hF, ⟨φ⟩⟩ | ⟨p, hp, hp2, ⟨φ⟩⟩
  · have hc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr φ.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF]
    have hm : m = 2 := by
      have h1 : (2 ^ m) ^ 2 - 1 ∣ 2 ^ a * 225 := by
        rw [hc] at hdvd
        exact (Dvd.intro_left _ rfl).trans hdvd
      have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
        have he : Even ((2 ^ m) ^ 2) :=
          Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hm0.ne'⟩, two_ne_zero⟩
        have hpos : 0 < (2 ^ m) ^ 2 := by positivity
        obtain ⟨r, hr⟩ := he
        exact ⟨r - 1, by omega⟩
      have h2 : (2 ^ m) ^ 2 - 1 ∣ 225 :=
        (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left h1
      have h3 : (2 ^ m) ^ 2 - 1 ≤ 225 := Nat.le_of_dvd (by norm_num) h2
      obtain ⟨k, rfl⟩ := hmev
      by_contra hne
      have hk : 4 ≤ k + k := by omega
      have h16 : 16 ≤ 2 ^ (k + k) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by norm_num) hk
      have : 256 ≤ (2 ^ (k + k)) ^ 2 := by
        calc 256 = 16 ^ 2 := by norm_num
          _ ≤ (2 ^ (k + k)) ^ 2 := Nat.pow_le_pow_left h16 2
      omega
    subst hm
    have := isSimpleGroup_of_sl2 φ le_rfl hF
    exact nonempty_alt5_of_card_sixty (by rw [hc]; norm_num)
  · have : Fact p.Prime := ⟨hp⟩
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hFc : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
    have hcardL := CFSG.GorensteinWalter.psl2_card_formula (ZMod p)
      (CFSG.Walter.isOddPrimePower_of_card hFc hodd one_pos)
    rw [Nat.card_zmod] at hcardL
    have hc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = p * (p ^ 2 - 1) / 2 := by
      rw [Nat.card_congr φ.toEquiv, hcardL]
    obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd hodd
    have hc' : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = p * (4 * k) := by
      rw [hc, hk, show p * (8 * k) = 2 * (p * (4 * k)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    have hp225 : p ∣ 225 := by
      have h1 : p ∣ 2 ^ a * 225 := (Dvd.intro _ hc'.symm).trans hdvd
      exact (Nat.Coprime.pow_right a
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).dvd_of_dvd_mul_left h1
    have hp35 : p = 3 ∨ p = 5 := by
      have h9 : p ∣ 3 ^ 2 * 5 ^ 2 := by simpa using hp225
      rcases (Nat.Prime.dvd_mul hp).mp h9 with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))
    rcases hp35 with rfl | rfl
    ·
      exfalso
      have hsol : Group.IsSolvable ↥(barSub K K) := by
        have := isSolvable_psl2_three
        have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
          Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        infer_instance
      exact hns (isSolvable_of_barSub le_rfl hsol)
    · have := isSimpleGroup_of_psl2 le_rfl φ
      exact nonempty_alt5_of_card_sixty (by rw [hc]; norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecD
