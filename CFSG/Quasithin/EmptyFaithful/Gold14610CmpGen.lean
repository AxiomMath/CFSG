module

public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpOrd
public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpArith

public section

namespace CFSG.Quasithin.Gold14610

open CFSG.Open

theorem CentralExt3.out {Q Y : Type} [Group Q] [Group Y] (h : CentralExt3 Q Y) :
    ∃ (X : Subgroup Q) (_ : X.Normal), Nonempty (Q ⧸ X ≃* Y) ∧ X ≤ Subgroup.center Q ∧
      Odd (Nat.card X) ∧ ¬ 3 ∣ Nat.card X ∧ Nat.card Q = Nat.card X * Nat.card Y := by
  obtain ⟨X, hX, hXz, hodd, hcop, ⟨e⟩⟩ := h
  refine ⟨X, hX, ⟨e⟩, hXz, Nat.odd_iff.mpr (by omega), ?_, ?_⟩
  · intro h3
    have h1 : 3 ∣ Nat.gcd (Nat.card X) 3 := Nat.dvd_gcd h3 dvd_rfl
    rw [show Nat.gcd (Nat.card X) 3 = 1 from hcop] at h1
    omega
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup X, Nat.card_congr e.toEquiv, mul_comm]

theorem Cat3Type.card {Q : Type} [Group Q] (h : Cat3Type Q) :
    ∃ w, Odd w ∧ Nat.card Q = 2 ^ 2 * w := by
  obtain ⟨Y, _, ⟨p, -, hp, hY⟩, hext⟩ := h
  obtain ⟨X, -, -, -, hodd, -, hQ⟩ := hext.out
  have hY' : Nat.card Y = p * (p ^ 2 - 1) / 2 := by
    simpa using card_isL2_odd hY (by simp; omega)
  obtain ⟨w, hw, hwe⟩ := psl_card_four (q := p) (by omega)
  exact ⟨w * Nat.card X, Nat.odd_mul.mpr ⟨hw, hodd⟩, by rw [hQ, hY', hwe]; ring⟩

theorem not_cat3_of_dvd {Q : Type} [Group Q] {N : ℕ} (hN : Nat.card Q = N) (h8 : 8 ∣ N) :
    ¬ Cat3Type Q := by
  rintro h
  obtain ⟨w, hw, hc⟩ := h.card
  have := Nat.odd_iff.mp hw
  omega

theorem F618Core.ord_le {Y : Type} [Group Y] (h : F618Core Y) :
    F618Ord (Nat.card Y) :=
  (F618Core.ord h).elim Or.inl fun h => Or.inr h.1

theorem false_of_card {Q Y : Type} [Group Q] [Group Y]
    (hY : F618Core Y) (hext : CentralExt3 Q Y) {N : ℕ} (hN : Nat.card Q = N)
    (hex : F618Excl N) : False := by
  obtain ⟨X, -, -, -, hodd, h3, hQ⟩ := hext.out
  exact hex _ _ (hQ.symm.trans hN) hodd h3 (F618Core.ord_le hY)

theorem false_of_two_pow {Q Y : Type} [Group Q] [Group Y]
    (hY : F618Core Y) (hext : CentralExt3 Q Y) {k M : ℕ} (hk : 7 ≤ k) (hM : 2 ^ k ∣ M)
    (hMQ : M ∣ Nat.card Q) : False := by
  obtain ⟨X, -, -, -, hodd, -, hQ⟩ := hext.out
  have h1 : 2 ^ k ∣ Nat.card X * Nat.card Y := hQ ▸ hM.trans hMQ
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact (F618Core.ord_le hY).not_two_pow_dvd hk (hcop.dvd_of_dvd_mul_left h1)

theorem card_eq_ker_mul {Q A : Type} [Group Q] [Group A] (π : Q →* A)
    (hπ : Function.Surjective π) : Nat.card π.ker * Nat.card A = Nat.card Q := by
  have h1 := Subgroup.card_ker_mul_card_range π
  rwa [MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top] at h1

theorem false_of_surj {Q Y A : Type} [Group Q] [Finite Q]
    [Group Y] [Group A] (hq : CFSG.IsQuasisimple Q) (hY : F618Core Y) (hext : CentralExt3 Q Y)
    (π : Q →* A) (hπ : Function.Surjective π) (hnt : ∃ a : A, a ≠ 1)
    (hA : (∃ k, 7 ≤ k ∧ 2 ^ k ∣ Nat.card A) ∨ (64 ∣ Nat.card A ∧ Nat.card A < 95040)) :
    False := by
  have hcard := card_eq_ker_mul π hπ
  have hAQ : Nat.card A ∣ Nat.card Q := ⟨Nat.card π.ker, by rw [← hcard]; ring⟩
  rcases hA with ⟨k, hk, hdvd⟩ | ⟨h64, hlt⟩
  · exact false_of_two_pow hY hext hk hdvd hAQ
  · obtain ⟨X, hXn, ⟨e⟩, hXz, hodd, h3, hQ⟩ := hext.out
    have hcop : Nat.Coprime 64 (Nat.card X) :=
      Nat.Coprime.pow_left 6 (Nat.coprime_two_left.mpr hodd)
    have hy64 : 64 ∣ Nat.card Y := hcop.dvd_of_dvd_mul_left (hQ ▸ h64.trans hAQ)
    rcases F618Core.ord hY with hyA | ⟨hy95, -, hcenter⟩
    · exact hyA.not_dvd_sixty_four hy64
    · have hnt' : ∃ k : Q, π k ≠ 1 := by
        obtain ⟨a, ha⟩ := hnt
        obtain ⟨q, rfl⟩ := hπ a
        exact ⟨q, ha⟩
      have hker : π.ker ≤ X := by
        intro z hz
        have hzc : z ∈ Subgroup.center Q :=
          CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt' hz
        have hψ : e (QuotientGroup.mk z) ∈ Subgroup.center Y := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨q, rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective X) y
          change e (QuotientGroup.mk q) * e (QuotientGroup.mk z) =
            e (QuotientGroup.mk z) * e (QuotientGroup.mk q)
          rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.mp hzc q]
        rw [hcenter, Subgroup.mem_bot] at hψ
        exact (QuotientGroup.eq_one_iff z).mp (e.injective (hψ.trans (map_one e).symm))
      have hle : Nat.card π.ker ≤ Nat.card X := Subgroup.card_le_of_le hker
      have hpos : 0 < Nat.card π.ker := Nat.card_pos
      rw [hy95] at hQ
      have h1 : Nat.card π.ker * Nat.card A < Nat.card π.ker * 95040 :=
        Nat.mul_lt_mul_of_pos_left hlt hpos
      have h2 : Nat.card π.ker * 95040 ≤ Nat.card X * 95040 := Nat.mul_le_mul_right _ hle
      omega

end CFSG.Quasithin.Gold14610
