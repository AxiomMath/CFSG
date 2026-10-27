module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Dih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Stmt
public import CFSG.Quasithin.EmptyFaithful.Insp7NumA

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

section Reduction

variable {L : Type} [Group L] {Gc : Type} [Group Gc]
  {ρ : Gc →* MulAut L} {ž : Gc} {Ŝ Kh : Subgroup Gc}

theorem conj_range_normal : (MulAut.conj : L →* MulAut L).range.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨l, rfl⟩ := hx
  refine ⟨g l, ?_⟩
  ext y
  simp [MulAut.conj_apply]

theorem odd_index_comap_conj (hZ : Subgroup.center L = ⊥) (h6 : 2 ^ 6 ∣ Nat.card L)
    (hin : InspInput ρ ž Ŝ Kh) :
    ¬ 2 ∣ ((MulAut.conj : L →* MulAut L).range.comap ρ).index := by
  intro h2
  set N : Subgroup Gc := (MulAut.conj : L →* MulAut L).range.comap ρ with hN
  have hInn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hin.inn l
  have hNcard : Nat.card N = Nat.card L := by
    have h1 : N.map ρ = (MulAut.conj : L →* MulAut L).range := by
      rw [hN, Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hInn
    have h2 : Nat.card N = Nat.card (N.map ρ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective N ρ hin.inj).toEquiv
    rw [h2, h1]
    have h3 : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card (L ⧸ Subgroup.center L) := by
      rw [← Insp7.ker_conj_eq_center]
      exact (Nat.card_congr
        (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
    rw [h3, hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv
  have hG1 := Subgroup.card_mul_index N
  have hG2 := Subgroup.card_mul_index Ŝ
  have h128 : 2 ^ 7 ∣ Nat.card Gc := by
    rw [← hG1, hNcard]
    obtain ⟨m, hm⟩ := h6
    obtain ⟨n, hn⟩ := h2
    rw [hm, hn]
    exact ⟨m * n, by ring⟩
  rw [← hG2] at h128
  have hcop : Nat.Coprime (2 ^ 7) Ŝ.index :=
    Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hin.sylow.2)
  have h128' : 2 ^ 7 ∣ Nat.card Ŝ := hcop.dvd_of_dvd_mul_right h128
  rcases hin.card_S with h | h
  · rw [h] at h128'
    exact absurd (Nat.le_of_dvd (by positivity) h128') (by norm_num)
  · rw [h] at h128'
    exact absurd (Nat.le_of_dvd (by positivity) h128') (by norm_num)

theorem mem_conj_range_of_two_power (hZ : Subgroup.center L = ⊥) (h6 : 2 ^ 6 ∣ Nat.card L)
    (hin : InspInput ρ ž Ŝ Kh) {g : Gc} {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : ρ g ∈ (MulAut.conj : L →* MulAut L).range := by
  set N : Subgroup Gc := (MulAut.conj : L →* MulAut L).range.comap ρ with hN
  have hNn : N.Normal := conj_range_normal.comap ρ
  have hodd := odd_index_comap_conj hZ h6 hin
  have hcop : Nat.Coprime (2 ^ k) N.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  let q : Gc ⧸ N := QuotientGroup.mk g
  have hq1 : q ^ 2 ^ k = 1 := by
    show (QuotientGroup.mk g : Gc ⧸ N) ^ 2 ^ k = 1
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have hq2 : q ^ N.index = 1 := by
    have := pow_card_eq_one' (x := q)
    exact this
  have hd1 := orderOf_dvd_of_pow_eq_one hq1
  have hd2 := orderOf_dvd_of_pow_eq_one hq2
  have hone : orderOf q = 1 := (Nat.Coprime.coprime_dvd_left hd1 hcop).eq_one_of_dvd hd2
  have hq : q = 1 := orderOf_eq_one_iff.mp hone
  exact (QuotientGroup.eq_one_iff g).mp hq

theorem exists_dihedral_in_inn [Finite Gc] (hZ : Subgroup.center L = ⊥) (h6 : 2 ^ 6 ∣ Nat.card L)
    (hin : InspInput ρ ž Ŝ Kh) :
    ∃ w a b : L, orderOf w = 4 ∧ w * a = a * w ∧ w * b = b * w ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b ≠ b * a ∧ (a * b) ^ 4 = 1 := by
  have : Finite ↥Kh := inferInstance
  obtain ⟨w, a, b, hw4, hwc, ha, hb, hab, hab4⟩ := exists_dihedral_of_z4StarSL23 hin.K_shape
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  have hlift : ∀ (x : Kh) (k : ℕ), (x : Gc) ^ 2 ^ k = 1 → ∃ l : L, ρ x = MulAut.conj l :=
    fun x k hx => by
      obtain ⟨l, hl⟩ := mem_conj_range_of_two_power hZ h6 hin hx
      exact ⟨l, hl.symm⟩
  have hw2 : (w : Gc) ^ 2 ^ 2 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw4] at this
    exact congrArg Subtype.val this
  have ha1 : (a : Gc) * (a : Gc) = 1 := congrArg Subtype.val ha
  have hb1 : (b : Gc) * (b : Gc) = 1 := congrArg Subtype.val hb
  have ha2 : (a : Gc) ^ 2 ^ 1 = 1 := by simpa [pow_two] using ha1
  have hb2 : (b : Gc) ^ 2 ^ 1 = 1 := by simpa [pow_two] using hb1
  obtain ⟨lw, hlw⟩ := hlift w 2 hw2
  obtain ⟨la, hla⟩ := hlift a 1 ha2
  obtain ⟨lb, hlb⟩ := hlift b 1 hb2
  have hwa : (w : Gc) * (a : Gc) = (a : Gc) * (w : Gc) := (congrArg Subtype.val (hwc a)).symm
  have hwb : (w : Gc) * (b : Gc) = (b : Gc) * (w : Gc) := (congrArg Subtype.val (hwc b)).symm
  have hw2ne : (w : Gc) ^ 2 ≠ 1 := fun h => by
    have h1 : w ^ 2 = 1 := Subtype.ext h
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rw [hw4] at h2
    omega
  have hab' : (a : Gc) * (b : Gc) ≠ (b : Gc) * (a : Gc) := fun h => hab (Subtype.ext h)
  have hab4' : ((a : Gc) * (b : Gc)) ^ 4 = 1 := congrArg Subtype.val hab4
  have hconj : ∀ x : Gc, ∀ l : L, ρ x = MulAut.conj l → ∀ n : ℕ, ρ (x ^ n) = MulAut.conj (l ^ n) :=
    fun x l h n => by rw [map_pow, h, map_pow]
  have hw4L : lw ^ 4 = 1 := by
    apply hinj
    have h4 : (w : Gc) ^ 4 = 1 := by simpa using hw2
    rw [← hconj _ lw hlw 4, h4, map_one, map_one]
  have hw2L : lw ^ 2 ≠ 1 := fun h =>
    hw2ne (hin.inj (by rw [hconj _ lw hlw 2, h, map_one, map_one]))
  have hwo : orderOf lw = 4 := by
    have : orderOf lw = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hw2L) (by simpa using hw4L)
    simpa using this
  have hwaL : lw * la = la * lw := by
    apply hinj
    have h := congrArg ρ hwa
    rw [map_mul, map_mul, hlw, hla, ← map_mul, ← map_mul] at h
    exact h
  have hwbL : lw * lb = lb * lw := by
    apply hinj
    have h := congrArg ρ hwb
    rw [map_mul, map_mul, hlw, hlb, ← map_mul, ← map_mul] at h
    exact h
  have haaL : la * la = 1 := by
    apply hinj
    have h := congrArg ρ ha1
    rw [map_mul, hla, ← map_mul, map_one] at h
    rw [h, map_one]
  have hbbL : lb * lb = 1 := by
    apply hinj
    have h := congrArg ρ hb1
    rw [map_mul, hlb, ← map_mul, map_one] at h
    rw [h, map_one]
  have habL : la * lb ≠ lb * la := fun h =>
    hab' (hin.inj (by rw [map_mul, map_mul, hla, hlb, ← map_mul, ← map_mul, h]))
  have hab4L : (la * lb) ^ 4 = 1 := by
    apply hinj
    have h := hconj ((a : Gc) * (b : Gc)) (la * lb) (by rw [map_mul, hla, hlb, map_mul]) 4
    rw [← h, hab4', map_one, map_one]
  exact ⟨lw, la, lb, hwo, hwaL, hwbL, haaL, hbbL, habL, hab4L⟩

end Reduction

end InspW2

end S143

end CFSG.Quasithin
