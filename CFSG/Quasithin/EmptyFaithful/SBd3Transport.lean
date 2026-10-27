module

public import CFSG.Quasithin.Background.A3Structure316

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.SBd3T

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem map_oPrimeResidualOf [Finite A] (f : A →* B) (p : ℕ) (hp : p.Prime) (K : Subgroup A) :
    (oPrimeResidualOf p K).map f = oPrimeResidualOf p (K.map f) := by
  unfold oPrimeResidualOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxK, k, hk⟩, rfl⟩
    refine ⟨⟨x, hxK, rfl⟩, ?_⟩
    have hdvd : orderOf (f x) ∣ p ^ k := hk ▸ orderOf_map_dvd f x
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨j, hj⟩
  · rintro ⟨⟨x, hxK, rfl⟩, j, hj⟩
    have hm : 0 < orderOf x := orderOf_pos x
    obtain ⟨a, b, hb, hmab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
    have hcop : Nat.Coprime b (orderOf (f x)) := by
      rw [hj]
      exact Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    refine ⟨x ^ (b * c), ⟨Subgroup.pow_mem K hxK _, ?_⟩, ?_⟩
    · have h2 : (x ^ (b * c)) ^ (p ^ a) = 1 := by
        rw [← pow_mul]
        have : b * c * p ^ a = orderOf x * c := by rw [hmab]; ring
        rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
      have hd : orderOf (x ^ (b * c)) ∣ p ^ a := orderOf_dvd_of_pow_eq_one h2
      obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow hp).1 hd
      exact ⟨k, hk'⟩
    · rw [map_pow, pow_mul]
      exact hc

theorem isPGroup_map_iff {p : ℕ} (ι : A →* B) (hι : Function.Injective ι) (S : Subgroup A) :
    IsPGroup p ↥(S.map ι) ↔ IsPGroup p ↥S :=
  ⟨fun h => h.of_equiv (S.equivMapOfInjective ι hι).symm,
    fun h => h.of_equiv (S.equivMapOfInjective ι hι)⟩

theorem isSylowTwoOf_map_iff (ι : A →* B) (hι : Function.Injective ι) (S H : Subgroup A) :
    IsSylowTwoOf (S.map ι) (H.map ι) ↔ IsSylowTwoOf S H := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective hι, isPGroup_map_iff ι hι]
  have : ((S.map ι).subgroupOf (H.map ι)).index = (S.subgroupOf H).index := by
    have := Subgroup.relIndex_map_map_of_injective S H hι
    exact this
  rw [this]

theorem map_mem_normalizer_iff (ι : A →* B) (hι : Function.Injective ι) (S : Subgroup A) (x : A) :
    ι x ∈ Subgroup.normalizer ((S.map ι : Subgroup B) : Set B) ↔
      x ∈ Subgroup.normalizer (S : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (ι a)
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hι,
      Subgroup.mem_map_iff_mem hι] at this
    exact this
  · intro h b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨x * a * x⁻¹, (h a).1 ha, by simp⟩
    · rintro ⟨a, ha, hab⟩
      refine ⟨x⁻¹ * a * x, (h (x⁻¹ * a * x)).2 (by simpa [mul_assoc] using ha), ?_⟩
      calc ι (x⁻¹ * a * x) = (ι x)⁻¹ * ι a * ι x := by simp [map_mul, map_inv]
        _ = b := by rw [hab]; group

theorem map_le_normalizer_map_iff (ι : A →* B) (hι : Function.Injective ι) (S K : Subgroup A) :
    S.map ι ≤ Subgroup.normalizer ((K.map ι : Subgroup B) : Set B) ↔
      S ≤ Subgroup.normalizer (K : Set A) := by
  constructor
  · intro h x hx
    exact (map_mem_normalizer_iff ι hι K x).1 (h (Subgroup.mem_map_of_mem _ hx))
  · rintro h _ ⟨x, hx, rfl⟩
    exact (map_mem_normalizer_iff ι hι K x).2 (h hx)

end Transport

section Parabolic

variable {A B : Type} [Group A] [Group B]

theorem isParabolic2_map_iff (ι : A →* B) (hι : Function.Injective ι) (L P : Subgroup A) :
    IsParabolic2 (L.map ι) (P.map ι) ↔ IsParabolic2 L P := by
  unfold IsParabolic2
  rw [Subgroup.map_le_map_iff_of_injective hι]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨S', hS', hN⟩
    have hrange : S' ≤ ι.range := hS'.1.trans (Subgroup.map_le_range _ _)
    have hS'e : (S'.comap ι).map ι = S' := Subgroup.map_comap_eq_self hrange
    refine ⟨S'.comap ι, ?_, ?_⟩
    · rw [← hS'e] at hS'
      exact (isSylowTwoOf_map_iff ι hι _ _).1 hS'
    · intro x hx
      have h1 : ι x ∈ L.map ι := Subgroup.mem_map_of_mem _ hx.1
      have h2 : ι x ∈ Subgroup.normalizer (((S'.comap ι).map ι : Subgroup B) : Set B) :=
        (map_mem_normalizer_iff ι hι _ x).2 hx.2
      rw [hS'e] at h2
      exact (Subgroup.mem_map_iff_mem hι).1 (hN ⟨h1, h2⟩)
  · rintro ⟨S, hS, hN⟩
    refine ⟨S.map ι, (isSylowTwoOf_map_iff ι hι _ _).2 hS, ?_⟩
    rintro y ⟨⟨x, hxL, rfl⟩, hy⟩
    exact Subgroup.mem_map_of_mem _ (hN ⟨hxL, (map_mem_normalizer_iff ι hι _ x).1 hy⟩)

theorem isMaxParabolic2_map_iff (ι : A →* B) (hι : Function.Injective ι) (L P : Subgroup A) :
    IsMaxParabolic2 (L.map ι) (P.map ι) ↔ IsMaxParabolic2 L P := by
  unfold IsMaxParabolic2
  rw [isParabolic2_map_iff ι hι, (Subgroup.map_injective hι).ne_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h Q hQ hQL hPQ
    have := h (Q.map ι) ((isParabolic2_map_iff ι hι _ _).2 hQ)
      ((Subgroup.map_injective hι).ne_iff.2 hQL) (Subgroup.map_mono hPQ)
    exact (Subgroup.map_injective hι) this
  · intro h Q' hQ' hQ'L hPQ'
    have hQ'le : Q' ≤ L.map ι := hQ'.1
    have hrange : Q' ≤ ι.range := hQ'le.trans (Subgroup.map_le_range _ _)
    have hQe : (Q'.comap ι).map ι = Q' := Subgroup.map_comap_eq_self hrange
    rw [← hQe] at hQ' hQ'L hPQ' ⊢
    have := h (Q'.comap ι) ((isParabolic2_map_iff ι hι _ _).1 hQ')
      ((Subgroup.map_injective hι).ne_iff.1 hQ'L) ((Subgroup.map_le_map_iff_of_injective hι).1 hPQ')
    rw [this]

end Parabolic

end CFSG.Quasithin.SBd3T
