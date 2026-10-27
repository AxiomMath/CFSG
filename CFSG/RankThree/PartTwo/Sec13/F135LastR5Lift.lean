module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG

theorem r5a_card_comap {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal]
    (T : Subgroup (M ⧸ R)) :
    Nat.card (T.comap (QuotientGroup.mk' R)) = Nat.card R * Nat.card T := by
  have h1 := (T.comap (QuotientGroup.mk' R)).card_mul_index
  have h2 := R.card_mul_index
  have h3 := T.card_mul_index
  have h4 : (T.comap (QuotientGroup.mk' R)).index = T.index :=
    T.index_comap_of_surjective (QuotientGroup.mk'_surjective R)
  have h5 : R.index = Nat.card (M ⧸ R) := rfl
  have hT0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hT0) ?_
  calc Nat.card (T.comap (QuotientGroup.mk' R)) * T.index
      = Nat.card (T.comap (QuotientGroup.mk' R)) * (T.comap (QuotientGroup.mk' R)).index := by
        rw [h4]
    _ = Nat.card M := h1
    _ = Nat.card R * R.index := h2.symm
    _ = Nat.card R * (Nat.card T * T.index) := by rw [h5, h3]
    _ = Nat.card R * Nat.card T * T.index := by ring

theorem r5a_factorization_mul_pow {a p m : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (ha0 : a ≠ 0) :
    (a * p ^ m).factorization p = m := by
  rw [Nat.factorization_mul ha0 (pow_ne_zero m hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ha, Nat.factorization_pow, Finsupp.smul_apply,
    hp.factorization_self, zero_add, smul_eq_mul, mul_one]

theorem r5a_eq_of_mk_eq {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {F : Subgroup M}
    (hF : F ⊓ R = ⊥) {x y : M} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : QuotientGroup.mk' R x = QuotientGroup.mk' R y) : x = y := by
  have h1 : x⁻¹ * y ∈ R := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ F ⊓ R := ⟨F.mul_mem (F.inv_mem hx) hy, h1⟩
  rw [hF, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

theorem r5a_card_map_of_inf {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {F : Subgroup M}
    (hF : F ⊓ R = ⊥) : Nat.card (F.map (QuotientGroup.mk' R)) = Nat.card F := by
  let e : F ≃ F.map (QuotientGroup.mk' R) :=
    Equiv.ofBijective
      (fun x : F => (⟨QuotientGroup.mk' R (x : M), Subgroup.mem_map_of_mem (QuotientGroup.mk' R) x.2⟩ :
        F.map (QuotientGroup.mk' R)))
      ⟨fun x y hxy => Subtype.ext (r5a_eq_of_mk_eq R hF x.2 y.2 (congrArg Subtype.val hxy)),
        fun z => by
          obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
          exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩⟩
  exact (Nat.card_congr e).symm

theorem exists_invariant_sylow_two {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {F K : Subgroup X} (hF : IsPGroup p F) (hFK : F ≤ Subgroup.normalizer (K : Set X))
    (hK : ¬ p ∣ Nat.card K) :
    ∃ T : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 T K ∧ F ≤ Subgroup.normalizer (T : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulDistribMulAction F K := MulDistribMulAction.compHom K (Subgroup.inclusion hFK)
  haveI : Finite (Sylow 2 K) :=
    Finite.of_injective (fun P : Sylow 2 K => (P : Set K)) SetLike.coe_injective
  have hcard : ¬ p ∣ Nat.card (Sylow 2 K) := by
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 K))
    intro h
    exact hK (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨Q, hQ⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 K) hcard
  have hfix : ∀ g : F, g • Q = Q := fun g => MulAction.mem_fixedPoints.mp hQ g
  have key : ∀ (g : F) (k : K), k ∈ (Q : Subgroup K) → g • k ∈ (Q : Subgroup K) := by
    intro g k hk
    have h1 := Subgroup.smul_mem_pointwise_smul k g _ hk
    rw [← Sylow.pointwise_smul_def, hfix g] at h1
    exact h1
  have hconj : ∀ f : X, f ∈ F → ∀ h ∈ (Q : Subgroup K).map K.subtype,
      f * h * f⁻¹ ∈ (Q : Subgroup K).map K.subtype := by
    intro f hf h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_map.mpr ⟨(⟨f, hf⟩ : F) • k, key ⟨f, hf⟩ k hk, rfl⟩
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_⟩
  intro f hf
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · exact hconj f hf h
  · intro hh
    have hback := hconj f⁻¹ (F.inv_mem hf) (f * h * f⁻¹) hh
    have e : f⁻¹ * (f * h * f⁻¹) * f⁻¹⁻¹ = h := by group
    rw [e] at hback
    exact hback

theorem exists_two_lift {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R) {F : Subgroup M} (hF : IsPGroup p F)
    {T : Subgroup (M ⧸ R)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hFT : F.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (T : Set (M ⧸ R))) :
    ∃ T' : Subgroup M, T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ F ≤ Subgroup.normalizer (T' : Set M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hKcard := r5a_card_comap R T
  have hFK : F ≤ Subgroup.normalizer ((T.comap (QuotientGroup.mk' R) : Subgroup M) : Set M) := by
    intro f hf
    have hfT := hFT (Subgroup.mem_map_of_mem (QuotientGroup.mk' R) hf)
    rw [Subgroup.mem_set_normalizer_iff] at hfT ⊢
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
    exact hfT (QuotientGroup.mk' R h)
  have hK2 : ¬ p ∣ Nat.card (T.comap (QuotientGroup.mk' R)) := by
    rw [hKcard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hR h1
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
      rw [hn] at h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  obtain ⟨T', hT's, hFT'⟩ := exists_invariant_sylow_two hp hF hFK hK2
  refine ⟨T', ?_, hT's.isPGroup, hFT'⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hT
    exact Subgroup.card_eq_one.mp (by rw [hn, pow_zero])
  have h2K : 2 ∣ Nat.card (T.comap (QuotientGroup.mk' R)) := by
    rw [hKcard]
    exact Dvd.dvd.mul_left (by rw [hn]; exact dvd_pow_self 2 hn0) _
  have hpos : 0 < (Nat.card (T.comap (QuotientGroup.mk' R))).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
  intro hbot
  subst hbot
  have hc := hT's.card_eq
  rw [Subgroup.card_bot] at hc
  exact absurd hc (ne_of_lt (Nat.one_lt_two_pow hpos.ne'))

theorem exists_pSubgroup_lift {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R) {F₀ : Subgroup (M ⧸ R)}
    (hF₀ : IsPGroup p F₀) :
    ∃ F : Subgroup M, IsPGroup p F ∧ F.map (QuotientGroup.mk' R) = F₀ ∧ F ⊓ R = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFs⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F₀.comap (QuotientGroup.mk' R))
  have hFK : F ≤ F₀.comap (QuotientGroup.mk' R) := hFs.le
  have hFp : IsPGroup p F := hFs.isPGroup
  have hinf : F ⊓ R = ⊥ := by
    have hpg : IsPGroup p (F ⊓ R : Subgroup M) := hFp.to_inf_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    have hdvd : Nat.card (F ⊓ R : Subgroup M) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra hne
      exact hR ((dvd_pow_self p hne).trans hdvd)
    exact Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
  have hKcard : Nat.card (F₀.comap (QuotientGroup.mk' R)) = Nat.card R * Nat.card F₀ :=
    r5a_card_comap R F₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hF₀
  have hFcard : Nat.card F = p ^ m := by
    rw [hFs.card_eq, hKcard, hm, r5a_factorization_mul_pow hp hR Nat.card_pos.ne']
  have hle : F.map (QuotientGroup.mk' R) ≤ F₀ := Subgroup.map_le_iff_le_comap.mpr hFK
  refine ⟨F, hFp, ?_, hinf⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  exact le_of_eq (by rw [r5a_card_map_of_inf R hinf, hFcard, hm])

theorem isElemAbelian_of_lift {M : Type*} [Group M] [Finite M] {p : ℕ} (R : Subgroup M) [R.Normal]
    {F : Subgroup M} (hF : F ⊓ R = ⊥)
    (h : CFSG.Open.IsElemAbelian p (F.map (QuotientGroup.mk' R))) :
    CFSG.Open.IsElemAbelian p F ∧ Nat.card F = Nat.card (F.map (QuotientGroup.mk' R)) := by
  unfold CFSG.Open.IsElemAbelian at h ⊢
  obtain ⟨hc, he⟩ := h
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    apply r5a_eq_of_mk_eq R hF (F.mul_mem hx hy) (F.mul_mem hy hx)
    have h1 := congrArg Subtype.val (hc.is_comm.comm
      (⟨QuotientGroup.mk' R x, Subgroup.mem_map_of_mem (QuotientGroup.mk' R) hx⟩ :
        F.map (QuotientGroup.mk' R))
      ⟨QuotientGroup.mk' R y, Subgroup.mem_map_of_mem (QuotientGroup.mk' R) hy⟩)
    rw [map_mul, map_mul]
    exact h1
  have hpow : ∀ x ∈ F, x ^ p = 1 := by
    intro x hx
    have h1 : QuotientGroup.mk' R (x ^ p) = 1 := by
      rw [map_pow]
      exact he _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' R) hx)
    have h2 : x ^ p ∈ F ⊓ R :=
      ⟨F.pow_mem hx p, (QuotientGroup.eq_one_iff (N := R) (x ^ p)).mp h1⟩
    rw [hF, Subgroup.mem_bot] at h2
    exact h2
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hpow⟩, (r5a_card_map_of_inf R hF).symm⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
