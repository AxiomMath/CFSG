module

public import CFSG.Quasithin.H13.KG14726L115CDefs
public import CFSG.Quasithin.H13.KG14726Corr

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Quasithin

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem congr_conj (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply]

theorem map_congr_inn (e : X ≃* Y) :
    (MulAut.conj : X →* MulAut X).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : Y →* MulAut Y).range :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e

theorem kg115Excluded_of_mulEquiv (e : X ≃* Y) (h : KG115Excluded Y) : KG115Excluded X := by
  intro A B l hA hBA hBi hB hF1 hlB hl1 hlc hF2p
  set Φ := MulAut.congr e with hΦ
  have hΦi : Function.Injective Φ.toMonoidHom := Φ.injective
  have hinn : ∀ φ : MulAut X, φ ∈ (MulAut.conj : X →* MulAut X).range ↔
      Φ φ ∈ (MulAut.conj : Y →* MulAut Y).range := by
    intro φ
    rw [← map_congr_inn e]
    exact (mem_map_iff_mem hΦi).symm
  have hnorm : ∀ (N : Subgroup (MulAut X)) (φ : MulAut X),
      φ ∈ normalizer (N : Set (MulAut X)) ↔
        Φ φ ∈ normalizer ((N.map Φ.toMonoidHom : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro N φ
    rw [← map_equiv_normalizer_eq N Φ]
    exact (mem_map_iff_mem hΦi (K := normalizer (N : Set (MulAut X))) (x := φ)).symm
  refine h (A.map Φ.toMonoidHom) (B.map Φ.toMonoidHom) (e l) ?_ (map_mono hBA) ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · rw [← map_congr_inn e]
    exact map_mono hA
  · rwa [← relIndex, relIndex_map_map_of_injective _ _ hΦi]
  · rwa [card_map_of_injective hΦi]
  · obtain ⟨x, hxI, hx3, hxB, N, hNI, hxN, hBN, hNB⟩ := hF1
    refine ⟨Φ x, (hinn x).mp hxI, by rw [MulEquiv.orderOf_eq]; exact hx3,
      mem_map_of_mem _ hxB, N.map Φ.toMonoidHom, ?_, mem_map_of_mem _ hxN, ?_, ?_⟩
    · rw [← map_congr_inn e]
      exact map_mono hNI
    · rintro _ ⟨b, hb, rfl⟩
      exact (hnorm N b).mp (hBN hb)
    · intro a ha han
      obtain ⟨a', rfl⟩ := Φ.surjective a
      exact mem_map_of_mem _ (hNB a' ((hinn a').mpr ha) ((hnorm N a').mpr han))
  · rw [← congr_conj]
    exact mem_map_of_mem _ hlB
  · exact fun h1 => hl1 (e.injective (by rw [h1, map_one]))
  · rintro _ ⟨b, hb, rfl⟩
    rw [← congr_conj]
    change Φ b * Φ (MulAut.conj l) = Φ (MulAut.conj l) * Φ b
    rw [← map_mul, ← map_mul, hlc b hb]
  · intro ℓ hℓ hp hp2
    obtain ⟨ℓ', rfl⟩ := e.surjective ℓ
    rw [← congr_conj]
    have hℓ' : ℓ' * l = l * ℓ' := e.injective (by rw [map_mul, map_mul, hℓ])
    rw [MulEquiv.orderOf_eq] at hp hp2
    exact mem_map_of_mem _ (hF2p ℓ' hℓ' hp hp2)

theorem kg115Excluded_of_card {n : ℕ} (hn : Nat.card (MulAut X) ∣ n) (h27 : ¬ 27 ∣ n) :
    KG115Excluded X := fun _ _ _ _ _ _ hB _ _ _ _ _ => false_of_card_mulAut_dvd hn h27 hB

end Transport

section Data

theorem mem_normalizer_of_commute {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (h : ∀ s ∈ S, s * g = g * s) : g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [(h x hx).symm, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx
    have h2 : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [mul_assoc, h1]
        _ = g * x * g⁻¹ := by group
    rw [h2]
    exact hx

variable (X : Type) [Group X]

@[expose] def SylowTwoNoThree : Prop :=
  ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index →
    ∀ y : X, orderOf y = 3 → ¬ ∀ s ∈ S, s * y = y * s

@[expose] def KG115Data : Prop :=
  SylowTwoNoThree X ∧
    ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → ∀ l ∈ S, (∀ s ∈ S, s * l = l * s) →
      l ≠ 1 →
        (∃ ℓ : X, ℓ * l = l * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) ∨
        ∀ y : X, y * l = l * y → orderOf y ≠ 3

@[expose] def KG115At (S : Subgroup X) (l : X) : Prop :=
  ∀ D N : Subgroup X, S ≤ D → (∀ d ∈ D, d * l = l * d) → (∃ y ∈ N, orderOf y = 3) →
    normalizer (N : Set X) = D →
    (∀ ℓ : X, ℓ * l = l * ℓ → (orderOf ℓ).Prime → orderOf ℓ ≠ 2 → ℓ ∈ D) →
    (∃ a : ℕ, Nat.card D ∣ 2 ^ a * 27) →
    27 ∣ Nat.card D * (MulAut.conj : X →* MulAut X).range.index → False

variable {X}

theorem sylowTwoNoThree_of_twoCentral [Finite X] (hX : TwoCentralConstrained X)
    (h4 : 4 ∣ Nat.card X) : SylowTwoNoThree X := by
  intro S hS hSi y hy hyS
  have hcard : 2 < Nat.card S := by
    have h := S.card_mul_index
    have hcop : Nat.Coprime 4 S.index := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSi)
    have h4S : 4 ∣ Nat.card S := hcop.dvd_of_dvd_mul_right (h ▸ h4)
    have hpos : 0 < Nat.card S := Nat.card_pos
    have := Nat.le_of_dvd hpos h4S
    omega
  refine false_of_le_normalizer_zpowers hX hS hSi hcard hy fun s hs => ?_
  have hc : Commute s y := hyS s hs
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp only; rw [(hc.zpow_right k).eq, mul_inv_cancel_right]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only at hk ⊢
    have h1 : s⁻¹ * y ^ k * s = y ^ k := by
      rw [((hc.zpow_right k).inv_left).eq, inv_mul_cancel_right]
    calc y ^ k = s⁻¹ * y ^ k * s := h1.symm
      _ = s⁻¹ * (s * g * s⁻¹) * s := by rw [hk]
      _ = g := by group

theorem kg115At_of_prime {S : Subgroup X} {l : X}
    (h : ∃ ℓ : X, ℓ * l = l * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) : KG115At X S l := by
  intro D N _ _ _ _ hD ⟨a, ha⟩ _
  obtain ⟨ℓ, hℓ, p, hp, hp5, hℓp⟩ := h
  have h1 : orderOf ℓ ∣ 2 ^ a * 27 :=
    (D.orderOf_dvd_natCard (hD ℓ hℓ (hℓp ▸ hp) (by omega))).trans ha
  rw [hℓp] at h1
  exact not_prime_dvd_two_pow_mul hp hp5 a h1

theorem kg115At_of_noThree {S : Subgroup X} {l : X}
    (h : ∀ y : X, y * l = l * y → orderOf y ≠ 3) : KG115At X S l := by
  intro D N _ hDl ⟨y, hyN, hy3⟩ hND _ _ _
  have hyD : y ∈ D := by
    rw [← hND]
    exact le_normalizer hyN
  exact h y (hDl y hyD) hy3

theorem kg115At_of_card [Finite X] {S : Subgroup X} {l : X}
    (h : ¬ 27 ∣ Nat.card (centralizer {l} : Subgroup X) *
      (MulAut.conj : X →* MulAut X).range.index) : KG115At X S l := by
  intro D N _ hDl _ _ _ _ h27
  have hle : D ≤ centralizer {l} := fun d hd => mem_centralizer_singleton_iff.mpr (hDl d hd)
  exact h (h27.trans (Nat.mul_dvd_mul_right (card_dvd_of_le hle) _))

theorem kg115Excluded_of_at [Finite X] (hc : center X = ⊥) (hno3 : SylowTwoNoThree X)
    (h : ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → ∀ l ∈ S, (∀ s ∈ S, s * l = l * s) →
      l ≠ 1 → KG115At X S l) : KG115Excluded X := by
  intro A B l hA hBA hBi hB hF1 hlB hl1 hlc hF2p
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conj_eq_center, hc]
  have hconj_comm : ∀ u v : X, MulAut.conj u * MulAut.conj v = MulAut.conj v * MulAut.conj u →
      u * v = v * u := fun u v h => hinj (by rw [map_mul, map_mul, h])
  obtain ⟨a, ha⟩ := hB
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [ha]; positivity)
  obtain ⟨T', hT'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 2
    (show 2 ^ a ∣ Nat.card B from ⟨27, ha⟩)
  set T : Subgroup (MulAut X) := T'.map B.subtype with hTdef
  have hTB : T ≤ B := map_subtype_le T'
  have hTcard : Nat.card T = 2 ^ a := by rw [card_map_of_injective B.subtype_injective, hT']
  have hTp : IsPGroup 2 T := IsPGroup.of_card hTcard
  have hTA : ¬ 2 ∣ (T.subgroupOf A).index := by
    have h1 : T.relIndex B * B.relIndex A = T.relIndex A :=
      Subgroup.relIndex_mul_relIndex T B A hTB hBA
    have h2 : T.relIndex B = 27 := by
      have h3 := Subgroup.relIndex_mul_card T B
      rw [inf_eq_left.mpr hTB, hTcard, ha] at h3
      have : 0 < 2 ^ a := by positivity
      nlinarith
    intro h
    rw [← Subgroup.relIndex, ← h1, h2] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · norm_num at h
    · exact hBi h
  set S : Subgroup X := T.comap (MulAut.conj : X →* MulAut X) with hSdef
  have hSp : IsPGroup 2 S := hTp.comap_of_injective _ hinj
  have hSi : ¬ 2 ∣ S.index := by
    rw [hSdef, Subgroup.index_comap]
    exact odd_relIndex_inn hA (hTB.trans hBA) hTA
  have hlS : ∀ s ∈ S, s * l = l * s := fun s hs =>
    hconj_comm s l (hlc _ (hTB hs))
  have hlord : orderOf l ∣ 2 ^ a * 3 ^ 3 := by
    rw [← orderOf_injective _ hinj l, ← Subgroup.orderOf_mk _ hlB,
      show 2 ^ a * 3 ^ 3 = Nat.card B by rw [ha]; norm_num]
    exact orderOf_dvd_natCard _
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.mp hlord
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  have hj : j = 0 := by
    by_contra hj
    set y := l ^ (2 ^ i * 3 ^ (j - 1)) with hydef
    have hy3 : orderOf y = 3 := by
      rw [hydef, orderOf_pow' _ (by positivity), ← hd]
      have hj' : 3 ^ j = 3 ^ (j - 1) * 3 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hj', ← mul_assoc, Nat.gcd_mul_right_left]
      · rw [Nat.mul_div_cancel_left _ (by positivity)]
    exact hno3 S hSp hSi y hy3 fun s hs => (Commute.pow_right (hlS s hs : Commute s l) _).eq
  subst hj
  rw [pow_zero, mul_one] at hd
  have hl2 : IsPGroup 2 (zpowers l) := IsPGroup.of_card (n := i) (by
    rw [Nat.card_zpowers, ← hd])
  have hlmem : l ∈ S := by
    have hlN : zpowers l ≤ normalizer (S : Set X) := by
      rw [zpowers_le]
      exact mem_normalizer_of_commute hlS
    have hsup : IsPGroup 2 ↥(S ⊔ zpowers l) := hSp.to_sup_of_normal_left' hl2 hlN
    have h1 : S.relIndex (S ⊔ zpowers l) ∣ S.index := relIndex_dvd_index_of_le le_sup_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hsup
    have h2 : S.relIndex (S ⊔ zpowers l) ∣ 2 ^ k := by
      rw [← hk]
      exact (S.subgroupOf (S ⊔ zpowers l)).index_dvd_card
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hm0 : m = 0 := by
      by_contra hm0
      apply hSi
      rw [hm] at h1
      exact (dvd_pow_self 2 hm0).trans h1
    rw [hm0, pow_zero, relIndex_eq_one] at hm
    exact hm (mem_sup_right (mem_zpowers l))
  obtain ⟨_, ⟨y, rfl⟩, hy3, -, N, hNI, hyN, hBN, hNB⟩ := hF1
  have hDcard : Nat.card (B.comap (MulAut.conj : X →* MulAut X)) = Nat.card ↥(I ⊓ B) := by
    rw [← card_map_of_injective hinj, map_comap_eq]
  refine h S hSp hSi l hlmem hlS hl1 (B.comap MulAut.conj) (N.comap MulAut.conj)
    (comap_mono hTB) (fun d hd => hconj_comm d l (hlc _ hd))
    ⟨y, hyN, by rwa [orderOf_injective _ hinj] at hy3⟩ ?_ hF2p ⟨a, ?_⟩ ?_
  ·
    ext g
    rw [mem_comap, mem_normalizer_iff]
    constructor
    · intro hg
      refine hNB _ ⟨g, rfl⟩ ?_
      rw [mem_normalizer_iff]
      intro m
      constructor
      · intro hm
        obtain ⟨n, rfl⟩ := hNI hm
        have hn : n ∈ N.comap MulAut.conj := hm
        have := (hg n).mp hn
        rwa [mem_comap, map_mul, map_mul, map_inv] at this
      · intro hm
        have hmI : m ∈ I := by
          have h1 : MulAut.conj g * m * (MulAut.conj g)⁻¹ ∈ I := hNI hm
          have h2 := I.mul_mem (I.mul_mem (I.inv_mem ⟨g, rfl⟩) h1) ⟨g, rfl⟩
          rwa [show (MulAut.conj g)⁻¹ * (MulAut.conj g * m * (MulAut.conj g)⁻¹) *
            MulAut.conj g = m by group] at h2
        obtain ⟨n, rfl⟩ := hmI
        have hn : g * n * g⁻¹ ∈ N.comap MulAut.conj := by
          rw [mem_comap, map_mul, map_mul, map_inv]
          exact hm
        exact (hg n).mpr hn
    · intro hg n
      rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hBN hg)) _
  ·
    rw [hDcard, ← ha]
    exact card_dvd_of_le inf_le_right
  ·
    have : I.Normal := inn_normal
    have h1 := Subgroup.relIndex_mul_card I B
    rw [ha, ← hDcard] at h1
    have h2 : 27 ∣ I.relIndex B * Nat.card (B.comap (MulAut.conj : X →* MulAut X)) :=
      ⟨2 ^ a, by rw [h1]; ring⟩
    rw [mul_comm] at h2
    exact h2.trans (Nat.mul_dvd_mul_left _ (relIndex_dvd_index_of_normal I B))

theorem kg115Excluded_of_data [Finite X] (hc : center X = ⊥) (hD : KG115Data X) :
    KG115Excluded X :=
  kg115Excluded_of_at hc hD.1 fun S hS hSi l hlS hlc hl1 =>
    (hD.2 S hS hSi l hlS hlc hl1).elim kg115At_of_prime kg115At_of_noThree

end Data

end CFSG.Quasithin.H13.KG14726

end
