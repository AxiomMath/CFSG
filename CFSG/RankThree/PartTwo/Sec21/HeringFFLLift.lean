module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)

private theorem card_comap_mk {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (K : Subgroup (X ⧸ Z)) :
    Nat.card (K.comap (QuotientGroup.mk' Z)) = Nat.card K * Nat.card Z := by
  have h1 : (K.comap (QuotientGroup.mk' Z)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective Z)
  have h2 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' Z))
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1] at h2
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h2, h4, ← h3]
  ring

private theorem isNilpotent_comap {X : Type} [Group X] (Z : Subgroup X) [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (V : Subgroup (X ⧸ Z)) [Group.IsNilpotent V] :
    Group.IsNilpotent (V.comap (QuotientGroup.mk' Z)) := by
  refine Subgroup.isNilpotent_of_ker_le_center
    (((QuotientGroup.mk' Z).comp (V.comap (QuotientGroup.mk' Z)).subtype).codRestrict V
      (fun x => x.2)) ?_
  intro g hg
  have h0 := MonoidHom.mem_ker.mp hg
  have h1 : QuotientGroup.mk' Z (g : X) = 1 := by
    have h2 := congrArg Subtype.val h0
    exact h2
  have hgZ : (g : X) ∈ Z := (QuotientGroup.eq_one_iff (N := Z) (g : X)).mp h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hZc hgZ) (y : X)

private theorem exists_normal_two_subgroup (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]
    (h2 : 2 ∣ Nat.card G) :
    ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧ P.Normal ∧
      ∀ g : G, (∃ k : ℕ, g ^ 2 ^ k = 1) → g ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hSn : S.toSubgroup.Normal := inferInstance
  refine ⟨S.toSubgroup, ?_, S.isPGroup', hSn, ?_⟩
  · intro hbot
    have h := S.not_dvd_index
    rw [hbot, Subgroup.index_bot] at h
    exact h h2
  · intro g hg
    obtain ⟨k, hk⟩ := hg
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hcard : Nat.card (Subgroup.zpowers g) = 2 ^ j := by
      rw [Nat.card_zpowers, hj]
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
    haveI := Sylow.unique_of_normal S inferInstance
    have hQS : Q = S := Subsingleton.elim Q S
    rw [hQS] at hQ
    exact hQ (Subgroup.mem_zpowers g)

theorem exists_e9_normalizing_two_of_quotient {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (h : ∃ E V : Subgroup (X ⧸ Z), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧
      IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set (X ⧸ Z))) :
    ∃ E V : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set X) := by
  obtain ⟨E, V, hE, hE9, hV, hV2, hEV⟩ := h
  obtain ⟨hEc, hEexp⟩ := hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ee, hEe⟩ : ∃ S : Subgroup X, S = E.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  obtain ⟨Vv, hVv⟩ : ∃ S : Subgroup X, S = V.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  have memEe : ∀ x : X, x ∈ Ee ↔ QuotientGroup.mk' Z x ∈ E := fun x => by
    rw [hEe, Subgroup.mem_comap]
  have memVv : ∀ x : X, x ∈ Vv ↔ QuotientGroup.mk' Z x ∈ V := fun x => by
    rw [hVv, Subgroup.mem_comap]
  have hcardEe : Nat.card Ee = 9 * Nat.card Z := by
    rw [hEe, card_comap_mk Z E, hE9]
  have hcardVv : Nat.card Vv = Nat.card V * Nat.card Z := by
    rw [hVv, card_comap_mk Z V]
  obtain ⟨Q, hQEe, hQcard⟩ : ∃ Q : Subgroup X, Q ≤ Ee ∧ Nat.card Q = 9 := by
    have hdvd : 3 ^ 2 ∣ Nat.card Ee := ⟨Nat.card Z, by rw [hcardEe]; norm_num⟩
    obtain ⟨P3, hP3⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    exact ⟨P3.map Ee.subtype, Subgroup.map_subtype_le P3,
      (Subgroup.card_map_of_injective Ee.subtype_injective).trans (hP3.trans (by norm_num))⟩
  have hQinj : ∀ x ∈ Q, QuotientGroup.mk' Z x = 1 → x = 1 := by
    intro x hx hxZ
    have hxZ' : x ∈ Z := (QuotientGroup.eq_one_iff (N := Z) x).mp hxZ
    have h9 : x ^ 9 = 1 := by
      have h := (pow_card_eq_one' : (⟨x, hx⟩ : ↥Q) ^ Nat.card ↥Q = 1)
      rw [hQcard] at h
      exact congrArg Subtype.val h
    have h3 : x ^ Nat.card Z = 1 := by
      have h := (pow_card_eq_one' : (⟨x, hxZ'⟩ : ↥Z) ^ Nat.card ↥Z = 1)
      exact congrArg Subtype.val h
    have hgcd : Nat.gcd 9 (Nat.card Z) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 2
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3))
    have hx1 := (pow_gcd_eq_one (a := x) (m := 9) (n := Nat.card Z)).mpr ⟨h9, h3⟩
    rw [hgcd, pow_one] at hx1
    exact hx1
  have hπE : ∀ x ∈ Q, QuotientGroup.mk' Z x ∈ E := fun x hx => (memEe x).mp (hQEe hx)
  have hinj : ∀ x ∈ Q, ∀ y ∈ Q, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := by
      apply hQinj _ (Q.mul_mem hx (Q.inv_mem hy))
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp h1
  have hEcomm : ∀ u v : X ⧸ Z, u ∈ E → v ∈ E → u * v = v * u := by
    intro u v hu hv
    have h := hEc.is_comm.comm (⟨u, hu⟩ : ↥E) ⟨v, hv⟩
    exact congrArg Subtype.val h
  have hQea : IsElemAbelian 3 Q := by
    unfold IsElemAbelian
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · show a * b = b * a
      apply Subtype.ext
      show (a : X) * b = (b : X) * a
      apply hinj _ (Q.mul_mem a.2 b.2) _ (Q.mul_mem b.2 a.2)
      rw [map_mul, map_mul]
      exact hEcomm _ _ (hπE _ a.2) (hπE _ b.2)
    · apply hinj _ (Q.pow_mem hx 3) 1 Q.one_mem
      rw [map_pow, hEexp _ (hπE x hx), map_one]
  haveI : Group.IsNilpotent V := IsPGroup.isNilpotent hV2
  have hnilVv : Group.IsNilpotent Vv := by
    subst hVv
    exact isNilpotent_comap Z hZc V
  have h2V : 2 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
    have h1 : 1 < Nat.card V := (Subgroup.one_lt_card_iff_ne_bot V).mpr hV
    rw [hn] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 2 hn0
  have h2Vv : 2 ∣ Nat.card Vv := by
    rw [hcardVv]
    exact Dvd.dvd.mul_right h2V _
  obtain ⟨P, hPne, hPpg, hPnorm, hPsyl⟩ := exists_normal_two_subgroup (↥Vv) h2Vv
  obtain ⟨W, hWmem, hWne, hWpg⟩ : ∃ W : Subgroup X,
      (∀ g : X, g ∈ W ↔ g ∈ Vv ∧ ∃ k : ℕ, g ^ 2 ^ k = 1) ∧ W ≠ ⊥ ∧ IsPGroup 2 W := by
    refine ⟨P.map Vv.subtype, ?_, ?_, ?_⟩
    · intro g
      constructor
      · intro hg
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
        refine ⟨y.2, ?_⟩
        obtain ⟨k, hk⟩ := hPpg ⟨y, hy⟩
        refine ⟨k, ?_⟩
        have h := congrArg Subtype.val (congrArg Subtype.val hk)
        simpa using h
      · rintro ⟨hgV, k, hk⟩
        have hmem : (⟨g, hgV⟩ : ↥Vv) ∈ P := by
          apply hPsyl
          refine ⟨k, ?_⟩
          apply Subtype.ext
          simpa using hk
        exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    · have hcardW : Nat.card ↥(P.map Vv.subtype) = Nat.card P :=
        Subgroup.card_map_of_injective Vv.subtype_injective
      have h1 : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hPne
      exact (Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hcardW]; exact h1)
    · obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPpg
      exact IsPGroup.of_card (n := m)
        (by rw [Subgroup.card_map_of_injective Vv.subtype_injective]; exact hm)
  have hconj : ∀ x ∈ Q, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro x hx w hw
    obtain ⟨hwVv, k, hk⟩ := (hWmem w).mp hw
    rw [hWmem]
    refine ⟨?_, k, ?_⟩
    · rw [memVv, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_set_normalizer_iff.mp (hEV (hπE x hx)) _).mp ((memVv w).mp hwVv)
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hQW : Q ≤ Subgroup.normalizer (W : Set X) := by
    intro x hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj x hx h hh, fun hh => ?_⟩
    have h' := hconj x⁻¹ (Q.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'
  exact ⟨Q, W, hQea, hQcard, hWne, hWpg, hQW⟩

end CFSG.RankThree.PartTwo.Sec21
