module

public import CFSG.Timmesfeld.Closure.Bender

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld.Connectivity

variable {X : Type*} [Group X]

theorem mem_map_conj_inv_iff {M : Subgroup X} {g t : X} :
    t ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * t * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro h
    exact ⟨g * t * g⁻¹, h, by simp [mul_assoc]⟩

theorem fusionStronglyEmbedded_iff (M : Subgroup X) :
    fusionStronglyEmbedded M ↔ BenderSuzuki.IsStronglyEmbeddedOrder M := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g hg => ?_⟩
    have := h3 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g hg => ?_⟩
    exact h3 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))

section Finite

variable [Finite X] {M : Subgroup X}

omit [Finite X] in
theorem mem_of_involution_mem (hM : fusionStronglyEmbedded M) {g t : X} (htM : t ∈ M)
    (htg : g * t * g⁻¹ ∈ M) (ht : orderOf t = 2) : g ∈ M := by
  by_contra hg
  exact not_mem_of_odd_card (hM.2.2 g hg) ht (Subgroup.mem_inf.2 ⟨htM, mem_map_conj_inv_iff.2 htg⟩)

theorem exists_sylow_le (hM : fusionStronglyEmbedded M) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 M) := inferInstance
  set Q' : Subgroup X := (Q : Subgroup M).map M.subtype with hQ'
  have hQ'M : Q' ≤ M := Subgroup.map_subtype_le _
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map _
  have hcardQ' : Nat.card Q' = Nat.card (Q : Subgroup M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have hQeven : 2 ∣ Nat.card Q' := by
    rw [hcardQ', Sylow.card_eq_multiplicity]
    have h2M : 2 ∣ Nat.card M := even_iff_two_dvd.1 hM.2.1
    have hpos : (Nat.card M).factorization 2 ≠ 0 := by
      have := Nat.card_pos (α := M)
      exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_two this.ne' h2M).ne'
    exact dvd_pow_self 2 hpos
  obtain ⟨P, hP⟩ := hQ'2.exists_le_sylow
  refine ⟨P, ?_⟩
  suffices hPQ : (P : Subgroup X) = Q' by rw [hPQ]; exact hQ'M
  by_contra hne
  have hlt : Q'.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm ?_ hP
    intro y hy
    have : (⟨y, hy⟩ : P) ∈ Q'.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyconj : ∀ h ∈ Q', (y : X) * h * (y : X)⁻¹ ∈ Q' := by
    intro h hh
    have := (Subgroup.mem_normalizer_iff.1 hyN ⟨h, hP hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
    exact Subgroup.mem_subgroupOf.1 this
  have hyconj' : ∀ h ∈ Q', (y : X)⁻¹ * h * (y : X) ∈ Q' := by
    intro h hh
    have hhP : (y : X)⁻¹ * h * (y : X) ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem y.2) (hP hh))
        y.2
    have := (Subgroup.mem_normalizer_iff.1 hyN ⟨_, hhP⟩).2 (Subgroup.mem_subgroupOf.2 (by
      simpa [mul_assoc] using hh))
    exact Subgroup.mem_subgroupOf.1 this
  have hyM : (y : X) ∉ M := by
    intro hyM
    set R : Subgroup X := Q' ⊔ Subgroup.zpowers (y : X) with hR
    have hRP : R ≤ P := sup_le hP (by rw [Subgroup.zpowers_le]; exact y.2)
    have hR2 : IsPGroup 2 R := P.isPGroup'.to_le hRP
    have hRM : R ≤ M := sup_le hQ'M (by rw [Subgroup.zpowers_le]; exact hyM)
    have hcomap2 : IsPGroup 2 (R.comap M.subtype) :=
      hR2.comap_of_injective M.subtype Subtype.val_injective
    have hQle : (Q : Subgroup M) ≤ R.comap M.subtype := fun q hq =>
      Subgroup.mem_sup_left ⟨q, hq, rfl⟩
    have heq := Q.is_maximal' hcomap2 hQle
    have hmem : (⟨y, hyM⟩ : M) ∈ R.comap M.subtype :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [heq] at hmem
    exact hyQ (Subgroup.mem_subgroupOf.2 ⟨_, hmem, rfl⟩)
  have hle : Q' ≤ M ⊓ M.map (MulAut.conj (y : X)⁻¹).toMonoidHom := by
    intro h hh
    exact Subgroup.mem_inf.2 ⟨hQ'M hh, mem_map_conj_inv_iff.2 (hQ'M (hyconj h hh))⟩
  have hodd := hM.2.2 (y : X) hyM
  have hdvd := Subgroup.card_dvd_of_le hle
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hQeven.trans hdvd))

theorem exists_conj_mem_sylow (P : Sylow 2 X) {t : X} {n : ℕ} (ht : t ^ 2 ^ n = 1) :
    ∃ g : X, g * t * g⁻¹ ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  obtain ⟨R, hR⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨t, hR (Subgroup.mem_zpowers t), by simp [MulAut.conj_apply]⟩

theorem isConj_of_orderOf_eq_two (hM : fusionStronglyEmbedded M) {s t : X} (hs : orderOf s = 2)
    (ht : orderOf t = 2) : IsConj s t := by
  obtain ⟨P, hPM⟩ := exists_sylow_le hM
  have hs2 : s ^ 2 ^ 1 = 1 := by rw [pow_one, ← hs, pow_orderOf_eq_one]
  have ht2 : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← ht, pow_orderOf_eq_one]
  obtain ⟨a, ha⟩ := exists_conj_mem_sylow P hs2
  obtain ⟨b, hb⟩ := exists_conj_mem_sylow P ht2
  have haM := hPM ha
  have hbM := hPM hb
  have hord : ∀ (c u : X), orderOf u = 2 → orderOf (c * u * c⁻¹) = 2 := fun c u hu => by
    rw [orderOf_conj_eq, hu]
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hall
    push Not at hall
    exact hM.1 (eq_top_iff.2 fun x _ => hall x)
  have hjM : g * (b * t * b⁻¹) * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
    ⟨_, hbM, by simp [MulAut.conj_apply]⟩
  have h1 : IsConj (a * s * a⁻¹) (g * (b * t * b⁻¹) * g⁻¹) :=
    isConj_of_stronglyEmbedded hM hg haM (hord a s hs) hjM (hord g _ (hord b t ht))
  have hsa : IsConj s (a * s * a⁻¹) := isConj_iff.2 ⟨a, rfl⟩
  have htb : IsConj (g * (b * t * b⁻¹) * g⁻¹) t := by
    refine isConj_iff.2 ⟨(g * b)⁻¹, ?_⟩
    group
  exact hsa.trans (h1.trans htb)

theorem fusionStronglyEmbedded.of_le (hM : fusionStronglyEmbedded M) {K : Subgroup X}
    (hMK : M ≤ K) (hK : K ≠ ⊤) : fusionStronglyEmbedded K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hK, ?_, fun g hg => ?_⟩
  · exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hM.2.1).trans (Subgroup.card_dvd_of_le hMK))
  by_contra hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (Nat.not_odd_iff_even.1 hodd).two_dvd
  have ht2 : orderOf (t : X) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htK : (t : X) ∈ K := (Subgroup.mem_inf.1 t.2).1
  have hgtK : g * (t : X) * g⁻¹ ∈ K := mem_map_conj_inv_iff.1 (Subgroup.mem_inf.1 t.2).2
  obtain ⟨P, hPM⟩ := exists_sylow_le hM
  have hPK : (P : Subgroup X) ≤ K := hPM.trans hMK
  have key : ∀ u ∈ K, orderOf u = 2 → ∃ k ∈ K, k * u * k⁻¹ ∈ (P : Subgroup X) := by
    intro u huK hu
    have hu2 : (⟨u, huK⟩ : K) ^ 2 ^ 1 = 1 := by
      apply Subtype.ext
      rw [pow_one]
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hu, pow_orderOf_eq_one]
    obtain ⟨k, hk⟩ := exists_conj_mem_sylow (P.subtype hPK) hu2
    refine ⟨k, k.2, ?_⟩
    have := Subgroup.mem_subgroupOf.1 hk
    simpa using this
  obtain ⟨k, hkK, hk⟩ := key _ htK ht2
  obtain ⟨k', hk'K, hk'⟩ := key _ hgtK (by rw [orderOf_conj_eq, ht2])
  have hmem : (k' * g * k⁻¹) * (k * (t : X) * k⁻¹) * (k' * g * k⁻¹)⁻¹ ∈ M := by
    have : (k' * g * k⁻¹) * (k * (t : X) * k⁻¹) * (k' * g * k⁻¹)⁻¹ =
        k' * (g * (t : X) * g⁻¹) * k'⁻¹ := by group
    rw [this]
    exact hPM hk'
  have hh := mem_of_involution_mem hM (hPM hk) hmem (by rw [orderOf_conj_eq, ht2])
  apply hg
  have : g = k'⁻¹ * (k' * g * k⁻¹) * k := by group
  rw [this]
  exact K.mul_mem (K.mul_mem (K.inv_mem hk'K) (hMK hh)) hkK

end Finite

end CFSG.Timmesfeld.Bridge
