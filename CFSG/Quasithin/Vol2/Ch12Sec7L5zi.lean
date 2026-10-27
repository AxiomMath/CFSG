module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin.NoTransv

section Comm

variable {W : Type*} [CommGroup W]

@[expose] def commHom (φ : MulAut W) : W →* W where
  toFun w := w⁻¹ * φ w
  map_one' := by rw [inv_one, map_one, one_mul]
  map_mul' a b := by
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm]

theorem commHom_apply (φ : MulAut W) (w : W) : commHom φ w = w⁻¹ * φ w := rfl

theorem apply_eq_mul (φ : MulAut W) (w : W) : φ w = w * commHom φ w := by
  rw [commHom_apply, mul_inv_cancel_left]

theorem range_commHom_conj (φ ψ : MulAut W) :
    (commHom (ψ * φ * ψ⁻¹)).range = (commHom φ).range.map ψ.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨commHom φ (ψ⁻¹ w), ⟨ψ⁻¹ w, rfl⟩, ?_⟩
    show ψ ((ψ⁻¹ w)⁻¹ * φ (ψ⁻¹ w)) = w⁻¹ * (ψ * φ * ψ⁻¹) w
    rw [map_mul, map_inv, MulAut.apply_inv_self, MulAut.mul_apply, MulAut.mul_apply]
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    refine ⟨ψ w, ?_⟩
    show (ψ w)⁻¹ * (ψ * φ * ψ⁻¹) (ψ w) = ψ (w⁻¹ * φ w)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]

theorem card_range_commHom_conj (φ ψ : MulAut W) :
    Nat.card (commHom (ψ * φ * ψ⁻¹)).range = Nat.card (commHom φ).range := by
  rw [range_commHom_conj, Subgroup.card_map_of_injective ψ.injective]

theorem pow_fortyEight_eq_one [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {a b : MulAut W}
    (ha : Nat.card (commHom a).range ≤ 2) (hb : Nat.card (commHom b).range ≤ 2) :
    (a * b) ^ 48 = 1 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Subgroup W,
      S = ((commHom a).range.subtype.coprod (commHom b).range.subtype).range := ⟨_, rfl⟩
  have hAS : ∀ w, commHom a w ∈ S := fun w => by
    rw [hS]
    exact ⟨(⟨commHom a w, w, rfl⟩, 1), by simp⟩
  have hBS : ∀ w, commHom b w ∈ S := fun w => by
    rw [hS]
    exact ⟨(1, ⟨commHom b w, w, rfl⟩), by simp⟩
  have hScard : Nat.card S ≤ 4 := by
    have h1 : Nat.card S ≤ Nat.card ((commHom a).range × (commHom b).range) := by
      rw [hS]
      exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    rw [Nat.card_prod] at h1
    calc Nat.card S ≤ _ := h1
      _ ≤ 2 * 2 := Nat.mul_le_mul ha hb
      _ = 4 := rfl
  have hPmul : ∀ φ ψ : MulAut W, ((∀ s ∈ S, φ s ∈ S) ∧ ∀ w, commHom φ w ∈ S) →
      ((∀ s ∈ S, ψ s ∈ S) ∧ ∀ w, commHom ψ w ∈ S) →
      (∀ s ∈ S, (φ * ψ) s ∈ S) ∧ ∀ w, commHom (φ * ψ) w ∈ S := by
    intro φ ψ hφ hψ
    refine ⟨fun s hs => hφ.1 _ (hψ.1 s hs), fun w => ?_⟩
    have e : commHom (φ * ψ) w = commHom ψ w * commHom φ (ψ w) := by
      rw [commHom_apply, commHom_apply, commHom_apply, MulAut.mul_apply]
      group
    rw [e]
    exact S.mul_mem (hψ.2 w) (hφ.2 _)
  have hP1 : ∀ φ : MulAut W, (∀ w, commHom φ w ∈ S) →
      (∀ s ∈ S, φ s ∈ S) ∧ ∀ w, commHom φ w ∈ S := fun φ h =>
    ⟨fun s hs => by rw [apply_eq_mul]; exact S.mul_mem hs (h s), h⟩
  have hPg := hPmul a b (hP1 a hAS) (hP1 b hBS)
  have hPpow : ∀ n : ℕ, (∀ s ∈ S, ((a * b) ^ n) s ∈ S) ∧ ∀ w, commHom ((a * b) ^ n) w ∈ S := by
    intro n
    induction n with
    | zero =>
      refine hP1 _ fun w => ?_
      rw [pow_zero, commHom_apply, MulAut.one_apply, inv_mul_cancel]
      exact S.one_mem
    | succ n ih =>
      rw [pow_succ]
      exact hPmul _ _ ih hPg
  have hinj : Function.Injective (fun s : ↥S => (⟨(a * b) s, hPg.1 s s.2⟩ : ↥S)) := by
    intro s t hst
    exact Subtype.ext ((a * b).injective (congrArg Subtype.val hst))
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ↥S, σ = Equiv.ofBijective _ hinj.bijective_of_finite :=
    ⟨_, rfl⟩
  have hσpow : ∀ (n : ℕ) (s : ↥S), (((σ ^ n) s : ↥S) : W) = ((a * b) ^ n) s := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply, hσ]
      rfl
  have hσ24 : σ ^ 24 = 1 := by
    have h1 : orderOf σ ∣ 24 := by
      refine (orderOf_dvd_natCard σ).trans ?_
      rw [Nat.card_perm]
      exact (Nat.factorial_dvd_factorial hScard).trans (by decide)
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hfix : ∀ s ∈ S, ((a * b) ^ 24) s = s := by
    intro s hs
    have := hσpow 24 ⟨s, hs⟩
    rw [hσ24, Equiv.Perm.one_apply, Subtype.coe_mk] at this
    rw [← this]
  have h48 : ((a * b) ^ 24) ^ 2 = 1 := by
    refine MulEquiv.ext fun w => ?_
    have hc := (hPpow 24).2 w
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, apply_eq_mul ((a * b) ^ 24) w, map_mul,
      hfix _ hc, apply_eq_mul ((a * b) ^ 24) w, mul_assoc, ← pow_two, hW, mul_one]
  calc (a * b) ^ 48 = ((a * b) ^ 24) ^ 2 := by rw [← pow_mul]
    _ = 1 := h48

end Comm

@[expose] def alt6a : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[expose] def alt6b : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 4, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem alt6_conj : ∀ b : alternatingGroup (Fin 6), b * b = 1 → b ≠ 1 →
    ∃ k : alternatingGroup (Fin 6), k * alt6a * k⁻¹ = b := by decide +kernel

theorem alt6_conj_ab : ∃ k : alternatingGroup (Fin 6), k * alt6a * k⁻¹ = alt6b := by
  decide +kernel

theorem alt6_ord5 : (alt6a * alt6b) ^ 5 = 1 ∧ alt6a * alt6b ≠ 1 := by decide +kernel

section Kernel

variable {Λ : Type*} [Group Λ]

theorem exists_mem_ker {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (ψ : Λ →* MulAut W) (π : Λ →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {r : Λ} (hr2 : π r * π r = 1) (hr1 : π r ≠ 1) (hψr : Nat.card (commHom (ψ r)).range ≤ 2) :
    ∃ k ∈ ψ.ker, π k ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k₀, hk₀⟩ := alt6_conj (π r) hr2 hr1
  obtain ⟨m, hm⟩ := alt6_conj_ab
  obtain ⟨h5, hne⟩ := alt6_ord5
  obtain ⟨g, hg⟩ := hπ (k₀ * m * k₀⁻¹)
  have hs : π (g * r * g⁻¹) = k₀ * alt6b * k₀⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg, ← hk₀, ← hm]
    group
  have hψs : Nat.card (commHom (ψ (g * r * g⁻¹))).range ≤ 2 := by
    rw [map_mul, map_mul, map_inv, card_range_commHom_conj]
    exact hψr
  refine ⟨(r * (g * r * g⁻¹)) ^ 48, ?_, fun h1 => ?_⟩
  · rw [MonoidHom.mem_ker, map_pow, map_mul]
    exact pow_fortyEight_eq_one hW hψr hψs
  · rw [map_pow, map_mul, hs, ← hk₀,
      show k₀ * alt6a * k₀⁻¹ * (k₀ * alt6b * k₀⁻¹) = k₀ * (alt6a * alt6b) * k₀⁻¹ by group,
      conj_pow] at h1
    have h48 : (alt6a * alt6b) ^ 48 = 1 := by
      have e : (alt6a * alt6b) ^ 48 = k₀⁻¹ * (k₀ * (alt6a * alt6b) ^ 48 * k₀⁻¹) * k₀ := by group
      rw [e, h1]
      group
    have ho : orderOf (alt6a * alt6b) = 5 := orderOf_eq_prime h5 hne
    have := orderOf_dvd_of_pow_eq_one h48
    rw [ho] at this
    norm_num at this

theorem eq_top_of_not_mem_center [Finite Λ] {O : Subgroup Λ} [O.Normal] (hO2 : IsPGroup 2 O)
    (hq : CFSG.IsQuasisimple (Λ ⧸ O))
    (hno2 : ∀ (N : Subgroup Λ) [N.Normal], IsPGroup 2 (Λ ⧸ N) → N = ⊤)
    {N : Subgroup Λ} [hN : N.Normal] {k : Λ} (hkN : k ∈ N)
    (hk : QuotientGroup.mk' O k ∉ Subgroup.center (Λ ⧸ O)) : N = ⊤ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (hN.map (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)) with h | h
  · refine hno2 N fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : QuotientGroup.mk' O y ∈ N.map (QuotientGroup.mk' O) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hny⟩ := hy
    have ho : n⁻¹ * y ∈ O := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hny
      exact QuotientGroup.eq.mp hny
    obtain ⟨j, hj⟩ := hO2 ⟨_, ho⟩
    refine ⟨j, ?_⟩
    have hj' : (n⁻¹ * y) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have e : QuotientGroup.mk' N y = QuotientGroup.mk' N (n⁻¹ * y) := by
      rw [map_mul, map_inv, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
        inv_one, one_mul]
    rw [e, ← map_pow, hj', map_one]
  · exact absurd (h (Subgroup.mem_map_of_mem _ hkN)) hk

theorem eq_one_of_transv [Finite Λ] {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (ψ : Λ →* MulAut W) {O : Subgroup Λ} [O.Normal]
    (hO2 : IsPGroup 2 O) (hq : CFSG.IsQuasisimple (Λ ⧸ O))
    (hcen : Nat.card (Subgroup.center (Λ ⧸ O)) = 3)
    (e : (Λ ⧸ O) ⧸ Subgroup.center (Λ ⧸ O) ≃* alternatingGroup (Fin 6))
    (hno2 : ∀ (N : Subgroup Λ) [N.Normal], IsPGroup 2 (Λ ⧸ N) → N = ⊤)
    {r : Λ} (hr2 : r * r ∈ O) (hr1 : r ∉ O) (hψr : Nat.card (commHom (ψ r)).range ≤ 2) :
    ψ = 1 := by
  obtain ⟨π, hπ⟩ : ∃ π : Λ →* alternatingGroup (Fin 6), π = e.toMonoidHom.comp
      ((QuotientGroup.mk' (Subgroup.center (Λ ⧸ O))).comp (QuotientGroup.mk' O)) := ⟨_, rfl⟩
  have hπapp : ∀ x, π x = e (QuotientGroup.mk' _ (QuotientGroup.mk' O x)) := fun x => by
    rw [hπ]
    rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O p
    exact ⟨x, by rw [hπapp, hq]⟩
  have hπc : ∀ x : Λ, π x = 1 ↔ QuotientGroup.mk' O x ∈ Subgroup.center (Λ ⧸ O) := by
    intro x
    rw [hπapp, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (QuotientGroup.mk' O x)
  have hO1 : ∀ x ∈ O, QuotientGroup.mk' O x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  have hr2' : π r * π r = 1 := by
    rw [← map_mul, hπc, hO1 _ hr2]
    exact Subgroup.one_mem _
  have hr1' : π r ≠ 1 := by
    intro h1
    have hc := (hπc r).mp h1
    have h3 : (QuotientGroup.mk' O r) ^ 3 = 1 := by
      have := orderOf_dvd_natCard (⟨_, hc⟩ : Subgroup.center (Λ ⧸ O))
      rw [hcen] at this
      have h' := orderOf_dvd_iff_pow_eq_one.mp this
      simpa using congrArg Subtype.val h'
    have h2 : (QuotientGroup.mk' O r) ^ 2 = 1 := by
      rw [← map_pow, pow_two]
      exact hO1 _ hr2
    apply hr1
    have h1' : QuotientGroup.mk' O r = 1 := by
      calc QuotientGroup.mk' O r =
          (QuotientGroup.mk' O r) ^ 3 * ((QuotientGroup.mk' O r) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, mul_one]
    exact (QuotientGroup.eq_one_iff r).mp h1'
  obtain ⟨k, hk, hπk⟩ := exists_mem_ker hW ψ π hπs hr2' hr1' hψr
  have hkc : QuotientGroup.mk' O k ∉ Subgroup.center (Λ ⧸ O) := fun hc => hπk ((hπc k).mpr hc)
  have htop := eq_top_of_not_mem_center hO2 hq hno2 (N := ψ.ker) hk hkc
  ext1 x
  have hx : x ∈ ψ.ker := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [MonoidHom.mem_ker] at hx
  rw [hx, MonoidHom.one_apply]

end Kernel

end CFSG.Quasithin.NoTransv
