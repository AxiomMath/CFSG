module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofL3Red

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open Item211Res5Proof
open scoped commutatorElement

section Abstract

variable {M : Type*} [Group M]

@[expose] def OuterCentConcl (I T : Subgroup M) : Prop :=
  (∀ P : Subgroup M, P ≤ threeClosureIn I T → IsPGroup 2 P →
      threeClosureIn I T ≤ Subgroup.normalizer (P : Set M) →
      ∀ x ∈ P, ∀ n ∈ threeClosureIn I T, x * n = n * x) ∧
    ∀ P : Subgroup M, P ≤ I ⊓ Subgroup.centralizer (T : Set M) ⊓
      Subgroup.centralizer (threeClosureIn I T : Set M) → IsPGroup 2 P → IsCyclic P

theorem commute_of_perfect {S : Subgroup M} (hS : ⁅S, S⁆ = S) {x : M}
    (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S)
    (hz : ∀ s ∈ S, ∀ s' ∈ S, (x * s * x⁻¹ * s⁻¹) * s' = s' * (x * s * x⁻¹ * s⁻¹)) :
    ∀ s ∈ S, x * s = s * x := by
  have hle : ⁅S, S⁆ ≤ Subgroup.centralizer ({x} : Set M) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    set za := x * a * x⁻¹ * a⁻¹ with hza
    set zb := x * b * x⁻¹ * b⁻¹ with hzb
    have hzaS : za ∈ S := S.mul_mem (hxS a ha) (S.inv_mem ha)
    have hzbS : zb ∈ S := S.mul_mem (hxS b hb) (S.inv_mem hb)
    have hxa : x * a * x⁻¹ = za * a := by rw [hza]; group
    have hxb : x * b * x⁻¹ = zb * b := by rw [hzb]; group
    have hzab : za * zb = zb * za := hz a ha zb hzbS
    have hzba : zb * a = a * zb := (hz b hb a ha)
    have hzab' : za * b = b * za := hz a ha b hb
    have hc : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      have e1 : x * ⁅a, b⁆ * x⁻¹ =
          (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e1, hxa, hxb]
      have hcS : ⁅a, b⁆ ∈ S := by
        rw [← hS]
        exact Subgroup.commutator_mem_commutator ha hb
      have hzac : za * ⁅a, b⁆ = ⁅a, b⁆ * za := hz a ha _ hcS
      have hzbc : zb * ⁅a, b⁆ = ⁅a, b⁆ * zb := hz b hb _ hcS
      calc za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹
          = za * (a * zb) * b * a⁻¹ * za⁻¹ * b⁻¹ * zb⁻¹ := by group
        _ = za * (zb * a) * b * a⁻¹ * za⁻¹ * b⁻¹ * zb⁻¹ := by rw [hzba]
        _ = za * zb * a * b * a⁻¹ * (za⁻¹ * b⁻¹) * zb⁻¹ := by group
        _ = za * zb * a * b * a⁻¹ * (b⁻¹ * za⁻¹) * zb⁻¹ := by
            rw [show za⁻¹ * b⁻¹ = (b * za)⁻¹ by group, ← hzab', mul_inv_rev]
        _ = za * zb * ⁅a, b⁆ * za⁻¹ * zb⁻¹ := by rw [commutatorElement_def]; group
        _ = za * (zb * ⁅a, b⁆) * za⁻¹ * zb⁻¹ := by group
        _ = za * (⁅a, b⁆ * zb) * za⁻¹ * zb⁻¹ := by rw [hzbc]
        _ = (za * ⁅a, b⁆) * zb * za⁻¹ * zb⁻¹ := by group
        _ = (⁅a, b⁆ * za) * zb * za⁻¹ * zb⁻¹ := by rw [hzac]
        _ = ⁅a, b⁆ * (za * zb) * za⁻¹ * zb⁻¹ := by group
        _ = ⁅a, b⁆ * (zb * za) * za⁻¹ * zb⁻¹ := by rw [hzab]
        _ = ⁅a, b⁆ := by group
    exact (calc x * ⁅a, b⁆ = x * ⁅a, b⁆ * x⁻¹ * x := by group
      _ = ⁅a, b⁆ * x := by rw [hc]).symm
  intro s hs
  rw [← hS] at hs
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hs)).symm

theorem threeClosureIn_le (I T : Subgroup M) :
    threeClosureIn I T ≤ I ⊓ Subgroup.centralizer (T : Set M) :=
  (Subgroup.closure_le _).mpr fun _ h => h.1

theorem le_threeClosureIn {I T S : Subgroup M} (hSC : S ≤ I ⊓ Subgroup.centralizer (T : Set M))
    (hSgen : S ≤ Subgroup.closure {s | s ∈ S ∧ s ^ 3 = 1}) : S ≤ threeClosureIn I T :=
  hSgen.trans (Subgroup.closure_mono fun _ hs => ⟨hSC hs.1, hs.2⟩)

theorem outerCentConcl_of_sub {I T S : Subgroup M}
    (hSC : S ≤ I ⊓ Subgroup.centralizer (T : Set M))
    (hSgen : S ≤ Subgroup.closure {s | s ∈ S ∧ s ^ 3 = 1})
    (hnorm : ∀ c ∈ I ⊓ Subgroup.centralizer (T : Set M), ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (hQ : ∀ Q : Subgroup M, Q ≤ S → IsPGroup 2 Q → (∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) →
      ∀ q ∈ Q, ∀ s ∈ S, q * s = s * q)
    (hperf : ⁅S, S⁆ = S)
    (hcent : ∀ c ∈ I ⊓ Subgroup.centralizer (T : Set M), (∀ s ∈ S, c * s = s * c) →
      ∀ c' ∈ I ⊓ Subgroup.centralizer (T : Set M), c * c' = c' * c)
    (hcyc : ∀ P : Subgroup M, P ≤ I ⊓ Subgroup.centralizer (T : Set M) →
      (∀ x ∈ P, ∀ s ∈ S, x * s = s * x) → IsPGroup 2 P → IsCyclic P) :
    OuterCentConcl I T := by
  have hSN := le_threeClosureIn hSC hSgen
  have hNC := threeClosureIn_le I T
  refine ⟨fun P hPN hP2 hNP x hx n hn => ?_, fun P hP hP2 => ?_⟩
  ·
    have hxC : x ∈ I ⊓ Subgroup.centralizer (T : Set M) := hNC (hPN hx)
    have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => hnorm x hxC s hs
    have hSP : ∀ s ∈ S, ∀ q ∈ P, s * q * s⁻¹ ∈ P := fun s hs q hq =>
      (Subgroup.mem_normalizer_iff.mp (hNP (hSN hs)) q).mp hq
    have hQS := hQ (P ⊓ S) inf_le_right (hP2.to_le inf_le_left) (fun s hs q hq =>
      ⟨hSP s hs q hq.1, S.mul_mem (S.mul_mem hs hq.2) (S.inv_mem hs)⟩)
    have hz : ∀ s ∈ S, ∀ s' ∈ S, (x * s * x⁻¹ * s⁻¹) * s' = s' * (x * s * x⁻¹ * s⁻¹) := by
      intro s hs s' hs'
      have hmemP : x * s * x⁻¹ * s⁻¹ ∈ P := by
        have h1 : s * x⁻¹ * s⁻¹ ∈ P := hSP s hs _ (P.inv_mem hx)
        have e : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
        rw [e]
        exact P.mul_mem hx h1
      have hmemS : x * s * x⁻¹ * s⁻¹ ∈ S := S.mul_mem (hxS s hs) (S.inv_mem hs)
      exact hQS _ ⟨hmemP, hmemS⟩ s' hs'
    have hxcomm := commute_of_perfect hperf hxS hz
    exact hcent x hxC hxcomm n (hNC hn)
  ·
    refine hcyc P (fun y hy => (hP hy).1) (fun y hy s hs => ?_) hP2
    have h := Subgroup.mem_centralizer_iff.mp (hP hy).2 s (hSN hs)
    exact h.symm

theorem isCyclic_of_unique_involution {P : Type*} [CommGroup P] [Finite P] (hP : IsPGroup 2 P)
    (h1 : ∀ a b : P, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b) : IsCyclic P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := P) (Monoid.ExponentExists.of_finite)
  by_contra hncyc
  have hne : Subgroup.zpowers g ≠ ⊤ := by
    intro htop
    exact hncyc ⟨g, fun x => by
      have hx : x ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top x
      exact hx⟩
  have hex : ∃ h : P, h ∉ Subgroup.zpowers g ∧ h ^ 2 ∈ Subgroup.zpowers g := by
    obtain ⟨y, hy⟩ : ∃ y : P, y ∉ Subgroup.zpowers g := by
      by_contra hall
      push Not at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    obtain ⟨e, he⟩ := hP y
    have hex' : ∃ k : ℕ, y ^ 2 ^ k ∈ Subgroup.zpowers g := ⟨e, by rw [he]; exact one_mem _⟩
    let k := Nat.find hex'
    have hk : y ^ 2 ^ k ∈ Subgroup.zpowers g := Nat.find_spec hex'
    have hk0 : k ≠ 0 := by
      intro h0
      have : y ^ 2 ^ k = y := by rw [h0, pow_zero, pow_one]
      exact hy (this ▸ hk)
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨y ^ 2 ^ k', fun hmem => ?_, ?_⟩
    · have := Nat.find_min hex' (show k' < k by omega)
      exact this hmem
    · rw [← pow_mul, ← pow_succ, show k' + 1 = k by omega]
      exact hk
  obtain ⟨h, hh, hh2⟩ := hex
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh2
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) g
  have hord_h : h ^ orderOf g = 1 := by
    rw [hg]
    exact Monoid.pow_exponent_eq_one h
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  ·
    rw [pow_zero] at hm
    rw [hm, pow_one] at hord_h
    exact hh (by rw [hord_h]; exact one_mem _)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hgi : g ^ (i * (2 : ℤ) ^ m') = 1 := by
      have h3 : (h ^ 2) ^ 2 ^ m' = 1 := by
        rw [← pow_mul, show 2 * 2 ^ m' = 2 ^ (m' + 1) by ring, ← hm]
        exact hord_h
      rw [← hi, ← zpow_natCast, ← zpow_mul] at h3
      push_cast at h3
      exact h3
    have hdvd : ((2 ^ (m' + 1) : ℕ) : ℤ) ∣ i * (2 : ℤ) ^ m' := by
      rw [← hm]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hgi
    obtain ⟨j, hj⟩ : (2 : ℤ) ∣ i := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h2 : (2 : ℤ) ^ m' ≠ 0 := pow_ne_zero _ (by norm_num)
      have : i * 2 ^ m' = (2 * c) * 2 ^ m' := by rw [hc]; push_cast; ring
      exact mul_right_cancel₀ h2 this
    set u := h * (g ^ j)⁻¹ with hu
    have hu2 : u ^ 2 = 1 := by
      rw [hu, mul_pow, inv_pow, ← zpow_natCast (g ^ j), ← zpow_mul, ← hi, hj]
      rw [show ((j : ℤ) * ((2 : ℕ) : ℤ)) = 2 * j by push_cast; ring]
      exact mul_inv_cancel _
    have hu1 : u ≠ 1 := by
      intro h1'
      apply hh
      have : h = g ^ j := by rw [hu] at h1'; exact (mul_inv_eq_one.mp h1')
      rw [this]
      exact Subgroup.zpow_mem_zpowers g j
    have hu_out : u ∉ Subgroup.zpowers g := by
      intro hmem
      apply hh
      have : h = u * g ^ j := by rw [hu]; group
      rw [this]
      exact mul_mem hmem (Subgroup.zpow_mem_zpowers g j)
    set v := g ^ 2 ^ m' with hv
    have hv2 : v ^ 2 = 1 := by
      rw [hv, ← pow_mul, show 2 ^ m' * 2 = 2 ^ (m' + 1) by ring, ← hm]
      exact pow_orderOf_eq_one g
    have hv1 : v ≠ 1 := by
      intro h1'
      have hdvd' := orderOf_dvd_of_pow_eq_one h1'
      rw [hm] at hdvd'
      have := Nat.le_of_dvd (by positivity) hdvd'
      have : 2 ^ (m' + 1) ≤ 2 ^ m' := this
      have h2 : 2 ^ m' < 2 ^ (m' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := h1 u v hu2 hv2 hu1 hv1
    exact hu_out (this ▸ Subgroup.npow_mem_zpowers g _)

end Abstract

section Transport

variable {M : Type*} [Group M]

theorem threeClosureIn_map_conj_le {I T : Subgroup M} {a : M}
    (haI : ∀ g : M, g ∈ I → a * g * a⁻¹ ∈ I) :
    (threeClosureIn I T).map (MulAut.conj a).toMonoidHom ≤
      threeClosureIn I (T.map (MulAut.conj a).toMonoidHom) := by
  rw [threeClosureIn, threeClosureIn, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨τ, ⟨hτC, hτ3⟩, rfl⟩
  obtain ⟨hτI, hτT⟩ := Subgroup.mem_inf.mp hτC
  refine ⟨Subgroup.mem_inf.mpr ⟨haI τ hτI, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hτT t ht
    change a * t * a⁻¹ * (a * τ * a⁻¹) = a * τ * a⁻¹ * (a * t * a⁻¹)
    calc a * t * a⁻¹ * (a * τ * a⁻¹) = a * (t * τ) * a⁻¹ := by group
      _ = a * (τ * t) * a⁻¹ := by rw [h]
      _ = a * τ * a⁻¹ * (a * t * a⁻¹) := by group
  · change (a * τ * a⁻¹) ^ 3 = 1
    rw [conj_pow, hτ3, mul_one, mul_inv_cancel]

theorem map_conj_inv_map_conj (T : Subgroup M) (a : M) :
    (T.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = T := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id T
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem threeClosureIn_map_conj {I T : Subgroup M} [I.Normal] (a : M) :
    threeClosureIn I (T.map (MulAut.conj a).toMonoidHom) =
      (threeClosureIn I T).map (MulAut.conj a).toMonoidHom := by
  have haI : ∀ (b g : M), g ∈ I → b * g * b⁻¹ ∈ I := fun b g hg =>
    (inferInstance : I.Normal).conj_mem g hg b
  refine le_antisymm ?_ (threeClosureIn_map_conj_le (haI a))
  have h1 := threeClosureIn_map_conj_le (I := I) (T := T.map (MulAut.conj a).toMonoidHom)
    (haI a⁻¹)
  rw [map_conj_inv_map_conj] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) h1
  rw [Subgroup.map_map] at h2
  convert h2 using 1
  convert (Subgroup.map_id _).symm
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem outerCentConcl_of_conj {I T : Subgroup M} [I.Normal] (a : M)
    (h : OuterCentConcl I (T.map (MulAut.conj a).toMonoidHom)) : OuterCentConcl I T := by
  set κ := (MulAut.conj a).toMonoidHom with hκ
  have hκinj : Function.Injective κ := (MulAut.conj a).injective
  have hN := threeClosureIn_map_conj (I := I) (T := T) a
  have haI : ∀ g : M, g ∈ I → a * g * a⁻¹ ∈ I := fun g hg =>
    (inferInstance : I.Normal).conj_mem g hg a
  obtain ⟨ha, hb⟩ := h
  refine ⟨fun P hPN hP2 hNP x hx n hn => ?_, fun P hP hP2 => ?_⟩
  · have hP'N : P.map κ ≤ threeClosureIn I (T.map κ) := by
      rw [hN]; exact Subgroup.map_mono hPN
    have hP'2 : IsPGroup 2 (P.map κ) := hP2.map κ
    have hNP' : threeClosureIn I (T.map κ) ≤
        Subgroup.normalizer ((P.map κ : Subgroup M) : Set M) := by
      rw [hN]
      exact (Subgroup.map_mono hNP).trans (Subgroup.le_normalizer_map κ)
    have := ha (P.map κ) hP'N hP'2 hNP' (κ x) ⟨x, hx, rfl⟩ (κ n)
      (by rw [hN]; exact ⟨n, hn, rfl⟩)
    apply hκinj
    rw [map_mul, map_mul]
    exact this
  · have hP' : P.map κ ≤ I ⊓ Subgroup.centralizer ((T.map κ : Subgroup M) : Set M) ⊓
        Subgroup.centralizer ((threeClosureIn I (T.map κ) : Subgroup M) : Set M) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := hP hy
      have hyI : y ∈ I := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy').1).1
      have hyT : y ∈ Subgroup.centralizer (T : Set M) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy').1).2
      have hyN : y ∈ Subgroup.centralizer (threeClosureIn I T : Set M) :=
        (Subgroup.mem_inf.mp hy').2
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨haI y hyI, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨t, ht, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hyT t ht]
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [SetLike.mem_coe, hN] at hz
        obtain ⟨n, hn, rfl⟩ := hz
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hyN n hn]
    have hcyc := hb (P.map κ) hP' (hP2.map κ)
    exact isCyclic_of_surjective
      ((Subgroup.equivMapOfInjective P κ hκinj).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective P κ hκinj).symm.surjective

end Transport

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
