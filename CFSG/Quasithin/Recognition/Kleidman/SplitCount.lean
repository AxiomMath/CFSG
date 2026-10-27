module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2NoA4Gen

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Quasithin.SzI47J2NoA4

variable {G : Type*} [Group G]

@[expose] def sqSet (R : Subgroup G) (v : G) : Set G := {r | r ∈ R ∧ r * r = v}

theorem sqSet_subset (R : Subgroup G) (v : G) : sqSet R v ⊆ (R : Set G) := fun _ h => h.1

theorem conj_mem_sqSet {R : Subgroup G} {ρ v w : G} (hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R)
    (hw : ρ * v * ρ⁻¹ = w) {r : G} (hr : r ∈ sqSet R v) : ρ * r * ρ⁻¹ ∈ sqSet R w := by
  refine ⟨hρR r hr.1, ?_⟩
  rw [← hw, ← hr.2]
  group

theorem ncard_sqSet_le {R : Subgroup G} [Finite R] {ρ v w : G}
    (hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R) (hw : ρ * v * ρ⁻¹ = w) :
    (sqSet R v).ncard ≤ (sqSet R w).ncard := by
  have : Finite (R : Set G) := inferInstanceAs (Finite R)
  have hfin : (sqSet R w).Finite := (R : Set G).toFinite.subset (sqSet_subset R w)
  refine Set.ncard_le_ncard_of_injOn (fun r => ρ * r * ρ⁻¹)
    (fun r hr => conj_mem_sqSet hρR hw hr) ?_ hfin
  intro a _ b _ hab
  simpa using hab

theorem mem_normalizer_of_pow_three {R : Subgroup G} {σ : G} (hσ3 : σ ^ 3 = 1)
    (hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) : σ ∈ Subgroup.normalizer (R : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hσR h hh, fun hh => ?_⟩
  have h1 := hσR _ (hσR _ hh)
  have h2 : σ * (σ * (σ * h * σ⁻¹) * σ⁻¹) * σ⁻¹ = h := by
    have : σ * (σ * (σ * h * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * h * (σ * σ * σ)⁻¹ := by group
    rw [this, ← pow_three', hσ3]
    group
  rwa [h2] at h1

theorem false_of_klein_squares {R : Subgroup G} [Finite R] {z t ρ σ : G}
    (hz : z ∈ R) (ht : t ∈ R) (hz2 : z * z = 1) (ht2 : t * t = 1) (hz1 : z ≠ 1) (ht1 : t ≠ 1)
    (hzt : z ≠ t)
    (hcz : ∀ r ∈ R, r * z = z * r) (hct : ∀ r ∈ R, r * t = t * r)
    (hsq : ∀ r ∈ R, r * r = 1 ∨ r * r = z ∨ r * r = t ∨ r * r = z * t)
    (hinv : ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = z ∨ r = t ∨ r = z * t)
    (hRle : Nat.card R ≤ 64) (h12 : 12 ≤ (sqSet R z).ncard)
    (hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R) (hρz : ρ * z * ρ⁻¹ = t) (hρt : ρ * t * ρ⁻¹ = z * t)
    (hσ3 : σ ^ 3 = 1) (hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) (hσz : σ * z = z * σ)
    (hσt : σ * t = t * σ) (hσ : ∃ r ∈ R, σ * r ≠ r * σ) : False := by
  classical
  have : Finite (R : Set G) := inferInstanceAs (Finite R)
  have hRfin : (R : Set G).Finite := (R : Set G).toFinite
  have hzt' : z * t = t * z := hct z hz
  have hzt2 : z * t * (z * t) = 1 := by
    rw [mul_assoc, ← mul_assoc t z t, ← hzt', mul_assoc z t t, ht2, mul_one, hz2]
  have hρzt : ρ * (z * t) * ρ⁻¹ = z := by
    have : ρ * (z * t) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by group
    rw [this, hρz, hρt, ← mul_assoc, ← hzt', mul_assoc, ht2, mul_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzt1 : z * t ≠ 1 := fun h => hzt (by rw [← hzinv]; exact (eq_inv_of_mul_eq_one_right h).symm)
  have hztz : z * t ≠ z := fun h => ht1 (by simpa using h)
  have hztt : z * t ≠ t := fun h => hz1 (by simpa using h)
  have hztR : z * t ∈ R := mul_mem hz ht
  set ℓ := (sqSet R z).ncard with hℓ
  have hℓt : (sqSet R t).ncard = ℓ := le_antisymm
    ((ncard_sqSet_le hρR hρt).trans (ncard_sqSet_le hρR hρzt)) (ncard_sqSet_le hρR hρz)
  have hℓzt : (sqSet R (z * t)).ncard = ℓ := le_antisymm (ncard_sqSet_le hρR hρzt)
    ((ncard_sqSet_le hρR hρz).trans (ncard_sqSet_le hρR hρt))
  set V : Set G := {1, z, t, z * t} with hV
  have hVcard : V.ncard = 4 := by
    rw [hV, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hztt.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hzt, fun h => hztz h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, ht1.symm, hzt1.symm⟩
  have hVsq : ∀ w ∈ V, w * w = 1 := by
    intro w hw
    simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact hz2
    · exact ht2
    · exact hzt2
  have hVR : V ⊆ R := by
    intro w hw
    simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem R
    · exact hz
    · exact ht
    · exact hztR
  have hdisj : ∀ {v w : G}, v ≠ w → Disjoint (sqSet R v) (sqSet R w) := by
    intro v w hvw
    exact Set.disjoint_left.mpr fun r hrv hrw => hvw (hrv.2.symm.trans hrw.2)
  have hdisjV : ∀ {v : G}, v ≠ 1 → Disjoint V (sqSet R v) := by
    intro v hv
    exact Set.disjoint_left.mpr fun r hrV hrv => hv (hrv.2.symm.trans (hVsq r hrV))
  have hpart : (R : Set G) = V ∪ sqSet R z ∪ sqSet R t ∪ sqSet R (z * t) := by
    ext r
    constructor
    · intro hr
      rcases hsq r hr with h | h | h | h
      · left; left; left
        rcases hinv r hr h with rfl | rfl | rfl | rfl <;> simp [hV]
      · left; left; right; exact ⟨hr, h⟩
      · left; right; exact ⟨hr, h⟩
      · right; exact ⟨hr, h⟩
    · rintro (((h | h) | h) | h)
      · exact hVR h
      · exact h.1
      · exact h.1
      · exact h.1
  have hfinS : ∀ v, (sqSet R v).Finite := fun v => hRfin.subset (sqSet_subset R v)
  have hVfin : V.Finite := hRfin.subset hVR
  have hcardR : Nat.card R = 4 + 3 * ℓ := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hpart,
      Set.ncard_union_eq _ ((hVfin.union (hfinS z)).union (hfinS t)) (hfinS _),
      Set.ncard_union_eq _ (hVfin.union (hfinS z)) (hfinS t),
      Set.ncard_union_eq (hdisjV hz1) hVfin (hfinS z), hVcard, hℓt, hℓzt]
    · ring
    · exact Set.disjoint_union_left.mpr ⟨hdisjV ht1, hdisj hzt⟩
    · exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hdisjV hzt1,
        hdisj (fun h => hztz h.symm)⟩, hdisj (fun h => hztt h.symm)⟩
  have hpow4 : ∀ r : R, r ^ 4 = 1 := by
    intro r
    have hr2 : (r : G) * r ∈ V := by
      rcases hsq r r.2 with h | h | h | h <;> rw [h] <;> simp [hV]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    exact hVsq _ hr2
  have h2grp : IsPGroup 2 R := IsPGroup.iff_orderOf.mpr fun r => by
    have hdvd : orderOf r ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hpow4 r)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨i, hi⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp h2grp)
  have hn6 : n = 6 := by
    have hle : 2 ^ n ≤ 2 ^ 6 := by omega
    have hn : n ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    interval_cases n <;> omega
  subst hn6
  have hR64 : Nat.card R = 64 := by rw [hn]; norm_num
  have hℓ20 : ℓ = 20 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := Subgroup.zpowers σ with hPdef
  have hP : IsPGroup 3 P := by
    have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  have hσN : σ ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_of_pow_three hσ3 hσR
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hσN
  have hkR : ∀ k ∈ P, ∀ x ∈ R, k * x * k⁻¹ ∈ R := fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.mp (hPN hk) x).mp hx
  have hkcomm : ∀ k ∈ P, ∀ {w : G}, σ * w = w * σ → k * w = w * k := by
    intro k hk w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ((Commute.zpow_left (show Commute σ w from hw) m) : _)
  have hσzt : σ * (z * t) = z * t * σ := by
    rw [← mul_assoc, hσz, mul_assoc, hσt, mul_assoc]
  have hfix : ∀ {x : G}, (∀ k ∈ P, k * x = x * k) ↔ σ * x = x * σ := by
    intro x
    exact ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h k hk => hkcomm k hk h⟩
  have hSstab : ∀ v, σ * v = v * σ → ∀ k ∈ P, ∀ x ∈ sqSet R v, k * x * k⁻¹ ∈ sqSet R v := by
    intro v hv k hk x hx
    refine ⟨hkR k hk x hx.1, ?_⟩
    have hkv := hkcomm k hk hv
    calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = v := by rw [hx.2, hkv]; group
  set Fx : G → Set G := fun v => {x | x ∈ sqSet R v ∧ σ * x = x * σ} with hFx
  have hFxeq : ∀ v, {x : G | x ∈ sqSet R v ∧ ∀ k ∈ P, k * x = x * k} = Fx v := by
    intro v
    ext x
    simp only [hFx, Set.mem_ofPred_eq, hfix]
  have hFxsub : ∀ v, Fx v ⊆ sqSet R v := fun v _ hx => hx.1
  have hFxfin : ∀ v, (Fx v).Finite := fun v => (hfinS v).subset (hFxsub v)
  have hmod : ∀ v, σ * v = v * σ → (sqSet R v).ncard ≡ (Fx v).ncard [MOD 3] := by
    intro v hv
    have : Finite (sqSet R v) := (hfinS v).to_subtype
    have h := card_modEq_card_fixed 3 P hP (sqSet R v) (hSstab v hv)
    rwa [hFxeq, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  have hfive : ∀ v, σ * v = v * σ → v ∈ R → (sqSet R v).ncard = 20 → 5 ≤ (Fx v).ncard := by
    intro v hv hvR h20
    have hm := hmod v hv
    rw [h20] at hm
    have hne : (Fx v).ncard ≠ 0 := by
      intro h0
      rw [h0] at hm
      exact absurd hm (by decide)
    obtain ⟨r, hr⟩ := Set.nonempty_of_ncard_ne_zero hne
    have hsub : (fun w => r * w) '' V ⊆ Fx v := by
      rintro _ ⟨w, hw, rfl⟩
      have hwR := hVR hw
      have hrw : r * w = w * r := by
        simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · simp
        · exact hcz r hr.1.1
        · exact hct r hr.1.1
        · rw [← mul_assoc, hcz r hr.1.1, mul_assoc, hct r hr.1.1, mul_assoc]
      have hσw : σ * w = w * σ := by
        simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · simp
        · exact hσz
        · exact hσt
        · exact hσzt
      refine ⟨⟨mul_mem hr.1.1 hwR, ?_⟩, ?_⟩
      · calc r * w * (r * w) = r * (w * r) * w := by group
          _ = r * (r * w) * w := by rw [hrw]
          _ = (r * r) * (w * w) := by group
          _ = v := by rw [hr.1.2, hVsq w hw, mul_one]
      · rw [← mul_assoc, hr.2, mul_assoc, hσw, ← mul_assoc]
    have h4 : 4 ≤ (Fx v).ncard := by
      rw [← hVcard, ← Set.ncard_image_of_injective V (mul_right_injective r)]
      exact Set.ncard_le_ncard hsub (hFxfin v)
    have hm' : (Fx v).ncard % 3 = 2 := by
      have := hm.symm
      unfold Nat.ModEq at this
      omega
    omega
  have h5z := hfive z hσz hz (by rw [← hℓ, hℓ20])
  have h5t := hfive t hσt ht (by rw [hℓt, hℓ20])
  have h5zt := hfive (z * t) hσzt hztR (by rw [hℓzt, hℓ20])
  set F : Subgroup G := R ⊓ Subgroup.centralizer ({σ} : Set G) with hF
  have hmemF : ∀ {x : G}, x ∈ F ↔ x ∈ R ∧ σ * x = x * σ := by
    intro x
    simp only [hF, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
  have hFR : F ≤ R := inf_le_left
  have : Finite F := Finite.of_injective (Subgroup.inclusion hFR) (Subgroup.inclusion_injective hFR)
  have hFfin : (F : Set G).Finite := (F : Set G).toFinite
  have hFdvd : Nat.card F ∣ 64 := hR64 ▸ Subgroup.card_dvd_of_le hFR
  have hFmod : Nat.card F % 3 = 1 := by
    have h := card_modEq_card_fixed 3 P hP (R : Set G) (fun k hk x hx => hkR k hk x hx)
    have heq : {x : G | x ∈ (R : Set G) ∧ ∀ k ∈ P, k * x = x * k} = (F : Set G) := by
      ext x
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, hfix, hmemF]
    rw [heq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Nat.card_coe_set_eq (F : Set G),
      SetLike.coe_sort_coe, ← Nat.card_coe_set_eq (R : Set G), SetLike.coe_sort_coe, hR64] at h
    unfold Nat.ModEq at h
    omega
  have hFge : 19 ≤ Nat.card F := by
    have hsub : V ∪ Fx z ∪ Fx t ∪ Fx (z * t) ⊆ (F : Set G) := by
      rintro x (((hx | hx) | hx) | hx)
      · refine hmemF.mpr ⟨hVR hx, ?_⟩
        simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · exact hσz
        · exact hσt
        · exact hσzt
      · exact hmemF.mpr ⟨hx.1.1, hx.2⟩
      · exact hmemF.mpr ⟨hx.1.1, hx.2⟩
      · exact hmemF.mpr ⟨hx.1.1, hx.2⟩
    have hdisjF : ∀ {v w : G}, v ≠ w → Disjoint (Fx v) (Fx w) := fun hvw =>
      (hdisj hvw).mono (hFxsub _) (hFxsub _)
    have hdisjFV : ∀ {v : G}, v ≠ 1 → Disjoint V (Fx v) := fun hv =>
      (hdisjV hv).mono_right (hFxsub _)
    have hcard : (V ∪ Fx z ∪ Fx t ∪ Fx (z * t)).ncard =
        4 + (Fx z).ncard + (Fx t).ncard + (Fx (z * t)).ncard := by
      rw [Set.ncard_union_eq _ ((hVfin.union (hFxfin z)).union (hFxfin t)) (hFxfin _),
        Set.ncard_union_eq _ (hVfin.union (hFxfin z)) (hFxfin t),
        Set.ncard_union_eq (hdisjFV hz1) hVfin (hFxfin z), hVcard]
      · exact Set.disjoint_union_left.mpr ⟨hdisjFV ht1, hdisjF hzt⟩
      · exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hdisjFV hzt1,
          hdisjF (fun h => hztz h.symm)⟩, hdisjF (fun h => hztt h.symm)⟩
    have hFn : (F : Set G).ncard = Nat.card F := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    have := Set.ncard_le_ncard hsub hFfin
    rw [hcard, hFn] at this
    omega
  have hF64 : Nat.card F = 64 := by
    have hmem : Nat.card F ∈ Nat.divisors 64 := Nat.mem_divisors.mpr ⟨hFdvd, by norm_num⟩
    rw [show Nat.divisors 64 = {1, 2, 4, 8, 16, 32, 64} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h <;> omega
  have hFeq : F = R := Subgroup.eq_of_le_of_card_ge hFR (by rw [hF64, hR64])
  obtain ⟨r, hr, hσr⟩ := hσ
  exact hσr (hmemF.mp (hFeq ▸ hr)).2

end CFSG.Quasithin.Kleidman
