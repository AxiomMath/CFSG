module

public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five.TorusSep

variable {Y : Type*} [Group Y]

@[expose] def IsCentInv (T : Subgroup Y) (x : Y) : Prop :=
  x ∈ T ∧ x * x = 1 ∧ ∀ y ∈ T, x * y = y * x

variable {T : Subgroup Y}

theorem IsCentInv.comm {x y : Y} (hx : IsCentInv T x) (hy : IsCentInv T y) : x * y = y * x :=
  hx.2.2 y hy.1

theorem IsCentInv.mul {x y : Y} (hx : IsCentInv T x) (hy : IsCentInv T y) :
    IsCentInv T (x * y) := by
  refine ⟨T.mul_mem hx.1 hy.1, ?_, fun z hz => ?_⟩
  · calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hx.comm hy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx.2.1, hy.2.1, one_mul]
  · calc x * y * z = x * (y * z) := by group
      _ = x * (z * y) := by rw [hy.2.2 z hz]
      _ = (x * z) * y := by group
      _ = z * x * y := by rw [hx.2.2 z hz]
      _ = z * (x * y) := by group

theorem IsCentInv.conj {x f : Y} (hx : IsCentInv T x) (hf : f ∈ Subgroup.normalizer (T : Set Y)) :
    IsCentInv T (f * x * f⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hf x).mp hx.1, ?_, fun z hz => ?_⟩
  · calc f * x * f⁻¹ * (f * x * f⁻¹) = f * (x * x) * f⁻¹ := by group
      _ = 1 := by rw [hx.2.1, mul_one, mul_inv_cancel]
  · have hz' : f⁻¹ * z * f ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hf) z).mp hz
      rwa [inv_inv] at h
    calc f * x * f⁻¹ * z = f * (x * (f⁻¹ * z * f)) * f⁻¹ := by group
      _ = f * ((f⁻¹ * z * f) * x) * f⁻¹ := by rw [hx.2.2 _ hz']
      _ = z * (f * x * f⁻¹) := by group

theorem conj_ne_one {f t : Y} (ht : t ≠ 1) : f * t * f⁻¹ ≠ 1 := by
  intro h
  apply ht
  calc t = f⁻¹ * (f * t * f⁻¹) * f := by group
    _ = 1 := by rw [h]; group

theorem eq_mul_of_mul_mul_eq_one {x y z : Y} (hxy : x * y = y * x) (hx : x * x = 1)
    (hy : y * y = 1) (h : x * y * z = 1) : z = x * y := by
  have hz : z = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [hz, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy, hxy]

variable {F : Subgroup Y}

theorem centralizes_of_mem
    (hV : ∀ x : Y, x ≠ 1 → x ^ 3 = 1 → ∀ u v : Y, u * u = 1 → v * v = 1 → u * v = v * u →
      x * u = u * x → x * v = v * x → u = 1 ∨ v = 1 ∨ u = v)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF3 : ∀ a ∈ F, a ^ 3 = 1)
    (hFT : F ≤ Subgroup.normalizer (T : Set Y)) {h s : Y} (hh : h ∈ F) (hh1 : h ≠ 1)
    (hs : IsCentInv T s) (hs1 : s ≠ 1) (hhs : h * s = s * h) : ∀ φ ∈ F, φ * s = s * φ := by
  intro φ hφ
  have hv := hs.conj (hFT hφ)
  have hhv : h * (φ * s * φ⁻¹) = (φ * s * φ⁻¹) * h := by
    have hφh : φ * h = h * φ := hFc φ hφ h hh
    calc h * (φ * s * φ⁻¹) = (h * φ) * s * φ⁻¹ := by group
      _ = φ * (h * s) * φ⁻¹ := by rw [← hφh]; group
      _ = φ * (s * h) * φ⁻¹ := by rw [hhs]
      _ = φ * s * (φ⁻¹ * (φ * h)) * φ⁻¹ := by group
      _ = φ * s * (φ⁻¹ * (h * φ)) * φ⁻¹ := by rw [hφh]
      _ = (φ * s * φ⁻¹) * h := by group
  rcases hV h hh1 (hF3 h hh) s (φ * s * φ⁻¹) hs.2.1 hv.2.1 (hs.comm hv) hhs hhv with h1 | h1 | h1
  · exact absurd h1 hs1
  · exact absurd h1 (conj_ne_one hs1)
  · calc φ * s = (φ * s * φ⁻¹) * φ := by group
      _ = s * φ := by rw [← h1]

theorem conj_conj (a b t : Y) : a * (b * t * b⁻¹) * a⁻¹ = (a * b) * t * (a * b)⁻¹ := by group

theorem norm_comm {h t : Y} (hF : h ∈ Subgroup.normalizer (T : Set Y)) (ht : IsCentInv T t)
    (h3 : h * (h * h) = 1) :
    h * (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) =
      (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * h := by
  have hF2 : h * h ∈ Subgroup.normalizer (T : Set Y) := mul_mem hF hF
  have ha := ht.conj hF
  have hb := ht.conj hF2
  have hab := ha.mul hb
  have e2 : h * ((h * h) * t * (h * h)⁻¹) * h⁻¹ = t := by
    rw [conj_conj, h3, one_mul, inv_one, mul_one]
  have hconj : h * (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * h⁻¹ =
      t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹) := by
    calc h * (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * h⁻¹ =
        (h * t * h⁻¹) * (h * (h * t * h⁻¹) * h⁻¹) * (h * ((h * h) * t * (h * h)⁻¹) * h⁻¹) := by
          group
      _ = ((h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * t := by rw [conj_conj, e2]
      _ = t * ((h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) := hab.comm ht
      _ = t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹) := by group
  calc h * (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) =
      (h * (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * h⁻¹) * h := by group
    _ = (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) * h := by rw [hconj]

theorem conj_eq_of_norms {f₁ f₂ t : Y} (hf₁ : f₁ ∈ Subgroup.normalizer (T : Set Y))
    (hf₂ : f₂ ∈ Subgroup.normalizer (T : Set Y)) (h12 : f₁ * f₂ = f₂ * f₁) (ht : IsCentInv T t)
    (hR1 : t * (f₁ * t * f₁⁻¹) * ((f₁ * f₁) * t * (f₁ * f₁)⁻¹) = 1)
    (hR2 : t * (f₂ * t * f₂⁻¹) * ((f₂ * f₂) * t * (f₂ * f₂)⁻¹) = 1)
    (hR3 : t * ((f₁ * f₂) * t * (f₁ * f₂)⁻¹) *
      (((f₁ * f₂) * (f₁ * f₂)) * t * ((f₁ * f₂) * (f₁ * f₂))⁻¹) = 1) :
    f₂ * t * f₂⁻¹ = f₁ * t * f₁⁻¹ := by
  have hN := fun {x : Y} (hx : x ∈ Subgroup.normalizer (T : Set Y)) => ht.conj hx
  have iA : IsCentInv T (f₁ * t * f₁⁻¹) := hN hf₁
  have iB : IsCentInv T (f₂ * t * f₂⁻¹) := hN hf₂
  have iC : IsCentInv T ((f₁ * f₂) * t * (f₁ * f₂)⁻¹) := hN (mul_mem hf₁ hf₂)
  have iB₂ : IsCentInv T ((f₂ * f₂) * t * (f₂ * f₂)⁻¹) := hN (mul_mem hf₂ hf₂)
  have iD : IsCentInv T ((f₁ * (f₂ * f₂)) * t * (f₁ * (f₂ * f₂))⁻¹) :=
    hN (mul_mem hf₁ (mul_mem hf₂ hf₂))
  have hR2' : (f₁ * t * f₁⁻¹) * ((f₁ * f₂) * t * (f₁ * f₂)⁻¹) *
      ((f₁ * (f₂ * f₂)) * t * (f₁ * (f₂ * f₂))⁻¹) = 1 := by
    have h := congrArg (fun z => f₁ * z * f₁⁻¹) hR2
    simp only [mul_one, mul_inv_cancel] at h
    rw [← h]
    group
  have hc1 : (f₂ * f₂) * f₁ = f₁ * (f₂ * f₂) := by
    rw [mul_assoc, ← h12, ← mul_assoc, ← h12, mul_assoc]
  have hc2 : (f₂ * f₂) * (f₁ * f₁) = (f₁ * f₂) * (f₁ * f₂) := by
    calc (f₂ * f₂) * (f₁ * f₁) = f₂ * ((f₂ * f₁) * f₁) := by group
      _ = f₂ * ((f₁ * f₂) * f₁) := by rw [h12]
      _ = (f₂ * f₁) * (f₂ * f₁) := by group
      _ = (f₁ * f₂) * (f₁ * f₂) := by rw [h12]
  have hR1'' : ((f₂ * f₂) * t * (f₂ * f₂)⁻¹) * ((f₁ * (f₂ * f₂)) * t * (f₁ * (f₂ * f₂))⁻¹) *
      (((f₁ * f₂) * (f₁ * f₂)) * t * ((f₁ * f₂) * (f₁ * f₂))⁻¹) = 1 := by
    have h := congrArg (fun z => (f₂ * f₂) * z * (f₂ * f₂)⁻¹) hR1
    simp only [mul_one, mul_inv_cancel] at h
    rw [← h, ← hc1, ← hc2]
    group
  have e1 := eq_mul_of_mul_mul_eq_one (ht.comm iC) ht.2.1 iC.2.1 hR3
  have e2 := eq_mul_of_mul_mul_eq_one (iB₂.comm iD) iB₂.2.1 iD.2.1 hR1''
  have e3 := eq_mul_of_mul_mul_eq_one (ht.comm iB) ht.2.1 iB.2.1 hR2
  have e4 := eq_mul_of_mul_mul_eq_one (iA.comm iC) iA.2.1 iC.2.1 hR2'
  set A := f₁ * t * f₁⁻¹ with hA
  set B := f₂ * t * f₂⁻¹ with hB
  set C := (f₁ * f₂) * t * (f₁ * f₂)⁻¹ with hC
  have h5 : t * C = t * B * (A * C) := by rw [← e1, e2, e3, e4]
  have h6 : B * A = 1 := by
    have h7 : C = B * A * C := by
      calc C = t⁻¹ * (t * C) := by group
        _ = t⁻¹ * (t * B * (A * C)) := by rw [h5]
        _ = B * A * C := by group
    calc B * A = B * A * C * C⁻¹ := by group
      _ = C * C⁻¹ := by rw [← h7]
      _ = 1 := mul_inv_cancel C
  calc B = (B * A) * A⁻¹ := by group
    _ = A⁻¹ := by rw [h6, one_mul]
    _ = A := inv_eq_of_mul_eq_one_right iA.2.1

theorem exists_involution_centralized [Finite Y]
    (hV : ∀ x : Y, x ≠ 1 → x ^ 3 = 1 → ∀ u v : Y, u * u = 1 → v * v = 1 → u * v = v * u →
      x * u = u * x → x * v = v * x → u = 1 ∨ v = 1 ∨ u = v)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hFT : F ≤ Subgroup.normalizer (T : Set Y)) :
    ∃ t : Y, t ≠ 1 ∧ t * t = 1 ∧ ∀ f ∈ F, f * t = t * f := by
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hF3 : ∀ a ∈ F, a ^ 3 = 1 := hFe.2
  obtain ⟨t, ht, ht1⟩ : ∃ t : Y, IsCentInv T t ∧ t ≠ 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnt : Nontrivial T := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact hT1
    have hZ := hT2.center_nontrivial
    have hZ2 : IsPGroup 2 (Subgroup.center T) := hT2.to_subgroup _
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    refine ⟨((z : T) : Y), ⟨(z : T).2, ?_, fun y hy => ?_⟩, ?_⟩
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center T => ((w : T) : Y)) h1
      simpa [sq] using h2
    · have h1 := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact (congrArg Subtype.val h1).symm
    · intro h1
      have h2 : z = 1 := Subtype.ext (Subtype.ext h1)
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨f₁, hf₁F, hf₁1⟩ : ∃ f₁ ∈ F, f₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hcon
    rw [hbot, Subgroup.card_bot] at hF9
    exact absurd hF9 (by norm_num)
  have hz3 : Nat.card (Subgroup.zpowers f₁) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hF3 f₁ hf₁F) hf₁1]
  obtain ⟨f₂, hf₂F, hf₂z⟩ : ∃ f₂ ∈ F, f₂ ∉ Subgroup.zpowers f₁ := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ Subgroup.zpowers f₁ := hcon
    have := Subgroup.card_le_of_le hle
    rw [hF9, hz3] at this
    exact absurd this (by norm_num)
  have hN1 := hFT hf₁F
  have hN2 := hFT hf₂F
  have h12 : f₁ * f₂ = f₂ * f₁ := hFc f₁ hf₁F f₂ hf₂F
  have hf12 : f₁ * f₂ ≠ 1 := by
    intro h
    apply hf₂z
    have : f₂ = f₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers f₁)
  have hnorm : ∀ h : Y, h ∈ F → h ≠ 1 →
      t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹) ≠ 1 →
        ∃ s : Y, s ≠ 1 ∧ s * s = 1 ∧ ∀ f ∈ F, f * s = s * f := by
    intro h hhF hh1 hne
    have hN := hFT hhF
    have hs : IsCentInv T (t * (h * t * h⁻¹) * ((h * h) * t * (h * h)⁻¹)) :=
      (ht.mul (ht.conj hN)).mul (ht.conj (mul_mem hN hN))
    have h3 : h * (h * h) = 1 := by rw [← pow_three]; exact hF3 h hhF
    exact ⟨_, hne, hs.2.1, centralizes_of_mem hV hFc hF3 hFT hhF hh1 hs hne
      (norm_comm hN ht h3)⟩
  by_cases hA : t * (f₁ * t * f₁⁻¹) * ((f₁ * f₁) * t * (f₁ * f₁)⁻¹) = 1
  · by_cases hB : t * (f₂ * t * f₂⁻¹) * ((f₂ * f₂) * t * (f₂ * f₂)⁻¹) = 1
    · by_cases hC : t * ((f₁ * f₂) * t * (f₁ * f₂)⁻¹) *
          (((f₁ * f₂) * (f₁ * f₂)) * t * ((f₁ * f₂) * (f₁ * f₂))⁻¹) = 1
      · have heq := conj_eq_of_norms hN1 hN2 h12 ht hA hB hC
        have hu : f₁⁻¹ * f₂ ∈ F := mul_mem (Subgroup.inv_mem _ hf₁F) hf₂F
        have hu1 : f₁⁻¹ * f₂ ≠ 1 := by
          intro h
          apply hf₂z
          rw [← (inv_mul_eq_one.mp h)]
          exact Subgroup.mem_zpowers f₁
        have hut : (f₁⁻¹ * f₂) * t = t * (f₁⁻¹ * f₂) := by
          calc (f₁⁻¹ * f₂) * t = f₁⁻¹ * (f₂ * t * f₂⁻¹) * f₂ := by group
            _ = f₁⁻¹ * (f₁ * t * f₁⁻¹) * f₂ := by rw [heq]
            _ = t * (f₁⁻¹ * f₂) := by group
        exact ⟨t, ht1, ht.2.1, centralizes_of_mem hV hFc hF3 hFT hu hu1 ht ht1 hut⟩
      · exact hnorm _ (mul_mem hf₁F hf₂F) hf12 hC
    · exact hnorm f₂ hf₂F (fun h => hf₂z (h ▸ Subgroup.one_mem _)) hB
  · exact hnorm f₁ hf₁F hf₁1 hA

end CFSG.RankThree.PartTwo.Sec4.Res417Five.TorusSep
