module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofA10T
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
  {φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)} {g : Perm (Fin 10)}

omit [Finite G] in
theorem mk_eq_of_projTen_eq [(kerAO2 A Y₀).Normal] {u v : ↥(A ⊔ Y₀)} (hu : (u : G) ∈ Y₀)
    (hv : (v : G) ∈ Y₀) (h : projTen Y₀ φ ⟨u, hu⟩ = projTen Y₀ φ ⟨v, hv⟩) :
    QuotientGroup.mk' (kerAO2 A Y₀) u = QuotientGroup.mk' (kerAO2 A Y₀) v := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, kerAO2,
    Subgroup.mem_subgroupOf]
  have := inv_mul_mem_of_projTen_eq h
  simpa using this

omit [Finite G] in
theorem projTen_eq_of_mk_eq [(kerAO2 A Y₀).Normal] {u v : ↥(A ⊔ Y₀)} (hu : (u : G) ∈ Y₀)
    (hv : (v : G) ∈ Y₀)
    (h : QuotientGroup.mk' (kerAO2 A Y₀) u = QuotientGroup.mk' (kerAO2 A Y₀) v) :
    projTen Y₀ φ ⟨u, hu⟩ = projTen Y₀ φ ⟨v, hv⟩ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, kerAO2,
    Subgroup.mem_subgroupOf] at h
  have h1 := projTen_eq_one_of_mem (φ := φ) (y := (⟨u, hu⟩ : ↥Y₀)⁻¹ * ⟨v, hv⟩)
    (by simpa using h)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem cimg_eq_k (hP : A10Pic A c L Y₀ φ g) {X : Subgroup G} (hXY : X ≤ Y₀)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX3 : ¬ 3 ∣ Nat.card X)
    (hX0 : cimg Y₀ φ g X ≠ ⊥) :
    cimg Y₀ φ g X = kOne ∨ cimg Y₀ φ g X = kTwo ∨ cimg Y₀ φ g X = kThree := by
  have hER := eTwentySeven_le_normalizer_cimg hP hAX
  rcases le_kOne_or_le_kTwo_or_le_kThree (not_three_dvd_card_cimg hXY hX3) hER with h1 | h1 | h1
  · exact Or.inl (kF_irreducible (Or.inl rfl) h1 hER hX0)
  · exact Or.inr (Or.inl (kF_irreducible (Or.inr (Or.inl rfl)) h1 hER hX0))
  · exact Or.inr (Or.inr (kF_irreducible (Or.inr (Or.inr rfl)) h1 hER hX0))

@[expose] def kInv : Fin 4 → Perm (Fin 10) := ![1, kOneF 1, kTwoF 1, kThreeF 1]

theorem kInv_prod_sq : ∀ x y : Fin 4, x ≠ y → x ≠ 0 → y ≠ 0 →
    ((kInv x * kInv y) ^ 2) ^ 3 = 1 ∧ (kInv x * kInv y) ^ 2 ≠ 1 := by
  decide +kernel

theorem kInv_ne_one : ∀ x : Fin 4, x ≠ 0 → kInv x ≠ 1 := by
  decide +kernel

theorem exists_kInv {K : Subgroup (Perm (Fin 10))} (hK : K = kOne ∨ K = kTwo ∨ K = kThree) :
    ∃ x : Fin 4, x ≠ 0 ∧ kInv x ∈ K := by
  rcases hK with rfl | rfl | rfl
  · exact ⟨1, by decide, ⟨1, rfl⟩⟩
  · exact ⟨2, by decide, ⟨1, rfl⟩⟩
  · exact ⟨3, by decide, ⟨1, rfl⟩⟩

theorem eq_of_kInv_mem {K K' : Subgroup (Perm (Fin 10))}
    (hK : K = kOne ∨ K = kTwo ∨ K = kThree) (hK' : K' = kOne ∨ K' = kTwo ∨ K' = kThree)
    {x : Fin 4} (hx : x ≠ 0) (hxK : kInv x ∈ K) (hxK' : kInv x ∈ K') : K = K' := by
  obtain ⟨hd12, hd13, hd23⟩ := kF_disjoint
  have h1 := kInv_ne_one x hx
  rcases hK with rfl | rfl | rfl <;> rcases hK' with rfl | rfl | rfl
  all_goals first
    | rfl
    | (obtain ⟨m, hm⟩ := hxK
       obtain ⟨n, hn⟩ := hxK'
       first
        | (have h0 := hd12 m n (hm.symm.trans hn); subst h0; exact absurd hm h1)
        | (have h0 := hd12 n m (hn.symm.trans hm); subst h0; exact absurd hn h1)
        | (have h0 := hd13 m n (hm.symm.trans hn); subst h0; exact absurd hm h1)
        | (have h0 := hd13 n m (hn.symm.trans hm); subst h0; exact absurd hn h1)
        | (have h0 := hd23 m n (hm.symm.trans hn); subst h0; exact absurd hm h1)
        | (have h0 := hd23 n m (hn.symm.trans hm); subst h0; exact absurd hn h1))

theorem three_dvd_of_a10 [(kerAO2 A Y₀).Normal] {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀)
    (hne : imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀)) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := projTen Y₀ φ with hπ
  set T := S ⊓ Y₀ with hT
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  obtain ⟨hwA, hwY⟩ := Subgroup.mem_inf.mp hw
  have hTY : T ≤ Y₀ := inf_le_right
  have hT'Y : T' ≤ Y₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hwY (hTY hx)) (inv_mem hwY)
  have hTN : T ≤ A ⊔ Y₀ := hTY.trans le_sup_right
  have hT'N : T' ≤ A ⊔ Y₀ := hT'Y.trans le_sup_right
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hT3 : ¬ 3 ∣ Nat.card T := Proof171.not_three_dvd_of_isPGroup_two (hS2.to_le inf_le_left)
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hT3
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hx
    have ha' : w⁻¹ * a * w ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwA) a).mp ha
      simpa using this
    have hat : (w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hAT ha') t).mp ht
    refine ⟨(w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹, hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKT := cimg_eq h hP h142
  obtain ⟨K, hK, hKT'⟩ : ∃ K : Subgroup (Perm (Fin 10)), (K = kOne ∨ K = kTwo) ∧
      cimg Y₀ φ g T = K := by
    rcases hKT with h1 | h1
    · exact ⟨kOne, Or.inl rfl, h1⟩
    · exact ⟨kTwo, Or.inr rfl, h1⟩
  have hK3 : K = kOne ∨ K = kTwo ∨ K = kThree := by tauto
  obtain ⟨x, hx0, hxK⟩ := exists_kInv hK3
  obtain ⟨u, huT, hue⟩ := mem_cimg.mp (hKT' ▸ hxK : kInv x ∈ cimg Y₀ φ g T)
  have hT'0 : cimg Y₀ φ g T' ≠ ⊥ := by
    intro h0
    have huw : g * π (⟨w, hwY⟩ * u * ⟨w, hwY⟩⁻¹) * g⁻¹ ∈ cimg Y₀ φ g T' :=
      mem_cimg.mpr ⟨_, ⟨u, huT, by simp [MulAut.conj_apply]⟩, rfl⟩
    rw [h0, Subgroup.mem_bot, map_mul, map_mul, map_inv] at huw
    have h1 : π u = 1 := by
      have := congrArg (fun z => (π ⟨w, hwY⟩)⁻¹ * (g⁻¹ * z * g) * π ⟨w, hwY⟩) huw
      simpa [mul_assoc] using this
    rw [h1, mul_one, mul_inv_cancel] at hue
    exact kInv_ne_one x hx0 hue.symm
  have hK' := cimg_eq_k hP hT'Y hAT' hT'3 hT'0
  obtain ⟨y, hy0, hyK⟩ := exists_kInv hK'
  obtain ⟨u', hu'T, hu'e⟩ := mem_cimg.mp hyK
  have hxy : x ≠ y := by
    intro hxy'
    subst hxy'
    apply hne
    have hcimg : cimg Y₀ φ g T' = cimg Y₀ φ g T := by
      rw [hKT']
      exact (eq_of_kInv_mem hK3 hK' hx0 hxK hyK).symm
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have hvT' : (v : G) ∈ T' := Subgroup.mem_subgroupOf.mp hv
      have hvY : (v : G) ∈ Y₀ := hT'Y hvT'
      obtain ⟨z, hzT, hze⟩ := mem_cimg.mp (hcimg ▸ mem_cimg.mpr ⟨⟨v, hvY⟩, hvT', rfl⟩ :
        g * π ⟨v, hvY⟩ * g⁻¹ ∈ cimg Y₀ φ g T)
      have he : π z = π ⟨v, hvY⟩ := by
        have := congrArg (fun z => g⁻¹ * z * g) hze
        simpa [mul_assoc] using this
      refine ⟨⟨z, Subgroup.mem_sup_right z.2⟩, Subgroup.mem_subgroupOf.mpr hzT, ?_⟩
      exact mk_eq_of_projTen_eq z.2 hvY he
    · rintro _ ⟨v, hv, rfl⟩
      have hvT : (v : G) ∈ T := Subgroup.mem_subgroupOf.mp hv
      have hvY : (v : G) ∈ Y₀ := hTY hvT
      obtain ⟨z, hzT, hze⟩ := mem_cimg.mp (hcimg.symm ▸ mem_cimg.mpr ⟨⟨v, hvY⟩, hvT, rfl⟩ :
        g * π ⟨v, hvY⟩ * g⁻¹ ∈ cimg Y₀ φ g T')
      have he : π z = π ⟨v, hvY⟩ := by
        have := congrArg (fun z => g⁻¹ * z * g) hze
        simpa [mul_assoc] using this
      refine ⟨⟨z, Subgroup.mem_sup_right z.2⟩, Subgroup.mem_subgroupOf.mpr hzT, ?_⟩
      exact mk_eq_of_projTen_eq z.2 hvY he
  obtain ⟨hz3, hz1⟩ := kInv_prod_sq x y hxy hx0 hy0
  set v : ↥Y₀ := (u * u') ^ 2 with hv
  have hve : g * π v * g⁻¹ = (kInv x * kInv y) ^ 2 := by
    rw [hv, ← hue, ← hu'e, hπ]
    simp only [map_mul, pow_two]
    group
  have hvJ : (v : G) ∈ T ⊔ T' := by
    rw [hv]
    exact pow_mem (mul_mem (Subgroup.mem_sup_left huT) (Subgroup.mem_sup_right hu'T)) 2
  set v' : ↥(A ⊔ Y₀) := ⟨v, Subgroup.mem_sup_right v.2⟩ with hv'
  set vb := QuotientGroup.mk' (kerAO2 A Y₀) v' with hvb
  have hvbJ : vb ∈ imgY0 A Y₀ T ⊔ imgY0 A Y₀ T' := by
    rw [← Proof1712.imgY0_sup hTN hT'N]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr hvJ, rfl⟩
  have hπv3 : projTen Y₀ φ (v ^ 3) = 1 := by
    have : g * π (v ^ 3) * g⁻¹ = 1 := by
      rw [map_pow, ← conj_pow, hve]
      exact hz3
    rwa [conj_eq_one_iff] at this
  have hY3 : ((v' ^ 3 : ↥(A ⊔ Y₀)) : G) ∈ Y₀ := by
    have e : ((v' ^ 3 : ↥(A ⊔ Y₀)) : G) = ((v ^ 3 : ↥Y₀) : G) := by simp [hv']
    rw [e]
    exact (v ^ 3).2
  have e1 : (⟨_, hY3⟩ : ↥Y₀) = v ^ 3 := Subtype.ext (by simp [hv'])
  have e2 : (⟨((1 : ↥(A ⊔ Y₀)) : G), one_mem Y₀⟩ : ↥Y₀) = 1 := rfl
  have hvb3 : vb ^ 3 = 1 := by
    have h1 : projTen Y₀ φ ⟨_, hY3⟩ = projTen Y₀ φ ⟨((1 : ↥(A ⊔ Y₀)) : G), one_mem Y₀⟩ := by
      rw [e1, e2, hπv3, map_one]
    have := mk_eq_of_projTen_eq hY3 (one_mem Y₀) h1
    rw [hvb, ← map_pow, this, map_one]
  have hvb1 : vb ≠ 1 := by
    intro h1
    rw [hvb, ← map_one (QuotientGroup.mk' (kerAO2 A Y₀))] at h1
    have h2 := projTen_eq_of_mk_eq (φ := φ) (show ((v' : ↥(A ⊔ Y₀)) : G) ∈ Y₀ from v.2)
      (one_mem Y₀) h1
    have e3 : (⟨(v' : G), v.2⟩ : ↥Y₀) = v := Subtype.ext rfl
    rw [e3, e2, map_one] at h2
    apply hz1
    rw [← hve, h2, mul_one, mul_inv_cancel]
  rw [← orderOf_eq_prime hvb3 hvb1]
  exact Subgroup.orderOf_dvd_natCard _ hvbJ

end CFSG.RankThree.PartTwo.Sec17.Proof17Res4
