module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.SignalizerFunctor.PermutingSubgroupProducts
public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G]

theorem IsSylowOf.le {q : ℕ} {T U : Subgroup G} (h : IsSylowOf q T U) : T ≤ U := by
  obtain ⟨P, rfl⟩ := h
  exact Subgroup.map_subtype_le _

theorem IsSylowOf.isPGroup {q : ℕ} {T U : Subgroup G} (h : IsSylowOf q T U) : IsPGroup q T := by
  obtain ⟨P, rfl⟩ := h
  exact P.isPGroup'.map U.subtype

theorem IsSylowOf.eq_of_le {q : ℕ} {T U Y : Subgroup G} (h : IsSylowOf q T U)
    (hY : IsPGroup q Y) (hTY : T ≤ Y) (hYU : Y ≤ U) : Y = T := by
  obtain ⟨P, rfl⟩ := h
  have hYP : Y.subgroupOf U = P.toSubgroup :=
    P.is_maximal' hY.comap_subtype (Subgroup.map_le_iff_le_comap.mp hTY)
  calc Y = (Y.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hYU).symm
    _ = P.toSubgroup.map U.subtype := by rw [hYP]

private theorem isSylowOf_of_maximal {q : ℕ} {T U : Subgroup G} (hTU : T ≤ U)
    (hT : IsPGroup q T) (hmax : ∀ Y : Subgroup G, IsPGroup q Y → T ≤ Y → Y ≤ U → Y = T) :
    IsSylowOf q T U := by
  refine ⟨⟨T.subgroupOf U, hT.comap_subtype, ?_⟩, Subgroup.map_subgroupOf_eq_of_le hTU⟩
  intro Q hQ hTQ
  have hQT : Q.map U.subtype = T := by
    refine hmax _ (hQ.map _) ?_ (Subgroup.map_subtype_le Q)
    calc T = (T.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hTU).symm
      _ ≤ Q.map U.subtype := Subgroup.map_mono hTQ
  calc Q = (Q.map U.subtype).comap U.subtype :=
        (Subgroup.comap_map_eq_self_of_injective U.subtype_injective Q).symm
    _ = T.subgroupOf U := congrArg (fun K : Subgroup G => K.comap U.subtype) hQT

theorem IsSylowOf.conj {q : ℕ} {T U : Subgroup G} (h : IsSylowOf q T U) (g : G) :
    IsSylowOf q (conjugateSubgroup g T) (conjugateSubgroup g U) := by
  refine isSylowOf_of_maximal (Subgroup.map_mono h.le) (h.isPGroup.map _) ?_
  intro Y hY hTY hYU
  have hY' : conjugateSubgroup g⁻¹ Y = T := by
    refine h.eq_of_le (hY.map _) ?_ ?_
    · have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hTY
      change conjugateSubgroup g⁻¹ (conjugateSubgroup g T) ≤ conjugateSubgroup g⁻¹ Y at this
      rwa [conjugate_subgroup_inv_cancel] at this
    · have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hYU
      change conjugateSubgroup g⁻¹ Y ≤ conjugateSubgroup g⁻¹ (conjugateSubgroup g U) at this
      rwa [conjugate_subgroup_inv_cancel] at this
  calc Y = conjugateSubgroup g (conjugateSubgroup g⁻¹ Y) := by
        rw [conjugate_subgroup_mul, mul_inv_cancel, conjugate_subgroup_one]
    _ = conjugateSubgroup g T := by rw [hY']

theorem IsSylowOf.le_of_normal [Finite G] {q : ℕ} {T U Y : Subgroup G} (h : IsSylowOf q T U)
    (hYU : Y ≤ U) (hY : IsPGroup q Y) (hN : U ≤ Subgroup.normalizer (Y : Set G)) : Y ≤ T := by
  obtain ⟨P, rfl⟩ := h
  have : (Y.subgroupOf U).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYU).mpr hN
  have hY' : IsPGroup q (Y.subgroupOf U) := hY.comap_subtype
  calc Y = (Y.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hYU).symm
    _ ≤ P.toSubgroup.map U.subtype := Subgroup.map_mono (hY'.le_sylow_of_normal P)

theorem IsSylowOf.card_eq [Finite G] {q : ℕ} (hq : q.Prime) {T T' U : Subgroup G}
    (h : IsSylowOf q T U) (h' : IsSylowOf q T' U) : Nat.card T = Nat.card T' := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, rfl⟩ := h
  obtain ⟨P', rfl⟩ := h'
  rw [Subgroup.card_subtype, Subgroup.card_subtype]
  exact P.card_eq_multiplicity.trans P'.card_eq_multiplicity.symm

private theorem exists_isSylowOf_ge_aux {q : ℕ} {U Y : Subgroup G} (hYU : Y ≤ U)
    (hY : IsPGroup q Y) : ∃ T : Subgroup G, Y ≤ T ∧ IsSylowOf q T U := by
  obtain ⟨P, hP⟩ := hY.comap_subtype (K := U) |>.exists_le_sylow
  refine ⟨P.toSubgroup.map U.subtype, ?_, P, rfl⟩
  calc Y = (Y.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hYU).symm
    _ ≤ P.toSubgroup.map U.subtype := Subgroup.map_mono hP

theorem IsSylowOf.card_le [Finite G] {q : ℕ} (hq : q.Prime) {T U Y : Subgroup G}
    (h : IsSylowOf q T U) (hY : IsPGroup q Y) (hYU : Y ≤ U) : Nat.card Y ≤ Nat.card T := by
  obtain ⟨T', hYT', hT'⟩ := exists_isSylowOf_ge_aux hYU hY
  exact (Subgroup.card_le_of_le hYT').trans (h.card_eq hq hT').ge

theorem IsSylowOf.le_of_le_normalizer [Finite G] {q : ℕ} (hq : q.Prime) {T U Y : Subgroup G}
    (h : IsSylowOf q T U) (hYU : Y ≤ U) (hY : IsPGroup q Y)
    (hN : Y ≤ Subgroup.normalizer (T : Set G)) : Y ≤ T := by
  have hsup : IsPGroup q (T ⊔ Y : Subgroup G) := h.isPGroup.to_sup_of_normal_left' hY hN
  have hTsup : T = T ⊔ Y :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (h.card_le hq hsup (sup_le h.le hYU))
  exact sup_eq_left.mp hTsup.symm

theorem exists_isSylowOf_ge [Finite G] {q : ℕ} (hq : q.Prime) {U Y : Subgroup G} (hYU : Y ≤ U)
    (hY : IsPGroup q Y) : ∃ T : Subgroup G, Y ≤ T ∧ IsSylowOf q T U := by
  have : Fact q.Prime := ⟨hq⟩
  exact exists_isSylowOf_ge_aux hYU hY

private theorem eq_pow_mul_pow_of_prime_support {q r n : ℕ} (hqr : q ≠ r) (hn : n ≠ 0)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ = q ∨ ℓ = r) :
    n = q ^ n.factorization q * r ^ n.factorization r := by
  have hsub : n.factorization.support ⊆ {q, r} := by
    intro ℓ hℓ
    rw [Nat.support_factorization] at hℓ
    have hℓ' := Nat.mem_primeFactors.mp hℓ
    simpa using hsupp ℓ hℓ'.1 hℓ'.2.1
  calc n = n.factorization.prod (fun p k => p ^ k) := (Nat.prod_factorization_pow_eq_self hn).symm
    _ = ∏ p ∈ ({q, r} : Finset ℕ), p ^ n.factorization p :=
        Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _)
    _ = q ^ n.factorization q * r ^ n.factorization r := Finset.prod_pair hqr

theorem subgroupProduct_eq_of_isSylowOf [Finite G] {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) {X P R : Subgroup G}
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ℓ = q ∨ ℓ = r)
    (hP : IsSylowOf q P X) (hR : IsSylowOf r R X) : subgroupProduct P R = (X : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  have hPcard : Nat.card P = q ^ (Nat.card X).factorization q := by
    obtain ⟨Q, rfl⟩ := hP
    rw [Subgroup.card_subtype]
    exact Q.card_eq_multiplicity
  have hRcard : Nat.card R = r ^ (Nat.card X).factorization r := by
    obtain ⟨Q, rfl⟩ := hR
    rw [Subgroup.card_subtype]
    exact Q.card_eq_multiplicity
  have hXcard := eq_pow_mul_pow_of_prime_support hqr (Nat.card_pos (α := X)).ne' hsupp
  generalize (Nat.card X).factorization q = a at hPcard hXcard
  generalize (Nat.card X).factorization r = b at hRcard hXcard
  have hinf : Nat.card (P ⊓ R : Subgroup G) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes (a := Nat.card P) (b := Nat.card R) ?_
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)
    rw [hPcard, hRcard]
    exact ((Nat.coprime_primes hq hr).mpr hqr).pow a b
  refine subgroup_product_eq_of_card_formula X P R hP.le hR.le ?_
  rw [hinf, mul_one, hPcard, hRcard, ← hXcard]

theorem permute_of_subgroupProduct_eq {S R X : Subgroup G} (hS : S ≤ X) (hR : R ≤ X)
    (h : subgroupProduct S R = (X : Set G)) :
    ∀ v ∈ R, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R, v * s = s' * v' := by
  intro v hv s hs
  have hmem : v * s ∈ subgroupProduct S R := by
    rw [h]
    exact X.mul_mem (hR hv) (hS hs)
  obtain ⟨s', hs', v', hv', hsv⟩ := hmem
  exact ⟨s', hs', v', hv', hsv.symm⟩

private theorem le_setLeftStabilizer_of_permute {S R W : Subgroup G} (hRW : R ≤ W)
    (h : ∀ v ∈ R, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R, v * s = s' * v') :
    R ≤ setLeftStabilizer (subgroupProduct S W) := by
  have key : ∀ v ∈ R, ∀ x ∈ subgroupProduct S W, v * x ∈ subgroupProduct S W := by
    intro v hv x hx
    obtain ⟨s, hs, w, hw, rfl⟩ := hx
    obtain ⟨s', hs', v', hv', hvs⟩ := h v hv s hs
    refine ⟨s', hs', v' * w, W.mul_mem (hRW hv') hw, ?_⟩
    show s' * (v' * w) = v * (s * w)
    rw [← mul_assoc, ← hvs, mul_assoc]
  intro v hv
  exact set_left_stabilizer_of_inclusions _ v (key v hv) (key v⁻¹ (R.inv_mem hv))

private theorem permute_of_le_setLeftStabilizer {S W : Subgroup G}
    (h : W ≤ setLeftStabilizer (subgroupProduct S W)) :
    ∀ v ∈ W, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ W, v * s = s' * v' := by
  intro v hv s hs
  have hmem : v * s ∈ subgroupProduct W S := ⟨v, hv, s, hs, rfl⟩
  rw [(permuting_subgroup_product_eq_sup S W h).2] at hmem
  obtain ⟨s', hs', v', hv', hsv⟩ := hmem
  exact ⟨s', hs', v', hv', hsv.symm⟩

theorem permute_sup {S R₁ R₂ : Subgroup G}
    (h₁ : ∀ v ∈ R₁, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R₁, v * s = s' * v')
    (h₂ : ∀ v ∈ R₂, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R₂, v * s = s' * v') :
    ∀ v ∈ R₁ ⊔ R₂, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R₁ ⊔ R₂, v * s = s' * v' :=
  permute_of_le_setLeftStabilizer
    (sup_le (le_setLeftStabilizer_of_permute le_sup_left h₁)
      (le_setLeftStabilizer_of_permute le_sup_right h₂))

theorem permute_conj {S R : Subgroup G}
    (h : ∀ v ∈ R, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ R, v * s = s' * v') {c : G} (hc : c ∈ S) :
    ∀ v ∈ conjugateSubgroup c R, ∀ s ∈ S,
      ∃ s' ∈ S, ∃ v' ∈ conjugateSubgroup c R, v * s = s' * v' := by
  intro v hv s hs
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨s₁, hs₁, r₁, hr₁, h₁⟩ :=
    h r hr (c⁻¹ * s * c) (S.mul_mem (S.mul_mem (S.inv_mem hc) hs) hc)
  refine ⟨c * s₁ * c⁻¹, S.mul_mem (S.mul_mem hc hs₁) (S.inv_mem hc), c * r₁ * c⁻¹,
    Subgroup.mem_map.mpr ⟨r₁, hr₁, rfl⟩, ?_⟩
  change c * r * c⁻¹ * s = c * s₁ * c⁻¹ * (c * r₁ * c⁻¹)
  calc c * r * c⁻¹ * s = c * (r * (c⁻¹ * s * c)) * c⁻¹ := by group
    _ = c * (s₁ * r₁) * c⁻¹ := by rw [h₁]
    _ = c * s₁ * c⁻¹ * (c * r₁ * c⁻¹) := by group

theorem subgroupProduct_eq_sup_of_permute {S V : Subgroup G}
    (h : ∀ v ∈ V, ∀ s ∈ S, ∃ s' ∈ S, ∃ v' ∈ V, v * s = s' * v') :
    subgroupProduct S V = ((S ⊔ V : Subgroup G) : Set G) :=
  (permuting_subgroup_product_eq_sup S V (le_setLeftStabilizer_of_permute le_rfl h)).1

theorem le_sup_conj_of_subgroupProduct_eq {S R X : Subgroup G}
    (h : subgroupProduct S R = (X : Set G)) {c : G} (hcS : c ∈ S) (hcX : c ∈ X) :
    X ≤ S ⊔ conjugateSubgroup c R := by
  intro x hx
  have hy : c⁻¹ * x ∈ subgroupProduct S R := by
    rw [h]
    exact X.mul_mem (X.inv_mem hcX) hx
  obtain ⟨s, hs, r, hr, hsr⟩ := hy
  replace hsr : s * r = c⁻¹ * x := hsr
  have h1 : c * s * c⁻¹ ∈ S ⊔ conjugateSubgroup c R :=
    Subgroup.mem_sup_left (S.mul_mem (S.mul_mem hcS hs) (S.inv_mem hcS))
  have h2 : c * r * c⁻¹ ∈ S ⊔ conjugateSubgroup c R :=
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
  have h3 : c ∈ S ⊔ conjugateSubgroup c R := Subgroup.mem_sup_left hcS
  have h4 := Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have h5 : c * s * c⁻¹ * (c * r * c⁻¹) * c = x :=
    calc c * s * c⁻¹ * (c * r * c⁻¹) * c = c * (s * r) := by group
      _ = c * (c⁻¹ * x) := by rw [hsr]
      _ = x := by group
  rwa [h5] at h4

theorem isSolvable_of_prime_support [Finite G] {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) {X : Subgroup G}
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ℓ = q ∨ ℓ = r) : Group.IsSolvable X := by
  have : Fintype X := Fintype.ofFinite X
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hq hr hqr
    (a := (Nat.card X).factorization q) (b := (Nat.card X).factorization r) ?_
  rw [← Nat.card_eq_fintype_card]
  exact eq_pow_mul_pow_of_prime_support hqr (Nat.card_pos (α := X)).ne' hsupp

end CFSG.SignalizerFunctorTheorem.Glauberman
