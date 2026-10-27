module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.ABGLocalTools
open CFSG.LocalAnalysis.GorensteinLyons (mem_normalizer_iff_conjugate_eq)

variable {H : Type*} [Group H]

theorem factorization_pow_mul_pow {p r a b : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) :
    (r ^ b * p ^ a).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) (pow_ne_zero _ hp.ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
    Finsupp.smul_apply, hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd
      (fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp h).symm), smul_eq_mul, smul_eq_mul,
    mul_zero, mul_one, zero_add]

theorem normal_prime_core_fixes_ambient_coprime_plane_factor_pair [Finite H] {r p : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hrp : r ≠ p) {X Y : Subgroup H} (hXY : X ≤ Y)
    (hXn : (X.subgroupOf Y).Normal) (hcard : Nat.card (X ⧸ pCore r X) = p ^ 2)
    {K₁ K₂ : Subgroup H}
    (hperm : ∀ y ∈ Y, ({conjugate K₁ y, conjugate K₂ y} : Set (Subgroup H)) = {K₁, K₂})
    (hXK₁ : X ≤ normalizer (K₁ : Set H)) (hXK₂ : X ≤ normalizer (K₂ : Set H))
    {P : Subgroup H} (hP : IsSylowOf p P X) (hPinf : (P ⊓ K₁) ⊓ (P ⊓ K₂) = ⊥)
    (hP₁ : Nat.card (P ⊓ K₁ : Subgroup H) = p) (hP₂ : Nat.card (P ⊓ K₂ : Subgroup H) = p) :
    (∀ R : Subgroup H, R ≤ Y → (R.subgroupOf Y).Normal → IsPGroup r R →
      R ≤ normalizer (K₁ : Set H) ⊓ normalizer (K₂ : Set H) ∧
        ∀ x ∈ R, ∀ g ∈ X, g⁻¹ * (x * g * x⁻¹) ∈ inSubgroup (pCore r) X) ∧
      inSubgroup (pCore r) Y ≤ normalizer (K₁ : Set H) ⊓ normalizer (K₂ : Set H) ∧
      (K₁.subgroupOf X).map (QuotientGroup.mk' (pCore r X)) =
        ((P ⊓ K₁).subgroupOf X).map (QuotientGroup.mk' (pCore r X)) ∧
      (K₂.subgroupOf X).map (QuotientGroup.mk' (pCore r X)) =
        ((P ⊓ K₂).subgroupOf X).map (QuotientGroup.mk' (pCore r X)) ∧
      Nat.card (((P ⊓ K₁).subgroupOf X).map (QuotientGroup.mk' (pCore r X))) = p ∧
      Nat.card (((P ⊓ K₂).subgroupOf X).map (QuotientGroup.mk' (pCore r X))) = p ∧
      ((P ⊓ K₁).subgroupOf X).map (QuotientGroup.mk' (pCore r X)) ≠
        ((P ⊓ K₂).subgroupOf X).map (QuotientGroup.mk' (pCore r X)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  set Q := pCore r X with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hPX : P ≤ X := hP.le
  have hXnorm : ∀ y ∈ Y, ∀ g ∈ X, y * g * y⁻¹ ∈ X := by
    intro y hy g hg
    exact hXn.conj_mem ⟨g, hXY hg⟩ hg ⟨y, hy⟩
  have hXQp : IsPGroup p (X ⧸ Q) := IsPGroup.of_card hcard
  have hQr : IsPGroup r Q := pCore_isPGroup
  have hmemQ : ∀ g : X, g ∈ Q ↔ (g : H) ∈ inSubgroup (pCore r) X := fun g =>
    (Subgroup.mem_map_iff_mem X.subtype_injective).symm
  have hPQ : P.subgroupOf X ⊓ Q = ⊥ := by
    have hPp : IsPGroup p (P.subgroupOf X) :=
      hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hQr
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp hr).mpr (Ne.symm hrp))
  have hπinj : ∀ a ∈ P.subgroupOf X, ∀ b ∈ P.subgroupOf X, π a = π b → a = b := by
    intro a ha b hb hab
    have h := QuotientGroup.eq.mp hab
    have h' : a⁻¹ * b ∈ P.subgroupOf X ⊓ Q := Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, h⟩
    rw [hPQ, mem_bot, inv_mul_eq_one] at h'
    exact h'
  have hcardP : ∀ K : Subgroup H, P ⊓ K ≤ X →
      Nat.card (((P ⊓ K).subgroupOf X).map π) = Nat.card (P ⊓ K : Subgroup H) := by
    intro K hle
    have hmemP : ∀ a : (P ⊓ K).subgroupOf X, (a : X) ∈ P.subgroupOf X := fun a =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp a.2)).1
    have hinj : Function.Injective (π.comp ((P ⊓ K).subgroupOf X).subtype) := fun a b hab =>
      Subtype.ext (hπinj _ (hmemP a) _ (hmemP b) hab)
    have h1 : ((P ⊓ K).subgroupOf X).map π =
        (π.comp ((P ⊓ K).subgroupOf X).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hc₁ : Nat.card (((P ⊓ K₁).subgroupOf X).map π) = p :=
    (hcardP K₁ (inf_le_left.trans hPX)).trans hP₁
  have hc₂ : Nat.card (((P ⊓ K₂).subgroupOf X).map π) = p :=
    (hcardP K₂ (inf_le_left.trans hPX)).trans hP₂
  have hne : ((P ⊓ K₁).subgroupOf X).map π ≠ ((P ⊓ K₂).subgroupOf X).map π := by
    intro h
    have hle : P ⊓ K₁ ≤ P ⊓ K₂ := by
      intro x hx
      have hxX : x ∈ X := hPX hx.1
      have hm : π ⟨x, hxX⟩ ∈ ((P ⊓ K₂).subgroupOf X).map π := h ▸ ⟨⟨x, hxX⟩, hx, rfl⟩
      obtain ⟨b, hb, hbx⟩ := hm
      have hbP : b ∈ P.subgroupOf X :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).1
      have heq := hπinj b hbP ⟨x, hxX⟩ (Subgroup.mem_subgroupOf.mpr hx.1) hbx
      have hb' : ((b : X) : H) ∈ P ⊓ K₂ := Subgroup.mem_subgroupOf.mp hb
      rw [heq] at hb'
      exact hb'
    have hbot : P ⊓ K₁ = ⊥ := by rw [← hPinf, inf_eq_left.mpr hle]
    have h1 : Nat.card (P ⊓ K₁ : Subgroup H) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hP₁] at h1
    exact hp.one_lt.ne' h1
  have himage : ∀ K : Subgroup H, X ≤ normalizer (K : Set H) →
      Nat.card (P ⊓ K : Subgroup H) = p →
      (K.subgroupOf X).map π = ((P ⊓ K).subgroupOf X).map π := by
    intro K hXK hPK
    have hXXK : X ≤ normalizer ((X ⊓ K : Subgroup H) : Set H) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨X.mul_mem (X.mul_mem hg h1) (X.inv_mem hg),
          (mem_normalizer_iff.mp (hXK hg) h).mp h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, (mem_normalizer_iff.mp (hXK hg) h).mpr h2⟩
        have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [e]
        exact X.mul_mem (X.mul_mem (X.inv_mem hg) h1) hg
    have hSyl := hP.inf_of_le_normalizer inf_le_left hXXK
    rw [← inf_assoc, inf_eq_left.mpr hPX] at hSyl
    have hv : (Nat.card (X ⊓ K : Subgroup H)).factorization p = 1 := by
      have h := hSyl.card_eq
      rw [hPK] at h
      exact (Nat.pow_right_injective hp.two_le
        (show p ^ 1 = p ^ _ from by rw [pow_one]; exact h)).symm
    let f : K.subgroupOf X →* X ⧸ Q := π.comp (K.subgroupOf X).subtype
    have hfrange : f.range = (K.subgroupOf X).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerr : IsPGroup r f.ker := by
      let ψ : f.ker →* Q :=
        { toFun := fun k => ⟨((k : K.subgroupOf X) : X), (QuotientGroup.eq_one_iff _).mp k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact hQr.of_injective ψ fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun w : Q => (w : X)) hab))
    have hrangep : IsPGroup p f.range := hXQp.to_subgroup _
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hrangep
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hkerr
    have hdom : Nat.card (K.subgroupOf X) = r ^ b * p ^ a := by
      rw [← hb, ← ha, ← Subgroup.index_ker, Subgroup.card_mul_index]
    have hdom' : Nat.card (K.subgroupOf X) = Nat.card (X ⊓ K : Subgroup H) := by
      have e : K.subgroupOf X = (X ⊓ K).subgroupOf X := by
        ext x
        simp only [mem_subgroupOf, mem_inf, x.2, true_and]
      rw [e]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have ha1 : a = 1 := by
      rw [← hv, ← hdom', hdom, factorization_pow_mul_pow hp hr hrp]
    have hcardM : Nat.card ((K.subgroupOf X).map π) = p := by
      rw [← hfrange, ha, ha1, pow_one]
    have hle : ((P ⊓ K).subgroupOf X).map π ≤ (K.subgroupOf X).map π :=
      map_mono fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    have hcardPK : Nat.card (((P ⊓ K).subgroupOf X).map π) = p :=
      (hcardP K (inf_le_left.trans hPX)).trans hPK
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardM, hcardPK])).symm
  have hi₁ := himage K₁ hXK₁ hP₁
  have hi₂ := himage K₂ hXK₂ hP₂
  have hRaction : ∀ R : Subgroup H, R ≤ Y → (R.subgroupOf Y).Normal → IsPGroup r R →
      ∀ x ∈ R, ∀ g ∈ X, g⁻¹ * (x * g * x⁻¹) ∈ inSubgroup (pCore r) X := by
    intro R hRY hRn hRr x hx g hg
    set W := R.subgroupOf X with hW
    have hWn : W.Normal := by
      refine ⟨fun w hw k => ?_⟩
      rw [mem_subgroupOf] at hw ⊢
      exact hRn.conj_mem ⟨w, hRY hw⟩ hw ⟨k, hXY k.2⟩
    have hWr : IsPGroup r W := by
      let ψ : W →* R :=
        { toFun := fun w => ⟨((w : X) : H), w.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact hRr.of_injective ψ fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun w : R => (w : H)) hab))
    have hWQ : W ≤ Q := le_sSup ⟨hWn, hWr⟩
    have hmemX : g⁻¹ * (x * g * x⁻¹) ∈ X := mul_mem (inv_mem hg) (hXnorm x (hRY hx) g hg)
    have hmemR : g⁻¹ * (x * g * x⁻¹) ∈ R := by
      have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ R := hRn.conj_mem ⟨x, hRY hx⟩ hx ⟨g⁻¹, hXY (inv_mem hg)⟩
      rw [inv_inv] at h1
      have e : g⁻¹ * (x * g * x⁻¹) = (g⁻¹ * x * g) * x⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem hx)
    exact ⟨⟨_, hmemX⟩, hWQ hmemR, rfl⟩
  have hRnorm : ∀ R : Subgroup H, R ≤ Y → (R.subgroupOf Y).Normal → IsPGroup r R →
      R ≤ normalizer (K₁ : Set H) ⊓ normalizer (K₂ : Set H) := by
    intro R hRY hRn hRr x hx
    have hact := hRaction R hRY hRn hRr
    have hxY : x ∈ Y := hRY hx
    have hmove : ∀ K K' : Subgroup H, conjugate K x = K' →
        (K.subgroupOf X).map π ≤ (K'.subgroupOf X).map π := by
      rintro K K' hKK' _ ⟨g, hg, rfl⟩
      have hgK : (g : H) ∈ K := Subgroup.mem_subgroupOf.mp hg
      have hcX : x⁻¹ * (g : H) * x ∈ X := by
        have h1 := hXnorm x⁻¹ (inv_mem hxY) g g.2
        rwa [inv_inv] at h1
      have hcK : x⁻¹ * (g : H) * x ∈ K' := by
        rw [← hKK']
        exact ⟨g, hgK, by simp⟩
      refine ⟨⟨_, hcX⟩, hcK, ?_⟩
      apply QuotientGroup.eq.mpr
      rw [hmemQ]
      have h1 := hact x⁻¹ (inv_mem hx) g g.2
      rw [inv_inv] at h1
      have e : (((⟨_, hcX⟩ : X)⁻¹ * g : X) : H) = ((g : H)⁻¹ * (x⁻¹ * g * x))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact inv_mem h1
    have hset := hperm x hxY
    have h1 : conjugate K₁ x = K₁ ∨ conjugate K₁ x = K₂ := by
      have h : conjugate K₁ x ∈ ({K₁, K₂} : Set (Subgroup H)) := hset ▸ Set.mem_insert _ _
      simpa using h
    have h2 : conjugate K₂ x = K₁ ∨ conjugate K₂ x = K₂ := by
      have h : conjugate K₂ x ∈ ({K₁, K₂} : Set (Subgroup H)) :=
        hset ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
      simpa using h
    have hcM₁ : Nat.card ((K₁.subgroupOf X).map π) = p := by rw [hi₁]; exact hc₁
    have hcM₂ : Nat.card ((K₂.subgroupOf X).map π) = p := by rw [hi₂]; exact hc₂
    have hx₁ : conjugate K₁ x = K₁ := by
      rcases h1 with h | h
      · exact h
      · exfalso
        apply hne
        rw [← hi₁, ← hi₂]
        exact Subgroup.eq_of_le_of_card_ge (hmove K₁ K₂ h) (by rw [hcM₁, hcM₂])
    have hx₂ : conjugate K₂ x = K₂ := by
      rcases h2 with h | h
      · exfalso
        apply hne
        rw [← hi₁, ← hi₂]
        exact (Subgroup.eq_of_le_of_card_ge (hmove K₂ K₁ h) (by rw [hcM₁, hcM₂])).symm
      · exact h
    exact ⟨mem_normalizer_iff_conjugate_eq.mpr hx₁, mem_normalizer_iff_conjugate_eq.mpr hx₂⟩
  have hOY : inSubgroup (pCore r) Y ≤ normalizer (K₁ : Set H) ⊓ normalizer (K₂ : Set H) := by
    have hle : inSubgroup (pCore r) Y ≤ Y := map_subtype_le _
    have hsub : (inSubgroup (pCore r) Y).subgroupOf Y = pCore r Y :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    refine hRnorm _ hle ?_ (pCore_isPGroup.map Y.subtype)
    rw [hsub]
    exact pCore_normal
  exact ⟨fun R hRY hRn hRr => ⟨hRnorm R hRY hRn hRr, hRaction R hRY hRn hRr⟩, hOY, hi₁, hi₂,
    hc₁, hc₂, hne⟩

end CFSG.Quasithin.SteinbergCD
