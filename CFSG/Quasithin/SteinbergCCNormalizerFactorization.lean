module

public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.SteinbergCCPerfectCentralization
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement Pointwise

variable {H : Type*} [Group H]

theorem coe_sup_inf_normalizer_eq_mul {X R C : Subgroup H} [X.Normal] (hCR : C ≤ R)
    [(C.subgroupOf R).Characteristic] :
    (((X ⊔ R) ⊓ normalizer (C : Set H) : Subgroup H) : Set H) =
      ((X ⊓ normalizer (C : Set H) : Subgroup H) : Set H) * R := by
  have hRC : R ≤ normalizer (C : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hCR).mp inferInstance
  ext n
  constructor
  · intro hn
    have hn1 : n ∈ (↑(X ⊔ R) : Set H) := (mem_inf.mp hn).1
    rw [normal_mul] at hn1
    obtain ⟨x, hx, r, hr, hxr⟩ := hn1
    have hxr : x * r = n := hxr
    refine ⟨x, mem_inf.mpr ⟨hx, ?_⟩, r, hr, hxr⟩
    have h1 := mul_mem (mem_inf.mp hn).2 (inv_mem (hRC hr))
    rwa [← hxr, mul_inv_cancel_right] at h1
  · rintro ⟨d, hd, r, hr, hdr⟩
    have hdr : d * r = n := hdr
    rw [← hdr]
    exact mem_inf.mpr ⟨mul_mem_sup (mem_inf.mp hd).1 hr,
      mul_mem (mem_inf.mp hd).2 (hRC hr)⟩

theorem le_normalizer_of_characteristic {R C Y : Subgroup H} (hCR : C ≤ R)
    [hC : (C.subgroupOf R).Characteristic] (hYR : Y ≤ normalizer (R : Set H)) :
    Y ≤ normalizer (C : Set H) := by
  refine le_normalizer_of_conj_mem fun y hy c hc => ?_
  have h1 := characteristic_iff_map_eq.mp hC (R.normalizerMonoidHom ⟨y, hYR hy⟩)
  have h2 : R.normalizerMonoidHom ⟨y, hYR hy⟩ ⟨c, hCR hc⟩ ∈ C.subgroupOf R := by
    rw [← h1]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr hc)
  exact mem_subgroupOf.mp h2

variable [Finite H]

theorem eq_of_not_le_frattini_preimage (X : Subgroup H) [X.Normal] (Y : Subgroup H)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y ∈ Y, ∀ u ∈ U, frattiniQuotConj X y u ∈ U) → U = ⊥ ∨ U = ⊤)
    {D : Subgroup H} (hQD : (CFSG.pCore 2 X).map X.subtype ≤ D) (hDX : D ≤ X)
    (hYD : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (hD : ¬ D ≤ (((frattini (X ⧸ CFSG.pCore 2 X)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X))).map X.subtype)) : D = X := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 X)
  let σ := QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))
  let U := ((D.subgroupOf X).map π).map σ
  have hUY : ∀ y ∈ Y, ∀ u ∈ U, frattiniQuotConj X y u ∈ U := by
    rintro y hy _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨π (MulAut.conjNormal y z), ⟨MulAut.conjNormal y z, ?_, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact hYD y hy _ (mem_subgroupOf.mp hz)
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hD
    intro d hd
    refine ⟨⟨d, hDX hd⟩, ?_, rfl⟩
    have h1 : σ (π ⟨d, hDX hd⟩) ∈ U := ⟨_, ⟨_, mem_subgroupOf.mpr hd, rfl⟩, rfl⟩
    rw [hbot, mem_bot] at h1
    rw [SetLike.mem_coe, mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hsup : (D.subgroupOf X).map π ⊔ frattini (X ⧸ CFSG.pCore 2 X) = ⊤ := by
    have h := congrArg (Subgroup.comap σ) ((hirr U hUY).resolve_left hUne)
    rwa [comap_map_eq, comap_top, QuotientGroup.ker_mk'] at h
  have hπD : (D.subgroupOf X).map π = ⊤ := frattini_nongenerating hsup
  refine le_antisymm hDX fun x hx => ?_
  have h1 : π ⟨x, hx⟩ ∈ (D.subgroupOf X).map π := hπD ▸ mem_top _
  obtain ⟨d, hd, hdx⟩ := h1
  have hk : d⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 X := QuotientGroup.eq.mp hdx
  have hkD : ((d⁻¹ * ⟨x, hx⟩ : X) : H) ∈ D := hQD ⟨_, hk, rfl⟩
  have e : x = (d : H) * ((d⁻¹ * ⟨x, hx⟩ : X) : H) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact mul_mem (mem_subgroupOf.mp hd) hkD

theorem characteristic_normalizer_factorization_captures_original_prime_witness_in_perfect_residual
    {X L : Subgroup H} [X.Normal] (hXL : X ≤ L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hP : IsPGroup q (X ⧸ CFSG.pCore 2 X)) (hW : frattini (X ⧸ CFSG.pCore 2 X) ≠ ⊤)
    {R : Subgroup H} (hR : IsPGroup 2 R) (hQR : (CFSG.pCore 2 X).map X.subtype ≤ R)
    {Y : Subgroup H} (hYL : Y ≤ L) (hY : Group.IsPerfect Y) (hYR : Y ≤ normalizer (R : Set H))
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y ∈ Y, ∀ u ∈ U, frattiniQuotConj X y u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ y ∈ Y, ∃ w, frattiniQuotConj X y w ≠ w)
    {C₁ C₂ : Subgroup H} (hC₁R : C₁ ≤ R) (hC₂R : C₂ ≤ R)
    (hC₁ : (C₁.subgroupOf R).Characteristic) (hC₂ : (C₂.subgroupOf R).Characteristic)
    (hfact : ((X ⊔ R : Subgroup H) : Set H) =
      (((X ⊔ R) ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) *
        (((X ⊔ R) ⊓ normalizer (C₂ : Set H) : Subgroup H) : Set H)) :
    X ⊓ R = (CFSG.pCore 2 X).map X.subtype ∧
      (((X ⊔ R) ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) =
        ((X ⊓ normalizer (C₁ : Set H) : Subgroup H) : Set H) * R ∧
      (((X ⊔ R) ⊓ normalizer (C₂ : Set H) : Subgroup H) : Set H) =
        ((X ⊓ normalizer (C₂ : Set H) : Subgroup H) : Set H) * R ∧
      ⁅X, Y⁆ = X ∧
      ∃ C : Subgroup H, (C = C₁ ∨ C = C₂) ∧ X ≤ L ⊓ normalizer (C : Set H) ∧
        X ≤ (CFSG.perfectResidual (L ⊓ normalizer (C : Set H) : Subgroup H)).map
          (L ⊓ normalizer (C : Set H)).subtype ∧ (C₁ ≠ ⊥ → C₂ ≠ ⊥ → C ≠ ⊥) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set Q := (CFSG.pCore 2 X).map X.subtype with hQdef
  have hQX : Q ≤ X := map_subtype_le _
  have hXR : X ⊓ R = Q := by
    refine le_antisymm (fun z hz => ?_) (le_inf hQX hQR)
    obtain ⟨hzX, hzR⟩ := mem_inf.mp hz
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨z, hzR⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP)
      (QuotientGroup.mk' (CFSG.pCore 2 X) ⟨z, hzX⟩)
    have hdvd : q ^ j ∣ 2 ^ k := by
      rw [← hj, ← hk, Subgroup.orderOf_mk, ← Subgroup.orderOf_mk z hzX]
      exact orderOf_map_dvd _ _
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hj
      exact ⟨⟨z, hzX⟩, hj, rfl⟩
    · exfalso
      have h1 : q ∣ 2 := hq.dvd_of_dvd_pow ((dvd_pow_self q j.succ_ne_zero).trans hdvd)
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)
  have hN₁ := coe_sup_inf_normalizer_eq_mul (X := X) hC₁R
  have hN₂ := coe_sup_inf_normalizer_eq_mul (X := X) hC₂R
  have hXY : ⁅X, Y⁆ = X := commutator_eq_of_irreducible_frattini X Y hX2 hirr hnt
  set K := ((frattini (X ⧸ CFSG.pCore 2 X)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 X))).map X.subtype with hKdef
  have hKX : K ≤ X := map_subtype_le _
  have hQK : Q ≤ K := map_mono fun x hx => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hKn : ∀ h : H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    rintro h _ ⟨k, hk, rfl⟩
    refine ⟨MulAut.conjNormal h k, ?_, MulAut.conjNormal_apply h k⟩
    rw [SetLike.mem_coe, mem_comap] at hk ⊢
    have h1 := characteristic_iff_map_eq.mp
      (inferInstance : (frattini (X ⧸ CFSG.pCore 2 X)).Characteristic) (coreQuotConj X h)
    rw [← h1]
    exact mem_map_of_mem (coreQuotConj X h).toMonoidHom hk
  have hsome : ¬ X ⊓ normalizer (C₁ : Set H) ≤ K ∨ ¬ X ⊓ normalizer (C₂ : Set H) ≤ K := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨h₁, h₂⟩ := hcon
    apply hW
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) v
    have hx : (x : H) ∈ ((X ⊔ R : Subgroup H) : Set H) := mem_sup_left x.2
    rw [hfact, hN₁, hN₂] at hx
    obtain ⟨_, ⟨d₁, hd₁, r₁, hr₁, rfl⟩, _, ⟨d₂, hd₂, r₂, hr₂, rfl⟩, hx⟩ := hx
    have hx : d₁ * r₁ * (d₂ * r₂) = (x : H) := hx
    have hk : d₁ * (r₁ * d₂ * r₁⁻¹) ∈ K := mul_mem (h₁ hd₁) (hKn r₁ d₂ (h₂ hd₂))
    have hr : (d₁ * (r₁ * d₂ * r₁⁻¹))⁻¹ * (x : H) ∈ X ⊓ R := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hKX hk)) x.2, ?_⟩
      rw [← hx, show (d₁ * (r₁ * d₂ * r₁⁻¹))⁻¹ * (d₁ * r₁ * (d₂ * r₂)) = r₁ * r₂ by group]
      exact mul_mem hr₁ hr₂
    rw [hXR] at hr
    have hxK : (x : H) ∈ K := by
      have e : (x : H) = d₁ * (r₁ * d₂ * r₁⁻¹) * ((d₁ * (r₁ * d₂ * r₁⁻¹))⁻¹ * x) := by group
      rw [e]
      exact mul_mem hk (hQK hr)
    obtain ⟨x', hx', hxx'⟩ := hxK
    rw [Subtype.ext hxx'] at hx'
    exact hx'
  have hfinish : ∀ C : Subgroup H, C ≤ R → (C.subgroupOf R).Characteristic →
      ¬ X ⊓ normalizer (C : Set H) ≤ K →
      X ≤ L ⊓ normalizer (C : Set H) ∧
        X ≤ (CFSG.perfectResidual (L ⊓ normalizer (C : Set H) : Subgroup H)).map
          (L ⊓ normalizer (C : Set H)).subtype := by
    intro C hCR hC hnot
    have hRC : R ≤ normalizer (C : Set H) :=
      (normal_subgroupOf_iff_le_normalizer hCR).mp inferInstance
    have hYC : Y ≤ normalizer (C : Set H) := le_normalizer_of_characteristic hCR hYR
    have hD : X ⊓ normalizer (C : Set H) = X := by
      refine eq_of_not_le_frattini_preimage X Y hirr (le_inf hQX (hQR.trans hRC)) inf_le_left
        (fun y hy d hd => mem_inf.mpr ⟨(inferInstance : X.Normal).conj_mem d (mem_inf.mp hd).1 y,
          mul_mem (mul_mem (hYC hy) (mem_inf.mp hd).2) (inv_mem (hYC hy))⟩) hnot
    have hXC : X ≤ normalizer (C : Set H) := by
      rw [← hD]
      exact inf_le_right
    refine ⟨le_inf hXL hXC, ?_⟩
    set A := L ⊓ normalizer (C : Set H) with hA
    obtain ⟨-, -, h3⟩ := CFSG.perfect_residual_transport (MonoidHom.id A)
    obtain ⟨-, hchar, -⟩ := CFSG.perfect_residual_characterization (G := A)
    have hYA : Y ≤ A := le_inf hYL hYC
    have hYperf : Group.IsPerfect (Y.subgroupOf A) := by
      rw [isPerfect_iff]
      apply map_injective (subtype_injective A)
      rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hYA, isPerfect_iff.mp hY]
    have hYD := h3 _ hYperf
    have hYD' : Y ≤ (CFSG.perfectResidual A).map A.subtype := fun y hy =>
      ⟨⟨y, hYA hy⟩, hYD (mem_subgroupOf.mpr hy), rfl⟩
    have hXA : X ≤ A := le_inf hXL hXC
    rw [← hXY, commutator_le]
    intro x hx y hy
    obtain ⟨a, ha, hay⟩ := hYD' hy
    have h1 := characteristic_iff_map_eq.mp hchar (MulAut.conj (⟨x, hXA hx⟩ : A))
    have h2 : (MulAut.conj (⟨x, hXA hx⟩ : A)) a ∈ CFSG.perfectResidual A := by
      rw [← h1]
      exact mem_map_of_mem _ ha
    rw [commutatorElement_def]
    refine mul_mem ⟨_, h2, ?_⟩ (inv_mem (hYD' hy))
    rw [← hay]
    rfl
  rcases hsome with h | h
  · obtain ⟨h1, h2⟩ := hfinish C₁ hC₁R hC₁ h
    exact ⟨hXR, hN₁, hN₂, hXY, C₁, Or.inl rfl, h1, h2, fun h₁ _ => h₁⟩
  · obtain ⟨h1, h2⟩ := hfinish C₂ hC₂R hC₂ h
    exact ⟨hXR, hN₁, hN₂, hXY, C₂, Or.inr rfl, h1, h2, fun _ h₂ => h₂⟩

end CFSG.Quasithin.SteinbergCC
