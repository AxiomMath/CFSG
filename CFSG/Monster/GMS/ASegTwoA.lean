module

public import CFSG.Monster.GMS.ASegDefs
public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.S341

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def BabyTwoAAutInner : Prop :=
  ∀ r : B, BabyInv 0 r → ∀ D : Subgroup B, D ≤ Subgroup.centralizer ({r} : Set B) →
    2 * Nat.card D = Nat.card (Subgroup.centralizer ({r} : Set B)) → r ∈ D →
      ⁅D, D⁆ = D ∧
        ∀ θ : D ≃* D, (∀ d : D, (d : B) = r → θ d = d) →
          ∃ g ∈ Subgroup.centralizer ({r} : Set B), ∀ d : D, (θ d : B) = g * d * g⁻¹

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem inv_mul_mul_eq_of_commute {x u₁ u₂ w : G} (h₁ : x * u₁ = u₁ * x) (h₂ : x * u₂ = u₂ * x) :
    (u₁ * u₂)⁻¹ * (x * u₁ * w) = (u₁⁻¹ * (x * u₁)) * (u₂⁻¹ * w) :=
  calc (u₁ * u₂)⁻¹ * (x * u₁ * w) = u₂⁻¹ * u₁⁻¹ * (x * u₁) * w := by group
    _ = u₂⁻¹ * u₁⁻¹ * (u₁ * x) * w := by rw [h₁]
    _ = u₂⁻¹ * (x * u₂) * u₂⁻¹ * w := by group
    _ = u₂⁻¹ * (u₂ * x) * u₂⁻¹ * w := by rw [h₂]
    _ = u₁⁻¹ * (u₁ * x) * (u₂⁻¹ * w) := by group
    _ = u₁⁻¹ * (x * u₁) * (u₂⁻¹ * w) := by rw [h₁]

theorem centInvAutInnerTwoA_of_baby
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hB : BabyTwoAAutInner) : CentInvAutInnerTwoA a := by
  classical
  intro x t hx ht
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG hx).exists_cover
  obtain ⟨htC, ht0⟩ := (mem_twoANbr_iff I.sls I.tableV I.leech I.tableIII hG hx hφ).mp ht
  set K : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {t} with hK
  intro ψ hψx hψt
  have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := inf_le_left
  set r : B := coverMap φ t with hr
  let f : K →* B := φ.comp (Subgroup.inclusion hKx)
  have hf : ∀ k : K, f k = coverMap φ (k : G) := fun k => (coverMap_apply (hKx k.2)).symm
  have hxt : x ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
  have hxK : x ∈ K := ⟨mem_centralizer_self x, hxt⟩
  have htK : t ∈ K := ⟨htC, mem_centralizer_self t⟩
  have hker : ∀ k : K, f k = 1 ↔ (k : G) = 1 ∨ (k : G) = x := fun k => by
    rw [hf]
    exact hφ.coverMap_eq_one_iff (hKx k.2)
  set D : Subgroup B := f.range with hD
  have hDle : D ≤ Subgroup.centralizer ({r} : Set B) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hf, hr]
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp k.2.2
    rw [← coverMap_mul (hKx k.2) htC, ← coverMap_mul htC (hKx k.2), hkt]
  have hrD : r ∈ D := ⟨⟨t, htK⟩, (hf _).trans rfl⟩
  have hcardK : Nat.card K = 2 * Nat.card D := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (K ⧸ f.ker) = Nat.card D :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = 2 := by
      have hx2 : orderOf (⟨x, hxK⟩ : K) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hφ.orderOf_eq
      have hS : f.ker = Subgroup.zpowers (⟨x, hxK⟩ : K) := by
        ext k
        rw [MonoidHom.mem_ker, hker, mem_zpowers_iff_of_orderOf_eq_two hx2]
        constructor
        · rintro (h | h)
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · rintro (h | h)
          · exact Or.inl (congrArg Subtype.val h)
          · exact Or.inr (congrArg Subtype.val h)
      rw [hS, Nat.card_zpowers, hx2]
    rw [h1, h2, h3, mul_comm]
  have hcardC : 2 * Nat.card D = Nat.card (Subgroup.centralizer ({r} : Set B)) := by
    rw [← hcardK, ht0.2, card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hx ht]
    rfl
  obtain ⟨hperf, hinner⟩ := hB r ht0 D hDle hcardC hrD
  let fD : K →* D := f.rangeRestrict
  have hfD : Function.Surjective fD := f.rangeRestrict_surjective
  have hfDv : ∀ k : K, ((fD k : D) : B) = f k := fun _ => rfl
  let gD : K →* D := fD.comp ψ.toMonoidHom
  have hψxK : ψ ⟨x, hxK⟩ = ⟨x, hxK⟩ := hψx _ rfl
  have hle : fD.ker ≤ gD.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hk' : f k = 1 := by
      rw [← hfDv, hk]
      rfl
    rcases (hker k).mp hk' with h | h
    · rw [show k = 1 from Subtype.ext h, map_one]
    · rw [show k = ⟨x, hxK⟩ from Subtype.ext h]
      show fD (ψ ⟨x, hxK⟩) = 1
      rw [hψxK, show (⟨x, hxK⟩ : K) = k from (Subtype.ext h).symm]
      exact hk
  let θ₀ : D →* D := (MonoidHom.liftOfSurjective fD hfD) ⟨gD, hle⟩
  have hθ₀ : ∀ k : K, θ₀ (fD k) = fD (ψ k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hθinj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨k, rfl⟩ := hfD d
    rw [hθ₀] at hd
    have hk' : f (ψ k) = 1 := by
      rw [← hfDv, hd]
      rfl
    rcases (hker (ψ k)).mp hk' with h | h
    · have : ψ k = 1 := Subtype.ext h
      rw [ψ.map_eq_one_iff] at this
      rw [this, map_one]
    · have : ψ k = ψ ⟨x, hxK⟩ := by rw [hψxK]; exact Subtype.ext h
      rw [ψ.injective this]
      apply Subtype.ext
      rw [hfDv]
      exact (hker _).mpr (Or.inr rfl)
  have : Finite D := Finite.of_injective (fun d : D => (d : B)) Subtype.val_injective
  let θ : D ≃* D := MulEquiv.ofBijective θ₀ ⟨hθinj, Finite.surjective_of_injective hθinj⟩
  have hθ : ∀ k : K, θ (fD k) = fD (ψ k) := hθ₀
  have hθr : ∀ d : D, (d : B) = r → θ d = d := by
    intro d hd
    have hdt : d = fD ⟨t, htK⟩ :=
      Subtype.ext (hd.trans ((hf ⟨t, htK⟩).symm.trans (hfDv _).symm))
    rw [hdt, hθ, hψt ⟨t, htK⟩ rfl]
  obtain ⟨gb, -, hgb⟩ := hinner θ hθr
  obtain ⟨g, hgC, hgφ⟩ := hφ.exists_coverMap_eq gb
  have hconjK : ∀ k : K, g * (k : G) * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := fun k =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC (hKx k.2)) (Subgroup.inv_mem _ hgC)
  have hcase : ∀ k : K, (ψ k : G) = g * k * g⁻¹ ∨ (ψ k : G) = x * (g * k * g⁻¹) := by
    intro k
    have h1 : coverMap φ (g * (k : G) * g⁻¹) = coverMap φ (ψ k : G) := by
      rw [coverMap_conj hgC (hKx k.2), hgφ, ← hf, ← hf, ← hfDv, ← hfDv, ← hθ, hgb]
    exact (hφ.coverMap_eq_iff (hconjK k) (hKx (ψ k).2)).mp h1
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_two hφ.orderOf_eq
  have hxcomm : ∀ k : K, x * (g * k * g⁻¹) = (g * k * g⁻¹) * x := fun k =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hconjK k)).symm
  have hval : ∀ k : K, (g * (k : G) * g⁻¹)⁻¹ * ψ k ∈ Subgroup.zpowers x := by
    intro k
    rw [mem_zpowers_iff_of_orderOf_eq_two hφ.orderOf_eq]
    rcases hcase k with h | h
    · left
      rw [h, inv_mul_cancel]
    · right
      rw [h, hxcomm k]
      group
  let χ : K →* Subgroup.zpowers x :=
    { toFun := fun k => ⟨(g * (k : G) * g⁻¹)⁻¹ * ψ k, hval k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro k₁ k₂
        apply Subtype.ext
        show (g * ((k₁ : G) * k₂) * g⁻¹)⁻¹ * (ψ (k₁ * k₂) : G) =
          ((g * (k₁ : G) * g⁻¹)⁻¹ * ψ k₁) * ((g * (k₂ : G) * g⁻¹)⁻¹ * ψ k₂)
        rw [map_mul, Subgroup.coe_mul,
          show g * ((k₁ : G) * k₂) * g⁻¹ = (g * k₁ * g⁻¹) * (g * k₂ * g⁻¹) by group]
        rcases hcase k₁ with h₁ | h₁
        · rw [h₁]
          group
        · rw [h₁]
          exact inv_mul_mul_eq_of_commute (hxcomm k₁) (hxcomm k₂) }
  have hχ : ∀ k : K, ((χ k : Subgroup.zpowers x) : G) = (g * (k : G) * g⁻¹)⁻¹ * ψ k :=
    fun _ => rfl
  have hcomm : commutator K ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have hχx : χ ⟨x, hxK⟩ = 1 := by
    apply Subtype.ext
    rw [hχ, hψxK]
    show (g * x * g⁻¹)⁻¹ * x = 1
    have hgx : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hgC]
      group
    rw [hgx, inv_mul_cancel]
  have hall : ∀ k : K, χ k = 1 := by
    intro k
    have hkD : f k ∈ (commutator K).map f := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, ← hD, hperf]
      exact ⟨k, rfl⟩
    obtain ⟨k', hk'c, hk'f⟩ := hkD
    have hq : f (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, hk'f, inv_mul_cancel]
    have hk'1 : χ k' = 1 := hcomm hk'c
    have hkk : k = k' * (k'⁻¹ * k) := by group
    rw [hkk, map_mul, hk'1, one_mul]
    rcases (hker _).mp hq with h | h
    · rw [show k'⁻¹ * k = 1 from Subtype.ext h, map_one]
    · rw [show k'⁻¹ * k = ⟨x, hxK⟩ from Subtype.ext h, hχx]
  have hψg : ∀ k : K, (ψ k : G) = g * k * g⁻¹ := by
    intro k
    have h := congrArg Subtype.val (hall k)
    rw [hχ] at h
    exact (inv_mul_eq_one.mp h).symm
  have hgt : g ∈ Subgroup.centralizer ({t} : Set G) := by
    have h := hψg ⟨t, htK⟩
    rw [hψt ⟨t, htK⟩ rfl] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [← h]
  exact ⟨g, ⟨hgC, hgt⟩, hψg⟩

end CFSG.Monster.GMS
