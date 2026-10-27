module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Open

section Lift

variable {U P : Type} [Group U] [Group P] [Finite U]

theorem exists_two_subgroup_lift (π : U →* P) (hπ : Function.Surjective π) (Z : Subgroup U)
    (hZk : π.ker = Z) (hZc : Z ≤ Subgroup.center U) (S : Subgroup P) (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (A : Subgroup U)
    (hA : ∀ a ∈ A, ∀ s ∈ S, π a * s * (π a)⁻¹ ∈ S) :
    ∃ T : Subgroup U, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Finite.of_surjective π hπ
  set H : Subgroup U := S.comap π with hH
  let f : ↥H →* ↥S := (π.comp H.subtype).codRestrict S (fun x => x.2)
  have hfker : f.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have hx1 : π (x : U) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxZ : (x : U) ∈ Z := by rw [← hZk]; exact hx1
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp (hZc hxZ) (g : U)
    exact Subtype.ext this
  have : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hnil : Group.IsNilpotent ↥H := Subgroup.isNilpotent_of_ker_le_center f hfker
  have h2S : 2 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hS (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hfsurj : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := hπ s
    exact ⟨⟨u, by simpa [hH, Subgroup.mem_comap, hu] using hs⟩, Subtype.ext hu⟩
  have h2H : 2 ∣ Nat.card H := h2S.trans (Subgroup.card_dvd_of_surjective hfsurj)
  obtain ⟨T₂⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  have hT₂ne : (T₂ : Subgroup ↥H) ≠ ⊥ := by
    intro hbot
    have h1 := Sylow.card_eq_multiplicity T₂
    rw [hbot, Subgroup.card_bot] at h1
    have h2 : 0 < (Nat.card ↥H).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2H
    have h3 : 2 ^ 1 ≤ 2 ^ (Nat.card ↥H).factorization 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hT₂n : (T₂ : Subgroup ↥H).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := ↥H)).out 1 4 rfl rfl).mp hnil 2 ⟨Nat.prime_two⟩ T₂
  have hle : (T₂ : Subgroup ↥H) ≤ pCore 2 ↥H := le_pCore 2 hT₂n T₂.isPGroup'
  have hKne : pCore 2 ↥H ≠ ⊥ := fun h => hT₂ne (le_bot_iff.mp (h ▸ hle))
  have hchar : (pCore 2 ↥H).Characteristic := pCore_characteristic 2
  refine ⟨(pCore 2 ↥H).map H.subtype, ?_, (pCore_isPGroup 2).map H.subtype, ?_⟩
  · intro hbot
    exact hKne ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hbot)
  · intro a ha t ht
    have hnorm : a ∈ Subgroup.normalizer (H : Set U) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 := hA a ha (π x) hx
        simpa [hH, Subgroup.mem_comap] using h1
      · intro hx
        have h1 := hA a⁻¹ (A.inv_mem ha) (π (a * x * a⁻¹))
          (by simpa [hH, Subgroup.mem_comap] using hx)
        have h2 : π a⁻¹ * π (a * x * a⁻¹) * (π a⁻¹)⁻¹ = π x := by
          simp only [map_mul, map_inv]
          group
        rw [h2] at h1
        simpa [hH, Subgroup.mem_comap] using h1
    have := normalizer_le_normalizer_map_of_characteristic (G := U) (H := H) (pCore 2 ↥H) hnorm
    exact (Subgroup.mem_normalizer_iff.mp this t).mp ht

end Lift

section Fixed

open Matrix

variable {K : Type} [Field K] {n : ℕ}

@[expose] def fixedSpace (T : Subgroup (GL (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ t ∈ T, (t : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := fun {a b} ha hb t ht => by rw [Matrix.mulVec_add, ha t ht, hb t ht]
  zero_mem' := fun t _ => by rw [Matrix.mulVec_zero]
  smul_mem' := fun c v hv t ht => by rw [Matrix.mulVec_smul, hv t ht]

theorem fixedSpace_invariant {T : Subgroup (GL (Fin n) K)} {a : GL (Fin n) K}
    (ha : ∀ t ∈ T, a⁻¹ * t * a ∈ T) {v : Fin n → K} (hv : v ∈ fixedSpace T) :
    (a : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ fixedSpace T := by
  intro t ht
  have h1 : a * (a⁻¹ * t * a) = t * a := by group
  have h2 : (t : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ * t * a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_mul, ← Units.val_mul, h1]
  rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, hv _ (ha t ht)]

theorem fixedSpace_ne_top {T : Subgroup (GL (Fin n) K)} (hT : T ≠ ⊥) : fixedSpace T ≠ ⊤ := by
  intro htop
  apply hT
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ fixedSpace T := htop ▸ Submodule.mem_top
  simp only [Matrix.toLin'_apply, Units.val_one, Matrix.one_mulVec]
  exact hv t ht

theorem fixedSpace_ne_bot [Finite K] (hK2 : 2 ∣ Nat.card K) (hn : 1 ≤ n)
    {T : Subgroup (GL (Fin n) K)} (hT : IsPGroup 2 T) : fixedSpace T ≠ ⊥ := by
  classical
  intro hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T (Fin n → K) :=
    { smul := fun t v => ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
      one_smul := fun v => by
        show ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v
        rw [Units.val_one, Matrix.one_mulVec]
      mul_smul := fun s t v => by
        show (((s * t : T) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul] }
  have h := hT.card_modEq_card_fixedPoints (Fin n → K)
  have hfp : Nat.card (MulAction.fixedPoints ↥T (Fin n → K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, fun t => Matrix.mulVec_zero _⟩⟩⟩
    have ha : (a : Fin n → K) ∈ fixedSpace T := fun t ht => a.2 ⟨t, ht⟩
    have hb : (b : Fin n → K) ∈ fixedSpace T := fun t ht => b.2 ⟨t, ht⟩
    rw [hbot, Submodule.mem_bot] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have hcard : Nat.card (Fin n → K) = Nat.card K ^ n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  have h2 : 2 ∣ Nat.card (Fin n → K) := by
    rw [hcard]
    exact dvd_pow hK2 (by omega : n ≠ 0)
  rw [hfp] at h
  unfold Nat.ModEq at h
  omega

end Fixed

end CFSG.RankThree.PartOne.KFU
