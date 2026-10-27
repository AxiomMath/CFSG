module

public import CFSG.RankThree.PartOne.KF.QuadTorus
public import CFSG.RankThree.PartOne.KF.D8Module

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def d8Pair : D8Mod p (Qext K) →* (Fin 2 → (Qext K)ˣ) where
  toFun v := ![((v.1 : rootsOfUnity p (Qext K)) : (Qext K)ˣ),
    ((v.2 : rootsOfUnity p (Qext K)) : (Qext K)ˣ)]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' v w := by
    funext i
    fin_cases i <;> simp

@[expose] noncomputable def d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  torusHom.comp d8Pair

theorem d8Emb_apply (v : D8Mod p (Qext K)) (w : QV K (Fin 2)) (i : Fin 2) :
    d8Emb v w i = (d8Pair v i : Qext K) * w i := rfl

theorem d8Emb_apply_zero (v : D8Mod p (Qext K)) (w : QV K (Fin 2)) :
    d8Emb v w 0 = (((v.1 : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * w 0 := by
  simp [d8Emb_apply, d8Pair]

theorem d8Emb_apply_one (v : D8Mod p (Qext K)) (w : QV K (Fin 2)) :
    d8Emb v w 1 = (((v.2 : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) * w 1 := by
  simp [d8Emb_apply, d8Pair]

theorem d8Emb_injective : Function.Injective (d8Emb (p := p) (K := K)) := by
  intro v w h
  have h0 := congrArg (fun g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => g (fun _ => 1) 0) h
  have h1 := congrArg (fun g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => g (fun _ => 1) 1) h
  simp only [d8Emb_apply_zero, d8Emb_apply_one, mul_one] at h0 h1
  refine Prod.ext ?_ ?_
  · simpa using (Units.ext h0)
  · simpa using (Units.ext h1)

theorem d8Emb_pow (v : D8Mod p (Qext K)) : d8Emb v ^ p = 1 := by
  rw [← map_pow]
  have : v ^ p = 1 := Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp v.1.2))
    (Subtype.ext ((mem_rootsOfUnity p _).mp v.2.2))
  rw [this, map_one]

theorem d8Emb_comm (v w : D8Mod p (Qext K)) : d8Emb v * d8Emb w = d8Emb w * d8Emb v := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem conj_eq_of_intertwine {ι : Type} (g : QV K ι ≃ₗ[K] QV K ι) (x y : ι → (Qext K)ˣ)
    (h : ∀ w, g (torusEquiv x w) = torusEquiv y (g w)) : g * torusEquiv x * g⁻¹ = torusEquiv y := by
  refine LinearEquiv.ext fun w => ?_
  have : g (torusEquiv x (g⁻¹ w)) = torusEquiv y w := by
    rw [h]
    simp
  simpa using this

@[expose] noncomputable def gRef : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) :=
  LinearEquiv.piCongrRight ![(frobQ K).toLinearEquiv, LinearEquiv.refl K (Qext K)]

@[expose] noncomputable def gSwap : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) :=
  LinearEquiv.funCongrLeft K (Qext K) (Equiv.swap (0 : Fin 2) 1)

@[expose] noncomputable def gRot : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) := gSwap * gRef

theorem gRef_apply (v : QV K (Fin 2)) : gRef v = ![frobQ K (v 0), v 1] := by
  funext i
  fin_cases i <;> simp [gRef]

theorem gSwap_apply (v : QV K (Fin 2)) : gSwap v = ![v 1, v 0] := by
  funext i
  fin_cases i <;> simp [gSwap, LinearEquiv.funCongrLeft_apply]

theorem gRot_apply (v : QV K (Fin 2)) : gRot v = ![v 1, frobQ K (v 0)] := by
  funext i
  fin_cases i <;> simp [gRot, gSwap_apply, gRef_apply]

theorem frobQ_root (hpq : p ∣ Nat.card K + 1) (z : rootsOfUnity p (Qext K)) :
    frobQ K (((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) =
      ((((z⁻¹ : rootsOfUnity p (Qext K)) : (Qext K)ˣ)) : Qext K) := by
  have hz : ((z : (Qext K)ˣ) : Qext K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p _).mp z.2, Units.val_one]
  have hq : ((z : (Qext K)ˣ) : Qext K) ^ (Nat.card K + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hz, one_pow]
  rw [frobQ_eq_inv hq]
  simp

theorem gRef_intertwine (hpq : p ∣ Nat.card K + 1) (v : D8Mod p (Qext K))
    (w : QV K (Fin 2)) : gRef (d8Emb v w) = d8Emb (d8Ref v) (gRef w) := by
  funext i
  fin_cases i
  · simp [gRef_apply, d8Emb_apply_zero, d8Ref_apply, map_mul, frobQ_root hpq]
  · simp [gRef_apply, d8Emb_apply_one, d8Ref_apply]

theorem gRot_intertwine (hpq : p ∣ Nat.card K + 1) (v : D8Mod p (Qext K))
    (w : QV K (Fin 2)) : gRot (d8Emb v w) = d8Emb (d8Rot v) (gRot w) := by
  funext i
  fin_cases i
  · simp [gRot_apply, d8Emb_apply_zero, d8Emb_apply_one, d8Rot_apply]
  · simp [gRot_apply, d8Emb_apply_zero, d8Emb_apply_one, d8Rot_apply, map_mul, frobQ_root hpq]

@[expose] def Realizes (γ : DihedralGroup 4) (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : Prop :=
  ∀ v : D8Mod p (Qext K), g * d8Emb v * g⁻¹ = d8Emb (d8Act γ v)

theorem realizes_mul {γ₁ γ₂ : DihedralGroup 4} {g₁ g₂ : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)}
    (h₁ : Realizes (p := p) γ₁ g₁) (h₂ : Realizes (p := p) γ₂ g₂) :
    Realizes (p := p) (γ₁ * γ₂) (g₁ * g₂) := by
  intro v
  have : g₁ * g₂ * d8Emb v * (g₁ * g₂)⁻¹ = g₁ * (g₂ * d8Emb v * g₂⁻¹) * g₁⁻¹ := by group
  rw [this, h₂ v, h₁, map_mul, MulAut.mul_apply]

theorem realizes_one : Realizes (p := p) (K := K) 1 1 := by
  intro v
  simp

theorem realizes_gRef (hpq : p ∣ Nat.card K + 1) :
    Realizes (p := p) (DihedralGroup.sr 0) (gRef : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) := by
  intro v
  refine conj_eq_of_intertwine _ _ _ fun w => ?_
  have := gRef_intertwine hpq v w
  rw [d8Act_sr_zero] at *
  exact this

theorem realizes_gRot (hpq : p ∣ Nat.card K + 1) :
    Realizes (p := p) (DihedralGroup.r 1) (gRot : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) := by
  intro v
  refine conj_eq_of_intertwine _ _ _ fun w => ?_
  have := gRot_intertwine hpq v w
  rw [d8Act_r_one]
  exact this

omit [Finite K] in
theorem det_eq_one_of_mul_self {V : Type*} [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (hg : g * g = 1) : LinearEquiv.det g = 1 := by
  have h1 : LinearEquiv.det g * LinearEquiv.det g = 1 := by rw [← map_mul, hg, map_one]
  have h2 : ((LinearEquiv.det g : Kˣ) : K) * ((LinearEquiv.det g : Kˣ) : K) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) h1
    simpa using this
  have h3 : (((LinearEquiv.det g : Kˣ) : K) - 1) ^ 2 = 0 := by
    have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (((LinearEquiv.det g : Kˣ) : K) - 1) ^ 2
        = ((LinearEquiv.det g : Kˣ) : K) * ((LinearEquiv.det g : Kˣ) : K)
          - 2 * ((LinearEquiv.det g : Kˣ) : K) + 1 := by ring
      _ = 0 := by
        have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2'
        rw [h2, h2', zero_mul, sub_zero]
        exact h11
  have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  exact Units.ext (sub_eq_zero.mp h4)

theorem gRef_mul_self : (gRef : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * gRef = 1 := by
  refine LinearEquiv.ext fun w => funext fun i => ?_
  fin_cases i
  · simp [gRef_apply, frobQ_frobQ]
  · simp [gRef_apply]

theorem gSwap_mul_self : (gSwap : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * gSwap = 1 := by
  refine LinearEquiv.ext fun w => funext fun i => ?_
  fin_cases i <;> simp [gSwap_apply]

theorem exists_realizer (hpq : p ∣ Nat.card K + 1) (γ : DihedralGroup 4) :
    ∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2), LinearEquiv.det g = 1 ∧ Realizes (p := p) γ g := by
  have hmul : ∀ γ₁ γ₂ : DihedralGroup 4,
      (∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2), LinearEquiv.det g = 1 ∧ Realizes (p := p) γ₁ g) →
      (∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2), LinearEquiv.det g = 1 ∧ Realizes (p := p) γ₂ g) →
      ∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2),
        LinearEquiv.det g = 1 ∧ Realizes (p := p) (γ₁ * γ₂) g := by
    rintro γ₁ γ₂ ⟨g₁, hd₁, hr₁⟩ ⟨g₂, hd₂, hr₂⟩
    exact ⟨g₁ * g₂, by rw [map_mul, hd₁, hd₂, one_mul], realizes_mul hr₁ hr₂⟩
  have h1 : ∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2),
      LinearEquiv.det g = 1 ∧ Realizes (p := p) 1 g := ⟨1, map_one _, realizes_one⟩
  have hs0 : ∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2),
      LinearEquiv.det g = 1 ∧ Realizes (p := p) (DihedralGroup.sr 0) g :=
    ⟨gRef, det_eq_one_of_mul_self _ gRef_mul_self, realizes_gRef hpq⟩
  have hr1 : ∃ g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2),
      LinearEquiv.det g = 1 ∧ Realizes (p := p) (DihedralGroup.r 1) g :=
    ⟨gRot, by
      rw [gRot, map_mul, det_eq_one_of_mul_self _ gSwap_mul_self,
        det_eq_one_of_mul_self _ gRef_mul_self, one_mul], realizes_gRot hpq⟩
  have e2 : (DihedralGroup.r 2 : DihedralGroup 4) = DihedralGroup.r 1 * DihedralGroup.r 1 := by
    decide
  have e3 : (DihedralGroup.r 3 : DihedralGroup 4) =
      DihedralGroup.r 1 * DihedralGroup.r 1 * DihedralGroup.r 1 := by decide
  have f1 : (DihedralGroup.sr 1 : DihedralGroup 4) = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
    decide
  have f2 : (DihedralGroup.sr 2 : DihedralGroup 4) =
      DihedralGroup.sr 0 * (DihedralGroup.r 1 * DihedralGroup.r 1) := by decide
  have f3 : (DihedralGroup.sr 3 : DihedralGroup 4) =
      DihedralGroup.sr 0 * (DihedralGroup.r 1 * DihedralGroup.r 1 * DihedralGroup.r 1) := by
    decide
  rcases dihedral_four_cases γ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [DihedralGroup.r_zero]
    exact h1
  · exact hr1
  · rw [e2]
    exact hmul _ _ hr1 hr1
  · rw [e3]
    exact hmul _ _ (hmul _ _ hr1 hr1) hr1
  · exact hs0
  · rw [f1]
    exact hmul _ _ hs0 hr1
  · rw [f2]
    exact hmul _ _ hs0 (hmul _ _ hr1 hr1)
  · rw [f3]
    exact hmul _ _ hs0 (hmul _ _ (hmul _ _ hr1 hr1) hr1)

omit [Finite K] in
theorem d8Pair_pow (v : D8Mod p (Qext K)) (i : Fin 2) : d8Pair v i ^ p = 1 := by
  fin_cases i
  · simpa [d8Pair] using (mem_rootsOfUnity p _).mp v.1.2
  · simpa [d8Pair] using (mem_rootsOfUnity p _).mp v.2.2

theorem perm_two_cases (π : Equiv.Perm (Fin 2)) : π = 1 ∨ π = Equiv.swap 0 1 := by
  revert π
  decide

theorem exists_dihedral_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
    (hg : ∀ v : D8Mod p (Qext K), ∃ v' : D8Mod p (Qext K), g * d8Emb v * g⁻¹ = d8Emb v') :
    ∃ w : DihedralGroup 4, ∀ v : D8Mod p (Qext K), g * d8Emb v * g⁻¹ = d8Emb (d8Act w v) := by
  have hg' : ∀ x : Fin 2 → (Qext K)ˣ, (∀ i, x i ^ p = 1) →
      ∃ y : Fin 2 → (Qext K)ˣ, g * torusEquiv x * g⁻¹ = torusEquiv y := by
    intro x hx
    let v : D8Mod p (Qext K) := (⟨x 0, (mem_rootsOfUnity p _).mpr (hx 0)⟩,
      ⟨x 1, (mem_rootsOfUnity p _).mpr (hx 1)⟩)
    obtain ⟨v', hv'⟩ := hg v
    refine ⟨d8Pair v', ?_⟩
    have hxv : x = d8Pair v := by
      funext i
      fin_cases i <;> simp [d8Pair, v]
    rw [hxv]
    exact hv'
  obtain ⟨π, ε, H⟩ := normalizer_torus_units hp hp2 hpq g hg'
  have key : ∃ w : DihedralGroup 4, ∀ v v' : D8Mod p (Qext K),
      g * d8Emb v * g⁻¹ = d8Emb v' → v' = d8Act w v := by
    rcases perm_two_cases π with rfl | rfl <;> cases h0 : ε 0 <;> cases h1 : ε 1
    · refine ⟨DihedralGroup.r 0, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_r_zero]
      refine Prod.ext ?_ ?_
      · simpa using a0
      · simpa using a1
    · refine ⟨DihedralGroup.sr 2, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_sr_two]
      refine Prod.ext ?_ ?_
      · simpa using a0
      · exact Subtype.ext (by simpa using a1)
    · refine ⟨DihedralGroup.sr 0, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_sr_zero]
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (by simpa using a0)
      · simpa using a1
    · refine ⟨DihedralGroup.r 2, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_r_two]
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (by simpa using a0)
      · exact Subtype.ext (by simpa using a1)
    · refine ⟨DihedralGroup.sr 3, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_sr_three]
      refine Prod.ext ?_ ?_
      · simpa using a1
      · simpa using a0
    · refine ⟨DihedralGroup.r 3, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_r_three]
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (by simpa using a1)
      · simpa using a0
    · refine ⟨DihedralGroup.r 1, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_r_one]
      refine Prod.ext ?_ ?_
      · simpa using a1
      · exact Subtype.ext (by simpa using a0)
    · refine ⟨DihedralGroup.sr 1, fun v v' hrel => ?_⟩
      have a0 := H _ _ (d8Pair_pow v) hrel 0
      have a1 := H _ _ (d8Pair_pow v) hrel 1
      simp [d8Pair, h0] at a0
      simp [d8Pair, h1] at a1
      rw [d8Act_sr_one]
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (by simpa using a1)
      · exact Subtype.ext (by simpa using a0)
  obtain ⟨w, hw⟩ := key
  refine ⟨w, fun v => ?_⟩
  obtain ⟨v', hv'⟩ := hg v
  rw [hv', hw v v' hv']

end CFSG.RankThree.PartOne.KFQ
