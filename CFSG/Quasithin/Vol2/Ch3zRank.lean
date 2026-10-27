module

public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace Ch3z

@[expose] def IsRankTwoQuotient (X : Type*) [Group X] : Prop :=
  ∃ (H₀ : Type) (_ : Group H₀) (_ : Finite H₀),
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup H₀) ≤ 2) ∧
    ∃ f : H₀ →* X, Function.Surjective f

section Cube

abbrev Cube : Type := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

def cubeA3 : Subgroup Cube :=
  (alternatingGroup (Fin 3)).prod ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))

theorem card_alt3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem cubeA3_card : Nat.card cubeA3 = 3 ^ 3 := by
  have h1 : Nat.card cubeA3 = Nat.card (alternatingGroup (Fin 3)) *
      (Nat.card (alternatingGroup (Fin 3)) * Nat.card (alternatingGroup (Fin 3))) := by
    unfold cubeA3
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  rw [h1, card_alt3]
  norm_num

theorem cubeA3_pGroup : IsPGroup 3 cubeA3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.of_card cubeA3_card

theorem cubeA3_normal : cubeA3.Normal := by
  unfold cubeA3
  infer_instance

theorem cube_centralizer_le : Subgroup.centralizer (cubeA3 : Set Cube) ≤ cubeA3 := by
  intro x hx
  have key' : ∀ a : Equiv.Perm (Fin 3), (∀ n : Equiv.Perm (Fin 3), Equiv.Perm.sign n = 1 →
      a * n = n * a) → Equiv.Perm.sign a = 1 := by
    decide +kernel
  have key : ∀ a : Equiv.Perm (Fin 3), (∀ n : Equiv.Perm (Fin 3), n ∈ alternatingGroup (Fin 3) →
      a * n = n * a) → a ∈ alternatingGroup (Fin 3) := fun a h =>
    Equiv.Perm.mem_alternatingGroup.mpr
      (key' a fun n hn => h n (Equiv.Perm.mem_alternatingGroup.mpr hn))
  obtain ⟨a, b, c⟩ := x
  have ha := key a fun n hn => by
    have := Subgroup.mem_centralizer_iff.mp hx (n, 1, 1)
      ⟨hn, Subgroup.one_mem _, Subgroup.one_mem _⟩
    exact (Prod.ext_iff.mp this).1.symm
  have hb := key b fun n hn => by
    have := Subgroup.mem_centralizer_iff.mp hx (1, n, 1)
      ⟨Subgroup.one_mem _, hn, Subgroup.one_mem _⟩
    exact (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).1.symm
  have hc := key c fun n hn => by
    have := Subgroup.mem_centralizer_iff.mp hx (1, 1, n)
      ⟨Subgroup.one_mem _, Subgroup.one_mem _, hn⟩
    exact (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).2.symm
  exact ⟨ha, hb, hc⟩

set_option synthInstance.maxSize 4096 in
def cubeE : Subgroup Cube where
  carrier := {x | (x.1 = 1 ∨ x.1 = Equiv.swap 0 1) ∧ (x.2.1 = 1 ∨ x.2.1 = Equiv.swap 0 1) ∧
    (x.2.2 = 1 ∨ x.2.2 = Equiv.swap 0 1)}
  mul_mem' := by
    have h : ∀ a b : Cube, ((a.1 = 1 ∨ a.1 = Equiv.swap 0 1) ∧ (a.2.1 = 1 ∨ a.2.1 = Equiv.swap 0 1) ∧
        (a.2.2 = 1 ∨ a.2.2 = Equiv.swap 0 1)) →
        ((b.1 = 1 ∨ b.1 = Equiv.swap 0 1) ∧ (b.2.1 = 1 ∨ b.2.1 = Equiv.swap 0 1) ∧
        (b.2.2 = 1 ∨ b.2.2 = Equiv.swap 0 1)) →
        (((a * b).1 = 1 ∨ (a * b).1 = Equiv.swap 0 1) ∧
          ((a * b).2.1 = 1 ∨ (a * b).2.1 = Equiv.swap 0 1) ∧
          ((a * b).2.2 = 1 ∨ (a * b).2.2 = Equiv.swap 0 1)) := by decide +kernel
    intro a b ha hb
    exact h a b ha hb
  one_mem' := by simp
  inv_mem' := by
    have h : ∀ a : Cube, ((a.1 = 1 ∨ a.1 = Equiv.swap 0 1) ∧ (a.2.1 = 1 ∨ a.2.1 = Equiv.swap 0 1) ∧
        (a.2.2 = 1 ∨ a.2.2 = Equiv.swap 0 1)) →
        (((a⁻¹).1 = 1 ∨ (a⁻¹).1 = Equiv.swap 0 1) ∧ ((a⁻¹).2.1 = 1 ∨ (a⁻¹).2.1 = Equiv.swap 0 1) ∧
        ((a⁻¹).2.2 = 1 ∨ (a⁻¹).2.2 = Equiv.swap 0 1)) := by decide +kernel
    intro a ha
    exact h a ha

set_option synthInstance.maxSize 4096 in
theorem cubeE_card : Nat.card cubeE = 2 ^ 3 := by
  have : Nat.card cubeE = Nat.card {x : Cube // (x.1 = 1 ∨ x.1 = Equiv.swap 0 1) ∧
      (x.2.1 = 1 ∨ x.2.1 = Equiv.swap 0 1) ∧ (x.2.2 = 1 ∨ x.2.2 = Equiv.swap 0 1)} := rfl
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem cubeE_elem : IsElemAbelian 2 cubeE := by
  have hc : ∀ a b : Cube, ((a.1 = 1 ∨ a.1 = Equiv.swap 0 1) ∧ (a.2.1 = 1 ∨ a.2.1 = Equiv.swap 0 1) ∧
        (a.2.2 = 1 ∨ a.2.2 = Equiv.swap 0 1)) →
        ((b.1 = 1 ∨ b.1 = Equiv.swap 0 1) ∧ (b.2.1 = 1 ∨ b.2.1 = Equiv.swap 0 1) ∧
        (b.2.2 = 1 ∨ b.2.2 = Equiv.swap 0 1)) → a * b = b * a := by decide +kernel
  have h2 : ∀ a : Cube, ((a.1 = 1 ∨ a.1 = Equiv.swap 0 1) ∧ (a.2.1 = 1 ∨ a.2.1 = Equiv.swap 0 1) ∧
        (a.2.2 = 1 ∨ a.2.2 = Equiv.swap 0 1)) → a ^ 2 = 1 := by decide +kernel
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => h2 x hx⟩
  exact hc a.1 b.1 a.2 b.2

theorem three_le_pRank_cube : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Cube) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top cubeE_elem cubeE_card

theorem false_of_cube {X : Type*} [Group X] (hX : IsRankTwoQuotient X)
    (ψ : Cube →* X) (hψ : Function.Injective ψ) : False := by
  obtain ⟨H₀, _, _, hrk, f, hf⟩ := hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let G₀ : Subgroup H₀ := ψ.range.comap f
  let Φ : ↥G₀ →* Cube := (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp
    ((f.comp G₀.subtype).codRestrict ψ.range (fun g => g.2))
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨s, hs⟩ := hf (ψ q)
    have hmem : s ∈ G₀ := by
      show f s ∈ ψ.range
      rw [hs]
      exact ⟨q, rfl⟩
    refine ⟨⟨s, hmem⟩, ?_⟩
    show (MonoidHom.ofInjective hψ).symm ⟨f s, _⟩ = q
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hs
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥G₀) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) G₀.subtype G₀.subtype_injective).trans
      (hrk 3 Nat.prime_three (by norm_num))
  have hN : cubeA3.Normal := cubeA3_normal
  have hle : cubeA3 ≤ CFSG.Open.pCore 3 Cube := le_pCore 3 hN cubeA3_pGroup
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 Cube : Set Cube) ≤ CFSG.Open.pCore 3 Cube :=
      fun x hx =>
    hle (cube_centralizer_le (Subgroup.centralizer_le hle hx))
  have h131 := A1c.A131Concl_of_surjective (p := 3) (by norm_num) hF (Nat.card G₀) ↥G₀ Φ hΦ rfl hrk'
  have h2 := h131.2.1
  have h3 := three_le_pRank_cube
  omega

end Cube

section Copies

def s3Emb (m j : ℕ) (hj : 3 * j + 3 ≤ m) : Fin 3 ↪ Fin m :=
  ⟨fun i => ⟨3 * j + i, by omega⟩, fun a b h => by
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)⟩

noncomputable def s3Copy (m j : ℕ) (hj : 3 * j + 3 ≤ m) :
    Equiv.Perm (Fin 3) →* Equiv.Perm (Fin m) :=
  Equiv.Perm.viaEmbeddingHom (s3Emb m j hj)

theorem s3Copy_injective (m j : ℕ) (hj : 3 * j + 3 ≤ m) : Function.Injective (s3Copy m j hj) :=
  Equiv.Perm.viaEmbeddingHom_injective _

theorem s3Copy_apply_image (m j : ℕ) (hj : 3 * j + 3 ≤ m) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    s3Copy m j hj σ ⟨3 * j + i, by omega⟩ = ⟨3 * j + σ i, by omega⟩ := by
  have := Equiv.Perm.viaEmbedding_apply σ (s3Emb m j hj) i
  exact this

theorem s3Copy_apply_far (m j : ℕ) (hj : 3 * j + 3 ≤ m) (σ : Equiv.Perm (Fin 3)) (x : Fin m)
    (hx : ¬ (3 * j ≤ x.val ∧ x.val < 3 * j + 3)) : s3Copy m j hj σ x = x := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  apply hx
  have h2 : 3 * j + i.val = x.val := congrArg Fin.val hi
  have h3 := i.isLt
  omega

theorem s3Copy_eq_one_of_fix (m j : ℕ) (hj : 3 * j + 3 ≤ m) (σ : Equiv.Perm (Fin 3))
    (h : ∀ i : Fin 3, s3Copy m j hj σ ⟨3 * j + i, by omega⟩ = ⟨3 * j + i, by omega⟩) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  have h1 := h i
  rw [s3Copy_apply_image] at h1
  have := congrArg Fin.val h1
  simp only at this
  exact Fin.ext (by simpa using this)

theorem s3Copy_commute (m : ℕ) {j k : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (hjk : j ≠ k)
    (σ τ : Equiv.Perm (Fin 3)) :
    s3Copy m j hj σ * s3Copy m k hk τ = s3Copy m k hk τ * s3Copy m j hj σ := by
  have hd : Equiv.Perm.Disjoint (s3Copy m j hj σ) (s3Copy m k hk τ) := by
    intro x
    by_cases hx : 3 * j ≤ x.val ∧ x.val < 3 * j + 3
    · right
      apply s3Copy_apply_far
      omega
    · left
      exact s3Copy_apply_far m j hj σ x hx
  exact hd.commute.eq

end Copies

section CubeHom

theorem s3Copy_indep₂ (m : ℕ) {j k : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (hjk : j ≠ k)
    (σ τ : Equiv.Perm (Fin 3)) (h : s3Copy m j hj σ * s3Copy m k hk τ = 1) : σ = 1 ∧ τ = 1 := by
  have hσ : σ = 1 := by
    refine s3Copy_eq_one_of_fix m j hj σ fun i => ?_
    have h1 := congrArg (fun f : Equiv.Perm (Fin m) => f ⟨3 * j + i, by omega⟩) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
    rw [s3Copy_apply_far m k hk τ ⟨3 * j + i, by omega⟩ (by simp only; omega)] at h1
    exact h1
  subst hσ
  rw [map_one, one_mul] at h
  exact ⟨rfl, (s3Copy_injective m k hk) (h.trans (map_one _).symm)⟩

theorem s3Copy_indep₃ (m : ℕ) {j k l : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m)
    (hl : 3 * l + 3 ≤ m) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (σ τ ρ : Equiv.Perm (Fin 3))
    (h : s3Copy m j hj σ * s3Copy m k hk τ * s3Copy m l hl ρ = 1) :
    σ = 1 ∧ τ = 1 ∧ ρ = 1 := by
  have hσ : σ = 1 := by
    refine s3Copy_eq_one_of_fix m j hj σ fun i => ?_
    have h1 := congrArg (fun f : Equiv.Perm (Fin m) => f ⟨3 * j + i, by omega⟩) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
    rw [s3Copy_apply_far m l hl ρ ⟨3 * j + i, by omega⟩ (by simp only; omega),
      s3Copy_apply_far m k hk τ ⟨3 * j + i, by omega⟩ (by simp only; omega)] at h1
    exact h1
  subst hσ
  rw [map_one, one_mul] at h
  obtain ⟨h2, h3⟩ := s3Copy_indep₂ m hk hl hkl τ ρ h
  exact ⟨rfl, h2, h3⟩

theorem exists_cube_hom {M : Type*} [Group M] (ι₁ ι₂ ι₃ : Equiv.Perm (Fin 3) →* M)
    (h12 : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) (h13 : ∀ a c, ι₁ a * ι₃ c = ι₃ c * ι₁ a)
    (h23 : ∀ b c, ι₂ b * ι₃ c = ι₃ c * ι₂ b)
    (hind : ∀ a b c, ι₁ a * ι₂ b * ι₃ c = 1 → a = 1 ∧ b = 1 ∧ c = 1) :
    ∃ ψ : Cube →* M, Function.Injective ψ ∧ ∀ a b c, ψ (a, b, c) = ι₁ a * ι₂ b * ι₃ c := by
  let ψ₂ : (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) →* M :=
    ι₂.noncommCoprod ι₃ (fun b c => h23 b c)
  have hψ₂ : ∀ b c, ψ₂ (b, c) = ι₂ b * ι₃ c := fun b c => MonoidHom.noncommCoprod_apply _ _ _ _
  let ψ : Cube →* M := ι₁.noncommCoprod ψ₂ (fun a bc => by
    obtain ⟨b, c⟩ := bc
    show ι₁ a * ψ₂ (b, c) = ψ₂ (b, c) * ι₁ a
    rw [hψ₂]
    calc ι₁ a * (ι₂ b * ι₃ c) = (ι₁ a * ι₂ b) * ι₃ c := (mul_assoc _ _ _).symm
      _ = (ι₂ b * ι₁ a) * ι₃ c := by rw [h12]
      _ = ι₂ b * (ι₁ a * ι₃ c) := mul_assoc _ _ _
      _ = ι₂ b * (ι₃ c * ι₁ a) := by rw [h13]
      _ = (ι₂ b * ι₃ c) * ι₁ a := (mul_assoc _ _ _).symm)
  have hψ : ∀ a b c, ψ (a, b, c) = ι₁ a * ι₂ b * ι₃ c := by
    intro a b c
    show ι₁ a * ψ₂ (b, c) = _
    rw [hψ₂, mul_assoc]
  refine ⟨ψ, ?_, hψ⟩
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c⟩ h
  rw [hψ] at h
  obtain ⟨ha, hb, hc⟩ := hind a b c h
  rw [ha, hb, hc]
  rfl

end CubeHom

section BlockCubes

variable {V : Type} [CommGroup V]

noncomputable def blockCopy {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m)) (j : ℕ)
    (hj : 3 * j + 3 ≤ m) : Equiv.Perm (Fin 3) →* MulAut V :=
  H.subtype.comp (θ.symm.toMonoidHom.comp (s3Copy m j hj))

theorem blockCopy_mem {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m)) (j : ℕ)
    (hj : 3 * j + 3 ≤ m) (σ : Equiv.Perm (Fin 3)) : blockCopy θ j hj σ ∈ H :=
  (θ.symm (s3Copy m j hj σ)).2

theorem blockCopy_injective {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    (j : ℕ) (hj : 3 * j + 3 ≤ m) : Function.Injective (blockCopy θ j hj) := by
  intro a b h
  have h1 : θ.symm (s3Copy m j hj a) = θ.symm (s3Copy m j hj b) := Subtype.ext h
  exact s3Copy_injective m j hj (θ.symm.injective h1)

theorem blockCopy_commute {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    {j k : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (hjk : j ≠ k) (σ τ : Equiv.Perm (Fin 3)) :
    blockCopy θ j hj σ * blockCopy θ k hk τ = blockCopy θ k hk τ * blockCopy θ j hj σ := by
  have h := s3Copy_commute m hj hk hjk σ τ
  have h1 : θ.symm (s3Copy m j hj σ) * θ.symm (s3Copy m k hk τ) =
      θ.symm (s3Copy m k hk τ) * θ.symm (s3Copy m j hj σ) := by
    rw [← map_mul, ← map_mul, h]
  exact congrArg Subtype.val h1

theorem blockCopy_mul_eq_one {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    {j k : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (σ τ : Equiv.Perm (Fin 3)) :
    blockCopy θ j hj σ * blockCopy θ k hk τ =
      ((θ.symm (s3Copy m j hj σ * s3Copy m k hk τ) : ↥H) : MulAut V) := by
  simp only [map_mul]
  rfl

theorem blockCopy_indep₂ {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    {j k : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (hjk : j ≠ k) (σ τ : Equiv.Perm (Fin 3))
    (h : blockCopy θ j hj σ * blockCopy θ k hk τ = 1) : σ = 1 ∧ τ = 1 := by
  rw [blockCopy_mul_eq_one] at h
  have h1 : θ.symm (s3Copy m j hj σ * s3Copy m k hk τ) = 1 := Subtype.ext h
  have h2 := θ.symm.injective (h1.trans (map_one θ.symm).symm)
  exact s3Copy_indep₂ m hj hk hjk σ τ h2

theorem blockCopy_indep₃ {H : Subgroup (MulAut V)} {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m))
    {j k l : ℕ} (hj : 3 * j + 3 ≤ m) (hk : 3 * k + 3 ≤ m) (hl : 3 * l + 3 ≤ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (σ τ ρ : Equiv.Perm (Fin 3))
    (h : blockCopy θ j hj σ * blockCopy θ k hk τ * blockCopy θ l hl ρ = 1) :
    σ = 1 ∧ τ = 1 ∧ ρ = 1 := by
  have h1 : θ.symm (s3Copy m j hj σ * s3Copy m k hk τ * s3Copy m l hl ρ) = 1 := by
    apply Subtype.ext
    have e : ((θ.symm (s3Copy m j hj σ * s3Copy m k hk τ * s3Copy m l hl ρ) : ↥H) : MulAut V) =
        blockCopy θ j hj σ * blockCopy θ k hk τ * blockCopy θ l hl ρ := by
      simp only [map_mul]
      rfl
    exact e.trans h
  have h2 := θ.symm.injective (h1.trans (map_one θ.symm).symm)
  exact s3Copy_indep₃ m hj hk hl hjk hjl hkl σ τ ρ h2

theorem false_of_three_blocks {X H₁ H₂ H₃ : Subgroup (MulAut V)} (hX : IsRankTwoQuotient ↥X)
    (h₁X : H₁ ≤ X) (h₂X : H₂ ≤ X) (h₃X : H₃ ≤ X)
    {m₁ m₂ m₃ : ℕ} (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m₁)) (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m₂))
    (θ₃ : ↥H₃ ≃* Equiv.Perm (Fin m₃)) (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) (hm₃ : 3 ≤ m₃)
    (h12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (h13 : ∀ a ∈ H₁, ∀ b ∈ H₃, a * b = b * a)
    (h23 : ∀ a ∈ H₂, ∀ b ∈ H₃, a * b = b * a)
    (hind : ∀ a ∈ H₁, ∀ b ∈ H₂, ∀ c ∈ H₃, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1) : False := by
  have e₁ : 3 * 0 + 3 ≤ m₁ := by omega
  have e₂ : 3 * 0 + 3 ≤ m₂ := by omega
  have e₃ : 3 * 0 + 3 ≤ m₃ := by omega
  obtain ⟨ψ, hψi, hψ⟩ := exists_cube_hom (blockCopy θ₁ 0 e₁) (blockCopy θ₂ 0 e₂)
    (blockCopy θ₃ 0 e₃) (fun a b => h12 _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _))
    (fun a c => h13 _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _))
    (fun b c => h23 _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _))
    (fun a b c h => by
      obtain ⟨ha, hb, hc⟩ := hind _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _) _
        (blockCopy_mem _ _ _ _) h
      exact ⟨blockCopy_injective θ₁ 0 e₁ (ha.trans (map_one _).symm),
        blockCopy_injective θ₂ 0 e₂ (hb.trans (map_one _).symm),
        blockCopy_injective θ₃ 0 e₃ (hc.trans (map_one _).symm)⟩)
  have hmem : ∀ x : Cube, ψ x ∈ X := by
    rintro ⟨a, b, c⟩
    rw [hψ]
    exact X.mul_mem (X.mul_mem (h₁X (blockCopy_mem _ _ _ _)) (h₂X (blockCopy_mem _ _ _ _)))
      (h₃X (blockCopy_mem _ _ _ _))
  exact false_of_cube hX (ψ.codRestrict X hmem) fun x y hxy => hψi (congrArg Subtype.val hxy)

theorem false_of_two_blocks {X H₁ H₂ : Subgroup (MulAut V)} (hX : IsRankTwoQuotient ↥X)
    (h₁X : H₁ ≤ X) (h₂X : H₂ ≤ X) {m₁ m₂ : ℕ} (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m₁))
    (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m₂)) (hm₁ : 6 ≤ m₁) (hm₂ : 3 ≤ m₂)
    (h12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a)
    (hind : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = 1 → a = 1 ∧ b = 1) : False := by
  have e₀ : 3 * 0 + 3 ≤ m₁ := by omega
  have e₁ : 3 * 1 + 3 ≤ m₁ := by omega
  have e₃ : 3 * 0 + 3 ≤ m₂ := by omega
  obtain ⟨ψ, hψi, hψ⟩ := exists_cube_hom (blockCopy θ₁ 0 e₀) (blockCopy θ₁ 1 e₁)
    (blockCopy θ₂ 0 e₃) (fun a b => blockCopy_commute θ₁ e₀ e₁ (by omega) a b)
    (fun a c => h12 _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _))
    (fun b c => h12 _ (blockCopy_mem _ _ _ _) _ (blockCopy_mem _ _ _ _))
    (fun a b c h => by
      obtain ⟨hab, hc⟩ := hind _ (blockCopy_mem θ₁ 0 e₀ a |> fun h0 =>
        H₁.mul_mem h0 (blockCopy_mem θ₁ 1 e₁ b)) _ (blockCopy_mem _ _ _ _) h
      obtain ⟨ha, hb⟩ := blockCopy_indep₂ θ₁ e₀ e₁ (by omega) a b hab
      exact ⟨ha, hb, blockCopy_injective θ₂ 0 e₃ (hc.trans (map_one _).symm)⟩)
  have hmem : ∀ x : Cube, ψ x ∈ X := by
    rintro ⟨a, b, c⟩
    rw [hψ]
    exact X.mul_mem (X.mul_mem (h₁X (blockCopy_mem _ _ _ _)) (h₁X (blockCopy_mem _ _ _ _)))
      (h₂X (blockCopy_mem _ _ _ _))
  exact false_of_cube hX (ψ.codRestrict X hmem) fun x y hxy => hψi (congrArg Subtype.val hxy)

theorem false_of_one_block {X H : Subgroup (MulAut V)} (hX : IsRankTwoQuotient ↥X) (hHX : H ≤ X)
    {m : ℕ} (θ : ↥H ≃* Equiv.Perm (Fin m)) (hm : 9 ≤ m) : False := by
  have e₀ : 3 * 0 + 3 ≤ m := by omega
  have e₁ : 3 * 1 + 3 ≤ m := by omega
  have e₂ : 3 * 2 + 3 ≤ m := by omega
  obtain ⟨ψ, hψi, hψ⟩ := exists_cube_hom (blockCopy θ 0 e₀) (blockCopy θ 1 e₁) (blockCopy θ 2 e₂)
    (fun a b => blockCopy_commute θ e₀ e₁ (by omega) a b)
    (fun a c => blockCopy_commute θ e₀ e₂ (by omega) a c)
    (fun b c => blockCopy_commute θ e₁ e₂ (by omega) b c)
    (fun a b c h => blockCopy_indep₃ θ e₀ e₁ e₂ (by omega) (by omega) (by omega) a b c h)
  have hmem : ∀ x : Cube, ψ x ∈ X := by
    rintro ⟨a, b, c⟩
    rw [hψ]
    exact X.mul_mem (X.mul_mem (hHX (blockCopy_mem _ _ _ _)) (hHX (blockCopy_mem _ _ _ _)))
      (hHX (blockCopy_mem _ _ _ _))
  exact false_of_cube hX (ψ.codRestrict X hmem) fun x y hxy => hψi (congrArg Subtype.val hxy)

end BlockCubes

end Ch3z

end CFSG.Quasithin
