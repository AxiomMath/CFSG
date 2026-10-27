module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection
public import CFSG.LocalAnalysis.StandardType.GGCoxeterPrimeSquare
public import CFSG.LocalAnalysis.StandardType.GGCoxeterPrimePower

public section

namespace CFSG.StandardType.QuotMove

open CFSG CFSG.Assembly Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K] {R : Type} [Group R]
  {N : Subgroup (GL κ K)} {c : N →* MulAut R} {S : Subgroup (GL κ K)}
  {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} {p : ℕ}

theorem conj_mem_inducedSub_of_shear (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (E : S) (δ : N) (hδ : c δ ∈ TypeA.inducedSub ψ A)
    (hEx : (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = δ * x₀)
    (hEy : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      (E : GL κ K) * y = y * E)
    {x : MulAut R} (hx : x ∈ TypeA.inducedSub ψ A) :
    c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
      TypeA.inducedSub ψ A := by
  set X := TypeA.inducedSub ψ A with hX
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hconj : ∀ z : N, c E' * c z * (c E')⁻¹ = c (E' * z * E'⁻¹) := fun z => by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
  obtain ⟨M', hM'⟩ := hAI a ha
  have hMx : c M' = x := TypeA.induced_unique ψ hψ hM' hxa
  obtain ⟨s, y, k, hyX, hyp, hMeq⟩ :=
    exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ (M := M') (hMx ▸ hx)
  have e : E' * M' * E'⁻¹ =
      ⟨GeneralLinearGroup.scalar κ s, hc.scalar_mem s⟩ * y * (δ * x₀) ^ k := by
    apply Subtype.ext
    change (E : GL κ K) * M' * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ s * y * ((δ : GL κ K) * x₀) ^ k
    have hEs := (TypeA.PGLTor.commute_scalar s (E : GL κ K)).eq
    rw [hMeq, ← hEx, conj_pow]
    calc (E : GL κ K) * (GeneralLinearGroup.scalar κ s * y * (x₀ : GL κ K) ^ k) *
          (E : GL κ K)⁻¹
        = ((E : GL κ K) * GeneralLinearGroup.scalar κ s) * y * (x₀ : GL κ K) ^ k *
            (E : GL κ K)⁻¹ := by group
      _ = GeneralLinearGroup.scalar κ s * ((E : GL κ K) * y) * (x₀ : GL κ K) ^ k *
            (E : GL κ K)⁻¹ := by rw [← hEs]; group
      _ = GeneralLinearGroup.scalar κ s * y *
            ((E : GL κ K) * (x₀ : GL κ K) ^ k * (E : GL κ K)⁻¹) := by
          rw [hEy y hyX hyp]; group
  rw [← hMx, hconj, e, map_mul, map_mul, hc.map_scalar, one_mul, map_pow, map_mul]
  exact X.mul_mem hyX (X.pow_mem (X.mul_mem hδ hx₀) k)

theorem exists_mem_ggAutomizer_of_conj_mem (hc : IsScalarQuot c S) [Finite L']
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    (E : S) (hEN : ∀ x ∈ TypeA.inducedSub ψ A,
      c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
        TypeA.inducedSub ψ A) :
    ∃ t ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ∀ (a b : ↥A) (Ma Mb : N), (∀ l, c Ma (ψ l) = ψ ((a : MulAut L') l)) →
        (∀ l, c Mb (ψ l) = ψ ((b : MulAut L') l)) →
        c (Subgroup.inclusion hc.le E) * c Ma * (c (Subgroup.inclusion hc.le E))⁻¹ = c Mb →
        t a = b := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  obtain ⟨r₀, hr₀⟩ := hc.inner' E
  obtain ⟨n, hψn⟩ := hψ r₀
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hcn : MulAut.conj (ψ n) = c E' := by
    rw [hψn]; exact hr₀
  have hact : ∀ (a b : MulAut L') (Ma Mb : N), (∀ l, c Ma (ψ l) = ψ (a l)) →
      (∀ l, c Mb (ψ l) = ψ (b l)) → c E' * c Ma * (c E')⁻¹ = c Mb →
      MulAut.conj n * a * (MulAut.conj n)⁻¹ = b := by
    intro a b Ma Mb hMa hMb hab
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← TypeA.conj_induced_apply ψ hMa n l, hcn, hab, hMb]
  have hnN : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj n)).injective).ge
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨Ma, hMa⟩ := hAI a ha
    have hMaX : c Ma ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hMa⟩
    obtain ⟨b, hb, hbind⟩ := TypeA.mem_inducedSub.mp (hEN _ hMaX)
    obtain ⟨Mb, hMb⟩ := hAI b hb
    have hcb : c E' * c Ma * (c E')⁻¹ = c Mb := TypeA.induced_unique ψ hψ hbind hMb
    change MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A
    rw [hact a b Ma Mb hMa hMb hcb]
    exact hb
  refine ⟨ggConjAut A hnN, ggConjAut_mem_ggAutomizer
    (H := (MulAut.conj : L' →* MulAut L').range) (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN, ?_⟩
  intro a b Ma Mb hMa hMb hab
  apply Subtype.ext
  rw [ggConjAut_apply, hact a b Ma Mb hMa hMb hab]

theorem card_le_sq_of_forall_eq_scalar_mul_pow (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    {δ : N} (hδ : c δ ∈ TypeA.inducedSub ψ A)
    (hall : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      ∃ (u : Kˣ) (e : ℕ), (y : GL κ K) = GeneralLinearGroup.scalar κ u * (δ : GL κ K) ^ e) :
    Nat.card A ≤ p ^ 2 := by
  classical
  set X := TypeA.inducedSub ψ A with hX
  have hXab : IsElemAbelian p X := TypeA.isElemAbelian_inducedSub hψ hA
  set T : Finset (MulAut R) := (Finset.range p ×ˢ Finset.range p).image
    (fun jk : ℕ × ℕ => c δ ^ jk.1 * c x₀ ^ jk.2) with hT
  have hsub : (X : Set (MulAut R)) ⊆ (T : Set (MulAut R)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨M, hM⟩ := hAI a ha
    have hMx : c M = x := TypeA.induced_unique ψ hψ hM hxa
    obtain ⟨s, y, k, hyX, hyp, hMeq⟩ :=
      exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ (M := M) (hMx ▸ hx)
    obtain ⟨u, e, hu⟩ := hall y hyX hyp
    have hMe : M = ⟨GeneralLinearGroup.scalar κ (s * u), hc.scalar_mem _⟩ * δ ^ e * x₀ ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_mk]
      rw [hMeq, hu, map_mul]
      simp only [mul_assoc]
    have hcx : x = c δ ^ (e % p) * c x₀ ^ (k % p) := by
      rw [← hMx, hMe, map_mul, map_mul, hc.map_scalar, one_mul, map_pow, map_pow,
        ← pow_eq_pow_mod e (hXab.2 _ hδ), ← pow_eq_pow_mod k (hXab.2 _ hx₀)]
    rw [Finset.mem_coe, hT, Finset.mem_image]
    exact ⟨(e % p, k % p), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp.pos),
      Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)⟩, hcx.symm⟩
  have hcardX : Nat.card X = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨M, hM⟩ := hAI a ha
      exact ⟨c M, hM⟩)
  have h1 : Nat.card X ≤ T.card := by
    calc Nat.card X = (X : Set (MulAut R)).ncard := Nat.card_coe_set_eq _
      _ ≤ (T : Set (MulAut R)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet T)
      _ = T.card := Set.ncard_coe_finset T
  have h2 : T.card ≤ p ^ 2 := by
    calc T.card ≤ (Finset.range p ×ˢ Finset.range p).card := Finset.card_image_le
      _ = p ^ 2 := by rw [Finset.card_product, Finset.card_range, sq]
  omega

section TwoShears


theorem false_of_two_shears (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hp : p.Prime) (hp5 : 5 ≤ p) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l)) (hcardA : Nat.card A ≤ p ^ 4)
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (E₁ E₂ : S) (δ₁ δ₂ : N) (hδ₁ : c δ₁ ∈ TypeA.inducedSub ψ A)
    (hδ₂ : c δ₂ ∈ TypeA.inducedSub ψ A) (hδ₁p : (δ₁ : GL κ K) ^ p = 1)
    (hδ₂p : (δ₂ : GL κ K) ^ p = 1) (hind : ∀ i k : ℕ, c δ₁ ^ i * c δ₂ ^ k = 1 → p ∣ i ∧ p ∣ k)
    (hE₁x : (E₁ : GL κ K) * x₀ * (E₁ : GL κ K)⁻¹ = δ₁ * x₀)
    (hE₂x : (E₂ : GL κ K) * x₀ * (E₂ : GL κ K)⁻¹ = δ₂ * x₀)
    (hE₁y : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      (E₁ : GL κ K) * y = y * E₁)
    (hE₂y : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      (E₂ : GL κ K) * y = y * E₂)
    [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  set X := TypeA.inducedSub ψ A with hX
  obtain ⟨a₀v, ha₀v, ha₀⟩ := TypeA.mem_inducedSub.mp hx₀
  obtain ⟨d₁v, hd₁v, hd₁⟩ := TypeA.mem_inducedSub.mp hδ₁
  obtain ⟨d₂v, hd₂v, hd₂⟩ := TypeA.mem_inducedSub.mp hδ₂
  set a₀ : ↥A := ⟨a₀v, ha₀v⟩ with ha₀def
  set d₁ : ↥A := ⟨d₁v, hd₁v⟩ with hd₁def
  set d₂ : ↥A := ⟨d₂v, hd₂v⟩ with hd₂def
  have hApow : ∀ b : ↥A, b ^ p = 1 := fun b => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 _ b.2)
  have hAcomm : ∀ b b' : ↥A, b * b' = b' * b := fun b b' => hA.1.is_comm.comm b b'
  have hdecomp : ∀ a : ↥A, ∃ (y : N) (b : ↥A) (k : ℕ), c y ∈ X ∧ (y : GL κ K) ^ p = 1 ∧
      (∀ l, c y (ψ l) = ψ ((b : MulAut L') l)) ∧ a = b * a₀ ^ k := by
    intro a
    obtain ⟨Ma, hMa⟩ := hAI a a.2
    have hMaX : c Ma ∈ X := TypeA.mem_inducedSub.mpr ⟨a, a.2, hMa⟩
    obtain ⟨s, y, k, hyX, hyp, hMeq⟩ := exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ hMaX
    obtain ⟨bv, hbv, hb⟩ := TypeA.mem_inducedSub.mp hyX
    refine ⟨y, ⟨bv, hbv⟩, k, hyX, hyp, hb, ?_⟩
    have e : Ma = ⟨GeneralLinearGroup.scalar κ s, hc.scalar_mem s⟩ * y * x₀ ^ k :=
      Subtype.ext hMeq
    apply Subtype.ext
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hMa l, e, map_mul, map_mul, hc.map_scalar, one_mul, map_pow, MulAut.mul_apply,
      TypeA.induced_pow ψ ha₀ k l, hb]
    rfl
  have hshear : ∀ (E : S) (δ : N) (d : ↥A) (t : MulAut ↥A),
      (∀ l, c δ (ψ l) = ψ ((d : MulAut L') l)) →
      (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = δ * x₀ →
      (∀ y : N, c y ∈ X → (y : GL κ K) ^ p = 1 → (E : GL κ K) * y = y * E) →
      (∀ (a b : ↥A) (Ma Mb : N), (∀ l, c Ma (ψ l) = ψ ((a : MulAut L') l)) →
        (∀ l, c Mb (ψ l) = ψ ((b : MulAut L') l)) →
        c (Subgroup.inclusion hc.le E) * c Ma * (c (Subgroup.inclusion hc.le E))⁻¹ = c Mb →
        t a = b) →
      t a₀ = d * a₀ ∧ ∀ (y : N) (b : ↥A), (y : GL κ K) ^ p = 1 → c y ∈ X →
        (∀ l, c y (ψ l) = ψ ((b : MulAut L') l)) → t b = b := by
    intro E δ d t hd hEx hEy ht
    have hconj : ∀ z : N, c (Subgroup.inclusion hc.le E) * c z *
        (c (Subgroup.inclusion hc.le E))⁻¹ = c (Subgroup.inclusion hc.le E * z *
          (Subgroup.inclusion hc.le E)⁻¹) := fun z => by
      rw [map_mul, map_mul, map_inv]
    refine ⟨ht a₀ (d * a₀) x₀ (δ * x₀) ha₀ (fun l => ?_) ?_, ?_⟩
    · rw [map_mul, MulAut.mul_apply, ha₀, hd]
      rfl
    · rw [hconj]
      congr 1
      exact Subtype.ext hEx
    · intro y b hyp hyX hb
      refine ht b b y y hb hb ?_
      rw [hconj]
      congr 1
      apply Subtype.ext
      change (E : GL κ K) * y * (E : GL κ K)⁻¹ = y
      rw [hEy y hyX hyp, mul_inv_cancel_right]
  obtain ⟨t₁, ht₁W, ht₁⟩ := exists_mem_ggAutomizer_of_conj_mem hc hψ hker hperf hAI E₁
    (fun x hx => conj_mem_inducedSub_of_shear hc hp hp2 hψ hA hAI hx₀ hx₀p hl₀ E₁ δ₁ hδ₁ hE₁x
      hE₁y hx)
  obtain ⟨t₂, ht₂W, ht₂⟩ := exists_mem_ggAutomizer_of_conj_mem hc hψ hker hperf hAI E₂
    (fun x hx => conj_mem_inducedSub_of_shear hc hp hp2 hψ hA hAI hx₀ hx₀p hl₀ E₂ δ₂ hδ₂ hE₂x
      hE₂y hx)
  obtain ⟨ht₁a, ht₁b⟩ := hshear E₁ δ₁ d₁ t₁ hd₁ hE₁x hE₁y ht₁
  obtain ⟨ht₂a, ht₂b⟩ := hshear E₂ δ₂ d₂ t₂ hd₂ hE₂x hE₂y ht₂
  have ht₁d₁ : t₁ d₁ = d₁ := ht₁b δ₁ d₁ hδ₁p hδ₁ hd₁
  have ht₁d₂ : t₁ d₂ = d₂ := ht₁b δ₂ d₂ hδ₂p hδ₂ hd₂
  have ht₂d₁ : t₂ d₁ = d₁ := ht₂b δ₁ d₁ hδ₁p hδ₁ hd₁
  have ht₂d₂ : t₂ d₂ = d₂ := ht₂b δ₂ d₂ hδ₂p hδ₂ hd₂
  have hpow : ∀ (t : MulAut ↥A) (d : ↥A), t a₀ = d * a₀ → t d = d →
      (∀ (y : N) (b : ↥A), (y : GL κ K) ^ p = 1 → c y ∈ X →
        (∀ l, c y (ψ l) = ψ ((b : MulAut L') l)) → t b = b) →
      ∀ m : ℕ, (t ^ m) a₀ = d ^ m * a₀ ∧ (t ^ m) d = d ∧
        ∀ (y : N) (b : ↥A), (y : GL κ K) ^ p = 1 → c y ∈ X →
          (∀ l, c y (ψ l) = ψ ((b : MulAut L') l)) → (t ^ m) b = b := by
    intro t d hta htd htb m
    induction m with
    | zero => exact ⟨by rw [pow_zero, pow_zero, one_mul]; rfl, rfl, fun _ _ _ _ _ => rfl⟩
    | succ m ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · rw [pow_succ, MulAut.mul_apply, hta, map_mul, ih1, ih2, ← mul_assoc, ← pow_succ']
      · rw [pow_succ, MulAut.mul_apply, htd, ih2]
      · intro y b hyp hyX hb
        rw [pow_succ, MulAut.mul_apply, htb y b hyp hyX hb, ih3 y b hyp hyX hb]
  have horder : ∀ (t : MulAut ↥A) (d : ↥A), t a₀ = d * a₀ → t d = d →
      (∀ (y : N) (b : ↥A), (y : GL κ K) ^ p = 1 → c y ∈ X →
        (∀ l, c y (ψ l) = ψ ((b : MulAut L') l)) → t b = b) → d ≠ 1 → orderOf t = p := by
    intro t d hta htd htb hd1
    apply orderOf_eq_prime
    · ext1 a
      obtain ⟨y, b, k, hyX, hyp, hb, rfl⟩ := hdecomp a
      obtain ⟨h1, -, h3⟩ := hpow t d hta htd htb p
      rw [map_mul, map_pow, h1, h3 y b hyp hyX hb, hApow d, one_mul]
      rfl
    · intro ht1
      apply hd1
      have e := hta
      rw [ht1] at e
      exact (mul_eq_right.mp e.symm)
  have hind' : ∀ i k : ℕ, d₁ ^ i * d₂ ^ k = 1 → p ∣ i ∧ p ∣ k := by
    intro i k hik
    apply hind i k
    have hv : d₁v ^ i * d₂v ^ k = 1 := by
      have := congrArg Subtype.val hik
      simpa [hd₁def, hd₂def] using this
    apply TypeA.induced_unique ψ hψ (a := d₁v ^ i * d₂v ^ k) ?_ ?_
    · intro l
      rw [MulAut.mul_apply, TypeA.induced_pow ψ hd₂ k l, TypeA.induced_pow ψ hd₁ i, MulAut.mul_apply]
    · intro l
      rw [hv]
      rfl
  have hd₁1 : d₁ ≠ 1 := fun he => by
    have := (hind' 1 0 (by rw [he, one_pow, pow_zero, one_mul])).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hd₂1 : d₂ ≠ 1 := fun he => by
    have := (hind' 0 1 (by rw [he, one_pow, pow_zero, one_mul])).2
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hord₁ := horder t₁ d₁ ht₁a ht₁d₁ ht₁b hd₁1
  have hord₂ := horder t₂ d₂ ht₂a ht₂d₂ ht₂b hd₂1
  have hcomm : t₁ * t₂ = t₂ * t₁ := by
    ext1 a
    obtain ⟨y, b, k, hyX, hyp, hb, rfl⟩ := hdecomp a
    have e₁ : t₂ (b * a₀ ^ k) = b * (d₂ * a₀) ^ k := by
      rw [map_mul, map_pow, ht₂a, ht₂b y b hyp hyX hb]
    have e₂ : t₁ (b * a₀ ^ k) = b * (d₁ * a₀) ^ k := by
      rw [map_mul, map_pow, ht₁a, ht₁b y b hyp hyX hb]
    rw [MulAut.mul_apply, MulAut.mul_apply, e₁, e₂, map_mul, map_mul, map_pow, map_pow, map_mul,
      map_mul, ht₁a, ht₂a, ht₁d₂, ht₂d₁, ht₁b y b hyp hyX hb, ht₂b y b hyp hyX hb, ← mul_assoc,
      ← mul_assoc, hAcomm d₂ d₁]
  have : Finite V := Finite.of_equiv (Additive ↥A) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) V ≤ 4 := by
    have hcard : p ^ Module.finrank (ZMod p) V = Nat.card A := by
      rw [FiniteField.pow_finrank_eq_natCard p V]
      exact Nat.card_congr ι.toEquiv.symm
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard ▸ hcardA)
  have hnot := not_prime_sq_dvd_card_closure_of_cartan_finrank_le_four hp5 ι hM hC hdim φ h α
    hpair hlin
  set H : Subgroup (MulAut ↥A) := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hH
  have hHle : H ≤ Subgroup.closure (Set.range φ) := by
    rw [← hgen]
    exact sup_le (Subgroup.zpowers_le.mpr ht₁W) (Subgroup.zpowers_le.mpr ht₂W)
  have hp1 : IsPGroup p (Subgroup.zpowers t₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord₁, pow_one])
  have hp2' : IsPGroup p (Subgroup.zpowers t₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord₂, pow_one])
  have hnorm : Subgroup.zpowers t₁ ≤ Subgroup.normalizer (Subgroup.zpowers t₂ : Set (MulAut ↥A)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left hcomm.symm k).eq)
  have hHp : IsPGroup p H := hp1.to_sup_of_normal_right' hp2' hnorm
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hHp
  have hm1 : m ≤ 1 := by
    by_contra hm2
    apply hnot
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hHle)
    rw [hm]
    exact Nat.pow_dvd_pow p (by omega)
  have hHeq : Subgroup.zpowers t₁ = H := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hm, Nat.card_zpowers, hord₁]
    calc p ^ m ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hm1
      _ = p := pow_one p
  have ht₂mem : t₂ ∈ Subgroup.zpowers t₁ := hHeq ▸ (le_sup_right : Subgroup.zpowers t₂ ≤ H)
    (Subgroup.mem_zpowers t₂)
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ht₂mem)
  have e : (t₁ ^ j) a₀ = t₂ a₀ := by rw [hj]
  rw [(hpow t₁ d₁ ht₁a ht₁d₁ ht₁b j).1, ht₂a] at e
  have hdj : d₁ ^ j = d₂ := mul_right_cancel e
  have h1 : d₁ ^ j * d₂ ^ (p - 1) = 1 := by
    rw [hdj, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hApow]
  have h2 := (hind' j (p - 1) h1).2
  have h3 : p ≤ p - 1 := Nat.le_of_dvd (by omega) h2
  omega

end TwoShears

theorem finrank_span_coroots_lt (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    [Fact p.Prime] {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) <
      Module.finrank (ZMod p) V := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have : Finite V := Finite.of_injective ι.symm ι.symm.injective
  set X := TypeA.inducedSub ψ A with hX
  have hXab : IsElemAbelian p X := TypeA.isElemAbelian_inducedSub hψ hA
  set G : Subgroup (GL κ K) := (X.comap c).map N.subtype with hG
  have hGp : TypeA.PGLTor.IsProjElem p G :=
    TypeA.PGLTor.isProjElem_comap_map_subtype hc.scalar_mem hc.map_scalar hc.ker hXab
  set lm := TypeA.PGLTor.lam hp hp2 hGp with hlm
  let cls : G →* TypeA.PGLTor.PowQuot K p := (QuotientGroup.mk' _).comp lm
  have hcls : ∀ z : G, cls z = (QuotientGroup.mk (lm z) : TypeA.PGLTor.PowQuot K p) :=
    fun _ => rfl
  let mkG : ∀ z : N, c z ∈ X → G := fun z hz => ⟨z, z, hz, rfl⟩
  have hlm_eq : ∀ (z : G) (u : Kˣ), (z : GL κ K) ^ p = GeneralLinearGroup.scalar κ u →
      lm z = u := fun z u hz => TypeA.PGLTor.scalar_injective (ι := κ)
        (by rw [← TypeA.PGLTor.lam_spec hp hp2 hGp z, hz])
  have hcls_scalar : ∀ (z : G) (u : Kˣ), (z : GL κ K) = GeneralLinearGroup.scalar κ u →
      cls z = 1 := by
    intro z u hz
    rw [hcls, hlm_eq z (u ^ p) (by rw [hz, ← map_pow]),
      TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  have hcls_pow : ∀ x : TypeA.PGLTor.PowQuot K p, x ^ p = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  have hlift : ∀ a : ↥A, ∃ B : N, ∀ l, c B (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hBX : ∀ a : ↥A, c (B a) ∈ X := fun a => TypeA.mem_inducedSub.mpr ⟨a, a.2, hB a⟩
  have hBeq : ∀ (a : ↥A) (B' : N),
      (∀ l, c B' (ψ l) = ψ ((a : MulAut L') l)) →
        ∃ u : Kˣ, (B a : GL κ K) = GeneralLinearGroup.scalar κ u * B' := fun a B' hB' =>
    hc.exists_scalar_mul_of_eq (TypeA.induced_unique ψ hψ (hB a) hB')
  let jA : ↥A →* TypeA.PGLTor.PowQuot K p :=
    { toFun := fun a => cls (mkG (B a) (hBX a))
      map_one' := by
        obtain ⟨u, hu⟩ := hBeq 1 1 fun l => by rw [map_one]; rfl
        exact hcls_scalar _ u (by rw [hu]; simp)
      map_mul' := by
        intro a b
        obtain ⟨u, hu⟩ := hBeq (a * b) (B a * B b) fun l => by
          rw [map_mul, MulAut.mul_apply, hB b, hB a]
          rfl
        have e : mkG (B (a * b)) (hBX (a * b)) =
            ⟨GeneralLinearGroup.scalar κ u, hGp.scalar_mem u⟩ *
              (mkG (B a) (hBX a) * mkG (B b) (hBX b)) := Subtype.ext hu
        change cls (mkG (B (a * b)) (hBX (a * b))) = _
        rw [e, map_mul, hcls_scalar _ u rfl, one_mul, map_mul] }
  have hjA : ∀ a : ↥A, jA a = cls (mkG (B a) (hBX a)) := fun _ => rfl
  have hinv : ∀ f ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ a, jA (f a) = jA a := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      obtain ⟨g, ⟨n, rfl⟩, -, hgf⟩ := hf
      intro a
      obtain ⟨s, hs⟩ := hc.inner (ψ n)
      set S' : N := Subgroup.inclusion hc.le s with hS'
      have hcS : c S' = MulAut.conj (ψ n) := hs.symm
      have hconj : ∀ l, c (S' * B a * S'⁻¹) (ψ l) = ψ (((f a : ↥A) : MulAut L') l) := by
        intro l
        have h1 : c (S' * B a * S'⁻¹) = c S' * c (B a) * (c S')⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [h1, hcS, TypeA.conj_induced_apply ψ (hB a) n l, ← hgf a]
      obtain ⟨u, hu⟩ := hBeq (f a) _ hconj
      have hmem : c (S' * B a * S'⁻¹) ∈ X :=
        TypeA.mem_inducedSub.mpr ⟨f a, (f a).2, hconj⟩
      have e1 : mkG (B (f a)) (hBX (f a)) =
          ⟨GeneralLinearGroup.scalar κ u, hGp.scalar_mem u⟩ * mkG _ hmem := Subtype.ext hu
      have e2 : lm (mkG _ hmem) = lm (mkG (B a) (hBX a)) := by
        apply hlm_eq
        change ((S' : GL κ K) * B a * (S' : GL κ K)⁻¹) ^ p = _
        rw [conj_pow, TypeA.PGLTor.lam_spec hp hp2 hGp (mkG (B a) (hBX a))]
        change (S' : GL κ K) * GeneralLinearGroup.scalar κ _ * (S' : GL κ K)⁻¹ = _
        rw [← (TypeA.PGLTor.commute_scalar _ (S' : GL κ K)).eq, mul_inv_cancel_right]
      rw [hjA, hjA, e1, map_mul, hcls_scalar _ u rfl, one_mul, hcls, hcls, e2]
    | one => intro a; rfl
    | mul f g _ _ hf hg =>
      intro a
      rw [MulAut.mul_apply, hf, hg]
    | inv f _ hf =>
      intro a
      have e := hf (f⁻¹ a)
      rw [MulAut.apply_inv_self] at e
      exact e.symm
  obtain ⟨a₀v, ha₀v, ha₀⟩ := TypeA.mem_inducedSub.mp hx₀
  set a₀ : ↥A := ⟨a₀v, ha₀v⟩ with ha₀def
  have hja₀ : jA a₀ ≠ 1 := by
    obtain ⟨u, hu⟩ := hBeq a₀ x₀ ha₀
    have e1 : mkG (B a₀) (hBX a₀) =
        ⟨GeneralLinearGroup.scalar κ u, hGp.scalar_mem u⟩ * mkG x₀ hx₀ := Subtype.ext hu
    rw [hjA, e1, map_mul, hcls_scalar _ u rfl, one_mul, hcls, hlm_eq _ l₀ hx₀p]
    intro hcon
    obtain ⟨μ, hμ⟩ := TypeA.PGLTor.powQuot_mk_eq_one_iff.mp hcon
    exact hl₀ μ hμ
  have hlt : Nat.card jA.ker < Nat.card A := by
    have hne : jA.ker ≠ ⊤ := fun htop => hja₀ ((MonoidHom.mem_ker).mp (htop ▸ Subgroup.mem_top a₀))
    have hlt' := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hne)
    rwa [Subgroup.card_top] at hlt'
  have hφA : ∀ i, φ i ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := fun i => by
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hhker : ∀ i, jA (Additive.toMul (ι.symm (h i))) = 1 := by
    intro i
    set b : ↥A := Additive.toMul (ι.symm (h i)) with hb
    have hii : α i (h i) = 2 := by rw [hpair i i, hC.1 i]; simp
    have hrefl : ggLin (p := p) ι (φ i) (h i) = -h i := by
      rw [hlin, hii]
      module
    have hφb : φ i b = b⁻¹ := by
      have e := ggLin_apply_ofMul (p := p) ι (φ i) b
      rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply, hrefl] at e
      apply_fun fun v => Additive.toMul (ι.symm v) at e
      rw [AddEquiv.symm_apply_apply, toMul_ofMul] at e
      rw [← e, map_neg, toMul_neg]
    have h1 := hinv (φ i) (hφA i) b
    rw [hφb, map_inv] at h1
    have h2 : jA b ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h1]
      exact inv_mul_cancel _
    have h3 := hcls_pow (jA b)
    have hord : orderOf (jA b) ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have hgcd : Nat.gcd 2 p = 1 := by
      rw [Nat.coprime_primes Nat.prime_two hp |>.mpr (Ne.symm hp2)]
    rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have hspan : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), jA (Additive.toMul (ι.symm v)) = 1 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hhker i
    | zero => rw [map_zero, toMul_zero, map_one]
    | add x y _ _ hx hy => rw [map_add, toMul_add, map_mul, hx, hy, one_mul]
    | smul a x _ hx =>
      rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, map_nsmul, toMul_nsmul, map_pow, hx,
        one_pow]
  set W := Submodule.span (ZMod p) (Set.range h)
  have hinj : Function.Injective (fun w : W =>
      (⟨Additive.toMul (ι.symm w), hspan w w.2⟩ : jA.ker)) := by
    intro w w' hww
    apply Subtype.ext
    have := congrArg (fun x : jA.ker => ι (Additive.ofMul (x : ↥A))) hww
    simpa using this
  have hcardW := Nat.card_le_card_of_injective _ hinj
  have hcardV : p ^ Module.finrank (ZMod p) V = Nat.card A := by
    rw [FiniteField.pow_finrank_eq_natCard p V]
    exact Nat.card_congr ι.toEquiv.symm
  rw [← FiniteField.pow_finrank_eq_natCard p W] at hcardW
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (hcardW.trans_lt (hlt.trans_eq hcardV.symm))

section AllShears


theorem false_of_shears (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (hshear : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      ∃ E : S, (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = y * x₀ ∧
        ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ p = 1 →
          (E : GL κ K) * z = z * E)
    [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  set X := TypeA.inducedSub ψ A with hX
  obtain ⟨a₀v, ha₀v, ha₀⟩ := TypeA.mem_inducedSub.mp hx₀
  set a₀ : ↥A := ⟨a₀v, ha₀v⟩ with ha₀def
  have hApow : ∀ b : ↥A, b ^ p = 1 := fun b => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 _ b.2)
  have hAcomm : ∀ b b' : ↥A, b * b' = b' * b := fun b b' => hA.1.is_comm.comm b b'
  set Dset : Set ↥A := {b | ∃ y : N, c y ∈ X ∧ (y : GL κ K) ^ p = 1 ∧
    ∀ l, c y (ψ l) = ψ ((b : MulAut L') l)} with hDset
  set D : Subgroup ↥A := Subgroup.closure Dset with hD
  have hdecomp : ∀ a : ↥A, ∃ b ∈ Dset, ∃ k : ℕ, a = b * a₀ ^ k := by
    intro a
    obtain ⟨Ma, hMa⟩ := hAI a a.2
    have hMaX : c Ma ∈ X := TypeA.mem_inducedSub.mpr ⟨a, a.2, hMa⟩
    obtain ⟨s, y, k, hyX, hyp, hMeq⟩ := exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ hMaX
    obtain ⟨bv, hbv, hb⟩ := TypeA.mem_inducedSub.mp hyX
    refine ⟨⟨bv, hbv⟩, ⟨y, hyX, hyp, hb⟩, k, ?_⟩
    have e : Ma = ⟨GeneralLinearGroup.scalar κ s, hc.scalar_mem s⟩ * y * x₀ ^ k :=
      Subtype.ext hMeq
    apply Subtype.ext
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hMa l, e, map_mul, map_mul, hc.map_scalar, one_mul, map_pow, MulAut.mul_apply,
      TypeA.induced_pow ψ ha₀ k l, hb]
    rfl
  have hshearT : ∀ b ∈ Dset, ∃ t ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      t a₀ = b * a₀ ∧ ∀ b' ∈ Dset, t b' = b' := by
    rintro b ⟨y, hyX, hyp, hb⟩
    obtain ⟨E, hEx, hEy⟩ := hshear y hyX hyp
    obtain ⟨t, htW, ht⟩ := exists_mem_ggAutomizer_of_conj_mem hc hψ hker hperf hAI E
      (fun x hx => conj_mem_inducedSub_of_shear hc hp hp2 hψ hA hAI hx₀ hx₀p hl₀ E y hyX hEx
        hEy hx)
    have hconj : ∀ z : N, c (Subgroup.inclusion hc.le E) * c z *
        (c (Subgroup.inclusion hc.le E))⁻¹ = c (Subgroup.inclusion hc.le E * z *
          (Subgroup.inclusion hc.le E)⁻¹) := fun z => by
      rw [map_mul, map_mul, map_inv]
    refine ⟨t, htW, ht a₀ (b * a₀) x₀ (y * x₀) ha₀ (fun l => ?_) ?_, ?_⟩
    · rw [map_mul, MulAut.mul_apply, ha₀, hb]
      rfl
    · rw [hconj]
      congr 1
      exact Subtype.ext hEx
    · rintro b' ⟨y', hy'X, hy'p, hb'⟩
      refine ht b' b' y' y' hb' hb' ?_
      rw [hconj]
      congr 1
      apply Subtype.ext
      change (E : GL κ K) * y' * (E : GL κ K)⁻¹ = y'
      rw [hEy y' hy'X hy'p, mul_inv_cancel_right]
  choose! tb htbW htba htbD using hshearT
  set T : Subgroup (MulAut ↥A) := Subgroup.closure (tb '' Dset) with hT
  have hTle : T ≤ Subgroup.closure (Set.range φ) := by
    rw [← hgen, hT, Subgroup.closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact htbW b hb
  have hfixD : ∀ t : MulAut ↥A, (∀ b' ∈ Dset, t b' = b') → ∀ e ∈ D, t e = e := by
    intro t ht e he
    induction he using Subgroup.closure_induction with
    | mem x hx => exact ht x hx
    | one => exact map_one t
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hTprop : ∀ t ∈ T, (∀ b' ∈ Dset, t b' = b') ∧ ∃ e ∈ D, t a₀ = e * a₀ := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨htbD b hb, b, Subgroup.subset_closure hb, htba b hb⟩
    | one => exact ⟨fun _ _ => rfl, 1, D.one_mem, by rw [one_mul]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxD, ex, hex, hxa⟩ := hx
      obtain ⟨hyD, ey, hey, hya⟩ := hy
      refine ⟨fun b' hb' => by rw [MulAut.mul_apply, hyD b' hb', hxD b' hb'], ey * ex,
        D.mul_mem hey hex, ?_⟩
      rw [MulAut.mul_apply, hya, map_mul, hfixD x hxD ey hey, hxa, mul_assoc]
    | inv x _ hx =>
      obtain ⟨hxD, ex, hex, hxa⟩ := hx
      refine ⟨fun b' hb' => by
        rw [MulAut.inv_def, MulEquiv.symm_apply_eq, hxD b' hb'], ex⁻¹, D.inv_mem hex, ?_⟩
      rw [MulAut.inv_def, MulEquiv.symm_apply_eq, map_mul, map_inv, hfixD x hxD ex hex, hxa,
        ← mul_assoc,
        inv_mul_cancel, one_mul]
  have hTexp : ∀ t ∈ T, t ^ p = 1 := by
    intro t ht
    obtain ⟨htD, e, he, hta⟩ := hTprop t ht
    have hpow : ∀ m : ℕ, (t ^ m) a₀ = e ^ m * a₀ := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, one_mul]; rfl
      | succ m ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfixD t htD e he, hta,
          ← mul_assoc, ← pow_succ]
    have hpowD : ∀ m : ℕ, ∀ b' ∈ Dset, (t ^ m) b' = b' := by
      intro m
      induction m with
      | zero => intro b' _; rfl
      | succ m ih => intro b' hb'; rw [pow_succ', MulAut.mul_apply, ih b' hb', htD b' hb']
    ext1 a
    obtain ⟨b, hb, k, rfl⟩ := hdecomp a
    rw [map_mul, map_pow, hpowD p b hb, hpow p, hApow e, one_mul]
    rfl
  have hTp : IsPGroup p T := by
    intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hTexp g g.2)⟩
  have hsurj : ∀ e ∈ D, ∃ t ∈ T, t a₀ = e * a₀ := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem x hx => exact ⟨tb x, Subgroup.subset_closure ⟨x, hx, rfl⟩, htba x hx⟩
    | one => exact ⟨1, T.one_mem, by rw [one_mul]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨tx, htx, htxa⟩ := hx
      obtain ⟨ty, hty, htya⟩ := hy
      refine ⟨ty * tx, T.mul_mem hty htx, ?_⟩
      have hyD : ∀ b' ∈ Dset, ty b' = b' := (hTprop ty hty).1
      rw [MulAut.mul_apply, htxa, map_mul, hfixD ty hyD x (by assumption), htya, ← mul_assoc]
    | inv x hxD hx =>
      obtain ⟨tx, htx, htxa⟩ := hx
      refine ⟨tx⁻¹, T.inv_mem htx, ?_⟩
      have hxD' : ∀ b' ∈ Dset, tx b' = b' := (hTprop tx htx).1
      rw [MulAut.inv_def, MulEquiv.symm_apply_eq, map_mul, map_inv, hfixD tx hxD' x hxD, htxa,
        ← mul_assoc, inv_mul_cancel, one_mul]
  have hcardD : Nat.card D ≤ Nat.card T := by
    let F : ↥T → ↥D := fun t => ⟨t.1 a₀ * a₀⁻¹, by
      obtain ⟨-, e, he, hta⟩ := hTprop t.1 t.2
      rw [hta, mul_inv_cancel_right]
      exact he⟩
    apply Nat.card_le_card_of_surjective F
    rintro ⟨e, he⟩
    obtain ⟨t, ht, hta⟩ := hsurj e he
    exact ⟨⟨t, ht⟩, Subtype.ext (by
      change t a₀ * a₀⁻¹ = e
      rw [hta, mul_inv_cancel_right])⟩
  have hcardA : Nat.card A ≤ Nat.card D * p := by
    let G : ↥D × Fin p → ↥A := fun q => (q.1 : ↥A) * a₀ ^ (q.2 : ℕ)
    have hG : Function.Surjective G := by
      intro a
      obtain ⟨b, hb, k, rfl⟩ := hdecomp a
      refine ⟨(⟨b, Subgroup.subset_closure hb⟩, ⟨k % p, Nat.mod_lt _ hp.pos⟩), ?_⟩
      change b * a₀ ^ (k % p) = b * a₀ ^ k
      rw [← pow_eq_pow_mod k (hApow a₀)]
    have := Nat.card_le_card_of_surjective G hG
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this
  have : Finite V := Finite.of_equiv (Additive ↥A) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  set a := Module.finrank (ZMod p) V with ha
  have hcardV : p ^ a = Nat.card A := by
    rw [ha, FiniteField.pow_finrank_eq_natCard p V]
    exact Nat.card_congr ι.toEquiv.symm
  have ha3 : 3 ≤ a := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcardV ▸ h3)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hTp
  have hja : a - 1 ≤ j := by
    have h1 : p ^ a ≤ p ^ j * p := by
      rw [hcardV, ← hj]
      exact hcardA.trans (Nat.mul_le_mul_right _ hcardD)
    rw [← pow_succ] at h1
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  have hspan := finrank_span_coroots_lt hc hp hp2 hψ hA hAI hx₀ hx₀p hl₀ hC ι φ h α hpair hlin hgen
  apply not_prime_pow_dvd_card_closure_of_span_lt hp2 ι hM hC ha3 φ h α hpair hlin hspan
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hTle)
  rw [hj]
  exact Nat.pow_dvd_pow p hja

end AllShears

end CFSG.StandardType.QuotMove
