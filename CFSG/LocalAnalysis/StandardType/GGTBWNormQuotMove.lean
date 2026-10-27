module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormPairing
public import CFSG.LocalAnalysis.StandardType.GGPGLCommForm
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.StandardType.QuotMove

open CFSG CFSG.Assembly Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K] {R : Type} [Group R]
  {N : Subgroup (GL κ K)} (c : N →* MulAut R)

structure IsScalarQuot (S : Subgroup (GL κ K)) : Prop where
  scalar_mem : ∀ u : Kˣ, GeneralLinearGroup.scalar κ u ∈ N
  map_scalar : ∀ u : Kˣ, c ⟨GeneralLinearGroup.scalar κ u, scalar_mem u⟩ = 1
  ker : ∀ M : N, c M = 1 → ∃ u : Kˣ, (M : GL κ K) = GeneralLinearGroup.scalar κ u
  le : S ≤ N
  inner : ∀ r : R, ∃ s : S, MulAut.conj r = c (Subgroup.inclusion le s)
  inner' : ∀ s : S, ∃ r : R, MulAut.conj r = c (Subgroup.inclusion le s)

variable {c} {S : Subgroup (GL κ K)}

theorem IsScalarQuot.exists_scalar_mul_of_eq (hc : IsScalarQuot c S) {M M' : N} (h : c M = c M') :
    ∃ u : Kˣ, (M : GL κ K) = GeneralLinearGroup.scalar κ u * M' := by
  have h1 : c (M * M'⁻¹) = 1 := by rw [map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨u, hu⟩ := hc.ker (M * M'⁻¹) h1
  refine ⟨u, ?_⟩
  have h2 : ((M * M'⁻¹ : N) : GL κ K) = (M : GL κ K) * (M' : GL κ K)⁻¹ := rfl
  rw [h2] at hu
  calc (M : GL κ K) = (M : GL κ K) * (M' : GL κ K)⁻¹ * M' := by group
    _ = GeneralLinearGroup.scalar κ u * M' := by rw [hu]

variable {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} {p : ℕ}

theorem commForm_inner_invariant (hc : IsScalarQuot c S) [Nonempty κ]
    (hψ : Function.Surjective ψ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (B : ↥A → N)
    (hB : ∀ a l, c (B a) (ψ l) = ψ ((a : MulAut L') l))
    (hBmul : ∀ a b : ↥A, ∃ u : Kˣ,
      (B (a * b) : GL κ K) = GeneralLinearGroup.scalar κ u * (B a * B b))
    (hcommA : ∀ a b : ↥A, a * b = b * a) {ω : LinearMap.BilinForm (ZMod p) V}
    (hω : ∀ a b : ↥A, ζ ^ (ω (ι (Additive.ofMul a)) (ι (Additive.ofMul b))).val =
      CommForm.scomm (B a : GL κ K) (B b)) :
    ∀ f ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ u v,
      ω (ggLin (p := p) ι f u) (ggLin (p := p) ι f v) = ω u v := by
  intro f hf
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    obtain ⟨g, ⟨n, rfl⟩, -, hgf⟩ := hf
    obtain ⟨s, hs⟩ := hc.inner (ψ n)
    set S' : N := Subgroup.inclusion hc.le s with hS'
    refine CommForm.commForm_ggLin hζ hBmul hcommA ι hω (S := (S' : GL κ K)) fun a => ?_
    refine hc.exists_scalar_mul_of_eq (M := B (f a)) (M' := S' * B a * S'⁻¹) ?_
    apply TypeA.induced_unique ψ hψ (a := ((f a : ↥A) : MulAut L'))
    · exact hB (f a)
    · intro l
      have hcn : c S' = MulAut.conj (ψ n) := hs.symm
      have h1 : c (S' * B a * S'⁻¹) = c S' * c (B a) * (c S')⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [h1, hcn, TypeA.conj_induced_apply ψ (hB a) n l, ← hgf a]
  | one => intro u v; rw [map_one]; rfl
  | mul f g _ _ hf hg =>
    intro u v
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hf, hg]
  | inv f _ hf =>
    intro u v
    have e := hf (ggLin (p := p) ι f⁻¹ u) (ggLin (p := p) ι f⁻¹ v)
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel,
      map_one] at e
    exact e.symm

theorem exists_inner_of_permuting_lifts (hc : IsScalarQuot c S) [Finite L']
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (B : A → N)
    (hB : ∀ a l, c (B a) (ψ l) = ψ ((a : MulAut L') l))
    (E : S) (hE : ∀ a : A, ∃ b : A, ∃ u : Kˣ,
      (E : GL κ K) * B a * (E : GL κ K)⁻¹ = GeneralLinearGroup.scalar κ u * B b) :
    ∃ n : L', MulAut.conj (ψ n) = c (Subgroup.inclusion hc.le E) ∧
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
      ∀ (a b : A) (u : Kˣ),
        (E : GL κ K) * B a * (E : GL κ K)⁻¹ = GeneralLinearGroup.scalar κ u * B b →
        MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ = (b : MulAut L') := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  obtain ⟨r₀, hr₀⟩ := hc.inner' E
  obtain ⟨n, hψn⟩ := hψ r₀
  have hcn : MulAut.conj (ψ n) = c (Subgroup.inclusion hc.le E) := by
    rw [hψn]; exact hr₀
  have hact : ∀ (a b : ↥A) (u : Kˣ), (E : GL κ K) * B a * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ u * B b →
      MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ = (b : MulAut L') := by
    intro a b u hu
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← TypeA.conj_induced_apply ψ (hB a) n l, hcn]
    have h1 : c (Subgroup.inclusion hc.le E) * c (B a) *
        (c (Subgroup.inclusion hc.le E))⁻¹ =
        c (Subgroup.inclusion hc.le E * B a * (Subgroup.inclusion hc.le E)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    have h2 : (Subgroup.inclusion hc.le E * B a * (Subgroup.inclusion hc.le E)⁻¹ : N) =
        ⟨GeneralLinearGroup.scalar κ u, hc.scalar_mem u⟩ * B b := by
      apply Subtype.ext
      show (Subgroup.inclusion hc.le E : GL κ K) * (B a : GL κ K) *
          ((Subgroup.inclusion hc.le E : GL κ K))⁻¹ =
        GeneralLinearGroup.scalar κ u * (B b : GL κ K)
      exact hu
    rw [h2, map_mul, hc.map_scalar, one_mul]
    exact hB b l
  have hnN : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj n)).injective).ge
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, u, hu⟩ := hE ⟨a, ha⟩
    change MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A
    rw [hact ⟨a, ha⟩ b u hu]
    exact b.2
  exact ⟨n, hcn, hnN, hact⟩


theorem exists_inner_of_normalizes_inducedSub (hc : IsScalarQuot c S) [Finite L']
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    (E : S) (hEN : ∀ x ∈ TypeA.inducedSub ψ A,
      c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
        TypeA.inducedSub ψ A) :
    ∃ n : L', MulAut.conj (ψ n) = c (Subgroup.inclusion hc.le E) ∧
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  have hlift : ∀ a : A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hE : ∀ a : A, ∃ b : A, ∃ u : Kˣ,
      (E : GL κ K) * B a * (E : GL κ K)⁻¹ = GeneralLinearGroup.scalar κ u * B b := by
    intro a
    have ha : c (B a) ∈ TypeA.inducedSub ψ A := ⟨a, a.2, hB a⟩
    obtain ⟨b, hb, hcb⟩ := TypeA.mem_inducedSub.mp (hEN _ ha)
    have heq : c (Subgroup.inclusion hc.le E * B a * (Subgroup.inclusion hc.le E)⁻¹) =
        c (B ⟨b, hb⟩) := by
      apply TypeA.induced_unique ψ hψ
      · intro l
        rw [map_mul, map_mul, map_inv]
        exact hcb l
      · exact hB ⟨b, hb⟩
    obtain ⟨u, hu⟩ := hc.exists_scalar_mul_of_eq heq
    exact ⟨⟨b, hb⟩, u, hu⟩
  obtain ⟨n, hcn, hnN, _⟩ := exists_inner_of_permuting_lifts hc hψ hker hperf B hB E hE
  exact ⟨n, hcn, hnN⟩


theorem false_of_move (hc : IsScalarQuot c S) [Finite L'] (hp2 : p ≠ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    [Fact p.Prime] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdiag : ∀ i, α i (h i) = 2) (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    (B : ↥A → N) (hB : ∀ a l, c (B a) (ψ l) = ψ ((a : MulAut L') l))
    (ω : LinearMap.BilinForm (ZMod p) V) (halt : ∀ v, ω v v = 0)
    (hW : ∀ f ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ u v,
      ω (ggLin (p := p) ι f u) (ggLin (p := p) ι f v) = ω u v)
    (E : S)
    (hE : ∀ a : ↥A, ∃ b : ↥A, ∃ u : Kˣ, (E : GL κ K) * B a * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ u * B b)
    {a₁ b₁ : ↥A} {u₁ : Kˣ}
    (hab : (E : GL κ K) * B a₁ * (E : GL κ K)⁻¹ = GeneralLinearGroup.scalar κ u₁ * B b₁)
    {w : V} (hmove : ω (ι (Additive.ofMul b₁) - ι (Additive.ofMul a₁)) w ≠ 0) : False := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  obtain ⟨n, _hcn, hnN, hact⟩ := exists_inner_of_permuting_lifts hc hψ hker hperf B hB E hE
  have htW : ggConjAut A hnN ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN
  have hta : ggConjAut A hnN a₁ = b₁ :=
    Subtype.ext (by rw [ggConjAut_apply, hact a₁ b₁ u₁ hab])
  refine false_of_pairing_of_moves hp2 ι φ h α hdiag hlin ω halt hW hgen htW
    (v := ι (Additive.ofMul a₁)) (u := w) ?_
  rwa [ggLin_apply_ofMul, hta]

theorem false_of_normalizing_move (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ y₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) (hy₀ : c y₀ ∈ TypeA.inducedSub ψ A)
    {u₀ : Kˣ} (hu₀ : (x₀ : GL κ K) * y₀ = GeneralLinearGroup.scalar κ u₀ * (y₀ * x₀))
    (hu₀1 : u₀ ≠ 1) (E : S)
    (hEN : ∀ x ∈ TypeA.inducedSub ψ A,
      c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
        TypeA.inducedSub ψ A)
    {k : ℕ} (hk : ¬ p ∣ k) {uE : Kˣ}
    (hEy : (E : GL κ K) * y₀ * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ uE * ((y₀ : GL κ K) * (x₀ : GL κ K) ^ k))
    [Fact p.Prime] {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  set ζ : Kˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
    exact hζ₀
  have hlift : ∀ a : ↥A, ∃ B : N, ∀ l, c B (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hBeq : ∀ (a : ↥A) (B' : N),
      (∀ l, c B' (ψ l) = ψ ((a : MulAut L') l)) →
        ∃ u : Kˣ, B a = GeneralLinearGroup.scalar κ u * B' := fun a B' hB' =>
    hc.exists_scalar_mul_of_eq (TypeA.induced_unique ψ hψ (hB a) hB')
  have hBmul : ∀ a b : ↥A, ∃ u : Kˣ,
      (B (a * b) : GL κ K) = GeneralLinearGroup.scalar κ u * (B a * B b) := by
    intro a b
    refine hBeq (a * b) (B a * B b) fun l => ?_
    rw [map_mul, MulAut.mul_apply, hB b, hB a]
    rfl
  have hcommA : ∀ a b : ↥A, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2)
  have hexpA : ∀ a : ↥A, a ^ p = 1 := fun a =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hA.2 a a.2)
  obtain ⟨ω, hω, halt⟩ := CommForm.exists_commForm (B := fun a => (B a : GL κ K))
    hζ hBmul hcommA hexpA ι
  have hW := commForm_inner_invariant hc hψ ι hζ B hB hBmul hcommA hω
  obtain ⟨ax, haxA, hax⟩ := hx₀
  obtain ⟨ay, hayA, hay⟩ := hy₀
  set ax' : ↥A := ⟨ax, haxA⟩ with hax'
  set ay' : ↥A := ⟨ay, hayA⟩ with hay'
  obtain ⟨ux, hux⟩ := hBeq ax' x₀ hax
  obtain ⟨uy, huy⟩ := hBeq ay' y₀ hay
  have huxGL : (B ax' : GL κ K) = GeneralLinearGroup.scalar κ ux * (x₀ : GL κ K) := hux
  have huyGL : (B ay' : GL κ K) = GeneralLinearGroup.scalar κ uy * (y₀ : GL κ K) := huy
  have hE : ∀ a : ↥A, ∃ b : ↥A, ∃ u : Kˣ, (E : GL κ K) * B a * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ u * B b := by
    intro a
    have hmem : c (Subgroup.inclusion hc.le E * B a * (Subgroup.inclusion hc.le E)⁻¹) ∈
        TypeA.inducedSub ψ A := by
      have h1 : c (Subgroup.inclusion hc.le E * B a * (Subgroup.inclusion hc.le E)⁻¹) =
          c (Subgroup.inclusion hc.le E) * c (B a) * (c (Subgroup.inclusion hc.le E))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [h1]
      exact hEN _ ⟨a, a.2, hB a⟩
    obtain ⟨b, hb, hbind⟩ := hmem
    obtain ⟨u, hu⟩ := hBeq ⟨b, hb⟩ _ hbind
    refine ⟨⟨b, hb⟩, u⁻¹, ?_⟩
    rw [hu, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rfl
  obtain ⟨u₁, hu₁⟩ := hBeq (ay' * ax' ^ k) (y₀ * x₀ ^ k) fun l => by
    rw [map_mul, map_pow, MulAut.mul_apply, TypeA.induced_pow ψ hax k, hay]
    rfl
  have hu₁GL : (B (ay' * ax' ^ k) : GL κ K) =
      GeneralLinearGroup.scalar κ u₁ * ((y₀ : GL κ K) * (x₀ : GL κ K) ^ k) := by
    simpa using hu₁
  have hab : (E : GL κ K) * B ay' * (E : GL κ K)⁻¹ =
      GeneralLinearGroup.scalar κ (uy * uE * u₁⁻¹) * B (ay' * ax' ^ k) := by
    have e1 : (E : GL κ K) * B ay' * (E : GL κ K)⁻¹ =
        GeneralLinearGroup.scalar κ uy * ((E : GL κ K) * y₀ * (E : GL κ K)⁻¹) := by
      rw [huyGL, ← mul_assoc (E : GL κ K), ← (TypeA.PGLTor.commute_scalar uy (E : GL κ K)).eq]
      simp only [mul_assoc]
    rw [e1, hEy, hu₁GL, ← mul_assoc (GeneralLinearGroup.scalar κ (uy * uE * u₁⁻¹)), ← map_mul,
      mul_assoc (uy * uE), inv_mul_cancel, mul_one, map_mul, mul_assoc]
  have hne0 : ω (ι (Additive.ofMul ax')) (ι (Additive.ofMul ay')) ≠ 0 := by
    intro h0
    have e := hω ax' ay'
    rw [h0, ZMod.val_zero, pow_zero] at e
    apply hu₀1
    rw [e]
    symm
    apply CommForm.scomm_eq
    rw [huxGL, huyGL]
    have hsc := TypeA.PGLTor.scalar_mul_comm (ι := κ) (K := K)
    calc (GeneralLinearGroup.scalar κ ux * (x₀ : GL κ K)) *
          (GeneralLinearGroup.scalar κ uy * (y₀ : GL κ K))
        = GeneralLinearGroup.scalar κ (ux * uy * u₀) *
            ((y₀ : GL κ K) * (x₀ : GL κ K)) := by
          rw [mul_assoc, ← mul_assoc (x₀ : GL κ K), ← hsc uy (x₀ : GL κ K), mul_assoc, hu₀]
          simp only [← mul_assoc, ← map_mul (GeneralLinearGroup.scalar κ)]
      _ = GeneralLinearGroup.scalar κ u₀ * (GeneralLinearGroup.scalar κ uy * (y₀ : GL κ K) *
            (GeneralLinearGroup.scalar κ ux * (x₀ : GL κ K))) := by
          rw [mul_assoc (GeneralLinearGroup.scalar κ uy), ← mul_assoc (y₀ : GL κ K),
            ← hsc ux (y₀ : GL κ K)]
          simp only [← mul_assoc, ← map_mul (GeneralLinearGroup.scalar κ)]
          rw [mul_comm ux uy, mul_comm (uy * ux) u₀, ← mul_assoc]
  have hk0 : (k : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine false_of_move hc hp2 hψ hker hperf ι φ h α hdiag hlin hgen B hB ω halt hW E hE hab
    (w := ι (Additive.ofMul ay')) ?_
  rw [ofMul_mul, map_add, add_sub_cancel_left, ofMul_pow, map_nsmul,
    ← Nat.cast_smul_eq_nsmul (ZMod p), LinearMap.BilinForm.smul_left]
  exact mul_ne_zero hk0 hne0

omit [Fintype κ] [DecidableEq κ] in
theorem exists_pow_eq_units [NeZero p] {ζ u : Kˣ} (hζ : IsPrimitiveRoot ζ p) (hu : u ^ p = 1) :
    ∃ m < p, ζ ^ m = u := by
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have huK : (u : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨m, hm, e⟩ := hζK.eq_pow_of_pow_eq_one huK
  exact ⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val, e])⟩

theorem conj_mem_inducedSub_of_phase (hc : IsScalarQuot c S) [Nonempty κ] (hp : p.Prime)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) (hx₀p : (x₀ : GL κ K) ^ p = 1) (E : N)
    (hE : ∀ (z : GL κ K) (m : ℕ),
      (x₀ : GL κ K) * z = GeneralLinearGroup.scalar κ (ζ ^ m) * (z * x₀) →
        ∃ u : Kˣ, (E : GL κ K) * z * (E : GL κ K)⁻¹ =
          GeneralLinearGroup.scalar κ u * (z * (x₀ : GL κ K) ^ m)) :
    ∀ z ∈ TypeA.inducedSub ψ A, c E * z * (c E)⁻¹ ∈ TypeA.inducedSub ψ A := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hXab := TypeA.isElemAbelian_inducedSub hψ hA
  intro z hz
  obtain ⟨a, ha, hza⟩ := TypeA.mem_inducedSub.mp hz
  obtain ⟨M, hM⟩ := hAI a ha
  have hMz : c M = z := TypeA.induced_unique ψ hψ hM hza
  have hcomm : c (x₀ * M * x₀⁻¹ * M⁻¹) = 1 := by
    have h1 : c x₀ * z = z * c x₀ := TableB.IsElemAbelian.comm hXab hx₀ hz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hMz, h1, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨w, hw⟩ := hc.ker _ hcomm
  have hwM : (x₀ : GL κ K) * M = GeneralLinearGroup.scalar κ w * (M * x₀) := by
    have e : ((x₀ * M * x₀⁻¹ * M⁻¹ : N) : GL κ K) = (x₀ : GL κ K) * M * (x₀ : GL κ K)⁻¹ *
        (M : GL κ K)⁻¹ := rfl
    rw [e] at hw
    rw [← hw]
    group
  have hwp : w ^ p = 1 := by
    have hMx : (M : GL κ K) * x₀ = GeneralLinearGroup.scalar κ w⁻¹ * (x₀ * M) := by
      rw [hwM, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have e := TypeA.PGLTor.mul_pow_eq_of_mul_eq (TypeA.PGLTor.commute_scalar w⁻¹ _) hMx p
    rw [hx₀p, mul_one, one_mul, ← map_pow] at e
    have e2 : GeneralLinearGroup.scalar κ (w⁻¹ ^ p) = 1 := by
      have := congrArg (· * (M : GL κ K)⁻¹) e
      simpa using this.symm
    have e3 : w⁻¹ ^ p = 1 := TypeA.PGLTor.scalar_injective (by rw [e2, map_one])
    rw [inv_pow] at e3
    exact inv_eq_one.mp e3
  obtain ⟨m, -, hm⟩ := exists_pow_eq_units hζ hwp
  obtain ⟨u, hu⟩ := hE M m (by rw [hm]; exact hwM)
  have hEM : E * M * E⁻¹ = ⟨GeneralLinearGroup.scalar κ u, hc.scalar_mem u⟩ * (M * x₀ ^ m) := by
    apply Subtype.ext
    simpa using hu
  have h2 : c E * z * (c E)⁻¹ = z * c x₀ ^ m := by
    rw [← hMz, ← map_inv, ← map_mul, ← map_mul, hEM, map_mul, hc.map_scalar, one_mul, map_mul,
      map_pow]
  rw [h2]
  exact (TypeA.inducedSub ψ A).mul_mem hz ((TypeA.inducedSub ψ A).pow_mem hx₀ _)

theorem isScalarQuot_PSL {d : ℕ} [Finite K] (hd : 0 < d) :
    IsScalarQuot ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K).comp
      (⊤ : Subgroup (GL (Fin d) K)).subtype)
      (Matrix.SpecialLinearGroup.toGL : _ →* GL (Fin d) K).range := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ => Subgroup.mem_top _
  · exact fun u => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar u
  · intro M hM
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hM
    obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar hd hc
    exact ⟨u, hu⟩
  · exact le_top
  · intro r
    obtain ⟨g, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective d K r
    exact ⟨⟨SpecialLinearGroup.toGL g, ⟨g, rfl⟩⟩,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_toGL g).symm⟩
  · rintro ⟨g, hg⟩
    obtain ⟨gs, rfl⟩ := hg
    exact ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d K gs,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_toGL gs).symm⟩

end CFSG.StandardType.QuotMove
