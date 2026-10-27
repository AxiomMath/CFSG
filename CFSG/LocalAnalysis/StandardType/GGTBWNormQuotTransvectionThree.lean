module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection
public import CFSG.LocalAnalysis.StandardType.GGTWHLNormalizer
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix Polynomial

section BlockInvariant

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem roots_charpoly_of_conjMatrix_eq_diagonal (A x : GL ι K) {w : ι → K}
    (h : conjMatrix A x = diagonal w) :
    (x : Matrix ι ι K).charpoly.roots = Finset.univ.val.map w := by
  have h1 : (x : Matrix ι ι K).charpoly = (diagonal w).charpoly := by
    rw [← h, conjMatrix, Matrix.coe_units_inv]
    exact (Matrix.charpoly_units_conj A _).symm
  rw [h1, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun i => X - C (w i)) =
      (Finset.univ.val.map w).map (fun a => X - C a) by rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

theorem map_univ_eq_nsmul_of_block {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (block : ι → β) (hsize : ∀ b, Fintype.card {i // block i = b} = n) (r : β → ι)
    (hr : ∀ b, block (r b) = b) (f : ι → K) (hf : ∀ i j, block i = block j → f i = f j) :
    Finset.univ.val.map f = n • Finset.univ.val.map (fun b => f (r b)) := by
  have hfr : f = (fun b => f (r b)) ∘ block := funext fun i => hf i (r (block i)) (hr _).symm
  have hblock : Finset.univ.val.map block = n • (Finset.univ : Finset β).val := by
    ext b
    rw [Multiset.count_nsmul, Multiset.count_univ, mul_one, Multiset.count_map, ← hsize b,
      Fintype.card_subtype]
    change (Finset.univ.filter fun a => b = block a).card = _
    simp_rw [eq_comm]
  calc Finset.univ.val.map f = Finset.univ.val.map ((fun b => f (r b)) ∘ block) := by rw [← hfr]
    _ = (Finset.univ.val.map block).map (fun b => f (r b)) := by rw [Multiset.map_map]
    _ = n • Finset.univ.val.map (fun b => f (r b)) := by rw [hblock, Multiset.map_nsmul]

theorem exists_threeBlock_invariant [Finite K] [Nonempty ι] (hpK : 3 ∣ Nat.card K - 1)
    {G : Subgroup (GL ι K)} (hG : IsProjElem 3 G)
    (hcent : ∀ h ∈ G, h ^ 3 = 1 → ∀ x ∈ G, x * h = h * x) (hNT : ¬ IsToral G)
    (hdim : Fintype.card ι = 9) (hcard : 3 ^ 3 * (Nat.card K - 1) ≤ Nat.card G) :
    ∃ σ : GL ι K → K,
      (∀ z ∈ G, ∀ z' ∈ G, z ^ 3 = 1 → z' ^ 3 = 1 → σ (z * z') = σ z * σ z') ∧
      (∀ u : Kˣ, u ^ 3 = 1 → ∀ z : GL ι K, σ (GeneralLinearGroup.scalar ι u * z) = σ z) ∧
      (∀ z ∈ G, z ^ 3 = 1 → σ z ^ 3 = 1) ∧
      (∀ s z : GL ι K, z ∈ G → z ^ 3 = 1 → s * z * s⁻¹ ∈ G → σ (s * z * s⁻¹) = σ z) ∧
      (∀ ζ : K, ζ ≠ 1 → ∀ z ∈ G, z ^ 3 = 1 → ∀ (Q : GL ι K) (w : ι → K),
        ((Q⁻¹ * z * Q : GL ι K) : Matrix ι ι K) = diagonal w → (∀ j, w j = 1 ∨ w j = ζ) →
          (∃ j, w j = 1) → (∃ j, w j = ζ) → σ z ≠ 1) := by
  classical
  obtain ⟨D, hn, hsize⟩ := exists_three_blockModel_of_central_of_not_toral Nat.prime_three
    (by norm_num) hpK hG hcent hNT (by rw [hdim]) hcard
  choose r hr using D.block_surjective
  set dg : GL ι K → ι → K := fun z i => conjMatrix D.basis z i i with hdg
  have hdiag : ∀ z ∈ G, z ^ 3 = 1 → conjMatrix D.basis z = diagonal (dg z) ∧
      ∀ i j, D.block i = D.block j → dg z i = dg z j := by
    intro z hz hz3
    have hk : z ∈ D.kernel := (D.kernel_mem_iff z hz).mpr ⟨1, by rw [hz3, one_pow, map_one]⟩
    obtain ⟨δ, hδ, hδc, -⟩ := D.kernel_diagonal z hk
    have e : dg z = δ := funext fun i => by
      change conjMatrix D.basis z i i = δ i
      rw [hδ, diagonal_apply_eq]
    rw [e]
    exact ⟨hδ, hδc⟩
  have hcube : ∀ z ∈ G, z ^ 3 = 1 → ∀ i, dg z i ^ 3 = 1 := by
    intro z hz hz3 i
    have e := conjMatrix_pow D.basis z 3
    rw [hz3, conjMatrix_one, (hdiag z hz hz3).1, diagonal_pow] at e
    have e2 := congrFun (congrFun e i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply] at e2
    exact e2.symm
  set bv : GL ι K → Multiset K := fun z => Finset.univ.val.map fun b => dg z (r b) with hbv
  have hroots : ∀ z ∈ G, z ^ 3 = 1 → (z : Matrix ι ι K).charpoly.roots = 3 • bv z := by
    intro z hz hz3
    rw [roots_charpoly_of_conjMatrix_eq_diagonal D.basis z (hdiag z hz hz3).1]
    exact map_univ_eq_nsmul_of_block D.block hsize r hr _ (hdiag z hz hz3).2
  have hcancel : ∀ s t : Multiset K, 3 • s = 3 • t → s = t := by
    intro s t hst
    ext a
    have e := congrArg (Multiset.count a) hst
    rw [Multiset.count_nsmul, Multiset.count_nsmul] at e
    omega
  set σ : GL ι K → K := fun z => ∏ b, dg z (r b) with hσ
  have hσbv : ∀ z, σ z = (bv z).prod := fun z => Finset.prod_eq_multiset_prod _ _
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz z' hz' hz3 hz'3
    have e : ∀ i, dg (z * z') i = dg z i * dg z' i := by
      intro i
      change conjMatrix D.basis (z * z') i i = _
      rw [conjMatrix_mul, (hdiag z hz hz3).1, (hdiag z' hz' hz'3).1, diagonal_mul_diagonal,
        diagonal_apply_eq]
    simp only [hσ, e, Finset.prod_mul_distrib]
  ·
    intro u hu z
    have e : ∀ i, dg (GeneralLinearGroup.scalar ι u * z) i = (u : K) * dg z i := by
      intro i
      change conjMatrix D.basis (GeneralLinearGroup.scalar ι u * z) i i = _
      rw [conjMatrix_scalar_mul, Matrix.smul_apply, smul_eq_mul]
    simp only [hσ, e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hn]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one, one_mul]
  ·
    intro z hz hz3
    simp only [hσ, ← Finset.prod_pow, hcube z hz hz3, Finset.prod_const_one]
  ·
    intro s z hz hz3 hsz
    have hsz3 : (s * z * s⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have e : ((s * z * s⁻¹ : GL ι K) : Matrix ι ι K).charpoly = (z : Matrix ι ι K).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj s _
    have e2 := hroots _ hsz hsz3
    rw [e, hroots z hz hz3] at e2
    rw [hσbv, hσbv, hcancel _ _ e2]
  ·
    intro ζ hζ z hz hz3 Q w hQ hw h1 hζw
    have hQ' : conjMatrix Q⁻¹ z = diagonal w := by
      rw [conjMatrix, inv_inv, ← hQ, Units.val_mul, Units.val_mul]
    have e := roots_charpoly_of_conjMatrix_eq_diagonal Q⁻¹ z hQ'
    rw [hroots z hz hz3] at e
    have hmem : ∀ v, v ∈ bv z ↔ ∃ j, w j = v := by
      intro v
      rw [← Multiset.mem_nsmul_of_ne_zero (n := 3) (by norm_num), e, Multiset.mem_map]
      simp
    have hval : ∀ b, dg z (r b) = 1 ∨ dg z (r b) = ζ := by
      intro b
      obtain ⟨j, hj⟩ := (hmem (dg z (r b))).mp
        (Multiset.mem_map.mpr ⟨b, Finset.mem_univ_val _, rfl⟩)
      rw [← hj]
      exact hw j
    obtain ⟨b₁, hb₁⟩ : ∃ b, dg z (r b) = ζ := by
      obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp ((hmem ζ).mpr hζw)
      exact ⟨b, hb⟩
    obtain ⟨b₂, hb₂⟩ : ∃ b, dg z (r b) = 1 := by
      obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp ((hmem 1).mpr h1)
      exact ⟨b, hb⟩
    have hζ3 : ζ ^ 3 = 1 := hb₁ ▸ hcube z hz hz3 (r b₁)
    have e3 : σ z = ζ ^ (Finset.univ.filter fun b => dg z (r b) = ζ).card := by
      show ∏ b, dg z (r b) = _
      rw [← Finset.prod_const, Finset.prod_filter]
      refine Finset.prod_congr rfl fun b _ => ?_
      rcases hval b with h | h
      · rw [h, if_neg (Ne.symm hζ)]
      · rw [h, if_pos rfl]
    have hk1 : 0 < (Finset.univ.filter fun b => dg z (r b) = ζ).card :=
      Finset.card_pos.mpr ⟨b₁, by simp [hb₁]⟩
    have hk2 : (Finset.univ.filter fun b => dg z (r b) = ζ).card < 3 := by
      have hlt : (Finset.univ.filter fun b => dg z (r b) = ζ) ⊂ Finset.univ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun he => ?_⟩
        have hb₂m : b₂ ∈ Finset.univ.filter fun b => dg z (r b) = ζ := by
          rw [he]; exact Finset.mem_univ _
        rw [Finset.mem_filter, hb₂] at hb₂m
        exact hζ hb₂m.2.symm
      have := Finset.card_lt_card hlt
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this.trans_eq hn
    rw [e3]
    obtain ⟨k, hk⟩ : ∃ k, (Finset.univ.filter fun b => dg z (r b) = ζ).card = k := ⟨_, rfl⟩
    rw [hk] at hk1 hk2 ⊢
    interval_cases k
    · rwa [pow_one]
    · intro h2
      apply hζ
      calc ζ = ζ ^ 2 * ζ := by rw [h2, one_mul]
        _ = ζ ^ 3 := by ring
        _ = 1 := hζ3

end BlockInvariant

end CFSG.StandardType.TypeA.PGLTor

namespace CFSG.StandardType.QuotMove

open CFSG CFSG.Assembly Matrix

section TransvectionThree

variable {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K] {R : Type} [Group R]
  {N : Subgroup (GL κ K)} {c : N →* MulAut R} {S : Subgroup (GL κ K)}
  {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}

theorem false_of_transvection_three (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A) (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ 3 = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ 3 ≠ l₀)
    (E : S)
    (hEN : ∀ x ∈ TypeA.inducedSub ψ A,
      c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
        TypeA.inducedSub ψ A)
    {δ : N} (hδ : c δ ∈ TypeA.inducedSub ψ A) (hδ3 : (δ : GL κ K) ^ 3 = 1)
    (hEx : c (Subgroup.inclusion hc.le E) * c x₀ * (c (Subgroup.inclusion hc.le E))⁻¹ =
      c δ * c x₀)
    (σ : GL κ K → K)
    (hcomm3 : ∀ z z' : N, c z ∈ TypeA.inducedSub ψ A → c z' ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → (z : GL κ K) * z' = z' * z)
    (hσmul : ∀ z z' : N, c z ∈ TypeA.inducedSub ψ A → c z' ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → (z' : GL κ K) ^ 3 = 1 → σ ((z : GL κ K) * z') = σ z * σ z')
    (hσsc : ∀ (u : Kˣ) (z : N), u ^ 3 = 1 → c z ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → σ (GeneralLinearGroup.scalar κ u * z) = σ z)
    (hσconj : ∀ s : N, (∀ x ∈ TypeA.inducedSub ψ A, c s * x * (c s)⁻¹ ∈ TypeA.inducedSub ψ A) →
      ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ 3 = 1 →
        σ ((s : GL κ K) * z * (s : GL κ K)⁻¹) = σ z)
    (hσ3 : ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ 3 = 1 → σ z ^ 3 = 1)
    (hσδ : σ δ ≠ 1)
    [Fact (Nat.Prime 3)] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : NeZero 3 := ⟨by norm_num⟩
  set X := TypeA.inducedSub ψ A with hX
  have hXab : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  set G : Subgroup (GL κ K) := (X.comap c).map N.subtype with hG
  have hGp : TypeA.PGLTor.IsProjElem 3 G :=
    TypeA.PGLTor.isProjElem_comap_map_subtype hc.scalar_mem hc.map_scalar hc.ker hXab
  set lm := TypeA.PGLTor.lam hp hp2 hGp with hlm
  let cls : G →* TypeA.PGLTor.PowQuot K 3 := (QuotientGroup.mk' _).comp lm
  have hcls : ∀ z : G, cls z = (QuotientGroup.mk (lm z) : TypeA.PGLTor.PowQuot K 3) :=
    fun _ => rfl
  let mkG : ∀ z : N, c z ∈ X → G := fun z hz => ⟨z, z, hz, rfl⟩
  have hlm_eq : ∀ (z : G) (u : Kˣ), (z : GL κ K) ^ 3 = GeneralLinearGroup.scalar κ u →
      lm z = u := fun z u hz => TypeA.PGLTor.scalar_injective (ι := κ)
        (by rw [← TypeA.PGLTor.lam_spec hp hp2 hGp z, hz])
  have hcls_scalar : ∀ (z : G) (u : Kˣ), (z : GL κ K) = GeneralLinearGroup.scalar κ u →
      cls z = 1 := by
    intro z u hz
    rw [hcls, hlm_eq z (u ^ 3) (by rw [hz, ← map_pow]),
      TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  have hlift : ∀ a : ↥A, ∃ B : N, ∀ l, c B (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hBX : ∀ a : ↥A, c (B a) ∈ X := fun a => TypeA.mem_inducedSub.mpr ⟨a, a.2, hB a⟩
  have hBeq : ∀ (a : ↥A) (B' : N),
      (∀ l, c B' (ψ l) = ψ ((a : MulAut L') l)) →
        ∃ u : Kˣ, (B a : GL κ K) = GeneralLinearGroup.scalar κ u * B' := fun a B' hB' =>
    hc.exists_scalar_mul_of_eq (TypeA.induced_unique ψ hψ (hB a) hB')
  have hBc : ∀ (a : ↥A) (B' : N), (∀ l, c B' (ψ l) = ψ ((a : MulAut L') l)) → c B' = c (B a) :=
    fun a B' hB' => TypeA.induced_unique ψ hψ hB' (hB a)
  let jA : ↥A →* TypeA.PGLTor.PowQuot K 3 :=
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
        change ((S' : GL κ K) * B a * (S' : GL κ K)⁻¹) ^ 3 = _
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
  have hlift3 : ∀ a : ↥A, jA a = 1 → ∃ z : N, c z = c (B a) ∧ (z : GL κ K) ^ 3 = 1 := by
    intro a ha
    rw [hjA, hcls, TypeA.PGLTor.powQuot_mk_eq_one_iff] at ha
    obtain ⟨μ, hμ⟩ := ha
    refine ⟨⟨GeneralLinearGroup.scalar κ μ⁻¹, hc.scalar_mem μ⁻¹⟩ * B a, ?_, ?_⟩
    · rw [map_mul, hc.map_scalar, one_mul]
    · change (GeneralLinearGroup.scalar κ μ⁻¹ * (B a : GL κ K)) ^ 3 = 1
      rw [(TypeA.PGLTor.commute_scalar _ _).mul_pow, ← map_pow,
        TypeA.PGLTor.lam_spec hp hp2 hGp (mkG (B a) (hBX a))]
      change GeneralLinearGroup.scalar κ (μ⁻¹ ^ 3) * GeneralLinearGroup.scalar κ (lm _) = 1
      rw [← hμ, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hσwd : ∀ z z' : N, c z ∈ X → (z : GL κ K) ^ 3 = 1 → (z' : GL κ K) ^ 3 = 1 →
      c z' = c z → σ z' = σ z := by
    intro z z' hz hz3 hz'3 hzz
    obtain ⟨u, hu⟩ := hc.exists_scalar_mul_of_eq hzz
    have hu3 : u ^ 3 = 1 := by
      apply TypeA.PGLTor.scalar_injective (ι := κ)
      rw [map_pow, map_one]
      have e : (z' : GL κ K) ^ 3 = (GeneralLinearGroup.scalar κ u) ^ 3 * (z : GL κ K) ^ 3 := by
        rw [hu, (TypeA.PGLTor.commute_scalar u _).mul_pow]
      rw [hz'3, hz3, mul_one] at e
      exact e.symm
    rw [hu]
    exact hσsc u z hu3 hz hz3
  let σA : ↥A → K := fun a =>
    if ha : jA a = 1 then σ ((Classical.choose (hlift3 a ha) : N) : GL κ K) else 1
  have hσA : ∀ (a : ↥A) (z : N), c z = c (B a) → (z : GL κ K) ^ 3 = 1 → σA a = σ z := by
    intro a z hz hz3
    have ha : jA a = 1 := by
      obtain ⟨u, hu⟩ := hBeq a z (fun l => by rw [hz, hB a])
      rw [hjA, hcls, hlm_eq (mkG (B a) (hBX a)) (u ^ 3) (by
          change ((B a : N) : GL κ K) ^ 3 = _
          rw [hu, (TypeA.PGLTor.commute_scalar u _).mul_pow, hz3, mul_one, ← map_pow]),
        TypeA.PGLTor.powQuot_mk_eq_one_iff]
      exact ⟨u, rfl⟩
    have hspec := Classical.choose_spec (hlift3 a ha)
    show (if ha' : jA a = 1 then σ ((Classical.choose (hlift3 a ha') : N) : GL κ K) else 1) =
      σ z
    rw [dif_pos ha]
    exact hσwd z _ (hz ▸ hBX a) hz3 hspec.2 (hspec.1.trans hz.symm)
  have hσ1 : σ 1 = 1 := by
    have h1X : c 1 ∈ X := by rw [map_one]; exact X.one_mem
    have e1 := hσmul 1 1 h1X h1X (by simp) (by simp)
    have e3 := hσ3 1 h1X (by simp)
    simp only [OneMemClass.coe_one, mul_one] at e1 e3
    have h0 : σ 1 ≠ 0 := by
      intro h0
      rw [h0] at e3
      norm_num at e3
    have : σ 1 * σ 1 = σ 1 * 1 := by rw [mul_one]; exact e1.symm
    exact mul_left_cancel₀ h0 this
  have hσA1 : σA 1 = 1 := by
    rw [hσA 1 1 (hBc 1 1 fun l => by rw [map_one]; rfl) (by simp)]
    exact hσ1
  have hσAmul : ∀ a b : ↥A, jA a = 1 → jA b = 1 → σA (a * b) = σA a * σA b := by
    intro a b ha hb
    obtain ⟨za, hza, hza3⟩ := hlift3 a ha
    obtain ⟨zb, hzb, hzb3⟩ := hlift3 b hb
    have hzaX : c za ∈ X := hza ▸ hBX a
    have hzbX : c zb ∈ X := hzb ▸ hBX b
    have hcab : c (za * zb) = c (B (a * b)) := by
      rw [map_mul, hza, hzb, ← map_mul]
      exact (hBc (a * b) (B a * B b) fun l => by
        rw [map_mul, MulAut.mul_apply, hB b, hB a]; rfl)
    have hab3 : ((za * zb : N) : GL κ K) ^ 3 = 1 := by
      change ((za : GL κ K) * zb) ^ 3 = 1
      rw [(Commute.mul_pow (hcomm3 za zb hzaX hzbX hza3)), hza3, hzb3, one_mul]
    rw [hσA (a * b) (za * zb) hcab hab3, hσA a za hza hza3, hσA b zb hzb hzb3]
    exact hσmul za zb hzaX hzbX hza3 hzb3
  have hσAinv : ∀ f ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ a : ↥A,
      jA a = 1 → σA (f a) = σA a := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      obtain ⟨g, ⟨n, rfl⟩, hgN, hgf⟩ := hf
      intro a ha
      obtain ⟨s, hs⟩ := hc.inner (ψ n)
      set S' : N := Subgroup.inclusion hc.le s with hS'
      have hcS : c S' = MulAut.conj (ψ n) := hs.symm
      obtain ⟨za, hza, hza3⟩ := hlift3 a ha
      have hconj : ∀ l, c (S' * za * S'⁻¹) (ψ l) = ψ (((f a : ↥A) : MulAut L') l) := by
        intro l
        have h1 : c (S' * za * S'⁻¹) = c S' * c (B a) * (c S')⁻¹ := by
          rw [map_mul, map_mul, map_inv, hza]
        rw [h1, hcS, TypeA.conj_induced_apply ψ (hB a) n l, ← hgf a]
      have hS'N : ∀ x ∈ X, c S' * x * (c S')⁻¹ ∈ X := by
        intro x hx
        obtain ⟨b, hb, hxb⟩ := TypeA.mem_inducedSub.mp hx
        refine TypeA.mem_inducedSub.mpr ⟨MulAut.conj n * b * (MulAut.conj n)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgN b).mp hb, fun l => ?_⟩
        rw [hcS]
        exact TypeA.conj_induced_apply ψ hxb n l
      have hz3 : ((S' * za * S'⁻¹ : N) : GL κ K) ^ 3 = 1 := by
        change ((S' : GL κ K) * za * (S' : GL κ K)⁻¹) ^ 3 = 1
        rw [conj_pow, hza3, mul_one, mul_inv_cancel]
      rw [hσA (f a) _ (hBc (f a) _ hconj) hz3, hσA a za hza hza3]
      exact hσconj S' hS'N za (hza ▸ hBX a) hza3
    | one => intro a _; rfl
    | mul f g hf hg ihf ihg =>
      intro a ha
      rw [MulAut.mul_apply, ihf (g a) (by rw [hinv g hg a]; exact ha), ihg a ha]
    | inv f hf ihf =>
      intro a ha
      have hb : jA (f⁻¹ a) = 1 := by
        have e := hinv f hf (f⁻¹ a)
        rw [MulAut.apply_inv_self] at e
        rw [← e, ha]
      have e := ihf (f⁻¹ a) hb
      rw [MulAut.apply_inv_self] at e
      exact e.symm
  have hφA : ∀ i, φ i ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := fun i => by
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hcls_pow : ∀ x : TypeA.PGLTor.PowQuot K 3, x ^ 3 = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  have hhker : ∀ i, jA (Additive.toMul (ι.symm (h i))) = 1 ∧
      σA (Additive.toMul (ι.symm (h i))) = 1 := by
    intro i
    set b : ↥A := Additive.toMul (ι.symm (h i)) with hb
    have hii : α i (h i) = 2 := by rw [hpair i i, hC.1 i]; simp
    have hrefl : ggLin (p := 3) ι (φ i) (h i) = -h i := by
      rw [hlin, hii]
      module
    have hφb : φ i b = b⁻¹ := by
      have e := ggLin_apply_ofMul (p := 3) ι (φ i) b
      rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply, hrefl] at e
      apply_fun fun v => Additive.toMul (ι.symm v) at e
      rw [AddEquiv.symm_apply_apply, toMul_ofMul] at e
      rw [← e, map_neg, toMul_neg]
    have hjb : jA b = 1 := by
      have h1 := hinv (φ i) (hφA i) b
      rw [hφb, map_inv] at h1
      have h2 : jA b ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 1 [← h1]
        exact inv_mul_cancel _
      have h3 := hcls_pow (jA b)
      have hord : orderOf (jA b) ∣ Nat.gcd 2 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
      rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hord
      exact hord
    refine ⟨hjb, ?_⟩
    have hjb' : jA b⁻¹ = 1 := by rw [map_inv, hjb, inv_one]
    have h1 := hσAinv (φ i) (hφA i) b hjb
    rw [hφb] at h1
    have h2 : σA b * σA b = 1 := by
      have e := hσAmul b b⁻¹ hjb hjb'
      rw [mul_inv_cancel, hσA1, h1] at e
      exact e.symm
    have h3 : σA b ^ 3 = 1 := by
      obtain ⟨z, hz, hz3⟩ := hlift3 b hjb
      rw [hσA b z hz hz3]
      exact hσ3 z (hz ▸ hBX b) hz3
    calc σA b = σA b * (σA b * σA b) := by rw [h2, mul_one]
      _ = σA b ^ 3 := by ring
      _ = 1 := h3
  have hspan : ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      jA (Additive.toMul (ι.symm v)) = 1 ∧ σA (Additive.toMul (ι.symm v)) = 1 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hhker i
    | zero => rw [map_zero, toMul_zero, map_one]; exact ⟨rfl, hσA1⟩
    | add x y _ _ hx hy =>
      rw [map_add, toMul_add, map_mul, hx.1, hy.1, one_mul]
      exact ⟨rfl, by rw [hσAmul _ _ hx.1 hy.1, hx.2, hy.2, one_mul]⟩
    | smul a x _ hx =>
      rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, map_nsmul, toMul_nsmul]
      refine ⟨by rw [map_pow, hx.1, one_pow], ?_⟩
      induction a.val with
      | zero => rw [pow_zero]; exact hσA1
      | succ k ih =>
        rw [pow_succ, hσAmul _ _ (by rw [map_pow, hx.1, one_pow]) hx.1, ih, hx.2, one_mul]
  obtain ⟨r₀, hr₀⟩ := hc.inner' E
  obtain ⟨n, hψn⟩ := hψ r₀
  have hcn : MulAut.conj (ψ n) = c (Subgroup.inclusion hc.le E) := by
    rw [hψn]; exact hr₀
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hact : ∀ (a b : ↥A), c E' * c (B a) * (c E')⁻¹ = c (B b) →
      MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ = (b : MulAut L') := by
    intro a b hab
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← TypeA.conj_induced_apply ψ (hB a) n l, hcn, hab, hB b]
  have hnN : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj n)).injective).ge
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbind⟩ := TypeA.mem_inducedSub.mp (hEN _ (hBX ⟨a, ha⟩))
    have hcb : c E' * c (B ⟨a, ha⟩) * (c E')⁻¹ = c (B ⟨b, hb⟩) :=
      TypeA.induced_unique ψ hψ hbind (hB ⟨b, hb⟩)
    change MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A
    rw [hact ⟨a, ha⟩ ⟨b, hb⟩ hcb]
    exact hb
  set t := ggConjAut A hnN with ht
  have htW : t ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN
  obtain ⟨a₀v, ha₀v, ha₀⟩ := TypeA.mem_inducedSub.mp hx₀
  set a₀ : ↥A := ⟨a₀v, ha₀v⟩ with ha₀def
  obtain ⟨aδv, haδv, haδ⟩ := TypeA.mem_inducedSub.mp hδ
  set aδ : ↥A := ⟨aδv, haδv⟩ with haδdef
  have hta₀ : t a₀ = aδ * a₀ := by
    apply Subtype.ext
    rw [ggConjAut_apply]
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← TypeA.conj_induced_apply ψ ha₀ n l, hcn, hEx]
    change c δ (c x₀ (ψ l)) = ψ (aδv (a₀v l))
    rw [ha₀, haδ]
  have hσaδ : σA aδ ≠ 1 := by
    rw [hσA aδ δ (hBc aδ δ haδ) hδ3]
    exact hσδ
  have htcl : t ∈ Subgroup.closure (Set.range φ) := hgen ▸ htW
  have hmove := ggLin_sub_mem_span_of_mem_closure (p := 3) ι φ h α hlin htcl
    (ι (Additive.ofMul a₀))
  rw [ggLin_apply_ofMul, hta₀, ofMul_mul, map_add, add_sub_cancel_right] at hmove
  apply hσaδ
  have := (hspan _ hmove).2
  rwa [AddEquiv.symm_apply_apply, toMul_ofMul] at this

theorem false_of_transvection_three_of_commute (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    [Finite L'] (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ 3 = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ 3 ≠ l₀)
    (E : S) (δ : N) (hδ : c δ ∈ TypeA.inducedSub ψ A) (hδ3 : (δ : GL κ K) ^ 3 = 1)
    (hEx : (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = δ * x₀)
    (hEy : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ 3 = 1 →
      (E : GL κ K) * y = y * E)
    (σ : GL κ K → K)
    (hcomm3 : ∀ z z' : N, c z ∈ TypeA.inducedSub ψ A → c z' ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → (z : GL κ K) * z' = z' * z)
    (hσmul : ∀ z z' : N, c z ∈ TypeA.inducedSub ψ A → c z' ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → (z' : GL κ K) ^ 3 = 1 → σ ((z : GL κ K) * z') = σ z * σ z')
    (hσsc : ∀ (u : Kˣ) (z : N), u ^ 3 = 1 → c z ∈ TypeA.inducedSub ψ A →
      (z : GL κ K) ^ 3 = 1 → σ (GeneralLinearGroup.scalar κ u * z) = σ z)
    (hσconj : ∀ s : N, (∀ x ∈ TypeA.inducedSub ψ A, c s * x * (c s)⁻¹ ∈ TypeA.inducedSub ψ A) →
      ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ 3 = 1 →
        σ ((s : GL κ K) * z * (s : GL κ K)⁻¹) = σ z)
    (hσ3 : ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ 3 = 1 → σ z ^ 3 = 1)
    (hσδ : σ δ ≠ 1)
    [Fact (Nat.Prime 3)] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hconj : ∀ z : N, c E' * c z * (c E')⁻¹ = c (E' * z * E'⁻¹) := fun z => by
    rw [map_mul, map_mul, map_inv]
  refine false_of_transvection_three hc hψ hker hperf hA hAI hx₀ hx₀p hl₀ E
    (conj_mem_inducedSub_of_commute_order_p hc Nat.prime_three (by norm_num) hψ hA hAI hx₀ hx₀p
      hl₀ E' δ hδ hEx hEy) hδ hδ3 ?_ σ hcomm3 hσmul hσsc hσconj hσ3 hσδ hC ι φ h α hpair hlin hgen
  rw [hconj]
  have e : E' * x₀ * E'⁻¹ = δ * x₀ := Subtype.ext hEx
  rw [e, map_mul]

end TransvectionThree

end CFSG.StandardType.QuotMove
