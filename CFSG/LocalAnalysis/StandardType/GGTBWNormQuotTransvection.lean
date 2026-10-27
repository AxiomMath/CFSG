module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMove
public import CFSG.Mathlib.GroupTheory.Automorphism.Translations
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Cartan
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.GroupTheory.PrimeSqDvdCard

public section

namespace CFSG.StandardType.QuotMove

open CFSG CFSG.Assembly Matrix

section Datum

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]

omit [Fintype Λ] [DecidableEq Λ] in
theorem fix_of_mem_closure_refl (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (σ : Λ → V ≃ₗ[ZMod p] V) (hσ : ∀ i v, σ i v = v - α i v • h i)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Subgroup.closure (Set.range σ)) {w : V}
    (hw : ∀ i, α i w = 0) : g w = w := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hσ, hw i, zero_smul, sub_zero]
  | one => rfl
  | mul x y _ _ hx hy =>
    rw [LinearEquiv.mul_apply, hy, hx]
  | inv x _ hx =>
    change x.symm w = w
    conv_lhs => rw [← hx]
    exact x.symm_apply_apply w

theorem linearIndependent_coroots_typeA {m : ℕ} (e : Fin (m + 1) ≃ Λ)
    {C : Matrix Λ Λ ℤ} (hCA : ∀ i j : Fin (m + 1), C (e i) (e j) = CartanMatrix.A (m + 1) i j)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hm : ((m + 1 : ℕ) : ZMod p) ≠ 0) :
    LinearIndependent (ZMod p) (fun k : Fin m => h (e k.castSucc)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set Am : Matrix (Fin m) (Fin m) (ZMod p) := (CartanMatrix.A m).map (Int.castRingHom (ZMod p))
    with hAm
  have hentry : ∀ i k : Fin m, (C (e i.castSucc) (e k.castSucc) : ZMod p) = Am i k := by
    intro i k
    rw [hCA, hAm, Matrix.map_apply]
    congr 1
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.coe_castSucc]
  have hmul : Am *ᵥ c = 0 := by
    funext i
    have h0 := congrArg (α (e i.castSucc)) hc
    rw [map_sum, map_zero] at h0
    simp only [map_smul, hpair, smul_eq_mul] at h0
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hentry, mul_comm]
  have hdet : Am.det ≠ 0 := by
    rw [hAm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, CartanMatrix.A_det]
    simpa using hm
  have hc0 := (Matrix.eq_zero_of_mulVec_eq_zero hdet hmul)
  intro k
  exact congrFun hc0 k

theorem eq_one_of_fix_span_coroots (hp5 : 5 ≤ p) {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (σ : Λ → V ≃ₗ[ZMod p] V)
    (hσ : ∀ i v, σ i v = v - α i v • h i)
    (hdim : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) ≤ 2)
    {t : V ≃ₗ[ZMod p] V} (ht : t ∈ Subgroup.closure (Set.range σ))
    (htfix : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), t v = v) : t = 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set W := Submodule.span (ZMod p) (Set.range h) with hW
  by_cases hdet : ((C.det : ℤ) : ZMod p) = 0
  · exfalso
    rcases ggRC_singular_typeA_or_E6 hp hp2 hM hC hdet with ⟨⟨r, e, hr, hMe⟩, hpr⟩ | ⟨hp3, -⟩
    · have hcard : Fintype.card Λ = r := by simpa using (Fintype.card_congr e).symm
      rw [hcard] at hpr
      have hr4 : 4 ≤ r := by
        have := Nat.le_of_dvd (by omega) hpr
        omega
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hCA := ggQ2_cartan_A e hMe hC
      have hm : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have h1 : p ∣ m + 1 + 1 - (m + 1) := Nat.dvd_sub hpr hd
        rw [show m + 1 + 1 - (m + 1) = 1 by omega] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hli := linearIndependent_coroots_typeA e hCA h α hpair hm
      let g : Fin m → W := fun k => ⟨h (e k.castSucc), Submodule.subset_span ⟨_, rfl⟩⟩
      have hli' : LinearIndependent (ZMod p) g := by
        apply LinearIndependent.of_comp W.subtype
        exact hli
      have : Module.Finite (ZMod p) W := by
        apply Module.Finite.span_of_finite
        exact Set.finite_range h
      have hle := hli'.fintype_card_le_finrank
      rw [Fintype.card_fin] at hle
      omega
    · omega
  · refine LinearEquiv.ext fun v => ?_
    change t v = v
    set Cp : Matrix Λ Λ (ZMod p) := C.map (Int.castRingHom (ZMod p)) with hCp
    have hdet' : IsUnit Cp.det := by
      rw [hCp, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact isUnit_iff_ne_zero.mpr hdet
    set a : Λ → ZMod p := fun i => α i v with ha
    set c : Λ → ZMod p := Cp⁻¹ *ᵥ a with hc
    have hCc : Cp *ᵥ c = a := by
      rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
    set u : V := ∑ j, c j • h j with hu
    have huW : u ∈ W := Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hw : ∀ i, α i (v - u) = 0 := by
      intro i
      rw [map_sub, hu, map_sum]
      simp only [map_smul, hpair, smul_eq_mul]
      have h1 := congrFun hCc i
      rw [Matrix.mulVec, dotProduct] at h1
      refine sub_eq_zero.mpr ?_
      rw [← show a i = α i v from rfl, ← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hCp, Matrix.map_apply, mul_comm]
      rfl
    have hfix := fix_of_mem_closure_refl h α σ hσ ht hw
    calc t v = t (u + (v - u)) := by rw [add_sub_cancel]
      _ = t u + t (v - u) := map_add t _ _
      _ = u + (v - u) := by rw [htfix u huW, hfix]
      _ = v := add_sub_cancel u v

end Datum

section Transvection

variable {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K] {R : Type} [Group R]
  {N : Subgroup (GL κ K)} {c : N →* MulAut R} {S : Subgroup (GL κ K)}
  {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} {p : ℕ}

theorem exists_power_class_character (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l)) :
    ∃ ν : ↥A →* TypeA.PGLTor.PowQuot K p,
      (∀ (a : ↥A) (z : N) (u : Kˣ),
        (∀ l : L', c z (ψ l) = ψ ((a : MulAut L') l)) →
        (z : GL κ K) ^ p = GeneralLinearGroup.scalar κ u →
        ν a = (QuotientGroup.mk u : TypeA.PGLTor.PowQuot K p)) ∧
      (∀ a : ↥A, ν a = 1 ↔ ∃ z : N,
        (∀ l : L', c z (ψ l) = ψ ((a : MulAut L') l)) ∧ (z : GL κ K) ^ p = 1) ∧
      ∀ f ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
        ∀ a : ↥A, ν (f a) = ν a := by
  classical
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
  have hspec : ∀ (a : ↥A) (z : N) (u : Kˣ),
      (∀ l : L', c z (ψ l) = ψ ((a : MulAut L') l)) →
      (z : GL κ K) ^ p = GeneralLinearGroup.scalar κ u →
      jA a = (QuotientGroup.mk u : TypeA.PGLTor.PowQuot K p) := by
    intro a z u hza hzp
    have hzX : c z ∈ X := TypeA.mem_inducedSub.mpr ⟨a, a.2, hza⟩
    obtain ⟨v, hv⟩ := hBeq a z hza
    have e : mkG (B a) (hBX a) =
        ⟨GeneralLinearGroup.scalar κ v, hGp.scalar_mem v⟩ * mkG z hzX := Subtype.ext hv
    rw [hjA, e, map_mul, hcls_scalar _ v rfl, one_mul, hcls, hlm_eq _ u hzp]
  refine ⟨jA, hspec, ?_, hinv⟩
  intro a
  constructor
  · intro ha
    rw [hjA, hcls, TypeA.PGLTor.powQuot_mk_eq_one_iff] at ha
    obtain ⟨μ, hμ⟩ := ha
    let z : N := ⟨GeneralLinearGroup.scalar κ μ⁻¹, hc.scalar_mem μ⁻¹⟩ * B a
    have hcz : c z = c (B a) := by
      change c (⟨GeneralLinearGroup.scalar κ μ⁻¹, hc.scalar_mem μ⁻¹⟩ * B a) = _
      rw [map_mul, hc.map_scalar, one_mul]
    refine ⟨z, (fun l => by rw [hcz]; exact hB a l), ?_⟩
    change (GeneralLinearGroup.scalar κ μ⁻¹ * (B a : GL κ K)) ^ p = 1
    rw [(TypeA.PGLTor.commute_scalar _ _).mul_pow, ← map_pow,
      TypeA.PGLTor.lam_spec hp hp2 hGp (mkG (B a) (hBX a))]
    change GeneralLinearGroup.scalar κ (μ⁻¹ ^ p) * GeneralLinearGroup.scalar κ (lm _) = 1
    rw [← hμ, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  · rintro ⟨z, hza, hzp⟩
    simpa using hspec a z 1 hza (by simpa using hzp)

theorem false_of_transvection (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] [Finite L']
    (hp : p.Prime) (hp5 : 5 ≤ p) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l)) (hcardA : Nat.card A ≤ p ^ 3)
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (E : S)
    (hEN : ∀ x ∈ TypeA.inducedSub ψ A,
      c (Subgroup.inclusion hc.le E) * x * (c (Subgroup.inclusion hc.le E))⁻¹ ∈
        TypeA.inducedSub ψ A)
    (hEfix : ∀ z : N, c z ∈ TypeA.inducedSub ψ A → (z : GL κ K) ^ p = 1 →
      c (Subgroup.inclusion hc.le E) * c z * (c (Subgroup.inclusion hc.le E))⁻¹ = c z)
    (hEmove : c (Subgroup.inclusion hc.le E) * c x₀ * (c (Subgroup.inclusion hc.le E))⁻¹ ≠ c x₀)
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
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have : Finite V := Finite.of_injective ι.symm ι.symm.injective
  set X := TypeA.inducedSub ψ A with hX
  obtain ⟨jA, hjA, hjker, hinv⟩ := exists_power_class_character hc hp hp2 hψ hA hAI
  have hlift : ∀ a : ↥A, ∃ B : N, ∀ l, c B (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hBX : ∀ a : ↥A, c (B a) ∈ X := fun a => TypeA.mem_inducedSub.mpr ⟨a, a.2, hB a⟩
  have hcls_pow : ∀ x : TypeA.PGLTor.PowQuot K p, x ^ p = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨u, rfl⟩
  obtain ⟨a₀v, ha₀v, ha₀⟩ := TypeA.mem_inducedSub.mp hx₀
  set a₀ : ↥A := ⟨a₀v, ha₀v⟩ with ha₀def
  have hja₀ : jA a₀ ≠ 1 := by
    rw [hjA a₀ x₀ l₀ ha₀ hx₀p]
    intro hcon
    obtain ⟨μ, hμ⟩ := TypeA.PGLTor.powQuot_mk_eq_one_iff.mp hcon
    exact hl₀ μ hμ
  have hApg : IsPGroup p A := hA.isPGroup
  have hkercard : Nat.card jA.ker ≤ p ^ 2 := by
    have hlt : Nat.card jA.ker < Nat.card A := by
      have hne : jA.ker ≠ ⊤ := fun htop => hja₀ ((MonoidHom.mem_ker).mp (htop ▸ Subgroup.mem_top a₀))
      have hlt' := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hne)
      rwa [Subgroup.card_top] at hlt'
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hApg)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ Subgroup.card_subgroup_dvd_card jA.ker)
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hk ▸ hcardA)
    rw [hj, hk] at hlt
    have hjk : j < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    rw [hj]
    exact Nat.pow_le_pow_right hp.pos (by omega)
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
  have hdim : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) ≤ 2 := by
    set W := Submodule.span (ZMod p) (Set.range h)
    have hinj : Function.Injective (fun w : W =>
        (⟨Additive.toMul (ι.symm w), hspan w w.2⟩ : jA.ker)) := by
      intro w w' hww
      apply Subtype.ext
      have := congrArg (fun x : jA.ker => ι (Additive.ofMul (x : ↥A))) hww
      simpa using this
    have hcardW := Nat.card_le_card_of_injective _ hinj
    rw [← FiniteField.pow_finrank_eq_natCard p W] at hcardW
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcardW.trans hkercard)
  obtain ⟨n, hcn, hnN⟩ := exists_inner_of_normalizes_inducedSub hc hψ hker hperf hAI E hEN
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hact : ∀ (a b : ↥A), c E' * c (B a) * (c E')⁻¹ = c (B b) →
      MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ = (b : MulAut L') := by
    intro a b hab
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← TypeA.conj_induced_apply ψ (hB a) n l, hcn, hab, hB b]
  set t := ggConjAut A hnN with ht
  have htW : t ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN
  have htfix : ∀ a : ↥A, jA a = 1 → t a = a := by
    intro a ha
    obtain ⟨z, hza, hzp⟩ := (hjker a).mp ha
    have hcz : c z = c (B a) := TypeA.induced_unique ψ hψ hza (hB a)
    have hfix := hEfix z (by rw [hcz]; exact hBX a) hzp
    rw [hcz] at hfix
    apply Subtype.ext
    rw [ggConjAut_apply, hact a a hfix]
  have htmove : t a₀ ≠ a₀ := by
    intro he
    have he' : MulAut.conj n * (a₀ : MulAut L') * (MulAut.conj n)⁻¹ = (a₀ : MulAut L') := by
      have := congrArg Subtype.val he
      rwa [ggConjAut_apply] at this
    apply hEmove
    apply TypeA.induced_unique ψ hψ (a := (a₀ : MulAut L'))
    · intro l
      rw [← hcn, TypeA.conj_induced_apply ψ ha₀ n l, he']
    · exact ha₀
  have hσ : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i := hlin
  have htσ : ggLin (p := p) ι t ∈ Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    have h1 : t ∈ Subgroup.closure (Set.range φ) := hgen ▸ htW
    have h2 := Subgroup.mem_map_of_mem (ggLin (p := p) ι) h1
    rwa [MonoidHom.map_closure, ← Set.range_comp] at h2
  have htfixV : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), ggLin (p := p) ι t v = v := by
    intro v hv
    have hv' := hspan v hv
    have e := ggLin_apply_ofMul (p := p) ι t (Additive.toMul (ι.symm v))
    rwa [ofMul_toMul, AddEquiv.apply_symm_apply, htfix _ hv', ofMul_toMul,
      AddEquiv.apply_symm_apply] at e
  have hone := eq_one_of_fix_span_coroots hp5 hM hC h α hpair _ hσ hdim htσ htfixV
  apply htmove
  have e := ggLin_apply_ofMul (p := p) ι t a₀
  rw [hone] at e
  have e2 : ι (Additive.ofMul a₀) = ι (Additive.ofMul (t a₀)) := e
  exact (Additive.ofMul.injective (ι.injective e2)).symm

theorem exists_decomp_of_class (hc : IsScalarQuot c S) [Nonempty κ] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    {M : N} (hM : c M ∈ TypeA.inducedSub ψ A) :
    ∃ (s : Kˣ) (y : N) (k : ℕ), c y ∈ TypeA.inducedSub ψ A ∧ (y : GL κ K) ^ p = 1 ∧
      (M : GL κ K) = GeneralLinearGroup.scalar κ s * y * (x₀ : GL κ K) ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
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
  have hg₁ : cls (mkG x₀ hx₀) ≠ 1 := by
    rw [hcls, hlm_eq _ l₀ hx₀p]
    intro hcon
    obtain ⟨μ, hμ⟩ := TypeA.PGLTor.powQuot_mk_eq_one_iff.mp hcon
    exact hl₀ μ hμ
  have hgp : cls (mkG x₀ hx₀) ^ p = 1 := by
    rw [hcls, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨_, rfl⟩
  have htop : Subgroup.zpowers (cls (mkG x₀ hx₀)) = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, orderOf_eq_prime hgp hg₁]
    exact TypeA.PGLTor.card_powQuot_le
  obtain ⟨k, hk⟩ : ∃ k : ℕ, cls (mkG x₀ hx₀) ^ k = cls (mkG M hM) := by
    have h1 : cls (mkG M hM) ∈ Subgroup.zpowers (cls (mkG x₀ hx₀)) :=
      htop ▸ Subgroup.mem_top _
    exact mem_powers_iff_mem_zpowers.mpr h1
  set w : N := M * (x₀ ^ k)⁻¹ with hw
  have hwX : c w ∈ X := by
    rw [hw, map_mul, map_inv, map_pow]
    exact X.mul_mem hM (X.inv_mem (X.pow_mem hx₀ k))
  have hwcls : cls (mkG w hwX) = 1 := by
    have e : mkG w hwX = mkG M hM * (mkG x₀ hx₀ ^ k)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv, map_pow, hk, mul_inv_cancel]
  rw [hcls, TypeA.PGLTor.powQuot_mk_eq_one_iff] at hwcls
  obtain ⟨μ, hμ⟩ := hwcls
  have hwp : (w : GL κ K) ^ p = GeneralLinearGroup.scalar κ (μ ^ p) := by
    rw [hμ]
    exact TypeA.PGLTor.lam_spec hp hp2 hGp (mkG w hwX)
  refine ⟨μ, ⟨GeneralLinearGroup.scalar κ μ⁻¹, hc.scalar_mem _⟩ * w, k, ?_, ?_, ?_⟩
  · rw [map_mul, hc.map_scalar, one_mul]
    exact hwX
  · exact TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow hwp
  · change (M : GL κ K) = GeneralLinearGroup.scalar κ μ *
      (GeneralLinearGroup.scalar κ μ⁻¹ * ((M : GL κ K) * ((x₀ : GL κ K) ^ k)⁻¹)) *
        (x₀ : GL κ K) ^ k
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, inv_mul_cancel_right]

theorem exists_nonscalar_of_lt_card (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (hcard : p < Nat.card A) :
    ∃ y : N, c y ∈ TypeA.inducedSub ψ A ∧ (y : GL κ K) ^ p = 1 ∧
      ∀ u : Kˣ, (y : GL κ K) ≠ GeneralLinearGroup.scalar κ u := by
  classical
  by_contra hcon
  push Not at hcon
  set X := TypeA.inducedSub ψ A with hX
  have hXab : IsElemAbelian p X := TypeA.isElemAbelian_inducedSub hψ hA
  have hle : X ≤ Subgroup.zpowers (c x₀) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨M, hM⟩ := hAI a ha
    have hMx : c M = x := TypeA.induced_unique ψ hψ hM hxa
    obtain ⟨s, y, k, hyX, hyp, hMeq⟩ :=
      exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ (M := M) (hMx ▸ hx)
    obtain ⟨u, hu⟩ := hcon y hyX hyp
    have e : M = ⟨GeneralLinearGroup.scalar κ (s * u), hc.scalar_mem _⟩ * x₀ ^ k := by
      apply Subtype.ext
      rw [hMeq, hu, ← map_mul]
      rfl
    rw [← hMx, e, map_mul, hc.map_scalar, one_mul, map_pow]
    exact Subgroup.npow_mem_zpowers _ k
  have hcardX : Nat.card X = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨M, hM⟩ := hAI a ha
      exact ⟨c M, hM⟩)
  have hord : orderOf (c x₀) ≤ p := orderOf_le_of_pow_eq_one hp.pos (hXab.2 _ hx₀)
  have hpos : 0 < orderOf (c x₀) := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p, hp.pos, hXab.2 _ hx₀⟩)
  have : Finite (Subgroup.zpowers (c x₀)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hcardX] at h1
  omega

theorem conj_mem_inducedSub_of_commute_order_p (hc : IsScalarQuot c S)
    [Nonempty κ] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l))
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀)
    (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀) (E δ : N)
    (hδ : c δ ∈ TypeA.inducedSub ψ A)
    (hEx : (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = δ * x₀)
    (hEy : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      (E : GL κ K) * y = y * E) :
    ∀ x ∈ TypeA.inducedSub ψ A, c E * x * (c E)⁻¹ ∈ TypeA.inducedSub ψ A := by
  set X := TypeA.inducedSub ψ A with hX
  have hconj : ∀ z : N, c E * c z * (c E)⁻¹ = c (E * z * E⁻¹) := fun z => by
    rw [map_mul, map_mul, map_inv]
  intro x hx
  obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
  obtain ⟨M', hM'⟩ := hAI a ha
  have hMx : c M' = x := TypeA.induced_unique ψ hψ hM' hxa
  obtain ⟨s, y, k, hyX, hyp, hMeq⟩ :=
    exists_decomp_of_class hc hp hp2 hψ hA hx₀ hx₀p hl₀ (M := M') (hMx ▸ hx)
  have e : E * M' * E⁻¹ =
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

theorem false_of_transvection_of_commute (hc : IsScalarQuot c S) [Nonempty κ] [Finite K]
    [Finite L'] (hp : p.Prime) (hp5 : 5 ≤ p) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ M : N, ∀ l : L', c M (ψ l) = ψ (a l)) (hcardA : Nat.card A ≤ p ^ 3)
    {x₀ : N} (hx₀ : c x₀ ∈ TypeA.inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ p = GeneralLinearGroup.scalar κ l₀) (hl₀ : ∀ μ : Kˣ, μ ^ p ≠ l₀)
    (E : S) (δ : N) (hδ : c δ ∈ TypeA.inducedSub ψ A)
    (hδs : ∀ u : Kˣ, (δ : GL κ K) ≠ GeneralLinearGroup.scalar κ u)
    (hEx : (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = δ * x₀)
    (hEy : ∀ y : N, c y ∈ TypeA.inducedSub ψ A → (y : GL κ K) ^ p = 1 →
      (E : GL κ K) * y = y * E)
    [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  have hp2 : p ≠ 2 := by omega
  set X := TypeA.inducedSub ψ A with hX
  set E' : N := Subgroup.inclusion hc.le E with hE'
  have hconj : ∀ z : N, c E' * c z * (c E')⁻¹ = c (E' * z * E'⁻¹) := fun z => by
    rw [map_mul, map_mul, map_inv]
  have hfix : ∀ z : N, c z ∈ X → (z : GL κ K) ^ p = 1 → E' * z * E'⁻¹ = z := by
    intro z hz hzp
    apply Subtype.ext
    change (E : GL κ K) * z * (E : GL κ K)⁻¹ = z
    rw [hEy z hz hzp, mul_inv_cancel_right]
  refine false_of_transvection hc hp hp5 hψ hker hperf hA hAI hcardA hx₀ hx₀p hl₀ E ?_ ?_ ?_
    hM hC ι φ h α hpair hlin hgen
  ·
    exact conj_mem_inducedSub_of_commute_order_p hc hp hp2 hψ hA hAI hx₀ hx₀p hl₀
      E' δ hδ hEx hEy
  · intro z hz hzp
    rw [hconj, hfix z hz hzp]
  · intro he
    rw [hconj] at he
    have e : E' * x₀ * E'⁻¹ = δ * x₀ := Subtype.ext hEx
    rw [e, map_mul] at he
    obtain ⟨u, hu⟩ := hc.ker δ (mul_eq_right.mp he)
    exact hδs u hu

end Transvection

end CFSG.StandardType.QuotMove
