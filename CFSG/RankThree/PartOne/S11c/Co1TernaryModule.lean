module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Certificates.Certificate6950
public import CFSG.Sporadic.Schreier.Co1SplitLocal

public section

namespace CFSG.RankThree.PartOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open scoped IsMulCommutative

theorem co1_bilin_invariant_matrix {n : ℕ} (B : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3))
    (M : Matrix (Fin n) (Fin n) (ZMod 3)) (h : ∀ u v, B (M *ᵥ u) (M *ᵥ v) = B u v) :
    Mᵀ * LinearMap.BilinForm.toMatrix' B * M = LinearMap.BilinForm.toMatrix' B := by
  have h1 : B.comp (Matrix.toLin' M) (Matrix.toLin' M) = B := by
    refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
    simpa using h u v
  have := congrArg LinearMap.BilinForm.toMatrix' h1
  rw [LinearMap.BilinForm.toMatrix'_comp] at this
  simpa using this

@[expose] noncomputable def co1ModuleEquiv {S : Type*} [Group S] (E : Subgroup S)
    [CFSG.IsElementaryAbelian 3 E]
    (φ : Multiplicative (Fin 6 → ZMod 3) ≃* E) : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] Additive E :=
  let f : (Fin 6 → ZMod 3) ≃+ Additive E :=
    { toFun := fun u => Additive.ofMul (φ (Multiplicative.ofAdd u))
      invFun := fun x => Multiplicative.toAdd (φ.symm (Additive.toMul x))
      left_inv := fun u => by simp
      right_inv := fun x => by simp
      map_add' := fun u v => by simp [ofAdd_add] }
  { f with
    map_smul' := fun c x => by
      show f (c • x) = c • f x
      have h1 : c • x = c.val • x := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
      have h2 : ∀ y : Additive E, c • y = c.val • y := fun y => rfl
      rw [h1, h2, map_nsmul] }

theorem co1ModuleEquiv_apply {S : Type*} [Group S] (E : Subgroup S)
    [CFSG.IsElementaryAbelian 3 E] (φ : Multiplicative (Fin 6 → ZMod 3) ≃* E)
    (u : Fin 6 → ZMod 3) :
    co1ModuleEquiv E φ u = Additive.ofMul (φ (Multiplicative.ofAdd u)) := rfl

theorem co1_bilin_zero {S : Type*} [Group S] (E : Subgroup S)
    [CFSG.IsElementaryAbelian 3 E] (φ : Multiplicative (Fin 6 → ZMod 3) ≃* E) (c : Fin 2 → S)
    (hCE : ∀ i, c i ∈ Subgroup.normalizer (E : Set S))
    (hc : ∀ (i : Fin 2) (b : Fin 6 → ZMod 3),
      c i * (φ (Multiplicative.ofAdd b) : S) * (c i)⁻¹ =
        (φ (Multiplicative.ofAdd ((![co1M0, co1M1] i) *ᵥ b)) : S))
    (B : LinearMap.BilinForm (ZMod 3) (Additive E)) (halt : ∀ x, B x x = 0)
    (hinv : ∀ (i : Fin 2) (x y : E),
      B (Additive.ofMul (E.normalizerMonoidHom ⟨c i, hCE i⟩ x))
        (Additive.ofMul (E.normalizerMonoidHom ⟨c i, hCE i⟩ y)) =
        B (Additive.ofMul x) (Additive.ofMul y)) : B = 0 := by
  set L := co1ModuleEquiv E φ with hLdef
  set B' : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3) :=
    B.compl₁₂ (L : (Fin 6 → ZMod 3) →ₗ[ZMod 3] Additive E)
      (L : (Fin 6 → ZMod 3) →ₗ[ZMod 3] Additive E) with hB'
  have hB'apply : ∀ u v, B' u v = B (L u) (L v) := fun u v => rfl
  have hconj : ∀ (i : Fin 2) (u : Fin 6 → ZMod 3),
      L ((![co1M0, co1M1] i) *ᵥ u) =
        Additive.ofMul (E.normalizerMonoidHom ⟨c i, hCE i⟩ (Additive.toMul (L u))) := by
    intro i u
    rw [hLdef, co1ModuleEquiv_apply, co1ModuleEquiv_apply]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (hc i u).symm
  have hB'inv : ∀ (i : Fin 2) (u v : Fin 6 → ZMod 3),
      B' ((![co1M0, co1M1] i) *ᵥ u) ((![co1M0, co1M1] i) *ᵥ v) = B' u v := by
    intro i u v
    rw [hB'apply, hB'apply, hconj, hconj]
    exact hinv i (Additive.toMul (L u)) (Additive.toMul (L v))
  have hB'alt : ∀ u, B' u u = 0 := fun u => halt _
  set Bm := LinearMap.BilinForm.toMatrix' B' with hBm
  have hd : ∀ i, Bm i i = 0 := fun i => by
    rw [hBm, LinearMap.BilinForm.toMatrix'_apply]
    exact hB'alt _
  have hs : ∀ i j, Bm i j = - Bm j i := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact eq_neg_of_add_eq_zero_left (by rw [hd i]; decide)
    · have h1 := hB'alt (Pi.single i 1 + Pi.single j 1)
      simp only [map_add, LinearMap.add_apply, hB'alt, zero_add, add_zero] at h1
      rw [hBm, LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.toMatrix'_apply]
      exact eq_neg_of_add_eq_zero_right h1
  have h0 := co1_bilin_invariant_matrix B' co1M0 (hB'inv 0)
  have h1 := co1_bilin_invariant_matrix B' co1M1 (hB'inv 1)
  have hz : Bm = 0 := co1_skew_invariant_zero Bm hd hs h0 h1
  have hB'zero : B' = 0 := by
    apply LinearMap.BilinForm.toMatrix'.injective
    rw [← hBm, hz, map_zero]
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have := hB'apply (L.symm x) (L.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hB'zero] at this
  exact this.symm

theorem co1_conjExps (i : Fin 2) (j k : Fin 6) :
    Native.expVec ((Data.conjExps.getD i.val []).getD j.val []) k = (![co1M0, co1M1] i) k j := by
  revert i j k
  exact Certificates.certificate6950.1

theorem co1_c_conj_a (i : Fin 2) (j : Fin 6) :
    c i * a j * (c i)⁻¹ = eProd (fun k => (![co1M0, co1M1] i) k j) := by
  have hdE : d i ∈ E := by rw [d_eq]; exact eProd_mem _
  have h1 := g_conj_a i.castSucc j
  have hE : g i.castSucc * a j * (g i.castSucc)⁻¹ ∈ E := by rw [h1]; exact eProd_mem _
  have hc : c i = d i ^ 2 * g i.castSucc := rfl
  have hcomm : d i ^ 2 * (g i.castSucc * a j * (g i.castSucc)⁻¹) * (d i ^ 2)⁻¹ =
      g i.castSucc * a j * (g i.castSucc)⁻¹ := by
    rw [(E_comm _ (E.pow_mem hdE 2) _ hE).eq, mul_inv_cancel_right]
  calc c i * a j * (c i)⁻¹
      = d i ^ 2 * (g i.castSucc * a j * (g i.castSucc)⁻¹) * (d i ^ 2)⁻¹ := by
        rw [hc]; group
    _ = g i.castSucc * a j * (g i.castSucc)⁻¹ := hcomm
    _ = eProd (fun k => (![co1M0, co1M1] i) k j) := by
        rw [h1]
        congr 1
        funext k
        exact co1_conjExps i j k

theorem co1_conj_eProd_of_basis (x : GL24) (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hx : ∀ j, x * a j * x⁻¹ = eProd (fun k => M k j)) (b : Fin 6 → ZMod 3) :
    x * eProd b * x⁻¹ = eProd (M *ᵥ b) := by
  have hadd : ∀ u v : Fin 6 → ZMod 3, x * eProd u * x⁻¹ = eProd (M *ᵥ u) →
      x * eProd v * x⁻¹ = eProd (M *ᵥ v) →
      x * eProd (u + v) * x⁻¹ = eProd (M *ᵥ (u + v)) := by
    intro u v hu hv
    rw [eProd_add, Matrix.mulVec_add, eProd_add, ← hu, ← hv]
    group
  have hone : ∀ j, x * eProd (Pi.single j 1) * x⁻¹ = eProd (M *ᵥ Pi.single j 1) := by
    intro j
    rw [eProd_single, hx]
    congr 1
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hnsmul : ∀ (j : Fin 6) (n : ℕ),
      x * eProd (n • (Pi.single j 1 : Fin 6 → ZMod 3)) * x⁻¹ =
        eProd (M *ᵥ (n • (Pi.single j 1 : Fin 6 → ZMod 3))) := by
    intro j n
    induction n with
    | zero => simp [eProd_zero]
    | succ n ih => rw [succ_nsmul]; exact hadd _ _ ih (hone j)
  have hsingle : ∀ (j : Fin 6) (t : ZMod 3),
      x * eProd (Pi.single j t) * x⁻¹ = eProd (M *ᵥ Pi.single j t) := by
    intro j t
    have : (Pi.single j t : Fin 6 → ZMod 3) = t.val • (Pi.single j 1 : Fin 6 → ZMod 3) := by
      funext i
      by_cases h : i = j
      · subst h
        simp [nsmul_eq_mul]
      · simp [h]
    rw [this]
    exact hnsmul j t.val
  have hsum : ∀ s : Finset (Fin 6),
      x * eProd (∑ j ∈ s, Pi.single j (b j)) * x⁻¹ = eProd (M *ᵥ ∑ j ∈ s, Pi.single j (b j)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [eProd_zero]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact hadd _ _ (hsingle j (b j)) ih
  have := hsum Finset.univ
  rwa [Finset.univ_sum_single] at this

theorem co1_c_conj_eProd (i : Fin 2) (b : Fin 6 → ZMod 3) :
    c i * eProd b * (c i)⁻¹ = eProd ((![co1M0, co1M1] i) *ᵥ b) :=
  co1_conj_eProd_of_basis (c i) _ (co1_c_conj_a i) b

theorem co1_c_mem_C (i : Fin 2) : c i ∈ C := by
  rw [C]
  apply Subgroup.subset_closure
  fin_cases i <;> simp

theorem co1_proj_c (i : Fin 2) : proj ⟨c i, c_mem_A i⟩ = σ i := by
  have hc : (⟨c i, c_mem_A i⟩ : A) = (rA * gA i * rA⁻¹ * (gA i)⁻¹) ^ 2 * gA i :=
    Subtype.ext (cA_val i).symm
  have hk : proj (rA * gA i * rA⁻¹ * (gA i)⁻¹) = 1 :=
    MonoidHom.mem_ker.mp (EA_le_ker (gA_comm_mem i))
  rw [hc, map_mul, map_pow, hk, one_pow, one_mul]
  exact proj_g i

theorem co1_cEquiv_c (i : Fin 2) :
    ((cEquiv ⟨c i, co1_c_mem_C i⟩ : Q) : GL (Fin 12) (ZMod 3)) = σ i :=
  (cEquiv_apply ⟨c i, co1_c_mem_C i⟩ (c_mem_A i)).trans (co1_proj_c i)

theorem co1_sigma_zero_sq : σ 0 ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  change σMat 0 * σMat 0 = 1
  exact Certificates.certificate6950.2.1

theorem co1_sigma_zero_ne_one : σ 0 ≠ 1 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 12) (ZMod 3) => (g : Matrix (Fin 12) (Fin 12) (ZMod 3))) h
  change σMat 0 = 1 at h'
  revert h'
  exact Certificates.certificate6950.2.2.1

theorem co1_c_zero_sq : c 0 ^ 2 = 1 := by
  set x : C := ⟨c 0, co1_c_mem_C 0⟩ with hx
  have h : cEquiv (x ^ 2) = 1 := by
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, co1_cEquiv_c, co1_sigma_zero_sq, Subgroup.coe_one]
  have h1 : x ^ 2 = 1 := cEquiv.injective (h.trans (map_one cEquiv).symm)
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2

theorem co1_c_zero_ne_one : c 0 ≠ 1 := by
  intro h
  have h1 : (⟨c 0, co1_c_mem_C 0⟩ : C) = 1 := Subtype.ext h
  have h2 := congrArg (fun y : C => ((cEquiv y : Q) : GL (Fin 12) (ZMod 3))) h1
  simp only [co1_cEquiv_c, map_one, Subgroup.coe_one] at h2
  exact co1_sigma_zero_ne_one h2

theorem co1_orderOf_c_zero : orderOf (c 0) = 2 :=
  orderOf_eq_prime co1_c_zero_sq co1_c_zero_ne_one

theorem co1_card_fixed :
    Fintype.card {b : Fin 6 → ZMod 3 // co1M0 *ᵥ b = b} = 3 ^ 4 :=
  Certificates.certificate6950.2.2.2.1

theorem eProd_injective : Function.Injective eProd := fun _ _ h =>
  Multiplicative.ofAdd.injective (eHom_injective h)

theorem co1_mem_centralizer_eProd (b : Fin 6 → ZMod 3) :
    eProd b ∈ Subgroup.centralizer ({c 0} : Set GL24) ↔ co1M0 *ᵥ b = b := by
  have hconj : c 0 * eProd b * (c 0)⁻¹ = eProd (co1M0 *ᵥ b) := co1_c_conj_eProd 0 b
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : c 0 * eProd b * (c 0)⁻¹ = eProd b := by
      rw [← h, mul_inv_cancel_right]
    exact (eProd_injective (hconj.symm.trans h1))
  · intro h
    rw [h] at hconj
    calc eProd b * c 0 = (c 0 * eProd b * (c 0)⁻¹) * c 0 := by rw [hconj]
      _ = c 0 * eProd b := by group

theorem co1_card_centralizer : Nat.card ↥(E ⊓ Subgroup.centralizer {c 0}) = 3 ^ 4 := by
  have key : Nat.card {b : Fin 6 → ZMod 3 // co1M0 *ᵥ b = b} =
      Nat.card ↥(E ⊓ Subgroup.centralizer {c 0}) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun b => (⟨eProd b.1, Subgroup.mem_inf.mpr
        ⟨eProd_mem _, (co1_mem_centralizer_eProd _).mpr b.2⟩⟩ :
          ↥(E ⊓ Subgroup.centralizer {c 0}))) ⟨?_, ?_⟩)
    · intro b b' h
      exact Subtype.ext (eProd_injective (by simpa using congrArg Subtype.val h))
    · rintro ⟨x, hxE, hxC⟩
      obtain ⟨bm, hbm⟩ : x ∈ eHom.range := eHom_range ▸ hxE
      refine ⟨⟨bm.toAdd, ?_⟩, Subtype.ext ?_⟩
      · refine (co1_mem_centralizer_eProd _).mp ?_
        have hx' : eProd bm.toAdd = x := hbm
        rw [hx']
        exact hxC
      · exact hbm
  rw [← key, Nat.card_eq_fintype_card, co1_card_fixed]

end CFSG.RankThree.PartOne
