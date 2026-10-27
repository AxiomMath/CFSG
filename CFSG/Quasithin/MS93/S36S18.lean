module

public import CFSG.Quasithin.MS93.S36Inputs
public import CFSG.Quasithin.MS93.ML3Bridge
public import CFSG.Quasithin.MS93.ASKer
public import CFSG.Quasithin.MS93.S32Cent

public section

namespace CFSG.Quasithin.MS93

namespace S36

open Matrix

section Schur

theorem eq_smul_of_mulVec_comm {F : Type} [Field F] (D : (Fin 3 → F) →+ (Fin 3 → F))
    (hD : ∀ g : SL3 F, ∀ w, D ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ D w) :
    ∃ c : F, ∀ w, D w = c • w := by
  have hroot : ∀ {i j : Fin 3}, i ≠ j → ∀ (a : F) (w : Fin 3 → F),
      D (Pi.single i (a * w j)) = Pi.single i (a * D w j) := by
    intro i j hij a w
    have h1 := hD (rootElt i j a) w
    rw [coe_rootElt hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, map_add, Matrix.single_mulVec, Matrix.single_mulVec] at h1
    exact add_left_cancel h1
  have hsing : ∀ {i j : Fin 3}, i ≠ j → ∀ a : F,
      D (Pi.single i a) = Pi.single i (a * D (Pi.single j 1) j) := by
    intro i j hij a
    have := hroot hij a (Pi.single j 1)
    simpa using this
  have hδ : ∀ {i j : Fin 3}, i ≠ j → D (Pi.single i 1) i = D (Pi.single j 1) j := by
    intro i j hij
    have := congrFun (hsing hij 1) i
    simpa using this
  set c : F := D (Pi.single 0 1) 0 with hc
  have hall : ∀ (i : Fin 3) (a : F), D (Pi.single i a) = Pi.single i (a * c) := by
    intro i a
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · rw [hsing (show (0 : Fin 3) ≠ 1 by decide) a, hδ (show (1 : Fin 3) ≠ 0 by decide)]
    · rw [hsing (show (1 : Fin 3) ≠ 0 by decide) a]
    · rw [hsing (show (2 : Fin 3) ≠ 0 by decide) a]
  refine ⟨c, fun w => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  ext k
  simp only [hall, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp [mul_comm]

end Schur

section Trace

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

@[expose] noncomputable def smulLin (y : F) : (Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F) :=
  (y • (LinearMap.id : (Fin 3 → F) →ₗ[F] (Fin 3 → F))).restrictScalars (ZMod 2)

omit [Fintype F] in
theorem smulLin_apply (y : F) (n : Fin 3 → F) : smulLin y n = y • n := rfl

@[expose] noncomputable def finThreeEquiv : (Fin 3 → F) ≃ₗ[ZMod 2] F × F × F where
  toFun n := (n 0, n 1, n 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv n := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

omit [Fintype F] in
theorem finThreeEquiv_apply (n : Fin 3 → F) : finThreeEquiv n = (n 0, n 1, n 2) := rfl

omit [Fintype F] in
theorem finThreeEquiv_symm_apply (p : F × F × F) :
    finThreeEquiv.symm p = ![p.1, p.2.1, p.2.2] := rfl

theorem trace_smulLin (y : F) :
    LinearMap.trace (ZMod 2) (Fin 3 → F) (smulLin y) = Algebra.trace (ZMod 2) F y := by
  have h := LinearMap.trace_conj' (smulLin y) (finThreeEquiv (F := F))
  have he : (finThreeEquiv (F := F)).conj (smulLin y) =
      LinearMap.prodMap (Algebra.lmul (ZMod 2) F y)
        (LinearMap.prodMap (Algebra.lmul (ZMod 2) F y) (Algebra.lmul (ZMod 2) F y)) := by
    ext p <;> simp [LinearEquiv.conj_apply, finThreeEquiv_apply, finThreeEquiv_symm_apply,
      smulLin_apply, smul_eq_mul]
  rw [← h, he, LinearMap.trace_prodMap', LinearMap.trace_prodMap', Algebra.trace_apply]
  have h2 : ∀ t : ZMod 2, t + (t + t) = t := by decide
  exact h2 _

end Trace

section Cocycle

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

@[expose] noncomputable def matLin (g : SL3 F) : (Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F)).restrictScalars (ZMod 2)

omit [Fintype F] in
theorem matLin_apply (g : SL3 F) (n : Fin 3 → F) :
    matLin g n = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ n := rfl

omit [Fintype F] in
theorem matLin_mul_apply (g h : SL3 F) (n : Fin 3 → F) :
    matLin (g * h) n = matLin g (matLin h n) := by
  rw [matLin_apply, matLin_apply, matLin_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]

omit [Fintype F] in
theorem matLin_one_apply (n : Fin 3 → F) : matLin (1 : SL3 F) n = n := by
  rw [matLin_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

omit [Fintype F] in
theorem matLin_smul (g : SL3 F) (y : F) (n : Fin 3 → F) :
    matLin g (y • n) = y • matLin g n := by
  rw [matLin_apply, matLin_apply, Matrix.mulVec_smul]

variable {L : Type} [Group L] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_zero_of_perfect_of_scalar [Group.IsPerfect L]
    (ρ : L → (W →ₗ[ZMod 2] W)) (hρ : ∀ m m' w, ρ (m * m') w = ρ m (ρ m' w))
    (g : L →* SL3 F) (π : W →ₗ[ZMod 2] (Fin 3 → F)) (hπ : Function.Surjective π)
    (j : (Fin 3 → F) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (hjπ : ∀ w, π w = 0 → ∃ n, j n = w)
    (hπρ : ∀ m w, π (ρ m w) = matLin (g m) (π w))
    (hρj : ∀ m n, ρ m (j n) = j (matLin (g m) n))
    {l : L} (hl : g l = 1) {c : F} (hc : ∀ w, ρ l w = w + j (c • π w)) : c = 0 := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π
    (LinearMap.range_eq_top.mpr hπ)
  have hs' : ∀ n, π (s n) = n := fun n => LinearMap.congr_fun hs n
  let Φ : L → ((Fin 3 → F) →ₗ[ZMod 2] W) := fun m => ρ m ∘ₗ s - s ∘ₗ matLin (g m)
  have hΦ : ∀ m n, Φ m n ∈ LinearMap.range j := by
    intro m n
    obtain ⟨b, hb⟩ := hjπ (Φ m n) (by
      simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hπρ, hs', sub_self])
    exact ⟨b, hb⟩
  let B : L → ((Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F)) := fun m =>
    (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ (Φ m).codRestrict _ (hΦ m)
  have hB : ∀ m n, j (B m n) = Φ m n := by
    intro m n
    have := (LinearEquiv.ofInjective j hj).apply_symm_apply ⟨Φ m n, hΦ m n⟩
    exact congrArg Subtype.val this
  let A : L → ((Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F)) := fun m => B m ∘ₗ matLin (g m⁻¹)
  have hginv : ∀ m n, matLin (g m) (matLin (g m⁻¹) n) = n := by
    intro m n
    rw [← matLin_mul_apply, ← map_mul, mul_inv_cancel, map_one, matLin_one_apply]
  have hginv' : ∀ m n, matLin (g m⁻¹) (matLin (g m) n) = n := by
    intro m n
    rw [← matLin_mul_apply, ← map_mul, inv_mul_cancel, map_one, matLin_one_apply]
  have hA : ∀ m m' n, A (m * m') n = A m n + matLin (g m) (A m' (matLin (g m⁻¹) n)) := by
    intro m m' n
    apply hj
    set n' := matLin (g m'⁻¹) (matLin (g m⁻¹) n) with hn'
    set n'' := matLin (g m⁻¹) n with hn''
    have e1 : matLin (g (m * m')⁻¹) n = n' := by
      rw [_root_.mul_inv_rev, map_mul, matLin_mul_apply]
    have e2 : matLin (g (m * m')) n' = n := by
      rw [map_mul, matLin_mul_apply, hn', hginv, hginv]
    have e3 : matLin (g m') n' = n'' := by rw [hn', hginv]
    have e4 : ρ m' (s n') = j (B m' n') + s n'' := by
      rw [hB]
      simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, e3]
      abel
    have e5 : ρ m (s n'') = j (B m n'') + s n := by
      rw [hB]
      simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, hn'', hginv]
      abel
    show j (B (m * m') (matLin (g (m * m')⁻¹) n)) =
      j (B m (matLin (g m⁻¹) n) + matLin (g m) (B m' (matLin (g m'⁻¹) (matLin (g m⁻¹) n))))
    rw [e1, ← hn', ← hn'', hB, map_add, ← hρj]
    simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, e2, hρ, e4, map_add, e5]
    abel
  have hψ : ∀ (x : F) (m m' : L),
      LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A (m * m')) =
        LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A m) +
          LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A m') := by
    intro x m m'
    have hsplit : smulLin x ∘ₗ A (m * m') = smulLin x ∘ₗ A m +
        matLin (g m) ∘ₗ (smulLin x ∘ₗ A m') ∘ₗ matLin (g m⁻¹) := by
      refine LinearMap.ext fun n => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, hA, smulLin_apply, smul_add,
        matLin_smul]
    rw [hsplit, map_add]
    congr 1
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
      ← LinearMap.comp_assoc]
    congr 1
    have : matLin (g m⁻¹) ∘ₗ matLin (g m) = LinearMap.id :=
      LinearMap.ext fun n => hginv' m n
    rw [this, LinearMap.id_comp]
  have hzero : ∀ x : F, LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A l) = 0 := by
    intro x
    let f : L →* Multiplicative (ZMod 2) :=
      { toFun := fun m => Multiplicative.ofAdd (LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A m))
        map_one' := by
          have h1 := hψ x 1 1
          rw [mul_one] at h1
          have : LinearMap.trace (ZMod 2) _ (smulLin x ∘ₗ A 1) = 0 := by
            have h2 : ∀ t : ZMod 2, t = t + t → t = 0 := by decide
            exact h2 _ h1
          simp [this]
        map_mul' := fun m m' => by
          rw [hψ]
          rfl }
    have hker : f.ker = ⊤ := by
      rw [eq_top_iff, ← (Group.IsPerfect.commutator_eq_top (G := L))]
      exact Abelianization.commutator_subset_ker f
    have hl' : l ∈ f.ker := by rw [hker]; exact Subgroup.mem_top l
    exact hl'
  have hAl : A l = smulLin c := by
    refine LinearMap.ext fun n => ?_
    have e : A l n = B l n := by
      show B l (matLin (g l⁻¹) n) = B l n
      rw [map_inv, hl, inv_one, matLin_one_apply]
    rw [e]
    have : j (B l n) = j (c • n) := by
      rw [hB]
      simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, hl, matLin_one_apply, hc, hs']
      abel
    rw [hj this]
    rfl
  have htr : ∀ x : F, Algebra.trace (ZMod 2) F (x * c) = 0 := by
    intro x
    have := hzero x
    rw [hAl] at this
    have hxc : smulLin x ∘ₗ smulLin c = smulLin (x * c) :=
      LinearMap.ext fun n => by simp [smulLin_apply, mul_smul]
    rw [hxc, trace_smulLin] at this
    exact this
  by_contra hc0
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  have := htr (y * c⁻¹)
  rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one, hy] at this
  exact one_ne_zero this

theorem eq_of_perfect_of_commute [Group.IsPerfect L]
    (ρ : L → (W →ₗ[ZMod 2] W)) (hρ : ∀ m m' w, ρ (m * m') w = ρ m (ρ m' w))
    (g : L →* SL3 F) (hg : Function.Surjective g)
    (π : W →ₗ[ZMod 2] (Fin 3 → F)) (hπ : Function.Surjective π)
    (j : (Fin 3 → F) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (hjπ : ∀ w, π w = 0 → ∃ n, j n = w)
    (hπρ : ∀ m w, π (ρ m w) = matLin (g m) (π w))
    (hρj : ∀ m n, ρ m (j n) = j (matLin (g m) n))
    {l : L} (hl : g l = 1) (hcomm : ∀ m w, ρ l (ρ m w) = ρ m (ρ l w)) (w : W) :
    ρ l w = w := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π
    (LinearMap.range_eq_top.mpr hπ)
  have hs' : ∀ n, π (s n) = n := fun n => LinearMap.congr_fun hs n
  have hπl : ∀ w, π (ρ l w) = π w := fun w => by rw [hπρ, hl, matLin_one_apply]
  have hjl : ∀ n, ρ l (j n) = j n := fun n => by rw [hρj, hl, matLin_one_apply]
  let E : W →ₗ[ZMod 2] W := ρ l - LinearMap.id
  have hE : ∀ w, E w ∈ LinearMap.range j := by
    intro w
    obtain ⟨b, hb⟩ := hjπ (E w) (by simp [E, hπl])
    exact ⟨b, hb⟩
  let D₀ : W →ₗ[ZMod 2] (Fin 3 → F) :=
    (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ E.codRestrict _ hE
  have hD₀ : ∀ w, j (D₀ w) = ρ l w - w := by
    intro w
    have := (LinearEquiv.ofInjective j hj).apply_symm_apply ⟨E w, hE w⟩
    exact congrArg Subtype.val this
  have hD₀j : ∀ n, D₀ (j n) = 0 := fun n => hj (by rw [hD₀, hjl, sub_self, map_zero])
  have hD₀π : ∀ w, D₀ w = D₀ (s (π w)) := by
    intro w
    obtain ⟨b, hb⟩ := hjπ (w - s (π w)) (by rw [map_sub, hs', sub_self])
    have : w = s (π w) + j b := by rw [hb]; abel
    conv_lhs => rw [this]
    rw [map_add, hD₀j, add_zero]
  let D : (Fin 3 → F) →+ (Fin 3 → F) := (D₀ ∘ₗ s).toAddMonoidHom
  have hDeq : ∀ (m : L) (n : Fin 3 → F), D (matLin (g m) n) = matLin (g m) (D n) := by
    intro m n
    show D₀ (s (matLin (g m) n)) = matLin (g m) (D₀ (s n))
    have h1 : D₀ (s (matLin (g m) n)) = D₀ (ρ m (s n)) := by
      rw [hD₀π (ρ m (s n)), hπρ, hs']
    rw [h1]
    apply hj
    rw [hD₀, ← hρj, hD₀, map_sub, hcomm]
  obtain ⟨c, hc⟩ := eq_smul_of_mulVec_comm D fun g' w' => by
    obtain ⟨m, rfl⟩ := hg g'
    exact hDeq m w'
  have hcw : ∀ w, ρ l w = w + j (c • π w) := by
    intro w
    have h1 : j (D₀ w) = j (c • π w) := by
      rw [hD₀π, ← hc]
      rfl
    rw [← h1, hD₀]
    abel
  have hc0 := eq_zero_of_perfect_of_scalar ρ hρ g π hπ j hj hjπ hπρ hρj hl hcw
  rw [hcw, hc0, zero_smul, map_zero, add_zero]

end Cocycle

section Natural

variable {G : Type} [Group G]

open CFSG.Quasithin

theorem conj_mul_inv_mem_of_eq_one {A V Z : Subgroup G} {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ}
    (hnat : IsSumOfNaturalModulesVia A V Z α false 1) {a : ↥A} (ha : α a = 1) {v : G}
    (hv : v ∈ V) : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ Z := by
  obtain ⟨hAV, -, β, -, hβk, hβeq⟩ := hnat
  have hv' : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp hv
  have h0 := hβeq a ⟨v, hv⟩ ⟨_, hv'⟩ rfl 0
  rw [ha] at h0
  have hβ : β ⟨_, hv'⟩ = β ⟨v, hv⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [h0]
    simp [moduleAct]
  have hmem : (⟨_, hv'⟩ * (⟨v, hv⟩ : ↥V)⁻¹ : ↥V) ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

end Natural

section Kernel

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

theorem ker_le_pCore_of_natNat (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥L →* ↥(StatedSL 3 F)} (hV2 : ∀ v ∈ Vq M L, v ^ 2 = 1)
    (hU : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1)
    (hVU : IsSumOfNaturalModulesVia L (Vq M L) (Uq M T L) a false 1) :
    a.ker ≤ CFSG.pCore 2 ↥L := by
  apply ker_le_pCore_of_odd a
  intro ℓ hℓ hodd
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hUV : Uq M T L ≤ Vq M L := hVU.2.1
  have hℓU : ∀ u ∈ Uq M T L, (ℓ : G) * u = u * (ℓ : G) := by
    intro u hu
    have h1 := conj_mul_inv_mem_of_eq_one hU hℓ hu
    rw [Subgroup.mem_bot] at h1
    calc (ℓ : G) * u = (ℓ : G) * u * (ℓ : G)⁻¹ * u⁻¹ * (u * ℓ) := by group
      _ = u * ℓ := by rw [h1, one_mul]
  have hcomm := commute_of_commutator_mem hodd' hℓU (fun u hu => ⟨1, by simpa using hV2 u (hUV hu)⟩)
    (fun v hv => conj_mul_inv_mem_of_eq_one hVU hℓ hv)
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hcomm)

theorem ker_trivial_of_natNat (h : PUHyp M T L) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {a : ↥L →* ↥(StatedSL 3 F)} (ha : Function.Surjective a)
    (hVc : ∀ v ∈ Vq M L, ∀ w ∈ Vq M L, v * w = w * v) (hV2 : ∀ v ∈ Vq M L, v ^ 2 = 1)
    (hU : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1)
    (hVU : IsSumOfNaturalModulesVia L (Vq M L) (Uq M T L) a false 1) :
    ∀ l : ↥L, a l = 1 → ∀ v ∈ Vq M L, (l : G) * v * (l : G)⁻¹ = v := by
  intro l hl v hv
  have hkerP := ker_le_pCore_of_natNat h hV2 hU hVU
  have hlQ : (l : G) ∈ pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
      (mem_pCoreOf_of_mem_pCore_two (hkerP hl))
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  let _ : CharP F 2 := FFC.charP_two_of_card_pow hF'
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  set V := Vq M L with hVdef
  set U := Uq M T L with hUdef
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun x y => Subtype.ext (hVc x x.2 y y.2) }
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hV2 _ (Additive.toMul x).2)
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  obtain ⟨hLU, -, βU, hβUs, hβUk, hβUeq⟩ := hU
  obtain ⟨hLV, hUV, βV, hβVs, hβVk, hβVeq⟩ := hVU
  have hβUi : Function.Injective βU := by
    rw [← MonoidHom.ker_eq_bot_iff, hβUk, Subgroup.bot_subgroupOf]
  let eU : ↥U ≃* Multiplicative (Fin 1 → Fin 3 → F) := MulEquiv.ofBijective βU ⟨hβUi, hβUs⟩
  have hcoord : ∀ x y : Multiplicative (Fin 1 → Fin 3 → F),
      Multiplicative.toAdd x 0 = Multiplicative.toAdd y 0 → x = y := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hxy
  let ρ : ↥L → (Additive ↥V →ₗ[ZMod 2] Additive ↥V) := fun m =>
    ((MulEquiv.toAdditive (conjOn hLV m)).toAddMonoidHom).toZModLinearMap 2
  have hρapp : ∀ m w, ρ m w = Additive.ofMul (conjOn hLV m (Additive.toMul w)) := fun _ _ => rfl
  let π₀ : Additive ↥V →+ (Fin 3 → F) :=
    AddMonoidHom.mk' (fun w => Multiplicative.toAdd (βV (Additive.toMul w)) 0) fun w w' => by
      simp only [toMul_add, map_mul, toAdd_mul, Pi.add_apply]
  let π : Additive ↥V →ₗ[ZMod 2] (Fin 3 → F) := π₀.toZModLinearMap 2
  have hπapp : ∀ w, π w = Multiplicative.toAdd (βV (Additive.toMul w)) 0 := fun _ => rfl
  let j₀ : (Fin 3 → F) →+ Additive ↥V :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (Subgroup.inclusion hUV
        (eU.symm (Multiplicative.ofAdd (fun _ => x))))) fun x y => by
      rw [← ofMul_mul, ← map_mul, ← map_mul]
      rfl
  let j : (Fin 3 → F) →ₗ[ZMod 2] Additive ↥V := j₀.toZModLinearMap 2
  have hjapp : ∀ x, j x = Additive.ofMul (Subgroup.inclusion hUV
      (eU.symm (Multiplicative.ofAdd (fun _ => x)))) := fun _ => rfl
  have hβUj : ∀ x, βU (eU.symm (Multiplicative.ofAdd (fun _ => x))) =
      Multiplicative.ofAdd (fun _ => x) := fun x => eU.apply_symm_apply _
  have hmat : ∀ m : ↥L, moduleAct false (a m : Matrix.GeneralLinearGroup (Fin 3) F) =
      ((toSL3 a m : SL3 F) : Matrix (Fin 3) (Fin 3) F) := fun m => by
    rw [coe_toSL3]
    rfl
  have hρ : ∀ m m' w, ρ (m * m') w = ρ m (ρ m' w) := by
    intro m m' w
    rw [hρapp, hρapp, hρapp, map_mul]
    rfl
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨u, hu⟩ := hβVs (Multiplicative.ofAdd (fun _ => x))
    exact ⟨Additive.ofMul u, by rw [hπapp]; simp [hu]⟩
  have hj : Function.Injective j := by
    intro x y hxy
    rw [hjapp, hjapp] at hxy
    have h1 := Subgroup.inclusion_injective hUV (Additive.ofMul.injective hxy)
    have h2 := congrArg (fun z : Multiplicative (Fin 1 → Fin 3 → F) => Multiplicative.toAdd z 0)
      (eU.symm.injective h1)
    simpa using h2
  have hjπ : ∀ w, π w = 0 → ∃ x, j x = w := by
    intro w hw
    have h1 : βV (Additive.toMul w) = 1 := hcoord _ _ (by rw [← hπapp, hw]; rfl)
    have h2 : Additive.toMul w ∈ U.subgroupOf V := by rw [← hβVk]; exact h1
    rw [Subgroup.mem_subgroupOf] at h2
    refine ⟨Multiplicative.toAdd (βU ⟨_, h2⟩) 0, ?_⟩
    rw [hjapp]
    apply Additive.toMul.injective
    apply Subtype.ext
    have h3 : eU.symm (Multiplicative.ofAdd (fun _ => Multiplicative.toAdd (βU ⟨_, h2⟩) 0)) =
        ⟨_, h2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact hcoord _ _ rfl
    rw [h3]
    rfl
  have hπρ : ∀ m w, π (ρ m w) = matLin (toSL3 a m) (π w) := by
    intro m w
    rw [hπapp, hπapp, hρapp, matLin_apply, ← hmat]
    exact hβVeq m (Additive.toMul w) _ (coe_conjOn_apply hLV m _) 0
  have hρj : ∀ m x, ρ m (j x) = j (matLin (toSL3 a m) x) := by
    intro m x
    rw [hρapp, hjapp, hjapp]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, coe_conjOn_apply, Subgroup.coe_inclusion]
    set u := eU.symm (Multiplicative.ofAdd (fun _ => x)) with hu
    have hu' : (m : G) * u * (m : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU m.2) u).mp u.2
    have h1 : eU.symm (Multiplicative.ofAdd (fun _ => matLin (toSL3 a m) x)) = ⟨_, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply hcoord
      show _ = Multiplicative.toAdd (βU ⟨_, hu'⟩) 0
      rw [hβUeq m u ⟨_, hu'⟩ rfl 0, hmat, hβUj]
      rfl
    rw [h1]
  have hl' : toSL3 a l = 1 := by
    simp [toSL3, hl]
  have hcomm : ∀ m w, ρ l (ρ m w) = ρ m (ρ l w) := by
    intro m w
    rw [hρapp, hρapp, hρapp, hρapp]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, coe_conjOn_apply]
    set x := ((Additive.toMul w : ↥V) : G)
    have hx : x ∈ V := (Additive.toMul w).2
    have hc : ⁅(l : G), (m : G)⁆ ∈ V := Subgroup.commutator_mem_commutator hlQ m.2
    have hmx : (m : G) * ((l : G) * x * (l : G)⁻¹) * (m : G)⁻¹ ∈ V := by
      have h1 : (l : G) * x * (l : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV l.2) x).mp hx
      exact (Subgroup.mem_normalizer_iff.mp (hLV m.2) _).mp h1
    have key := hVc _ hc _ hmx
    rw [commutatorElement_def] at key
    calc (l : G) * ((m : G) * x * (m : G)⁻¹) * (l : G)⁻¹ =
        ((l : G) * (m : G) * (l : G)⁻¹ * (m : G)⁻¹) *
          ((m : G) * ((l : G) * x * (l : G)⁻¹) * (m : G)⁻¹) *
            ((l : G) * (m : G) * (l : G)⁻¹ * (m : G)⁻¹)⁻¹ := by group
      _ = (m : G) * ((l : G) * x * (l : G)⁻¹) * (m : G)⁻¹ := by
          rw [key]
          group
  have hfix := eq_of_perfect_of_commute ρ hρ (toSL3 a) (toSL3_surjective ha) π hπ j hj hjπ hπρ
    hρj hl' hcomm (Additive.ofMul ⟨v, hv⟩)
  rw [hρapp] at hfix
  have := congrArg (fun w : Additive ↥V => ((Additive.toMul w : ↥V) : G)) hfix
  simpa [coe_conjOn_apply] using this

theorem vq_elem_of_frattiniIn (h : PUHyp M T L) (hΦ : frattiniIn (Vq M L) = ⊥) :
    (∀ v ∈ Vq M L, ∀ w ∈ Vq M L, v * w = w * v) ∧ ∀ v ∈ Vq M L, v ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(Vq M L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (Vq_le_pCoreOf h.L_le)
  have : Fact (IsPGroup 2 ↥(Vq M L)) := ⟨h2⟩
  have hΦ' : frattini ↥(Vq M L) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Vq M L).subtype_injective).mp hΦ
  refine ⟨fun v hv w hw => ?_, fun v hv => ?_⟩
  · have hc := CFSG.commutator_le_frattini_of_isPGroup (R := ↥(Vq M L)) (p := 2)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨v, hv⟩ : ↥(Vq M L)))
        (Subgroup.mem_top (⟨w, hw⟩ : ↥(Vq M L))))
    rw [hΦ', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact congrArg Subtype.val hc
  · have hp := CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥(Vq M L)) (p := 2)
      (⟨v, hv⟩ : ↥(Vq M L))
    rw [hΦ', Subgroup.mem_bot] at hp
    simpa using congrArg Subtype.val hp

end Kernel

end S36

open S36

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem s18_of (h18 : MS18Int) : S18 := by
  intro G _ _ M T L h _ _ hD
  obtain ⟨hΦ, -, n, F, _, _, a, hF, ha, hU, hVU⟩ := hD
  obtain ⟨hVc, hV2⟩ := vq_elem_of_frattiniIn h hΦ
  have hker := ker_trivial_of_natNat h hF ha hVc hV2 hU hVU
  have hkerP : IsPGroup 2 ↥(toSL3 a).ker := by
    have h1 : (toSL3 a).ker = a.ker := by
      ext x
      simp [toSL3, MonoidHom.mem_ker]
    rw [h1]
    exact (isPGroup_pCore_two L).to_le (ker_le_pCore_of_natNat h hV2 hU hVU)
  have hsq : SQTKGroup (SL3 F) :=
    InternalSec.sqtkGroup_of_surjective (toSL3 a) (toSL3_surjective ha) hkerP
      (InternalSec.sqtkGroup_mono h.sqtk h.L_le)
  exact ⟨n, F, inferInstance, inferInstance, a, hF, ha, h18 hF ha hVc hV2 hker hsq hU hVU⟩

end CFSG.Quasithin.MS93
