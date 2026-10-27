module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterNormalForm
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangDatum
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangSetup
public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour
public import CFSG.LocalAnalysis.StandardType.GGExcPRankBound
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.ExcMaxToral
open CFSG.Open (IsElemAbelian)

open CFSG.LieType.Steinberg.Adjoint

private theorem ggPA44_iform_foldl_reflect
    (l : List ℕ) (v : Fin Tag.F4.rank → ℤ) :
    iform (l.foldl (fun v i => reflect Tag.F4 (Tag.F4.idx i) v) v)
      (l.foldl (fun v i => reflect Tag.F4 (Tag.F4.idx i) v) v) = iform v v := by
  induction l generalizing v with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    exact (ih (reflect Tag.F4 (Tag.F4.idx i) v)).trans (iform_reflect (Tag.F4.idx i) v v)

private theorem ggPA44_symmetrizer_two_iff (j : Fin Tag.F4.rank) :
    Tag.F4.symmetrizer j j = 2 ↔ j = 0 ∨ j = 1 := by
  fin_cases j <;> decide

private theorem ggPA44_seed_long_of_iform
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (hlong : iform α α = 4) : (pinnedData Tag.F4 α).1 = 0 ∨ (pinnedData Tag.F4 α).1 = 1 := by
  have hfold := foldl_reflect_pinnedData (τ := Tag.F4) hα
  have hif : iform (Pi.single (pinnedData Tag.F4 α).1 1 : Fin Tag.F4.rank → ℤ)
      (Pi.single (pinnedData Tag.F4 α).1 1) = 4 := by
    have h1 := ggPA44_iform_foldl_reflect (pinnedData Tag.F4 α).2.1
      (Pi.single (pinnedData Tag.F4 α).1 1)
    rw [hfold] at h1
    exact h1.symm.trans hlong
  have hs : Tag.F4.symmetrizer (pinnedData Tag.F4 α).1 (pinnedData Tag.F4 α).1 = 2 := by
    have h2 := iform_single_single (τ := Tag.F4) (pinnedData Tag.F4 α).1
    rw [h2] at hif
    omega
  exact (ggPA44_symmetrizer_two_iff _).1 hs

private theorem ggPA44_not_isRoot_add_two_smul_F4_long
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    {j : Fin Tag.F4.rank}
    (hj : iform (Pi.single j 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1) = 4)
    (h₁ : α ≠ Pi.single j 1) (h₂ : α ≠ -Pi.single j 1) :
    ¬ IsRoot Tag.F4 (α + (2 : ℤ) • Pi.single j 1) := by
  intro h
  have h' : IsRoot Tag.F4 (1 • α + 2 • Pi.single j 1) := by
    have e : (1 • α + 2 • Pi.single j 1 : Fin Tag.F4.rank → ℤ) =
        α + (2 : ℤ) • Pi.single j 1 := by
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, one_smul, smul_eq_mul, Nat.cast_ofNat]
      ring
    rw [e]
    exact h
  rcases exponent_pair_cases noG2_F4 hα (IsRoot.basis j) h₁ h₂ (le_refl 1) (by norm_num) h' with
    ⟨-, hj1⟩ | ⟨-, hj2, -, hb2, -⟩ | ⟨hi2, -, -, -, -⟩
  · omega
  · rw [hj] at hb2
    omega
  · omega

private theorem ggPA44_exists_cartan_neighbour_F4_long (j : Fin Tag.F4.rank)
    (hj : j = 0 ∨ j = 1) : ∃ l : Fin Tag.F4.rank, (Tag.F4.cartan l j).natAbs = 1 := by
  rcases hj with rfl | rfl
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

private theorem ggPA44_xCoeff_two_range_le_F4_long
    {L : Type} [Field L] (j : Fin Tag.F4.rank)
    (hj : j = 0 ∨ j = 1) :
    Module.finrank L (LinearMap.range (xCoeff Tag.F4 L j 2)) ≤ 1 := by
  have hjlong : iform (Pi.single j 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1) = 4 := by
    rcases hj with rfl | rfl <;> decide
  have hw : (rootVec Tag.F4 L (Pi.single j 1) : RootModule Tag.F4 L) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot' (isRoot_single Tag.F4 j)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have hle : LinearMap.range (xCoeff Tag.F4 L j 2) ≤
      Submodule.span L {rootVec Tag.F4 L (Pi.single j 1)} := by
    rintro _ ⟨v, rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => rw [map_add]; exact add_mem hv hw
    | single b c =>
      rw [← Finsupp.smul_single_one, map_smul]
      refine Submodule.smul_mem _ _ ?_
      rcases b with l | ⟨α, hα⟩
      · change xCoeff Tag.F4 L j 2 (hVec Tag.F4 L l) ∈ _
        rw [xCoeff_hVec]
        simp
      · rw [← rootVec_eq_single_of_isRoot' hα]
        by_cases h₁ : α = Pi.single j 1
        · subst h₁
          rw [xCoeff_rootVec_single]
          simp
        by_cases h₂ : α = -Pi.single j 1
        · subst h₂
          rw [xCoeff_rootVec_neg_single]
          simp [Submodule.mem_span_singleton_self]
        have hnr := ggPA44_not_isRoot_add_two_smul_F4_long hα hjlong h₁ h₂
        rw [xCoeff_rootVec_of_ne j 2 hα h₁ h₂,
          rootVec_eq_zero_of_not_isRoot'
            (β := α + ((2 : ℕ) : ℤ) • Pi.single j 1) (by simpa only [Nat.cast_ofNat] using hnr),
          smul_zero]
        exact zero_mem _
  calc Module.finrank L (LinearMap.range (xCoeff Tag.F4 L j 2)) ≤
        Module.finrank L (Submodule.span L {rootVec Tag.F4 L (Pi.single j 1)}) :=
      Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw

private theorem ggPA44_xCoeff_one_range_ge_F4_long
    {L : Type} [Field L] (j : Fin Tag.F4.rank)
    (hj : j = 0 ∨ j = 1) :
    2 ≤ Module.finrank L (LinearMap.range (xCoeff Tag.F4 L j 1)) := by
  obtain ⟨l, hl⟩ := ggPA44_exists_cartan_neighbour_F4_long j hj
  set w1 : RootModule Tag.F4 L :=
    Finsupp.single (Sum.inr ⟨Pi.single j 1, isRoot_single Tag.F4 j⟩) 1 with hw1d
  set w2 : RootModule Tag.F4 L := Finsupp.single (Sum.inl j) 1 with hw2d
  have hw1 : xCoeff Tag.F4 L j 1 (hVec Tag.F4 L l) = w1 := by
    rw [xCoeff_hVec]
    simp only [one_ne_zero, ↓reduceIte, hl, Nat.cast_one, one_smul]
    exact rootVec_eq_single_of_isRoot' (isRoot_single Tag.F4 j)
  have hw2 : xCoeff Tag.F4 L j 1 (rootVec Tag.F4 L (-Pi.single j 1)) = w2 := by
    rw [xCoeff_rootVec_neg_single]
    simp only [one_ne_zero, ↓reduceIte]
    rfl
  have hli : LinearIndependent L ![w1, w2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun v : RootModule Tag.F4 L =>
      v (Sum.inr ⟨Pi.single j 1, isRoot_single Tag.F4 j⟩)) hst
    have h2 := congrArg (fun v : RootModule Tag.F4 L => v (Sum.inl j)) hst
    simp [hw1d, hw2d] at h1 h2
    exact ⟨h1, h2⟩
  have hsub : Submodule.span L (Set.range ![w1, w2]) ≤
      LinearMap.range (xCoeff Tag.F4 L j 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨hVec Tag.F4 L l, hw1⟩
    · exact ⟨rootVec Tag.F4 L (-Pi.single j 1), hw2⟩
  have := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli] at this
  simpa using this

private theorem ggPA44_pinnedX_expand_F4_long
    {L : Type} [Field L] {α : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot Tag.F4 α) (hlong : iform α α = 4) :
    ∃ A B : Module.End L (RootModule Tag.F4 L), A ≠ 0 ∧
      (2 ≤ Module.finrank L (LinearMap.range A) ∧
        Module.finrank L (LinearMap.range B) ≤ 1) ∧ ∀ c : L,
      ((pinnedX Tag.F4 L α c : (Module.End L (RootModule Tag.F4 L))ˣ) :
        Module.End L (RootModule Tag.F4 L)) = 1 + c • A + c ^ 2 • B := by
  have hj01 : (pinnedData Tag.F4 α).1 = 0 ∨ (pinnedData Tag.F4 α).1 = 1 :=
    ggPA44_seed_long_of_iform hα hlong
  set j := (pinnedData Tag.F4 α).1 with hj
  set ε := (pinnedData Tag.F4 α).2.2 with hε
  set W := pinnedWeyl Tag.F4 L α with hW
  set e : L := (ε : L) with he
  have hεs : ε = 1 ∨ ε = -1 := pinnedData_sign Tag.F4 α
  have he0 : e ≠ 0 := by
    rcases hεs with h | h <;> simp [he, h]
  have hj' : j = 0 ∨ j = 1 := by rw [hj]; exact hj01
  have hx : ∀ c : L, xOp Tag.F4 L j c =
      1 + c • xCoeff Tag.F4 L j 1 + c ^ 2 • xCoeff Tag.F4 L j 2 := by
    intro c
    rw [xOp_eq_sum_xCoeff_entryDegreeBound, entryDegreeBound_of_ne_G2 (τ := Tag.F4) (by decide)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul,
      xCoeff_zero_eq_one (τ := Tag.F4) (by decide), pow_one]
  refine ⟨e • ((W : Module.End L (RootModule Tag.F4 L)) * xCoeff Tag.F4 L j 1 *
      ((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L))),
    e ^ 2 • ((W : Module.End L (RootModule Tag.F4 L)) * xCoeff Tag.F4 L j 2 *
      ((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L))),
    ?_, ?_, fun c => ?_⟩
  · intro h0
    have h1 : ((W : Module.End L (RootModule Tag.F4 L)) * xCoeff Tag.F4 L j 1 *
        ((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L))) = 0
        := by
      rcases smul_eq_zero.1 h0 with h | h
      · exact absurd h he0
      · exact h
    have h2 : xCoeff Tag.F4 L j 1 = 0 := by
      have := congrArg (fun m => ((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) :
        Module.End L (RootModule Tag.F4 L)) * m * (W : Module.End L (RootModule Tag.F4 L))) h1
      simpa [mul_assoc] using this
    exact xCoeff_one_ne_zero (τ := Tag.F4) j h2
  · constructor
    · rw [finrank_range_smul_eq he0, finrank_range_conj_eq]
      exact ggPA44_xCoeff_one_range_ge_F4_long j hj'
    · refine (finrank_range_smul_le _ _).trans ?_
      refine (finrank_range_conj_le W _).trans ?_
      exact ggPA44_xCoeff_two_range_le_F4_long j hj'
  · have hp : ((pinnedX Tag.F4 L α c : (Module.End L (RootModule Tag.F4 L))ˣ) :
        Module.End L (RootModule Tag.F4 L)) =
        (W : Module.End L (RootModule Tag.F4 L)) * xOp Tag.F4 L j (e * c) *
          ((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L)) := by
      change ((W * xUnit Tag.F4 L j (ε • c) * W⁻¹ :
        (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L)) = _
      rw [Units.val_mul, Units.val_mul, coe_xUnit]
      congr 3
      simp [he, mul_comm]
    rw [hp, hx (e * c)]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_one]
    have hWW : (W : Module.End L (RootModule Tag.F4 L)) *
((W⁻¹ : (Module.End L (RootModule Tag.F4 L))ˣ) : Module.End L (RootModule Tag.F4 L)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hWW]
    congr 2 <;> congr 1 <;> ring

private theorem ggPA44_conj_map_pinnedX_expand_F4_long
    {L : Type} [Field L] (ψ : L →+* L) (g : ModGL Tag.F4 L)
    {μ : L} (hμ : μ ≠ 0) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (hlong : iform α α = 4) :
    ∃ a b : Module.End L (RootModule Tag.F4 L), a ≠ 0 ∧
      (2 ≤ Module.finrank L (LinearMap.range a) ∧
        Module.finrank L (LinearMap.range b) ≤ 1) ∧ ∀ c : L,
      ((Units.map (entrywiseHom ψ) (g * pinnedX Tag.F4 L α (μ * c) * g⁻¹) : ModGL Tag.F4 L) :
        Module.End L (RootModule Tag.F4 L)) = 1 + (ψ c) • a + (ψ c) ^ 2 • b := by
  obtain ⟨A, B, hA, hrk, hAB⟩ := ggPA44_pinnedX_expand_F4_long (L := L) hα hlong
  set g' : ModGL Tag.F4 L := Units.map (entrywiseHom ψ) g with hg'
  have hgg : (g' : Module.End L (RootModule Tag.F4 L)) * ((g'⁻¹ : ModGL Tag.F4 L) :
      Module.End L (RootModule Tag.F4 L)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hψμ : ψ μ ≠ 0 := fun h => hμ ((map_eq_zero ψ).1 h)
  refine ⟨ψ μ • ((g' : Module.End L (RootModule Tag.F4 L)) * A *
      ((g'⁻¹ : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L))),
    (ψ μ) ^ 2 • ((g' : Module.End L (RootModule Tag.F4 L)) * B *
      ((g'⁻¹ : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L))), ?_, ?_, fun c => ?_⟩
  · intro h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact hψμ h
    · apply hA
      have := congrArg (fun m => ((g'⁻¹ : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L))
          * m *
        (g' : Module.End L (RootModule Tag.F4 L))) h
      simpa [mul_assoc] using this
  · constructor
    · rw [finrank_range_smul_eq hψμ, finrank_range_conj_eq]
      exact hrk.1
    · refine (finrank_range_smul_le _ _).trans ?_
      refine (finrank_range_conj_le g' _).trans ?_
      exact hrk.2
  · rw [map_mul, map_mul, map_inv, entrywise_pinnedX_units, ← hg']
    rw [Units.val_mul, Units.val_mul, hAB, map_mul]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_one, hgg]
    congr 2 <;> congr 1 <;> ring

private theorem ggPA44_exists_factor_data_F4_long
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.F4 L p)
    (ψ : L →+* L) (zu : ModGL Tag.F4 L) {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ)
    (k : ℕ) (hγlong : iform ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ) = 4) :
    ∃ a b a' b' : Module.End L (RootModule Tag.F4 L), a ≠ 0 ∧ a' ≠ 0 ∧
      (2 ≤ Module.finrank L (LinearMap.range a') ∧
        Module.finrank L (LinearMap.range b) ≤ 1) ∧
      (∀ t : L, ((iterHom S.D.step k (zu * pinnedX Tag.F4 L γ t * zu⁻¹) : ModGL Tag.F4 L) :
        Module.End L (RootModule Tag.F4 L)) = 1 + (t ^ (S.D.q ^ k)) • a +
          (t ^ (S.D.q ^ k)) ^ 2 • b) ∧
      (∀ t : L, ((Units.map (entrywiseHom ψ) (iterHom S.D.step k
        (zu * pinnedX Tag.F4 L γ t * zu⁻¹)) : ModGL Tag.F4 L) :
          Module.End L (RootModule Tag.F4 L)) =
          1 + (ψ (t ^ (S.D.q ^ k))) • a' + (ψ (t ^ (S.D.q ^ k))) ^ 2 • b') := by
  have hγk : IsRoot Tag.F4 ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ) := by
    clear hγlong
    induction k with
    | zero => simpa using hγ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (S.frob.isRoot_iff _).2 ih
  obtain ⟨μ, hμ, hμe⟩ := iter_step_pinnedX S k hγ
  have hit : ∀ t : L, iterHom S.D.step k (zu * pinnedX Tag.F4 L γ t * zu⁻¹) =
      iterHom S.D.step k zu * pinnedX Tag.F4 L ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ)
        (μ * t ^ (S.D.q ^ k)) * (iterHom S.D.step k zu)⁻¹ := by
    intro t
    rw [map_mul, map_mul, map_inv, iterHom_eq_iterate, iterHom_eq_iterate, hμe]
  obtain ⟨a, b, ha, hrk, hab⟩ := ggPA44_conj_map_pinnedX_expand_F4_long (RingHom.id L)
    (iterHom S.D.step k zu) hμ hγk hγlong
  obtain ⟨a', b', ha', hrk', hab'⟩ := ggPA44_conj_map_pinnedX_expand_F4_long ψ
    (iterHom S.D.step k zu) hμ hγk hγlong
  refine ⟨a, b, a', b', ha, ha', ⟨hrk'.1, hrk.2⟩, fun t => ?_, fun t => ?_⟩
  · rw [hit]
    have h1 := hab (t ^ (S.D.q ^ k))
    have e : ∀ x : ModGL Tag.F4 L, Units.map (entrywiseHom (RingHom.id L)) x = x :=
      fun x => Units.ext (entrywise_id _)
    rw [e] at h1
    simpa using h1
  · rw [hit, hab' (t ^ (S.D.q ^ k))]

private theorem ggPA44_iform_iterate_rho
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.F4 L p)
    (γ : Fin Tag.F4.rank → ℤ) (k : ℕ) :
    iform ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] γ) = iform γ γ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', S.frob.iform_eq, ih]

private theorem ggPA44_outer_false_of_norm_fixed_F4
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.F4 L p)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin Tag.F4.rank → ℤ} (hθr : IsRoot Tag.F4 θ) (hθlong : iform θ θ = 4)
    (zu : ModGL Tag.F4 L)
    (hy : ∀ t : L, zu * pinnedX Tag.F4 L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0)
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (r ^ (f * s)))
    (hrt : ∀ t : L, σ t = t → (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hj0 : 0 < j) (hjf : j < f) (z' : ModGL Tag.F4 L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  have hr2 := hr.two_le
  have hf2 : 2 ≤ f := by omega
  have hfs : 0 < f * s := Nat.mul_pos (by omega) hs0
  have hrf4 : 4 ≤ r ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf2
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hfs σ hσ
  let : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σ) = (r ^ f) ^ s := by
    rw [← Nat.card_eq_fintype_card, hKcard, pow_mul]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →+* L, ψ = iterateFrobenius L r j := ⟨_, rfl⟩
  rw [← hψ] at hfix
  have hψpow : ∀ x : L, ψ x = x ^ (r ^ j) := fun x => by rw [hψ, iterateFrobenius_def]
  have hdata := fun κ : ZMod s =>
    ggPA44_exists_factor_data_F4_long S ψ zu hθr κ.val
      ((ggPA44_iform_iterate_rho S θ κ.val).trans hθlong)
  choose aZ bZ aZ' bZ' haZ haZ' hrkZ hE1 hE2 using hdata
  have hcast : ∀ κ : ZMod s, ((κ.val : ℕ) : ZMod s) = κ := ZMod.natCast_zmod_val
  obtain ⟨aN, haN⟩ : ∃ aN : ℕ → Module.End L (RootModule Tag.F4 L),
      ∀ κ : ZMod s, aN κ.val = aZ κ := ⟨fun n => aZ (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨bN, hbN⟩ : ∃ bN : ℕ → Module.End L (RootModule Tag.F4 L),
      ∀ κ : ZMod s, bN κ.val = bZ κ := ⟨fun n => bZ (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨aN', haN'⟩ : ∃ aN' : ℕ → Module.End L (RootModule Tag.F4 L),
      ∀ κ : ZMod s, aN' κ.val = aZ' κ := ⟨fun n => aZ' (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨bN', hbN'⟩ : ∃ bN' : ℕ → Module.End L (RootModule Tag.F4 L),
      ∀ κ : ZMod s, bN' κ.val = bZ' κ := ⟨fun n => bZ' (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨ks, hks⟩ : ∃ ks : List ℕ,
      ks = (Finset.univ : Finset (ZMod s)).toList.map ZMod.val := ⟨_, rfl⟩
  have hnd : ks.Nodup := by
    rw [hks]
    exact List.Nodup.map (ZMod.val_injective s) (Finset.nodup_toList _)
  have h0 : 0 ∈ ks := by
    rw [hks]
    exact List.mem_map.2 ⟨0, Finset.mem_toList.2 (Finset.mem_univ _), ZMod.val_zero⟩
  have hksl : ∀ k ∈ ks, k < s := fun k hk => by
    rw [hks] at hk
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hk
    exact ZMod.val_lt κ
  have hsq : ∀ (x : L) (m : ℕ), x ^ (2 * m) = (x ^ m) ^ 2 := fun x m => by
    rw [← pow_mul, mul_comm]
  have hmain : ∀ t : fixSubfield σ,
      (z' : Module.End L (RootModule Tag.F4 L)) *
        evAt (((t : L)) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) *
          (↑z'⁻¹ : Module.End L (RootModule Tag.F4 L)) =
        evAt (t : L) (prodList (r ^ f) aN bN ks) := by
    intro t
    have hc : σ (t : L) = t := t.2
    have hf := hfix _ (hrt (t : L) hc)
    have hnormeq := norm_eq_list_prod P ⟨_, hy (t : L)⟩
    have hnormA : ((P.norm ⟨_, hy (t : L)⟩ : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L)) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + ((t : L) ^ (r ^ f) ^ κ.val) • aZ κ +
            ((t : L) ^ (r ^ f) ^ κ.val) ^ 2 • bZ κ).prod := by
      rw [hnormeq, units_coe_list_prod]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      have e := hE1 κ (t : L)
      rw [hq] at e
      exact e
    have hnormA' : ((Units.map (entrywiseHom ψ) (P.norm ⟨_, hy (t : L)⟩) : ModGL Tag.F4 L) :
        Module.End L (RootModule Tag.F4 L)) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + (ψ ((t : L) ^ (r ^ f) ^ κ.val)) • aZ' κ +
            (ψ ((t : L) ^ (r ^ f) ^ κ.val)) ^ 2 • bZ' κ).prod := by
      rw [hnormeq, map_list_prod, List.map_map, units_coe_list_prod]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      have e := hE2 κ (t : L)
      rw [hq] at e
      exact e
    have hfA := congrArg (fun m : ModGL Tag.F4 L => (m : Module.End L (RootModule Tag.F4 L))) hf
    simp only [Units.val_mul] at hfA
    rw [hnormA, hnormA'] at hfA
    have hR : evAt (t : L) (prodList (r ^ f) aN bN ks) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + ((t : L) ^ (r ^ f) ^ κ.val) • aZ κ +
            ((t : L) ^ (r ^ f) ^ κ.val) ^ 2 • bZ κ).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, haN, hbN, hsq]
    have hL : evAt ((t : L) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + (ψ ((t : L) ^ (r ^ f) ^ κ.val)) • aZ' κ +
            (ψ ((t : L) ^ (r ^ f) ^ κ.val)) ^ 2 • bZ' κ).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, haN', hbN', hsq, hψpow]
      rw [pow_right_comm ((t : L)) ((r ^ f) ^ κ.val) (r ^ j)]
    rw [hR, hL]
    exact hfA
  by_cases hex : r ^ j = 2 ∧ r ^ f = 4
  ·
    obtain ⟨hrj, hrf⟩ := hex
    have hm4 := twisted_conj_q4 (fixSubfield σ).subtype hs0 (by rw [hKcard', hrf]) ks hnd h0
      hksl aN bN aN' bN' z' (fun t => by
        have := hmain t
        rwa [hrf, hrj] at this)
    obtain ⟨hr2, hr1⟩ := hrkZ 0
    have haN0 : aN' 0 = aZ' 0 := by
      have := haN' 0
      rwa [ZMod.val_zero] at this
    have hbN0 : bN 0 = bZ 0 := by
      have := hbN 0
      rwa [ZMod.val_zero] at this
    rw [haN0, hbN0] at hm4
    have h3 := finrank_range_conj_eq z' (aZ' 0)
    rw [hm4] at h3
    omega
  · refine no_twisted_conj (fixSubfield σ).subtype hr hj0 hjf hs0 hKcard' hrf4 ?_ ks hnd h0 hksl
      aN bN aN' bN' ?_ ?_ z' hmain
    · intro hc2
      have hr2' : r = 2 := by
        have : r ∣ 2 := by
          rw [← hc2]
          exact dvd_pow_self r hj0.ne'
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
      subst hr2'
      have hf3 : f ≠ 2 := fun hf2' => hex ⟨hc2, by rw [hf2']; norm_num⟩
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    · have := haZ 0
      rwa [← haN 0, ZMod.val_zero] at this
    · have := haZ' 0
      rwa [← haN' 0, ZMod.val_zero] at this

private theorem ggPA44_outer_false_of_component_fixed_by_twist_F4
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.F4 L p)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hlong : ∃ θ ∈ componentRoots (rootCharHom a) i, iform θ θ = 4)
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f)
    (hj0 : 0 < j) (hjf : j < f) (z' : ModGL Tag.F4 L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False := by
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  obtain ⟨θ, hθ, hθlong⟩ := hlong
  have hθr : IsRoot Tag.F4 θ := isRoot_of_mem_componentRoots hθ
  have hθs : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] θ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact Set.mem_image_of_mem _ hθ
  obtain ⟨w, hw, hwθ⟩ := outer_exists_smul_eq (isRootComponent_componentRoots i) hθ hθs
    (outer_iterate_iform S s θ θ).symm
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := outer_exists_untwist_root S hT i hs0 hθ hw hwθ.symm
  have hσ' : ∀ c, σ c = c ^ (r ^ (f * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hfs : 0 < f * s := Nat.mul_pos (by omega) hs0
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hfs σ hσ'
  have hQ4 : 4 ≤ r ^ (f * s) := by
    have hr2 := hr.two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ (f * s) :=
        Nat.pow_le_pow_right (by omega) (le_trans (by omega) (Nat.le_mul_of_pos_right f hs0))
  have hperf : Group.IsPerfect (SL2 (fixSubfield σ)) := by
    let : Fintype (fixSubfield σ) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset (fixSubfield σ)).card by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard]
        exact hQ4)
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  have hP0 : P.S 0 = rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hneg : -θ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem θ hθ
  have hmemS : ∀ A : SL2 L, zu * rootSL2 Tag.F4 L θ A * zu⁻¹ ∈ P.S 0 := by
    intro A
    rw [hP0]
    refine (hnorm i _).1 ?_
    have h1 : rootSL2 Tag.F4 L θ A ∈ rootRankOneGroup Tag.F4 L θ := ⟨A, rfl⟩
    rw [(exceptional_Lang_root_rank_one_torus_transport Tag.F4 L hθr).1] at h1
    exact sup_le (rootSubgroup_le_rootSpan hθ) (rootSubgroup_le_rootSpan hneg) h1
  let θ₀ : SL2 (fixSubfield σ) →* P.S 0 :=
    ((MulAut.conj zu).toMonoidHom.comp ((rootSL2 Tag.F4 L θ).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype))).codRestrict (P.S 0)
      fun A => hmemS _
  have hθ₀ : ∀ A, ((θ₀ A : P.S 0) : ModGL Tag.F4 L) =
      zu * rootSL2 Tag.F4 L θ (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) * zu⁻¹ :=
    fun A => rfl
  have hσι : ∀ A : SL2 (fixSubfield σ), Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) =
        Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A := by
    intro A
    ext k l
    exact ((A : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) k l).2
  have hθfix : ∀ A, iterHom S.D.step s ((θ₀ A : P.S 0) : ModGL Tag.F4 L) = θ₀ A := by
    intro A
    rw [hθ₀, hz, hσι]
  have hy : ∀ t : L, zu * pinnedX Tag.F4 L θ t * zu⁻¹ ∈ P.S 0 := by
    intro t
    rw [hP0]
    exact (hnorm i _).1 (pinnedX_mem_rootSpan hθ _)
  refine ggPA44_outer_false_of_norm_fixed_F4 S hT i hs hmin hθr hθlong zu hy hr hq σ hσ'
    (fun t ht => ?_) hj0 hjf z' hfix
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = (pinnedData Tag.F4 θ).2.2 := ⟨_, rfl⟩
  have hε2 : ε • ε • t = t := by
    rcases pinnedSign_eq Tag.F4 θ with h | h <;> rw [hε, h] <;> simp
  have hA : ((θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) : P.S 0) : ModGL Tag.F4 L) =
      zu * pinnedX Tag.F4 L θ t * zu⁻¹ := by
    rw [hθ₀, map_uSL, rootSL2_uSL_eq, map_zsmul, ← hε]
    have e : ε • ε • (fixSubfield σ).subtype (⟨t, ht⟩ : fixSubfield σ) = t := hε2
    rw [e]
  have h1 := outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hθfix
    (uSL (ε • (⟨t, ht⟩ : fixSubfield σ)))
  have h2 : θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) = ⟨_, hy t⟩ := Subtype.ext hA
  rw [h2] at h1
  exact h1

private theorem ggPA44_outer_false_of_component_fixed_by_twist_of_E_F4
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.F4 L p)
    {a : Fin Tag.F4.rank → Lˣ} (hE : rootDiagUnit Tag.F4 a ∈ S.E)
    (i : KernelComponent (rootCharHom a))
    (hlong : ∃ θ ∈ componentRoots (rootCharHom a) i, iform θ θ = 4)
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f)
    (hj0 : 0 < j) (hjf : j < f) (z' : ModGL Tag.F4 L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False :=
  ggPA44_outer_false_of_component_fixed_by_twist_F4 S (Subgroup.mem_inf.1 (S.E_le hE)).1 i
    hlong hr hq hj0 hjf z' hfix

private def ggPA44_dotMod (p : ℕ) (θ : Fin 4 → ℤ) (x : Fin 4 → ZMod p) : ZMod p :=
  ∑ i, (θ i : ZMod p) * x i

private theorem ggPA44_exists_long_dot_zero (p : ℕ) (hp35 : p = 3 ∨ p = 5) :
    ∀ x : Fin 4 → ZMod p, ∃ k : Fin Tag.F4.rootCertificate.roots.length,
      iform (Tag.F4.rootCertificate.root (k : ℕ)) (Tag.F4.rootCertificate.root (k : ℕ)) = 4 ∧
      ggPA44_dotMod p (Tag.F4.rootCertificate.root (k : ℕ)) x = 0 := by
  rcases hp35 with rfl | rfl
  · decide +kernel
  · decide +kernel

private theorem ggPA44_exists_longRoot_rootChar_one
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp35 : p = 3 ∨ p = 5) (a : Fin Tag.F4.rank → Lˣ) (ha : ∀ i, a i ^ p = 1) :
    ∃ θ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 θ ∧ iform θ θ = 4 ∧ rootChar a θ = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by rcases hp35 with h | h <;> omega
  have hpL : (p : L) ≠ 0 := by
    intro h
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  haveI : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  let ζ' : Lˣ := (hζ.isUnit hp.ne_zero).unit
  have hζ' : IsPrimitiveRoot ζ' p := hζ.isUnit_unit hp.ne_zero
  have hx : ∀ i, ∃ x : ℕ, x < p ∧ ζ' ^ x = a i := fun i =>
    hζ'.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (a i)).mpr (ha i))
  choose x _ hxeq using hx
  obtain ⟨k, hk4, hk0⟩ := ggPA44_exists_long_dot_zero p hp35 (fun i => (x i : ZMod p))
  refine ⟨Tag.F4.rootCertificate.root (k : ℕ),
    RootCertificate.isRoot_root Tag.F4.rootCertificate_check k k.2, hk4, ?_⟩
  set S : ℤ := ∑ i : Fin 4, (x i : ℤ) * (Tag.F4.rootCertificate.root (k : ℕ)) i with hS
  have hSzmod : (S : ZMod p) = 0 := by
    rw [hS, Int.cast_sum]
    have hterm : ∀ i : Fin 4,
        (((x i : ℤ) * (Tag.F4.rootCertificate.root (k : ℕ)) i : ℤ) : ZMod p) =
          (Tag.F4.rootCertificate.root (k : ℕ) i : ZMod p) * (x i : ZMod p) := by
      intro i; push_cast; ring
    simp only [hterm]
    simpa only [ggPA44_dotMod] using hk0
  have hdvd : (p : ℤ) ∣ S := (ZMod.intCast_zmod_eq_zero_iff_dvd S p).mp hSzmod
  have hζS : ζ' ^ S = 1 := (hζ'.zpow_eq_one_iff_dvd S).mpr hdvd
  have hprod : (∏ i : Fin 4,
      ζ' ^ ((x i : ℤ) * (Tag.F4.rootCertificate.root (k : ℕ)) i)) = ζ' ^ S := by
    rw [Fin.prod_univ_four, hS, Fin.sum_univ_four, zpow_add, zpow_add, zpow_add]
  have hfac : ∀ i : Fin 4, a i ^ (Tag.F4.rootCertificate.root (k : ℕ)) i =
      ζ' ^ ((x i : ℤ) * (Tag.F4.rootCertificate.root (k : ℕ)) i) := by
    intro i
    rw [← hxeq i, ← zpow_natCast, ← zpow_mul]
  have hroot : rootChar (τ := Tag.F4) a (Tag.F4.rootCertificate.root (k : ℕ)) =
      ∏ i : Fin 4, ζ' ^ ((x i : ℤ) * (Tag.F4.rootCertificate.root (k : ℕ)) i) := by
    rw [rootChar]
    exact Finset.prod_congr rfl fun i _ => hfac i
  rw [hroot, hprod, hζS]

private theorem ggPA44_frobeniusEquiv_pow_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) (c : K) : (frobeniusEquiv K 2 ^ n) c = c ^ 2 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, frobeniusEquiv_def, ← pow_mul, ← pow_succ]

private theorem ggPA44_normalForm_F4
    {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.F4 K)) (hα2 : α * α = 1)
    (hout : ∀ c : adjointGroup Tag.F4 K, α ≠ MulAut.conj c) :
    ∃ (e : ℕ) (σ : K ≃+* K) (g : adjointGroup Tag.F4 K), f = 2 * e ∧
      (∀ c, σ c = c ^ 2 ^ e) ∧ α = MulAut.conj g * entrywiseAdjointAut Tag.F4 σ := by
  obtain ⟨e, g, hfe, hαeq⟩ := ggFieldOuterNormalForm_F4 hf hfe hK α hα2 hout
  refine ⟨e, frobeniusEquiv K 2 ^ e, g, hfe, fun c => ggPA44_frobeniusEquiv_pow_apply e c, ?_⟩
  rw [hαeq]
  congr 1
  exact (CFSG.LieType.Chevalley.entrywiseAdjointAut_eq_finiteFrobeniusAut_pow
    (fun c => ggPA44_frobeniusEquiv_pow_apply e c)).symm

private theorem ggPA44_baseChange_normalForm
    {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L] [ExpChar L 2]
    {e : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {g : adjointGroup τ K} {α : MulAut (adjointGroup τ K)}
    (hαeq : α = MulAut.conj g * entrywiseAdjointAut τ σ) :
    ∀ c : adjointGroup τ K,
      baseChangeGL (algebraMap K L) ((α c : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K L) (g : ModGL τ K) *
        Units.map (entrywiseHom (iterateFrobenius L 2 e))
          (baseChangeGL (algebraMap K L) (c : ModGL τ K)) *
        (baseChangeGL (algebraMap K L) (g : ModGL τ K))⁻¹ := by
  intro c
  have hcomp : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L 2 e).comp (algebraMap K L) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change (algebraMap K L) (σ x) = (iterateFrobenius L 2 e) ((algebraMap K L) x)
    rw [hσ, map_pow, iterateFrobenius_def]
  have key : baseChangeGL (algebraMap K L)
        (Units.map (entrywiseHom σ.toRingHom) (c : ModGL τ K)) =
      Units.map (entrywiseHom (iterateFrobenius L 2 e))
        (baseChangeGL (algebraMap K L) (c : ModGL τ K)) := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have h1 : ((α c : adjointGroup τ K) : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (c : ModGL τ K) *
        (g : ModGL τ K)⁻¹ := by
    rw [hαeq]
    simp only [MulAut.mul_apply, MulAut.conj_apply, coe_entrywiseAdjointAut, Subgroup.coe_mul,
      Subgroup.coe_inv]
  rw [h1, map_mul, map_mul, map_inv, key]

private theorem ggPA44_four_le_excDegCount
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E) :
    4 ≤ excDegCount τ (orderOf (Nat.card K : ZMod p)) := by
  by_contra h
  have h3 : excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ 3 := by omega
  have hle := excPRankBound hτ K hp hp2 h3 E hE
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact not_lt_of_ge hle (lt_of_lt_of_le hlt h4)

private theorem ggPA44_assembly_general
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ 2) :
    GGFieldOuterInvModel (adjointGroup Tag.F4 K) := by
  intro p b α hp hp2 hb1 hbp ⟨E, hE, hbE, h4, hmax⟩ hα2 hout hαb ⟨L₁, hL₁⟩ hfix
  have hf : 1 ≤ 2 := by norm_num
  have hfe : Even 2 := ⟨1, rfl⟩
  obtain ⟨e, σ, g, hfe2, hσ, hαeq⟩ := ggPA44_normalForm_F4 hf hfe K hK α hα2 hout
  have he1 : 1 ≤ e := by omega
  have he2 : e < 2 := by omega
  have hcard4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hq : ∃ e', Nat.card K = 4 ^ e' := ⟨1, by rw [hcard4]; norm_num⟩
  obtain ⟨Fr, hFr, w, g0, hg0C, hg0, htor⟩ :=
    exists_langDatum_of_maxElem (τ := Tag.F4) (Or.inr (Or.inr rfl)) K hq hp hp2 E hE h4 hmax
  have hK4 : 4 ≤ Nat.card K := by rw [hcard4]
  obtain ⟨S, a, ι, hSD, hrootE, ha, hinj, hirange, hιc, hιconj⟩ :=
    exists_langSetup_conj (τ := Tag.F4) (Or.inr (Or.inr rfl)) K hK4 hp hp2 hFr hg0C hg0 b hbp
      (htor b hbE)
  have hdT : rootDiagUnit Tag.F4 a ∈ S.D.torus := (S.E_le hrootE).1
  have hBC := ggPA44_baseChange_normalForm (K := K) (L := AlgebraicClosure K) (τ := Tag.F4)
    hσ hαeq
  have hdeg : 4 ≤ excDegCount Tag.F4 (orderOf (Nat.card K : ZMod p)) :=
    ggPA44_four_le_excDegCount (Or.inr (Or.inr rfl)) K hp hp2 E hE h4
  have hd12 : orderOf (Nat.card K : ZMod p) = 1 ∨ orderOf (Nat.card K : ZMod p) = 2 := by
    rcases excDegCount_ge_four hdeg with ⟨-, hd, -⟩ | ⟨hE8, -, -⟩
    · exact hd
    · exact absurd hE8 (by decide)
  have hp35 : p = 3 ∨ p = 5 := by
    have hcardZ : (Nat.card K : ZMod p) = (4 : ℕ) := by rw [hcard4]
    rcases hd12 with hd | hd
    · left
      have h1 : ((4 : ℕ) : ZMod p) = 1 := by
        have h := orderOf_eq_one_iff.mp hd
        rwa [hcardZ] at h
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        have e : ((4 : ℕ) : ZMod p) - 1 = ((3 : ℕ) : ZMod p) := by norm_num
        have h : ((4 : ℕ) : ZMod p) - 1 = 0 := by rw [h1]; ring
        rwa [e] at h
      have hdvd3 : p ∣ 3 := by
        have hz : (p : ℤ) ∣ (3 : ℤ) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp (by simpa using h3)
        exact Int.natCast_dvd_natCast.mp hz
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd3
    · have h2 : ((4 : ℕ) : ZMod p) ^ 2 = 1 := by
        have hd' : orderOf ((4 : ℕ) : ZMod p) = 2 := by rw [← hcardZ]; exact hd
        have h := pow_orderOf_eq_one ((4 : ℕ) : ZMod p)
        rwa [hd'] at h
      have h15 : ((15 : ℕ) : ZMod p) = 0 := by
        have e : ((4 : ℕ) : ZMod p) ^ 2 - 1 = ((15 : ℕ) : ZMod p) := by norm_num
        have h : ((4 : ℕ) : ZMod p) ^ 2 - 1 = 0 := by rw [h2]; ring
        rwa [e] at h
      have hdvd15 : p ∣ 15 := by
        have hz : (p : ℤ) ∣ (15 : ℤ) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd 15 p).mp (by simpa using h15)
        exact Int.natCast_dvd_natCast.mp hz
      have hdvd15' : p ∣ 3 * 5 := by
        rw [show (3 * 5 : ℕ) = 15 by norm_num]
        exact hdvd15
      rcases hp.dvd_mul.mp hdvd15' with h3 | h5
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5)
  obtain ⟨θ, hθroot, hθlong, hθker⟩ := ggPA44_exists_longRoot_rootChar_one hp hp35 a ha
  have hk : θ ∈ kernelRoots (rootCharHom a) := ⟨hθroot, hθker⟩
  let i : KernelComponent (rootCharHom a) := (⟦⟨θ, hk⟩⟧ : KernelComponent (rootCharHom a))
  have hlong : ∃ θ' ∈ componentRoots (rootCharHom a) i, iform θ' θ' = 4 :=
    ⟨θ, ⟨hk, rfl⟩, hθlong⟩
  let z' : ModGL Tag.F4 (AlgebraicClosure K) :=
    ι g * (g0⁻¹ * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) g0)
  have hz' : z' = ι g * (g0⁻¹ *
      Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) g0) := rfl
  have hconj : ∀ c : adjointGroup Tag.F4 K,
      z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) (ι c) *
        z'⁻¹ = ι (α c) := by
    intro c
    set FrL : ModGL Tag.F4 (AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K) :=
      Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) with hFrL
    have hz : z' = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL Tag.F4 K) *
        FrL g0 := by
      rw [hz', hιc g]
      group
    have hιc' : ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c : ModGL Tag.F4 K) * g0 := hιc c
    rw [hz, hιc', hFrL]
    rw [map_mul, map_mul, map_inv]
    rw [hιc (α c), hBC c, hFrL]
    group
  have hfix' : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) x *
        z'⁻¹ = x := by
    intro x hx
    have hsub := langSubnormal_of_mem_torus S hdT i
    have hxΓ : x ∈ S.Γ := (hsub.1 hx).1
    have hxd : x ∈ Subgroup.centralizer {rootDiagUnit Tag.F4 a} := (hsub.1 hx).2
    obtain ⟨c, hcx⟩ : x ∈ ι.range := by
      rw [hirange]
      exact hxΓ
    have hxd' : rootDiagUnit Tag.F4 a * x * (rootDiagUnit Tag.F4 a)⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hxd]
      group
    have hιbc : ι (b * c * b⁻¹) = ι c := by
      rw [hιconj c, hcx, hxd']
    have hbcb : b * c * b⁻¹ = c := hinj hιbc
    have hccent : c ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcb : b * c = c * b := by
        calc b * c = b * c * b⁻¹ * b := by group
          _ = c * b := by rw [hbcb]
      exact hcb.symm
    have hαc : α c = c := hfix c hccent
    calc z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) x *
          z'⁻¹ =
          z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 e)) (ι c) *
            z'⁻¹ := by rw [hcx]
        _ = ι (α c) := hconj c
        _ = ι c := by rw [hαc]
        _ = x := hcx
  have hqouter : S.D.q = 2 ^ 2 := by rw [hSD]; exact hK
  exact ggPA44_outer_false_of_component_fixed_by_twist_of_E_F4 (S := S) (a := a) (i := i)
    (r := 2) (f := 2) (j := e) hrootE hlong Nat.prime_two hqouter he1 he2 z' hfix'

private theorem ggPA44_assembly_F4_four :
    GGFieldOuterInvModel (adjointGroup .F4 (GaloisField 2 2)) :=
  ggPA44_assembly_general (GaloisField 2 2)
    (GaloisField.card (p := 2) (n := 2) (by norm_num))

theorem ggFieldOuterInvModel_F4_four :
    GGFieldOuterInvModel (adjointGroup .F4 (GaloisField 2 2)) :=
  ggPA44_assembly_F4_four

end CFSG.StandardType
