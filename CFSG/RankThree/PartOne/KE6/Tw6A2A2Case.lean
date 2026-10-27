module

public import CFSG.RankThree.PartOne.KE6.Tw6A2Case
public import CFSG.RankThree.PartOne.KE6.Tw6A2b
public import CFSG.RankThree.PartOne.KE6.Tw6Std
public import CFSG.RankThree.PartOne.KE6.Phi3A2A2Case

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_unitary)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

section Case

variable {Fr : Ω →+* Ω}

theorem tw6_A2_layer_gen₂ {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support56) :
    (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support56 ∧
    Finite ↥(rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S ⊓
      (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    e6Commutant (((rootSpan Tag.E6 Ω S ⊓
        (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) ∧
    ∃ h₀ : ModGL Tag.E6 Ω, ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω (e6Index 4) (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) *
        h₀⁻¹ ∈ rootSpan Tag.E6 Ω S ⊓
          (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support56 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj₂ hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      tw6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π j) (π i)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_tw6Theta_pinnedX (Fr := Fr) w
      (chainRoot56_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ, ← chainRoot_swap]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta₂ hFrs
    (tw6ThetaConj Ω Fr w) (tw6ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, hfin, hq⟩ := sl3_root_permuting_frobenius_fixed_unitary hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  set P := rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) with hPdef
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup_gen₂ (tw6Theta Ω Fr) (tw6ThetaConj Ω Fr w)
    (tw6ThetaConj_conj w) hQ hmaps Φ hΦ₀
  have hmemQ₂ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfinP : Finite ↥P := Finite.of_equiv _ e.symm.toEquiv
  have hqsP : CFSG.IsQuasisimple ↥P :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm (hq (by omega)).1
  have hA2 := isA2Layer_a2Inv₂ (Ω := Ω)
  have hconj : ((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω)) =
      unitaryLayer (a2Inv₂ Ω) (ℓ ^ f) (Matrix.SpecialLinearGroup.toGL H') := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz := hmemQ₂ y hy.1
      obtain ⟨Y, hY, hXY⟩ := (hH' (e ⟨y, hy⟩ : SL(3, Ω))).1 (e ⟨y, hy⟩).2
      have h1 : a2Inv₂ Ω (e ⟨y, hy⟩ : SL(3, Ω)) = n * y * n⁻¹ :=
        (a2Inv₂_eq_iff hz).2 (he ⟨y, hy⟩)
      exact ⟨(e ⟨y, hy⟩ : SL(3, Ω)), ⟨Y, hY, hXY.symm⟩, h1⟩
    · rintro ⟨X, ⟨Y, hY, hXY⟩, rfl⟩
      have hX : X ∈ fixSubgroup Φ := (hH' X).2 ⟨Y, hY, hXY.symm⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨X, hX⟩
      have hz := hmemQ₂ y y.2.1
      have h1 := he y
      rw [hy] at h1
      have h2 : a2Inv₂ Ω X = n * y * n⁻¹ := (a2Inv₂_eq_iff hz).2 h1
      exact ⟨y, y.2, h2.symm⟩
  have hcommP : e6Commutant (((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
    rw [hconj]
    exact hA2.e6Commutant_unitaryLayer hℓ hf hK hq3 _
  obtain ⟨m, hmQ, hsl⟩ := hA2.exists_conj_simpleRootSL2_mem_unitaryLayer hℓ hf hK
    (Matrix.SpecialLinearGroup.toGL H')
  refine ⟨hQ, hfinP, hqsP, hcommP, n⁻¹ * m, fun B => ?_⟩
  have hmem : m * simpleRootSL2 Tag.E6 Ω (e6Index 4)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ ∈
        ((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
          Set (ModGL Tag.E6 Ω)) := by
    rw [hconj]
    exact hsl B
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hyeq' : n * y * n⁻¹ = m * simpleRootSL2 Tag.E6 Ω (e6Index 4)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ := hyeq
  have this : n⁻¹ * m * simpleRootSL2 Tag.E6 Ω (e6Index 4)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * (n⁻¹ * m)⁻¹ = y := by
    have h3 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [h3, hyeq']
    group
  rw [this]
  exact hy


theorem tw6_A2A2_kernelLayer {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hA : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    Nonempty (KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K
      (Fin 2)) := by
  classical
  obtain ⟨w, hw⟩ := hA
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Sx := torusRootKernel x with hSxdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hvS := tw6_torusRootKernel_smul_stable hFr hx
  have hT : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  have hcolJ : ∀ j ∈ supportA2A2, ∀ i ∉ supportA2A2, lget L i j = 0 := by
    intro j hj i hi
    have hsingle : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots Tag.E6 supportA2A2 :=
      ⟨isRoot_single Tag.E6 j, fun i' hi' => Pi.single_eq_of_ne (fun h => hi' (by rw [h]; exact hj)) 1⟩
    have h := (hT _ hsingle).2 i hi
    rw [smul_single_apply_eq_lget hLT] at h
    exact h
  have hmemJ : ∀ j : Fin Tag.E6.rank, (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) → j ∈ supportA2A2 := by
    intro j hj
    rw [mem_supportA2A2]
    exact hj
  have hnJ : ∀ i : Fin Tag.E6.rank, (i = 1 ∨ i = 3) → i ∉ supportA2A2 := by
    intro i hi hmem
    rw [mem_supportA2A2] at hmem
    revert hi hmem
    revert i
    decide
  obtain ⟨hblk, hA13, hA56⟩ := e6T3Orbit_A2A2_shape L hL
    ⟨hcolJ 0 (hmemJ 0 (Or.inl rfl)) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 0 (hmemJ 0 (Or.inl rfl)) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 3 (hnJ 3 (Or.inr rfl))⟩
  obtain ⟨hb40, hb50, hb42, hb52, hb04, hb24, hb05, hb25⟩ := hblk
  have hcol13 : ∀ j ∈ support13, ∀ i ∉ support13, lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 0 ∨ j = e6Index 2 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first | exact absurd (Or.inl rfl) hi | exact absurd (Or.inr rfl) hi | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hcol56 : ∀ j ∈ support56, ∀ i ∉ support56, lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 4 ∨ j = e6Index 5 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first | exact absurd (Or.inl rfl) hi | exact absurd (Or.inr rfl) hi | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hT13 : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := fun β hβ =>
    smul_mem_parabolicRoots_of_lget hLT hcol13 hβ
  have hT56 : ∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56 := fun β hβ =>
    smul_mem_parabolicRoots_of_lget hLT hcol56 hβ
  set S₁ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13 with hS₁
  set S₂ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56 with hS₂
  have hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13 := by
    rw [hS₁, Set.image_image]
    simp
  have hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56 := by
    rw [hS₂, Set.image_image]
    simp
  have hS₁roots : ∀ α ∈ S₁, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hS₂roots : ∀ α ∈ S₂, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT13 β hβ, by simp [mul_smul]⟩
  have hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT56 β hβ, by simp [mul_smul]⟩
  have h13A : support13 ⊆ supportA2A2 := fun i hi => by
    rw [mem_supportA2A2]
    have hi' : i = e6Index 0 ∨ i = e6Index 2 := hi
    rcases hi' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h56A : support56 ⊆ supportA2A2 := fun i hi => by
    rw [mem_supportA2A2]
    have hi' : i = e6Index 4 ∨ i = e6Index 5 := hi
    rcases hi' with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hsub : ∀ {J : Set (Fin Tag.E6.rank)}, J ⊆ supportA2A2 →
      (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J ⊆ Sx := by
    intro J hJ
    rintro _ ⟨β, hβ, rfl⟩
    have hβJ : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
      ⟨hβ.1, fun i hi => hβ.2 i (fun hiJ => hi (hJ hiJ))⟩
    rw [← hw] at hβJ
    obtain ⟨α, hα, rfl⟩ := hβJ
    simpa using hα
  have hQ : (rootSpan Tag.E6 Ω Sx).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω supportA2A2 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w Sx (fun α hα => hα.1), hw,
      subsystemGroup_eq_rootSpan]
  obtain ⟨hQ₁, hfin₁, hq₁, hcomm₁, h₀, hsl₁⟩ := tw6_A2_layer_gen hf hK hq3 hFr hS₁roots hvS₁ hw₁
  obtain ⟨hQ₂, hfin₂, hq₂, hcomm₂, -⟩ := tw6_A2_layer_gen₂ hf hK hq3 hFr hS₂roots hvS₂ hw₂
  have hsep₁₂ : CFSG.RankThree.Lattice.IsSeparated support13 support56 := by
    intro a ha b hb
    have ha' : a = e6Index 0 ∨ a = e6Index 2 := ha
    have hb' : b = e6Index 4 ∨ b = e6Index 5 := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide
  have hsep₂₁ : CFSG.RankThree.Lattice.IsSeparated support56 support13 := by
    intro a ha b hb
    have ha' : a = e6Index 4 ∨ a = e6Index 5 := ha
    have hb' : b = e6Index 0 ∨ b = e6Index 2 := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide
  have hunion : supportA2A2 = support13 ∪ support56 := by
    ext i
    rw [mem_supportA2A2]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h)
      · have h' : i = e6Index 0 ∨ i = e6Index 2 := h
        rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · have h' : i = e6Index 4 ∨ i = e6Index 5 := h
        rcases h' with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
  set P₁ : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω S₁ ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) with hP₁
  set P₂ : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω S₂ ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) with hP₂
  have hle : ∀ k : Fin 2, ((![P₁, P₂] k).map (MulAut.conj n).toMonoidHom) ≤
      subsystemGroup Tag.E6 Ω (![support13, support56] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hQ₁ ▸ Subgroup.map_mono inf_le_left, hQ₂ ▸ Subgroup.map_mono inf_le_left⟩
  have hC : ∀ k : Fin 2, e6Commutant ((((![P₁, P₂] k).map (MulAut.conj n).toMonoidHom :
      Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω (![support13, support56] k) :
        Set (ModGL Tag.E6 Ω)) := by
    rw [Fin.forall_fin_two]
    exact ⟨hcomm₁, hcomm₂⟩
  have hsep : ∀ k l : Fin 2, k ≠ l → CFSG.RankThree.Lattice.IsSeparated
      (![support13, support56] k) (![support13, support56] l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact hsep₁₂
    · exact hsep₂₁
    · exact absurd rfl hkl
  have hJ : supportA2A2 = ⋃ k, ![support13, support56] k := by
    rw [hunion]
    ext i
    simp [Set.mem_iUnion, Fin.exists_fin_two]
  obtain ⟨-, μ, -, hμrange, hμcomm, -, -⟩ := CFSG.RankThree.Lattice.e6_product_layers
    (Ω := Ω) supportA2A2 ![support13, support56]
    (fun k => (![P₁, P₂] k).map (MulAut.conj n).toMonoidHom) hsep hJ hle hC
  have hcommP : e6Commutant ((((⨆ k : Fin 2, ![P₁, P₂] k).map (MulAut.conj n).toMonoidHom :
      Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω supportA2A2 : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.map_iSup, ← hμrange]
    exact hμcomm
  have hspan : ∀ k : Fin 2, ![P₁, P₂] k ≤ rootSpan Tag.E6 Ω Sx := by
    rw [Fin.forall_fin_two]
    exact ⟨inf_le_left.trans (rootSpan_mono (hsub h13A)),
      inf_le_left.trans (rootSpan_mono (hsub h56A))⟩
  have hfix : ∀ k : Fin 2, ![P₁, P₂] k ≤
      twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) := by
    rw [Fin.forall_fin_two]
    exact ⟨inf_le_right, inf_le_right⟩
  have hfinF : ∀ k : Fin 2, Finite ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hfin₁, hfin₂⟩
  have hqF : ∀ k : Fin 2, CFSG.IsQuasisimple ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hq₁, hq₂⟩
  have hnormF : ∀ k : Fin 2, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω Sx,
      y ∈ twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) →
      ∀ u ∈ ![P₁, P₂] k, y * u * y⁻¹ ∈ ![P₁, P₂] k := by
    rw [Fin.forall_fin_two]
    constructor
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup (fun α hα => hα.1) hQ hy
      rw [hunion] at hy'
      have hn₁ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω) (J₁ := support13)
        (J₂ := support56) hsep₂₁ hy'
      exact thetaQ_conj_mem (mem_normalizer_of_conj hQ₁ hn₁) hyR hu
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup (fun α hα => hα.1) hQ hy
      rw [hunion, Set.union_comm] at hy'
      have hn₂ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω) (J₁ := support56)
        (J₂ := support13) hsep₁₂ hy'
      exact thetaQ_conj_mem (mem_normalizer_of_conj hQ₂ hn₂) hyR hu
  exact ⟨KernelLayer.ofFamily ![P₁, P₂] (fun α hα => hα.1) hQ hfinF hqF hspan hfix hnormF hcommP
    (fun _ => ⟨0, e6Index 0, h₀, hsl₁⟩)⟩


end Case

end CFSG.RankThree.PartOne.KE6
