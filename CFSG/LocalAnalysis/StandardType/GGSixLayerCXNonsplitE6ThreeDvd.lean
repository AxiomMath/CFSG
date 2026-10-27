module

public import CFSG.RankThree.PartOne.KE6.Phi3Solvable
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeCardA2
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeCardD4
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.PartOne.KETw3 (chainRoot13_add chainRoot56_add map_zero_of_add
  map_neg_of_add)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_split)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf)
open CFSG.Assembly (IsComponentOf)
open scoped Matrix MatrixGroups Pointwise

namespace NonsplitLayers


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem exists_kernelLayer_family_P {n : ModGL Tag.E6 Ω}
    {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω} {S : Set (Fin Tag.E6.rank → ℤ)} {K : Type} [Field K]
    [Algebra K Ω] {ι' : Type} (P : ι' → Subgroup (ModGL Tag.E6 Ω))
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    (hfin : ∀ i, Finite (P i)) (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hspan : ∀ i, P i ≤ rootSpan Tag.E6 Ω S) (hfix : ∀ i, P i ≤ twistedFixedPoints n Φ)
    (hnorm : ∀ i, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hcomm : e6Commutant (((⨆ i, P i).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom : Subgroup
          (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)))
    (hsl2 : S.Nonempty → ∃ (i₀ : ι') (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        P i₀) :
    ∃ KL : KernelLayer n Φ S K ι', KL.P = P := by
  refine ⟨⟨P, hfin, hq, hspan, hfix, hnorm, ?_, ?_, hsl2⟩, rfl⟩
  · intro y hy hc
    refine hPcent_of_std hS hQ hcomm y hy (fun u hu => ?_)
    have hle : (⨆ i, P i) ≤ Subgroup.centralizer ({y} : Set (ModGL Tag.E6 Ω)) :=
      iSup_le fun i u' hu' => Subgroup.mem_centralizer_singleton_iff.2 (hc i u' hu').symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm
  · intro X hX g hg
    have hP := e6Commutant_eq_of_conj_commutant hQ hcomm
    have hX' : X ∈ e6Commutant (((⨆ i, P i : Subgroup (ModGL Tag.E6 Ω)) :
        Set (ModGL Tag.E6 Ω))) := by
      rw [CFSG.RankThree.Lattice.e6Commutant_iSup, Set.mem_iInter]
      exact fun i u hu => hX i u hu
    rw [hP] at hX'
    exact hX' g hg

theorem exists_kernelLayer_single_P {n : ModGL Tag.E6 Ω}
    {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω} {S : Set (Fin Tag.E6.rank → ℤ)} {K : Type} [Field K]
    [Algebra K Ω] (hS : ∀ α ∈ S, IsRoot Tag.E6 α) {w : WeylGroup Tag.E6}
    {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    (hfin : Finite ↥(rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ))
    (hq : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ))
    (hcomm : e6Commutant (((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)))
    (hsl2 : ∃ (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ) :
    ∃ KL : KernelLayer n Φ S K Unit,
      ∀ i, KL.P i = rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ := by
  have hnorm : ∀ _ : Unit, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S,
      y ∈ twistedFixedPoints n Φ → ∀ u ∈ rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ,
        y * u * y⁻¹ ∈ rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ := by
    intro _ y hy hyR u hu
    refine ⟨(Subgroup.mem_normalizer_iff.1
      (torusGroup_sup_rootSpan_le_normalizer' hS hy) u).1 hu.1, ?_⟩
    have hy' : n * Φ y * n⁻¹ = y := mem_twistedFixedPoints.1 hyR
    have hu' : n * Φ u * n⁻¹ = u := mem_twistedFixedPoints.1 hu.2
    refine mem_twistedFixedPoints.2 ?_
    rw [map_mul, map_mul, map_inv]
    calc n * (Φ y * Φ u * (Φ y)⁻¹) * n⁻¹ =
        (n * Φ y * n⁻¹) * (n * Φ u * n⁻¹) * (n * Φ y * n⁻¹)⁻¹ := by group
      _ = y * u * y⁻¹ := by rw [hy', hu']
  have hcomm' : e6Commutant (((⨆ _ : Unit, rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
    rw [iSup_const]
    exact hcomm
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_family_P (n := n) (Φ := Φ) (S := S) (K := K)
    (fun _ : Unit => rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ) hS hQ (fun _ => hfin)
    (fun _ => hq) (fun _ => inf_le_left) (fun _ => inf_le_right) hnorm hcomm'
    (fun _ => by
      obtain ⟨m, h₀, h⟩ := hsl2
      exact ⟨(), m, h₀, h⟩)
  exact ⟨KL, fun i => by rw [hKL]⟩

theorem phi3_A2_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K Unit,
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨w, hw⟩ := hA2
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := phi3_A2_layer_data hf hK hFr hx hw
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_single_P (fun α hα => hα.1) hQ hfin hq hcomm
    ⟨e6Index 0, h₀, hsl⟩
  refine ⟨KL, fun i => ?_⟩
  have hc := phi3_A2_layer_card hf hK hFr (fun α hα => hα.1) (torusRootKernel_smul_stable hFr hx) hw
  have hd := dvd_card_SL_three_of_dvd_phiThree hpq
  rw [← hc] at hd
  rw [hKL i]
  exact hd

theorem phi3_D4_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hD4 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K Unit,
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  obtain ⟨w, hw⟩ := hD4
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := phi3_D4_layer_data hf hK hFr hx hw
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_single_P (fun α hα => hα.1) hQ hfin hq hcomm
    ⟨d4Idx 2, h₀, hsl⟩
  refine ⟨KL, fun i => ?_⟩
  have hc := phi3_D4_layer_card hf hK hFr hx hw
  rw [hKL i, hc, ← hK]
  exact dvd_card_triality_of_dvd_phiThree Nat.card_pos hpq

theorem phi3_A2A2_kernelLayer_dvd_P {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ (w : WeylGroup Tag.E6) (S₁ S₂ : Set (Fin Tag.E6.rank → ℤ))
      (KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K (Fin 2)),
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 ∧
      (w • ·) '' S₁ = parabolicRoots Tag.E6 support13 ∧
      (w • ·) '' S₂ = parabolicRoots Tag.E6 support56 ∧
      (∀ α ∈ S₁, IsRoot Tag.E6 α) ∧ (∀ α ∈ S₁, e6T3W • α ∈ S₁) ∧
      (∀ α ∈ S₂, IsRoot Tag.E6 α) ∧ (∀ α ∈ S₂, e6T3W • α ∈ S₂) ∧
      KL.P = ![rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints (phi3N Ω)
          (Units.map (entrywiseHom Fr)),
        rootSpan Tag.E6 Ω S₂ ⊓ twistedFixedPoints (phi3N Ω)
          (Units.map (entrywiseHom Fr))] ∧
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  classical
  obtain ⟨w, hw⟩ := hA
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Sx := torusRootKernel x with hSxdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hvS := torusRootKernel_smul_stable hFr hx
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
  obtain ⟨hQ₁, hfin₁, hq₁, hcomm₁, h₀, hsl₁⟩ := phi3_A2_layer_gen hf hK hFr hS₁roots hvS₁ hw₁
  obtain ⟨hQ₂, hfin₂, hq₂, hcomm₂, -⟩ := phi3_A2_layer_gen₂ hf hK hFr hS₂roots hvS₂ hw₂
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
    twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) with hP₁
  set P₂ : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω S₂ ⊓
    twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) with hP₂
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
      twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) := by
    rw [Fin.forall_fin_two]
    exact ⟨inf_le_right, inf_le_right⟩
  have hfinF : ∀ k : Fin 2, Finite ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hfin₁, hfin₂⟩
  have hqF : ∀ k : Fin 2, CFSG.IsQuasisimple ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hq₁, hq₂⟩
  have hnormF : ∀ k : Fin 2, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω Sx,
      y ∈ twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) →
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
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_family_P ![P₁, P₂] (fun α hα => hα.1) hQ hfinF hqF hspan
    hfix hnormF hcommP (fun _ => ⟨0, e6Index 0, h₀, hsl₁⟩)
  have hc₁ := phi3_A2_layer_card hf hK hFr hS₁roots hvS₁ hw₁
  have hc₂ := phi3_A2_layer_card₂ hf hK hFr hS₂roots hvS₂ hw₂
  have hd := dvd_card_SL_three_of_dvd_phiThree hpq
  have hdvd : ∀ i, p ∣ Nat.card ↥(KL.P i) := by
    rw [Fin.forall_fin_two, hKL]
    constructor
    · show p ∣ Nat.card ↥P₁
      rw [← hc₁] at hd
      exact hd
    · show p ∣ Nat.card ↥P₂
      rw [← hc₂] at hd
      exact hd
  exact ⟨w, S₁, S₂, KL, hw, hw₁, hw₂, hS₁roots, hvS₁, hS₂roots, hvS₂, hKL, hdvd⟩

theorem phi3_A2A2_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K (Fin 2),
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  obtain ⟨-, -, -, KL, -, -, -, -, -, -, -, -, hdvd⟩ :=
    phi3_A2A2_kernelLayer_dvd_P hf hK hFr hx hA hpq
  exact ⟨KL, hdvd⟩


theorem phi3_perx_dvd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL .E6 L} (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi3N L)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorus (phi3N L) (iterateFrobenius L ℓ f)) :
    ∃ (ι' : Type) (KL : KernelLayer (phi3N L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
        (torusRootKernel (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0)) K ι')
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L),
      Function.Injective ψ ∧
      (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L
        (torusRootKernel (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0))) ∧
      (∀ y, phi3N L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * (phi3N L)⁻¹ =
        ψ y) ∧
      (∀ i, KL.P i ≤ ψ.range) ∧ (∀ i, p ∣ Nat.card ↥(KL.P i)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hℓ : ℓ.Prime := Fact.out
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup hq0 hp hpq'
  have hp7 : 7 ≤ p := (e6Three_data hp hp3 hpq').2.2.2.2.1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := not_dvd_card_weyl_E6 hp (by omega)
  set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
  set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hh).1
  have hb' : rootDiagUnit .E6 b = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hb.symm
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hhp : h ^ p = 1 := hordh ▸ pow_orderOf_eq_one h
  have hh1 : h ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hordh
    exact hp.one_lt.ne hordh
  have htri : torusRootKernel h = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 support13) ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 supportA2A2) ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 d4Support) := by
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨z, -, hzc, hzker, hz0⟩ := exists_column_of_phi3Torus hFr hζ hh hhp
    rw [hzker]
    exact phi3_kernel_types (by omega) z (hz0 hh1) _ hzc
  have hnC : phi3N L ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup _ L _
  have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [CFSG.RankThree.Classical2.rootChar_neg', hα.2, inv_one]⟩
  have hpqN : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by exact_mod_cast hpq
  have finish : ∀ {ι' : Type} (KL : KernelLayer (phi3N L) (Units.map (entrywiseHom Fr))
      (torusRootKernel h) K ι'), (∀ i, p ∣ Nat.card ↥(KL.P i)) →
      ∃ (ι'' : Type) (KL' : KernelLayer (phi3N L)
        (Units.map (entrywiseHom Fr)) (torusRootKernel h) K ι'')
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L),
      Function.Injective ψ ∧
      (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L (torusRootKernel h)) ∧
      (∀ y, phi3N L * Units.map (entrywiseHom Fr) (ψ y) * (phi3N L)⁻¹ = ψ y) ∧
      (∀ i, KL'.P i ≤ ψ.range) ∧ (∀ i, p ∣ Nat.card ↥(KL'.P i)) := by
    intro ι' KL hKL
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
        (subtorusSigma (phi3N L) (Units.map (entrywiseHom Fr)) (torusRootKernel h)) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have hle := rootSpan_le_centralizer (K := L) b (S := torusRootKernel h) (by
        rw [← torusRootKernel_rootDiagUnit, hb])
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hb'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit .E6 a = g0⁻¹ * ι (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ torusRootKernel h :=
      fun a ha => by
        have : a = b := rootDiagUnit_injective (ha.trans hb'.symm)
        rw [this, ← torusRootKernel_rootDiagUnit, hb]
    obtain ⟨ψ, hψinj, -, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data ι adjEmb_injective
      adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK) (phi3N L) g0 hg0C hg0
      hperf hp hordW (fun α hα => hα.1) hrootneg KL.P KL.fin KL.quasi KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup L _)) KL.norm
      (fun y hy hyR hc => by
        obtain ⟨hyH, hyC⟩ := KL.cent y hy hc
        exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩, hyC⟩)
      hx c hcS hkerZ
    exact ⟨ι', KL, ψ, hψinj, hψHQ, hψR, hPψ, hKL⟩
  rcases htri with hreg | hA2 | hA2A2 | hD4
  · have KL : KernelLayer (phi3N L) (Units.map (entrywiseHom Fr)) (torusRootKernel h) K Empty := by
      rw [hreg]
      exact KernelLayer.empty
    exact finish KL (fun e => e.elim)
  · obtain ⟨KL, hKL⟩ := phi3_A2_kernelLayer_dvd hf hK hFr hh hA2 hpqN
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := phi3_A2A2_kernelLayer_dvd hf hK hFr hh hA2A2 hpqN
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := phi3_D4_kernelLayer_dvd hf hK hFr hh hD4 hpqN
    exact finish KL hKL

theorem e6_three_components_dvd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : adjointGroup .E6 K, orderOf x = p →
      ∀ X : Subgroup (adjointGroup .E6 K),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) →
          p ∣ Nat.card X := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_three_frame K hf hK hp hp3 hpq L
  intro x hx X hX
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ι', KL, ψ, hψinj, hψT, hψθ, hPψ, hPd⟩ :=
    phi3_perx_dvd K hf hK hp hp3 hpq L hg0C hg0 hperf hx c hh
  exact CFSG.StandardType.E6Nonsplit.dvd_card_of_isComponentOf_of_layers ψ hψinj KL.P hPψ KL.quasi
    (fun i d u hu => KL.norm i (ψ d) (hψT d) (mem_twistedFixedPoints.2 (hψθ d)) u hu)
    (Z := (torusGroup .E6 L : Set (ModGL .E6 L)))
    (fun a ha b hb => phi3_torusGroup_comm a ha b hb)
    (fun d hd => (KL.cent (ψ d) (hψT d) hd).1) hPd hX

end NonsplitLayers

end CFSG.RankThree.PartOne.KE6
