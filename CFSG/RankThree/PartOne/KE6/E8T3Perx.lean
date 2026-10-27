module

public import CFSG.RankThree.PartOne.KE6.E8T3Layers
public import CFSG.RankThree.PartOne.KE6.E8T3Seven
public import CFSG.RankThree.PartOne.KE6.E8T3Stab
public import CFSG.RankThree.PartOne.KE6.Phi3Core
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.PartOne.KE.E8Rigid

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix MatrixGroups

theorem e8T3_hq2 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ} (hq : 2 ≤ q) {p : ℕ}
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) : ε = -1 → 2 < q := by
  intro hε1
  by_contra hle
  have hq2 : q = 2 := by omega
  subst hq2
  subst hε1
  have h3 : (p : ℤ) ∣ 3 := by
    have : ((2 : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * ((2 : ℕ) : ℤ) + 1 = 3 := by norm_num
    rwa [this] at hpf
  have h3' : p ∣ 3 := by exact_mod_cast h3
  have := Nat.le_of_dvd (by norm_num) h3'
  omega

theorem e8T3_perx (hD4 : D4TrialityLayer Tag.E8)
    (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (n : ModGL .E8 L)
    (hnm : n ∈ monomialSubgroup .E8 L) (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL .E8 L) (hg0C : g0 ∈ adjointGroup .E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom .E8 L))
    {x : adjointGroup .E8 K} (hx : orderOf x = p) (c : adjointGroup .E8 K)
    (hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      (∀ b : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
        (rootCharKernel b).Nonempty →
        ∀ {B : Subgroup (MulAut (adjointGroup .E8 K))},
          (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
          inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .E8 K))} :
              Set (MulAut (adjointGroup .E8 K)))) ≤
            (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ u : Fin Tag.E8.rank → ℤ,
      weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T3We ε • u := fun u => by rw [hnW]
  have hq2' : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq2 : ε = -1 → 2 < ℓ ^ f := fun h1 => hK ▸ e8T3_hq2 hε hq2' hp3 hpf h1
  set ι : adjointGroup .E8 K →* ModGL .E8 L := adjEmb .E8 K L with hιdef
  set h : ModGL .E8 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E8 b = h := hbh
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
  have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (weylMatrix (e8T3We ε)) Fr hFr hp hb hap hb1
  have hU : ¬ p ∣ Nat.card (dualWeylStabilizer z) :=
    e8T3_dualStab_prime hp hp3 hε hpf hz0 hzM
  have hbS : rootCharKernel b = rootKernel z := by rw [hzk]; rfl
  obtain ⟨u, J, hΦJ, hJne⟩ := exists_smul_rootKernel_eq_parabolicRoots_of_card z hU
  have hSneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hSw : ∀ α ∈ rootCharKernel b, e8T3We ε • α ∈ rootCharKernel b := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 _, by
      rw [← weylMatrix_mulVec, mem_fixedCharTuples_iff.1 hb α, hα.2]
      exact map_one _⟩
  set J' : Finset (Fin Tag.E8.rank) := Finset.univ.filter (fun i => i ∈ J) with hJ'
  have hJJ' : (↑J' : Set (Fin Tag.E8.rank)) = J := by
    ext i
    simp [hJ']
  have hJ'ne : J' ≠ Finset.univ := fun h1 => hJne hz0 (by rw [← hJJ', h1]; simp)
  have hΦJ' : (fun γ => u • γ) '' rootCharKernel b =
      parabolicRoots Tag.E8 (↑J' : Set (Fin Tag.E8.rank)) := by
    rw [hbS, hJJ']
    exact hΦJ
  obtain ⟨ι', P, hfam, hsl2⟩ := e8T3_layers (k := K) hD4 hE6 hε hq2 hf hK n hnm hnC hnWv u J' hJ'ne
    hΦJ' hSneg hSw
  have hstab : ∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit .E8 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup .E8)) := by
    intro a hap' ha1 hmem
    rw [hT] at hmem
    obtain ⟨a', ha', hae⟩ := hmem
    have haa : a' = a := hinj0 hae
    subst haa
    exact rootCharStabilizer_subset_closure_of_fixed (weylMatrix (e8T3We ε)) Fr hFr hp ha' hap'
      ha1 (fun z' hz' hzM' =>
        (dualWeylStabilizer_eq_closure_of_card z' (e8T3_dualStab_prime hp hp3 hε hpf hz' hzM')).le)
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hsub : rootCharKernel b ⊆ rootCharKernel b := fun α hα => hα
  have hle := rootSpan_le_centralizer (K := L) b hsub
  have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ (rootCharKernel b)) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hbh'] at h1
    exact h1
  have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a ⊆ rootCharKernel b := fun a ha => by
    rw [hker a ha]
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, hψV⟩ := sigma_embedding_data_of_stab ι adjEmb_injective
    adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp hstab (fun α hα => hα.1) hSneg
    P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
  refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
    (hψV V hVn hVs v hv), ?_⟩
  intro b' hb'h hne B hB
  have hC : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨α₀, hα₀⟩ := hne
  rw [hker b' hb'h] at hα₀
  obtain ⟨i₀, m, h₀, hh₀⟩ := hsl2 ⟨α₀, hα₀⟩
  intro η hη
  have hfix : ∀ (i : ι') (d : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))),
      ψ d ∈ P i → η (d : adjointGroup .E8 K) = d := by
    intro i d hd
    set P' : Subgroup (adjointGroup .E8 K) :=
      ((P i).comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype
      with hP'
    have hPD : P' ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) :=
      Subgroup.map_subtype_le _
    have hPn : ∀ e ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)), ∀ u ∈ P',
        e * u * e⁻¹ ∈ P' := by
      rintro e he _ ⟨u, hu, rfl⟩
      refine ⟨⟨e, he⟩ * u * ⟨e, he⟩⁻¹, ?_, rfl⟩
      change ψ (⟨e, he⟩ * u * ⟨e, he⟩⁻¹) ∈ P i
      rw [map_mul ψ, map_mul ψ, map_inv ψ]
      exact hPnorm i (ψ ⟨e, he⟩) (hψHQ _) (mem_twistedFixedPoints.2 (hψR _)) (ψ u) hu
    have hmapeq : ((P i).comap ψ).map ψ = P i := by
      rw [Subgroup.map_comap_eq, inf_of_le_right (hPψ i)]
    have hPq' : CFSG.IsQuasisimple P' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((((Subgroup.equivMapOfInjective ((P i).comap ψ) ψ hψinj).trans
          (MulEquiv.subgroupCongr hmapeq)).symm).trans
          (Subgroup.equivMapOfInjective ((P i).comap ψ)
            (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype
            (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype_injective))
        (hPq i)
    exact core_fixes_normal_quasisimple hp hC hB hPD hPn hPq' hη (d : adjointGroup .E8 K)
      ⟨d, hd, rfl⟩
  set T : ModGL .E8 L := (adjEmb .E8 K L c)⁻¹ * g0 with hT'
  have hιψ : ∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      adjEmb .E8 K L (d : adjointGroup .E8 K) = T * ψ d * T⁻¹ := by
    intro d
    rw [hψ d, hT']
    simp only [map_mul, map_inv, hιdef]
    group
  set h'' : ModGL .E8 L := (adjEmb .E8 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 K, ∃ y : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      ψ y ∈ P i₀ ∧
      adjEmb .E8 K L (y : adjointGroup .E8 K) = h'' * simpleRootSL2 .E8 L m
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    obtain ⟨y, hy⟩ := hPψ i₀ hmem
    refine ⟨y, hy ▸ hmem, ?_⟩
    rw [hιψ y, hy, hh'', hT']
    group
  let Z : Subgroup (MulAut (adjointGroup .E8 K)) :=
    { carrier := {η' | ∀ y : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        ψ y ∈ P i₀ → η' (y : adjointGroup .E8 K) = y}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [MulAut.mul_apply, hb y hy, ha y hy]
      one_mem' := fun y _ => rfl
      inv_mem' := fun {a} ha y hy => by
        have := ha y hy
        calc a⁻¹ (y : adjointGroup .E8 K) = a⁻¹ (a (y : adjointGroup .E8 K)) := by
              rw [this]
          _ = y := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
  have hηZ : η ∈ Z := fun y hy => hfix i₀ y hy
  have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup .E8 K) (Y : SL2 K),
      baseChangeGL (algebraMap K L) (u : ModGL .E8 K) =
        h'' * simpleRootSL2 .E8 L m (conjGL (1 : GL (Fin 2) L)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ → η' u = u := by
    intro η' hη'Z u Y hu
    obtain ⟨y, hyP, hy⟩ := hKey Y
    rw [conjGL_one, ← hy] at hu
    have hu' : adjEmb .E8 K L u = adjEmb .E8 K L (y : adjointGroup .E8 K) := by
      rw [adjEmb_apply, hu]
    rw [adjEmb_injective hu']
    exact hη'Z y hyP
  have hU' : ∀ Y : SL2 K, h'' * simpleRootSL2 .E8 L m
      (conjGL (1 : GL (Fin 2) L) (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ ∈
      (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
    intro Y
    obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one, ← hy]
    exact ⟨((y : adjointGroup .E8 K) : ModGL .E8 K), (y : adjointGroup .E8 K).2, rfl⟩
  exact (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E8
    (Or.inr (Or.inr rfl)) K L m 1 h'' hU' Z hZ).2.2.2 rfl η hηZ

end CFSG.RankThree.PartOne.KE6
