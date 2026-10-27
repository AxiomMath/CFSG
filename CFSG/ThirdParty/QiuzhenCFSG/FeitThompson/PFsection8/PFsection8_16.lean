module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_13

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u


/-- Peterfalvi `(8.17)`. -/


public theorem theorem_8_16_tiWithNormalizer_of_fusion_centralizers
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {X : Set G}
    (hMnormX : M ≤ Subgroup.normalizer X)
    (hXne : ∃ x : G, x ∈ X ∧ x ≠ 1)
    (hfusion : ∀ x y : G, x ∈ X → y ∈ X →
      section16ConjugateInSubgroup (⊤ : Subgroup G) x y →
        section16ConjugateInSubgroup M x y)
    (hcent : ∀ x : G, x ∈ X → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ M) :
    section16TISubsetWithNormalizer X M := by
  classical
  have hconj_eq_of_mem_M :
      ∀ g : G, g ∈ M → section16ConjugateSet X g = X := by
    intro g hgM
    ext z
    constructor
    · rintro ⟨x, hxX, rfl⟩
      have hnorm := hMnormX hgM
      exact (hnorm x).1 hxX
    · intro hzX
      have hginvM : g⁻¹ ∈ M := M.inv_mem hgM
      have hnorm := hMnormX hginvM
      have hxX : g⁻¹ * z * (g⁻¹)⁻¹ ∈ X := (hnorm z).1 hzX
      refine ⟨g⁻¹ * z * (g⁻¹)⁻¹, hxX, ?_⟩
      group
  have hmemM_of_conj_nontrivial :
      ∀ g z : G, z ∈ X → z ∈ section16ConjugateSet X g → z ≠ 1 → g ∈ M := by
    intro g z hzX hzConj hzNe
    rcases hzConj with ⟨y, hyX, hzy⟩
    have htop : section16ConjugateInSubgroup (⊤ : Subgroup G) y z :=
      ⟨g, by simp, hzy⟩
    rcases hfusion y z hyX hzX htop with ⟨m, hmM, hmconj⟩
    have hcentral : m⁻¹ * g ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (m⁻¹ * g) * y = m⁻¹ * (g * y * g⁻¹) * m * (m⁻¹ * g) := by group
        _ = m⁻¹ * z * m * (m⁻¹ * g) := by rw [hzy]
        _ = y * (m⁻¹ * g) := by
          rw [hmconj]
          group
    have hyNe : y ≠ 1 := by
      intro hy
      exact hzNe (by simpa [hy] using hzy)
    have hmgM : m⁻¹ * g ∈ M := hcent y hyX hyNe hcentral
    have hm_mg : m * (m⁻¹ * g) ∈ M := M.mul_mem hmM hmgM
    simpa [mul_assoc] using hm_mg
  refine ⟨?_, ?_⟩
  · intro g
    by_cases hbad :
        ∃ z : G, z ∈ X ∧ z ∈ section16ConjugateSet X g ∧ z ≠ 1
    · rcases hbad with ⟨z, hzX, hzConj, hzNe⟩
      exact Or.inl (hconj_eq_of_mem_M g
        (hmemM_of_conj_nontrivial g z hzX hzConj hzNe))
    · right
      intro z hz
      by_contra hzNeSet
      have hzNe : z ≠ 1 := by
        intro hz1
        exact hzNeSet (by simp [hz1])
      exact hbad ⟨z, hz.1, hz.2, hzNe⟩
  · apply le_antisymm
    · intro g hgNorm
      rcases hXne with ⟨x, hxX, hxNe⟩
      have hxConj : g * x * g⁻¹ ∈ X := (hgNorm x).1 hxX
      have hconj_mem :
          g * x * g⁻¹ ∈ section16ConjugateSet X g := ⟨x, hxX, rfl⟩
      have hxConjNe : g * x * g⁻¹ ≠ 1 := by
        intro hzero
        apply hxNe
        have h := congrArg (fun y : G => g⁻¹ * y * g) hzero
        simpa [mul_assoc] using h
      exact hmemM_of_conj_nontrivial g (g * x * g⁻¹)
        hxConj hconj_mem hxConjNe
    · exact hMnormX

private theorem theorem_8_16_mem_normalizer_of_nonidentity_conjugateSet_eq
    {G : Type u} [Group G] {H : Subgroup G} {g : G}
    (hEq :
      section16ConjugateSet (section16NonidentityElements (H : Set G)) g =
        section16NonidentityElements (H : Set G)) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  classical
  change ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H
  intro x
  constructor
  · intro hxH
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hxSharp : x ∈ section16NonidentityElements (H : Set G) := ⟨hxH, hx1⟩
      have hxConj :
          g * x * g⁻¹ ∈
            section16ConjugateSet (section16NonidentityElements (H : Set G)) g :=
        ⟨x, hxSharp, rfl⟩
      have hxConjSharp :
          g * x * g⁻¹ ∈ section16NonidentityElements (H : Set G) := by
        simpa [hEq] using hxConj
      exact hxConjSharp.1
  · intro hxConjH
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hxConj_ne : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx1
        have h' := congrArg (fun y : G => g⁻¹ * y * g) h
        simpa [mul_assoc] using h'
      have hxConjSharp :
          g * x * g⁻¹ ∈ section16NonidentityElements (H : Set G) :=
        ⟨hxConjH, hxConj_ne⟩
      have hxConjMem :
          g * x * g⁻¹ ∈
            section16ConjugateSet (section16NonidentityElements (H : Set G)) g := by
        simpa [hEq] using hxConjSharp
      rcases hxConjMem with ⟨y, hySharp, hy_eq⟩
      have hxy : x = y := by
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hy_eq]
          _ = y := by group
      simpa [hxy] using hySharp.1

private theorem theorem_8_16_le_normalizer_nonidentity_of_normal
    {G : Type u} [Group G] {H M : Subgroup G}
    (hHM : H ≤ M) (hNorm : (H.subgroupOf M).Normal) :
    M ≤ Subgroup.normalizer (section16NonidentityElements (H : Set G)) := by
  classical
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hNorm
  intro m hmM
  change ∀ x : G,
    x ∈ section16NonidentityElements (H : Set G) ↔
      m * x * m⁻¹ ∈ section16NonidentityElements (H : Set G)
  intro x
  constructor
  · intro hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormH hmM) x).1 hx.1, ?_⟩
    intro h
    exact hx.2 (by
      have h' := congrArg (fun y : G => m⁻¹ * y * m) h
      simpa [mul_assoc] using h')
  · intro hx
    have hmInv : m⁻¹ ∈ M := M.inv_mem hmM
    have hxH : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hMnormH hmInv) (m * x * m⁻¹)).1 hx.1
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using hxH
    · intro hx1
      exact hx.2 (by simp [hx1])

public theorem theorem_8_16_le_normalizer_centralizerUnion
    {G : Type u} [Group G] {M C H : Subgroup G}
    (hMnormC : M ≤ Subgroup.normalizer (C : Set G))
    (hMnormH : M ≤ Subgroup.normalizer (H : Set G)) :
    M ≤ Subgroup.normalizer (section8CentralizerUnion C H) := by
  classical
  have hforward :
      ∀ m : G, m ∈ M → ∀ y : G, y ∈ section8CentralizerUnion C H →
        m * y * m⁻¹ ∈ section8CentralizerUnion C H := by
    intro m hmM y hy
    rw [section8CentralizerUnion] at hy ⊢
    rcases hy with ⟨x, hxHSharp, hyCentSharp⟩
    refine ⟨m * x * m⁻¹, ?_, ?_⟩
    · refine ⟨(hMnormH hmM x).1 hxHSharp.1, ?_⟩
      intro h
      exact hxHSharp.2 (by
        have h' := congrArg (fun z : G => m⁻¹ * z * m) h
        simpa [mul_assoc] using h')
    · refine ⟨?_, ?_⟩
      · refine ⟨(hMnormC hmM y).1 hyCentSharp.1.1, ?_⟩
        change m * y * m⁻¹ ∈ Subgroup.centralizer ({m * x * m⁻¹} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : y * x = x * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyCentSharp.1.2
        calc
          (m * y * m⁻¹) * (m * x * m⁻¹) = m * (y * x) * m⁻¹ := by group
          _ = m * (x * y) * m⁻¹ := by rw [hcomm]
          _ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      · intro h
        exact hyCentSharp.2 (by
          have h' := congrArg (fun z : G => m⁻¹ * z * m) h
          simpa [mul_assoc] using h')
  intro m hmM
  change ∀ y : G,
    y ∈ section8CentralizerUnion C H ↔ m * y * m⁻¹ ∈ section8CentralizerUnion C H
  intro y
  constructor
  · exact hforward m hmM y
  · intro hy
    have hback := hforward m⁻¹ (M.inv_mem hmM) (m * y * m⁻¹) hy
    simpa [mul_assoc] using hback

public theorem theorem_8_16_le_normalizer_conjugates_by_M
    {G : Type u} [Group G] {M : Subgroup G} {X : Set G} :
    M ≤ Subgroup.normalizer (section16ConjugatesOfSetBySet X (M : Set G)) := by
  classical
  intro m hmM
  change ∀ z : G,
    z ∈ section16ConjugatesOfSetBySet X (M : Set G) ↔
      m * z * m⁻¹ ∈ section16ConjugatesOfSetBySet X (M : Set G)
  intro z
  constructor
  · rintro ⟨x, hx, n, hnM, rfl⟩
    exact ⟨x, hx, m * n, M.mul_mem hmM hnM, by group⟩
  · rintro ⟨x, hx, n, hnM, hnz⟩
    refine ⟨x, hx, m⁻¹ * n, M.mul_mem (M.inv_mem hmM) hnM, ?_⟩
    calc
      z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = m⁻¹ * (n * x * n⁻¹) * m := by rw [hnz]
      _ = (m⁻¹ * n) * x * (m⁻¹ * n)⁻¹ := by group

public theorem theorem_8_16_le_normalizer_union
    {G : Type u} [Group G] {M : Subgroup G} {X Y : Set G}
    (hX : M ≤ Subgroup.normalizer X)
    (hY : M ≤ Subgroup.normalizer Y) :
    M ≤ Subgroup.normalizer (X ∪ Y) := by
  intro m hmM
  change ∀ z : G, z ∈ X ∪ Y ↔ m * z * m⁻¹ ∈ X ∪ Y
  intro z
  constructor
  · intro hz
    rcases hz with hzX | hzY
    · exact Or.inl ((hX hmM z).1 hzX)
    · exact Or.inr ((hY hmM z).1 hzY)
  · intro hz
    rcases hz with hzX | hzY
    · exact Or.inl ((hX hmM z).2 hzX)
    · exact Or.inr ((hY hmM z).2 hzY)


public theorem theorem_8_16_typeII_mf_punctured_tiWithNormalizer
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hSrcII : typeIIDefinitionData M MF) :
    section16TISubsetWithNormalizer
      (section16NonidentityElements (MF : Set G)) M := by
  classical
  rcases hSrcII with ⟨U, W1, W2, _U1, _U0, hP, hCond, _hUcomm, _hUnorm, _hF⟩
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
  rcases hMF.1 with ⟨hMFM, hMFnorm, _hMFnil, _hMFhall⟩
  let F : Subgroup G := section8FittingSubgroup M
  have hMFleF : MF ≤ F := by
    intro z hz
    change z ∈ section8FittingSubgroup M
    rw [← hFittingEq]
    exact (show MF ≤ MF ⊔ subgroupCentralizerIn M MF from le_sup_left) hz
  have hXne :
      ∃ x : G, x ∈ section16NonidentityElements (MF : Set G) ∧ x ≠ 1 := by
    obtain ⟨x, hxW2, hxne⟩ : ∃ x : G, x ∈ W2 ∧ x ≠ 1 := by
      by_contra hnone
      apply hW2ne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · exact False.elim (hnone ⟨x, hx, hx1⟩)
    exact ⟨x, ⟨(hW2le hxW2).1, hxne⟩, hxne⟩
  have hMnormX :
      M ≤ Subgroup.normalizer (section16NonidentityElements (MF : Set G)) :=
    theorem_8_16_le_normalizer_nonidentity_of_normal
      (G := G) (H := MF) (M := M) hMFM hMFnorm
  have hFTI :
      section16TISubset
        (section16NonidentityElements (F : Set G)) := by
    simpa [F] using hCond.2.2
  have hFnormalizer : Subgroup.normalizer (F : Set G) = M := by
    have hW2_card_ne_one : Nat.card W2 ≠ 1 := by
      intro hcard
      exact hW2ne ((Subgroup.eq_bot_iff_card (H := W2)).2 hcard)
    rcases Nat.exists_prime_and_dvd (n := Nat.card W2) hW2_card_ne_one with
      ⟨q, hqprime, hqdiv⟩
    let qP : Nat.Primes := ⟨q, hqprime⟩
    have hqW2 : qP ∈ subgroupPrimeSet W2 := by
      change q ∣ Nat.card W2
      exact hqdiv
    have hqF : qP ∈ subgroupPrimeSet F :=
      section8_subgroupPrimeSet_mono (fun x hx => hMFleF ((hW2le hx).1)) hqW2
    have hM8 : M ∈ section8MaximalSubgroups G := by
      simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
    exact section8_normalizer_fittingSubgroup_eq (G := G) (M := M) (q := qP) hM8 hqF
  have hTI :
      section16TISubset (section16NonidentityElements (MF : Set G)) := by
    intro g
    rcases hFTI g with hFsame | hFsmall
    · have hgNormF : g ∈ Subgroup.normalizer (F : Set G) := by
        exact theorem_8_16_mem_normalizer_of_nonidentity_conjugateSet_eq
          (G := G) (H := F) hFsame
      have hgM : g ∈ M := by
        simpa [hFnormalizer] using hgNormF
      exact Or.inl <| by
        ext x
        constructor
        · rintro ⟨y, hyX, rfl⟩
          exact (hMnormX hgM y).1 hyX
        · intro hxX
          have hginvM : g⁻¹ ∈ M := M.inv_mem hgM
          have hyX :
              g⁻¹ * x * (g⁻¹)⁻¹ ∈ section16NonidentityElements (MF : Set G) :=
            (hMnormX hginvM x).1 hxX
          exact ⟨g⁻¹ * x * (g⁻¹)⁻¹, hyX, by group⟩
    · refine Or.inr ?_
      intro x hx
      have hxF :
          x ∈ section16NonidentityElements (F : Set G) ∩
            section16ConjugateSet (section16NonidentityElements (F : Set G)) g := by
        rcases hx with ⟨hxMF, hxConjMF⟩
        refine ⟨⟨hMFleF hxMF.1, hxMF.2⟩, ?_⟩
        rcases hxConjMF with ⟨y, hyMF, hyx⟩
        exact ⟨y, ⟨hMFleF hyMF.1, hyMF.2⟩, hyx⟩
      exact hFsmall hxF
  have hNormX : Subgroup.normalizer (section16NonidentityElements (MF : Set G)) = M := by
    apply le_antisymm
    · intro g hgNorm
      rcases hXne with ⟨x, hxX, hxne⟩
      have hxConjX : g * x * g⁻¹ ∈ section16NonidentityElements (MF : Set G) :=
        (hgNorm x).1 hxX
      have hxConjF :
          g * x * g⁻¹ ∈ section16ConjugateSet (section16NonidentityElements (F : Set G)) g :=
        ⟨x, ⟨hMFleF hxX.1, hxX.2⟩, rfl⟩
      rcases hFTI g with hFsame | hFsmall
      · have hgNormF : g ∈ Subgroup.normalizer (F : Set G) :=
          theorem_8_16_mem_normalizer_of_nonidentity_conjugateSet_eq
            (G := G) (H := F) hFsame
        simpa [hFnormalizer] using hgNormF
      · have hxInter :
            g * x * g⁻¹ ∈ section16NonidentityElements (F : Set G) ∩
              section16ConjugateSet (section16NonidentityElements (F : Set G)) g :=
          ⟨⟨hMFleF hxConjX.1, hxConjX.2⟩, hxConjF⟩
        have hxOne : g * x * g⁻¹ ∈ ({1} : Set G) := hFsmall hxInter
        exact False.elim (hxConjX.2 (by simpa using hxOne))
    · exact hMnormX
  exact ⟨hTI, hNormX⟩


end CFSG.Section8
