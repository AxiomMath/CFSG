module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCUnitaryModel InndiagSU

variable {K : Type} [Field K] {n d p : ℕ}

theorem exists_isDiagTorusModelU
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
      ∀ l, φa (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker) ∧
        IsDiagTorusModelU p φ A := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn1 : 1 ≤ n := by omega
  have h := TableBU.unitaryFieldData_of_card hK hn1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by omega) hdq
  let proj : ↥(unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d) :=
    LargeEvenProjMk (unitarySU 2 n K d)
  have hproj : Function.Surjective proj := QuotientGroup.mk'_surjective _
  set Λ : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut L' :=
    ReflInner.liftConj ψ hψ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZ
  have hΛmap : ∀ (e : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (l : L'),
      ψ (Λ e l) = e * ψ l * e⁻¹ := ReflInner.map_liftConj_apply hψ hker
  have hAΛ : ∀ a ∈ A,
      ∃ e : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), Λ e = a := by
    intro a ha
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l : L', (φa ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero =>
        intro l
        simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
    have hφp : φa ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := InndiagSU.ggOutdiagPrime_unitary hK hn1 (by omega) hdq hp hpq hpd
      φa hφaI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφa l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := A.comap Λ
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hnp : ∀ z ∈ proj.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    refine TableBUE.eq_one_of_mem_suScalars h hp hpd ?_ hzp
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    change z ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker at hz
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hz
    exact hz
  obtain ⟨A', hA'map, -, hA'ab, -⟩ :=
    TableBUE.exists_lift_of_noTorsion proj hproj hp hnp hE
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA'ab
  have hcover : ∃ φ₀ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ (φ₀ s) = proj s := by
    rcases (show d = 4 ∨ 5 ≤ d by omega) with hd4 | hd5
    · subst hd4
      have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      refine LineU.exists_hom_of_sections proj ψ hψ hker ?_
      intro E _ _ π hπ hcen
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
        (F := K) (p := 2) (f := n) (n := 4) hK ⟨2, by norm_num⟩ le_rfl hq hπ hcen
    · have hd6 : (d, n) ≠ (6, 1) := by
        rintro ⟨rfl, rfl⟩
        omega
      obtain ⟨-, hcov⟩ := LineU.unitaryCoverAt hK hd5 hd6
      exact hcov L' ψ hψ hker hperf
  obtain ⟨φ₀, hφ₀⟩ := hcover
  have hφ₀s : Function.Surjective φ₀ :=
    LineU.surjective_of_cover proj hproj ψ hker hperf φ₀ hφ₀
  let c : ↥(unitarySU 2 n K d) ≃* ↥(unitarySU 2 n K d) := TableBUE.conjSU h P hP
  let φ : ↥(unitarySU 2 n K d) →* L' := φ₀.comp c.symm.toMonoidHom
  have hφsurj : Function.Surjective φ := hφ₀s.comp c.symm.surjective
  have hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := by
    intro g hg
    have h1 : proj (c.symm g) = 1 := by
      have h2 := hφ₀ (c.symm g)
      rw [show φ₀ (c.symm g) = 1 from hg, map_one] at h2
      exact h2.symm
    have hmem : c.symm g ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
      have h2 : c.symm g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [LargeEvenProjMk, QuotientGroup.ker_mk'] at h2
    have hmap := TableBUE.map_conjSU_suScalars h P hP
    have hg' : c (c.symm g) ∈ (LargeEvenScalars (Fin d) K).subgroupOf
        (unitarySU 2 n K d) := by
      have h3 : c (c.symm g) ∈ (TableBUE.suScalars n d K).map c :=
        Subgroup.mem_map.mpr ⟨c.symm g, hmem, rfl⟩
      rwa [hmap] at h3
    rw [MulEquiv.apply_symm_apply] at hg'
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    exact hg'
  have hfwd : ∀ a ∈ A, ∃ D : ↥(unitarySU 2 n K d),
      (∃ σ : Fin d → Kˣ, (D : GL (Fin d) K) = diagHom d σ) ∧ D ^ p = 1 ∧
        a = MulAut.conj (φ D) := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    have heE : e ∈ E := by
      show Λ e ∈ A
      rw [he]
      exact ha
    have hemap : e ∈ A'.map proj := by
      rw [hA'map]
      exact heE
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hemap
    refine ⟨c y, ?_, ?_, ?_⟩
    · obtain ⟨σ, hσ⟩ := hPd y hy
      exact ⟨σ, hσ⟩
    · rw [← map_pow, hA'ab.2 y hy, map_one]
    · have hφD : φ (c y) = φ₀ y := by
        show φ₀ (c.symm (c y)) = φ₀ y
        rw [MulEquiv.symm_apply_apply]
      rw [hφD]
      exact he.symm.trans (ReflInner.liftConj_eq hψ hker ((hφ₀ y).trans hye))
  refine ⟨φ, hφsurj, hφker, fun a => ⟨fun ha => hfwd a ha, ?_⟩⟩
  rintro ⟨D, ⟨σ, hDσ⟩, hDp, rfl⟩
  apply hsc (φ D)
  · intro a ha
    obtain ⟨D', ⟨σ', hD'σ⟩, -, haD'⟩ := hfwd a ha
    rw [haD', MulAut.conj_apply]
    have hcommGL : (D' : GL (Fin d) K) * (D : GL (Fin d) K) =
        (D : GL (Fin d) K) * (D' : GL (Fin d) K) := by
      rw [hD'σ, hDσ, ← map_mul, ← map_mul, mul_comm]
    have hcomm : D' * D = D * D' := Subtype.ext hcommGL
    have hcommφ : φ D' * φ D = φ D * φ D' := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [hcommφ]
    group
  · rw [← map_pow, hDp, map_one]

end SuNsRootGen

end CFSG.StandardType

end
