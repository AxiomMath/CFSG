module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

theorem tcjLin_component_lift {K Q : Type*} [Group K] [Group Q] [Finite K]
    (π : K →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (α : MulAut K) (β : MulAut Q) (hαβ : ∀ k, π (α k) = β (π k))
    {A : Subgroup Q} (hA : CFSG.Assembly.IsComponentOf A (fixSubgroup β)) :
    ∃ J : Subgroup K, CFSG.Assembly.IsComponentOf J (fixSubgroup α) ∧ J.map π = A := by
  obtain ⟨hAC, hAsub, hAcomm, hAsimple⟩ := hA
  set A₁ : Subgroup K := A.comap π with hA₁def
  set J : Subgroup K := ⁅A₁, A₁⁆ with hJdef
  have hmov : ∀ x ∈ A₁, ∃ z ∈ Subgroup.center K, α x = x * z := by
    intro x hx
    have h1 : β (π x) = π x := hAC hx
    have h2 : π (α x) = π x := by rw [hαβ, h1]
    have h3 : x⁻¹ * α x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    exact ⟨x⁻¹ * α x, hker h3, by group⟩
  have hfix : J ≤ fixSubgroup α := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨z, hz, hza⟩ := hmov a ha
    obtain ⟨w, hw, hwb⟩ := hmov b hb
    show α ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hza, hwb]
    exact CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
      (Commute.symm (Subgroup.mem_center_iff.1 hz b))
      (Commute.symm (Subgroup.mem_center_iff.1 hz w))
      (Commute.symm (Subgroup.mem_center_iff.1 hw a))
  have hA₁map : A₁.map π = A := Subgroup.map_comap_eq_self_of_surjective hπ A
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp (Group.IsPerfect.mk hAcomm)
  have hJmap : J.map π = A := by
    rw [hJdef, Subgroup.map_commutator, hA₁map, hAperf]
  have hdec : ∀ x ∈ A₁, ∃ k ∈ J, ∃ z ∈ Subgroup.center K, x = k * z := by
    intro x hx
    have hxJ : π x ∈ J.map π := by rw [hJmap]; exact hx
    obtain ⟨k, hk, hkx⟩ := hxJ
    refine ⟨k, hk, k⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
  have hJperf : ⁅J, J⁆ = J := by
    refine le_antisymm (Subgroup.commutator_le_self J) ?_
    show ⁅A₁, A₁⁆ ≤ ⁅J, J⁆
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec a ha
    obtain ⟨k', hk', w, hw, rfl⟩ := hdec b hb
    rw [CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
      (Commute.symm (Subgroup.mem_center_iff.1 hz k'))
      (Commute.symm (Subgroup.mem_center_iff.1 hz w))
      (Commute.symm (Subgroup.mem_center_iff.1 hw k))]
    exact Subgroup.commutator_mem_commutator hk hk'
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := by
    have hperfJ : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
    refine ⟨hperfJ.commutator_eq_top, ?_⟩
    let eJA : ↥(J.map π) ≃* ↥A := MulEquiv.subgroupCongr hJmap
    let f : ↥J →* ↥A := eJA.toMonoidHom.comp (π.subgroupMap J)
    have hfsurj : Function.Surjective f := eJA.surjective.comp (π.subgroupMap_surjective J)
    have hfker : f.ker ≤ Subgroup.center ↥J := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : π.subgroupMap J x = 1 := eJA.injective (by simpa [f] using hx)
      have hx2 : π (x : K) = 1 := congrArg Subtype.val hx1
      have hxz : (x : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr hx2)
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 hxz (y : K))
    obtain ⟨e⟩ := center_quot_equiv_of_surjective hperfJ.commutator_eq_top f hfsurj hfker
    haveI : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hAsimple
    exact MulEquiv.isSimpleGroup e.symm
  have hsub : CFSG.Assembly.IsSubnormal J (fixSubgroup α) := by
    have h1 : CFSG.Assembly.IsSubnormal A₁ ((fixSubgroup β).comap π) := hAsub.comap π
    have hC : fixSubgroup α ≤ (fixSubgroup β).comap π := by
      intro y hy
      show β (π y) = π y
      rw [← hαβ y, mem_fixSubgroup.1 hy]
    have h2 : CFSG.Assembly.IsSubnormal (A₁ ⊓ fixSubgroup α) (fixSubgroup α) :=
      h1.inf_of_le hC
    have hA₁J : J ≤ A₁ := Subgroup.commutator_le_self A₁
    have hJJ : J ≤ A₁ ⊓ fixSubgroup α := le_inf hA₁J hfix
    have hnormA₁ : (J.subgroupOf A₁).Normal := by
      have h : J.subgroupOf A₁ = commutator ↥A₁ := by
        rw [hJdef, ← Subgroup.map_subtype_commutator]
        exact Subgroup.comap_map_eq_self_of_injective A₁.subtype_injective _
      rw [h]
      infer_instance
    have hconj : ∀ h g : K, h ∈ J → g ∈ A₁ → g * h * g⁻¹ ∈ J :=
      (Subgroup.normal_subgroupOf_iff hA₁J).1 hnormA₁
    have hnorm : (J.subgroupOf (A₁ ⊓ fixSubgroup α)).Normal :=
      (Subgroup.normal_subgroupOf_iff hJJ).2 fun h g hh hg => hconj h g hh hg.1
    exact CFSG.Assembly.IsSubnormal.step hJJ hnorm h2
  exact ⟨J, ⟨hfix, hsub, hJq⟩, hJmap⟩

theorem tcjLin_component_transport {S R : Type*} [Group S] [Group R] (e : S ≃* R) (β : MulAut S)
    {J : Subgroup S} (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup β)) :
    CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup (MulAut.congr e β)) := by
  have hfix : (fixSubgroup β).map e.toMonoidHom = fixSubgroup (MulAut.congr e β) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : β y = y := hy
      show MulAut.congr e β (e y) = e y
      simp [MulAut.congr, hy']
    · intro hx
      have hx' : e (β (e.symm x)) = x := hx
      refine ⟨e.symm x, ?_, by simp⟩
      show β (e.symm x) = e.symm x
      apply e.injective
      rw [hx', MulEquiv.apply_symm_apply]
  rw [← hfix]
  exact ⟨Subgroup.map_mono hJ.1, hJ.2.1.map e.toMonoidHom,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm hJ.2.2⟩

theorem tcjLin_component_psl_fixed {K : Type} [Field K] [Finite K] (hSL : SLComponentsTrivial)
    (h2 : (2 : K) = 0) {d : ℕ} (hd : 1 ≤ d) (A : GL (Fin d) K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ p = 1) (J : Subgroup (LargeEvenProj (StatedSL d K)))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup u)) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨c, hc⟩ := isScalar_of_pow_trivial h2 A p u hu hpow
  have hodd : Odd (orderOf A) := odd_orderOf_of_pow_scalar h2 hd A (hp.odd_of_ne_two hp2) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M, hM, hMJ⟩ := tcjLin_component_lift (LargeEvenProjMk (StatedSL d K))
    (QuotientGroup.mk_surjective) ker_projMk_le_center (conjSL A) u
    (fun k => (hu k (conjSL A k) rfl).symm) hJ
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : CFSG.Assembly.IsComponentOf (M.map (StatedSL d K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedSL d K) := by
    rw [← map_fixSubgroup_conjSL A]
    exact ⟨Subgroup.map_mono hM.1, hM.2.1.map (StatedSL d K).subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective M (StatedSL d K).subtype Subtype.val_injective).symm
        hM.2.2⟩
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩⟩ :=
    held_linear_components_gl hSL A hord (M.map (StatedSL d K).subtype)
      ((CFSG.Assembly.isComponentOf_iff_open).1 hM')
  have hperf : commutator ↥(M.map (StatedSL d K).subtype) = ⊤ := hM'.2.2.1
  have hmemJ : ∀ x : ↥M, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J := fun x => by
    rw [← hMJ]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp M.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) = 1 :=
      congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSL d K)) ∈ Subgroup.center ↥(StatedSL d K) :=
      ker_projMk_le_center (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e : ↥M ≃* ↥(M.map (StatedSL d K).subtype) :=
    Subgroup.equivMapOfInjective M (StatedSL d K).subtype hMinj
  let f' : ↥(M.map (StatedSL d K).subtype) →* ↥J := fJ.comp e.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥(M.map (StatedSL d K).subtype) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e.symm x : ↥M) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hx' : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨φ⟩ := center_quot_equiv_of_surjective hperf f' hsurj' hker'
  exact ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ.trans eM⟩⟩

theorem tcjLin_component_canonLabel_eq_typeA_of_labelDict (hP2 : LinLabelDict)
    (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel) (hFam : FamLin labK) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) :
    ∃ (a m : ℕ), 2 ≤ a ∧ canonLabel labJ = ⟨.A, a - 1, m⟩ ∧
      (canonLabel labK).n ∣ m := by
  obtain ⟨K, hK, hKf, d, hd, hcard, A, u, e, hαu, hgraph⟩ := innDiag_linear_data hcen hFam hin
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, n, hqp, hqcard⟩ := FiniteField.card' K
    rw [Nat.card_eq_fintype_card, hqcard] at hcard
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hcard]
      exact dvd_pow_self q (PNat.ne_zero n)
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hJ' : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup u) := by
    rw [← hMEq]
    exact tcjLin_component_transport e α hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom) (fun l : GLALabel => l = labJ) :=
    hasLabel_transport e hlabJ
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    tcjLin_component_psl_fixed SLComponentsTrivial_holds h2 hd A hp hp2 u hgraph hpow
      (J.map e.toMonoidHom) hJ'
  have hEcard : Nat.card E = 2 ^ ((canonLabel labK).n * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hcard, ← pow_mul]
  have hcanon := hP2 ↥(J.map e.toMonoidHom) labJ a _ E ha hEcard hlabJ' ⟨φ⟩
  exact ⟨a, (canonLabel labK).n * Module.finrank K E, ha, hcanon, Dvd.intro _ rfl⟩

theorem tcjLin_innDiagAllLin_of_labelDict (hP2 : LinLabelDict) : InnDiagAllOn FamLin := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨a, m, ha, hcanon, hdvd⟩ :=
    tcjLin_component_canonLabel_eq_typeA_of_labelDict hP2 S p α J labK labJ hFam hp hp2 hcen hin
      hα hlabJ hJ
  show (canonLabel labK).n ∣ (canonLabel labJ).n
  rw [hcanon]
  exact hdvd

theorem innDiagAllLin :
    InnDiagAllOn FamLin :=
  tcjLin_innDiagAllLin_of_labelDict linLabelDict_holds

end CFSG.StandardType.TCJ

end
