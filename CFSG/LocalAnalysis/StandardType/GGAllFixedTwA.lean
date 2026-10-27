module

public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
public import CFSG.LieType.SemisimpleCentralizers.UnitCentralizerSolvable
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.GroupTheory.FixedCentralQuotientFamily
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GroupTheory.FixedCentralQuotientFamily CFSG.LieType.SemisimpleCentralizers

set_option maxHeartbeats 1600000 in
theorem largeEvenLabelAll_twA_fullFixedSolvable_of_hasNormalPComplement
    (p f l : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ (2 ^ f) ^ 2 - 1) (hl : 3 ≤ l) :
    LargeEvenLabelAll ⟨.twA, l, f⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsPGroup p E → IsMulCommutative E →
        let F : Subgroup R :=
          ggFixedSubgroup E
        CFSG.HasNormalPComplement p ↥⁅F, F⁆ → Group.IsSolvable ↥F := by
  classical
  have hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have h := Nat.sq_sub_sq (2 ^ f) 1
      simpa [mul_comm] using h
    rcases hp.dvd_mul.mp (hfac ▸ hpdvd) with h | h
    · exact Or.inl h
    · exact Or.inr h
  intro Q hQ
  change LargeEvenRecipeUnitary (l + 1) (2 ^ f) Q at hQ
  refine recipeUnitary_and (d := l + 1) (q := 2 ^ f) (Q := Q) (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsPGroup p E → IsMulCommutative E →
      let F : Subgroup R :=
        ggFixedSubgroup E
      CFSG.HasNormalPComplement p ↥⁅F, F⁆ → Group.IsSolvable ↥F) ?_ hQ
  · intro K _ _ hK
    have hf : 1 ≤ f := by
      by_contra h
      have h0 : f = 0 := by omega
      rw [h0] at hK
      norm_num at hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    have hF : Nat.card K = (2 ^ f) ^ 2 := hK
    have h : UnitaryFieldData 2 f K :=
      ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
    haveI : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hF, pow_mul])
    intro E hEI hE hEab
    let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ f))
    let I : Set (MulAut R) :=
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ f)))
        (LargeEvenGUSet (Fin (l + 1)) K (2 ^ f))
    let F0 : Subgroup R :=
      ggFixedSubgroup E
    change CFSG.HasNormalPComplement p ↥⁅F0, F0⁆ → Group.IsSolvable ↥F0
    intro hNPC
    let φ : E →* MulAut R :=
      { toFun := fun e => (e : MulAut R)⁻¹
        map_one' := by simp
        map_mul' := fun e f => by
          change (((e * f : E) : MulAut R))⁻¹ =
            ((e : E) : MulAut R)⁻¹ * ((f : E) : MulAut R)⁻¹
          have hcomm : ((e : E) : MulAut R) * ((f : E) : MulAut R) =
              ((f : E) : MulAut R) * ((e : E) : MulAut R) := by
            simpa using congrArg (fun x : E => (x : MulAut R)) (hEab.is_comm.comm e f)
          calc (((e * f : E) : MulAut R))⁻¹
              = (((e : E) : MulAut R) * ((f : E) : MulAut R))⁻¹ := by
                  rw [Subgroup.coe_mul]
            _ = ((f : E) : MulAut R)⁻¹ * ((e : E) : MulAut R)⁻¹ := by
                  rw [_root_.mul_inv_rev]
            _ = ((e : E) : MulAut R)⁻¹ * ((f : E) : MulAut R)⁻¹ := by
                  have h := congrArg (fun x : MulAut R => x⁻¹) hcomm
                  simpa [_root_.mul_inv_rev] using h }
    let G : Type := R ⋊[φ] E
    let inl : R →* G := SemidirectProduct.inl
    let inr : E →* G := SemidirectProduct.inr
    let E' : Subgroup G := inr.range
    let d : ℕ := l + 1
    have hd : 4 ≤ d := by dsimp only [d]; omega
    have hd3 : 3 ≤ d := by omega
    let U : Type := SU (unitaryInvolution K 2 f) d
    let τ : K ≃+* K := RingEquiv.refl K
    obtain ⟨P, hP⟩ := exists_wittMatrix hF d
    let ψ₀ : U →* R :=
      MpStdSU.stdProj (F := K) (K := K) (f := f) (n := d) hF τ P hP
    let ψ : U →* G := inl.comp ψ₀
    have hψ₀surj : Function.Surjective ψ₀ :=
      MpStdSU.stdProj_surjective (F := K) (K := K) (f := f) (n := d) hF τ P hP
    have hker₀ : ψ₀.ker = Subgroup.center U :=
      MpStdSU.ker_stdProj (F := K) (K := K) (f := f) (n := d) hF τ P hP
        hd3 (MpStdSU.ne_three_two hd)
    have hker : ψ.ker ≤ Subgroup.center U := by
      have hker_eq : ψ.ker = ψ₀.ker := by
        ext u
        dsimp only [ψ]
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact ⟨fun h => SemidirectProduct.inl_injective (by simpa using h),
          fun h => by rw [h, map_one]⟩
      rw [hker_eq, hker₀]
    have hrange : ψ.range = (inl : R →* G).range := by
      dsimp only [ψ]
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj, Subgroup.map_top]
    let θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R :=
      MpStdSU.stdEquiv (F := K) (K := K) (f := f) (n := d) hF hF τ P hP ψ
        hd3 (MpStdSU.ne_three_two hd) hker
    have hmem_inl : ∀ r : R, inl r ∈ ψ.range := by
      intro r
      rw [hrange]
      exact ⟨r, rfl⟩
    have hθ_inl : ∀ r : R,
        θ (QuotientGroup.mk' (Subgroup.center ↥ψ.range) ⟨inl r, hmem_inl r⟩) = r := by
      intro r
      obtain ⟨u, rfl⟩ := hψ₀surj r
      have hx : (⟨inl (ψ₀ u), hmem_inl (ψ₀ u)⟩ : ↥ψ.range) = ψ.rangeRestrict u :=
        Subtype.ext rfl
      rw [hx]
      simpa [MpStdSU.rangeProj] using
        MpStdSU.stdEquiv_rangeProj (F := K) (K := K) (f := f) (n := d) hF hF τ P hP ψ
          hd3 (MpStdSU.ne_three_two hd) hker u
    letI : Finite R := inferInstance
    letI : Finite G := Finite.of_equiv (R × E) SemidirectProduct.equivProd.symm
    have hN : ∀ e' ∈ E', e' ∈ Subgroup.normalizer (ψ.range : Set G) := by
      intro e' he'
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp he'
      rw [hrange, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨(e : MulAut R)⁻¹ r, by
          simpa [φ] using (SemidirectProduct.inl_aut (φ := φ) e r)⟩
      · intro hx
        obtain ⟨r, hr⟩ := hx
        refine ⟨(e : MulAut R) r, ?_⟩
        calc inl ((e : MulAut R) r)
            = (inr e)⁻¹ * inl r * inr e := by
                simpa [φ] using (SemidirectProduct.inl_aut_inv (φ := φ) e r)
          _ = (inr e)⁻¹ * (inr e * x * (inr e)⁻¹) * inr e := by rw [hr]
          _ = ((inr e)⁻¹ * inr e) * (x * ((inr e)⁻¹ * inr e)) := by
              simp only [_root_.mul_assoc]
          _ = x := by
              rw [_root_.inv_mul_cancel (inr e), _root_.one_mul, _root_.mul_one]
    have hrev : GGRevProp (Unitary.rootDatum hF d) ψ ψ.range (ggInndiag R I) θ :=
      MpStdSU.ggRevProp_stdEquiv (F := K) (K := K) (f := f) (n := d) hF hF τ P hP
        hd ψ hker
    have hdiag : ∀ e' ∈ E', GGPsiInnerDiag (Unitary.rootDatum hF d) ψ e' := by
      intro e' he'
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp he'
      have heI : (e : MulAut R) ∈ I := hEI e.2
      refine hrev (inr e) (hN (inr e) (MonoidHom.mem_range.mpr ⟨e, rfl⟩))
        ⟨(e : MulAut R), subset_ggInndiag heI, ?_⟩
      intro l l' hrel
      obtain ⟨r, hr⟩ : ∃ r : R, (l : G) = inl r := by
        have hl : (l : G) ∈ (inl : R →* G).range := by
          simpa [hrange] using l.2
        obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hl
        exact ⟨r, hr.symm⟩
      have hl_eq : l = ⟨inl r, hmem_inl r⟩ := Subtype.ext hr
      have hl'_eq : (l' : G) = inl ((e : MulAut R) r) := by
        rw [hrel, hl_eq]
        simpa [φ] using (SemidirectProduct.inl_aut_inv (φ := φ) e r).symm
      have hθl : θ (QuotientGroup.mk l) = r := by
        rw [hl_eq]
        exact hθ_inl r
      have hθl' : θ (QuotientGroup.mk l') = (e : MulAut R) r := by
        have hl'_sub : l' = ⟨inl ((e : MulAut R) r), hmem_inl _⟩ := Subtype.ext hl'_eq
        rw [hl'_sub]
        exact hθ_inl _
      rw [hθl, hθl']
    have hE' : IsPGroup p E' := by
      have htop : IsPGroup p ↥(⊤ : Subgroup E) :=
        IsPGroup.of_equiv hE Subgroup.topEquiv.symm
      have hmap : IsPGroup p ↥(Subgroup.map inr (⊤ : Subgroup E)) := htop.map inr
      have hEq : Subgroup.map inr (⊤ : Subgroup E) = E' := by
        rw [Subgroup.map_top]
      exact hEq ▸ hmap
    have hmemF : ∀ r : R, r ∈ F0 ↔ ∀ e : E, (e : MulAut R) r = r := by
      intro r
      change (∀ a ∈ E, a r = r) ↔ ∀ e : E, (e : MulAut R) r = r
      exact ⟨fun h e => h e.1 e.2, fun h a ha => h ⟨a, ha⟩⟩
    have hfix : ψ.range ⊓ Subgroup.centralizer (E' : Set G) = F0.map inl := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxrange, hxC⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (by rwa [hrange] at hxrange)
        refine Subgroup.mem_map.mpr ⟨r, ?_, hr⟩
        rw [hmemF]
        intro e
        have he' : inr e ∈ E' := MonoidHom.mem_range.mpr ⟨e, rfl⟩
        have hcent := Subgroup.mem_centralizer_iff.mp hxC (inr e) he'
        rw [← hr] at hcent
        have heq : inl r = inl ((e : MulAut R) r) := by
          calc inl r = (inr e)⁻¹ * (inr e * inl r) := by simp
            _ = (inr e)⁻¹ * (inl r * inr e) := by rw [hcent]
            _ = (inr e)⁻¹ * inl r * inr e := by rw [mul_assoc]
            _ = inl ((e : MulAut R) r) := by
                simpa [φ] using (SemidirectProduct.inl_aut_inv (φ := φ) e r).symm
        exact (SemidirectProduct.inl_injective heq).symm
      · intro hx
        obtain ⟨r, hrF, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [hrange]
          exact ⟨r, rfl⟩
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hy
          have her : (e : MulAut R) r = r := (hmemF r).mp hrF e
          have heinv : (e : MulAut R)⁻¹ r = r := by
            calc (e : MulAut R)⁻¹ r = (e : MulAut R)⁻¹ ((e : MulAut R) r) := by rw [her]
              _ = r := by simp
          have hcalc : inr e * inl r = inl ((e : MulAut R)⁻¹ r) * inr e := by
            have h : inl ((e : MulAut R)⁻¹ r) = inr e * inl r * (inr e)⁻¹ := by
              simpa [φ] using (SemidirectProduct.inl_aut (φ := φ) e r)
            calc
              inr e * inl r = (inr e * inl r) * ((inr e)⁻¹ * inr e) := by
                rw [_root_.inv_mul_cancel, _root_.mul_one]
              _ = (inr e * inl r * (inr e)⁻¹) * inr e := by
                simp only [_root_.mul_assoc]
              _ = inl ((e : MulAut R)⁻¹ r) * inr e := by rw [← h]
          rw [hcalc, heinv]
    have hNPC' : CFSG.HasNormalPComplement p
        ↥⁅ψ.range ⊓ Subgroup.centralizer (E' : Set G),
           ψ.range ⊓ Subgroup.centralizer (E' : Set G)⁆ := by
      rw [hfix]
      have hmap := CFSG.RankThree.Coprime.hasNormalPComplement_map (p := p)
        (f := (inl : R →* G)) hNPC
      rwa [Subgroup.map_commutator] at hmap
    have hsolvG : Group.IsSolvable
        ↥(ψ.range ⊓ Subgroup.centralizer (E' : Set G)) :=
      isSolvable_unitary_centralizer_of_hasNormalPComplement_field (m := l) h hF hd hker hp hp2 hpq hE' hdiag hNPC'
    rw [hfix] at hsolvG
    letI : Group.IsSolvable ↥(F0.map inl) := hsolvG
    exact Group.isSolvable_of_isSolvable_injective
      (f := MonoidHom.subgroupMap (inl : R →* G) F0)
      (MonoidHom.subgroupMap_injective (inl : R →* G) F0 SemidirectProduct.inl_injective)


theorem largeEvenLabelAll_unitary_fullFixedSolvable
    {lab : LargeEvenLabel}
    (hrow : (lab.tag = .twA ∧ 3 ≤ lab.rank) ∨ (lab.tag = .twD ∧ lab.rank = 3))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E) := by
  have hr : 3 ≤ lab.rank := by rcases hrow with h | h <;> omega
  have hdonor := largeEvenLabelAll_twA_fullFixedSolvable_of_hasNormalPComplement
    p lab.n lab.rank hp hp2 hpq hr
  intro Q hQ
  have hrecipe : LargeEvenRawDatum ⟨.twA, lab.rank, lab.n⟩ Q := by
    rcases hrow with ⟨htag, hr⟩ | ⟨htag, hr⟩
    · simpa only [LargeEvenRawDatum, htag] using hQ
    · simpa [LargeEvenRawDatum, htag, hr] using hQ
  have hres : LargeEvenRawDatum ⟨.twA, lab.rank, lab.n⟩ (fun R _ I F =>
      Q R I F ∧ ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E)) := by
    refine largeEvenRawDatum_mono ?_ (hdonor Q hrecipe)
    rintro R _ I F ⟨hQ, hsolv⟩
    refine ⟨hQ, ?_⟩
    intro E hEI hE hNPC
    apply hsolv E hEI hE.isPGroup
    · exact hE.1
    · have h := CFSG.hasNormalPComplement_of_equiv p
        ((_root_.commutator ↥(ggFixedSubgroup E)).equivMapOfInjective
          (ggFixedSubgroup E).subtype (ggFixedSubgroup E).subtype_injective) hNPC
      rwa [Subgroup.map_subtype_commutator] at h
  rcases hrow with ⟨htag, hr⟩ | ⟨htag, hr⟩
  · simpa only [LargeEvenRawDatum, htag] using hres
  · simpa [LargeEvenRawDatum, htag, hr] using hres

theorem isSolvable_inf_centralizer_of_unitary_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      ((lab.tag = .twA ∧ 3 ≤ lab.rank) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
      p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => ((lab.tag = .twA ∧ 3 ≤ lab.rank) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
      p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun _ _ hs => largeEvenLabelAll_unitary_fullFixedSolvable hs.1 hp hp2 hs.2)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ := largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE⟩, hrow⟩ := hP
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ
    (hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
      (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ))

end CFSG.StandardType
