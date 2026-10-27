module

public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBWNormNbr
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGGammaHypsK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResXDatumA_compat_K (hRig : GGLabelRigidInput)
    (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs K) (hyB : y ∈ Bs) :
    ∃ (lab : LargeEvenLabel), LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧ (lab.tag = .A ∨ lab.tag = .twA) ∧
      6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
        (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
        (e : Fin lab.rank ≃ Λ),
        M = (CoxeterMatrix.A lab.rank).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
          (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
          (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
          (∃ f : M.Group ≃* ↥(ggAutomizer K Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
          ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧
          ∃ (S : ℕ → LargeEvenLabel → Prop) (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
            GGTBWNormInputNbr S ∧ GGInnerDiagOnLab S p Bs K ∧
              ∃ ψ : Λ → MulAut ↥(ggGamma K hN).range,
                (∀ i (b : ↥Bs), ψ i ((ggGamma K hN).rangeRestrict b) =
                  (ggGamma K hN).rangeRestrict (φ i b)) ∧
                ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hN).range =
                  Subgroup.closure (Set.range ψ) := by
  have hp : p.Prime := Fact.out
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  let S : ℕ → LargeEvenLabel → Prop := fun p lab =>
    (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab
  have hW' : GGTBWNormInputNbr S :=
    ggTBWNormInputNbr_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp (ggHLT_ne_two_of_S hpp hlab hSlab) lab hlab (ggHLT_not_excl_of_S hSlab)
        (by rcases hSlab.1 with h | h <;> rw [h] <;> decide)
  have hM : GGInnerDiagOnLab S p Bs K :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨hP.1, ggHLT_split_of_S hP.1, hP.2.1, hP.2.2⟩) h
  obtain ⟨lab, hN, hlab, hHas, htag, hrank, hdvd, hdvdM, hTor⟩ :=
    ggResXDatumA_core_K hT hLift hH h
  obtain ⟨w, hw⟩ := hTor
  have hp2 : p ≠ 2 := ggHLT_ne_two_of_S hp hlab ⟨htag, hrank, hdvd, hdvdM⟩
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  obtain ⟨hnk, hbk, α, hlin, hpair, hyker⟩ :=
    ggHLT_lin (ggHLT_odd_ggTorM hlab) hdvdM hBs hSdef hN w hw V ι hyB hyK
  let φ : Fin lab.rank → MulAut ↥Bs := fun k => ggTDρB K Bs (ggTDnH w hnk k)
  let hvec : Fin lab.rank → V := fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))
  have hfx : ∀ i, α i (hvec i) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A lab.rank).1 i]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let ψ : Fin lab.rank → MulAut ↥(ggGamma K hN).range :=
    fun k => ggConjAut (ggGamma K hN).range (w.hn k)
  have hcompat : ∀ i (b : ↥Bs), ψ i ((ggGamma K hN).rangeRestrict b) =
      (ggGamma K hN).rangeRestrict (φ i b) := by
    intro i b
    have hgb : (w.n i : G) * b * (w.n i : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnk i) b).mp b.2
    have hconj : MulAut.conj (w.n i) =
        K.normalizerMonoidHom ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ := by
      ext l
      rfl
    apply Subtype.ext
    rw [show ψ i = ggConjAut (ggGamma K hN).range (w.hn i) from rfl, ggConjAut_apply,
      MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj]
    rw [show φ i b = (⟨(w.n i : G) * b * (w.n i : G)⁻¹, hgb⟩ : ↥Bs) from
      Subtype.ext (ggTDρB_apply (X := K) (Bs := Bs) (ggTDnH w hnk i) b)]
    exact ggGamma_conj_normalizer K hN
      ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ b hgb
  have hA : ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hN).range =
      Subgroup.closure (Set.range ψ) := by
    simpa only [ψ] using hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨lab, hlab, hHas, htag, hrank, hdvd, hdvdM, Fin lab.rank, inferInstance, inferInstance,
    CoxeterMatrix.A lab.rank, CartanMatrix.A lab.rank, V, hVadd, hVmod, ι, φ, hvec, α,
    Equiv.refl _, ggHLT_coxeter_reindex_refl _, ggHLT_weyl_A (by omega),
    ggIntCartan_A lab.rank, hlin, hrefl, hpair, ⟨e, he⟩, hcl, S, hN, hW', hM, ψ, hcompat, hA⟩

end CFSG.StandardType
