module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nP2H_not_excl_of_S {r₀ p : ℕ} {lab : LargeEvenLabel}
    (h : GGTWRowPred r₀ p lab) : ¬ GGTBWExcl lab := by
  unfold GGTWRowPred at h
  rintro (hF4 | ⟨hBC, -⟩)
  · rcases h.1 with h | h <;> rw [h] at hF4 <;> exact absurd hF4 (by decide)
  · rcases h.1 with h | h <;> rw [h] at hBC <;> exact absurd hBC (by decide)

private lemma l05nP2H_ne_two_of_S {r₀ p : ℕ} {lab : LargeEvenLabel}
    (hpp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGTWRowPred r₀ p lab) :
    p ≠ 2 := by
  unfold GGTWRowPred at h
  intro h2
  have heven : Even (ggTorM lab) := even_iff_two_dvd.mpr (h2 ▸ h.2.2.2.1)
  exact (Nat.not_even_iff_odd.mpr (ggHLT_odd_ggTorM hlab)) heven

private lemma l05nP2H_split_of_S {r₀ p : ℕ} {lab : LargeEvenLabel}
    (h : GGTWRowPred r₀ p lab) : LargeEvenSplit p lab := by
  unfold GGTWRowPred at h
  obtain ⟨htag, -, -, hdvdM, -⟩ := h
  unfold LargeEvenSplit
  unfold ggTorM at hdvdM
  rcases htag with hA | htwA
  · left
    refine ⟨?_, ?_⟩
    · rw [hA]; simp [LargeEvenUntwisted]
    · rwa [if_neg (by rw [hA]; decide)] at hdvdM
  · right; left
    refine ⟨?_, ?_, ?_⟩
    · rw [htwA]; simp [LargeEvenUntwisted]
    · rw [htwA]; decide
    · rwa [if_pos (by rw [htwA]; decide)] at hdvdM

private lemma l05nP2H_not_twisted_of_S {r₀ p : ℕ} {lab : LargeEvenLabel}
    (h : GGTWRowPred r₀ p lab) : ¬ GGOutdiagTwistedLabel lab := by
  unfold GGTWRowPred at h
  rintro (h6 | h3 | h2)
  · rcases h.1 with h | h <;> rw [h] at h6 <;> exact absurd h6 (by decide)
  · rcases h.1 with h | h <;> rw [h] at h3 <;> exact absurd h3 (by decide)
  · rcases h.1 with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)

theorem ggResXDatumA_compat_from
    {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom r₀)
    (hLift : GGTBTorLiftAFrom r₀) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs L) (hxB : x ∈ Bs) :
    ∃ (lab : LargeEvenLabel), LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧ GGTWRowPred r₀ p lab ∧
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
        (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
        (e : Fin lab.rank ≃ Λ),
        M = (CoxeterMatrix.A lab.rank).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
          (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
          (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
          (∃ f : M.Group ≃* ↥(ggAutomizer L Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
          ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
          ∃ (S : ℕ → LargeEvenLabel → Prop) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
            GGTBWNormInputOn S ∧ GGInnerDiagOnLab S p Bs L ∧
              (∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T) ∧
              ∃ ψ : Λ → MulAut ↥(ggGamma L hN).range,
                (∀ i (b : ↥Bs), ψ i ((ggGamma L hN).rangeRestrict b) =
                  (ggGamma L hN).rangeRestrict (φ i b)) ∧
                ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hN).range =
                  Subgroup.closure (Set.range ψ) := by
  have hp : p.Prime := Fact.out
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp', hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => GGTWRowPred r₀ p lab
  have hW' : GGTBWNormInputOn S :=
    ggTBWNormInputOn_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp (l05nP2H_ne_two_of_S hpp hlab hSlab) lab hlab (l05nP2H_not_excl_of_S hSlab)
        (by rcases hSlab.1 with h | h <;> rw [h] <;> decide)
  have hM : GGInnerDiagOnLab S p Bs L :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨hP.1, l05nP2H_split_of_S hP.1, hP.2.1, hP.2.2⟩) h
  obtain ⟨lab, hN, hlab, hHas, hP, hTor⟩ := ggResXDatumA_core_L_from hT hLift hH h
  unfold GGTWRowPred at hP
  have hrank : r₀ ≤ lab.rank := hP.2.1
  obtain ⟨w, hw⟩ := hTor
  have hp2 : p ≠ 2 := l05nP2H_ne_two_of_S hp hlab hP
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInputOn_not_twisted G p B x L hH.1.1
      (largeEvenMarking_mono
        (fun lab R _ I F θ hP =>
          ⟨l05nP2H_not_twisted_of_S hP.1, l05nP2H_split_of_S hP.1, hBBs.trans hP.2.1,
            fun b hb => hP.2.2 b (hBBs hb)⟩) h)
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  obtain ⟨hnk, hbk, α, hlin, hpair, hxker⟩ :=
    ggHLT_lin (ggHLT_odd_ggTorM hlab) hP.2.2.2.1 hBs hSdef hN w hw V ι hxB hxL
  let φ : Fin lab.rank → MulAut ↥Bs := fun k => ggTDρB L Bs (ggTDnH w hnk k)
  let hvec : Fin lab.rank → V := fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))
  have hfx : ∀ i, α i (hvec i) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A lab.rank).1 i]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let ψ : Fin lab.rank → MulAut ↥(ggGamma L hN).range :=
    fun k => ggConjAut (ggGamma L hN).range (w.hn k)
  have hcompat : ∀ i (b : ↥Bs), ψ i ((ggGamma L hN).rangeRestrict b) =
      (ggGamma L hN).rangeRestrict (φ i b) := by
    intro i b
    have hgb : (w.n i : G) * b * (w.n i : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnk i) b).mp b.2
    have hconj : MulAut.conj (w.n i) =
        L.normalizerMonoidHom ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ := by
      ext l
      rfl
    apply Subtype.ext
    rw [show ψ i = ggConjAut (ggGamma L hN).range (w.hn i) from rfl, ggConjAut_apply,
      MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj]
    rw [show φ i b = (⟨(w.n i : G) * b * (w.n i : G)⁻¹, hgb⟩ : ↥Bs) from
      Subtype.ext (ggTDρB_apply (X := L) (Bs := Bs) (ggTDnH w hnk i) b)]
    exact ggGamma_conj_normalizer L hN
      ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ b hgb
  have hA : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hN).range =
      Subgroup.closure (Set.range ψ) := by
    simpa only [ψ] using hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨lab, hlab, hHas, hP, Fin lab.rank, inferInstance, inferInstance,
    CoxeterMatrix.A lab.rank, CartanMatrix.A lab.rank, V, hVadd, hVmod, ι, φ, hvec, α,
    Equiv.refl _, ggHLT_coxeter_reindex_refl _, ggHLT_weyl_A (by omega),
    ggIntCartan_A lab.rank, hlin, hrefl, hpair, ⟨e, he⟩, hcl, S, hN, hW', hM, hnc, ψ, hcompat, hA⟩

theorem ggResXDatumA_compat_from_K {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hRig : GGLabelRigidInput)
    (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs K) (hyB : y ∈ Bs) :
    ∃ (lab : LargeEvenLabel), LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧ GGTWRowPred r₀ p lab ∧
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
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => GGTWRowPred r₀ p lab
  have hW' : GGTBWNormInputNbr S :=
    ggTBWNormInputNbr_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp (l05nP2H_ne_two_of_S hpp hlab hSlab) lab hlab (l05nP2H_not_excl_of_S hSlab)
        (by rcases hSlab.1 with h | h <;> rw [h] <;> decide)
  have hM : GGInnerDiagOnLab S p Bs K :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨hP.1, l05nP2H_split_of_S hP.1, hP.2.1, hP.2.2⟩) h
  obtain ⟨lab, hN, hlab, hHas, hP, hTor⟩ := ggResXDatumA_core_K_from hT hLift hH h
  unfold GGTWRowPred at hP
  have hrank : r₀ ≤ lab.rank := hP.2.1
  obtain ⟨w, hw⟩ := hTor
  have hp2 : p ≠ 2 := l05nP2H_ne_two_of_S hp hlab hP
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
    ggHLT_lin (ggHLT_odd_ggTorM hlab) hP.2.2.2.1 hBs hSdef hN w hw V ι hyB hyK
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
  refine ⟨lab, hlab, hHas, hP, Fin lab.rank, inferInstance, inferInstance,
    CoxeterMatrix.A lab.rank, CartanMatrix.A lab.rank, V, hVadd, hVmod, ι, φ, hvec, α,
    Equiv.refl _, ggHLT_coxeter_reindex_refl _, ggHLT_weyl_A (by omega),
    ggIntCartan_A lab.rank, hlin, hrefl, hpair, ⟨e, he⟩, hcl, S, hN, hW', hM, ψ, hcompat, hA⟩

end CFSG.StandardType

end
