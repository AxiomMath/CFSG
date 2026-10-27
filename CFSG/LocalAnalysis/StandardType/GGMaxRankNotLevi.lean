module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankSide
public import CFSG.LocalAnalysis.StandardType.GGMaxRankNine
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggMaxRank_levi_false {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (hX : GGMaxRankSideChain p Bs X J eJ)
    {ΛJ : Type} [Fintype ΛJ] [DecidableEq ΛJ] {MJ : CoxeterMatrix ΛJ} (hMJ : GGIsWeylMatrix MJ)
    {V' : Type} [AddCommGroup V'] [Module (ZMod p) V'] (ι' : Additive ↥Bs ≃+ V')
    (φ' : ΛJ → MulAut ↥Bs) (h' : ΛJ → V') (α' : ΛJ → Module.Dual (ZMod p) V')
    (hlin' : ∀ i w, ggLin (p := p) ι' (φ' i) w = w - α' i w • h' i)
    (hrefl' : ∀ i, GGIsReflection p (φ' i))
    (hfJ : ∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs), ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ' j)
    (hAJgen : ggAutomizer J Bs = Subgroup.closure (Set.range φ'))
    (hconj : GGReflConjSimple p (ggAutomizer J Bs) φ')
    (hind : Fintype.card ΛJ = 8 → LinearIndependent (ZMod p) h') : False := by
  classical
  have hM'A8 : GGIsWeylMatrix (CoxeterMatrix.A 8) := by
    refine Or.inl ⟨8, Equiv.refl _, by norm_num, Or.inl ?_⟩
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl
  obtain ⟨-, V, instACV, instMV, ι, φ, h, α, hlin, hrefl, hchain, -, -, -, hdim7, -, -⟩ := hX
  letI : AddCommGroup V := instACV
  letI : Module (ZMod p) V := instMV
  obtain ⟨fJ, hfJ⟩ := hfJ
  have hconjInput : ∀ k : Fin 8, ∃ (w : ↥(ggAutomizer J Bs)) (i : ΛJ),
      eJ ((CoxeterMatrix.A 8).simple k) = w * fJ (MJ.simple i) * w⁻¹ := by
    intro k
    have htmem : (((eJ ((CoxeterMatrix.A 8).simple k) : ↥(ggAutomizer J Bs))) : MulAut ↥Bs)
        ∈ ggAutomizer J Bs := (eJ ((CoxeterMatrix.A 8).simple k)).2
    have htrefl : GGIsReflection p
        (((eJ ((CoxeterMatrix.A 8).simple k) : ↥(ggAutomizer J Bs))) : MulAut ↥Bs) := by
      have h1 := hrefl (Sum.inl k)
      rwa [hchain k] at h1
    obtain ⟨w, hw, i, hi⟩ := hconj _ htmem htrefl
    exact ⟨⟨w, hw⟩, i, by
      apply Subtype.ext
      simpa [hfJ i] using hi⟩
  obtain ⟨σ, -, -⟩ :=
    ggWeylSimpleSystemsConjInput_holds ΛJ (Fin 8) MJ (CoxeterMatrix.A 8)
      hMJ hM'A8 (↥(ggAutomizer J Bs)) fJ eJ hconjInput
  have hcardJ : Fintype.card ΛJ = 8 := by
    have h := Fintype.card_congr σ
    simpa using h
  have hindJ : LinearIndependent (ZMod p) h' := hind hcardJ
  have hAcl : Subgroup.closure (Set.range fun i : Fin 8 => eJ ((CoxeterMatrix.A 8).simple i))
      = ⊤ := by
    have h1 : Subgroup.closure (Set.range (CoxeterMatrix.A 8).simple) = ⊤ := by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        CoxeterSystem.subgroup_closure_range_simple (cs := (CoxeterMatrix.A 8).toCoxeterSystem)
    have hmap := MonoidHom.map_closure eJ.toMonoidHom
      (Set.range (CoxeterMatrix.A 8).simple)
    have hrange : eJ.toMonoidHom '' Set.range (CoxeterMatrix.A 8).simple
        = Set.range (fun i : Fin 8 => eJ ((CoxeterMatrix.A 8).simple i)) := by
      ext x; constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hrange, h1, Subgroup.map_top_of_surjective _ eJ.surjective] at hmap
    exact hmap.symm
  have hgenChain : ggAutomizer J Bs
      = Subgroup.closure (Set.range fun i : Fin 8 => φ (Sum.inl i)) := by
    let A : Subgroup (MulAut ↥Bs) := ggAutomizer J Bs
    have htop : (⊤ : Subgroup ↥A).map A.subtype = A := by
      ext x; constructor
      · rintro ⟨y, -, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    have himg : (A.subtype : ↥A → MulAut ↥Bs) ''
        Set.range (fun i : Fin 8 => eJ ((CoxeterMatrix.A 8).simple i))
        = Set.range (fun i : Fin 8 => φ (Sum.inl i)) := by
      have hcomp : (A.subtype : ↥A → MulAut ↥Bs) ∘
          (fun i : Fin 8 => eJ ((CoxeterMatrix.A 8).simple i))
          = fun i : Fin 8 => φ (Sum.inl i) := by
        funext i
        exact (hchain i).symm
      rw [← Set.range_comp, hcomp]
    have hmap := MonoidHom.map_closure A.subtype
      (Set.range (fun i : Fin 8 => eJ ((CoxeterMatrix.A 8).simple i)))
    rw [hAcl, himg] at hmap
    calc ggAutomizer J Bs = A := rfl
      _ = (⊤ : Subgroup ↥A).map A.subtype := htop.symm
      _ = Subgroup.closure (Set.range fun i : Fin 8 => φ (Sum.inl i)) := hmap
  have hindChain : LinearIndependent (ZMod p) (fun i : Fin 8 => h (Sum.inl i)) :=
    ggDatum_indep_transfer (Bs := Bs) (X := J) (Λ := ΛJ) (Λ' := Fin 8)
      (V := V') (V' := V) (ι := ι') (ι' := ι)
      (φ := φ') (φ' := fun i : Fin 8 => φ (Sum.inl i))
      (h := h') (α := α') (h' := fun i : Fin 8 => h (Sum.inl i))
      (α' := fun i : Fin 8 => α (Sum.inl i))
      hlin' hrefl' (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i))
      hAJgen hgenChain (by rw [hcardJ, Fintype.card_fin]) hindJ
  have hfin := finrank_span_eq_card hindChain
  have h78 : (7 : ℕ) = 8 := by
    rw [← hdim7, hfin]
    simp
  exact absurd h78 (by norm_num)

theorem ggMaxRank_notLevi {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X Y J : Subgroup G} (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (hX : GGMaxRankSideChain p Bs X J eJ) : ¬ GGResSideDatum p Bs Y J := by
  classical
  rintro ⟨Λ, instFL, instDL, b, M, C, MJ, V', instAC', instM', ι', φ', h', α',
    hM, hC, hMJ, hMJe, hlin', hrefl', hpair', hfY, hAY, hfJ, hAJgen, hconj⟩
  letI : Fintype Λ := instFL
  letI : DecidableEq Λ := instDL
  letI : AddCommGroup V' := instAC'
  letI : Module (ZMod p) V' := instM'
  exact ggMaxRank_levi_false (ΛJ := {j : Λ // j ≠ b}) (MJ := MJ) eJ hX hMJ ι'
    (fun j => φ' j) (fun j => h' j) (fun j => α' j)
    (fun i w => hlin' i w) (fun i => hrefl' i) hfJ hAJgen hconj
    (fun hcardJ => by
      have hcard9 : Fintype.card Λ = 9 := by
        have hLJcompl : Fintype.card {j : Λ // j ≠ b} = Fintype.card Λ - 1 :=
          Set.card_ne_eq b
        omega
      have hind9 : LinearIndependent (ZMod p) h' :=
        ggMaxRank_nine_indep hX.1 hcard9 hM hC h' α' hpair'
      simpa only [Function.comp_def] using
        hind9.comp (Subtype.val : {j : Λ // j ≠ b} → Λ) (fun _ _ hh => Subtype.ext hh))

end CFSG.StandardType

end
