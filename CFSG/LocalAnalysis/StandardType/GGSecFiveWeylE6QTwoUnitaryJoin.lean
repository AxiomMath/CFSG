module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOvergroup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open Module
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem e6QTwoModelData {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A) (hA : ∀ ψ ∈ A, ψ ∈ ggInduced ⊤ Bs) {b : ↥Bs}
    (hb : b ≠ 1) {A₁ : Subgroup (MulAut ↥Bs)} (hA₁ : A₁ ≤ A) (hfix : ∀ ψ ∈ A₁, ψ b = b)
    (h720 : 720 ≤ Nat.card A₁) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : Finite V)
      (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
      (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
      (B : LinearMap.BilinForm (ZMod 3) V) (ι : Additive ↥Bs ≃+ V),
      Nat.card V = 3 ^ 5 ∧ (∀ i v, B (h i) v = α i v) ∧
        ι (Additive.ofMul b) ≠ 0 ∧ B (ι (Additive.ofMul b)) (ι (Additive.ofMul b)) = 2 ∧
        Nat.card (E6QTwo.e6Weyl hα) = 51840 ∧
        Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))) = 720 ∧
        A.map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα ∧
        A₁.map (ggLin (p := 3) ι) =
          (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))).map
            (E6QTwo.e6Weyl hα).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  letI := hVadd
  letI := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  haveI hVfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨e, h, α, hα, he, hP⟩ := E6QTwo.exists_cartan_pairing_E6 hNT hW hA ι
  obtain ⟨B, hB⟩ := E6QTwo.exists_bilinForm hP hVcard
  have hmapA : A.map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα :=
    E6QTwo.map_ggLin_eq_e6Weyl ι e hα he
  have hE6card : Nat.card (E6QTwo.e6Weyl hα) = 51840 := by
    rw [E6QTwo.card_e6Weyl_eq ι e hα he]
    rw [show Nat.card A = Nat.card (CoxeterMatrix.E₆).Group from
      (Nat.card_congr e.toEquiv).symm, hWcard]
  have hbv : ι (Additive.ofMul b) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul b = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : b = 1 := by simpa using congrArg Additive.toMul h1
    exact hb h2
  have hmapA₁ : A₁.map (ggLin (p := 3) ι) ≤
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))).map
        (E6QTwo.e6Weyl hα).subtype := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have hmem : ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα := by
      rw [← hmapA]
      exact Subgroup.mem_map_of_mem _ (hA₁ hψ)
    have hstab : (⟨ggLin (p := 3) ι ψ, hmem⟩ : ↥(E6QTwo.e6Weyl hα)) ∈
        MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b)) := by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]
      exact (ggLin_fix_iff ι ψ b).mp (hfix ψ hψ)
    exact Subgroup.mem_map_of_mem (E6QTwo.e6Weyl hα).subtype hstab
  have hcardle : Nat.card A₁ ≤
      Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))) := by
    have h' := Subgroup.card_le_of_le hmapA₁
    rwa [Subgroup.card_map_of_injective (E6QTwo.e6Weyl hα).subtype_injective,
      Subgroup.card_map_of_injective (ggLin_injective ι)] at h'
  have hge : 720 ≤
      Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))) :=
    le_trans h720 hcardle
  have hcases := E6QTwo.stabilizer_cases hP hVcard hB hα hE6card hbv
  have hstabc : Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))) =
      720 := by
    rcases hcases with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact h1
    · omega
    · omega
  have hBvv : B (ι (Additive.ofMul b)) (ι (Additive.ofMul b)) = 2 := by
    rcases hcases with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact h1
    · omega
    · omega
  have hmapA₁eq : A₁.map (ggLin (p := 3) ι) =
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b))).map
        (E6QTwo.e6Weyl hα).subtype := by
    refine Subgroup.eq_of_le_of_card_ge hmapA₁ ?_
    rw [Subgroup.card_map_of_injective (E6QTwo.e6Weyl hα).subtype_injective,
      Subgroup.card_map_of_injective (ggLin_injective ι), hstabc]
    exact h720
  exact ⟨V, hVadd, hVmod, hVfin, h, α, hα, hP, B, ι, hVcard, hB, hbv, hBvv, hE6card,
    hstabc, hmapA, hmapA₁eq⟩

theorem E6QTwo.eq_or_forall_apply_eq_of_le {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A) (hA : ∀ ψ ∈ A, ψ ∈ ggInduced ⊤ Bs) {b : ↥Bs}
    (hb : b ≠ 1) {A₁ : Subgroup (MulAut ↥Bs)} (hA₁ : A₁ ≤ A) (hfix : ∀ ψ ∈ A₁, ψ b = b)
    (h720 : 720 ≤ Nat.card A₁) {H : Subgroup (MulAut ↥Bs)} (hA₁H : A₁ ≤ H) (hHA : H ≤ A) :
    H = A ∨ ∀ ψ ∈ H, ψ b = b ∨ ψ b = b⁻¹ := by
  classical
  obtain ⟨V, hVadd, hVmod, hVfin, h, α, hα, hP, B, ι, hVcard, hB, hbv, hBvv, hE6card,
    hstabc, hmapA, hmapA₁⟩ := e6QTwoModelData hBs hNT hcard hWcard hW hA hb hA₁ hfix h720
  letI := hVadd
  letI := hVmod
  letI := hVfin
  have hHle : H.map (ggLin (p := 3) ι) ≤ E6QTwo.e6Weyl hα := by
    rw [← hmapA]
    exact Subgroup.map_mono hHA
  have hS : ∀ g ∈ E6QTwo.e6Weyl hα, g (ι (Additive.ofMul b)) = ι (Additive.ofMul b) →
      g ∈ H.map (ggLin (p := 3) ι) := by
    intro g hg hgv
    have hgA : g ∈ A.map (ggLin (p := 3) ι) := by
      rw [hmapA]
      exact hg
    obtain ⟨ψ, hψA, hψg⟩ := Subgroup.mem_map.mp hgA
    have hψfix : ψ b = b := by
      rw [ggLin_fix_iff (p := 3) ι ψ b]
      rw [hψg]
      exact hgv
    have hψA₁ : ψ ∈ A₁ := by
      have hψe6 : ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα := by
        rw [← hmapA]
        exact Subgroup.mem_map_of_mem _ hψA
      have hstab : (⟨ggLin (p := 3) ι ψ, hψe6⟩ : ↥(E6QTwo.e6Weyl hα)) ∈
          MulAction.stabilizer (E6QTwo.e6Weyl hα) (ι (Additive.ofMul b)) := by
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]
        change ggLin (p := 3) ι ψ (ι (Additive.ofMul b)) = ι (Additive.ofMul b)
        rw [← ggLin_fix_iff (p := 3) ι ψ b]
        exact hψfix
      have hmem : ggLin (p := 3) ι ψ ∈ A₁.map (ggLin (p := 3) ι) := by
        rw [hmapA₁]
        exact Subgroup.mem_map.mpr ⟨⟨ggLin (p := 3) ι ψ, hψe6⟩, hstab, rfl⟩
      obtain ⟨ψ', hψ', hψ'g⟩ := Subgroup.mem_map.mp hmem
      rwa [show ψ' = ψ from ggLin_injective (p := 3) ι hψ'g] at hψ'
    exact ⟨ψ, hA₁H hψA₁, hψg⟩
  rcases E6QTwo.eq_e6Weyl_or_forall_apply_eq_of_stabilizer_le hP hVcard hB hα hE6card hBvv
    hHle hS with hHeq | hHfix
  · left
    exact Subgroup.map_injective (ggLin_injective ι) (hHeq.trans hmapA.symm)
  · right
    intro ψ hψ
    have hψ' : ggLin (p := 3) ι ψ ∈ H.map (ggLin (p := 3) ι) :=
      Subgroup.mem_map_of_mem _ hψ
    have h := hHfix _ hψ'
    rw [ggLin_fix_iff (p := 3) ι ψ b, ggLin_inv_iff (p := 3) ι ψ b]
    exact h

theorem E6QTwo.exists_mem_apply_ne_of_le {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A) (hA : ∀ ψ ∈ A, ψ ∈ ggInduced ⊤ Bs) {b : ↥Bs}
    (hb : b ≠ 1) {A₁ : Subgroup (MulAut ↥Bs)} (hA₁ : A₁ ≤ A) (hfix : ∀ ψ ∈ A₁, ψ b = b)
    (h720 : 720 ≤ Nat.card A₁) :
    ∃ ψ ∈ A, ψ b ≠ b ∧ ψ b ≠ b⁻¹ := by
  classical
  obtain ⟨V, hVadd, hVmod, hVfin, h, α, hα, hP, B, ι, hVcard, hB, hbv, hBvv, hE6card,
    hstabc, hmapA, hmapA₁⟩ := e6QTwoModelData hBs hNT hcard hWcard hW hA hb hA₁ hfix h720
  letI := hVadd
  letI := hVmod
  letI := hVfin
  obtain ⟨g, hg, hgv, hgv'⟩ := E6QTwo.exists_mem_e6Weyl_apply_ne hP hVcard hB hα hBvv
  have hgA : g ∈ A.map (ggLin (p := 3) ι) := by
    rw [hmapA]
    exact hg
  obtain ⟨ψ, hψA, hψg⟩ := Subgroup.mem_map.mp hgA
  refine ⟨ψ, hψA, ?_, ?_⟩
  · intro h
    exact hgv (by rw [← hψg, ← ggLin_fix_iff (p := 3) ι ψ b]; exact h)
  · intro h
    exact hgv' (by rw [← hψg, ← ggLin_inv_iff (p := 3) ι ψ b]; exact h)

theorem GGSecFiveRouteCfg.exists_sup_eq_of_twA5
    (hRig : GGLabelRigidInput) (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hNS : ¬ GGSplitLie 3 L) {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : ∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e')
    (hr : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)) :
    ∃ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  classical
  have hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J :=
    ⟨𝒦, hR, hNS, ι, M, e, hP, hM, hr⟩
  obtain ⟨hRest, hG, hS, hBs, hxB, hx1, horderx, hLx, hstar, hcyc, hNT⟩ :=
    e6QTwo_config_facts hC
  have hIDall : GGInnerDiagAll 3 B Bs x L D J := hRest.2.2.1
  have hSclosed : ∀ lab lab' : LargeEvenLabel, GGLabelIso lab lab' →
      (lab'.tag = .twA ∧ lab'.rank = 5 ∧ lab'.n = 1) →
      (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) := by
    intro lab lab' hiso h'
    have heq : lab = lab' :=
      E6QTwo.eq_of_ggLabelIso_end hiso ⟨Or.inl ⟨h'.1, h'.2.1⟩, h'.2.2⟩
    rw [heq]
    exact h'
  have hlab' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs L :=
    E6QTwo.innerDiagOnLabel_of_marking hRig hSclosed hIDall.1 hlab
  have hcard : Nat.card Bs = 3 ^ 5 :=
    GGSecFiveE6QTwoCfg.card_bstar_eq_of_twA5 hT hC hlab'
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab'
  letI := hfieldK
  letI := hfiniteK
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  let K' : Subgroup G := ggConjPreimage Bs (ggAutomizerJoin L Bs 𝒦)
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K' Bs = ggAutomizerJoin L Bs 𝒦 :=
    sup_ggAutomizer_ggConjPreimage L Bs 𝒦
  have hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) := by
    obtain ⟨e', rfl⟩ := hM
    exact GGWeylOfType.of_reindex (M := CoxeterMatrix.E₆) (e := e') ⟨e, hP.2⟩
  have hW' : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) := by
    rw [hsup]
    exact hW
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center hK4 θ hperf hBs hNT hcard hxB hx1 hLx hBL hstar hBsN hI hW'
  obtain ⟨-, θ', hmap⟩ :=
    E6QTwo.card_inf_eq_and_exists_map_eq_torU_of_isPGroup hK4 θ hperf hZ2 hBs hcard hxB
      hx1 hBL hstar hBsN hI
  have hxL : x ∉ L := not_mem_of_isPGroup_two_center hZ2 horderx hLx
  have h720 : 720 ≤ Nat.card (ggAutomizer L Bs) :=
    E6QTwo.le_card_ggAutomizer_of_isPGroup hK4 θ' hZ2 hmap hBs hcard hxB hxL hLx
  have hAind : ∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ ∈ ggInduced ⊤ Bs := by
    intro ψ hψ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top)
        (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hψ)
  let b : ↥Bs := ⟨x, hxB⟩
  have hb : b ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext_iff.mp h)
  have hfixAL : ∀ ψ ∈ ggAutomizer L Bs, ψ b = b := fun ψ hψ =>
    ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  have hALle : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rw [ggAutomizerJoin]
    exact le_sup_left
  by_contra hcon
  have hne : ∀ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs 𝒦 := by
    intro K hK heq
    exact hcon ⟨K, hK, heq⟩
  let P : Subgroup (MulAut ↥Bs) :=
    { carrier := {ψ | ψ b = b ∨ ψ b = b⁻¹}
      one_mem' := by
        left
        simp
      mul_mem' := by
        rintro φ ψ (hφ | hφ) (hψ | hψ)
        · exact Or.inl (by rw [MulAut.mul_apply, hψ, hφ])
        · exact Or.inr (by rw [MulAut.mul_apply, hψ, map_inv, hφ])
        · exact Or.inr (by rw [MulAut.mul_apply, hψ, hφ])
        · exact Or.inl (by rw [MulAut.mul_apply, hψ, map_inv, hφ, inv_inv])
      inv_mem' := by
        intro φ hφ
        rcases hφ with hφ | hφ
        · exact Or.inl (φ.injective (by rw [MulAut.apply_inv_self, hφ]))
        · exact Or.inr (φ.injective (by rw [MulAut.apply_inv_self, map_inv, hφ, inv_inv])) }
  have hALP : ggAutomizer L Bs ≤ P := fun ψ hψ => Or.inl (hfixAL ψ hψ)
  have hKP : ∀ K ∈ 𝒦, ggAutomizer K Bs ≤ P := by
    intro K hK
    have hHle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
      rw [ggAutomizerJoin]
      have hKle : ggAutomizer K Bs ≤ ⨆ K' ∈ 𝒦, ggAutomizer K' Bs :=
        le_iSup₂_of_le K hK le_rfl
      exact sup_le le_sup_left (le_sup_of_le_right hKle)
    have hres := E6QTwo.eq_or_forall_apply_eq_of_le hBs hNT hcard card_coxeterE6_group hW
      hAind hb hALle hfixAL h720 le_sup_left hHle
    rcases hres with hEq | hFor
    · exact absurd hEq (hne K hK)
    · intro ψ hψ
      exact hFor ψ (Subgroup.mem_sup_right hψ)
  have hAjoin : ggAutomizerJoin L Bs 𝒦 ≤ P := by
    rw [ggAutomizerJoin]
    exact sup_le hALP (iSup₂_le hKP)
  obtain ⟨ψ, hψA, hψb, hψb'⟩ :=
    E6QTwo.exists_mem_apply_ne_of_le hBs hNT hcard card_coxeterE6_group hW hAind hb hALle
      hfixAL h720
  have hmem : ψ b = b ∨ ψ b = b⁻¹ := hAjoin hψA
  exact hmem.elim hψb hψb'

end CFSG.StandardType

end
