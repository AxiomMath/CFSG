module

public import CFSG.LocalAnalysis.StandardType.GGTBJLinearSidesLE3
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem exists_diagonal_cover_of_large_linear_side_of_marking_with_card
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* X),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        p ^ (r - 1) ≤ Nat.card ↥(ggGamma X hN).range := by
  have hp : p.Prime := Fact.out
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  have heq : lab = ⟨.A, r, f⟩ := by
    obtain ⟨R, _, I, F, hs, hna, θ, heq, -⟩ := largeEvenRawDatum_exists hraw
    exact heq
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hF, hs, hna, θ, -, hN, hI⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hLift : GGTorusLift p (r - 1) (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) F)) := by
    have hrank : r - 1 = r + 1 - 2 := by omega
    rw [hrank]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (r + 1) F)
      (TypeA.ggTorusLift_sub_two hp (by simpa only [hF] using hpq) (by omega)
        (slHasSections_of_four_le hp (by simpa only [hF] using hpq) (by omega)))
  have hTB : GGTorusTBGroup p (r - 1)
      (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) F)) Set.univ)
      X (ggQuotHom θ) (ggGamma X hN).range := by
    rcases hside with rfl | ⟨z, hz⟩
    · exact ggTorusTBGroup_of_L hcfg hXperf θ hN
        (fun b hb => ggLAut_mem_of_induces X θ hN hI hb) hLift
    · exact ggTorusTBGroup_of_nbr hcfg hz hXperf θ hN
        (fun b hb => ggLAut_mem_of_induces X θ hN hI hb) hLift
  have hcard : p ^ (r - 1) ≤ Nat.card ↥(ggGamma X hN).range := hTB.2.2.2.2.2.1
  have hTB' := hTB.mulEquiv (TypeA.recipeEquiv (r + 1) F)
    (fun _ h => TypeA.congr_recipeEquiv_mem h)
  obtain ⟨φ, hφs, hker, hdiag⟩ := exists_actsDiag_model_of_tbGroup
    hp (by simpa only [hF] using hpq) (by omega) (by omega) hTB'
  exact ⟨F, hField, hFinite, inferInstance, hN, φ, hF, hφs, hker, hdiag, hcard⟩

theorem exists_block_of_large_linear_L_of_marking_with_card
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    {r f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        p ^ (r - 1) ≤ Nat.card ↥(ggGamma L hN).range ∧
        2 ≤ S.card ∧ J = (blockSpecialLinear S).map (L.subtype.comp φ) := by
  have hr : 3 ≤ r := hcfg.three_le_rank_of_typeA_marking hmark hpq
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag, hcard⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking_with_card hcfg (Or.inl rfl) hr hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hcfg.2.2.1.2.2.2.2.2.1
  have hDB : D ≤ Bs := hcfg.2.2.1.1.trans hcfg.2.1.1
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (L.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma L hN b) ⟨b, rfl⟩
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    hφs hker hdiag' hDB hJ
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hcard, hS, hJ⟩

theorem ggCorank_le_three_of_datum
    {G : Type} [Group G] [Finite G] {p r c : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} (hcr : c ≤ r)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ' : Fin r → MulAut Bs) (h' : Fin r → V) (α' : Fin r → Module.Dual (ZMod p) V)
    (hlin' : ∀ i v, ggLin (p := p) ι (φ' i) v = v - α' i v • h' i)
    (hJgen' : ggAutomizer J Bs = Subgroup.closure
      (Set.range (φ' ∘ Fin.castLE (by omega : r - c ≤ r))))
    (hBsCard : p ^ r ≤ Nat.card Bs)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    (hfix : ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) :
    c ≤ 3 := by
  classical
  have hp : p.Prime := Fact.out
  have hVfin : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  let Lα : V →ₗ[ZMod p] (Fin (r - c) → ZMod p) :=
    LinearMap.pi fun i => α' (Fin.castLE (by omega : r - c ≤ r) i)
  let W : Submodule (ZMod p) V := LinearMap.ker Lα
  have hVcard : Nat.card V = Nat.card W * Nat.card (V ⧸ W) :=
    Submodule.card_eq_card_quotient_mul_card W
  have hquot : Nat.card (V ⧸ W) ≤ p ^ (r - c) := by
    have h1 : Nat.card (V ⧸ W) = Nat.card ↥(LinearMap.range Lα) :=
      Nat.card_congr (LinearMap.quotKerEquivRange Lα).toEquiv
    have h2 : Nat.card ↥(LinearMap.range Lα) ≤ Nat.card (Fin (r - c) → ZMod p) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have h3 : Nat.card (Fin (r - c) → ZMod p) = p ^ (r - c) := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hWC : ∀ w : W, ((Additive.toMul (ι.symm (w : V)) : Bs) : G) ∈
      Bs ⊓ Subgroup.centralizer (J : Set G) := by
    intro w
    refine ⟨(Additive.toMul (ι.symm (w : V)) : Bs).2, hfix _ ?_⟩
    intro a ha
    rw [hJgen'] at ha
    refine Subgroup.closure_induction (p := fun a _ => a (Additive.toMul (ι.symm (w : V))) =
      Additive.toMul (ι.symm (w : V))) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨i, rfl⟩
      rw [ggLin_fix_iff (p := p) ι]
      have hw : Lα (w : V) = 0 := LinearMap.mem_ker.mp w.2
      have hα : α' (Fin.castLE (by omega : r - c ≤ r) i) (w : V) = 0 := by
        simpa [Lα] using congrFun hw i
      simp only [Function.comp_apply, ofMul_toMul, AddEquiv.apply_symm_apply]
      rw [hlin', hα, zero_smul, sub_zero]
    · rfl
    · intro a₁ a₂ _ _ h₁ h₂
      change a₁ (a₂ _) = _
      rw [h₂, h₁]
    · intro a _ h
      apply a.injective
      rw [MulAut.apply_inv_self]
      exact h.symm
  have hWle : Nat.card W ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun w => (⟨_, hWC w⟩ : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)))) ?_
    intro w w' hww
    have h0 : ((Additive.toMul (ι.symm (w : V)) : Bs) : G) =
        ((Additive.toMul (ι.symm (w' : V)) : Bs) : G) :=
      congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (z : G)) hww
    have h1 : (Additive.toMul (ι.symm (w : V)) : Bs) = Additive.toMul (ι.symm (w' : V)) :=
      Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  have hVBs : Nat.card Bs = Nat.card V := card_eq_of_ggLin ι
  have hmain : p ^ r ≤ p ^ 3 * p ^ (r - c) := by
    calc p ^ r ≤ Nat.card Bs := hBsCard
      _ = Nat.card V := hVBs
      _ = Nat.card W * Nat.card (V ⧸ W) := hVcard
      _ ≤ p ^ 3 * p ^ (r - c) := Nat.mul_le_mul (hWle.trans hCJ) hquot
  rw [← pow_add] at hmain
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hmain
  omega

theorem ggLinear_corank_le_three_of_block
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 3 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (hBsCard : p ^ r ≤ Nat.card Bs)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    (hfix : ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (S : Finset (Fin (r + 1))) (hS2 : 2 ≤ S.card)
    (hJ : J = (blockSpecialLinear S).map (X.subtype.comp ψ)) :
    r + 1 - S.card ≤ 3 := by
  classical
  have hSle : S.card ≤ r + 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  obtain ⟨c, hc⟩ : ∃ c, c = r + 1 - S.card := ⟨_, rfl⟩
  have hScard : S.card = r + 1 - c := by omega
  have hcr : c ≤ r := by omega
  have hrc : 1 ≤ r - c := by omega
  obtain ⟨V, hVadd, hVmod, ι, φ', h', α', hlin', -, -, -, -, hJgen'⟩ :=
    exists_adapted_weyl_datum_of_diagonal_linear_block_corank hp2 hpF hr hcr hrc hBs hSC hN hψ
      hker hdiag S hScard hJ
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have := ggCorank_le_three_of_datum hcr ι φ' h' α' hlin' hJgen' hBsCard hCJ hfix
  omega

theorem ggTBJLeft_splitA_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hcardA, hS2, hJ⟩ :=
    exists_block_of_large_linear_L_of_marking_with_card hH.1 hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hH.1.tableB_facts.2.2.2.1 hl) x rfl).symm
  have hBsCard : p ^ r ≤ Nat.card Bs := by
    have h1 := card_range_ggGamma_mul_prime_le hp hBs hN hxBs hx1 hxC
    calc p ^ r = p ^ (r - 1) * p := by rw [← pow_succ]; congr 1; omega
      _ ≤ Nat.card ↥(ggGamma L hN).range * p := Nat.mul_le_mul_right _ hcardA
      _ ≤ Nat.card Bs := h1
  have hfix := hH.fix_mem_centralizer_J_of_typeA_marking hpq hmark
  have hcor : r + 1 - S.card ≤ 3 :=
    ggLinear_corank_le_three_of_block hp2 hpF hr hBs hSC hN hφs hker hdiag hBsCard
      hH.1.card_bstar_inf_centralizer_J_le hfix S hS2 hJ
  have hSle : S.card ≤ r := by
    by_contra hSgt
    have hSr : S.card = r + 1 := by
      have := Finset.card_le_univ S
      simp only [Fintype.card_fin] at this
      omega
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hSr)
    have hJL : J = L := by
      rw [hJ, hSuniv]
      have htop : (blockSpecialLinear (K := F) (Finset.univ : Finset (Fin (r + 1))) :
          Subgroup (SpecialLinearGroup (Fin (r + 1)) F)) = ⊤ := by
        refine eq_top_iff.mpr fun g _ => ?_
        rw [mem_blockSpecialLinear]
        intro i j hij
        rcases hij with h | h <;> simp at h
      rw [htop, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
        MonoidHom.range_eq_top_of_surjective _ hφs, Subgroup.map_top, Subgroup.range_subtype]
    have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
    have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
    rw [hJL, inf_centralizer_eq_zpowers_of_sstar hp hH.1.1.2.2.2.2.2.2.1] at hD
    rw [hD, Nat.card_zpowers, orderOf_eq_prime (hH.1.2.1.2.1.2 x hxBs) hx1] at hDcard
    have : 1 < p := hp.one_lt
    nlinarith
  have hc1 : 1 ≤ r + 1 - S.card := by omega
  have hres := ggResSideDatumLE3_of_diagonal_linear_block (c := r + 1 - S.card) hp2 hpF hr hc1
    hcor (by omega) hBs hSC hN hφs hker hdiag S (by omega) hJ
  by_cases hc : r + 1 - S.card = 1
  · exact Or.inl (hres.1 hc)
  · exact Or.inr (hres.2 (by omega))

end CFSG.StandardType

end
