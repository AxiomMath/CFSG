module

public import CFSG.LocalAnalysis.StandardType.GGResKHighDegree
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeNine
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUClassLarge
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Monster.B.Geometry
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepA9_weyl_of_not_mem (hKS : GGReflClassOmegaSmall) (hOrbK : GGResCentBoundNbrInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (9 - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection 3 (φ i))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame 3 9 (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)))
    (hcardBs : Nat.card ↥Bs = 3 ^ (9 - 1))
    (hLrefl : GGReflGenerated 3 (ggAutomizer L Bs))
    {t : MulAut ↥Bs} (htL : t ∈ ggAutomizer L Bs) {ha : V} {αa : Module.Dual (ZMod 3) V}
    (hform : ∀ w, ggLin (p := 3) ι t w = w - αa w • ha) (hαa : αa ha = 2)
    (hw : αa (ι (Additive.ofMul ⟨y, hy⟩)) ≠ 0) (hjoin : ∃ c : Fin (9 - 1), αa (h (e c)) ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (9 - 1) =>
        ggLin (p := 3) ι (φ (e i))) ∪ {ggLin (p := 3) ι t}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hnH : ha ∉ Submodule.span (ZMod 3) (Set.range fun i => h (e i))) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 3) V = 8 := ggFinrank_eq_of_card_Bs ι hcardBs
  let r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hirrA := ggDepA_absIrred_of_not_mem (p := 3) (N := 9) (by norm_num) (by norm_num) F r hr
    (ggLin (p := 3) ι t) ha αa hform hαa hjoin hw hnt hdim hnH
  have hφsup : ∀ i, φ i ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun i =>
    Subgroup.mem_sup_right (by rw [hAK]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have htsup : t ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_left htL
  have hRA : Subgroup.closure (Set.range r ∪ {ggLin (p := 3) ι t}) ≤
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) := by
    rw [Subgroup.closure_le]
    rintro z (⟨i, rfl⟩ | hz)
    · exact Subgroup.mem_map.mpr ⟨φ (e i), hφsup (e i), rfl⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subgroup.mem_map.mpr ⟨t, htsup, rfl⟩
  have hirr := ggIndep_absIrred_mono hRA hirrA
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup hLrefl (ggIndep_reflGenerated_of_closure hrefl hAK)
  have hjoinc := ggIndep_card_join_le (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⟨y, hy⟩
    (hOrbK G 3 B Bs x L D J y K hH hy)
  have hAKc : Nat.card ↥(ggAutomizer K Bs) ≤ Nat.factorial 9 :=
    ggDepA_card_automizer_K (p := 3) (N := 9) (by norm_num) (by norm_num) hy ι hφ hAK e F
  have hsmall : 8 * Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) < 3 ^ (8 * (8 - 1) / 2) := by
    calc 8 * Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        ≤ 8 * (Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs))) :=
          Nat.mul_le_mul_left 8 hjoinc
      _ ≤ 8 * (3 ^ (9 - 1) * ((3 - 1) * 6 * Nat.factorial 9)) := by
          rw [hcardBs]
          exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAKc))
      _ < 3 ^ (8 * (8 - 1) / 2) := by norm_num [Nat.factorial]
  have hcardR : Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)) =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := 3) ι)
      (ggLin_injective ι)).toEquiv).symm
  exact ggRC_weylReflGroup_of_linWeyl ι _
    (HdRo7SU.su_linWeyl_of_card_lt_small hKS (d := 8) (by norm_num) le_rfl hdim _ hirr
      (ggIndep_map_reflGen ι _ hgen') (by rw [hcardR]; exact hsmall))

theorem ggExactThreeAtK_weyl_of_dep_nine
    (hKS : GGReflClassOmegaSmall) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (9 - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (9 - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card ↥Bs = p ^ (9 - 1))
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hAJ : Nat.card ↥(ggAutomizer J Bs) = (8 - 2).factorial) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hdep := ggXDatumA_dep_K_of_exactThree_card_three hFix rfl hH hy (by norm_num)
    (by norm_num) e hMK hCK hφ hpair hAK hcardBs h3
  have hfixK := ggXDatumA_fix_K_of_card hp2 hH hy (by norm_num) (by norm_num) hcardBs e hMK hCK
    hφ hpair hAK
  let F : GGDepAFrame 3 9 (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨y, hy⟩)) :=
    ggXDatumA_frame_K hp2 hH hy hfixK (by norm_num) (by norm_num) e hMK hCK hφ hpair hAK hdep
  have hJK : ggAutomizer J Bs ≤ ggAutomizer K Bs := by
    obtain ⟨Λ', i1, i2, S, Λa, i3, i4, ML, CL, MK', CK', V', i5, i6, ι', φ', h', α',
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin', hrefl', hpairL, hpairK, hsel,
      hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
    rw [hclosJ, hclosL]
    refine Subgroup.closure_mono ?_
    rintro z ⟨j, rfl⟩
    exact ⟨j.1, rfl⟩
  have hLside : GGResSideDatum 3 Bs L J ∨ GGResLeviSideDatumLE3 3 Bs L J :=
    ggSideDatum_of_exact3 hp2 h3 hAJ (by norm_num)
  obtain ⟨t, ha, αa, htL, htlin, hαaha, hαay, hjoin, hnt, -⟩ :=
    hLside.elim
      (fun hL => ggTwoNodeL_lside hFix hOrbK hp2 hH hy (by norm_num) e hφ hAK hJK F hL)
      (fun hL => ggTwoNodeL_lside_LE3 hFix hOrbK hp2 hH hy (by norm_num) e hφ hAK hJK F hL)
  by_cases hHa : ha ∈ Submodule.span (ZMod 3) (Set.range (fun i : Fin (9 - 1) => h (e i)))
  · exact (ggDepA9_caseII_false F (fun i => ggLin (p := 3) ι (φ (e i))) (fun i v => hφ (e i) v)
      (ggLin (p := 3) ι t) ha αa htlin hαaha hαay hnt hHa).elim
  · exact ggDepA9_weyl_of_not_mem hKS hOrbK hH hy e hφ hrefl hAK F hcardBs
      (ggResLeviDatumExact3_reflGenerated_L h3) htL htlin hαaha hαay hjoin hnt hHa

theorem GGResHyp.unitary_rankEight_exactThree_K_datum
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 8 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p = 3 ∧ GGResXDatumA p Bs K (9 - 1) ∧ Nat.card ↥Bs = p ^ (9 - 1) ∧
      Nat.card ↥(ggAutomizer J Bs) = (8 - 2).factorial := by
  classical
  obtain ⟨-, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨⟨htag, hrank, hpq⟩, -, -⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change rank = 8 at hrank
  change p ∣ 2 ^ n + 1 at hpq
  subst htag
  subst hrank
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let _ : Field F := hField
  let _ : Finite F := hFinite
  obtain ⟨-, -, θ, -, hNK, hact⟩ := hQ
  have h63 : ¬ (8 + 1 = 6 ∧ p = 3) := by omega
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data hFK hΛ.1 (by omega) hpq h63 θ hNK hact
  obtain ⟨r, hdr, hpd, hXA, hcardBs, -, -, hcardJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by omega) hdiag h3
  have hr : r = 8 := by omega
  subst hr
  have hp : p.Prime := Fact.out
  have hp3 : p = 3 := by
    have h9 : p ∣ 3 ^ 2 := by simpa using hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h9)
  exact ⟨hp3, hXA, hcardBs, hcardJ⟩

theorem GGResHyp.weyl_of_unitary_rankEight_exactThree_K
    (hKS : GGReflClassOmegaSmall) (hFix : GGTBFixInput) (hOrbK : GGResCentBoundNbrInput)
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 8 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  obtain ⟨hp3, hXA, hcardBs, hAJ⟩ := hH.unitary_rankEight_exactThree_K_datum hLB hU h3
  obtain ⟨Λ, _, _, MK, CK, V, _, _, ι, φ, h, α, e, hMK, -, hCK, hφ, hrefl, hpair, -, hAK⟩ :=
    hXA
  exact ggExactThreeAtK_weyl_of_dep_nine hKS hOrbK hFix hp3 hH hy e hMK hCK hφ hrefl hpair hAK
    hcardBs h3 hAJ

section OriginalLeaf


theorem ggResLeaf_unitary_rankEight_exactThree_K :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = 8 ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hU, h3, -⟩ := hP
  exact hH.weyl_of_unitary_rankEight_exactThree_K
    (ZS.ggReflClassOmegaSmall_of_useInput ZS.useInput_holds) ggTBFixInput_holds
    ggResCentBoundNbrInput_holds ggGammaSuppliers_proved.1
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) hU) h3

end OriginalLeaf

end CFSG.StandardType

end
