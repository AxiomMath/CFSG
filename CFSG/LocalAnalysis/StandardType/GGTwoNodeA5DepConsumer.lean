module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepExclusion
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAL
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeA5DepL_of_moving_K (hA5 : LR6A5DepAll) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hcard : Nat.card ↥Bs = 3 ^ 6)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} (e : Fin 5 ≃ Λ)
    (hML : ML = (CoxeterMatrix.A 5).reindex e) (hCL : GGIntCartan ML CL)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (f : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hf : ∀ i, (f (ML.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h)
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK] {MK : CoxeterMatrix ΛK}
    {φK : ΛK → MulAut ↥Bs} (hWMK : GGIsWeylMatrix MK)
    (hreflK : ∀ i, GGIsReflection p (φK i)) (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    (hfK : ∀ i, (fK (MK.simple i) : MulAut ↥Bs) = φK i)
    (hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hNontrivK : 1 < Fintype.card ΛK) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  haveI : Nontrivial ΛK := Fintype.one_lt_card_iff_nontrivial.mp hNontrivK
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let xv : V := ι (Additive.ofMul ⟨x, hx⟩)
  have Fdep : GGDepAFrame 3 6 (fun i : Fin 5 => h (e i)) (fun i => α (e i)) xv :=
    ggXDatumA_frame hFix hp2 hH hx (N := 6) (by norm_num) (by norm_num) e hML hCL hlin hpair hclos hdep
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hV6 : Module.finrank (ZMod 3) V = 6 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := by rw [← hcardV, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hgenK : GGReflGenerated 3 (ggAutomizer K Bs) := hH.2.2.2.2.2.1
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup (ggIndep_reflGenerated_of_closure hrefl hclos) hgenK
  obtain ⟨AA, hAA⟩ : ∃ AA : Subgroup (MulAut ↥Bs), AA = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hAA] at hgen' hA ⊢
  let r : Fin 5 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 5) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hlin (e i) v
  have hφAA : ∀ i, φ i ∈ AA := fun i =>
    hAA ▸ Subgroup.mem_sup_left (by rw [hclos]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hrR : ∀ i : Fin 5, r i ∈ AA.map (ggLin (p := 3) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφAA (e i), rfl⟩
  have hgenR : AA.map (ggLin (p := 3) ι) =
      Subgroup.closure {s | s ∈ AA.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
    apply le_antisymm
    · calc AA.map (ggLin (p := 3) ι)
          = (Subgroup.closure {ψ | ψ ∈ AA ∧ GGIsReflection 3 ψ}).map (ggLin (p := 3) ι) := by
            rw [← hgen']
        _ = Subgroup.closure ((ggLin (p := 3) ι) '' {ψ | ψ ∈ AA ∧ GGIsReflection 3 ψ}) :=
            MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure {s | s ∈ AA.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
            apply Subgroup.closure_mono
            rintro _ ⟨ψ, ⟨hψA, hψr⟩, rfl⟩
            exact ⟨Subgroup.mem_map.mpr ⟨ψ, hψA, rfl⟩,
              (ggRC_isReflection_iff_linRefl (p := 3) ι ψ).mp hψr⟩
    · rw [Subgroup.closure_le]
      intro w hw
      exact hw.1
  have hnt : ∀ g ∈ AA.map (ggLin (p := 3) ι),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hcardA1 : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial 6 := by
    have h1 : Nat.card ↥(ggAutomizer L Bs) = Nat.card ML.Group :=
      (Nat.card_congr f.toEquiv).symm
    have h2 : Nat.card ML.Group = Nat.card (CoxeterMatrix.A 5).Group := by
      rw [hML]
      exact Nat.card_congr ((CoxeterMatrix.A 5).reindexGroupEquiv e).toEquiv
    have h3 : Nat.card (CoxeterMatrix.A 5).Group = Nat.factorial 6 := by
      rw [l05nK3a_card_coxeterA 5]
    rw [h1, h2, h3]
  have hstabAA := hOrb G 3 B Bs x L D J y K hH hx
  rw [← hAA] at hstabAA
  have hmapStab : (AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map
      (ggLin (p := 3) ι) =
      AA.map (ggLin (p := 3) ι) ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨ψ, ⟨hψA, hψs⟩, rfl⟩
      exact ⟨⟨ψ, hψA, rfl⟩, (ggLin_fix_iff (p := 3) ι ψ ⟨x, hx⟩).mp hψs⟩
    · rintro ⟨⟨ψ, hψA, rfl⟩, hs⟩
      exact ⟨ψ, ⟨hψA, (ggLin_fix_iff (p := 3) ι ψ ⟨x, hx⟩).mpr hs⟩, rfl⟩
  have hstabR : Nat.card ↥(AA.map (ggLin (p := 3) ι) ⊓
      MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv) ≤ (3 - 1) * 6 * Nat.factorial 6 := by
    rw [← hmapStab]
    calc Nat.card ↥((AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map
          (ggLin (p := 3) ι))
        = Nat.card ↥(AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hstabAA
      _ ≤ (3 - 1) * 6 * Nat.factorial 6 := Nat.mul_le_mul_left _ hcardA1
  obtain ⟨t', ht'K, ht'refl, ht'move⟩ := hmoveK
  have hKA : ggAutomizer K Bs ≤ AA := hAA ▸ le_sup_right
  have hBs : Nat.card ↥Bs ≤ 3 ^ 6 := hcard.le
  have hcardR : Nat.card ↥(AA.map (ggLin (p := 3) ι)) ≤
      3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by
    calc Nat.card ↥(AA.map (ggLin (p := 3) ι)) = Nat.card ↥AA :=
          (Nat.card_congr (Subgroup.equivMapOfInjective AA (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
          ggIndep_card_join_le AA ⟨x, hx⟩ hstabAA
      _ ≤ 3 ^ 6 * ((3 - 1) * 6 * Nat.factorial 6) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = 3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by rw [Nat.mul_comm (3 - 1) 6]
  have hres := hA5 3 rfl V hV6 (fun i => h (e i)) (fun i => α (e i)) xv r Fdep hr
    (AA.map (ggLin (p := 3) ι)) hrR hgenR hnt hcardR hstabR
  rcases hres with hlinW | hline
  · exact ggRC_weylReflGroup_of_linWeyl ι AA hlinW
  · exfalso
    exact ggWeyl_rootLine_false hp2 ι hKA hWMK hreflK fK hfK hclosK
      ⟨t', ht'K, ht'move⟩ hnt hline


theorem ggTwoNodeA5DepL_core (hA5 : LR6A5DepAll) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hcard : Nat.card ↥Bs = 3 ^ 6)
    (hXd : GGResXDatumA p Bs L 5) (hxL : x ∉ L) (hKs : GGResLeviSideDatumLE3 p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨Λ, i1, i2, ML, CL, V, i3, i4, ι, φ, h, α, e, hML, hWML, hCL, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos⟩ := hXd
  letI := i1; letI := i2; letI := i3; letI := i4
  have hdep : ¬ LinearIndependent (ZMod p) h :=
    ggXDatumA_dep hFix (by omega) hH hx hxL (N := 6) (by norm_num)
      (by rw [hp3]; norm_num) e hML hCL hlin hpair hclos
  obtain ⟨Λ', j1, j2, S', M', C', MJ', V', j3, j4, ι', φ', h', α', hS2', hS3', hW',
    hC', hWJ', hMJ', hlin', hrefl', hpair', ⟨f', hf'⟩, hcl', hfJ', hclJ', hconj'⟩ := hKs
  letI := j1; letI := j2
  have hNontriv : 1 < Fintype.card Λ' := by
    have hs : 2 ≤ Fintype.card Λ' := le_trans hS2' (Finset.card_le_univ S')
    omega
  exact ggTwoNodeA5DepL_of_moving_K hA5 hOrb hFix hp3 hH hx hcard
    (ggIndep_moving_K hFixK hH hx) e hML hCL hlin hrefl hpair f hf hclos hdep
    hW' hrefl' f' hf' hcl' hNontriv

theorem ggTwoNodeA5DepK_core (hA5 : LR6A5DepAll) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hcard : Nat.card ↥Bs = 3 ^ 6)
    (hXd : GGResXDatumA p Bs K 5) (hyK : y ∉ K)
    (hfixK : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hLs : GGResLeviSideDatumLE3 p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨Λ, i1, i2, MK, CK, V, i3, i4, ι, φ, h, α, e, hMK, hWMK, hCK, hlin, hrefl, hpair, ⟨f, hf⟩,
    hclos⟩ := hXd
  letI := i1; letI := i2; letI := i3; letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hN5 : 5 ≤ 6 := by norm_num
  have hpN : 3 ∣ 6 := by norm_num
  let yv : V := ι (Additive.ofMul ⟨y, hy⟩)
  have hdep : ¬ LinearIndependent (ZMod 3) h :=
    ggXDatumA_dep_K hp2 hH hy hyK hfixK (N := 6) (by norm_num) (by norm_num) e hMK hCK hlin hpair
      hclos
  have Fdep : GGDepAFrame 3 6 (fun i : Fin 5 => h (e i)) (fun i => α (e i)) yv :=
    ggXDatumA_frame_K hp2 hH hy hfixK (N := 6) (by norm_num) (by norm_num) e hMK hCK hlin hpair
      hclos hdep
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hV6 : Module.finrank (ZMod 3) V = 6 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := by rw [← hcardV, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hLrefl : GGReflGenerated 3 (ggAutomizer L Bs) := by
    obtain ⟨Λ', j1, j2, S', M', C', MJ', V', j3, j4, ι', φ', h', α', hS2', hS3', hW', hC', hWJ',
      hMJ', hlin', hrefl', hpair', ⟨f', hf'⟩, hcl', hfJ', hclJ', hconj'⟩ := hLs
    exact ggIndep_reflGenerated_of_closure hrefl' hcl'
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup hLrefl (ggIndep_reflGenerated_of_closure hrefl hclos)
  obtain ⟨AA, hAA⟩ : ∃ AA : Subgroup (MulAut ↥Bs), AA = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hAA] at hgen' hA ⊢
  let r : Fin 5 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 5) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hlin (e i) v
  have hφAA : ∀ i, φ i ∈ AA := fun i =>
    hAA ▸ Subgroup.mem_sup_right (by rw [hclos]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hrR : ∀ i : Fin 5, r i ∈ AA.map (ggLin (p := 3) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφAA (e i), rfl⟩
  have hgenR : AA.map (ggLin (p := 3) ι) =
      Subgroup.closure {s | s ∈ AA.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
    apply le_antisymm
    · calc AA.map (ggLin (p := 3) ι)
          = (Subgroup.closure {ψ | ψ ∈ AA ∧ GGIsReflection 3 ψ}).map (ggLin (p := 3) ι) := by
            rw [← hgen']
        _ = Subgroup.closure ((ggLin (p := 3) ι) '' {ψ | ψ ∈ AA ∧ GGIsReflection 3 ψ}) :=
            MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure {s | s ∈ AA.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
            apply Subgroup.closure_mono
            rintro _ ⟨ψ, ⟨hψA, hψr⟩, rfl⟩
            exact ⟨Subgroup.mem_map.mpr ⟨ψ, hψA, rfl⟩,
              (ggRC_isReflection_iff_linRefl (p := 3) ι ψ).mp hψr⟩
    · rw [Subgroup.closure_le]
      intro w hw
      exact hw.1
  have hnt : ∀ g ∈ AA.map (ggLin (p := 3) ι),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hcardA1 : Nat.card ↥(ggAutomizer K Bs) ≤ Nat.factorial 6 := by
    have h1 : Nat.card ↥(ggAutomizer K Bs) = Nat.card MK.Group :=
      (Nat.card_congr f.toEquiv).symm
    have h2 : Nat.card MK.Group = Nat.card (CoxeterMatrix.A 5).Group := by
      rw [hMK]
      exact Nat.card_congr ((CoxeterMatrix.A 5).reindexGroupEquiv e).toEquiv
    have h3 : Nat.card (CoxeterMatrix.A 5).Group = Nat.factorial 6 := by
      rw [l05nK3a_card_coxeterA 5]
    rw [h1, h2, h3]
  have hstabAA := hOrbK G 3 B Bs x L D J y K hH hy
  rw [← hAA] at hstabAA
  have hmapStab : (AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)).map
      (ggLin (p := 3) ι) =
      AA.map (ggLin (p := 3) ι) ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨ψ, ⟨hψA, hψs⟩, rfl⟩
      exact ⟨⟨ψ, hψA, rfl⟩, (ggLin_fix_iff (p := 3) ι ψ ⟨y, hy⟩).mp hψs⟩
    · rintro ⟨⟨ψ, hψA, rfl⟩, hs⟩
      exact ⟨ψ, ⟨hψA, (ggLin_fix_iff (p := 3) ι ψ ⟨y, hy⟩).mpr hs⟩, rfl⟩
  have hstabR : Nat.card ↥(AA.map (ggLin (p := 3) ι) ⊓
      MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv) ≤ (3 - 1) * 6 * Nat.factorial 6 := by
    rw [← hmapStab]
    calc Nat.card ↥((AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)).map
          (ggLin (p := 3) ι))
        = Nat.card ↥(AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := hstabAA
      _ ≤ (3 - 1) * 6 * Nat.factorial 6 := Nat.mul_le_mul_left _ hcardA1
  obtain ⟨t', ht'L, ht'refl, ht'move⟩ := ggIndep_moving_L hFix hH hy hLrefl
  have hLA : ggAutomizer L Bs ≤ AA := hAA ▸ le_sup_left
  have hBs : Nat.card ↥Bs ≤ 3 ^ 6 := hcard.le
  have hcardR : Nat.card ↥(AA.map (ggLin (p := 3) ι)) ≤
      3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by
    calc Nat.card ↥(AA.map (ggLin (p := 3) ι)) = Nat.card ↥AA :=
          (Nat.card_congr (Subgroup.equivMapOfInjective AA (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) :=
          ggIndep_card_join_le AA ⟨y, hy⟩ hstabAA
      _ ≤ 3 ^ 6 * ((3 - 1) * 6 * Nat.factorial 6) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = 3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by rw [Nat.mul_comm (3 - 1) 6]
  have hres := hA5 3 rfl V hV6 (fun i => h (e i)) (fun i => α (e i)) yv r Fdep hr
    (AA.map (ggLin (p := 3) ι)) hrR hgenR hnt hcardR hstabR
  rcases hres with hlinW | hline
  · exact ggRC_weylReflGroup_of_linWeyl ι AA hlinW
  · exfalso
    obtain ⟨Λ', j1, j2, S', M', C', MJ', V', j3, j4, ι', φ', h', α', hS2', hS3', hW', hC', hWJ',
      hMJ', hlin', hrefl', hpair', ⟨f', hf'⟩, hcl', hfJ', hclJ', hconj'⟩ := hLs
    letI := j1; letI := j2
    haveI : Nontrivial Λ' := by
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num : 1 < 2) hS2')
      exact ⟨a, b, hab⟩
    exact ggWeyl_rootLine_false hp2 ι hLA hW' hrefl' f' hf' hcl' ⟨t', ht'L, ht'move⟩ hnt hline

theorem ggTwoNodeA5DepL
    (hA5 : LR6A5DepAll) (hOrb : GGResCentBoundInput) (hRig : GGLabelRigidInput)
    (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4) (hW : GGTBWNormLabelInput)
    (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labL => ggRowTwoNodeSmallJA q labJ labL ∧ labL.rank = 5) p J L)
    (hxL : x ∉ L) (hKs : GGResLeviSideDatumLE3 p Bs K J) (hp3 : p = 3)
    (hcard : Nat.card ↥Bs = 3 ^ 6) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨labJ₀, labL₀, hJΛ₀, hLΛ₀, hJl₀, hLl₀, hrow₀⟩ := hrow
  have hrowJA : GGResRowAt ggRowTwoNodeSmallJA p J L :=
    ⟨labJ₀, labL₀, hJΛ₀, hLΛ₀, hJl₀, hLl₀, hrow₀.1⟩
  have hLrank : labL₀.rank = 5 := hrow₀.2
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hrow' := ggTWSmallA_row_narrow hp2 hrowJA
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw) hH
      hrow' hxL
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have h4X : 4 ≤ labX.rank := by omega
  have hiso : GGLabelIso labL₀ labX := hRig labL₀ labX _ hLΛ₀ hXΛ hLl₀ hXl
  have hEq : labL₀ = labX := ggTWR_iso_eq hiso hAtag h4X
  have hN6 : N = 6 := by
    have : labX.rank = 5 := by rw [← hEq]; exact hLrank
    omega
  have hXd : GGResXDatumA p Bs L 5 := by
    have hN1 : N - 1 = 5 := by omega
    rw [hN1] at hdatL
    exact hdatL
  exact ggTwoNodeA5DepL_core hA5 hOrb hFix hFixK hp3 hH hx hcard hXd hxL hKs

end CFSG.StandardType

end
