module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineFrameK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineAllDefs
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepRefl
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeNineDepK_two (hAll : LR6NineAll) (hFix : GGTBFixInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstab : Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs))
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hXd : GGResXDatumA p Bs K 8) (hnc : y ∉ (ggBstarComm K Bs).map Bs.subtype)
    (hLs : GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨Λ, i1, i2, MK, CK, V, i3, i4, ι, φ, h, α, e, hMK, -, hCK, hlin, hrefl, hpair, ⟨f, -⟩,
    hclos⟩ := hXd
  letI := i1; letI := i2; letI := i3; letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hN5 : 5 ≤ 9 := by norm_num
  have hpN : 3 ∣ 9 := by norm_num
  let yv : V := ι (Additive.ofMul ⟨y, hy⟩)
  have hdep : ¬ LinearIndependent (ZMod 3) h :=
    ggNineDepK_dep_of_notComm hp2 hH hy hstrong hN5 hpN e hMK hCK hlin hrefl hpair hclos hnc
  have Fdep : GGDepAFrame 3 9 (fun i : Fin 8 => h (e i)) (fun i => α (e i)) yv :=
    ggXDatumA_depframe_K hp2 hH hy hstrong hpN e hMK hCK hlin hpair hclos hdep
  have hVN : Module.finrank (ZMod 3) V ≤ 9 := (ggDepA_finrank_bounds Fdep).2
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hgenL : GGReflGenerated 3 (ggAutomizer L Bs) := l6a_reflGen_of_side (Or.inr (Or.inl hLs))
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup hgenL (ggIndep_reflGenerated_of_closure hrefl hclos)
  obtain ⟨AA, hAA⟩ : ∃ AA : Subgroup (MulAut ↥Bs), AA = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hAA] at hgen' hA ⊢
  let r : Fin 8 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 8) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hlin (e i) v
  have hφAA : ∀ i, φ i ∈ AA := fun i =>
    hAA ▸ Subgroup.mem_sup_right (by rw [hclos]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hrR : ∀ i : Fin 8, r i ∈ AA.map (ggLin (p := 3) ι) := fun i =>
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
  have hcardA1 : Nat.card ↥(ggAutomizer K Bs) ≤ Nat.factorial 9 := by
    have h1 : Nat.card ↥(ggAutomizer K Bs) = Nat.card MK.Group :=
      (Nat.card_congr f.toEquiv).symm
    have h2 : Nat.card MK.Group = Nat.card (CoxeterMatrix.A 8).Group := by
      rw [hMK]
      exact Nat.card_congr ((CoxeterMatrix.A 8).reindexGroupEquiv e).toEquiv
    have h3 : Nat.card (CoxeterMatrix.A 8).Group = Nat.factorial 9 := by
      rw [l05nK3a_card_coxeterA 8]
    rw [h1, h2, h3]
  have hstabAA := hstab
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
      MulAction.stabilizer (V ≃ₗ[ZMod 3] V) yv) ≤ (3 - 1) * 6 * Nat.factorial 9 := by
    rw [← hmapStab]
    calc Nat.card ↥((AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)).map
          (ggLin (p := 3) ι))
        = Nat.card ↥(AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := hstabAA
      _ ≤ (3 - 1) * 6 * Nat.factorial 9 := Nat.mul_le_mul_left _ hcardA1
  obtain ⟨t', ht'L, ht'refl, ht'move⟩ := ggIndep_moving_L hFix hH hy hgenL
  have hLA : ggAutomizer L Bs ≤ AA := hAA ▸ le_sup_left
  have hmovR : ∃ s ∈ AA.map (ggLin (p := 3) ι), GGLinRefl s ∧ s yv ≠ yv := by
    refine ⟨ggLin (p := 3) ι t', Subgroup.mem_map.mpr ⟨t', hLA ht'L, rfl⟩,
      (ggRC_isReflection_iff_linRefl (p := 3) ι t').mp ht'refl, ?_⟩
    intro hfix
    exact ht'move ((ggLin_fix_iff (p := 3) ι t' ⟨y, hy⟩).mpr hfix)
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hBs : Nat.card ↥Bs ≤ 3 ^ 9 := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hVN
  have hcardR : Nat.card ↥(AA.map (ggLin (p := 3) ι)) ≤ 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by
    calc Nat.card ↥(AA.map (ggLin (p := 3) ι)) = Nat.card ↥AA :=
          (Nat.card_congr (Subgroup.equivMapOfInjective AA (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) :=
          ggIndep_card_join_le AA ⟨y, hy⟩ hstabAA
      _ ≤ 3 ^ 9 * ((3 - 1) * 6 * Nat.factorial 9) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by rw [Nat.mul_comm (3 - 1) 6]
  have hres := hAll 3 rfl V hVN (fun i => h (e i)) (fun i => α (e i)) yv r Fdep hr
    (AA.map (ggLin (p := 3) ι)) hrR hgenR hnt hcardR hstabR hmovR
  rcases hres with hlinW | ⟨t, -, -, -, htcent, htuniq⟩
  · exact ggRC_weylReflGroup_of_linWeyl ι AA hlinW
  · exfalso
    obtain ⟨Λ', j1, j2, b₁, b₂, M', C', MJ', V', j3, j4, ι', φ', h', α', hb, hW', hC', hWJ', hMJ',
      hlin', hrefl', hpair', ⟨f', hf'⟩, hcl', hfJ', hclJ', hconj'⟩ := hLs
    letI := j1; letI := j2
    haveI : Nontrivial Λ' := ⟨⟨b₁, b₂, hb⟩⟩
    exact ggNine_A1_false ι hLA hW' hrefl' f' hf' hcl' ⟨t', ht'L, ht'move⟩ htcent htuniq

theorem ggTwoNodeNineDepK_two_of_orbK (hAll : LR6NineAll) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hXd : GGResXDatumA p Bs K 8) (hnc : y ∉ (ggBstarComm K Bs).map Bs.subtype)
    (hLs : GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  ggTwoNodeNineDepK_two hAll hFix hp3 hH hy (hOrbK G p B Bs x L D J y K hH hy) hstrong hXd hnc hLs

end CFSG.StandardType

end
