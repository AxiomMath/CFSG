module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepFrame
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepRefl
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma nt9_span_gen_le_image {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤
      (ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs)) : Set V) := by
  let H : Submodule (ZMod p) V :=
    { carrier := ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs))
      zero_mem' := ⟨0, ⟨1, Subgroup.one_mem _, rfl⟩, by simp⟩
      add_mem' := by
        rintro u v ⟨du, hdu, rfl⟩ ⟨dv, hdv, rfl⟩
        obtain ⟨cu, hcu, rfl⟩ := hdu
        obtain ⟨cv, hcv, rfl⟩ := hdv
        exact ⟨Additive.ofMul (cu * cv), ⟨cu * cv, Subgroup.mul_mem _ hcu hcv, rfl⟩, by
          show ι (Additive.ofMul (cu * cv)) = ι (Additive.ofMul cu) + ι (Additive.ofMul cv)
          rw [← map_add, ← ofMul_mul]⟩
      smul_mem' := by
        rintro a u ⟨d, hd, rfl⟩
        obtain ⟨c, hc, rfl⟩ := hd
        refine ⟨Additive.ofMul (c ^ a.val), ⟨c ^ a.val, Subgroup.pow_mem _ hc a.val, rfl⟩, ?_⟩
        show ι (Additive.ofMul (c ^ a.val)) = a • ι (Additive.ofMul c)
        have h1 : a • ι (Additive.ofMul c) = (a.val : ℕ) • ι (Additive.ofMul c) := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [h1, ← map_nsmul, ofMul_pow] }
  intro v hv
  have hle : Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
      ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤ H := by
    rw [Submodule.span_le]
    rintro v ⟨q, rfl⟩
    change ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2 ∈ (H : Set V)
    obtain ⟨b, hb⟩ := ι.surjective q.2
    have hb' : q.2 = ι (Additive.ofMul (Additive.toMul b)) := by
      rw [← hb]
      exact congrArg ι (ofMul_toMul b).symm
    rw [hb']
    refine ⟨Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b)),
      ⟨(Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b), ?_, rfl⟩, ?_⟩
    · exact Subgroup.subset_closure ⟨Additive.toMul b, q.1, q.1.2, rfl⟩
    · show ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) (ι (Additive.ofMul (Additive.toMul b))) -
          ι (Additive.ofMul (Additive.toMul b))
      rw [ggLin_apply_ofMul]
      have hkeyV : ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
          ι (Additive.ofMul ((q.1 : MulAut ↥Bs) (Additive.toMul b))) -
            ι (Additive.ofMul (Additive.toMul b)) := by
        rw [ofMul_mul, ofMul_inv, map_add, map_neg]
        abel
      exact hkeyV
  exact hle hv

theorem ggNine_A1_false {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {AA AK : Subgroup (MulAut ↥Bs)} (hKA : AK ≤ AA) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    [Nontrivial Λ] {M : CoxeterMatrix Λ} (hW : GGIsWeylMatrix M) {φ : Λ → MulAut ↥Bs}
    (hrefl : ∀ i, GGIsReflection p (φ i)) (f : M.Group ≃* ↥AK)
    (hf : ∀ i, ((f (M.simple i) : ↥AK) : MulAut ↥Bs) = φ i)
    (hcl : AK = Subgroup.closure (Set.range φ)) {z : ↥Bs} (hmove : ∃ t ∈ AK, t z ≠ z)
    {t : V ≃ₗ[ZMod p] V} (htcent : ∀ g ∈ AA.map (ggLin (p := p) ι), g * t = t * g)
    (htuniq : ∀ s ∈ AA.map (ggLin (p := p) ι), GGLinRefl s →
      s (ι (Additive.ofMul z)) ≠ ι (Additive.ofMul z) → s = t) : False := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, φ i z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨t', ht'K, ht'z⟩ := hmove
    apply ht'z
    have hle : AK ≤ MulAction.stabilizer (MulAut ↥Bs) z := by
      rw [hcl, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr (hcon j)
    exact MulAction.mem_stabilizer_iff.mp (hle ht'K)
  have hφK : ∀ j, φ j ∈ AK := fun j => by rw [hcl]; exact Subgroup.subset_closure ⟨j, rfl⟩
  have hψR : ∀ j, ggLin (p := p) ι (φ j) ∈ AA.map (ggLin (p := p) ι) := fun j =>
    Subgroup.mem_map.mpr ⟨φ j, hKA (hφK j), rfl⟩
  have hψi : ggLin (p := p) ι (φ i) = t := by
    refine htuniq _ (hψR i) ((ggRC_isReflection_iff_linRefl (p := p) ι _).mp (hrefl i)) ?_
    intro hfix
    exact hi ((ggLin_fix_iff (p := p) ι (φ i) z).mpr hfix)
  have hcomm : ∀ j, φ i * φ j = φ j * φ i := by
    intro j
    apply ggLin_injective (p := p) ι
    rw [map_mul, map_mul, hψi]
    exact (htcent _ (hψR j)).symm
  obtain ⟨j, hji, hj3⟩ := ggWeyl_exists_bond hW i
  have hsc : M.simple i * M.simple j = M.simple j * M.simple i := by
    apply f.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hf, hf]
    exact hcomm j
  have hii : M.simple i * M.simple i = 1 :=
    CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem i
  have hjj : M.simple j * M.simple j = 1 :=
    CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem j
  have hsq : (M.simple i * M.simple j) ^ 2 = 1 := by
    rw [pow_two]
    calc M.simple i * M.simple j * (M.simple i * M.simple j)
        = M.simple i * (M.simple j * M.simple i) * M.simple j := by group
      _ = M.simple i * (M.simple i * M.simple j) * M.simple j := by rw [hsc]
      _ = (M.simple i * M.simple i) * (M.simple j * M.simple j) := by group
      _ = 1 := by rw [hii, hjj, one_mul]
  have hord : orderOf (M.simple i * M.simple j) = M.M i j :=
    CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
  have hdvd : M.M i j ∣ 2 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hsq
  have hle : M.M i j ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem ggTwoNodeNineDepL_two (hAll : LR6NineAll) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hXd : GGResXDatumA p Bs L 8)
    (hnc : x ∉ (ggBstarComm L Bs).map Bs.subtype) (hKs : GGResTwoNodeSideDatum p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨Λ, i1, i2, ML, CL, V, i3, i4, ι, φ, h, α, e, hML, hWML, hCL, hlin, hrefl, hpair, ⟨f, hf⟩,
    hclos⟩ := hXd
  letI := i1; letI := i2; letI := i3; letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hN5 : 5 ≤ 9 := by norm_num
  have hpN : 3 ∣ 9 := by norm_num
  let xv : V := ι (Additive.ofMul ⟨x, hx⟩)
  have hdep : ¬ LinearIndependent (ZMod 3) h := by
    intro hindL
    have Find := ggXDatumA_indep_frame hFix hp2 hH hx hN5 hpN e hML hCL hlin hpair hclos hindL
    have hrange : Set.range (fun i : Fin 8 => h (e i)) = Set.range h :=
      e.surjective.range_comp h
    have hxmem : xv ∈ Submodule.span (ZMod 3) (Set.range h) := by
      rw [← hrange]
      exact Find.x_mem
    have hspan := l6tr_span_eq (p := 3) (X := L) (Bs := Bs) (ι := ι) (φ := φ) (h := h) (α := α)
      hlin hrefl hclos
    have hxgen : xv ∈ Submodule.span (ZMod 3) (Set.range (fun q : ↥(ggAutomizer L Bs) × V =>
        ggLin (p := 3) ι q.1 q.2 - q.2)) := by
      rw [← hspan]
      exact hxmem
    have hxH := nt9_span_gen_le_image (p := 3) (X := L) (Bs := Bs) ι hxgen
    obtain ⟨d, hd, hdv⟩ := hxH
    obtain ⟨c, hc, rfl⟩ := hd
    apply hnc
    refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
    have h1 : ι (Additive.ofMul c) = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) := by
      rw [hdv]
    have h2 : Additive.ofMul c = Additive.ofMul (⟨x, hx⟩ : ↥Bs) := ι.injective h1
    exact congrArg Subtype.val (by simpa using h2)
  have Fdep : GGDepAFrame 3 9 (fun i : Fin 8 => h (e i)) (fun i => α (e i)) xv :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hML hCL hlin hpair hclos hdep
  have hVN : Module.finrank (ZMod 3) V ≤ 9 := (ggDepA_finrank_bounds Fdep).2
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hgenK : GGReflGenerated 3 (ggAutomizer K Bs) := hH.2.2.2.2.2.1
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup (ggIndep_reflGenerated_of_closure hrefl hclos) hgenK
  obtain ⟨AA, hAA⟩ : ∃ AA : Subgroup (MulAut ↥Bs), AA = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hAA] at hgen' hA ⊢
  let r : Fin 8 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 8) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hlin (e i) v
  have hφAA : ∀ i, φ i ∈ AA := fun i =>
    hAA ▸ Subgroup.mem_sup_left (by rw [hclos]; exact Subgroup.subset_closure ⟨i, rfl⟩)
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
  have hcardA1 : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial 9 := by
    have h1 : Nat.card ↥(ggAutomizer L Bs) = Nat.card ML.Group :=
      (Nat.card_congr f.toEquiv).symm
    have h2 : Nat.card ML.Group = Nat.card (CoxeterMatrix.A 8).Group := by
      rw [hML]
      exact Nat.card_congr ((CoxeterMatrix.A 8).reindexGroupEquiv e).toEquiv
    have h3 : Nat.card (CoxeterMatrix.A 8).Group = Nat.factorial 9 := by
      rw [l05nK3a_card_coxeterA 8]
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
      MulAction.stabilizer (V ≃ₗ[ZMod 3] V) xv) ≤ (3 - 1) * 6 * Nat.factorial 9 := by
    rw [← hmapStab]
    calc Nat.card ↥((AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map
          (ggLin (p := 3) ι))
        = Nat.card ↥(AA ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hstabAA
      _ ≤ (3 - 1) * 6 * Nat.factorial 9 := Nat.mul_le_mul_left _ hcardA1
  obtain ⟨t', ht'K, ht'refl, ht'move⟩ := ggIndep_moving_K hFixK hH hx
  have hKA : ggAutomizer K Bs ≤ AA := hAA ▸ le_sup_right
  have hmovR : ∃ s ∈ AA.map (ggLin (p := 3) ι), GGLinRefl s ∧ s xv ≠ xv := by
    refine ⟨ggLin (p := 3) ι t', Subgroup.mem_map.mpr ⟨t', hKA ht'K, rfl⟩,
      (ggRC_isReflection_iff_linRefl (p := 3) ι t').mp ht'refl, ?_⟩
    intro hfix
    exact ht'move ((ggLin_fix_iff (p := 3) ι t' ⟨x, hx⟩).mpr hfix)
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
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
          ggIndep_card_join_le AA ⟨x, hx⟩ hstabAA
      _ ≤ 3 ^ 9 * ((3 - 1) * 6 * Nat.factorial 9) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by rw [Nat.mul_comm (3 - 1) 6]
  have hres := hAll 3 rfl V hVN (fun i => h (e i)) (fun i => α (e i)) xv r Fdep hr
    (AA.map (ggLin (p := 3) ι)) hrR hgenR hnt hcardR hstabR hmovR
  rcases hres with hlinW | ⟨t, -, -, -, htcent, htuniq⟩
  · exact ggRC_weylReflGroup_of_linWeyl ι AA hlinW
  · exfalso
    obtain ⟨Λ', j1, j2, b₁, b₂, M', C', MJ', V', j3, j4, ι', φ', h', α', hb, hW', hC', hWJ', hMJ',
      hlin', hrefl', hpair', ⟨f', hf'⟩, hcl', hfJ', hclJ', hconj'⟩ := hKs
    letI := j1; letI := j2
    haveI : Nontrivial Λ' := ⟨⟨b₁, b₂, hb⟩⟩
    exact ggNine_A1_false ι hKA hW' hrefl' f' hf' hcl' ⟨t', ht'K, ht'move⟩ htcent htuniq

end CFSG.StandardType

end
