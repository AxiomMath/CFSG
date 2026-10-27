module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLDatumWeyl
public import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
public import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggPmD_not_even_succ {r : ℕ} (h : Even r) : ¬ Even (r + 1) := by
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.even_add_one]
  intro h2
  exact h2 ⟨k, rfl⟩

private theorem ggPmD_card_ge {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel}
    (hW : GGQ2LabelWeyl labL M.coxeter) (hlab : GGQ2TBLabel labL) :
    3 ≤ Fintype.card M.Λ := by
  have h := ggQ2LD_card_lie hW hlab
  rcases hlab with ⟨htag, h4⟩ | ⟨htag, h4⟩ | ⟨htag, -, h4⟩ | ⟨htag, -, h4⟩ |
    htag | htag | htag | htag
  · rw [h]; simp [GGQ2LieRank, htag]; omega
  · rcases htag with htag | htag <;> rw [h] <;> simp [GGQ2LieRank, htag] <;> omega
  · rw [h]; simp [GGQ2LieRank, htag]; omega
  · rw [h]; simp [GGQ2LieRank, htag]; omega
  · rw [h]; simp [GGQ2LieRank, htag]
  · rw [h]; simp [GGQ2LieRank, htag]
  · rw [h]; simp [GGQ2LieRank, htag]
  · rw [h]; simp [GGQ2LieRank, htag]

private theorem ggPmD_fix {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) :
    ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := by
  intro v
  have hfixed : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) ↔
      ∀ g ∈ M.toWDatum.weyl, g v = v := by
    rw [M.weyl_eq_map, mem_ggFixedSubmodule_iff]
    constructor
    · rintro h g hg
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h φ hφ
    · intro h φ hφ
      exact h (ggLin (p := 3) M.model φ) (Subgroup.mem_map_of_mem _ hφ)
  rw [← hfixed, M.fixed_x]
  rfl

private theorem ggPmD_transvectionFree {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x)
    (hNT : GGNoTransvection 3 Bs) : TransvectionFree M.toWDatum.weyl := by
  have htop : TransvectionFree ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)) := by
    rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
    rw [Subgroup.mem_map] at hg
    obtain ⟨φ, hφ, rfl⟩ := hg
    obtain ⟨k, -, hkN, hkφ⟩ := mem_ggAutomizer_iff.mp hφ
    exact hNT φ ⟨k, Subgroup.mem_top k, hkN, hkφ⟩
      (ggIsTransvection_of_apply M.model hu hψ hψu hgv)
  rw [M.weyl_eq_map]
  intro g hg
  refine htop g (Subgroup.map_mono ?_ hg)
  rw [ggAutomizer, ggAutomizer]
  exact Subgroup.closure_mono (by
    rintro φ ⟨g, hgL, hgn, hgφ⟩
    exact ⟨g, Subgroup.mem_top g, hgn, hgφ⟩)

private theorem ggPmD_of_wpm {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (φ : MulAut ↥Bs)
    (hpm : ∃ w' ∈ M.toWDatum.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model φ (w' v) - ε • v ∈
        Submodule.span (ZMod 3) {M.xV}) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  obtain ⟨w', hw', ε, hε, hpm⟩ := hpm
  have hw'map : w' ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model) := by
    rwa [M.weyl_eq_map] at hw'
  obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp hw'map
  refine ⟨w, hw, ε, hε, fun v => ?_⟩
  rw [map_mul, LinearEquiv.mul_apply]
  have hwv : (ggLin (p := 3) M.model w) v = w' v :=
    congrArg (fun e : M.V ≃ₗ[ZMod 3] M.V => e v) hw_eq
  rw [hwv]
  exact hpm v

private theorem ggPmD_inner {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (φ : MulAut ↥Bs)
    (hfix : ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV})
    (hcard : 3 ≤ Fintype.card M.Λ)
    (hind : LinearIndependent (ZMod 3) M.coroot)
    {n : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ)
    (hC : ∀ i j, M.toWDatum.cartan (e i) (e j) = C₀ i j)
    (hInner : GGQ2WeylInner n C₀)
    (hT : ggLin (p := 3) M.model φ ∈
      Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V))) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  obtain ⟨w', hw', ε, hε, hpm⟩ :=
    M.toWDatum.pmW_of_inner M.xV hfix hcard (ggLin (p := 3) M.model φ)
      (M.toWDatum.inner_of_transport C₀ e hC hind hInner _ hT)
  exact ggPmD_of_wpm M φ ⟨w', hw', ε, hε, hpm⟩

private theorem ggPmD_ker {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (φ : MulAut ↥Bs)
    (hfix : ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV})
    (hx : M.xV ≠ 0) (hCshape : M.ShapeC)
    (h6 : 6 ≤ Module.finrank (ZMod 3) M.V)
    (hNT : GGNoTransvection 3 Bs)
    (hT : ggLin (p := 3) M.model φ ∈
      Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V))) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  have hdimEq : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 := hCshape.2.2.2.1
  have hdimco : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hCshape.2.1
  have hnotli : ¬ LinearIndependent (ZMod 3) M.coroot := by
    intro hli
    have hfr : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hli
    omega
  obtain ⟨κ, hκsum, hκi⟩ := Fintype.not_linearIndependent_iff.mp hnotli
  have hκne : κ ≠ 0 := by
    obtain ⟨i, hi⟩ := hκi
    exact fun h => hi (congrFun h i)
  have hker : ∃ κ : M.Λ → ZMod 3, κ ≠ 0 ∧
      ∀ i : M.Λ, ∑ j : M.Λ, (M.cartan i j : ZMod 3) * κ j = 0 := by
    refine ⟨κ, hκne, fun i => ?_⟩
    have h := congrArg (M.root i) hκsum
    simp only [map_sum, map_smul, M.pairing, map_zero] at h
    simpa [mul_comm] using h
  have hdim : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ + 1 := le_of_eq hdimEq
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by omega
  have hTF : TransvectionFree M.toWDatum.weyl := ggPmD_transvectionFree M hNT
  obtain ⟨w', hw', ε, hε, hpm⟩ :=
    M.toWDatum.pmW_of_ker M.xV hx hfix hker hdim h4 hTF (Or.inr hdimEq)
      (ggLin (p := 3) M.model φ) hT
  exact ggPmD_of_wpm M φ ⟨w', hw', ε, hε, hpm⟩

private theorem ggPmD_indep {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (φ : MulAut ↥Bs)
    {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hne : labL.tag ≠ .twE6)
    (hsh3 : M.ShapeFull ∨ M.ShapeA ∨ M.ShapeD)
    (hev : Even (Module.finrank (ZMod 3) M.V))
    (h6 : 6 ≤ Module.finrank (ZMod 3) M.V)
    (hhrt : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)
    (hdim_le : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ + 1)
    (hfix : ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV})
    (hcard : 3 ≤ Fintype.card M.Λ)
    (hind : LinearIndependent (ZMod 3) M.coroot)
    (hT : ggLin (p := 3) M.model φ ∈
      Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V))) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  have hcard_eq : Fintype.card M.Λ = GGQ2LieRank labL := ggQ2LD_card_lie hW hlab
  have hdimH : M.ShapeD → Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
    fun hD => ggQ2LD_dim_heart M (Or.inr hD)
  have hdimN : (M.ShapeFull ∨ M.ShapeA) →
      Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 := by
    rintro (hF | hA)
    · exact ggQ2LD_dim_nonheart M (Or.inl hF)
    · exact ggQ2LD_dim_nonheart M (Or.inr (Or.inl hA))
  have hnon : ¬ M.ShapeD → M.ShapeFull ∨ M.ShapeA := by
    intro hD
    rcases hsh3 with hF | hA | hDD
    · exact Or.inl hF
    · exact Or.inr hA
    · exact absurd hDD hD
  have hlab0 : GGQ2TBLabel labL := hlab
  rcases labL with ⟨tag, rank, n⟩
  rcases hlab with ⟨htwA, hrA⟩ | ⟨hBC, hrBC⟩ | ⟨hDtag, hEvenD, hrD⟩ |
    ⟨htwD, hOddD, hrD⟩ | hF4 | htwE6 | hE7 | hE8
  · have htag : tag = .twA := htwA
    have hcart := ggQ2_label_cartan M hW hlab0
    simp [htag] at hcart
    obtain ⟨e, hC⟩ := hcart
    exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.A rank) e hC
      (ggQ2WeylInner_A (by omega)) hT
  · rcases hBC with htagB | htagC
    · have htag : tag = .B := htagB
      have hr : 4 ≤ rank := hrBC
      have hcart := ggQ2_label_cartan M hW hlab0
      simp [htag] at hcart
      obtain ⟨e, hBCH⟩ := hcart
      rcases hBCH with hCB | hCC
      · exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.B rank) e hCB
          (ggQ2WeylInner_B (by omega)) hT
      · exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.C rank) e hCC
          (ggQ2WeylInner_C (by omega)) hT
    · have htag : tag = .C := htagC
      have hr : 4 ≤ rank := hrBC
      have hcart := ggQ2_label_cartan M hW hlab0
      simp [htag] at hcart
      obtain ⟨e, hBCH⟩ := hcart
      rcases hBCH with hCB | hCC
      · exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.B rank) e hCB
          (ggQ2WeylInner_B (by omega)) hT
      · exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.C rank) e hCC
          (ggQ2WeylInner_C (by omega)) hT
  · by_cases hD : M.ShapeD
    · have hdim := hdimH hD
      rcases hhrt (le_of_eq hdim) with ⟨htagA, -⟩ | htagE6
      · exact absurd hDtag (by rw [htagA]; decide)
      · exact absurd htagE6 hne
    · have hnonD := hnon hD
      have hdim := hdimN hnonD
      have htagD : tag = .D := hDtag
      have hcardrank : Fintype.card M.Λ = rank := by
        rw [hcard_eq]; simp [GGQ2LieRank, htagD]
      rw [hdim, hcardrank] at hev
      exact absurd hev (ggPmD_not_even_succ hEvenD)
  · have htag : tag = .twD := htwD
    have hcart := ggQ2_label_cartan M hW hlab0
    simp [htag] at hcart
    obtain ⟨e, hC⟩ := hcart
    obtain ⟨k, hk⟩ := hOddD
    exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.D rank) e hC
      (ggQ2WeylInner_D_odd (by omega) ⟨k, hk⟩) hT
  · have htagF4 : tag = .F4 := hF4
    have hcard4 : Fintype.card M.Λ = 4 := by
      rw [hcard_eq]; simp [GGQ2LieRank, htagF4]
    omega
  · exact absurd htwE6 hne
  · have htag : tag = .E7 := hE7
    have hcart := ggQ2_label_cartan M hW hlab0
    simp [htag] at hcart
    obtain ⟨e, hC⟩ := hcart
    exact ggPmD_inner M φ hfix hcard hind (CartanMatrix.E 7) e hC
      ggQ2WeylInner_E7 hT
  · have htagE8 : tag = .E8 := hE8
    have hcard8 : Fintype.card M.Λ = 8 := by
      rw [hcard_eq]; simp [GGQ2LieRank, htagE8]
    by_cases hD : M.ShapeD
    · have hdim := hdimH hD
      rcases hhrt (le_of_eq hdim) with ⟨htagA, -⟩ | htagE6
      · exact absurd hE8 (by rw [htagA]; decide)
      · exact absurd htagE6 hne
    · have hnonD := hnon hD
      have hdim := hdimN hnonD
      rw [hdim, hcard8] at hev
      norm_num at hev

theorem ggQ2_pm_of_datum {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hne : labL.tag ≠ .twE6) (hsh : M.Shape) (hx : M.xV ≠ 0)
    (hev : Even (Module.finrank (ZMod 3) M.V)) (h6 : 6 ≤ Module.finrank (ZMod 3) M.V)
    (hhrt : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)
    (hB : ¬ M.ShapeB) (hNT : GGNoTransvection 3 Bs) (φ : MulAut ↥Bs)
    (hN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  have hcard : 3 ≤ Fintype.card M.Λ := ggPmD_card_ge M hW hlab
  have hfix : ∀ v : M.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := ggPmD_fix M
  have hT : ggLin (p := 3) M.model φ ∈
      Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V)) := by
    have hmem : ggLin (p := 3) M.model φ ∈
        (Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))).map
          (ggLin (p := 3) M.model) :=
      Subgroup.mem_map_of_mem _ hN
    have hle := Subgroup.le_normalizer_map (f := ggLin (p := 3) M.model) hmem
    rwa [← M.weyl_eq_map] at hle
  have hdim_le : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ + 1 :=
    ggQ2LD_finrank_le_card_succ M hsh
  rcases hsh with hF | hA | hBsh | hCsh | hDsh
  · exact ggPmD_indep M φ hW hlab hne (Or.inl hF) hev h6 hhrt hdim_le hfix hcard
      hF.2.1 hT
  · exact ggPmD_indep M φ hW hlab hne (Or.inr (Or.inl hA)) hev h6 hhrt hdim_le hfix hcard
      hA.2.1 hT
  · exact absurd hBsh hB
  · exact ggPmD_ker M φ hfix hx hCsh h6 hNT hT
  · exact ggPmD_indep M φ hW hlab hne (Or.inr (Or.inr hDsh)) hev h6 hhrt hdim_le hfix hcard
      hDsh.2.1 hT

end CFSG.StandardType

end
