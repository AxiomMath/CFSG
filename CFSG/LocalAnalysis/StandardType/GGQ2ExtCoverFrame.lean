module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplit

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def ExtE6At (R : RawFrameData) (vx z : R.V) (ℓ k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup ℓ ∧
    W.toLin.parab {i | i ≠ W.b} = R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {vx}) ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z}) ∧
    ∃ e : Fin 6 ≃ W.ι, W.coxeter = CoxeterMatrix.E₆.reindex e ∧ W.a = e 1

@[expose] def NbrLinAt (R : RawFrameData) (z : R.V) (k : R.Code) (W : GGQ2LinOn 3 R.V) : Prop :=
  W.toLin.weyl = R.normalizerGroup k ∧
    ∀ v, (∀ i, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z}

@[expose] def ExtInnerAt (R : RawFrameData) (z : R.V) (k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V, NbrLinAt R z k W ∧ ((W.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
    ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ W.ι),
      (∀ i j, W.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀

@[expose] def ExtDetAt (R : RawFrameData) (z : R.V) (k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V, NbrLinAt R z k W ∧ ((W.cartan.det : ℤ) : ZMod 3) = 0 ∧
    (LinearIndependent (ZMod 3) W.coroot ∨ finrank (ZMod 3) R.V = Fintype.card W.ι + 1)

@[expose] def ExtAmbDAt (R : RawFrameData) (vx z : R.V) (ℓ k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup k ∧
    W.toLin.simpleRefl W.a ∈ R.normalizerGroup ℓ ⊔ R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z}) ∧
    (∀ i, i ≠ W.a → i ≠ W.b → W.root i vx = 0) ∧ W.toLin.Basis ∧
    ∃ m : ℕ, 3 ≤ m ∧ ∃ f : Fin (2 * m) ≃ {i // i ≠ W.a},
      ∀ i j, W.cartan (f i) (f j) = CartanMatrix.D (2 * m) i j

@[expose] def ExtD5At (R : RawFrameData) (vx z : R.V) (ℓ j k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup k ∧
    W.toLin.simpleRefl W.a ∈ R.normalizerGroup ℓ ⊔ R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z}) ∧
    (∀ i, i ≠ W.a → i ≠ W.b → W.root i vx = 0) ∧ W.toLin.Basis ∧
    (∃ e : Fin 5 ≃ W.ι, (∀ i j, W.cartan (e i) (e j) = CartanMatrix.D 5 i j) ∧ W.a = e 0 ∧
      (W.b = e 1 ∨ W.b = e 3 ∨ W.b = e 4)) ∧
    W.toLin.parab {i | i ≠ W.a ∧ i ≠ W.b} = R.normalizerGroup j ∧
    ∃ lab : LargeEvenLabel, (lab = ⟨.twA, 3, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩) ∧ GGLabelIso lab (R.label j) ∧
    R.inside j ⊓ R.cent j = ⊥ ∧ R.inside j ⊔ R.cent j = ⊤ ∧ finrank (ZMod 3) (R.inside j) = 3

@[expose] def ExtCases (R : RawFrameData) : Prop :=
  ∀ vx : R.V, vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ →
    (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∉ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k : R.Code, Candidate R vx j z k →
    R.inside j ≤ R.inside k →
    TwoNodeLabels 3 (R.label ℓ) (R.label j) ∨ TwoNodeLabels 3 (R.label k) (R.label j) ∨
    InLLeafAt R vx z ℓ k ∨ ExtE6At R vx z ℓ k ∨ ExtInnerAt R z k ∨ ExtDetAt R z k ∨
    ExtAmbDAt R vx z ℓ k ∨ ExtD5At R vx z ℓ j k

@[expose] def GGQ2ExtCoverAtFrame (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K → ActualFrame (ggG0 p B x L D J) Bs R →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2NbrE6Sel p Bs x y D L J K → ¬ GGQ2SelInner G p Bs y J K →
    ¬ GGQ2NbrAmbDSel p Bs x y L K → ¬ GGQ2SelDet G p Bs y J K →
    GGQ2NbrD5Frame p Bs x y L J K

@[expose] def ExtNbrBridge (R : RawFrameData) : Prop :=
  GGLBalanceInput → GGStdSubPrimeInput →
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G},
    GGNbr 3 B x D J y K → ∀ (real : Realization (ggG0 3 B x L D J) Bs R) (hyBs : y ∈ Bs)
    {k : R.Code}, R.admissible k → real.component k = K →
    R.cent k = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) →
    ∀ W : GGQ2LinOn 3 R.V, NbrLinAt R (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k W →
    ∃ (N : GGQ2NbrDatum 3 Bs K) (e : W.ι ≃ N.Λ),
      (∀ i j, N.cartan (e i) (e j) = W.cartan i j) ∧ N.coxeter = W.coxeter.reindex e ∧
      ((N.cartan.det : ℤ) : ZMod 3) = ((W.cartan.det : ℤ) : ZMod 3) ∧
      (LinearIndependent (ZMod 3) N.coroot ↔ LinearIndependent (ZMod 3) W.coroot) ∧
      Module.finrank (ZMod 3) N.V = Module.finrank (ZMod 3) R.V

@[expose] def ExtD5Bridge (R : RawFrameData) : Prop :=
  GGLBalanceInput → GGStdSubPrimeInput → GGLabelRigidInput →
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → x ∉ L → ∀ {y : G} {K : Subgroup G},
    GGNbr 3 B x D J y K → ∀ (real : Realization (ggG0 3 B x L D J) Bs R) (hxBs : x ∈ Bs)
    (hyBs : y ∈ Bs) {ℓ j k : R.Code}, R.admissible ℓ → real.component ℓ = L → R.admissible j →
    real.component j = J → R.admissible k → real.component k = K →
    ExtD5At R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
      (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) ℓ j k →
    GGQ2NbrD5Frame 3 Bs x y L J K

theorem extCoverAtFrame_of_cases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) {R : RawFrameData} (hN : ExtNbrBridge R) (hD5 : ExtD5Bridge R)
    (hC : ExtCases R) : GGQ2ExtCoverAtFrame R := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb hF hrow hleaf hE6 hin hamb hdet
  subst hp
  obtain ⟨real⟩ := hF
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  obtain ⟨hyx, hxy, hyBs, ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent,
    hjcomp, hins, hnorm, hvx0, hUfin, hxU⟩ :=
    ggQ2CensusFrame_setup real hS hI1 hxBs hnb
  obtain ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK, hcandK, hvyU, hvyx⟩ :=
    ggQ2CensusFrame_caseDCand real hLB hP hS hI1 hxBs hnb hyx hxy hyBs hjadm hjcomp
  have hLk : ∀ (W : GGQ2LinOn 3 R.V) (S : Set W.ι),
      W.toLin.parab S = R.normalizerGroup ℓ →
      (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) = W.toLin.parab S := fun W S h => by
    rw [h, ← real.normalizer_eq ℓ hℓadm, hℓcomp]
  have hKk : ∀ (W : GGQ2LinOn 3 R.V) (S : Set W.ι),
      W.toLin.parab S = R.normalizerGroup k →
      (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) = W.toLin.parab S := fun W S h => by
    rw [h, ← real.normalizer_eq k hkadm, hkcomp]
  rcases hC _ hvx0 ℓ hℓadm (codeL_label_q2 hrig real hS hℓadm hℓcomp) hℓocc hℓcent
    (fun h => hxL (hvxℓ.mp h)) _ hUfin hxU j hjadm hjocc hjcent hins hnorm _ hvyU hvyx k hcandK
    hinsJK with
    htwoL | htwoK | ⟨W, hWL, hWK, hfixx, hfixy, hleafW⟩ |
    ⟨W, hWL, hWK, hfixx, hfixy, e, hcox, hae⟩ | hI | hD | hA | h5
  · exact (hrow (Or.inl ((markedRow_iff 3 L J).mpr
      ⟨R.label ℓ, R.label j, hℓcomp ▸ real.marked ℓ hℓadm, hjcomp ▸ real.marked j hjadm,
        htwoL⟩))).elim
  · exact (hrow (Or.inr ((markedRow_iff 3 K J).mpr
      ⟨R.label k, R.label j, hkcomp ▸ real.marked k hkadm, hjcomp ▸ real.marked j hjadm,
        htwoK⟩))).elim
  · exact (hleaf (GGQ2Lin.toModel (p := 3) (by norm_num) W.toLin real.coord hxBs hyBs
      (hLk W _ hWL) (hKk W _ hWK) hfixx hfixy) hleafW).elim
  · exact (hE6 ⟨GGQ2Lin.toModel (p := 3) (by norm_num) W.toLin real.coord hxBs hyBs
      (hLk W _ hWL) (hKk W _ hWK) hfixx hfixy, e, hcox, hae⟩).elim
  · obtain ⟨W, hW, hdetW, n, C₀, e, hC₀, hWI⟩ := hI
    obtain ⟨N, e', hcart, -, hdetN, -, -⟩ :=
      hN hLB hP hS hI1 hnb real hyBs hkadm hkcomp hkcent W hW
    refine (hin ⟨N, by rw [hdetN]; exact hdetW, n, C₀, e.trans e', fun i j => ?_,
      fun _ => hWI⟩).elim
    simp only [Equiv.trans_apply]
    rw [hcart, hC₀]
  · obtain ⟨W, hW, hdet0, hpos⟩ := hD
    obtain ⟨N, e', -, -, hdetN, hind, hfin⟩ :=
      hN hLB hP hS hI1 hnb real hyBs hkadm hkcomp hkcent W hW
    refine (hdet ⟨N, by rw [hdetN]; exact hdet0, ?_⟩).elim
    rcases hpos with hli | hfr
    · exact Or.inl (hind.mpr hli)
    · refine Or.inr ?_
      rw [hfin, hfr]
      have := Fintype.card_congr e'
      omega
  · obtain ⟨W, hWK, hWa, hfix, hyJ, hB, m, hm, f, hf⟩ := hA
    have hmem : W.toLin.simpleRefl W.a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) ⊔
        (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) := by
      have hsubℓ : ggAutomizer (real.component ℓ) Bs = ggAutomizer L Bs := by rw [hℓcomp]
      have hsubk : ggAutomizer (real.component k) Bs = ggAutomizer K Bs := by rw [hkcomp]
      rw [← hsubℓ, ← hsubk, real.normalizer_eq ℓ hℓadm, real.normalizer_eq k hkadm]
      exact hWa
    exact (hamb ⟨GGQ2Lin.toAmbModel (p := 3) (by norm_num) W.toLin real.coord hyBs hxBs
      (hKk W _ hWK) (mem_map_ggAutomizer_sup (p := 3) real.coord hmem) hfix hyJ, hB, m, hm, f,
      hf⟩).elim
  · exact hD5 hLB hP hrig hS hI1 hxL hnb real hxBs hyBs hℓadm hℓcomp hjadm hjcomp hkadm hkcomp h5

theorem ggQ2ExtCoverInput_of_placement (catalogue : FrameKind → RawFrameData)
    (hp : PlacementInput catalogue) (h : ∀ kind, GGQ2ExtCoverAtFrame (catalogue kind)) :
    GGQ2ExtCoverInput := by
  intro G _ _ p B Bs x L D J hS hp3 hI1 hxL _ y K hnb hrow hleaf hE6 hin hamb hdet
  obtain ⟨kind, hF⟩ := hp hS hp3
  exact h kind hS hp3 hI1 hxL hnb hF hrow hleaf hE6 hin hamb hdet

theorem ggQ2ExtCoverInput_of_cases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) (hN : ∀ R, ExtNbrBridge R) (hD5 : ∀ R, ExtD5Bridge R)
    (catalogue : FrameKind → RawFrameData) (hp : PlacementInput catalogue)
    (hc : ∀ kind, ExtCases (catalogue kind)) : GGQ2ExtCoverInput :=
  ggQ2ExtCoverInput_of_placement catalogue hp fun kind =>
    extCoverAtFrame_of_cases hLB hP hrig (hN _) (hD5 _) (hc kind)

end CFSG.StandardType.GGQ2Frame

end
