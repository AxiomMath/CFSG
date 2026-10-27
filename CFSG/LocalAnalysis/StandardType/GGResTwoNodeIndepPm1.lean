module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepWeyl
public import CFSG.LocalAnalysis.StandardType.GGRCScalarsPm1Two
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepChain
public import CFSG.LocalAnalysis.StandardType.GGTWAlign
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import TauCeti.GroupTheory.Coxeter.Matrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l6m_iso {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') : V ≃ₗ[ZMod p] V' :=
  LinearEquiv.ofBijective ((ι.symm.trans ι').toAddMonoidHom.toZModLinearMap p)
    (ι.symm.trans ι').bijective

private lemma l6m_iso_apply {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') (v : V) :
    l6m_iso (p := p) ι ι' v = ι' (ι.symm v) := rfl

private lemma l6m_conj {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') (a : MulAut ↥Bs) :
    ggLin (p := p) ι' a = ggLinConj (l6m_iso (p := p) ι ι') (ggLin (p := p) ι a) := by
  ext v
  have h1 : (l6m_iso (p := p) ι ι').symm v = ι (ι'.symm v) := by
    apply (l6m_iso (p := p) ι ι').injective
    rw [LinearEquiv.apply_symm_apply, l6m_iso_apply]
    simp
  change ggLin (p := p) ι' a v =
    l6m_iso (p := p) ι ι' (ggLin (p := p) ι a ((l6m_iso (p := p) ι ι').symm v))
  rw [h1, ggLin_apply, ggLin_apply, l6m_iso_apply]
  simp

private lemma l6m_conj_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (τ : V ≃ₗ[ZMod p] V')
    (g : V ≃ₗ[ZMod p] V) (v : V) : ggLinConj τ g (τ v) = τ (g v) := by
  change τ (g (τ.symm (τ v))) = τ (g v)
  rw [LinearEquiv.symm_apply_apply]

private lemma l6m_conj_apply_symm {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (τ : V ≃ₗ[ZMod p] V')
    (g : V ≃ₗ[ZMod p] V) (v : V') : τ.symm (ggLinConj τ g v) = g (τ.symm v) := by
  change τ.symm (τ (g (τ.symm v))) = g (τ.symm v)
  rw [LinearEquiv.symm_apply_apply]

private lemma l6m_absIrred {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (τ : V ≃ₗ[ZMod p] V')
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (h : ZS.AbsIrred p A) :
    ZS.AbsIrred p (A.map (ggLinConj τ).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · intro W' hW'
    have hW : ∀ a ∈ A, ∀ w ∈ W'.comap (τ : V →ₗ[ZMod p] V'),
        a w ∈ W'.comap (τ : V →ₗ[ZMod p] V') := by
      intro a ha w hw
      have hw' : τ w ∈ W' := hw
      have := hW' (ggLinConj τ a) ⟨a, ha, rfl⟩ (τ w) hw'
      rw [l6m_conj_apply] at this
      exact this
    rcases h.1 _ hW with h0 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      have : τ.symm w ∈ W'.comap (τ : V →ₗ[ZMod p] V') := by
        change τ (τ.symm w) ∈ W'
        rwa [LinearEquiv.apply_symm_apply]
      rw [h0] at this
      have h00 : τ.symm w = 0 := this
      have : w = 0 := by
        have := congrArg τ h00
        simpa using this
      simp [this]
    · right
      rw [eq_top_iff]
      intro w _
      have : τ.symm w ∈ W'.comap (τ : V →ₗ[ZMod p] V') := by rw [h1]; trivial
      have h2 : τ (τ.symm w) ∈ W' := this
      rwa [LinearEquiv.apply_symm_apply] at h2
  · intro S hS
    let S₀ : Module.End (ZMod p) V :=
      (τ.symm : V' →ₗ[ZMod p] V) ∘ₗ S ∘ₗ (τ : V →ₗ[ZMod p] V')
    have hS₀ : ∀ a ∈ A, S₀ ∘ₗ (a : V →ₗ[ZMod p] V) = (a : V →ₗ[ZMod p] V) ∘ₗ S₀ := by
      intro a ha
      have hc := hS (ggLinConj τ a) ⟨a, ha, rfl⟩
      apply LinearMap.ext
      intro v
      have h1 : S (ggLinConj τ a (τ v)) = ggLinConj τ a (S (τ v)) :=
        congrArg (fun T : Module.End (ZMod p) V' => T (τ v)) hc
      rw [l6m_conj_apply] at h1
      have h2 : τ.symm (S (τ (a v))) = a (τ.symm (S (τ v))) := by
        rw [h1, l6m_conj_apply_symm]
      exact h2
    obtain ⟨c, hc⟩ := h.2 S₀ hS₀
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro w
    have h1 : S₀ (τ.symm w) = c • τ.symm w := by rw [hc]; rfl
    have h3 : S₀ (τ.symm w) = τ.symm (S w) := by simp [S₀]
    have h2 : τ.symm (S w) = c • τ.symm w := by rw [← h3, h1]
    calc S w = τ (τ.symm (S w)) := by simp
      _ = τ (c • τ.symm w) := by rw [h2]
      _ = c • w := by simp

theorem ggIndep_pm1_transfer {p n : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') (A : Subgroup (MulAut ↥Bs))
    (h' : GGIndepPm1 p n ι' A) : GGIndepPm1 p n ι A := by
  intro hirr f hmon
  let τ : V ≃ₗ[ZMod p] V' := l6m_iso (p := p) ι ι'
  have hmap : A.map (ggLin (p := p) ι') =
      (A.map (ggLin (p := p) ι)).map (ggLinConj τ).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext a v
    exact congrArg (fun T : V' ≃ₗ[ZMod p] V' => T v) (l6m_conj (p := p) ι ι' a)
  have hirr' : ZS.AbsIrred p (A.map (ggLin (p := p) ι')) := by
    rw [hmap]
    exact l6m_absIrred τ _ hirr
  let f' : Module.Basis (Fin n) (ZMod p) V' := f.map τ
  have hmon' : ∀ a ∈ A.map (ggLin (p := p) ι'), ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f' i) = c i • f' (σ i) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨σ, c, hc0, hc⟩ := hmon (ggLin (p := p) ι a₀) ⟨a₀, ha₀, rfl⟩
    refine ⟨σ, c, hc0, fun i => ?_⟩
    have hf' : ∀ j, f' j = τ (f j) := fun j => by simp [f', Module.Basis.map_apply]
    rw [hf', hf', l6m_conj (p := p) ι ι' a₀, l6m_conj_apply, hc i, map_smul]
  obtain ⟨b'', hb''⟩ := h' hirr' f' hmon'
  refine ⟨b''.map τ.symm, fun a ha => ?_⟩
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨σ, c, hc1, hc⟩ := hb'' (ggLin (p := p) ι' a₀) ⟨a₀, ha₀, rfl⟩
  refine ⟨σ, c, hc1, fun i => ?_⟩
  have hb : ∀ j, (b''.map τ.symm) j = τ.symm (b'' j) := fun j => by simp [Module.Basis.map_apply]
  rw [hb, hb]
  have h2 := l6m_conj_apply_symm τ (ggLin (p := p) ι a₀) (b'' i)
  rw [← l6m_conj (p := p) ι ι' a₀] at h2
  rw [← h2, hc i, map_smul]

theorem ggIndep_bond_two_of_deleted_connected {n : ℕ} (hn : 4 ≤ n)
    {Λ : Type} (e : Fin n ≃ Λ) (b₁ b₂ : Λ) (hb : b₁ ≠ b₂)
    (hconn : GGDeletedConnected2 ((CoxeterMatrix.A n).reindex e) b₁ b₂) :
    ∃ j j' : Λ, j ≠ b₁ ∧ j ≠ b₂ ∧ j' ≠ b₁ ∧ j' ≠ b₂ ∧ j ≠ j' ∧
      ((CoxeterMatrix.A n).reindex e).M j j' = 3 := by
  obtain ⟨s, hs, hS⟩ := ggChainA_deleted_interval (by omega) e b₁ b₂ hb hconn
  let i : Fin n := ⟨s, by omega⟩
  let i' : Fin n := ⟨s + 1, by omega⟩
  have hi : e i ≠ b₁ ∧ e i ≠ b₂ := (hS i).2 ⟨by simp [i], by simp [i]; omega⟩
  have hi' : e i' ≠ b₁ ∧ e i' ≠ b₂ := (hS i').2 ⟨by simp [i'], by simp [i']; omega⟩
  refine ⟨e i, e i', hi.1, hi.2, hi'.1, hi'.2, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val (e.injective h)
    simp only [i, i'] at this
    omega
  · rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact TauCeti.coxeterMatrixA_eq_three (Or.inl (by simp [i, i']))

theorem ggIndep_pm1_join_of_deleted_connected (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hN : 5 ≤ N) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {X Y : Subgroup G}
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hYr : GGReflGenerated p (ggAutomizer Y Bs)) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    GGIndepPm1 p N ι (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V', i3, i4, ι', φX, hX, αX, hb, hWM, hC, hWMJ, hMJ,
    hlinX, hreflX, hpairX, hfX, hclosX, hfJ, hclosJ, hconj⟩ := hXs
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨fX, hfX⟩ := hfX
  obtain ⟨fJ, hfJ⟩ := hfJ
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁, hlin₁,
    hrefl₁, hpair₁, ⟨f₁, hf₁⟩, hclos₁⟩ := hXd
  letI := iΛ₁f; letI := iΛ₁d; letI := iV₁add; letI := iV₁mod
  have hn2 : 2 ≤ N - 1 := by omega
  obtain ⟨e₂, hM₂⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 hn2 hBs (ggAutomizer X Bs) e₁ hM₁ hWM₁ f₁ φ₁
      hf₁ hrefl₁ hWM fX φX hfX hreflX
  have hdel : GGDeletedConnected2 M b₁ b₂ := by
    intro j j'
    simpa only [hMJ] using ggRC_weyl_connected hWMJ j j'
  have hbond : ∃ j j' : Λ, j ≠ b₁ ∧ j ≠ b₂ ∧ j' ≠ b₁ ∧ j' ≠ b₂ ∧ j ≠ j' ∧ M.M j j' = 3 := by
    obtain ⟨j, j', hj1, hj2, hj'1, hj'2, hjne, hM3⟩ :=
      ggIndep_bond_two_of_deleted_connected (n := N - 1) (by omega) e₂ b₁ b₂ hb
        (hM₂ ▸ hdel)
    exact ⟨j, j', hj1, hj2, hj'1, hj'2, hjne, by rw [hM₂]; exact hM3⟩
  let Λa := {ψ : MulAut ↥Bs // ψ ∈ ggAutomizer Y Bs ∧ GGIsReflection p ψ}
  haveI : Finite V' := Finite.of_equiv (Additive ↥Bs) ι'.toEquiv
  have hex : ∀ a : Λa, ∃ (x : V') (f : Module.Dual (ZMod p) V'),
      f x = 2 ∧ ∀ w, ggLin (p := p) ι' a.1 w = w - f w • x :=
    fun a => exists_of_ggIsReflection (p := p) ι' a.2.2
  let φ : Λ ⊕ Λa → MulAut ↥Bs := Sum.elim φX (fun a => a.1)
  let h : Λ ⊕ Λa → V' := fun o => match o with
    | Sum.inl i => hX i
    | Sum.inr a => Classical.choose (hex a)
  let α : Λ ⊕ Λa → Module.Dual (ZMod p) V' := fun o => match o with
    | Sum.inl i => αX i
    | Sum.inr a => Classical.choose (Classical.choose_spec (hex a))
  have hφ : ∀ o w, ggLin (p := p) ι' (φ o) w = w - α o w • h o := by
    intro o w
    cases o with
    | inl i => exact hlinX i w
    | inr a => exact (Classical.choose_spec (Classical.choose_spec (hex a))).2 w
  have hrefl : ∀ o, GGIsReflection p (φ o) := by
    intro o
    cases o with
    | inl i => exact hreflX i
    | inr a => exact a.2.2
  have hL' : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (C i j : ZMod p) :=
    fun i j => hpairX i j
  have hJL' : J ≤ L := (hH.1.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  have hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs := by
    intro j
    have hj : φ (Sum.inl j) ∈ ggAutomizer J Bs := by
      rw [hclosJ]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    exact ggAutomizer_mono Bs hJL' hj
  have hφX : ∀ i : Λ, φ (Sum.inl i) ∈ ggAutomizer X Bs := by
    intro i
    rw [hclosX]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hφY : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer Y Bs := fun a => a.2.1
  have hXtop : ggAutomizer X Bs ≤ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top
  have hYtop : ggAutomizer Y Bs ≤ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top
  have hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs := by
    intro o
    cases o with
    | inl i => exact hXtop (hφX i)
    | inr a => exact hYtop (hφY a)
  have hgen : Subgroup.closure (Set.range φ) = ggAutomizer X Bs ⊔ ggAutomizer Y Bs := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | inl i => exact Subgroup.mem_sup_left (hφX i)
      | inr a => exact Subgroup.mem_sup_right (hφY a)
    · apply sup_le
      · rw [hclosX]
        apply Subgroup.closure_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · have hYr' : ggAutomizer Y Bs =
            Subgroup.closure {ψ | ψ ∈ ggAutomizer Y Bs ∧ GGIsReflection p ψ} := hYr
        rw [hYr', Subgroup.closure_le]
        rintro ψ ⟨hψA, hψrefl⟩
        exact Subgroup.subset_closure ⟨Sum.inr ⟨ψ, hψA, hψrefl⟩, rfl⟩
  have hA' : (ggAutomizer X Bs ⊔ ggAutomizer Y Bs).map (ggLin (p := p) ι') =
      Subgroup.closure (Set.range fun o => ggLin (p := p) ι' (φ o)) := by
    rw [← hgen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) := hclosJ
  have hP' : GGIndepPm1 p N ι' (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) := by
    intro hirr f hmon
    rw [hA'] at hirr hmon ⊢
    exact ggRC_scalars_pm1_two hJr hPump hLB hSP hp5 hH hC hbond hφ hrefl hL' hφtop hJL hJ
      (by omega) f hirr hmon
  exact ggIndep_pm1_transfer ι ι' _ hP'

theorem ggIndep_pm1_join (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hN : 7 ≤ N) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {X Y : Subgroup G}
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hYr : GGReflGenerated p (ggAutomizer Y Bs)) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    GGIndepPm1 p N ι (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) :=
  ggIndep_pm1_join_of_deleted_connected hJr hPump hLB hSP hp5 (by omega) hH hXd hXs hYr ι

end CFSG.StandardType

end
