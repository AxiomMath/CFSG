module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZXfer
public import CFSG.LocalAnalysis.StandardType.GGTWLowCloseOne
public import CFSG.LocalAnalysis.StandardType.GGTWLowCloseTwo
public import CFSG.LocalAnalysis.StandardType.GGTWLowLeafClose

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nLL_close_two {p N : ℕ} [Fact p.Prime] (hPZin : GGPZInput)
    (hp : 3 ≤ p) (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 9)
    {pos : GGTWPos} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV yV : V} (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 2)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hA2 : ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex eK) (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod p) V = N - 1) (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g)
    (hxa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hy0 : yV ≠ 0)
    (hyJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV)
    (hHK : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g yV = yV → GGHLLines (ggHLRoots
        (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
        (fun o => h (o.map Subtype.val id))) yV g)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hcardB : Nat.card ↥Bs = p ^ (N - 1))
    (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank) (hJrefl : GGReflGenerated p (ggAutomizer J Bs))
    (ι : Additive ↥Bs ≃+ V) (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range r)) (hAJ : (ggAutomizer J Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)))
    (xg yg : ↥Bs) (hxV : xV = ι (Additive.ofMul xg)) (hyV : yV = ι (Additive.ofMul yg))
    (hzD : ∀ c : ZMod p, (xg : G) * (yg : G) ^ c.val ∈ D)
    (hzx : ∀ c : ZMod p, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers x)
    (hzy : ∀ c : ZMod p, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers y)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : GGTWLowSurv2 p N Out ∨
      ∃ (θ : V ≃ₗ[ZMod p] GGTWE p N) (S : Set (Module.End (ZMod p) (GGTWE p N))), Out S ∧
          (∀ g ∈ Set.range r, ∃ y ∈ S,
            (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) ∧
          (∀ y ∈ S, ∃ g ∈ Set.range r,
            (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hN' : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hN with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨θ, a₁, a₂, c, c₂, ha1, αa1, ha2, αa2, lam, mu, news, rN,
    hθx, _ha1_def, _ha2_def, ha12, hpat, hpairs, hxne, hlam_mu_ne, hdoty1, hdoty2, hy_lam_mu,
    hnews, hrF, hrN, hrefl1, hrefl2, hsub, hnt', hHL', hrootsO, hkillF⟩ :=
    ggTWSurv2_cell (p := p) (N := N) (pos := pos) hp hpN hN' hb hcard hJpos hWMK hCK hA2 hr hF
      hdim hpairK hnt hHL hxa hy0 hyJ hya
  let rF : Fin (N - 1) → V ≃ₗ[ZMod p] V := fun i => r (Sum.inl (e i))
  have hmem : ∀ a : Λa, a = a₁ ∨ a = a₂ := by
    have hcard2 : ({a₁, a₂} : Finset Λa).card = Fintype.card Λa := by
      rw [Finset.card_pair ha12, ← Nat.card_eq_fintype_card, hcard]
    have htop : ({a₁, a₂} : Finset Λa) = Finset.univ := Finset.eq_univ_of_card _ hcard2
    intro a
    have : a ∈ ({a₁, a₂} : Finset Λa) := by rw [htop]; exact Finset.mem_univ a
    simpa using this
  have hcorr1 : ∀ g ∈ Set.range r, ∃ y ∈ ggTWGens p N news,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    rintro g ⟨o, rfl⟩
    cases o with
    | inl i =>
        refine ⟨ggTWRefl (ggTWh p N (e.symm i)) (ggTWα p N (e.symm i)), ?_, ?_⟩
        · rw [ggTWGens, ggTWFrameGens]
          exact Set.mem_union_left _ ⟨e.symm i, rfl⟩
        · apply LinearMap.ext
          intro v
          show r (Sum.inl i) v =
            θ.symm (ggTWRefl (ggTWh p N (e.symm i)) (ggTWα p N (e.symm i)) (θ v))
          have h := hrF (e.symm i) v
          rw [Equiv.apply_symm_apply] at h
          rw [← h, LinearEquiv.symm_apply_apply]
    | inr b =>
        rcases hmem b with hb1 | hb2
        · rw [hb1]
          refine ⟨ggTWRefl ha1 αa1, ?_, ?_⟩
          · rw [ggTWGens]
            exact Set.mem_union_right _ ⟨(ha1, αa1), by simp [hnews], rfl⟩
          · apply LinearMap.ext
            intro v
            show r (Sum.inr a₁) v = θ.symm (ggTWRefl ha1 αa1 (θ v))
            rw [← hrefl1 v, LinearEquiv.symm_apply_apply]
        · rw [hb2]
          refine ⟨ggTWRefl ha2 αa2, ?_, ?_⟩
          · rw [ggTWGens]
            exact Set.mem_union_right _ ⟨(ha2, αa2), by simp [hnews], rfl⟩
          · apply LinearMap.ext
            intro v
            show r (Sum.inr a₂) v = θ.symm (ggTWRefl ha2 αa2 (θ v))
            rw [← hrefl2 v, LinearEquiv.symm_apply_apply]
  have hcorr2 : ∀ y ∈ ggTWGens p N news, ∃ g ∈ Set.range r,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    intro y hy
    rw [ggTWGens, ggTWFrameGens] at hy
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := hy
      refine ⟨r (Sum.inl (e i)), ⟨Sum.inl (e i), rfl⟩, ?_⟩
      apply LinearMap.ext
      intro v
      show r (Sum.inl (e i)) v = θ.symm (ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
      rw [← hrF i v, LinearEquiv.symm_apply_apply]
    · obtain ⟨t, ht, rfl⟩ := hy
      rw [hnews] at ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · refine ⟨r (Sum.inr a₁), ⟨Sum.inr a₁, rfl⟩, ?_⟩
        apply LinearMap.ext
        intro v
        show r (Sum.inr a₁) v = θ.symm (ggTWRefl ha1 αa1 (θ v))
        rw [← hrefl1 v, LinearEquiv.symm_apply_apply]
      · refine ⟨r (Sum.inr a₂), ⟨Sum.inr a₂, rfl⟩, ?_⟩
        apply LinearMap.ext
        intro v
        show r (Sum.inr a₂) v = θ.symm (ggTWRefl ha2 αa2 (θ v))
        rw [← hrefl2 v, LinearEquiv.symm_apply_apply]
  have hJ₁ : ∀ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
      ∃ i : {i : Fin (N - 1) // ggTWInJ N pos i.val},
        (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ
          ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ θ.toLinearMap := by
    rintro g ⟨j, rfl⟩
    let i : {i : Fin (N - 1) // ggTWInJ N pos i.val} :=
      ⟨e.symm j.1, (hJpos (e.symm j.1)).mpr (by
        rw [Equiv.apply_symm_apply]; exact j.2)⟩
    refine ⟨i, ?_⟩
    apply LinearMap.ext
    intro v
    have h := hrF i.1 v
    have hi1 : e i.1 = j.1 := Equiv.apply_symm_apply e j.1
    rw [hi1] at h
    change r (Sum.inl j.1) v = θ.symm (ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) (θ v))
    rw [← h, LinearEquiv.symm_apply_apply]
  have hJ₂ : ∀ i : {i : Fin (N - 1) // ggTWInJ N pos i.val},
      ∃ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
        (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ
          ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ θ.toLinearMap := by
    intro i
    refine ⟨r (Sum.inl (e i.1)), ⟨⟨e i.1, (hJpos i.1).mp i.2⟩, rfl⟩, ?_⟩
    apply LinearMap.ext
    intro v
    have h := hrF i.1 v
    change r (Sum.inl (e i.1)) v = θ.symm (ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) (θ v))
    rw [← h, LinearEquiv.symm_apply_apply]
  have hHK' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
          (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
          (fun t : ↥news => θ.symm t.1.1))) yV g := by
    intro g hg hrefl hgy
    rw [hrootsO]
    exact hHK g (hsub hg) hrefl hgy
  have hkillO : ¬ GGTWKill .other p N pos news
      (lam • ggTWx p N + mu • ggTWz p N pos) := by
    have h := ggTW_notKill_other (p := p) (N := N) hp2 θ rF hrF news rN hrN hnt'
      pos hHK'
    simpa [hy_lam_mu] using h
  have hPZall := ggTWLowLeaf_pz_at hPZin hp2 hH hX hJΛ hXΛ hJl hXl hrow hAtag hXrank hJrank
    hcardB hJcard hJrefl ι θ pos (Set.range r)
    (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) hA hAJ
    (ggTWGens p N news) hcorr1 hcorr2 hJ₁ hJ₂ xg yg hxV hyV hzD hzx hzy
  have hPZclause : ∀ c' : ZMod p, c' ≠ 0 → ¬ GGTWPZBad p N pos (ggTWGens p N news)
      (ggTWx p N + c' • (lam • ggTWx p N + mu • ggTWz p N pos)) := by
    intro c' hc'
    simpa only [map_add, map_smul, hθx, hy_lam_mu] using hPZall c' hc'
  by_cases hOut : Out (ggTWGens p N news)
  · right
    exact ⟨θ, ggTWGens p N news, hOut, hcorr1, hcorr2⟩
  · left
    refine ⟨pos, c, c₂, ha1, αa1, ha2, αa2, lam, mu, hpat, hpairs, hxne, hlam_mu_ne, hdoty1,
      hdoty2, ?_, ?_, ?_, ?_⟩
    · simpa [hnews] using hkillF
    · simpa [hnews] using hkillO
    · intro c' hc'
      simpa only [hnews] using hPZclause c' hc'
    · simpa [hnews] using hOut


theorem ggTWLow_leaf (hPZ : GGPZInput) {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime]
    (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p) (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 9)
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hXΛ : LargeEvenInLambda2 labX) (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hCard : Nat.card ↥Bs = p ^ (N - 1))
    (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) (hcells : GGTWLowCells p N Out)
    (hOut : ∀ {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      {A : Subgroup (MulAut ↥Bs)} (θ : V ≃ₗ[ZMod p] GGTWE p N) (gens : Set (V ≃ₗ[ZMod p] V)),
      A.map (ggLin (p := p) ι) = Subgroup.closure gens →
      ∀ S : Set (Module.End (ZMod p) (GGTWE p N)), Out S →
        (∀ g ∈ gens, ∃ y ∈ S,
          (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) →
        (∀ y ∈ S, ∃ g ∈ gens,
          (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) →
        GGWeylReflectionGroup p A)
    (hcfg : (X = L ∧ GGTWLowCfg p N k Bs L J K x y) ∨ (X = K ∧ GGTWLowCfg p N k Bs K J L y x)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hDcl : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hDea : IsElemAbelian p D := hH.1.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hy_not_zx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_zpowers x
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact hy
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ p := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 x hxD))
    have : p ^ 2 ≤ p := by simpa [hDcard] using h1
    nlinarith [(Fact.out : p.Prime).two_le]
  have hx_not_zy : x ∉ Subgroup.zpowers y := by
    intro hx
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers y := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact hx
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact Subgroup.mem_zpowers y
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ p := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 y hyD))
    have : p ^ 2 ≤ p := by simpa [hDcard] using h1
    nlinarith [(Fact.out : p.Prime).two_le]
  have hx_ne1 : x ≠ 1 := by
    intro hx1
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers y := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz, hx1]; exact Subgroup.one_mem _
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact Subgroup.mem_zpowers y
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ p := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 y hyD))
    have : p ^ 2 ≤ p := by simpa [hDcard] using h1
    nlinarith [(Fact.out : p.Prime).two_le]
  have hy_ne1 : y ≠ 1 := by
    intro hy1
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_zpowers x
        · simp only [Set.mem_singleton_iff] at hz; rw [hz, hy1]; exact Subgroup.one_mem _
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ p := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 x hxD))
    have : p ^ 2 ≤ p := by simpa [hDcard] using h1
    nlinarith [(Fact.out : p.Prime).two_le]
  have hxord : orderOf x = p := orderOf_eq_prime (hDea.2 x hxD) hx_ne1
  have hyord : orderOf y = p := orderOf_eq_prime (hDea.2 y hyD) hy_ne1
  have hpow_x : ∀ c : ZMod p, c ≠ 0 → x ^ c.val ∉ Subgroup.zpowers y :=
    ggTWLowLeaf_pow_not_zpowers hy_not_zx hxord hyord
  have hpow_y : ∀ c : ZMod p, c ≠ 0 → y ^ c.val ∉ Subgroup.zpowers x :=
    ggTWLowLeaf_pow_not_zpowers hx_not_zy hyord hxord
  have hzDxy : ∀ c : ZMod p, x * y ^ c.val ∈ D := by
    intro c; rw [hDcl]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hzDyx : ∀ c : ZMod p, y * x ^ c.val ∈ D := by
    intro c; rw [hDcl]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hzx_xy : ∀ c : ZMod p, c ≠ 0 → x * y ^ c.val ∉ Subgroup.zpowers x := by
    intro c hc hmem
    apply hpow_y c hc
    have h : x⁻¹ * (x * y ^ c.val) ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) hmem
    simpa [mul_assoc] using h
  have hzy_xy : ∀ c : ZMod p, c ≠ 0 → x * y ^ c.val ∉ Subgroup.zpowers y := by
    intro c hc hmem
    apply hx_not_zy
    have h : (x * y ^ c.val) * (y ^ c.val)⁻¹ ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
    simpa [mul_assoc] using h
  have hzx_yx : ∀ c : ZMod p, c ≠ 0 → y * x ^ c.val ∉ Subgroup.zpowers x := by
    intro c hc hmem
    apply hy_not_zx
    have h : (y * x ^ c.val) * (x ^ c.val)⁻¹ ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
    simpa [mul_assoc] using h
  have hzy_yx : ∀ c : ZMod p, c ≠ 0 → y * x ^ c.val ∉ Subgroup.zpowers y := by
    intro c hc hmem
    apply hpow_x c hc
    have h : y⁻¹ * (y * x ^ c.val) ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) hmem
    simpa [mul_assoc] using h
  rcases hcfg with ⟨hXL, hcfg⟩ | ⟨hXK, hcfg⟩
  · obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α,
      xV, yV, hx, hy, hxV, hyV, hcore, hdim, hHL, hyVne, hyJ, hya, hHK⟩ := hcfg
    letI := iΛ1; letI := iΛ2; letI := iΛa1; letI := iΛa2; letI := iV1; letI := iV2
    obtain ⟨hb, hcardk, hJpos, hWMK, hCK, hk2, hφlin, hF, hpairK, hnt, hxa, hgenA, hgenJ⟩ := hcore
    let r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V := fun o => ggLin (p := p) ι (φ o)
    have hr : ∀ o w, r o w = w - α o w • h o := fun o w => hφlin o w
    have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
        Subgroup.closure (Set.range r) := by
      have hrg : Set.range r = (ggLin (p := p) ι) '' Set.range φ := by
        ext u; constructor
        · rintro ⟨o, rfl⟩; exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
      rw [hgenA, MonoidHom.map_closure, ← hrg]
    have hAJ : (ggAutomizer J Bs).map (ggLin (p := p) ι) = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) := by
      have hrgJ : Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) =
          (ggLin (p := p) ι) '' Set.range
            (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) := by
        ext u; constructor
        · rintro ⟨j, rfl⟩; exact ⟨φ (Sum.inl j.1), ⟨j, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
      rw [hgenJ, MonoidHom.map_closure, ← hrgJ]
    have hJrefl := ggTWLowLeaf_reflGenerated ι φ h α hCK hp2 hφlin hpairK hgenJ
    rcases hk with rfl | rfl
    · have hres := ggTWLowLeaf_close_one hPZ hp hpN hN hb hcardk hJpos hWMK hCK hr hF hdim
        hpairK hnt hHL hxa hyVne hyJ hya hHK hH (Or.inl hXL) hJΛ hXΛ hJl hXl hrow hAtag hXrank
        hJrank hCard hJcard hJrefl ι hA hAJ ⟨x, hx⟩ ⟨y, hy⟩ hxV hyV hzDxy hzx_xy hzy_xy Out
      rcases hres with hsurv | ⟨θ, S, hOutS, hc1, hc2⟩
      · exact absurd hsurv hcells.1
      · exact hOut ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) θ (Set.range r) hA S hOutS hc1 hc2
    · have hres := l05nLL_close_two hPZ hp hpN hN hb hcardk hJpos hWMK hCK (hk2 rfl) hr hF hdim
        hpairK hnt hHL hxa hyVne hyJ hya hHK hH (Or.inl hXL) hJΛ hXΛ hJl hXl hrow hAtag hXrank
        hJrank hCard hJcard hJrefl ι hA hAJ ⟨x, hx⟩ ⟨y, hy⟩ hxV hyV hzDxy hzx_xy hzy_xy Out
      rcases hres with hsurv | ⟨θ, S, hOutS, hc1, hc2⟩
      · exact absurd hsurv hcells.2
      · exact hOut ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) θ (Set.range r) hA S hOutS hc1 hc2
  · obtain ⟨pos, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α,
      xV, yV, hy, hx, hyV, hxV, hcore, hdim, hHL, hyVne, hyJ, hya, hHK⟩ := hcfg
    letI := iΛ1; letI := iΛ2; letI := iΛa1; letI := iΛa2; letI := iV1; letI := iV2
    obtain ⟨hb, hcardk, hJpos, hWMK, hCK, hk2, hφlin, hF, hpairK, hnt, hxa, hgenA, hgenJ⟩ := hcore
    let r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V := fun o => ggLin (p := p) ι (φ o)
    have hr : ∀ o w, r o w = w - α o w • h o := fun o w => hφlin o w
    have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
        Subgroup.closure (Set.range r) := by
      have hrg : Set.range r = (ggLin (p := p) ι) '' Set.range φ := by
        ext u; constructor
        · rintro ⟨o, rfl⟩; exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
      rw [sup_comm (ggAutomizer L Bs) (ggAutomizer K Bs), hgenA, MonoidHom.map_closure, ← hrg]
    have hAJ : (ggAutomizer J Bs).map (ggLin (p := p) ι) = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) := by
      have hrgJ : Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) =
          (ggLin (p := p) ι) '' Set.range
            (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) := by
        ext u; constructor
        · rintro ⟨j, rfl⟩; exact ⟨φ (Sum.inl j.1), ⟨j, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
      rw [hgenJ, MonoidHom.map_closure, ← hrgJ]
    have hJrefl := ggTWLowLeaf_reflGenerated ι φ h α hCK hp2 hφlin hpairK hgenJ
    rcases hk with rfl | rfl
    · have hres := ggTWLowLeaf_close_one hPZ hp hpN hN hb hcardk hJpos hWMK hCK hr hF hdim
        hpairK hnt hHL hxa hyVne hyJ hya hHK hH (Or.inr hXK) hJΛ hXΛ hJl hXl hrow hAtag hXrank
        hJrank hCard hJcard hJrefl ι hA hAJ ⟨y, hy⟩ ⟨x, hx⟩ hyV hxV hzDyx hzx_yx hzy_yx Out
      rcases hres with hsurv | ⟨θ, S, hOutS, hc1, hc2⟩
      · exact absurd hsurv hcells.1
      · exact hOut ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) θ (Set.range r) hA S hOutS hc1 hc2
    · have hres := l05nLL_close_two hPZ hp hpN hN hb hcardk hJpos hWMK hCK (hk2 rfl) hr hF hdim
        hpairK hnt hHL hxa hyVne hyJ hya hHK hH (Or.inr hXK) hJΛ hXΛ hJl hXl hrow hAtag hXrank
        hJrank hCard hJcard hJrefl ι hA hAJ ⟨y, hy⟩ ⟨x, hx⟩ hyV hxV hzDyx hzx_yx hzy_yx Out
      rcases hres with hsurv | ⟨θ, S, hOutS, hc1, hc2⟩
      · exact absurd hsurv hcells.2
      · exact hOut ι (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) θ (Set.range r) hA S hOutS hc1 hc2

end CFSG.StandardType

end
