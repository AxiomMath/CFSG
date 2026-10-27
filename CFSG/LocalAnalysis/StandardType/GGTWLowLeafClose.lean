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

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggTWLowLeaf_pow_not_zpowers {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {w z : G} (hwz : w ∉ Subgroup.zpowers z) (hzord : orderOf z = p) (hword : orderOf w = p) :
    ∀ c : ZMod p, c ≠ 0 → z ^ c.val ∉ Subgroup.zpowers w := by
  intro c hc hmem
  have hc0 : c.val ≠ 0 := (ZMod.val_ne_zero c).mpr hc
  have hclt : c.val < p := ZMod.val_lt c
  have hzc1 : z ^ c.val ≠ 1 := by
    intro h1
    have hdvd : orderOf z ∣ c.val := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hzord] at hdvd
    have hle : p ≤ c.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hdvd
    omega
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hord : orderOf (z ^ c.val) = p :=
    orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]) hzc1
  have hzeq : Subgroup.zpowers (z ^ c.val) = Subgroup.zpowers w := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hmem
    · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hword]
  have hzc_mem_z : z ^ c.val ∈ Subgroup.zpowers z :=
    Subgroup.pow_mem _ (Subgroup.mem_zpowers z) c.val
  have hw_zc : w ∈ Subgroup.zpowers (z ^ c.val) := by
    rw [hzeq]; exact Subgroup.mem_zpowers w
  exact hwz ((Subgroup.zpowers_le.mpr hzc_mem_z) hw_zc)

theorem ggTWLowLeaf_pz_at (hPZin : GGPZInput) {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hcard : Nat.card ↥Bs = p ^ (N - 1))
    (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank) (hJrefl : GGReflGenerated p (ggAutomizer J Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (pos : GGTWPos) (gensV gensJV : Set (V ≃ₗ[ZMod p] V))
    (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) = Subgroup.closure gensV)
    (hAJ : (ggAutomizer J Bs).map (ggLin (p := p) ι) = Subgroup.closure gensJV)
    (gens : Set (Module.End (ZMod p) (GGTWE p N))) (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV, (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin (N - 1) // ggTWInJ N pos i.val},
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ
        θ.toLinearMap) (hJ₂ : ∀ i : {i : Fin (N - 1) // ggTWInJ N pos i.val}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ
        θ.toLinearMap) {xV yV : V} (xg yg : ↥Bs) (hxV : xV = ι (Additive.ofMul xg))
    (hyV : yV = ι (Additive.ofMul yg)) (hzD : ∀ c : ZMod p, (xg : G) * (yg : G) ^ c.val ∈ D)
    (hzx : ∀ c : ZMod p, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers x)
    (hzy : ∀ c : ZMod p, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers y) :
    ∀ c : ZMod p, c ≠ 0 → ¬ GGTWPZBad p N pos gens (θ (xV + c • yV)) := by
  intro c hc
  have hzBs : (xg : G) * (yg : G) ^ c.val ∈ Bs := Bs.mul_mem xg.2 (Bs.pow_mem yg.2 _)
  have hzsub : (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs) = xg * yg ^ c.val := Subtype.ext rfl
  have hzval : ι (Additive.ofMul (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs)) = xV + c • yV := by
    rw [hxV, hyV, hzsub, ofMul_mul, ofMul_pow, map_add, map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val (ι (Additive.ofMul yg)), ZMod.natCast_zmod_val c]
  have h := ggTWPZ_xfer hPZin hp2 hH hX hJΛ hXΛ hJl hXl hrow hAtag hXrank hJrank hcard hJcard
    hJrefl ι θ pos gensV gensJV hA hAJ gens hg₁ hg₂ hJ₁ hJ₂
    (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs) (hzD c) (hzx c hc) (hzy c hc)
  rwa [hzval] at h

theorem ggTWLowLeaf_reflGenerated {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type}
    [Fintype Λa] [DecidableEq Λa] {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hCK : GGIntCartan MK CK) (hp2 : p ≠ 2)
    (hφlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hgenJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))) :
    GGReflGenerated p (ggAutomizer J Bs) := by
  have hrefl : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, GGIsReflection p (φ (Sum.inl j.1)) := by
    intro j
    have hfx : α (Sum.inl j.1) (h (Sum.inl j.1)) = 2 := by
      have h1 := hpair (Sum.inl j) (Sum.inl j)
      simp only [Sum.map_inl, id_eq] at h1
      rw [h1, hCK.1 (Sum.inl j)]
      norm_num
    exact ggIsReflection_of_eq_reflection hp2 ι hfx
      (ggLin_eq_reflection ι hfx (hφlin (Sum.inl j.1)))
  unfold GGReflGenerated
  rw [hgenJ]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨j, rfl⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨j, rfl⟩, hrefl j⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨hxA, _⟩
    exact hxA

theorem ggTWLowLeaf_close_one {p N : ℕ} [Fact p.Prime] (hPZin : GGPZInput)
    (hp : 3 ≤ p) (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 9)
    {pos : GGTWPos} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV yV : V} (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 1)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK) (hr : ∀ o w, r o w = w - α o w • h o)
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
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : GGTWLowSurv1 p N Out ∨
      ∃ (θ : V ≃ₗ[ZMod p] GGTWE p N) (S : Set (Module.End (ZMod p) (GGTWE p N))), Out S ∧
          (∀ g ∈ Set.range r, ∃ y ∈ S,
            (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) ∧
          (∀ y ∈ S, ∃ g ∈ Set.range r,
            (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap) := by
  classical
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hp2 : p ≠ 2 := by omega
  have hN' : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hN with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨θ, a, c0, m, n, ha, αa, lam, mu, news, rN, hθx, _hθh, _hθα, _hha_eq, hpat, hpairs,
    hha, hxne, hlam_mu_ne, hdoty, hy_lam_mu, hnews, hrF, hrN, hrNr_eq, hsub, hnt', hHL',
    hrootsO⟩ :=
    ggTWSurv1_cell (p := p) (N := N) (pos := pos) hp hpN hN' hb hcard hJpos hWMK hCK hr hF hdim
      hpairK hnt hHL hxa hy0 hyJ hya
  let rF : Fin (N - 1) → V ≃ₗ[ZMod p] V := fun i => r (Sum.inl (e i))
  have hmem_news : (ha, αa) ∈ news := by simp [hnews]
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
        refine ⟨ggTWRefl ha αa, ?_, ?_⟩
        · rw [ggTWGens]
          exact Set.mem_union_right _ ⟨(ha, αa), hmem_news, rfl⟩
        · apply LinearMap.ext
          intro v
          show r (Sum.inr b) v = θ.symm (ggTWRefl ha αa (θ v))
          have hb : b = a := Subsingleton.elim b a
          rw [hb]
          have h := hrN (ha, αa) hmem_news v
          rw [hrNr_eq] at h
          rw [← h, LinearEquiv.symm_apply_apply]
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
      have ht' : t = (ha, αa) := by
        rw [hnews] at ht
        exact Set.mem_singleton_iff.mp ht
      subst ht'
      refine ⟨r (Sum.inr a), ⟨Sum.inr a, rfl⟩, ?_⟩
      apply LinearMap.ext
      intro v
      show r (Sum.inr a) v = θ.symm (ggTWRefl ha αa (θ v))
      have h := hrN (ha, αa) hmem_news v
      rw [hrNr_eq] at h
      rw [← h, LinearEquiv.symm_apply_apply]
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
  have hkillF : ¬ GGTWKill .frame p N pos news
      (lam • ggTWx p N + mu • ggTWz p N pos) :=
    ggTW_notKill_frame (p := p) (N := N) hp2 θ hθx rF hrF news rN hrN hnt' hHL'
      pos (lam • ggTWx p N + mu • ggTWz p N pos)
  have hHK' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
          (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
          (fun t : ↥news => θ.symm t.1.1))) yV g := by
    intro g hg hrefl hgy
    rw [hrootsO]
    exact hHK g (Subgroup.closure_mono hsub hg) hrefl hgy
  have hkillO : ¬ GGTWKill .other p N pos news
      (lam • ggTWx p N + mu • ggTWz p N pos) := by
    have h := ggTW_notKill_other (p := p) (N := N) hp2 θ rF hrF news rN hrN hnt'
      pos hHK'
    simpa [hy_lam_mu] using h
  have hPZall := ggTWLowLeaf_pz_at hPZin hp2 hH hX hJΛ hXΛ hJl hXl hrow hAtag hXrank hJrank
    hcardB hJcard hJrefl ι θ pos (Set.range r)
    (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) hA hAJ
    (ggTWGens p N news) hcorr1 hcorr2 hJ₁ hJ₂ xg yg hxV hyV hzD hzx hzy
  have hPZclause : ∀ c : ZMod p, c ≠ 0 → ¬ GGTWPZBad p N pos (ggTWGens p N news)
      (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos)) := by
    intro c hc
    simpa only [map_add, map_smul, hθx, hy_lam_mu] using hPZall c hc
  by_cases hOut : Out (ggTWGens p N news)
  · right
    exact ⟨θ, ggTWGens p N news, hOut, hcorr1, hcorr2⟩
  · left
    refine ⟨pos, c0, m, n, ha, αa, lam, mu, hpat, hpairs, hha, hxne, hlam_mu_ne, hdoty, ?_, ?_,
      ?_, ?_⟩
    · simpa [hnews] using hkillF
    · simpa [hnews] using hkillO
    · intro c hc
      simpa only [hnews] using hPZclause c hc
    · simpa [hnews] using hOut

end CFSG.StandardType

end
