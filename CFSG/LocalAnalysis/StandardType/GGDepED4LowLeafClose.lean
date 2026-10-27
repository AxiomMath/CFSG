module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowCloseV
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowPZ
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowSurvOne
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowSurvTwo
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowKillFrame
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowKillOther
public import CFSG.LocalAnalysis.StandardType.GGTWLowLeafClose

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepELLeaf_close_one (hPZin : GGPZE6Input)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin 6 ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V} {xV yV : V}
    (hb1 : b₁ = e 0) (hb2 : b₂ = e 5) (hcard : Nat.card Λa = 1)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepEFrame 3 (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g)
    (hxa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hy0 : yV ≠ 0)
    (hyJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV)
    (hHK : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
        (fun o => h (o.map Subtype.val id))) yV g)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall 3 labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hcardB : Nat.card ↥Bs = 3 ^ 6)
    (hJcard : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank) (hJrefl : GGReflGenerated 3 (ggAutomizer J Bs))
    (ι : Additive ↥Bs ≃+ V)
    (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range r))
    (hAJ : (ggAutomizer J Bs).map (ggLin (p := 3) ι) = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)))
    (xg yg : ↥Bs) (hxV : xV = ι (Additive.ofMul xg)) (hyV : yV = ι (Additive.ofMul yg))
    (hzD : ∀ c : ZMod 3, (xg : G) * (yg : G) ^ c.val ∈ D)
    (hzx : ∀ c : ZMod 3, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers x)
    (hzy : ∀ c : ZMod 3, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers y) :
    GGDepED4LowSurv1 := by
  classical
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨θ, a, c0, ha, αa, lam, mu, news, rN, hθx, _hθh, _hθα, _hha_eq, hpat, hpairs, hha,
    hxne, hlam_mu_ne, hdoty, hy_lam_mu, hnews, hrF, hrN, hrNr_eq, hsub, hnt', hHL',
    hrootsO⟩ :=
    ggDepELSurv1_cell hb1 hb2 hcard hWMK hCK hr hF hdim hpairK hnt hHL hxa hy0 hyJ hya
  let rF : Fin 6 → V ≃ₗ[ZMod 3] V := fun i => r (Sum.inl (e i))
  have hmem_news : (ha, αa) ∈ news := by rw [hnews]; simp
  have hcorr1 : ∀ g ∈ Set.range r, ∃ y ∈ ggDepELGens news,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    rintro g ⟨o, rfl⟩
    cases o with
    | inl i =>
        refine ⟨ggDepELrefl (e.symm i), ?_, ?_⟩
        · rw [ggDepELGens, ggDepELFrameGens]
          exact Set.mem_union_left _ ⟨e.symm i, rfl⟩
        · apply LinearMap.ext
          intro v
          show r (Sum.inl i) v = θ.symm
            (ggDepARefl (ggDepELh (e.symm i)) (ggDepELα (e.symm i)) (θ v))
          have h := hrF (e.symm i) v
          rw [Equiv.apply_symm_apply] at h
          rw [← h, LinearEquiv.symm_apply_apply]
    | inr b =>
        refine ⟨ggDepARefl ha αa, ?_, ?_⟩
        · rw [ggDepELGens]
          exact Set.mem_union_right _ ⟨(ha, αa), hmem_news, rfl⟩
        · apply LinearMap.ext
          intro v
          show r (Sum.inr b) v = θ.symm (ggDepARefl ha αa (θ v))
          have hb : b = a := Subsingleton.elim b a
          rw [hb]
          have h := hrN (ha, αa) hmem_news v
          rw [hrNr_eq] at h
          rw [← h, LinearEquiv.symm_apply_apply]
  have hcorr2 : ∀ y ∈ ggDepELGens news, ∃ g ∈ Set.range r,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    intro y hy
    rw [ggDepELGens, ggDepELFrameGens] at hy
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := hy
      refine ⟨r (Sum.inl (e i)), ⟨Sum.inl (e i), rfl⟩, ?_⟩
      apply LinearMap.ext
      intro v
      show r (Sum.inl (e i)) v = θ.symm
        (ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
      rw [← hrF i v, LinearEquiv.symm_apply_apply]
    · obtain ⟨t, ht, rfl⟩ := hy
      have ht' : t = (ha, αa) := by rw [hnews] at ht; exact Set.mem_singleton_iff.mp ht
      subst ht'
      refine ⟨r (Sum.inr a), ⟨Sum.inr a, rfl⟩, ?_⟩
      apply LinearMap.ext
      intro v
      show r (Sum.inr a) v = θ.symm (ggDepARefl ha αa (θ v))
      have h := hrN (ha, αa) hmem_news v
      rw [hrNr_eq] at h
      rw [← h, LinearEquiv.symm_apply_apply]
  have hJ₁ : ∀ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
      ∃ i : {i : Fin 6 // GGDepED4In i},
        (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ
          ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ θ.toLinearMap := by
    rintro g ⟨j, rfl⟩
    let i : {i : Fin 6 // GGDepED4In i} :=
      ⟨e.symm j.1, ⟨fun h0 => j.2.1 (by
          have := congrArg e h0
          simpa [hb1] using this),
        fun h5 => j.2.2 (by
          have := congrArg e h5
          simpa [hb2] using this)⟩⟩
    refine ⟨i, ?_⟩
    apply LinearMap.ext
    intro v
    have h := hrF i.1 v
    have hi1 : e i.1 = j.1 := Equiv.apply_symm_apply e j.1
    rw [hi1] at h
    change r (Sum.inl j.1) v = θ.symm (ggDepARefl (ggDepELh i.1) (ggDepELα i.1) (θ v))
    rw [← h, LinearEquiv.symm_apply_apply]
  have hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i},
      ∃ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
        (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ
          ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ θ.toLinearMap := by
    intro i
    refine ⟨r (Sum.inl (e i.1)), ⟨⟨e i.1, ?_⟩, rfl⟩, ?_⟩
    · exact ⟨fun h => i.2.1 (e.injective (h.trans hb1)),
        fun h => i.2.2 (e.injective (h.trans hb2))⟩
    · apply LinearMap.ext
      intro v
      have h := hrF i.1 v
      change r (Sum.inl (e i.1)) v =
        θ.symm (ggDepARefl (ggDepELh i.1) (ggDepELα i.1) (θ v))
      rw [← h, LinearEquiv.symm_apply_apply]
  have hkillF : ¬ GGDepELKill .frame news (lam • ggDepELx + mu • ggDepELz) :=
    ggDepEL_notKill_frame θ hθx rF hrF news rN hrN hnt' hHL'
      (lam • ggDepELx + mu • ggDepELz)
  have hHK' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1) (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
          (fun t : ↥news => θ.symm t.1.1))) yV g := by
    intro g hg hrefl hgy
    rw [hrootsO]
    exact hHK g (Subgroup.closure_mono hsub hg) hrefl hgy
  have hkillO : ¬ GGDepELKill .other news (lam • ggDepELx + mu • ggDepELz) := by
    have h := ggDepEL_notKill_other θ rF hrF news rN hrN hnt' hHK'
    simpa [hy_lam_mu] using h
  have hPZclause : ∀ c : ZMod 3, c ≠ 0 → ¬ GGDepELPZBad (ggDepELGens news)
      (ggDepELx + c • (lam • ggDepELx + mu • ggDepELz)) := by
    intro c hc
    have hzBs : (xg : G) * (yg : G) ^ c.val ∈ Bs := Bs.mul_mem xg.2 (Bs.pow_mem yg.2 _)
    have hzsub : (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs) = xg * yg ^ c.val :=
      Subtype.ext rfl
    have hzval : ι (Additive.ofMul (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs)) =
        xV + c • yV := by
      rw [hxV, hyV, hzsub, ofMul_mul, ofMul_pow, map_add, map_nsmul]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c.val (ι (Additive.ofMul yg)),
        ZMod.natCast_zmod_val c]
    have h := ggDepELPZ_xfer hPZin hH hX hJΛ hXΛ hJl hXl hrow htag hcardB hJcard hJrefl ι θ
      (Set.range r) (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1))
      hA hAJ (ggDepELGens news) hcorr1 hcorr2 hJ₁ hJ₂
      (⟨(xg : G) * (yg : G) ^ c.val, hzBs⟩ : ↥Bs) (hzD c) (hzx c hc) (hzy c hc)
    rw [hzval] at h
    simpa only [map_add, map_smul, hθx, hy_lam_mu] using h
  refine ⟨c0, ha, αa, lam, mu, hpat, hpairs, hha, hxne, hlam_mu_ne, hdoty, ?_, ?_, ?_⟩
  · simpa [hnews] using hkillF
  · simpa [hnews] using hkillO
  · intro c hc
    simpa only [hnews] using hPZclause c hc

theorem ggDepELLeaf_close_two (hPZin : GGPZE6Input)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin 6 ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V} {xV yV : V}
    (hb1 : b₁ = e 0) (hb2 : b₂ = e 5) (hcard : Nat.card Λa = 2)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hA2 : ∃ eK : Fin 6 ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa), MK = CoxeterMatrix.E₆.reindex eK)
    (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepEFrame 3 (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hxa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hy0 : yV ≠ 0)
    (hyJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall 3 labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hcardB : Nat.card ↥Bs = 3 ^ 6)
    (hJcard : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank) (hJrefl : GGReflGenerated 3 (ggAutomizer J Bs))
    (ι : Additive ↥Bs ≃+ V)
    (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range r))
    (hAJ : (ggAutomizer J Bs).map (ggLin (p := 3) ι) = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)))
    (xg yg : ↥Bs) (hxV : xV = ι (Additive.ofMul xg)) (hyV : yV = ι (Additive.ofMul yg))
    (hzD : ∀ c : ZMod 3, (xg : G) * (yg : G) ^ c.val ∈ D)
    (hzx : ∀ c : ZMod 3, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers x)
    (hzy : ∀ c : ZMod 3, c ≠ 0 → (xg : G) * (yg : G) ^ c.val ∉ Subgroup.zpowers y) :
    GGDepED4LowSurv2 := by
  classical
  obtain ⟨θ, a₁, a₂, c, c', ha1, αa1, ha2, αa2, lam, mu, news, rN,
    hθx, _ha1_eq, _ha2_eq, ha12, hpat, hpat', hcne, hpairs, hxne, hlam_mu_ne, hdoty1,
    hdoty2, hy_lam_mu, hnews, hrF, hrN, hrefl1, hrefl2, _hsub, hnt'⟩ :=
    ggDepELSurv2_cell hb1 hb2 hcard hWMK hCK hA2 hr hF hdim hpairK hnt hxa hy0 hyJ hya
  let rF : Fin 6 → V ≃ₗ[ZMod 3] V := fun i => r (Sum.inl (e i))
  have hmem : ∀ a : Λa, a = a₁ ∨ a = a₂ := by
    have hcard2 : ({a₁, a₂} : Finset Λa).card = Fintype.card Λa := by
      rw [Finset.card_pair ha12, ← Nat.card_eq_fintype_card, hcard]
    have htop : ({a₁, a₂} : Finset Λa) = Finset.univ := Finset.eq_univ_of_card _ hcard2
    intro a
    have : a ∈ ({a₁, a₂} : Finset Λa) := by rw [htop]; exact Finset.mem_univ a
    simpa using this
  have hcorr1 : ∀ g ∈ Set.range r, ∃ y ∈ ggDepELGens news,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    rintro g ⟨o, rfl⟩
    cases o with
    | inl i =>
        refine ⟨ggDepELrefl (e.symm i), ?_, ?_⟩
        · rw [ggDepELGens, ggDepELFrameGens]
          exact Set.mem_union_left _ ⟨e.symm i, rfl⟩
        · apply LinearMap.ext
          intro v
          show r (Sum.inl i) v = θ.symm
            (ggDepARefl (ggDepELh (e.symm i)) (ggDepELα (e.symm i)) (θ v))
          have h := hrF (e.symm i) v
          rw [Equiv.apply_symm_apply] at h
          rw [← h, LinearEquiv.symm_apply_apply]
    | inr b =>
        rcases hmem b with hb | hb
        · rw [hb]
          refine ⟨ggDepARefl ha1 αa1, ?_, ?_⟩
          · rw [ggDepELGens]
            exact Set.mem_union_right _ ⟨(ha1, αa1), by simp [hnews], rfl⟩
          · apply LinearMap.ext
            intro v
            show r (Sum.inr a₁) v = θ.symm (ggDepARefl ha1 αa1 (θ v))
            rw [← hrefl1 v, LinearEquiv.symm_apply_apply]
        · rw [hb]
          refine ⟨ggDepARefl ha2 αa2, ?_, ?_⟩
          · rw [ggDepELGens]
            exact Set.mem_union_right _ ⟨(ha2, αa2), by simp [hnews], rfl⟩
          · apply LinearMap.ext
            intro v
            show r (Sum.inr a₂) v = θ.symm (ggDepARefl ha2 αa2 (θ v))
            rw [← hrefl2 v, LinearEquiv.symm_apply_apply]
  have hcorr2 : ∀ y ∈ ggDepELGens news, ∃ g ∈ Set.range r,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    intro y hy
    rw [ggDepELGens, ggDepELFrameGens] at hy
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := hy
      refine ⟨r (Sum.inl (e i)), ⟨Sum.inl (e i), rfl⟩, ?_⟩
      apply LinearMap.ext
      intro v
      show r (Sum.inl (e i)) v = θ.symm
        (ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
      rw [← hrF i v, LinearEquiv.symm_apply_apply]
    · obtain ⟨t, ht, rfl⟩ := hy
      rw [hnews] at ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · refine ⟨r (Sum.inr a₁), ⟨Sum.inr a₁, rfl⟩, ?_⟩
        apply LinearMap.ext
        intro v
        show r (Sum.inr a₁) v = θ.symm (ggDepARefl ha1 αa1 (θ v))
        rw [← hrefl1 v, LinearEquiv.symm_apply_apply]
      · refine ⟨r (Sum.inr a₂), ⟨Sum.inr a₂, rfl⟩, ?_⟩
        apply LinearMap.ext
        intro v
        show r (Sum.inr a₂) v = θ.symm (ggDepARefl ha2 αa2 (θ v))
        rw [← hrefl2 v, LinearEquiv.symm_apply_apply]
  have hJ₁ : ∀ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
      ∃ i : {i : Fin 6 // GGDepED4In i},
        (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ
          ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ θ.toLinearMap := by
    rintro g ⟨j, rfl⟩
    let i : {i : Fin 6 // GGDepED4In i} :=
      ⟨e.symm j.1, ⟨fun h0 => j.2.1 (by
          have := congrArg e h0
          simpa [hb1] using this),
        fun h5 => j.2.2 (by
          have := congrArg e h5
          simpa [hb2] using this)⟩⟩
    refine ⟨i, ?_⟩
    apply LinearMap.ext
    intro v
    have h := hrF i.1 v
    have hi1 : e i.1 = j.1 := Equiv.apply_symm_apply e j.1
    rw [hi1] at h
    change r (Sum.inl j.1) v = θ.symm (ggDepARefl (ggDepELh i.1) (ggDepELα i.1) (θ v))
    rw [← h, LinearEquiv.symm_apply_apply]
  have hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i},
      ∃ g ∈ Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)),
        (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ
          ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ θ.toLinearMap := by
    intro i
    refine ⟨r (Sum.inl (e i.1)), ⟨⟨e i.1, ?_⟩, rfl⟩, ?_⟩
    · exact ⟨fun h => i.2.1 (e.injective (h.trans hb1)),
        fun h => i.2.2 (e.injective (h.trans hb2))⟩
    · apply LinearMap.ext
      intro v
      have h := hrF i.1 v
      change r (Sum.inl (e i.1)) v =
        θ.symm (ggDepARefl (ggDepELh i.1) (ggDepELα i.1) (θ v))
      rw [← h, LinearEquiv.symm_apply_apply]
  have hTv : ¬ ∃ g ∈ Submonoid.closure (ggDepELGens news), GGDepAIsTv g :=
    ggDepEL_notTv θ rF hrF news rN hrN hnt'
  have hPZclause : ∀ c'' : ZMod 3, c'' ≠ 0 → ¬ GGDepELPZBad (ggDepELGens news)
      (ggDepELx + c'' • (lam • ggDepELx + mu • ggDepELz)) := by
    intro c'' hc''
    have hzBs : (xg : G) * (yg : G) ^ c''.val ∈ Bs := Bs.mul_mem xg.2 (Bs.pow_mem yg.2 _)
    have hzsub : (⟨(xg : G) * (yg : G) ^ c''.val, hzBs⟩ : ↥Bs) = xg * yg ^ c''.val :=
      Subtype.ext rfl
    have hzval : ι (Additive.ofMul (⟨(xg : G) * (yg : G) ^ c''.val, hzBs⟩ : ↥Bs)) =
        xV + c'' • yV := by
      rw [hxV, hyV, hzsub, ofMul_mul, ofMul_pow, map_add, map_nsmul]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c''.val (ι (Additive.ofMul yg)),
        ZMod.natCast_zmod_val c'']
    have h := ggDepELPZ_xfer hPZin hH hX hJΛ hXΛ hJl hXl hrow htag hcardB hJcard hJrefl ι θ
      (Set.range r) (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1))
      hA hAJ (ggDepELGens news) hcorr1 hcorr2 hJ₁ hJ₂
      (⟨(xg : G) * (yg : G) ^ c''.val, hzBs⟩ : ↥Bs) (hzD c'') (hzx c'' hc'') (hzy c'' hc'')
    rw [hzval] at h
    simpa only [map_add, map_smul, hθx, hy_lam_mu] using h
  refine ⟨c, c', ha1, αa1, ha2, αa2, lam, mu, hpat, hpat', hcne, hpairs, hxne, hlam_mu_ne,
    hdoty1, hdoty2, ?_, ?_⟩
  · simpa [hnews] using hTv
  · intro c'' hc''
    simpa only [hnews] using hPZclause c'' hc''

end CFSG.StandardType

end
