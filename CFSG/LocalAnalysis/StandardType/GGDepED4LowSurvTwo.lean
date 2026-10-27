module
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowModel
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowKillFrame
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
private theorem l05nS2_fixedJ_model :
    ∀ v : GGDepAE 3 6,
      (∀ c : Fin 6, c ≠ 0 → c ≠ 5 → ggDepAdot (ggDepELα c) v = 0) →
      ∃ lam mu : ZMod 3, v = lam • ggDepELx + mu • ggDepELz := by
  decide +kernel
theorem ggDepELSurv2_cell {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
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
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV) :
    ∃ (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (a₁ a₂ : Λa) (c c' : Fin 6)
      (ha1 αa1 ha2 αa2 : GGDepAE 3 6) (lam mu : ZMod 3)
      (news : Set (GGDepAE 3 6 × GGDepAE 3 6))
      (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V),
      θ xV = ggDepELx ∧
      ha1 = θ (h (Sum.inr a₁)) ∧
      ha2 = θ (h (Sum.inr a₂)) ∧
      a₁ ≠ a₂ ∧
      GGDepED4Leaf c ∧ GGDepED4Leaf c' ∧ c ≠ c' ∧
      GGDepELPairs2 c c' ha1 αa1 ha2 αa2 ∧
      (ggDepAdot αa1 ggDepELx ≠ 0 ∨ ggDepAdot αa2 ggDepELx ≠ 0) ∧
      (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggDepAdot αa1 (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      ggDepAdot αa2 (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      θ yV = lam • ggDepELx + mu • ggDepELz ∧
      news = {(ha1, αa1), (ha2, αa2)} ∧
      (∀ i v, θ (r (Sum.inl (e i)) v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)) ∧
      (∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v)) ∧
      (∀ v, θ (r (Sum.inr a₁) v) = ggDepARefl ha1 αa1 (θ v)) ∧
      (∀ v, θ (r (Sum.inr a₂) v) = ggDepARefl ha2 αa2 (θ v)) ∧
      Subgroup.closure (Set.range (fun i : Fin 6 => r (Sum.inl (e i))) ∪ rN '' news) ≤
        Subgroup.closure (Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 6 => r (Sum.inl (e i))) ∪ rN '' news),
        ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) := by
  classical
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepELModel_iso hF hdim
  obtain ⟨eK, heK⟩ := hA2
  have hne_of : ∀ c : Fin 6, GGDepED4In c → e c ≠ b₁ ∧ e c ≠ b₂ := by
    intro c hc
    obtain ⟨h0, h5⟩ := hc
    exact ⟨fun h => h0 (e.injective (by rw [h, hb1])),
      fun h => h5 (e.injective (by rw [h, hb2]))⟩
  have hne_symm : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, GGDepED4In (e.symm i.1) := by
    intro i
    obtain ⟨h1, h2⟩ := i.2
    exact ⟨fun h => h1 (by
        have hh : i.1 = e 0 := (Equiv.apply_symm_apply e i.1).symm.trans (congrArg e h)
        exact hh.trans hb1.symm),
      fun h => h2 (by
        have hh : i.1 = e 5 := (Equiv.apply_symm_apply e i.1).symm.trans (congrArg e h)
        exact hh.trans hb2.symm)⟩
  let eJ : {c : Fin 6 // GGDepED4In c} ≃ {i : Λ // i ≠ b₁ ∧ i ≠ b₂} :=
    { toFun := fun c => ⟨e c.1, hne_of c.1 c.2⟩
      invFun := fun i => ⟨e.symm i.1, hne_symm i⟩
      left_inv := by intro c; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }
  let ee : ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ≃
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) := Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := MK.reindex ee.symm
  let CK' : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)
      ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hMK' : MK' = CoxeterMatrix.E₆.reindex (eK.trans ee.symm) := by
    show MK.reindex ee.symm = _
    rw [heK]
    exact l05nBL_reindex_trans CoxeterMatrix.E₆ eK ee.symm
  have hWK' : GGIsWeylMatrix MK' := Or.inr (Or.inl ⟨eK.trans ee.symm, hMK'⟩)
  have hCK' : GGIntCartan MK' CK' := l05nBL_intCartan_reindex hCK ee
  have hcast : ∀ i j : {c : Fin 6 // GGDepED4In c},
      ((CK' (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        (((CartanMatrix.E 6) i.1 j.1 : ℤ) : ZMod 3) := by
    intro i j
    have h1 := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at h1
    have h2 := hF.pair i.1 j.1
    have hval : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp [CK', ee, eJ, Matrix.submatrix_apply]
    rw [hval, ← h1]
    rw [show (eJ i).val = e i.1 from rfl, show (eJ j).val = e j.1 from rfl]
    exact h2
  obtain ⟨a₁, a₂, c, c', ha12, hleafc, hleafc', hcc', hpair2, hp12, hp21, hp11, hp22⟩ :=
    ggDepED4_pattern2 hcard hWK' hCK' ⟨eK.trans ee.symm, hMK'⟩ hcast
  set ha1 : GGDepAE 3 6 := θ (h (Sum.inr a₁)) with ha1_def
  set ha2 : GGDepAE 3 6 := θ (h (Sum.inr a₂)) with ha2_def
  obtain ⟨αa1, hαa1⟩ := l05nPT_dot_of_comp_symm (α (Sum.inr a₁)) θ
  obtain ⟨αa2, hαa2⟩ := l05nPT_dot_of_comp_symm (α (Sum.inr a₂)) θ
  have hmem : ∀ a : Λa, a = a₁ ∨ a = a₂ := by
    have hcard2 : ({a₁, a₂} : Finset Λa).card = Fintype.card Λa := by
      rw [Finset.card_pair ha12, ← Nat.card_eq_fintype_card, hcard]
    have htop : ({a₁, a₂} : Finset Λa) = Finset.univ := Finset.eq_univ_of_card _ hcard2
    intro a
    have : a ∈ ({a₁, a₂} : Finset Λa) := by rw [htop]; exact Finset.mem_univ a
    simpa using this
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have hdiag : ∀ c : Fin 6, ((CartanMatrix.E 6) c c : ZMod 3) = 2 := by
    intro c
    rw [← ggDepELpair c c]
    fin_cases c <;> decide
  have hh_ne : ∀ c : Fin 6, h (Sum.inl (e c)) ≠ 0 := by
    intro c hzero
    have hpair := hF.pair c c
    rw [hzero, map_zero, hdiag c] at hpair
    exact h2ne hpair.symm
  have ha_ne : ∀ a : Λa, h (Sum.inr a) ≠ 0 := by
    intro a hzero
    have hpair := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpair
    rw [hzero, map_zero, hCK.1 (Sum.inr a)] at hpair
    exact h2ne (by simpa using hpair.symm)
  have hpair_main : ∀ d : Fin 6, GGDepED4In d →
      ggDepAdot αa1 (ggDepELh d) = (if d = c then (-1 : ZMod 3) else 0) ∧
      ggDepAdot (ggDepELα d) ha1 = (if d = c then (-1 : ZMod 3) else 0) ∧
      ggDepAdot αa2 (ggDepELh d) = (if d = c' then (-1 : ZMod 3) else 0) ∧
      ggDepAdot (ggDepELα d) ha2 = (if d = c' then (-1 : ZMod 3) else 0) := by
    intro d hd
    have hsymm : θ.symm (ggDepELh d) = h (Sum.inl (e d)) := by
      rw [← hθh d]; exact LinearEquiv.symm_apply_apply θ _
    have hsymmα : ∀ v, ggDepAdot (ggDepELα d) (θ v) = α (Sum.inl (e d)) v :=
      fun v => (hθα d v).symm
    have hne' : e d ≠ b₁ ∧ e d ≠ b₂ := hne_of d hd
    have hdot1 : ggDepAdot αa1 (ggDepELh d) =
        (CK' (Sum.inr a₁) (Sum.inl ⟨d, hd⟩) : ZMod 3) := by
      rw [hαa1 (ggDepELh d), hsymm, show CK' (Sum.inr a₁) (Sum.inl ⟨d, hd⟩) =
          CK (Sum.inr a₁) (Sum.inl ⟨e d, hne'⟩) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inr, Sum.map_inl, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inr a₁) (Sum.inl ⟨e d, hne'⟩)
    have hdot2 : ggDepAdot (ggDepELα d) ha1 =
        (CK' (Sum.inl ⟨d, hd⟩) (Sum.inr a₁) : ZMod 3) := by
      change ggDepAdot (ggDepELα d) (θ (h (Sum.inr a₁))) = _
      rw [hsymmα (h (Sum.inr a₁)), show CK' (Sum.inl ⟨d, hd⟩) (Sum.inr a₁) =
          CK (Sum.inl ⟨e d, hne'⟩) (Sum.inr a₁) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inl, Sum.map_inr, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inl ⟨e d, hne'⟩) (Sum.inr a₁)
    have hdot3 : ggDepAdot αa2 (ggDepELh d) =
        (CK' (Sum.inr a₂) (Sum.inl ⟨d, hd⟩) : ZMod 3) := by
      rw [hαa2 (ggDepELh d), hsymm, show CK' (Sum.inr a₂) (Sum.inl ⟨d, hd⟩) =
          CK (Sum.inr a₂) (Sum.inl ⟨e d, hne'⟩) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inr, Sum.map_inl, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inr a₂) (Sum.inl ⟨e d, hne'⟩)
    have hdot4 : ggDepAdot (ggDepELα d) ha2 =
        (CK' (Sum.inl ⟨d, hd⟩) (Sum.inr a₂) : ZMod 3) := by
      change ggDepAdot (ggDepELα d) (θ (h (Sum.inr a₂))) = _
      rw [hsymmα (h (Sum.inr a₂)), show CK' (Sum.inl ⟨d, hd⟩) (Sum.inr a₂) =
          CK (Sum.inl ⟨e d, hne'⟩) (Sum.inr a₂) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inl, Sum.map_inr, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inl ⟨e d, hne'⟩) (Sum.inr a₂)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hdot1, (hpair2 ⟨d, hd⟩).1]; simp
    · rw [hdot2, (hpair2 ⟨d, hd⟩).2.1]; simp
    · rw [hdot3, (hpair2 ⟨d, hd⟩).2.2.1]; simp
    · rw [hdot4, (hpair2 ⟨d, hd⟩).2.2.2]; simp
  have hpair : GGDepELPairs2 c c' ha1 αa1 ha2 αa2 := by
    refine ⟨hpair_main, ?_, ?_, ?_, ?_⟩
    · have h : ggDepAdot αa1 ha2 = (CK' (Sum.inr a₁) (Sum.inr a₂) : ZMod 3) := by
        change ggDepAdot αa1 (θ (h (Sum.inr a₂))) = _
        rw [hαa1 (θ (h (Sum.inr a₂)))]
        change α (Sum.inr a₁) (θ.symm (θ (h (Sum.inr a₂)))) = _
        rw [LinearEquiv.symm_apply_apply, show CK' (Sum.inr a₁) (Sum.inr a₂) =
          CK (Sum.inr a₁) (Sum.inr a₂) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₁) (Sum.inr a₂)
      rw [h, hp12]; simp
    · have h : ggDepAdot αa2 ha1 = (CK' (Sum.inr a₂) (Sum.inr a₁) : ZMod 3) := by
        change ggDepAdot αa2 (θ (h (Sum.inr a₁))) = _
        rw [hαa2 (θ (h (Sum.inr a₁)))]
        change α (Sum.inr a₂) (θ.symm (θ (h (Sum.inr a₁)))) = _
        rw [LinearEquiv.symm_apply_apply, show CK' (Sum.inr a₂) (Sum.inr a₁) =
          CK (Sum.inr a₂) (Sum.inr a₁) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₂) (Sum.inr a₁)
      rw [h, hp21]; simp
    · have h : ggDepAdot αa1 ha1 = (CK' (Sum.inr a₁) (Sum.inr a₁) : ZMod 3) := by
        change ggDepAdot αa1 (θ (h (Sum.inr a₁))) = _
        rw [hαa1 (θ (h (Sum.inr a₁)))]
        change α (Sum.inr a₁) (θ.symm (θ (h (Sum.inr a₁)))) = _
        rw [LinearEquiv.symm_apply_apply, show CK' (Sum.inr a₁) (Sum.inr a₁) =
          CK (Sum.inr a₁) (Sum.inr a₁) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₁) (Sum.inr a₁)
      rw [h, hp11]; norm_num
    · have h : ggDepAdot αa2 ha2 = (CK' (Sum.inr a₂) (Sum.inr a₂) : ZMod 3) := by
        change ggDepAdot αa2 (θ (h (Sum.inr a₂))) = _
        rw [hαa2 (θ (h (Sum.inr a₂)))]
        change α (Sum.inr a₂) (θ.symm (θ (h (Sum.inr a₂)))) = _
        rw [LinearEquiv.symm_apply_apply, show CK' (Sum.inr a₂) (Sum.inr a₂) =
          CK (Sum.inr a₂) (Sum.inr a₂) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₂) (Sum.inr a₂)
      rw [h, hp22]; norm_num
  have hnews_ne : (ha1, αa1) ≠ (ha2, αa2) := by
    intro hc
    have h0 : ggDepAdot αa1 ha2 = 0 := hpair.2.1
    have h2 : ggDepAdot αa2 ha2 = 2 := hpair.2.2.2.2
    rw [show αa1 = αa2 from congrArg Prod.snd hc] at h0
    rw [h2] at h0
    exact h2ne h0
  have hnews_ne' : (ha2, αa2) ≠ (ha1, αa1) := fun h => hnews_ne h.symm
  have hxne : ggDepAdot αa1 ggDepELx ≠ 0 ∨ ggDepAdot αa2 ggDepELx ≠ 0 := by
    obtain ⟨a₀, ha₀⟩ := hxa
    have hxV : θ.symm ggDepELx = xV := by
      rw [← hθx]; exact LinearEquiv.symm_apply_apply θ _
    rcases hmem a₀ with h | h
    · left
      intro h0
      apply ha₀
      rw [h, ← hxV, ← hαa1 ggDepELx, h0]
    · right
      intro h0
      apply ha₀
      rw [h, ← hxV, ← hαa2 ggDepELx, h0]
  have hfixθ : ∀ c : Fin 6, GGDepED4In c → ggDepAdot (ggDepELα c) (θ yV) = 0 := by
    intro c hc
    have hfix := hyJ ⟨e c, hne_of c hc⟩
    have h0 : α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = 0 := by
      have h1 : yV - α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = yV := by
        rw [← hr (Sum.inl (e c)) yV, hfix]
      have h2 : yV - α (Sum.inl (e c)) yV • h (Sum.inl (e c)) - yV = 0 := by
        rw [h1, sub_self]
      simpa using h2
    have hα0 : α (Sum.inl (e c)) yV = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (hh_ne c)
    rw [← hθα c yV]
    exact hα0
  have hfixθ' : ∀ c : Fin 6, c ≠ 0 → c ≠ 5 → ggDepAdot (ggDepELα c) (θ yV) = 0 :=
    fun c h0 h5 => hfixθ c ⟨h0, h5⟩
  obtain ⟨lam, mu, hy_eq⟩ := l05nS2_fixedJ_model (θ yV) hfixθ'
  have hy_ne : lam • ggDepELx + mu • ggDepELz ≠ 0 := by
    intro hzero
    have h1 : θ yV = 0 := by rw [hy_eq, hzero]
    exact hy0 (θ.injective (by rw [h1, map_zero]))
  have hlam : lam ≠ 0 ∨ mu ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hy_ne (by rw [h.1, h.2, zero_smul, zero_smul, add_zero])
  have hfixa1 : ggDepAdot αa1 (lam • ggDepELx + mu • ggDepELz) = 0 := by
    have h1 : ggDepAdot αa1 (θ yV) = α (Sum.inr a₁) yV := by
      rw [hαa1 (θ yV)]; simp
    have h2 : α (Sum.inr a₁) yV = 0 := by
      have hfix := hya a₁
      have h0 : α (Sum.inr a₁) yV • h (Sum.inr a₁) = 0 := by
        have h3 : yV - α (Sum.inr a₁) yV • h (Sum.inr a₁) = yV := by
          rw [← hr (Sum.inr a₁) yV, hfix]
        have h4 : yV - α (Sum.inr a₁) yV • h (Sum.inr a₁) - yV = 0 := by
          rw [h3, sub_self]
        simpa using h4
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ha_ne a₁)
    rw [← hy_eq, h1, h2]
  have hfixa2 : ggDepAdot αa2 (lam • ggDepELx + mu • ggDepELz) = 0 := by
    have h1 : ggDepAdot αa2 (θ yV) = α (Sum.inr a₂) yV := by
      rw [hαa2 (θ yV)]; simp
    have h2 : α (Sum.inr a₂) yV = 0 := by
      have hfix := hya a₂
      have h0 : α (Sum.inr a₂) yV • h (Sum.inr a₂) = 0 := by
        have h3 : yV - α (Sum.inr a₂) yV • h (Sum.inr a₂) = yV := by
          rw [← hr (Sum.inr a₂) yV, hfix]
        have h4 : yV - α (Sum.inr a₂) yV • h (Sum.inr a₂) - yV = 0 := by
          rw [h3, sub_self]
        simpa using h4
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ha_ne a₂)
    rw [← hy_eq, h1, h2]
  have hrefl1 : ∀ v, θ (r (Sum.inr a₁) v) = ggDepARefl ha1 αa1 (θ v) := by
    intro v
    have h2 : α (Sum.inr a₁) v = ggDepAdot αa1 (θ v) := by
      rw [hαa1 (θ v)]; simp
    rw [hr (Sum.inr a₁) v, map_sub, map_smul, h2, ← ha1_def]
    exact (l05nPT_refl_apply ha1 αa1 (θ v)).symm
  have hrefl2 : ∀ v, θ (r (Sum.inr a₂) v) = ggDepARefl ha2 αa2 (θ v) := by
    intro v
    have h2 : α (Sum.inr a₂) v = ggDepAdot αa2 (θ v) := by
      rw [hαa2 (θ v)]; simp
    rw [hr (Sum.inr a₂) v, map_sub, map_smul, h2, ← ha2_def]
    exact (l05nPT_refl_apply ha2 αa2 (θ v)).symm
  let rF : Fin 6 → V ≃ₗ[ZMod 3] V := fun i => r (Sum.inl (e i))
  let news : Set (GGDepAE 3 6 × GGDepAE 3 6) := {(ha1, αa1), (ha2, αa2)}
  let rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V := fun t =>
    if t = (ha1, αa1) then r (Sum.inr a₁)
    else if t = (ha2, αa2) then r (Sum.inr a₂) else 1
  have hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v) := by
    intro i v
    have h2 : α (Sum.inl (e i)) v = ggDepAdot (ggDepELα i) (θ v) := hθα i v
    change θ (r (Sum.inl (e i)) v) = _
    rw [hr (Sum.inl (e i)) v, map_sub, map_smul, h2, hθh i]
    exact (l05nPT_refl_apply (ggDepELh i) (ggDepELα i) (θ v)).symm
  have hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v) := by
    intro t ht v
    simp only [news, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · have h : rN (ha1, αa1) = r (Sum.inr a₁) := by simp [rN]
      rw [h]; exact hrefl1 v
    · have h' : rN (ha2, αa2) = r (Sum.inr a₂) := by simp [rN, hnews_ne']
      rw [h']; exact hrefl2 v
  have hrangeF : Set.range rF ⊆ Set.range r := by
    rintro g ⟨i, rfl⟩
    exact ⟨Sum.inl (e i), rfl⟩
  have hrangeN : rN '' news ⊆ Set.range r := by
    rintro g ⟨t, ht, rfl⟩
    simp only [news, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨Sum.inr a₁, by simp [rN]⟩
    · exact ⟨Sum.inr a₂, by simp [rN, hnews_ne']⟩
  have hsub : Subgroup.closure (Set.range rF ∪ rN '' news) ≤ Subgroup.closure (Set.range r) :=
    Subgroup.closure_mono (by
      intro g hg
      rcases hg with hg | hg
      · exact hrangeF hg
      · exact hrangeN hg)
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hnt g (hsub hg)
  refine ⟨θ, a₁, a₂, c, c', ha1, αa1, ha2, αa2, lam, mu, news, rN,
    hθx, ha1_def, ha2_def, ha12, hleafc, hleafc', hcc', hpair, hxne, hlam,
    hfixa1, hfixa2, hy_eq, rfl, hrF, hrN, hrefl1, hrefl2, hsub, hnt'⟩
end CFSG.StandardType
end
