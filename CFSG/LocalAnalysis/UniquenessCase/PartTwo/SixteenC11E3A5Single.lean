module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Holt.H78.AltModelAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private noncomputable def s1611e3_a5_sym5 :
    Equiv.Perm (Fin 5) →* MulAut (FFModel.symDn 5).Mod :=
  (FFModel.symDn_isActionModel 5).modAct

private noncomputable def s1611e3_a5_alt5 :
    ↥(alternatingGroup (Fin 5)) →* MulAut (FFModel.altDn 5).Mod :=
  (FFModel.altDn_isActionModel 5).modAct

private lemma s1611e3_a5_modAct_alt' (a : ↥(alternatingGroup (Fin 5)))
    (q : (FFModel.symDn 5).Mod) :
    s1611e3_a5_alt5 a q = s1611e3_a5_sym5 (a : Equiv.Perm (Fin 5)) q := rfl

private noncomputable def s1611e3_a5_res {W : Type} [CommGroup W] (J : Subgroup W)
    (e : MulAut W) (he : J.map e.toMonoidHom = J) : ↥J ≃* ↥J :=
  (MulEquiv.subgroupMap e J).trans (MulEquiv.subgroupCongr he)

private theorem s1611e3_a5_res_apply {W : Type} [CommGroup W] {J : Subgroup W}
    {e : MulAut W} (he : J.map e.toMonoidHom = J) (u : ↥J) :
    ((s1611e3_a5_res J e he u : ↥J) : W) = e (u : W) := rfl

private theorem s1611e3_a5_res_mul {W : Type} [CommGroup W] {J : Subgroup W}
    (a b : MulAut W) (ha : J.map a.toMonoidHom = J) (hb : J.map b.toMonoidHom = J)
    (hab : J.map (a * b).toMonoidHom = J) (u : ↥J) :
    s1611e3_a5_res J (a * b) hab u = s1611e3_a5_res J a ha (s1611e3_a5_res J b hb u) := by
  apply Subtype.ext
  rw [s1611e3_a5_res_apply, s1611e3_a5_res_apply, s1611e3_a5_res_apply]
  rfl

private theorem s1611e3_a5_transfer {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {J : Subgroup W}
    {E : Subgroup (MulAut W)}
    (hEL : ∀ e ∈ E, L.map (MulAut.conj e).toMonoidHom = L)
    (hEJ : ∀ e ∈ E, J.map e.toMonoidHom = J)
    (ρ : ↥(alternatingGroup (Fin 5)) ≃* ↥L) (β : ↥J ≃* (FFModel.altDn 5).Mod)
    (hβ : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥J),
      ((β.symm (s1611e3_a5_alt5 γ (β u)) : ↥J) : W) = ((ρ γ : ↥L) : MulAut W) (u : W))
    (hEend : Z391.EndUnitsTrivial L J) (e : E) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ u : ↥J,
      β (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) = s1611e3_a5_sym5 σ (β u) := by
  classical
  let βs : ↥J ≃* (FFModel.symDn 5).Mod := β
  have hβs : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥J),
      ((βs.symm (s1611e3_a5_sym5 (γ : Equiv.Perm (Fin 5)) (βs u)) : ↥J) : W) =
        ((ρ γ : ↥L) : MulAut W) (u : W) := by
    intro γ u
    rw [← s1611e3_a5_modAct_alt' γ (βs u)]
    exact hβ γ u
  have hβ_apply : ∀ (a : ↥(alternatingGroup (Fin 5))) (u : ↥J),
      βs (⟨((ρ a : ↥L) : MulAut W) (u : W),
          by rw [← hβs a u]; exact (βs.symm _).2⟩ : ↥J) =
        s1611e3_a5_sym5 (a : Equiv.Perm (Fin 5)) (βs u) := by
    intro a u
    have hsub : (⟨((ρ a : ↥L) : MulAut W) (u : W),
        by rw [← hβs a u]; exact (βs.symm _).2⟩ : ↥J) =
        βs.symm (s1611e3_a5_sym5 (a : Equiv.Perm (Fin 5)) (βs u)) :=
      Subtype.ext (hβs a u).symm
    rw [hsub]
    exact βs.apply_symm_apply _
  have hinvL : ∀ l : ↥L, ∀ u : ↥J, (l : MulAut W) (u : W) ∈ J := by
    intro l u
    obtain ⟨a, rfl⟩ := ρ.surjective l
    rw [← hβs a u]
    exact (βs.symm _).2
  have hJmapL : ∀ l : ↥L, J.map (l : MulAut W).toMonoidHom = J := by
    intro l
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact hinvL l ⟨z, hz⟩
    · exact le_of_eq (Nat.card_congr (MulEquiv.subgroupMap (l : MulAut W) J).toEquiv)
  let lJ : ↥L → ↥J → ↥J := fun l u => ⟨(l : MulAut W) (u : W), hinvL l u⟩
  have lJ_apply : ∀ (l : ↥L) (u : ↥J), ((lJ l u : ↥J) : W) = (l : MulAut W) (u : W) :=
    fun l u => rfl
  have hβL : ∀ (l : ↥L) (u : ↥J),
      βs (lJ l u) =
        s1611e3_a5_sym5 ((ρ.symm l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (βs u) := by
    intro l u
    have hsub : lJ l u = βs.symm
        (s1611e3_a5_sym5 ((ρ.symm l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (βs u)) := by
      apply Subtype.ext
      rw [lJ_apply, hβs (ρ.symm l) u]
      exact (congrArg (fun z : ↥L => (z : MulAut W) (u : W))
        (MulEquiv.apply_symm_apply ρ l)).symm
    rw [hsub]
    exact βs.apply_symm_apply _
  have hELc : ∀ e' ∈ E, L.map ((MulAut.conj e') : MulAut W →* MulAut W) = L := by
    intro e' he'
    have heq : ((MulAut.conj e') : MulAut W →* MulAut W) =
        (MulAut.conj e').toMonoidHom := rfl
    rw [heq]
    exact hEL e' he'
  let conjL : ↥L ≃* ↥L :=
    (MulEquiv.subgroupMap (MulAut.conj (e : MulAut W)) L).trans
      (MulEquiv.subgroupCongr (hELc (e : MulAut W) e.2))
  have conjL_apply : ∀ l : ↥L,
      ((conjL l : ↥L) : MulAut W) =
        (e : MulAut W) * (l : MulAut W) * (e : MulAut W)⁻¹ := by
    intro l
    change (((MulEquiv.subgroupCongr (hELc (e : MulAut W) e.2))
      ((MulEquiv.subgroupMap (MulAut.conj (e : MulAut W)) L) l) : ↥L) : MulAut W)
      = (e : MulAut W) * (l : MulAut W) * (e : MulAut W)⁻¹
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  let φ : MulAut ↥(alternatingGroup (Fin 5)) := (ρ.trans conjL).trans ρ.symm
  have hφ_conj : ∀ a : ↥(alternatingGroup (Fin 5)), ρ (φ a) = conjL (ρ a) := by
    intro a
    simp only [φ, MulEquiv.trans_apply]
    exact MulEquiv.apply_symm_apply ρ _
  have hφ_apply : ∀ a : ↥(alternatingGroup (Fin 5)),
      ((ρ (φ a) : ↥L) : MulAut W) =
        (e : MulAut W) * ((ρ a : ↥L) : MulAut W) * (e : MulAut W)⁻¹ := by
    intro a
    rw [hφ_conj a, conjL_apply]
  obtain ⟨σ, hσ⟩ := CFSG.Holt.H78.exists_perm_conj_eq_of_mulAut_alternatingGroup
    (Δ := Fin 5) (by norm_num) (by norm_num) φ
  have hβconj : ∀ a : ↥(alternatingGroup (Fin 5)),
      s1611e3_a5_sym5 ((φ a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        s1611e3_a5_sym5 (σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹) :=
    fun a => congrArg s1611e3_a5_sym5 (hσ a)
  have hres_mul : ∀ (l : ↥L) (u : ↥J),
      s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) (lJ l u) = lJ (conjL l)
        (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) := by
    intro l u
    apply Subtype.ext
    simp only [lJ_apply, s1611e3_a5_res_apply, conjL_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
  let θ : ↥J ≃* ↥J := (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2)).trans
    (((βs.trans (s1611e3_a5_sym5 σ⁻¹)).trans βs.symm))
  have hθβ : ∀ u : ↥J,
      βs (θ u) =
        s1611e3_a5_sym5 σ⁻¹ (βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u)) := by
    intro u
    simp only [θ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hθcomm : ∀ (l : ↥L) (x y : ↥J), (l : MulAut W) (x : W) = (y : W) →
      (l : MulAut W) ((θ x : ↥J) : W) = ((θ y : ↥J) : W) := by
    intro l x y hxy
    set a : ↥(alternatingGroup (Fin 5)) := ρ.symm l with ha
    have hρa : ρ a = l := by rw [ha, MulEquiv.apply_symm_apply]
    have hy : y = lJ l x := Subtype.ext hxy.symm
    have hmem : (l : MulAut W) ((θ x : ↥J) : W) ∈ J := hinvL l (θ x)
    have key : βs (⟨(l : MulAut W) ((θ x : ↥J) : W), hmem⟩ : ↥J) = βs (θ y) := by
      have h1 : βs (⟨(l : MulAut W) ((θ x : ↥J) : W), hmem⟩ : ↥J) =
          s1611e3_a5_sym5 (a : Equiv.Perm (Fin 5)) (βs (θ x)) := by
        have hsub : (⟨(l : MulAut W) ((θ x : ↥J) : W), hmem⟩ : ↥J) =
            βs.symm (s1611e3_a5_sym5 (a : Equiv.Perm (Fin 5)) (βs (θ x))) := by
          apply Subtype.ext
          rw [hβs a (θ x)]
          exact (congrArg (fun z : ↥L => (z : MulAut W) ((θ x : ↥J) : W)) hρa).symm
        rw [hsub]
        exact βs.apply_symm_apply _
      have hφsymm : ρ.symm (conjL l) = φ a := by
        rw [← hρa, ← hφ_conj a, MulEquiv.symm_apply_apply]
      have h2 : βs (θ y) = s1611e3_a5_sym5 ((a : Equiv.Perm (Fin 5)) * σ⁻¹)
          (βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) x)) := by
        rw [hy, hθβ, hres_mul, hβL, hφsymm, hβconj]
        rw [← MulAut.mul_apply, ← s1611e3_a5_sym5.map_mul]
        rw [show σ⁻¹ * (σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹) =
          (a : Equiv.Perm (Fin 5)) * σ⁻¹ by group]
      rw [h1, h2, hθβ]
      rw [← MulAut.mul_apply, ← s1611e3_a5_sym5.map_mul]
    exact congrArg Subtype.val (βs.injective key)
  have hθrefl : θ = MulEquiv.refl ↥J := hEend θ hθcomm
  refine ⟨σ, fun u => ?_⟩
  have h1 : θ u = u := congrArg (fun f : ↥J ≃* ↥J => f u) hθrefl
  have h2 : βs u =
      s1611e3_a5_sym5 σ⁻¹ (βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u)) :=
    (congrArg βs h1).symm.trans (hθβ u)
  have h4 : s1611e3_a5_sym5 σ
        (s1611e3_a5_sym5 σ⁻¹ (βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u))) =
      βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) := by
    rw [← MulAut.mul_apply, ← s1611e3_a5_sym5.map_mul, mul_inv_cancel,
      s1611e3_a5_sym5.map_one, MulAut.one_apply]
  exact ((congrArg (fun q => s1611e3_a5_sym5 σ q) h2).trans h4).symm

theorem s1611e3_a5_single {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {J : Subgroup W} (hL : IsAlt ↥L 5)
    (hJ : AlternatingNatural L J ⊥ 5) {E : Subgroup (MulAut W)} (hEel : IsElemAbelian2 E)
    (hEL : ∀ e ∈ E, L.map (MulAut.conj e).toMonoidHom = L)
    (hEJ : ∀ e ∈ E, J.map e.toMonoidHom = J) (hE1 : ∃ e ∈ E, ∃ j ∈ J, e j ≠ j) :
    ∃ B ≤ E, E3.mQuot E B = 1 ∧ ∃ u ∈ J, (∀ b ∈ B, b u = u) ∧ ∃ e ∈ E, e u ≠ u := by
  classical
  obtain ⟨ρ, β, hβ⟩ := s16c11_big_realizes_equiv (FFModel.altDn_isActionModel 5)
    (FFC.altDn_faithful (by norm_num)) hJ
  let βs : ↥J ≃* (FFModel.symDn 5).Mod := β
  have hEend : Z391.EndUnitsTrivial L J := s16c167_endUnits_alt (by norm_num) hJ
  have htransfer : ∀ e : ↥E, ∃ σ : Equiv.Perm (Fin 5), ∀ u : ↥J,
      βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) =
        s1611e3_a5_sym5 σ (βs u) := by
    intro e
    obtain ⟨σ, hσ⟩ := s1611e3_a5_transfer hEL hEJ ρ β hβ hEend e
    exact ⟨σ, hσ⟩
  have hsym_inj : Function.Injective s1611e3_a5_sym5 := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply FFC.symDn_faithful (by norm_num : 5 ≤ 5)
    intro m hm
    have h1 := congrArg (fun g : MulAut (FFModel.symDn 5).Mod =>
      g (QuotientGroup.mk ⟨m, hm⟩)) hσ
    simp only [MulAut.one_apply] at h1
    rw [show s1611e3_a5_sym5 σ = (FFModel.symDn_isActionModel 5).modAct
      (show (FFModel.symDn 5).Gam from σ) from rfl] at h1
    rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (⟨(FFModel.symDn 5).act σ m,
        (FFModel.symDn_isActionModel 5).sec_inv σ m hm⟩ : ↥(FFModel.symDn 5).sec)⁻¹
        * ⟨m, hm⟩ ∈ (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec := h2
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 := (FFModel.symDn 5).ker.inv_mem h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h4
    rw [mul_comm]
    exact h4
  have huniq : ∀ (e : ↥E) (σ τ : Equiv.Perm (Fin 5)),
      (∀ u : ↥J, βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) =
        s1611e3_a5_sym5 σ (βs u)) →
      (∀ u : ↥J, βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) =
        s1611e3_a5_sym5 τ (βs u)) → σ = τ := by
    intro e σ τ hσ hτ
    apply hsym_inj
    ext q
    obtain ⟨u, rfl⟩ := βs.surjective q
    rw [← hσ u, ← hτ u]
  let fFun : ↥E → Equiv.Perm (Fin 5) := fun e => Classical.choose (htransfer e)
  have fFun_spec : ∀ (e : ↥E) (u : ↥J),
      βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) =
        s1611e3_a5_sym5 (fFun e) (βs u) := fun e => Classical.choose_spec (htransfer e)
  have f_one : fFun 1 = 1 := by
    refine huniq 1 (fFun 1) 1 (fFun_spec 1) ?_
    intro u
    rw [map_one]
    have h : s1611e3_a5_res J ((1 : ↥E) : MulAut W) (hEJ (1 : ↥E) (1 : ↥E).2) u = u := by
      apply Subtype.ext
      rw [s1611e3_a5_res_apply]
      rfl
    rw [h]
    rfl
  have f_mul : ∀ a b : ↥E, fFun (a * b) = fFun a * fFun b := by
    intro a b
    refine huniq (a * b) (fFun (a * b)) (fFun a * fFun b) (fFun_spec (a * b)) ?_
    intro u
    rw [map_mul, MulAut.mul_apply, ← fFun_spec b u,
      ← fFun_spec a (s1611e3_a5_res J (b : MulAut W) (hEJ b b.2) u)]
    have h : s1611e3_a5_res J ((a * b : ↥E) : MulAut W) (hEJ (a * b) (a * b).2) u =
        s1611e3_a5_res J (a : MulAut W) (hEJ a a.2)
          (s1611e3_a5_res J (b : MulAut W) (hEJ b b.2) u) :=
      s1611e3_a5_res_mul (a : MulAut W) (b : MulAut W) (hEJ a a.2) (hEJ b b.2)
        (hEJ (a * b) (a * b).2) u
    rw [h]
  let f : ↥E →* Equiv.Perm (Fin 5) :=
    { toFun := fFun, map_one' := f_one, map_mul' := f_mul }
  have f_apply : ∀ e : ↥E, f e = fFun e := fun e => rfl
  have f_spec : ∀ (e : ↥E) (u : ↥J),
      βs (s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u) =
        s1611e3_a5_sym5 (f e) (βs u) := fun e => fFun_spec e
  let P : Subgroup (Equiv.Perm (Fin 5)) := Subgroup.map f (⊤ : Subgroup ↥E)
  have hPab : IsElemAbelian 2 P := by
    constructor
    · refine IsMulCommutative.of_comm fun x y => ?_
      obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨b, -, hb⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : Equiv.Perm (Fin 5)) * (y : Equiv.Perm (Fin 5)) =
        (y : Equiv.Perm (Fin 5)) * (x : Equiv.Perm (Fin 5))
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (hEel.1 (a : MulAut W) a.2 (b : MulAut W) b.2))
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
      have ha2 : a ^ 2 = 1 := by
        apply Subtype.ext
        change (a : MulAut W) ^ 2 = 1
        exact hEel.2 (a : MulAut W) a.2
      rw [← map_pow, ha2, map_one]
  obtain ⟨e0, he0E, j0, hj0J, he0j0⟩ := hE1
  let e0' : ↥E := ⟨e0, he0E⟩
  have hfe0 : f e0' ≠ 1 := by
    intro hfe
    apply he0j0
    have hfix : ∀ u : ↥J, s1611e3_a5_res J e0 (hEJ e0 he0E) u = u := by
      intro u
      apply β.injective
      have h1 := fFun_spec e0' u
      rw [show fFun e0' = 1 from hfe] at h1
      rw [map_one] at h1
      exact h1
    have hv := congrArg (fun z : ↥J => (z : W)) (hfix ⟨j0, hj0J⟩)
    rw [s1611e3_a5_res_apply] at hv
    exact hv
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hfe0
    have : f e0' ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))) := by
      rw [← hbot]
      exact Subgroup.mem_map.mpr ⟨e0', trivial, rfl⟩
    simpa using this
  by_contra hgoal
  have hgoal' : ∀ B : Subgroup (MulAut W), B ≤ E → E3.mQuot E B = 1 →
      ∀ u : W, u ∈ J → (∀ b ∈ B, b u = u) → ∀ e ∈ E, e u = u := by
    intro B hBE hmq u huJ hfix e heE
    by_contra hne
    exact hgoal ⟨B, hBE, hmq, u, huJ, hfix, e, heE, hne⟩
  have hB : ∀ (B : Subgroup (Equiv.Perm (Fin 5))), B ≤ P → B.relIndex P ≤ 2 →
      ∀ q : (FFModel.symDn 5).Mod,
        (∀ σ ∈ B, s1611e3_a5_sym5 σ q = q) →
          ∀ σ ∈ P, s1611e3_a5_sym5 σ q = q := by
    intro B hBP hrel q hqB σ hσP
    by_cases hBtop : B = P
    · subst hBtop
      exact hqB σ hσP
    have hrel2 : B.relIndex P = 2 := by
      have h0 : B.relIndex P ≠ 0 := by
        intro hz
        have hdvd := Subgroup.relIndex_dvd_card (H := B) (K := P)
        rw [hz] at hdvd
        haveI : Finite ↥P :=
          Finite.of_injective (fun x : ↥P => (x : Equiv.Perm (Fin 5))) Subtype.val_injective
        have hcard : Nat.card P ≠ 0 :=
          Nat.card_ne_zero.mpr ⟨⟨1, P.one_mem⟩, inferInstance⟩
        exact hcard (Nat.eq_zero_of_zero_dvd hdvd)
      have h1 : B.relIndex P ≠ 1 := by
        intro hone
        exact hBtop (le_antisymm hBP (Subgroup.relIndex_eq_one.mp hone))
      omega
    let BE : Subgroup (MulAut W) := (B.comap f).map E.subtype
    have hBE : BE ≤ E := Subgroup.map_subtype_le _
    have hmq : E3.mQuot E BE = 1 := by
      have hrelBE : BE.relIndex E = 2 := by
        have h3 : BE.relIndex E = (B.comap f).relIndex ⊤ := by
          have h := Subgroup.relIndex_map_map_of_injective (f := E.subtype)
            (B.comap f) ⊤ E.subtype_injective
          rw [Subgroup.map_top, Subgroup.range_subtype] at h
          exact h
        have h1 : (B.comap f).relIndex ⊤ = B.relIndex (Subgroup.map f (⊤ : Subgroup ↥E)) :=
          Subgroup.relIndex_comap (H := B) f ⊤
        have h2 : Subgroup.map f (⊤ : Subgroup ↥E) = P := rfl
        rw [h3, h1, h2, hrel2]
      unfold E3.mQuot
      rw [hrelBE]
      exact padicValNat_self
    obtain ⟨u, rfl⟩ := βs.surjective q
    have hfixBE : ∀ b ∈ BE, b (u : W) = (u : W) := by
      intro b hb
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hb
      have h2 : s1611e3_a5_sym5 (f e) (βs u) = βs u :=
        hqB (f e) (Subgroup.mem_comap.mp he)
      have h1 := f_spec e u
      rw [h2] at h1
      have h3 : s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u = u := βs.injective h1
      exact congrArg Subtype.val h3
    have huE : ∀ e ∈ E, e (u : W) = (u : W) :=
      hgoal' BE hBE hmq (u : W) u.2 hfixBE
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hσP
    have h2 : s1611e3_a5_res J (e : MulAut W) (hEJ e e.2) u = u := by
      apply Subtype.ext
      rw [s1611e3_a5_res_apply, huE e e.2]
    have h1 := f_spec e u
    rw [h2] at h1
    exact h1.symm
  exact s16c11_big_no_a2_odd (n := 5) (by norm_num) hPab hPne hB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
