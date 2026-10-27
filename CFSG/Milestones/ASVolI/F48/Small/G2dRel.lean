module

public import CFSG.Milestones.ASVolI.F48.Small.Rel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF48s_apartment_nbr {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S) {u l : c.Γ}
    (hu : u ∈ S) : ∃ d ∈ S, c.graph.Adj u d ∧ d ≠ l := by
  obtain ⟨e⟩ := hS
  haveI : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨i, hi⟩ := e.surjective ⟨u, hu⟩
  have hone : ((1 : Fin (2 * m)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hu' : (e i).1 = u := by rw [hi]
  have hadj1 : c.graph.Adj u (e (i + 1)).1 := by
    have h := (e.map_rel_iff (a := i) (b := i + 1)).2 (by
      rw [SimpleGraph.cycleGraph_adj']
      right
      rw [add_sub_cancel_left, hone])
    rw [← hu']
    exact h
  have hadj2 : c.graph.Adj u (e (i - 1)).1 := by
    have h := (e.map_rel_iff (a := i) (b := i - 1)).2 (by
      rw [SimpleGraph.cycleGraph_adj']
      left
      rw [sub_sub_cancel, hone])
    rw [← hu']
    exact h
  have hne : (e (i + 1)).1 ≠ (e (i - 1)).1 := by
    intro h
    have h2 := e.injective (Subtype.ext h)
    have h3 : i + 1 - (i - 1) = 0 := by rw [h2, sub_self]
    have h4 : i + 1 - (i - 1) = 1 + 1 := by abel
    rw [h4] at h3
    have h5 := congrArg Fin.val h3
    rw [Fin.val_add, hone, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h5
    omega
  by_cases h : (e (i + 1)).1 = l
  · refine ⟨(e (i - 1)).1, (e (i - 1)).2, hadj2, fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨(e (i + 1)).1, (e (i + 1)).2, hadj1, h⟩

section


theorem burnsideF48s_g2d_rel (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {E : Type} [Group E]
    {M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2d p f ⊤ M₁ M₂)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.G2d.m) :
    ∃ (u v : ↥M₂) (w : ↥M₁), (u : E) ∉ M₁ ∧ (v : E) ∉ M₁ ∧ (w : E) ∉ M₂ ∧ u * u = 1 ∧
      v * v = 1 ∧ (β.φ2 u * β.φ1 w * β.φ2 v * (β.φ1 w)⁻¹) ^ 3 = 1 := by
  have hadj : β.graph.Adj β.xv β.lv := CosetGeom.adj_γ₀_γ₁
  have hsimp : IsSimplex β.graph ({β.xv, β.lv} : Set β.Γ) := Or.inr ⟨_, _, hadj, rfl⟩
  obtain ⟨Sig, hSig, hsub, -⟩ :=
    (burnside_as_F_4_14_of h45 h46 .G2d p f E ⊤ M₁ M₂ hyp Y β hβ hs).2 _ _ hsimp hsimp
  have hxS : β.xv ∈ Sig := hsub (Set.mem_insert _ _)
  have hlS : β.lv ∈ Sig := hsub (Set.mem_insert_of_mem _ rfl)
  obtain ⟨c, hcS, hxc, hcl⟩ := burnsideF48s_apartment_nbr β (by decide : 2 ≤ GLKind.G2d.m) hSig
    (l := β.lv) hxS
  obtain ⟨sl, sc, hsl, hsc, hrl, hrc, hstab, ⟨eS3⟩, -, hreg, -⟩ :=
    (burnside_as_F_4_15_of h45 h46 .G2d p f E ⊤ M₁ M₂ hyp Y β hβ hs).2.2.2 ⟨rfl, rfl⟩ Sig hSig
      hxS hlS c hxc hcS hcl
  have hxt : CosetGeom.vtype β.xv = false := CosetGeom.vtype_γ₀
  have huniq : ∀ w₁ w₂ : ↥(setStab β Sig), (w₁ : β.G0) • β.xv = β.xv →
      (w₂ : β.G0) • β.xv = β.xv → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂
    obtain ⟨w, -, hw⟩ := hreg β.xv hxS hxt β.xv hxS hxt
    exact (hw w₁ h₁).trans (hw w₂ h₂).symm
  have hone : ∀ s ∈ setStab β Sig, s • β.xv = β.xv → s = 1 := by
    intro s hs hsx
    have := huniq ⟨s, hs⟩ 1 hsx (one_smul _ _)
    exact congrArg Subtype.val this
  have hsl2 : sl * sl = 1 :=
    hone _ ((setStab β Sig).mul_mem hrl.2.1 hrl.2.1) (hrl.1 _ hxS)
  have hsc2 : sc * sc = 1 :=
    hone _ ((setStab β Sig).mul_mem hrc.2.1 hrc.2.1) (hrc.1 _ hxS)
  have hxl : β.xv ≠ β.lv := by
    intro h
    have := congrArg CosetGeom.vtype h
    rw [CosetGeom.vtype_γ₀, CosetGeom.vtype_γ₁] at this
    exact Bool.false_ne_true this
  have hxc' : β.xv ≠ c := hxc.ne
  have hnotfix : ∀ s ∈ setStab β Sig, Set.ncard {w : β.Γ | w ∈ Sig ∧ s • w = w} = 2 →
      s • β.xv ≠ β.xv := by
    intro s hs hcard hsx
    have hs1 := hone s hs hsx
    subst hs1
    have hfin : Set.Finite {w : β.Γ | w ∈ Sig ∧ (1 : β.G0) • w = w} :=
      Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num)
    have hsub3 : ({β.xv, β.lv, c} : Set β.Γ) ⊆ {w : β.Γ | w ∈ Sig ∧ (1 : β.G0) • w = w} := by
      rintro w (rfl | rfl | rfl)
      · exact ⟨hxS, one_smul _ _⟩
      · exact ⟨hlS, one_smul _ _⟩
      · exact ⟨hcS, one_smul _ _⟩
    have h3 : ({β.xv, β.lv, c} : Set β.Γ).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hcl.symm]
      rintro (h | h)
      · exact hxl h
      · exact hxc' h
    have := Set.ncard_le_ncard hsub3 hfin
    omega
  have hrel3 : (sl * sc) ^ 3 = 1 := by
    let Q := ↥(setStab β Sig)
    let σ : Q := ⟨sl, hrl.2.1⟩
    let τ : Q := ⟨sc, hrc.2.1⟩
    have hσ : σ * σ = 1 := Subtype.ext hsl2
    have hτ : τ * τ = 1 := Subtype.ext hsc2
    have hgen : Subgroup.closure ({σ, τ} : Set Q) = ⊤ := by
      apply Subgroup.map_injective (setStab β Sig).subtype_injective
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
      exact hstab.symm
    haveI : Finite Q := Finite.of_equiv _ eS3.symm.toEquiv
    have hcard : Nat.card Q = 2 * 3 := by
      rw [Nat.card_congr eS3.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have h := burnsideF48s_dihedral_pow hσ hτ hgen (by norm_num) hcard
    exact congrArg Subtype.val h
  let φ₁ : ↥M₁ →* β.G0 := f1 (c := β)
  let φ₂ : ↥M₂ →* β.G0 := f2 (c := β)
  have hf1inj : Function.Injective φ₁ := f1_injective β hβ
  have hf2inj : Function.Injective φ₂ := f2_injective β hβ
  obtain ⟨u, hu⟩ : sl ∈ φ₂.range := stv_lv_le_range_f2 β hsl
  obtain ⟨g, hgx, hgl⟩ := CosetGeom.exists_stab_smul_eq hadj hxc
  obtain ⟨w, hw⟩ : g ∈ φ₁.range := (stv_xv_eq_range β).le (MulAction.mem_stabilizer_iff.2 hgx)
  have hsc' : g⁻¹ * sc * g ∈ stv β β.lv := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgl,
      MulAction.mem_stabilizer_iff.1 hsc, ← hgl, inv_smul_smul]
  obtain ⟨v, hv⟩ : g⁻¹ * sc * g ∈ φ₂.range := stv_lv_le_range_f2 β hsc'
  have hsc_eq : sc = φ₁ w * φ₂ v * (φ₁ w)⁻¹ := by
    rw [hv, hw]
    group
  have hfix2 : ∀ z : ↥M₂, (z : E) ∈ M₁ → φ₂ z • β.xv = β.xv := by
    intro z hz
    have e : φ₂ z = φ₁ ⟨(z : E), hz⟩ :=
      (burnsideF48s_iota12_eq_f2 β ⟨(z : E), ⟨hz, z.2⟩⟩).symm
    rw [e]
    exact f1_smul_xv _
  refine ⟨u, v, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro huM
    exact hnotfix sl hrl.2.1 hrl.2.2.2 (by rw [← hu]; exact hfix2 u huM)
  · intro hvM
    apply hnotfix sc hrc.2.1 hrc.2.2.2
    rw [hsc_eq, hw, mul_smul, mul_smul, inv_smul_eq_iff.2 hgx.symm, hfix2 v hvM, hgx]
  · intro hwM
    apply hcl
    rw [← hgl, ← hw]
    have e : φ₁ w = φ₂ ⟨(w : E), hwM⟩ := burnsideF48s_iota12_eq_f2 β ⟨(w : E), ⟨w.2, hwM⟩⟩
    rw [e]
    exact f2_smul_lv _
  · apply hf2inj
    rw [map_mul, hu, map_one]
    exact hsl2
  · apply hf2inj
    rw [map_mul, map_one]
    have e : φ₂ v = (φ₁ w)⁻¹ * sc * φ₁ w := by rw [hsc_eq]; group
    rw [e]
    calc (φ₁ w)⁻¹ * sc * φ₁ w * ((φ₁ w)⁻¹ * sc * φ₁ w) = (φ₁ w)⁻¹ * (sc * sc) * φ₁ w := by group
      _ = 1 := by rw [hsc2]; group
  · have e : φ₂ u * φ₁ w * φ₂ v * (φ₁ w)⁻¹ = sl * sc := by
      rw [hu, hsc_eq]
      group
    have key : (φ₂ u * φ₁ w * φ₂ v * (φ₁ w)⁻¹) ^ 3 = 1 := by
      rw [e]
      exact hrel3
    exact congrArg (fun z : β.G0 => (z : Y)) key

end

end CFSG.ASVolI
