module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaPolygon2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaMoufang
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Valency
public import CFSG.Quasithin.Recognition.Stroth.RootGroupLift

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

theorem degree_eq_of_isWeissEmbedding {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) {V : Type} [Fintype V] {Δ : SimpleGraph V}
    [DecidableRel Δ.Adj] {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V]
    [GraphAction D Δ] {u v : V} {ψ₁ : ↥P1 →* D} {ψ₂ : ↥P2 →* D} {ι : c.Γ → V}
    (hGP : IsGeneralizedPolygon Δ n) (hT : IsThick Δ) (hMΔ : MoufangCondition D Δ n)
    (hE : IsWeissEmbedding n c Δ u v ψ₁ ψ₂ ι)
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    (∃ e : ℕ, 1 ≤ e ∧ Δ.degree u = 2 ^ e + 1) ∧ (∃ e : ℕ, 1 ≤ e ∧ Δ.degree v = 2 ^ e + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hdu, hdv, -⟩ :=
    weissEmbeddingFacts n X P1 P2 Y c hn hc
      (show MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n from hM)
      V Δ D u v ψ₁ ψ₂ ι hGP hT hMΔ hE
  obtain ⟨e, he, hVe⟩ := hV1
  obtain ⟨f, hf, hVf⟩ := hV2
  exact ⟨⟨e, he, hdu.trans hVe⟩, ⟨f, hf, hdv.trans hVf⟩⟩

theorem exists_delta_of_goodPathSystem {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 3 ≤ n)
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph n) (hW : WeissFree c.G0 c.graph n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) < c.graph.egirth)
    (hv1 : 3 ≤ (P1 ⊓ P2).relIndex P1) (hv2 : 3 ≤ (P1 ⊓ P2).relIndex P2)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (hG : GoodPathSystem c.G0 c.graph n Good) :
    ∃ (V : Type) (_ : Fintype V) (Δ : SimpleGraph V) (_ : DecidableRel Δ.Adj)
      (D : Type) (_ : Group D) (_ : Finite D) (_ : MulAction D V) (_ : FaithfulSMul D V)
      (_ : GraphAction D Δ) (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V),
      IsGeneralizedPolygon Δ n ∧ IsThick Δ ∧ Δ.Adj u v ∧ MoufangCondition D Δ n ∧
        ψ₁.range ≤ MulAction.stabilizer D u ∧ ψ₂.range ≤ MulAction.stabilizer D v ∧
        IsWeissEmbedding n c Δ u v ψ₁ ψ₂ ι := by
  classical
  have hgirth' : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth := hgirth.le
  have hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w :=
    exists_adj_ne c hc hv1 hv2
  haveI hfin : Fintype ↥(edgeBall (n - 1) c) := Fintype.ofFinite _
  haveI hdec : DecidableRel (delta c Good n).Adj := Classical.decRel _
  have hthree : ∀ v w w' : c.Γ, c.graph.Adj v w → c.graph.Adj v w' →
      ∃ u, c.graph.Adj v u ∧ u ≠ w ∧ u ≠ w' := by
    intro v w w' _ _
    have hcard : 3 ≤ Nat.card (c.graph.neighborSet v) := by
      rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
      · rw [hv]; exact hv1
      · rw [hv]; exact hv2
    have hcard' : 3 ≤ (c.graph.neighborSet v).ncard := by
      rwa [Nat.card_coe_set_eq] at hcard
    by_contra hcon
    have hsub : c.graph.neighborSet v ⊆ ({w, w'} : Set c.Γ) := by
      intro u hu
      by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      exact hcon ⟨u, hu, hmem.1, hmem.2⟩
    have hle : (c.graph.neighborSet v).ncard ≤ ({w, w'} : Set c.Γ).ncard :=
      Set.ncard_le_ncard hsub
    have h2 : ({w, w'} : Set c.Γ).ncard ≤ 2 :=
      (Set.ncard_insert_le w {w'}).trans (by rw [Set.ncard_singleton])
    omega
  have hGP : IsGeneralizedPolygon (delta c Good n) n :=
    isGeneralizedPolygon_delta hn hgirth' hG hdeg
  have hT : IsThick (delta c Good n) := isThick_delta hn hgirth' hG hthree
  have hbase : (delta c Good n).Adj (deltaXv c n) (deltaLv c n) :=
    delta_adj_deltaXv_deltaLv hn
  haveI hGA : GraphAction ↥(deltaGroup hn hgirth' hG hdeg) (delta c Good n) :=
    graphAction_deltaGroup hn hgirth' hG hdeg
  have hMΔ : MoufangCondition ↥(deltaGroup hn hgirth' hG hdeg) (delta c Good n) n :=
    moufangCondition_delta hn hgirth' hG hdeg hM
  have hstab1 : (psiOne hn hgirth' hG hdeg).range ≤
      MulAction.stabilizer ↥(deltaGroup hn hgirth' hG hdeg) (deltaXv c n) :=
    psiOne_range_le_stabilizer hn hgirth' hG hdeg
  have hstab2 : (psiTwo hn hgirth' hG hdeg).range ≤
      MulAction.stabilizer ↥(deltaGroup hn hgirth' hG hdeg) (deltaLv c n) :=
    psiTwo_range_le_stabilizer hn hgirth' hG hdeg
  let iota : c.Γ → ↥(edgeBall (n - 1) c) :=
    fun w => if h : w ∈ edgeBall (n - 1) c then ⟨w, h⟩ else deltaXv c n
  have hiota_of_mem : ∀ {w : c.Γ} (hw : w ∈ edgeBall (n - 1) c), iota w = ⟨w, hw⟩ := by
    intro w hw
    simpa using dif_pos hw
  have hxv : c.xv ∈ edgeBall (n - 1) c := Or.inl (by simp)
  have hlv : c.lv ∈ edgeBall (n - 1) c := Or.inr (by simp)
  have hE0x : iota c.xv = deltaXv c n := by
    rw [hiota_of_mem hxv]
    exact Subtype.ext rfl
  have hE0y : iota c.lv = deltaLv c n := by
    rw [hiota_of_mem hlv]
    exact Subtype.ext rfl
  have hE1 : Set.BijOn iota (edgeBall (n - 1) c) Set.univ := by
    refine ⟨fun w _ => Set.mem_univ _, ?_, ?_⟩
    · intro w hw w' hw' heq
      rw [hiota_of_mem hw, hiota_of_mem hw'] at heq
      exact congrArg Subtype.val heq
    · intro y _
      exact ⟨(y : c.Γ), y.2, hiota_of_mem y.2⟩
  have hE2 : ∀ w w', w ∈ edgeBall (n - 2) c → w' ∈ edgeBall (n - 1) c →
      ((delta c Good n).Adj (iota w) (iota w') ↔ c.graph.Adj w w') := by
    intro w w' hw hw'
    have hw1 : w ∈ edgeBall (n - 1) c := by
      rcases hw with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hh : height c w ≤ n - 2 := by
      have h := height_le_of_mem_edgeBall (n := n - 1) hw
      omega
    rw [hiota_of_mem hw1, hiota_of_mem hw']
    exact delta_adj_iff_of_height_le hn hgirth' hG (u := ⟨w, hw1⟩) (v := ⟨w', hw'⟩) hh
  have hE3x : ∀ (g : ↥P1) (h : ↥(c.φ1.range ⊔ c.φ2.range)), (h : Y) = c.φ1 g →
      ∀ w, c.graph.dist c.xv w ≤ n - 1 →
        psiOne hn hgirth' hG hdeg g • iota w = iota (h • w) := by
    intro g h hh w hw
    have hh' : h = (RankTwoAmalgam.Completion.f1 (c := c) g : c.G0) := by
      apply Subtype.ext
      show (h : Y) = c.φ1 g
      exact hh
    subst h
    have hwmem : w ∈ edgeBall (n - 1) c := Or.inl hw
    have hmem : (RankTwoAmalgam.Completion.f1 (c := c) g : c.G0) • w ∈
        edgeBall (n - 1) c := by
      refine Or.inl ?_
      rw [GPath.dist_smul_fix (CosetGeom.connected rfl)
        (RankTwoAmalgam.Completion.f1_smul_xv g) w]
      exact hw
    have hf1 : (f1Stab (c := c) g : c.G0) = RankTwoAmalgam.Completion.f1 (c := c) g := rfl
    have hsmul : (psiOne hn hgirth' hG hdeg g • iota w : ↥(edgeBall (n - 1) c)) =
        ⟨(RankTwoAmalgam.Completion.f1 (c := c) g : c.G0) • w, hmem⟩ := by
      apply Subtype.ext
      rw [Subgroup.smul_def, psiOne_apply, hiota_of_mem hwmem, Equiv.Perm.smul_def,
        hatX_apply_of_dist_le hn hgirth' hG (a := f1Stab (c := c) g) hw, hf1]
    rw [hsmul, hiota_of_mem hmem]
  have hE3y : ∀ (g : ↥P2) (h : ↥(c.φ1.range ⊔ c.φ2.range)), (h : Y) = c.φ2 g →
      ∀ w, c.graph.dist c.lv w ≤ n - 1 →
        psiTwo hn hgirth' hG hdeg g • iota w = iota (h • w) := by
    intro g h hh w hw
    have hh' : h = (RankTwoAmalgam.Completion.f2 (c := c) g : c.G0) := by
      apply Subtype.ext
      show (h : Y) = c.φ2 g
      exact hh
    subst h
    have hwmem : w ∈ edgeBall (n - 1) c := Or.inr hw
    have hmem : (RankTwoAmalgam.Completion.f2 (c := c) g : c.G0) • w ∈
        edgeBall (n - 1) c := by
      refine Or.inr ?_
      rw [GPath.dist_smul_fix (CosetGeom.connected rfl)
        (RankTwoAmalgam.Completion.f2_smul_lv g) w]
      exact hw
    have hf2 : (f2Stab (c := c) g : c.G0) = RankTwoAmalgam.Completion.f2 (c := c) g := rfl
    have hsmul : (psiTwo hn hgirth' hG hdeg g • iota w : ↥(edgeBall (n - 1) c)) =
        ⟨(RankTwoAmalgam.Completion.f2 (c := c) g : c.G0) • w, hmem⟩ := by
      apply Subtype.ext
      rw [Subgroup.smul_def, psiTwo_apply, hiota_of_mem hwmem, Equiv.Perm.smul_def,
        hatY_apply_of_dist_le hn hgirth' hG (a := f2Stab (c := c) g) hw, hf2]
    rw [hsmul, hiota_of_mem hmem]
  have hagree : ∀ g : ↥(P1 ⊓ P2),
      psiOne hn hgirth' hG hdeg
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
        psiTwo hn hgirth' hG hdeg
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g) := by
    intro g
    have h1 : (f1Stab (c := c)
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) : c.G0) =
        (f2Stab (c := c)
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g) : c.G0) := by
      apply Subtype.ext
      show c.φ1 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
        c.φ2 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g)
      calc c.φ1 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g)
          = c.φ12 g := c.comm1 g
        _ = c.φ2 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g) :=
            (c.comm2 g).symm
    have ha : ((f1Stab (c := c)
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) : c.G0) • c.lv = c.lv) := by
      rw [h1]
      exact RankTwoAmalgam.Completion.f2_smul_lv _
    have hb : ((f2Stab (c := c)
          (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g) : c.G0) • c.xv = c.xv) := by
      rw [← h1]
      exact RankTwoAmalgam.Completion.f1_smul_xv _
    apply Subtype.ext
    apply Equiv.ext
    intro u
    apply Subtype.ext
    rw [psiOne_apply, psiTwo_apply,
      hatX_of_smul_eq hn hgirth' hG _ ha, hatY_of_smul_eq hn hgirth' hG _ hb, h1]
  have hgen : (psiOne hn hgirth' hG hdeg).range ⊔ (psiTwo hn hgirth' hG hdeg).range = ⊤ := by
    refine Subgroup.map_injective (Subgroup.subtype_injective _) ?_
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype]
    refine le_antisymm (sup_le (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)) ?_
    change Subgroup.closure ((hatXHom hn hgirth' hG hdeg).range ∪
      (hatYHom hn hgirth' hG hdeg).range) ≤
        (psiOne hn hgirth' hG hdeg).range.map (Subgroup.subtype _) ⊔
          (psiTwo hn hgirth' hG hdeg).range.map (Subgroup.subtype _)
    rw [Subgroup.closure_le]
    intro f hf
    rcases hf with hf | hf
    · obtain ⟨a, rfl⟩ := hf
      have ha : (a : c.G0) ∈ (RankTwoAmalgam.Completion.f1 (c := c)).range := by
        rw [f1_range_eq_stabilizer_xv c]
        exact a.2
      obtain ⟨g, hg⟩ := ha
      let g' : ↥P1 := g
      have hg' : RankTwoAmalgam.Completion.f1 (c := c) g' = (a : c.G0) := hg
      have hpsi : ((psiOne hn hgirth' hG hdeg g' : ↥(deltaGroup hn hgirth' hG hdeg)) :
          Equiv.Perm ↥(edgeBall (n - 1) c)) = hatXHom hn hgirth' hG hdeg a := by
        rw [psiOne_apply, hatXHom_apply,
          show f1Stab (c := c) g' = a from Subtype.ext hg']
      exact Subgroup.mem_sup_left ⟨psiOne hn hgirth' hG hdeg g', ⟨g', rfl⟩, hpsi⟩
    · obtain ⟨a, rfl⟩ := hf
      have ha : (a : c.G0) ∈ (RankTwoAmalgam.Completion.f2 (c := c)).range := by
        rw [f2_range_eq_stabilizer_lv c]
        exact a.2
      obtain ⟨g, hg⟩ := ha
      let g' : ↥P2 := g
      have hg' : RankTwoAmalgam.Completion.f2 (c := c) g' = (a : c.G0) := hg
      have hpsi : ((psiTwo hn hgirth' hG hdeg g' : ↥(deltaGroup hn hgirth' hG hdeg)) :
          Equiv.Perm ↥(edgeBall (n - 1) c)) = hatYHom hn hgirth' hG hdeg a := by
        rw [psiTwo_apply, hatYHom_apply,
          show f2Stab (c := c) g' = a from Subtype.ext hg']
      exact Subgroup.mem_sup_right ⟨psiTwo hn hgirth' hG hdeg g', ⟨g', rfl⟩, hpsi⟩
  refine ⟨↥(edgeBall (n - 1) c), hfin, delta c Good n, hdec,
    ↥(deltaGroup hn hgirth' hG hdeg), inferInstance,
    finite_deltaGroup hn hgirth' hG hdeg, inferInstance,
    faithfulSMul_deltaGroup hn hgirth' hG hdeg, hGA, deltaXv c n, deltaLv c n,
    psiOne hn hgirth' hG hdeg, psiTwo hn hgirth' hG hdeg, iota, hGP, hT, hbase, hMΔ,
    hstab1, hstab2, ?_⟩
  exact ⟨psiOne_injective hn hgirth' hG hW hdeg hc,
    psiTwo_injective hn hgirth' hG hW hdeg hc, hagree, hgen, hE0x, hE0y, hE1, hE2,
    hE3x, hE3y⟩

end CFSG.Quasithin.Stroth.WeissDelta

end
