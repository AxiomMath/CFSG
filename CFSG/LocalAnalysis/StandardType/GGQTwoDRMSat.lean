module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBar
public import CFSG.LocalAnalysis.StandardType.GGQTwoRMGlue

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Gen

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {𝒦 : Finset (Subgroup G)}

omit [Finite G] in
theorem qtwoD_reflGen_of_weyl {A : Subgroup (MulAut ↥Bs)} (h : GGWeylReflectionGroup 3 A) :
    GGReflGenerated 3 A := by
  obtain ⟨ι, M, -, f, hf⟩ := h
  apply le_antisymm
  · intro a ha
    obtain ⟨w, hwa⟩ := f.surjective ⟨a, ha⟩
    have hae : a = ((f w : ↥A) : MulAut ↥Bs) := by rw [hwa]
    rw [hae]
    have htop : Subgroup.closure (Set.range M.simple) = (⊤ : Subgroup M.Group) :=
      PresentedGroup.closure_range_of M.relationsSet
    have hw : w ∈ Subgroup.closure (Set.range M.simple) := by
      rw [htop]
      trivial
    refine Subgroup.closure_induction (p := fun w _ => ((f w : ↥A) : MulAut ↥Bs) ∈
        Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection 3 φ}) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨(f (M.simple i)).2, hf i⟩
    · simp
    · intro u v _ _ hu hv
      simpa using Subgroup.mul_mem _ hu hv
    · intro u _ hu
      simpa using Subgroup.inv_mem _ hu
  · exact (Subgroup.closure_le _).mpr fun φ hφ => hφ.1

theorem qtwoD_ainf_reflGen (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) :
    GGReflGenerated 3 (ggAInf 3 B Bs x L D J) := by
  have hgenK := reflGen_of_routeCfg hcfg
  have hgenL := qtwoD_reflGen_of_weyl hAL
  have hle : ∀ {K : Subgroup G}, ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J →
      GGReflGenerated 3 (ggAutomizer K Bs) →
      ggAutomizer K Bs ≤ Subgroup.closure {φ | φ ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 φ} :=
    fun {K} hK hgen => by
      conv_lhs => rw [hgen]
      exact Subgroup.closure_mono fun φ ⟨hφ, hr⟩ => ⟨hK hφ, hr⟩
  apply le_antisymm
  · rw [ggAInf]
    refine sup_le (hle le_sup_left hgenL)
      (iSup_le fun y => iSup_le fun K => iSup_le fun hK => ?_)
    exact hle (ggAutomizer_le_ggAInf_of_nbr hK) (hgenK y K hK)
  · exact (Subgroup.closure_le _).mpr fun φ hφ => hφ.1

end Gen

section Sat

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {𝒦 : Finset (Subgroup G)} {m : ℕ}

theorem qtwoD_saturation (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 4 ≤ m)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs)) (β : Additive ↥Bs ≃+ DVec m)
    (hsel : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven m) (hx : x ∈ Bs)
    (hsat : ∀ a ∈ ggInduced ⊤ Bs, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
      a ∈ ggAutomizer L Bs ∨
        ∃ i : Fin m, ∀ b : ↥Bs, β (Additive.ofMul (a b)) = dNeg m i (β (Additive.ofMul b))) :
    ∀ a ∈ ggAInf 3 B Bs x L D J, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
      (∃ g ∈ ggAInf 3 B Bs x L D J, ∃ r ∈ ggAutomizer L Bs, GGIsReflection 3 r ∧
        a = g * r * g⁻¹) → a ∈ ggAutomizer L Bs := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  rintro a ha hr hfix ⟨g, hg, r, hrA, hrr, hgr⟩
  rcases hsat a (ggRM_ainf_le_induced ha) hr hfix with h | ⟨i, hi⟩
  · exact h
  · exfalso
    have hjoin : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf 3 B Bs x L D J :=
      qTwoGlobSel_join_le_ggAInf hcfg
    have hW : dEven m ≤ qTwoBarA B Bs L D J x β := by
      rw [← hsel]
      exact Subgroup.map_mono hjoin
    have hTF : ∀ g ∈ qTwoBarA B Bs L D J x β, g ≠ 1 →
        ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) :=
      fun g hg => qTwo_bar_notr B Bs L D J x β hcfg.1.2.2.2.1 hg
    have hgen : qTwoBarA B Bs L D J x β =
        Subgroup.closure {t | t ∈ qTwoBarA B Bs L D J x β ∧ GGLinRefl t} := by
      have h1 := qtwoD_ainf_reflGen hcfg hAL
      apply le_antisymm
      · calc qTwoBarA B Bs L D J x β
            = (Subgroup.closure {φ | φ ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 φ}).map
              (ggLin (p := 3) β) := by
              change (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) β) = _
              rw [← h1]
          _ = Subgroup.closure (ggLin (p := 3) β ''
              {φ | φ ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 φ}) :=
              MonoidHom.map_closure _ _
          _ ≤ _ := by
              refine Subgroup.closure_mono ?_
              rintro t ⟨φ, ⟨hφA, hφr⟩, rfl⟩
              exact ⟨Subgroup.mem_map_of_mem _ hφA,
                (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) β φ).mp hφr⟩
      · exact (Subgroup.closure_le _).mpr fun t ht => ht.1
    have hrmem : ggLin (p := 3) β r ∈ dEven m := by
      rw [← hsel]
      exact Subgroup.mem_map_of_mem _ (by
        have : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
        exact this hrA)
    have hrefl : GGLinRefl (ggLin (p := 3) β r) :=
      (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) β r).mp hrr
    have hneg : ggLin (p := 3) β a = dNeg m i := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, v = β (Additive.ofMul b) :=
        ⟨Additive.toMul (β.symm v), by simp⟩
      rw [ggLin_apply_ofMul]
      exact hi b
    apply qtwoD_not_conj_neg hm hW hTF hgen
      (g := ggLin (p := 3) β g) (Subgroup.mem_map_of_mem _ hg) hrmem hrefl i
    rw [← map_mul, ← map_inv, ← map_mul, ← hgr]
    exact hneg

end Sat

end CFSG.StandardType.QTwo

end
