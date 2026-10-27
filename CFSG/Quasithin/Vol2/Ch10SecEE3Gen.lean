module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Tau

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

section Factor

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem factor_gen (hβ : A5Equivariant θ β) {P : Subgroup (MulAut W)} (hPK : P ≤ K)
    (hP : ∀ g (hg : g ∈ K), g ∈ P ↔ θ ⟨g, hg⟩ ∈ eFour) {Y : Subgroup (MulAut W)} (hYP : Y ≤ P)
    (hY : Nat.card Y * Nat.card ↥(fixV Y ⊓ commV K) = 16) {x y : Bool}
    (h : ((θ.symm (pr x y) : ↥K) : MulAut W) ∈ Y) :
    (x = true → ((θ.symm sA : ↥K) : MulAut W) ∈ Y) ∧
      (y = true → ((θ.symm sB : ↥K) : MulAut W) ∈ Y) := by
  have crit := (factor_bound hβ hPK hP hYP).2.mp hY
  cases x <;> cases y
  · exact ⟨fun h' => absurd h' Bool.false_ne_true, fun h' => absurd h' Bool.false_ne_true⟩
  · rw [show pr false true = sB by decide] at h
    exact ⟨fun h' => absurd h' Bool.false_ne_true, fun _ => h⟩
  · rw [show pr true false = sA by decide] at h
    exact ⟨fun _ => h, fun h' => absurd h' Bool.false_ne_true⟩
  · rw [show pr true true = sA * sB by decide] at h
    have hA := crit h
    refine ⟨fun _ => hA, fun _ => ?_⟩
    have e : θ.symm sB = θ.symm sA * θ.symm (sA * sB) := by
      rw [← map_mul, show sA * (sA * sB) = sB by decide]
    rw [e, Subgroup.coe_mul]
    exact Y.mul_mem hA h

end Factor

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

open Classical in
@[expose] noncomputable def phi
    (X : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))) :
    Finset (Fin 4) :=
  Finset.univ.filter fun i => D.tau i ∈ X

theorem mem_phi {X : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))}
    {i : Fin 4} : i ∈ D.phi X ↔ D.tau i ∈ X := by
  classical
  simp [phi]

theorem eq_Yg_of_exact
    {X : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))}
    (hX : X ≤ D.P₁ ⊔ D.P₂)
    (heq : Nat.card X * Nat.card ↥(fixV X ⊓ (commV D.K₁ ⊔ commV D.K₂)) =
      Nat.card ↥(commV D.K₁ ⊔ commV D.K₂)) : X = D.Yg (D.phi X) := by
  refine le_antisymm (fun p hp => ?_) (D.Yg_le_of fun i hi => D.mem_phi.mp hi)
  obtain ⟨S, rfl⟩ := D.exists_tauS (hX hp)
  have hX' : X ≤ D.P₂ ⊔ D.P₁ := sup_comm D.P₁ D.P₂ ▸ hX
  have heq' : Nat.card X * Nat.card ↥(fixV X ⊓ (commV D.K₂ ⊔ commV D.K₁)) =
      Nat.card ↥(commV D.K₂ ⊔ commV D.K₁) := by
    rw [sup_comm (commV D.K₂)]; exact heq
  obtain ⟨hpo, hpo16⟩ := D.prodSetting.projOne_le_of_eq D.bound₁ D.bound₂ hX heq
  obtain ⟨hpt, hpt16⟩ := D.prodSetting.symm.projOne_le_of_eq D.bound₂ D.bound₁ hX' heq'
  rw [D.card_commV₁] at hpo16
  rw [D.card_commV₂] at hpt16
  have hcomm := D.comm _ (D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S)))).2 _
    (D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S)))).2
  have hP₁ : ((D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S))) : ↥D.K₁) : MulAut _) ∈ D.P₁ :=
    (D.memP₁ _ (D.θ₁.symm _).2).mpr (by simpa using pr_mem_eFour _ _)
  have hP₂ : ((D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S))) : ↥D.K₂) : MulAut _) ∈ D.P₂ :=
    (D.memP₂ _ (D.θ₂.symm _).2).mpr (by simpa using pr_mem_eFour _ _)
  have ha : ((D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S))) : ↥D.K₁) : MulAut _) ∈
      D.prodSetting.projOne X := by
    refine (D.prodSetting.symm.mem_projTwo_iff hX').mpr ⟨hP₁, _, hP₂, ?_⟩
    rw [← hcomm]
    exact hp
  have hb : ((D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S))) : ↥D.K₂) : MulAut _) ∈
      D.prodSetting.projTwo X :=
    (D.prodSetting.mem_projTwo_iff hX).mpr ⟨hP₂, _, hP₁, hp⟩
  have fa := factor_gen D.equiv₁ inf_le_left D.memP₁ (D.prodSetting.symm.projTwo_le X)
    hpo16 ha
  have fb := factor_gen D.equiv₂ inf_le_left D.memP₂ (D.prodSetting.projTwo_le X) hpt16 hb
  refine D.tauS_mem_Yg_iff.mpr fun i hi => D.mem_phi.mpr ?_
  fin_cases i
  · exact hpo (fa.1 (decide_eq_true hi))
  · exact hpo (fa.2 (decide_eq_true hi))
  · exact hpt (fb.1 (decide_eq_true hi))
  · exact hpt (fb.2 (decide_eq_true hi))

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
