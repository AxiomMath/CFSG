module

public import CFSG.Milestones.ASVolI.F431.BUcDef
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMain

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.Un

theorem burnsideF4m_exists_model_yamStd {D : Type} [Group D] {f : ℕ} (hf1 : 1 ≤ f)
    (hD : CFSG.Blueprint.LieModel D .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (_ : CharP K 2),
      IsSimpleGroup (Xg h) ∧ Nonempty (D ≃* Xg h) ∧
      CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨hS, hY⟩ := yamStd_of_eps hF (brFD hF hf1) (brEps hF hf1) (brEps_map_Psy hF hf1)
  exact ⟨F, inferInstance, brFD hF hf1, inferInstance, hS,
    ⟨e.symm.trans (brEps hF hf1).symm⟩, hY⟩

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem burnsideF4m_center_Ssd_le (F₂ : Subgroup (K ≃+* K)) (w : MulAut (Xg h))
    (hw : w ∈ Ssd h (Psy h) (fStab_Psy h) F₂)
    (hc : ∀ y ∈ Ssd h (Psy h) (fStab_Psy h) F₂, y * w = w * y) :
    w ∈ Ssd h (ZX h) (fStab_ZX h) ⊥ := by
  have hfix : ∀ u ∈ Psy h, w u = u :=
    fun u hu => fix_of_comm_cj h (fun u hu => (hc _ (cj_mem_Ssd h hu)).symm) hu
  obtain ⟨a, haA, rfl⟩ := (fixes_miyamotoZ2_iff h w).1 fun g hg =>
    hfix g (miyamotoA1_le_P h (miyamotoZ2_le_A1 h hg))
  have haP : (a : GL (Fin 4) K) ∈ miyamotoP h := miyamotoA1_le_P h haA
  have haZ : (a : GL (Fin 4) K) ∈ miyamotoZ h := by
    rw [← centerIn_miyamotoP]
    refine ⟨haP, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyX : y ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false false hy
    have e := hfix ⟨y, hyX⟩ hy
    have e2 : a * ⟨y, hyX⟩ = ⟨y, hyX⟩ * a := by
      rw [MulAut.conj_apply] at e
      have := congrArg (fun x => x * a) e
      simpa [mul_assoc] using this
    exact (congrArg Subtype.val e2).symm
  exact cj_mem_Ssd h haZ

theorem burnsideF4m_ZX_eq_of_q2 (hf : f = 1) {a : Xg h} (ha : a ∈ ZX h) (ha1 : a ≠ 1) :
    a = z1X h := by
  obtain ⟨d, hd, e⟩ := (mem_Z h).1 (show (a : GL (Fin 4) K) ∈ miyamotoZ h from ha)
  have hd2 : d ^ 2 = d := by
    rw [UnitaryFieldData.bar_apply, hf, pow_one] at hd
    exact hd
  have h3 : d * (d - 1) = 0 := by linear_combination hd2
  rcases mul_eq_zero.1 h3 with h0 | h1
  · subst h0
    exact absurd (Subtype.ext (e.trans (miyamotoXGL_zero h))) ha1
  · have : d = 1 := sub_eq_zero.1 h1
    subst this
    exact Subtype.ext (e.trans (coe_z1X h).symm)

theorem burnsideF4m_Ssd_le_autStab_Pt [IsSimpleGroup (Xg h)] (hPt : IsCoatom (Pt h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)} (hF : F₂ ≤ FK h K₀) :
    Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab (Pt h) := by
  intro x hx
  have hx' : x ∈ Ssd h (Pt h) (fStab_Pt h) (FK h K₀) := Ssd_mono h (Psy_le_Pt h) hF hx
  rw [← inf_autStab_Pt h hPt hinn] at hx'
  exact hx'.2

theorem burnsideF4m_Ssd_le_autStab_Ln [IsSimpleGroup (Xg h)] (hLn : IsCoatom (Ln h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)} (hF : F₂ ≤ FK h K₀) :
    Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab (Ln h) := by
  intro x hx
  have hx' : x ∈ Ssd h (Ln h) (fStab_Ln h) (FK h K₀) := Ssd_mono h (Psy_le_Ln h) hF hx
  rw [← inf_autStab_Ln h hLn hinn] at hx'
  exact hx'.2

end CFSG.Quasithin.H13.F431.Un.OL

namespace CFSG.Quasithin.H13.F431.Un

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Un.OL
  CFSG.Quasithin.H13.F431.D4q.Struct

theorem burnsideF4m_unCenterProp_four_one : burnsideF4m_UnCenterProp 4 1 := by
  intro D _ hD A _
  obtain ⟨K, _, h, _, _, ⟨e⟩, hY⟩ := burnsideF4m_exists_model_yamStd le_rfl hD
  obtain ⟨A', hTD, hP, ⟨L⟩⟩ := exists_unNormalized h hY e A
  have hsup : A'.P1 ⊔ A'.P2 = ⊤ := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
    · rw [h1, h2, sup_comm]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
  have hinn := A'.range_conj_le_K hsup
  have := finite_aut h
  obtain ⟨F₂, hF₂⟩ := exists_isSylowTwoOf (FK h A'.K)
  have hsyl := isSylowTwoOf_Ssd_Psy h hinn hF₂
  have hPt := burnsideF4m_Ssd_le_autStab_Pt h hY.coatom₀ hinn hF₂.1
  have hLn := burnsideF4m_Ssd_le_autStab_Ln h hY.coatom₁ hinn hF₂.1
  have hT1 : Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab A'.P1 := by
    rcases hP with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    exacts [hPt, hLn]
  have hT2 : Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab A'.P2 := by
    rcases hP with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    exacts [hLn, hPt]
  refine burnsideF4m_unCenterConcl_of_kiso L
    (burnsideF4m_unCenterConcl_of_model A' hsyl hT1 hT2 (hinn ⟨z1X h, rfl⟩) ?_)
  intro w hw hc hw1
  obtain ⟨a, ha, φ, hφ, rfl⟩ := burnsideF4m_center_Ssd_le h F₂ w hw hc
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one] at hw1 ⊢
  have ha1 : a ≠ 1 := fun e => hw1 (by rw [e, cj_one])
  rw [burnsideF4m_ZX_eq_of_q2 h rfl ha ha1]
  exact ⟨1, A'.K.one_mem, by rw [one_mul, inv_one, mul_one]⟩

theorem burnsideF4m_unCenterProp_four_all (f : ℕ) : burnsideF4m_UnCenterProp 4 f := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · interval_cases f
    · intro D _ hD
      exact absurd hD.admissible.2.1 (by norm_num)
    · exact burnsideF4m_unCenterProp_four_one
  · exact burnsideF4m_unCenterProp_of_outLie (f431UnOutLieProp_four f hf)

end CFSG.Quasithin.H13.F431.Un
