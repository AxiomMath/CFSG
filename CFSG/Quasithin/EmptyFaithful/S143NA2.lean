module

public import CFSG.Quasithin.EmptyFaithful.S143NA
public import CFSG.Quasithin.EmptyFaithful.S143LC

public section

namespace CFSG.Quasithin.S143

namespace A6Model

theorem model_main3
    {R1 R2 N1 N2 Y : Mat4} (hR1 : IsRMat R1) (hR2 : IsRMat R2) (hR : RHypM R1 R2)
    (hN1 : IsUMat N1) (hN2 : IsUMat N2) (hU : UHypL [I4, R1, R2, mm R1 R2] N1 N2)
    (hY : IsYMat Y) (hYH : YHypM N1 N2 Y) :
    ∃ cm : Mat4, ModelConcl R1 R2 N1 N2 Y cm ∧
      ∃ (Vl Vr : List (Equiv.Perm (Fin 6))) (s : Equiv.Perm (Fin 6)), Conf6Plus cm Vl Vr s ∧
        (∀ σ ∈ Vl, ∃ P ∈ [I4, N1, N2, mm N1 N2], mm cm (matOf6 σ) = mm P cm) ∧
        ∀ σ ∈ Vr, ∃ P ∈ [I4, R1, R2, mm R1 R2], mm cm (matOf6 σ) = mm P cm := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := hR1.exists_Rpar
  obtain ⟨b0, b1, b2, b3, rfl⟩ := hR2.exists_Rpar
  obtain ⟨p0, p1, p2, p3, p4, rfl⟩ := hN1.exists_Upar
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := hN2.exists_Upar
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, rfl⟩ := hY.exists_Ypar
  have hRc := stageR a0 a1 a2 a3 b0 b1 b2 b3 hR
  have hmem : ∀ P, P ∈ Rstd4 ↔
      P ∈ [I4, Rpar a0 a1 a2 a3, Rpar b0 b1 b2 b3, mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3)] := by
    intro P
    constructor
    · exact hRc.2.2.2.2 P
    · intro hP
      have h1 := hRc.1
      simp only [Rstd4, List.mem_cons, List.not_mem_nil, or_false] at h1 hP ⊢
      rcases hP with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · rcases h1.1 with h | h | h <;> simp [h]
      · rcases h1.2.1 with h | h | h <;> simp [h]
      · rcases h1.2.2 with h | h | h <;> simp [h]
  have hU' : UHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 := by
    unfold UHyp
    exact (UHypL_congr (fun P => (hmem P).symm) _ _).mp hU
  have hYc := stageY p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 hU' y0 y1 y2 y3 y4 y5 y6 y7 y8 hYH
  have hRok : ∀ P ∈ [I4, Rpar a0 a1 a2 a3, Rpar b0 b1 b2 b3,
      mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3)], P ∈ Rstd4 := fun P hP => (hmem P).mpr hP
  obtain ⟨hd1, hd2, hd3⟩ := hYc.2
  have hd1' := mat4Eq_false_iff.mpr hd1
  have hd2' := mat4Eq_false_iff.mpr hd2
  have hd3' := mat4Eq_false_iff.mpr hd3
  rcases hYc.1 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hsubU : ∀ P ∈ [I4, Upar p0 p1 p2 p3 p4, Upar q0 q1 q2 q3 q4,
        mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)], P ∈ Uset1 := by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · simp [Uset1]
      · exact h1
      · exact h2
      · exact h3
    have hcov := cover1 _ h1 _ h2 hd1' hd2' hd3'
    refine ⟨c1, ⟨fun v w h => cInj1' v w h, fun P hP => ok1 P ?_, fun P hP => ok1 P ?_,
      ok1 _ List.mem_cons_self, ok1 _ ?_, closure1 _ h4, ?_⟩, Vl1, Vr1, Equiv.swap 3 4, conf6plus_one, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ (hRok P hP)))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hsubU P hP))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ h4))
    · intro P hP hPU hP1 P' hP' hP'U hP'1
      rcases inter1 P (hRok P hP) (hsubU P hPU) with a | a
      · exact absurd a hP1
      · rcases inter1 P' (hRok P' hP') (hsubU P' hP'U) with b | b
        · exact absurd b hP'1
        · exact a.trans b.symm
    · intro σ hσ
      obtain ⟨P, hP, hPm⟩ := uCorr1 σ hσ
      exact ⟨P, memM_iff.mp (hcov P hP), mat4Eq_iff.mp hPm⟩
    · intro σ hσ
      obtain ⟨P, hP, hPm⟩ := rCorr1 σ hσ
      exact ⟨P, (hmem P).mp hP, mat4Eq_iff.mp hPm⟩
  · have hsubU : ∀ P ∈ [I4, Upar p0 p1 p2 p3 p4, Upar q0 q1 q2 q3 q4,
        mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)], P ∈ Uset2 := by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · simp [Uset2]
      · exact h1
      · exact h2
      · exact h3
    have hcov := cover2 _ h1 _ h2 hd1' hd2' hd3'
    refine ⟨c2, ⟨fun v w h => cInj2' v w h, fun P hP => ok2 P ?_, fun P hP => ok2 P ?_,
      ok2 _ List.mem_cons_self, ok2 _ ?_, closure2 _ h4, ?_⟩, Vl2, Vr2, Equiv.swap 0 4, conf6plus_two, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ (hRok P hP)))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hsubU P hP))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ h4))
    · intro P hP hPU hP1 P' hP' hP'U hP'1
      rcases inter2 P (hRok P hP) (hsubU P hPU) with a | a
      · exact absurd a hP1
      · rcases inter2 P' (hRok P' hP') (hsubU P' hP'U) with b | b
        · exact absurd b hP'1
        · exact a.trans b.symm
    · intro σ hσ
      obtain ⟨P, hP, hPm⟩ := uCorr2 σ hσ
      exact ⟨P, memM_iff.mp (hcov P hP), mat4Eq_iff.mp hPm⟩
    · intro σ hσ
      obtain ⟨P, hP, hPm⟩ := rCorr2 σ hσ
      exact ⟨P, (hmem P).mp hP, mat4Eq_iff.mp hPm⟩


end A6Model

end CFSG.Quasithin.S143

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section KModel3

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

theorem Setup.exists_KModel3
    : ∃ (y : G) (cm : Mat4) (Vl Vr : List (Equiv.Perm (Fin 6)))
    (s : Equiv.Perm (Fin 6)), KModel hS cm y ∧ Conf6Plus cm Vl Vr s ∧
      (∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm) ∧
      ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm := by
  obtain ⟨R1, R2, hR1, hR2, hRH, hR⟩ := hS.exists_RHyp htT htRQ
  obtain ⟨N1, N2, hN1, hN2, hUH, hU⟩ := hS.exists_UHyp htT htRQ hR
  obtain ⟨y, hyH, hyN, hy3, hyM, hYH, hodd⟩ := hS.exists_YHyp hU
  obtain ⟨cm, ⟨hcm, hRok', hUok', hxok, hyok, hcl, hinter⟩, Vl, Vr, s, hconf, hVl, hVr⟩ :=
    model_main3 hR1 hR2 hRH hN1 hN2 hUH hyM hYH
  rw [← hS.cmat_x] at hxok hcl
  have hRok : ∀ γ ∈ rOf T M, A6ok cm (cmat z a r r1 γ) := fun γ hγ =>
    hRok' _ ((hR _).mpr ⟨γ, hγ, rfl⟩)
  have hUok : ∀ u ∈ uOfL22 T M, A6ok cm (cmat z a r r1 u) := fun u hu =>
    hUok' _ ((hU _).mpr ⟨u, hu, rfl⟩)
  have hinter' : ∀ γ₁ ∈ rOf T M, ∀ u₁ ∈ uOfL22 T M, ∀ γ₂ ∈ rOf T M, ∀ u₂ ∈ uOfL22 T M,
      cmat z a r r1 γ₁ = cmat z a r r1 u₁ → cmat z a r r1 γ₁ ≠ I4 →
        cmat z a r r1 γ₂ = cmat z a r r1 u₂ → cmat z a r r1 γ₂ ≠ I4 →
          cmat z a r r1 γ₁ = cmat z a r r1 γ₂ := by
    intro γ₁ hγ₁ u₁ hu₁ γ₂ hγ₂ u₂ hu₂ h1 h1' h2 h2'
    refine hinter _ ((hR _).mpr ⟨γ₁, hγ₁, rfl⟩) ((hU _).mpr ⟨u₁, hu₁, h1.symm⟩) h1' _
      ((hR _).mpr ⟨γ₂, hγ₂, rfl⟩) ((hU _).mpr ⟨u₂, hu₂, h2.symm⟩) h2'
  have hB := hS.basis
  have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
  have hUN : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun u hu => c.iTwo_le_normalizer_Ac hrW hrV hr2 (le_conjClosure _ _ hu)
  have hRG : rOf T M ≤ GoodSub hB cm := fun γ hγ => mem_GoodSub_of_A6ok hB (hRN hγ) (hRok γ hγ)
  have hUG : uOfL22 T M ≤ GoodSub hB cm := fun u hu => mem_GoodSub_of_A6ok hB (hUN u hu) (hUok u hu)
  have hxG : x ∈ GoodSub hB cm :=
    mem_GoodSub_of_A6ok hB (c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo) hxok
  have hyG : y ∈ GoodSub hB cm := mem_GoodSub_of_A6ok hB hyN hyok
  have hLG : yOfL22 T M ≤ GoodSub hB cm :=
    (c.yOfL22_le_rOf_sup_zpowers hS.x_mem hS.x_ord).trans
      (sup_le hRG (Subgroup.zpowers_le.mpr hxG))
  have hOG : oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ≤
      GoodSub hB cm :=
    (c.oTwoUpper_inf_normalizer_le_sup hrW hrV hr2 hyH hy3 hodd).trans
      (sup_le hUG (Subgroup.zpowers_le.mpr hyG))
  have hyodd : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact hy3)
    exact Odd.of_dvd_nat (by decide) hdvd
  refine ⟨y, cm, Vl, Vr, s, ⟨hcm, sup_le hOG hLG, (le_sup_right : yOfL22 T M ≤ _) hS.x_mem, ?_, hyN,
    hcl, hinter'⟩, hconf, ?_, ?_⟩
  · exact (le_sup_left : oTwoUpper _ ≤ _) (mem_oTwoUpper_of_odd ⟨hyH, hyN⟩ hyodd)
  · intro σ hσ
    obtain ⟨P, hP, hPm⟩ := hVl σ hσ
    obtain ⟨u, hu, hPu⟩ := (hU P).mp hP
    exact ⟨u, hu, by rw [hPu]; exact hPm⟩
  · intro σ hσ
    obtain ⟨P, hP, hPm⟩ := hVr σ hσ
    obtain ⟨ρ', hρ', hPρ⟩ := (hR P).mp hP
    exact ⟨ρ', hρ', by rw [hPρ]; exact hPm⟩


end KModel3

end S143

end CFSG.Quasithin
