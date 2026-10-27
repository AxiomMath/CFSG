module

public import CFSG.Quasithin.Background.H156Ind

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.ASVolI.ChH

theorem beta3_surj_UT (w : Wn 3) : ∃ u ∈ UT, beta3 u = w := by
  obtain ⟨y, hy, rfl⟩ := toW_surj 3 w
  have : ∀ y < 8, ∃ m ∈ uTMasks, actM c3 m = y := by decide +kernel
  obtain ⟨m, hm, hmy⟩ := this y hy
  exact ⟨toW 11 m, (toW_mem_UT_iff (uTMasks_lt m hm)).2 hm, by rw [beta3_toW, hmy]⟩

theorem beta3_inj_UT {u : W11} (hu : u ∈ UT) (h : beta3 u = 1) : u = 1 := by
  obtain ⟨m, hm, rfl⟩ := hu
  have hlt : m < 2 ^ 11 := combos_lt uTBasis_lt m hm
  have hmem : m ∈ uTMasks := (uT_combos m hlt).1 hm
  rw [beta3_toW, ← toW_zero 3] at h
  have h0 : actM c3 m = 0 := toW_inj (actM_lt c3_lt m) (by decide) h
  have : ∀ m ∈ uTMasks, actM c3 m = 0 → m = 0 := by decide +kernel
  rw [this m hmem h0, toW_zero]

theorem psiSpec_unique {g : MulAut W11} {a a' : GL (Fin 3) (ZMod 2)} {c c' : GL (Fin 2) (ZMod 2)}
    (h : PsiSpec g a c) (h' : PsiSpec g a' c') : a = a' ∧ c = c' := by
  refine ⟨natHom_injective 3 ?_, natHom_injective 2 ?_⟩
  · refine MulEquiv.ext fun w => ?_
    obtain ⟨u, hu, rfl⟩ := beta3_surj_UT w
    exact (h.1 u hu).symm.trans (h'.1 u hu)
  · refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := beta2_surjective w
    exact (h.2.1 x).symm.trans (h'.2.1 x)

theorem good_exists (g : ↥GoodSub) :
    ∃ p : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2), PsiSpec g.1 p.1 p.2 := by
  obtain ⟨-, -, a, c, h⟩ := g.2
  exact ⟨(a, c), h⟩

@[expose] noncomputable def psi0 (g : ↥GoodSub) : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) :=
  Classical.choose (good_exists g)

theorem psi0_spec (g : ↥GoodSub) : PsiSpec g.1 (psi0 g).1 (psi0 g).2 :=
  Classical.choose_spec (good_exists g)

theorem psi0_eq {g : ↥GoodSub} {a : GL (Fin 3) (ZMod 2)} {c : GL (Fin 2) (ZMod 2)}
    (h : PsiSpec g.1 a c) : psi0 g = (a, c) := by
  have := psiSpec_unique (psi0_spec g) h
  exact Prod.ext this.1 this.2

theorem psi0_one : psi0 (1 : ↥GoodSub) = 1 := by
  have h : PsiSpec ((1 : ↥GoodSub) : MulAut W11) 1 1 := by
    rw [OneMemClass.coe_one]
    exact psiSpec_one
  exact psi0_eq h

theorem psi0_mul (g h : ↥GoodSub) : psi0 (g * h) = psi0 g * psi0 h := by
  have hh : PsiSpec ((g * h : ↥GoodSub) : MulAut W11) (psi0 g * psi0 h).1 (psi0 g * psi0 h).2 := by
    rw [Subgroup.coe_mul]
    exact psiSpec_mul h.2.1 h.2.2.1 (psi0_spec g) (psi0_spec h)
  exact psi0_eq hh

@[expose] noncomputable def Psi0 : ↥GoodSub →* GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) where
  toFun := psi0
  map_one' := psi0_one
  map_mul' := psi0_mul

theorem Psi0_spec (g : ↥GoodSub) : PsiSpec g.1 (Psi0 g).1 (Psi0 g).2 := psi0_spec g

theorem Psi0_eq {g : ↥GoodSub} {a : GL (Fin 3) (ZMod 2)} {c : GL (Fin 2) (ZMod 2)}
    (h : PsiSpec g.1 a c) : Psi0 g = (a, c) := psi0_eq h

theorem gA_stab_UT : gA ∈ stabSub UT := img11_trQ_stab rhoTrA_mem

theorem gB_stab_UT : gB ∈ stabSub UT := img11_trQ_stab rhoTrB_mem

theorem gT3_stab_UT : gT3 ∈ stabSub UT := rho_t3_mem_stabSub

theorem gT2_stab_UT : gT2 ∈ stabSub UT := rho_t2_mem_stabSub

theorem gA_stab_V9 : gA ∈ stabSub V9 := mem_stabSub_V9 actsBy_gA (by decide +kernel)

theorem gB_stab_V9 : gB ∈ stabSub V9 := mem_stabSub_V9 actsBy_gB (by decide +kernel)

theorem gT3_stab_V9 : gT3 ∈ stabSub V9 := mem_stabSub_V9 actsBy_gT3 (by decide +kernel)

theorem gT2_stab_V9 : gT2 ∈ stabSub V9 := mem_stabSub_V9 actsBy_gT2 (by decide +kernel)

theorem closure_genSet_le_good : Subgroup.closure genSet ≤ GoodSub := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · exact ⟨gA_stab_UT, gA_stab_V9, aA, cA, psiSpec_gA⟩
  · exact ⟨gB_stab_UT, gB_stab_V9, aB, cB, psiSpec_gB⟩
  · exact ⟨gT3_stab_UT, gT3_stab_V9, aT3, cT3, psiSpec_gT3⟩
  · exact ⟨gT2_stab_UT, gT2_stab_V9, aT2, cT2, psiSpec_gT2⟩

theorem H_le_good :
    img11 stabUTP ≤ GoodSub := by
  rw [img11_stabUTP]
  exact closure_genSet_le_good

end CFSG.Quasithin.H156
