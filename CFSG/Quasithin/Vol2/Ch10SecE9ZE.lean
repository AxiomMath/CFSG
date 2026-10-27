module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZD
public import CFSG.Quasithin.Vol2.Ch10SecA312R1Main
public import CFSG.Quasithin.Vol2.Ch10SecAT1Fix
public import CFSG.Quasithin.Vol2.Ch10SecE9T
public import CFSG.Quasithin.Vol2.Ch10SecE9W
public import CFSG.Quasithin.Vol2.Ch10SecE9X
public import CFSG.Quasithin.Vol2.Ch10SecE9Y
public import CFSG.Quasithin.Vol2.Ch10SecE9ZA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def E9PtFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) →
    ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P → PtCond T L I P →
      oTwoUpper P ≤ Subgroup.centralizer (quasithinOmegaOneCenter (T1 T L) : Set G)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem false_of_pt (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hF1 : Fact10_2_6Pair)
    (hKG : FactA312L32RankOne) (h : MaxCtx T L I t Ψ c) (h3 : Case10_1_1Three T L I)
    (hN3 : ∀ y ∈ Subgroup.normalizer (T1 T L : Set G), y ∈ fsuM T L → orderOf y ≠ 3)
    (hcop : ∀ d ∈ Subgroup.normalizer (T1 T L : Set G), Nat.Coprime (orderOf d) 6 →
      d ∈ fsuM T L)
    (hD : ParData A K E) (hD2 : ParData2 K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    (hcore : E9CoreSharp T L (preIn Ψ (A.prod A) ⊔ T))
    (hX : XOf T L Ψ A ≤ Subgroup.centralizer (quasithinOmegaOneCenter (T1 T L) : Set G)) :
    False := by
  obtain ⟨K₁, s, p, hs, hK₁, hsn, hK, hp, h24, ⟨e⟩, hbad, hST, ⟨y, hyK, hy3, hyT, -⟩, -, -⟩ :=
    hcore
  have : Fact p.Prime := ⟨hp⟩
  have hyp := h.hyp
  set W := quasithinOmegaOneCenter (T1 T L) with hW
  have hTP : T ≤ preIn Ψ (A.prod A) ⊔ T := le_sup_right
  have hTN := T1_normal h.h37 h.h38 hyp
  have hNW := normalizer_le_normalizer_omega (T1 T L)
  have hKW : K₁ ⊔ CFSG.conjugate K₁ s ≤ Subgroup.centralizer (W : Set G) := by
    rw [← hK]
    exact conjClosure_le_centralizer
      ⟨hTP, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTP⟩ hX
      (hTN.trans hNW) hNW
  have hC0 : fsuCVM T L I = ⊥ := by
    by_contra hne
    exact hN3 y hyT (le_fsuM_of_le_centralizer h331 h.h37 h.h38 hyp hne hKW hyK) hy3
  obtain ⟨hN₁, hN₂, hcomm, hwit⟩ :=
    core_bundle h311 h hD hD2 hA hs hK₁ hsn hK hp (by omega) e hbad hST
  obtain ⟨v, hvU, hvC, hvT⟩ := SecA.exists_mem_centralizer_T1_of_fsuCVM_eq_bot hyp hC0
  have hv1 : v ≠ 1 := fun h1 => hvC (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hcommV, helem, -, h4, -⟩ := hyp.three
  have hvVM : v ∈ fsuVM T L I := SecA.fsuUL_le_fsuVM T L I hvU
  have hv2 : v ^ 2 = 1 := helem.2 v hvVM
  have hvV : v ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (hcommV.is_comm.comm ⟨u, hu⟩ ⟨v, hvVM⟩)
  have hvT1 : v ∈ T1 T L :=
    SecA.inf_centralizer_le_T1 h.h37 h.h38 hyp ⟨SecA.fsuVM_le_T hyp hvVM, hvV⟩
  have hvW : v ∈ W := Subgroup.subset_closure ⟨⟨hvT1, hvT⟩, hv2⟩
  have hwit' : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
      ∃ z ∈ Subgroup.normalizer (T1 T L : Set G), z ∈ Subgroup.centralizer (W : Set G) ∧
        ¬ 3 ∣ orderOf (n * z⁻¹) := by
    intro n hn hodd
    obtain ⟨z, hzK, hzT, hzX⟩ := hwit n hn hodd
    refine ⟨z, hzT, hKW hzK, fun ⟨k, hk⟩ => ?_⟩
    have hcT : n * z⁻¹ ∈ Subgroup.normalizer (T1 T L : Set G) :=
      Subgroup.mul_mem _ hn (Subgroup.inv_mem _ hzT)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (orderOf_pos (n * z⁻¹)).ne' (by rw [hk, mul_zero])
    have hck : orderOf ((n * z⁻¹) ^ k) = 3 := by
      rw [orderOf_pow_of_dvd hk0 ⟨3, by rw [hk, mul_comm]⟩, hk, Nat.mul_div_cancel _ (by omega)]
    exact E9.false_of_normalizes_XOf h hD hD2 hck (Subgroup.pow_mem _ hcT k)
      (Subgroup.pow_mem _ hzX k)
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
    ⟨hTN, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTN⟩
  have hSv := isSylowTwoOf_centralizer h.h37 h.h38 hyp hC0
    (fun g hg => exists_acts_all hNW (SecA.le_fsuM T L) hTsyl
      (fun n hn hodd => exists_acts_of_odd hNW hcop hwit' hn hodd) hg) hvU hv1 hvW
    (fun τ hτ => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hvT τ hτ))
  have hsG₀ : s ∈ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right hs)
  have hK₂ : CFSG.conjugate K₁ s ∈
      cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj s⁻¹) hK₁
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ hsG₀))] at h1
  have hT1G₀ : T1 T L ≤ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    Subgroup.le_normalizer.trans le_sup_left
  obtain ⟨e₂⟩ := nonempty_modO2_conjugate K₁ s
  have hKv : K₁ ⊔ CFSG.conjugate K₁ s ≤ Subgroup.centralizer ({v} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hKW hk) v hvW).symm
  have hLt : CFSG.conjugate L t ≤ Subgroup.centralizer ({v} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ((h4 t h.ht h.htn).2.2 hvU) l hl)
  exact false_of_components hList hSL2 h36 h.h37 h.h38 h39 hF1 hKG hyp h3 h.ht hv1 hv2 hSv hLt
    (cComp_subset_lFamily hT1G₀ hK₁) (cComp_subset_lFamily hT1G₀ hK₂) hcomm hN₁ hN₂
    (le_sup_left.trans hKv) (le_sup_right.trans hKv) h24 e (e₂.trans e)

theorem gap10_2_5E9PtSharp_of_fix (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h322 : TmpL6_3_2_2_two)
    (h3210 : TmpL6_3_2_10_eight) (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (hF1 : Fact10_2_6Pair) (hFix : E9PtFix) : Gap10_2_5E9PtSharp := by
  intro G _ _ T L I hyp h3 hN3 P P' hP hTP hP' hTP' hne hc hc'
  obtain ⟨t, Ψ, c, h⟩ := exists_maxCtx h37 h38 hyp h3
  have hcop : ∀ d ∈ Subgroup.normalizer (T1 T L : Set G), Nat.Coprime (orderOf d) 6 →
      d ∈ fsuM T L := fun d hd hd6 => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcopP, -⟩ := hc
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcopP', -⟩ := hc'
    exact mem_fsuM_of_normalizes h hP hTP hP' hTP' hne (hcopP d hd hd6) (hcopP' d hd hd6)
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := fun hJ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨y, -, hy3, hyT, -⟩, -, -⟩ := hc
    exact hN3 y hyT (normalizer_T1_le_of_thompsonJ h3210 h1012 hyp hJ hyT) hy3
  obtain ⟨A, hA, hpt⟩ := exists_ptCond h h3 h1011 h322
  have hor : preIn Ψ (A.prod A) ⊔ T = P ∨ preIn Ψ (A.prod A) ⊔ T = P' := by
    rcases maximal_classify h37 h38 hyp h.ht h.htn h.hC hP hTP with h1 | h1 <;>
      rcases maximal_classify h37 h38 hyp h.ht h.htn h.hC hP' hTP' with h2 | h2 <;>
      rcases hA with rfl | rfl <;>
      first
        | exact Or.inl h1.symm
        | exact Or.inr h2.symm
        | exact absurd (h1.trans h2.symm) hne
  have hcore : E9CoreSharp T L (preIn Ψ (A.prod A) ⊔ T) := by
    rcases hor with h' | h' <;> rw [h'] <;> assumption
  have hmax : IsMaxSubgroupIn (fsuL0 T L ⊔ T) (preIn Ψ (A.prod A) ⊔ T) := by
    rcases hor with h' | h' <;> rw [h'] <;> assumption
  have hX := hFix G T L I hyp h3 hJ _ hmax le_sup_right hpt
  rcases hA with rfl | rfl
  · exact false_of_pt h311 h331 hList hSL2 h36 h39 hF1 factA312L32RankOne_holds h h3 hN3 hcop
      parData_a parData2_a (Or.inl rfl) hcore hX
  · exact false_of_pt h311 h331 hList hSL2 h36 h39 hF1 factA312L32RankOne_holds h h3 hN3 hcop
      parData_b parData2_b (Or.inr rfl) hcore hX

end CFSG.Quasithin.Vol2.Ch10.SecB
