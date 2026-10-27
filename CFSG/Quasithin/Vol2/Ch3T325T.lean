module

public import CFSG.Quasithin.Vol2.Ch3T325R
public import CFSG.Quasithin.Vol2.Ch3D310C0
public import CFSG.Quasithin.Vol2.Ch3T325D
public import CFSG.Quasithin.Vol2.Ch3T325J
public import CFSG.Quasithin.Vol2.Ch3T325N

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace T325.Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem case_three_c0 (h316 : Theorem316Statement) (hD310 : D310C0)
    (h4 : Vol2.Ch11.TmpL6_3_2_2_four) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))]
    (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hV : V₀ ≠ conjClosure V₀ T) :
    V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
          ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 3 n) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* ↥(StatedSp 2 K)) ∧
          ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSp4 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n) ∨
        (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 6)) ∧
          ∃ _ : IsMulCommutative ↥V₀, AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 6) ∨
        (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
            Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 4 1) ∨
        (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
            Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
          ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 5 1) ∨
        (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 7)) ∧
          Nat.card V₀ = 2 ^ 4)) ∧
      (∃ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G)) ∧
      ∀ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G) →
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) = conjClosure V₀ T ∧
          conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t ∧ V₀ ⊓ CFSG.conjugate V₀ t = ⊥ ∧
          ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥ := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := conjClosure V₀ T with hVdef
  set VM := conjClosure V M with hVMdef
  have hV₀V : V₀ ≤ V := V₀_le_V T V₀
  have hVVM : V ≤ VM := V_le_VM T L V₀
  have hV₀VM : V₀ ≤ VM := hV₀V.trans hVVM
  have : IsMulCommutative ↥V₀ := isMulCommutative_of_le hV₀VM
  have hMW : M ≤ Subgroup.normalizer (VM : Set G) := M_le_NVM T L V₀
  have hLVM : L ≤ Subgroup.normalizer (VM : Set G) := Subgroup.le_normalizer.trans hMW
  have hTVM : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans hMW
  have hfix : fixV (autOn L VM) = ⊥ :=
    fixV_autOn_eq_bot (c.inf_centralizer_VM_eq_bot h4 hC) hLVM
  have hq : qhatOf (autOn M VM) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have h := qhatInt_VM_le h316 c
    exact_mod_cast h
  rcases hD310 _ _ _ _ _ _ (c.d3Std h316) rfl hq hfix with hstab | ⟨hlist, -, hsum⟩
  · exfalso
    apply hV
    refine le_antisymm hV₀V (conjClosure_le fun t ht v hv => ?_)
    have h1 := hstab (conjAct VM ⟨t, hTVM ht⟩) (Setup.mem_autOn_iff.mpr ⟨_, ht, rfl⟩)
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_stabSub hV₀VM _ h1) v).mp hv
  refine ⟨hC, ?_, ?_, fun t ht htn => ?_⟩
  · rw [hfix, inf_bot_eq] at hlist
    exact list_of_d310 hV₀V hVVM c.L_le_NV₀ c.L_le_NV hLVM hlist
  · by_contra hall
    push Not at hall
    exact hV (le_antisymm hV₀V (conjClosure_le fun t ht v hv =>
      (Subgroup.mem_normalizer_iff.mp (hall t ht) v).mp hv))
  have htinv : t⁻¹ ∈ Subgroup.normalizer (VM : Set G) := hTVM (T.inv_mem ht)
  have hτT : conjAct VM ⟨t⁻¹, htinv⟩ ∈ autOn T VM :=
    Setup.mem_autOn_iff.mpr ⟨_, T.inv_mem ht, rfl⟩
  have hτs : conjAct VM ⟨t⁻¹, htinv⟩ ∉ stabSub (V₀.subgroupOf VM) := by
    intro h
    apply htn
    have h1 := mem_normalizer_of_mem_stabSub hV₀VM htinv h
    simpa using (Subgroup.normalizer (V₀ : Set G)).inv_mem h1
  obtain ⟨⟨htop, hinf⟩, hniso⟩ := hsum _ hτT hτs
  rw [map_conjAct_inv_eq htinv, hfix, sup_bot_eq] at htop
  rw [map_conjAct_inv_eq htinv, hfix, sup_bot_eq, sup_bot_eq] at hinf
  rw [map_conjAct_inv_eq htinv, hfix, inf_bot_eq, inf_bot_eq] at hniso
  set W := CFSG.conjugate V₀ t with hWdef
  have htN : t ∈ Subgroup.normalizer (VM : Set G) := hTVM ht
  have hWVM : W ≤ VM := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htN x).mpr (hV₀VM (mem_conjugate_iff.mp hx))
  have hsum' : VM = V₀ ⊔ W := by
    have h1 := congrArg (Subgroup.map VM.subtype) htop
    rwa [map_subtype_top, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hV₀VM,
      Subgroup.map_subgroupOf_eq_of_le hWVM] at h1
  have hinf' : V₀ ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := hinf (show (⟨x, hV₀VM hx.1⟩ : ↥VM) ∈ V₀.subgroupOf VM ⊓ W.subgroupOf VM from hx)
    rw [Subgroup.mem_bot] at h1 ⊢
    exact congrArg Subtype.val h1
  have hWV : W ≤ V := fun x hx => by
    have h1 := mem_conjClosure (T.inv_mem ht) (mem_conjugate_iff.mp hx)
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hVM_eq : VM = V := le_antisymm (hsum'.le.trans (sup_le hV₀V hWV)) hVVM
  refine ⟨hVM_eq, hVM_eq.symm.trans hsum', hinf', fun hiso => hniso ?_⟩
  exact secIsoL_of_isXSectionIso₂ hV₀VM hWVM c.L_le_NV₀
    (le_normalizer_conjugate c.L_le_NV₀ (c.T_le_M ht)) hiso

end T325.Ctx

theorem stmt3_2_5_of_c0 (h316 : Theorem316Statement) (hD310 : D310C0) (h331 : Stmt3_3_1)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h4 : Vol2.Ch11.TmpL6_3_2_2_four) (h6 : Vol2.Ch11.TmpL6_3_2_2_six) (h56 : AsB56) :
    Stmt3_2_5 := by
  intro G _ _ T L V₀ hfsu hL
  have c := T325.Ctx.of h331 h3222 h3228 hfsu hL
  have : IsMulCommutative ↥(conjClosure V₀ T) := c.elemV.1
  have : IsMulCommutative
      ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := c.elemVM.1
  refine ⟨T325.qhat_V h316 c, T325.qhat_VM h316 c, ?_⟩
  by_cases hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · by_cases hV : V₀ = conjClosure V₀ T
    · exact Or.inr (Or.inl (c.case_two hC hV))
    · exact Or.inr (Or.inr (c.case_three_c0 h316 hD310 h4 hC hV))
  · exact Or.inl (c.case_one h56 h6 hC)

end CFSG.Quasithin.H13
