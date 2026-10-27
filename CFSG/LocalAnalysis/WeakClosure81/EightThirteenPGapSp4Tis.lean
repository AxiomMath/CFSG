module

import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4TisAux1
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix CFSG.LieType.Universal.SpecialLinear

@[expose] noncomputable def sp4Z {F : Type} [Field F] (b c : F) : StatedSp 2 F :=
  tau (sym2_transpose b c 0)

variable {F : Type} [Field F]

private lemma wcgapst_coe_sp4Z (b c : F) :
    (((sp4Z b c : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 (sym2 b c 0) 0 1 := by
  rw [sp4Z, coe_tau]

private lemma wcgapst_sp4Z_add (b c b' c' : F) :
    sp4Z b c * sp4Z b' c' = sp4Z (b + b') (c + c') := by
  rw [sp4Z, sp4Z, sp4Z, tau_mul_tau]
  refine tau_congr _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2, add_comm, add_left_comm]

private lemma wcgapst_sp4Z_zero : sp4Z (0 : F) 0 = 1 := by
  apply statedSp_ext
  rw [wcgapst_coe_sp4Z]
  rw [show sym2 (0 : F) 0 0 = 0 from by ext i j; fin_cases i <;> fin_cases j <;> simp [sym2],
    fromBlocks_one]
  rfl

private lemma wcgapst_sp4Z_injective {b c b' c' : F} (h : sp4Z b c = sp4Z b' c') :
    b = b' ∧ c = c' := by
  have h' : sym2 b c 0 = sym2 b' c' 0 := by
    apply tau_injective (sym2_transpose b c 0) (sym2_transpose b' c' 0)
    show sp4Z b c = sp4Z b' c'
    exact h
  exact ⟨by simpa [sym2] using congrFun₂ h' 0 0, by simpa [sym2] using congrFun₂ h' 0 1⟩

private lemma wcgapst_sp4Z_mem_unipotent (b c : F) : sp4Z b c ∈ unipotent 2 F :=
  tau_mem_unipotent (sym2_transpose b c 0)

private lemma wcgapst_sp4Z_mem_center_iff [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {g : StatedSp 2 F} :
    g ∈ unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
        Set (StatedSp 2 F)) ↔ ∃ b c : F, g = sp4Z b c := by
  have hcenter := (unique_symplectic_four_Sylow_center (K := F) 4 hF).2.2.2.2.2.2.2.1
  constructor
  · rintro ⟨hU, hC⟩
    have hmem : (⟨g, hU⟩ : unipotent 2 F) ∈ Subgroup.center (unipotent 2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC y y.2)
    obtain ⟨b, c, hbc⟩ := (hcenter ⟨g, hU⟩).mp hmem
    exact ⟨b, c, hbc⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨wcgapst_sp4Z_mem_unipotent b c, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hmem : (⟨sp4Z b c, wcgapst_sp4Z_mem_unipotent b c⟩ : unipotent 2 F) ∈
        Subgroup.center (unipotent 2 F) :=
      (hcenter _).mpr ⟨b, c, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)

private noncomputable def wcgapst_sp4XC : Subgroup (StatedSp 2 F) where
  carrier := {g | ∃ b : F, g = sp4Z b 0}
  one_mem' := ⟨0, wcgapst_sp4Z_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', by rw [wcgapst_sp4Z_add, zero_add]⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨-b, inv_eq_of_mul_eq_one_right (by
      rw [wcgapst_sp4Z_add, add_neg_cancel, add_zero, wcgapst_sp4Z_zero])⟩

private noncomputable def wcgapst_sp4XAB : Subgroup (StatedSp 2 F) where
  carrier := {g | ∃ c : F, g = sp4Z 0 c}
  one_mem' := ⟨0, wcgapst_sp4Z_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', by rw [wcgapst_sp4Z_add, zero_add]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, inv_eq_of_mul_eq_one_right (by
      rw [wcgapst_sp4Z_add, add_neg_cancel, add_zero, wcgapst_sp4Z_zero])⟩

private lemma wcgapst_card_sp4XC (hF : Nat.card F = 4) : Nat.card (wcgapst_sp4XC (F := F)) = 4 := by
  have hbij : Function.Bijective
      (fun b : F => (⟨sp4Z b 0, by exact ⟨b, rfl⟩⟩ : wcgapst_sp4XC (F := F))) := by
    refine ⟨fun b b' h => (wcgapst_sp4Z_injective (congrArg Subtype.val h)).1, ?_⟩
    rintro ⟨g, b, rfl⟩
    exact ⟨b, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hF]

private lemma wcgapst_card_sp4XAB (hF : Nat.card F = 4) :
    Nat.card (wcgapst_sp4XAB (F := F)) = 4 := by
  have hbij : Function.Bijective
      (fun c : F => (⟨sp4Z 0 c, by exact ⟨c, rfl⟩⟩ : wcgapst_sp4XAB (F := F))) := by
    refine ⟨fun c c' h => (wcgapst_sp4Z_injective (congrArg Subtype.val h)).2, ?_⟩
    rintro ⟨g, c, rfl⟩
    exact ⟨c, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hF]

private noncomputable def wcgapst_S_C : Subgroup (StatedSp 2 F) :=
  (unipotent 2 F).map (MulAut.conj (wcgapst_nC (F := F)))

private noncomputable def wcgapst_S_AB : Subgroup (StatedSp 2 F) :=
  (unipotent 2 F).map (MulAut.conj (wcgapst_nAB (F := F)))

private lemma wcgapst_isSylowIn_unipotent [Finite F] [CharP F 2] :
    IsSylowIn 2 (unipotent 2 F) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  rw [← hP]
  exact ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩

private lemma wcgapst_isSylowIn_map_conj {G : Type*} [Group G]
    {P : Subgroup G} (hP : IsSylowIn 2 P ⊤) (g : G) :
    IsSylowIn 2 (P.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine ⟨le_top, hP.isPGroup.map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have hidx : (P.map (MulAut.conj g).toMonoidHom).index = P.index :=
    Subgroup.index_map_equiv P (MulAut.conj g)
  rw [hidx, ← Subgroup.relIndex_top_right]
  exact hP.not_dvd_relIndex

private lemma wcgapst_isSylowIn_S_C [Finite F] [CharP F 2] :
    IsSylowIn 2 (wcgapst_S_C (F := F)) ⊤ := by
  rw [wcgapst_S_C]
  exact wcgapst_isSylowIn_map_conj (wcgapst_isSylowIn_unipotent (F := F))
    (wcgapst_nC (F := F))

private lemma wcgapst_isSylowIn_S_AB [Finite F] [CharP F 2] :
    IsSylowIn 2 (wcgapst_S_AB (F := F)) ⊤ := by
  rw [wcgapst_S_AB]
  exact wcgapst_isSylowIn_map_conj (wcgapst_isSylowIn_unipotent (F := F))
    (wcgapst_nAB (F := F))

private lemma wcgapst_coe_conj_sp4Z_nC [CharP F 2] (b c : F) :
    ((((wcgapst_nC (F := F))⁻¹ * sp4Z b c * wcgapst_nC (F := F) : StatedSp 2 F) :
        GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (fromBlocks 1 (sym2 b c 0) 0 1).submatrix wcgapst_wC wcgapst_wC := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  rw [wcgapst_coe_nC_inv, wcgapst_coe_sp4Z, wcgapst_coe_nC]
  rw [wcgapst_coe_permGL, wcgapst_coe_permGL]
  exact wcgapst_permMatrix_conj wcgapst_wC.symm _

private lemma wcgapst_coe_conj_sp4Z_nAB [CharP F 2] (b c : F) :
    ((((wcgapst_nAB (F := F))⁻¹ * sp4Z b c * wcgapst_nAB (F := F) : StatedSp 2 F) :
        GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (fromBlocks 1 (sym2 b c 0) 0 1).submatrix wcgapst_wAB wcgapst_wAB := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  rw [wcgapst_coe_nAB_inv, wcgapst_coe_sp4Z, wcgapst_coe_nAB]
  rw [wcgapst_coe_permGL, wcgapst_coe_permGL]
  exact wcgapst_permMatrix_conj wcgapst_wAB.symm _

private lemma wcgapst_conj_nC_sp4Z_long [CharP F 2] (b : F) :
    (wcgapst_nC (F := F))⁻¹ * sp4Z b 0 * wcgapst_nC (F := F) =
      tau (sym2_transpose 0 0 b) := by
  apply statedSp_ext
  rw [wcgapst_coe_conj_sp4Z_nC, coe_tau]
  ext i j
  rcases i with a | a <;> rcases j with b' | b' <;> fin_cases a <;> fin_cases b' <;>
    simp [Matrix.submatrix_apply, fromBlocks, sym2, wcgapst_wC]

private lemma wcgapst_conj_nAB_sp4Z_short [CharP F 2] (c : F) :
    (wcgapst_nAB (F := F))⁻¹ * sp4Z 0 c * wcgapst_nAB (F := F) = lam c := by
  apply statedSp_ext
  rw [wcgapst_coe_conj_sp4Z_nAB,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.coe_lam]
  ext i j
  rcases i with a | a <;> rcases j with b' | b' <;> fin_cases a <;> fin_cases b' <;>
    simp [Matrix.submatrix_apply, fromBlocks, sym2, wcgapst_wAB, unitri, CharTwo.neg_eq]

private lemma wcgapst_sp4Z_mem_S_C_iff [CharP F 2] (b c : F) :
    sp4Z b c ∈ wcgapst_S_C (F := F) ↔ c = 0 := by
  constructor
  · intro h
    rw [wcgapst_S_C, Subgroup.mem_map] at h
    obtain ⟨u, hu, hueq⟩ := h
    have hconj : (wcgapst_nC (F := F))⁻¹ * sp4Z b c * wcgapst_nC (F := F) = u := by
      change MulAut.conj (wcgapst_nC (F := F)) u = sp4Z b c at hueq
      rw [MulAut.conj_apply] at hueq
      rw [← hueq]; group
    have hU : (wcgapst_nC (F := F))⁻¹ * sp4Z b c * wcgapst_nC (F := F) ∈ unipotent 2 F := by
      rw [hconj]; exact hu
    rw [mem_unipotent] at hU
    obtain ⟨A, E, hA, -, hAE⟩ := hU
    have h2 := congrFun₂ (hAE.symm.trans (wcgapst_coe_conj_sp4Z_nC b c)) (Sum.inl 1) (Sum.inl 0)
    have h3 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
    have h5 : (blockMat A E) (Sum.inl 1) (Sum.inl 0) = A 1 0 := by
      simp [blockMat, fromBlocks]
    have h4 : (fromBlocks 1 (sym2 b c 0) 0 1).submatrix wcgapst_wC wcgapst_wC
        (Sum.inl 1) (Sum.inl 0) = c := by
      simp [Matrix.submatrix_apply, fromBlocks, sym2, wcgapst_wC]
    rw [h5, h3, h4] at h2
    exact h2.symm
  · intro hc
    rw [hc]
    rw [wcgapst_S_C, Subgroup.mem_map]
    refine ⟨tau (sym2_transpose 0 0 b), tau_mem_unipotent _, ?_⟩
    change MulAut.conj (wcgapst_nC (F := F)) (tau (sym2_transpose 0 0 b)) = sp4Z b 0
    rw [MulAut.conj_apply]
    rw [← wcgapst_conj_nC_sp4Z_long b]
    group

private lemma wcgapst_sp4Z_mem_S_AB_iff [CharP F 2] (b c : F) :
    sp4Z b c ∈ wcgapst_S_AB (F := F) ↔ b = 0 := by
  constructor
  · intro h
    rw [wcgapst_S_AB, Subgroup.mem_map] at h
    obtain ⟨u, hu, hueq⟩ := h
    have hconj : (wcgapst_nAB (F := F))⁻¹ * sp4Z b c * wcgapst_nAB (F := F) = u := by
      change MulAut.conj (wcgapst_nAB (F := F)) u = sp4Z b c at hueq
      rw [MulAut.conj_apply] at hueq
      rw [← hueq]; group
    have hU : (wcgapst_nAB (F := F))⁻¹ * sp4Z b c * wcgapst_nAB (F := F) ∈ unipotent 2 F := by
      rw [hconj]; exact hu
    rw [mem_unipotent] at hU
    obtain ⟨A, E, hA, -, hAE⟩ := hU
    have h2 := congrFun₂ (hAE.symm.trans (wcgapst_coe_conj_sp4Z_nAB b c)) (Sum.inr 1) (Sum.inl 1)
    have h3 : (fromBlocks 1 (sym2 b c 0) 0 1).submatrix wcgapst_wAB wcgapst_wAB
        (Sum.inr 1) (Sum.inl 1) = b := by
      simp [Matrix.submatrix_apply, fromBlocks, sym2, wcgapst_wAB]
    have h4 : (blockMat A E) (Sum.inr 1) (Sum.inl 1) = 0 := by
      simp [blockMat, fromBlocks]
    rw [h3, h4] at h2
    exact h2.symm
  · intro hb
    rw [hb]
    rw [wcgapst_S_AB, Subgroup.mem_map]
    refine ⟨lam c, lam_mem_unipotent c, ?_⟩
    change MulAut.conj (wcgapst_nAB (F := F)) (lam c) = sp4Z 0 c
    rw [MulAut.conj_apply]
    rw [← wcgapst_conj_nAB_sp4Z_short c]
    group

theorem sp4_tis_axes {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {A : Subgroup (StatedSp 2 F)}
    (hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (hA4 : Nat.card ↥A = 4) (hT : TISIn (⊤ : Subgroup (StatedSp 2 F)) A) :
    ((∃ g ∈ A, g ≠ 1 ∧ ∃ b : F, g = sp4Z b 0) → ∀ g, g ∈ A ↔ ∃ b : F, g = sp4Z b 0) ∧
    ((∃ g ∈ A, g ≠ 1 ∧ ∃ c : F, g = sp4Z 0 c) → ∀ g, g ∈ A ↔ ∃ c : F, g = sp4Z 0 c) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  constructor
  · rintro ⟨g, hgA, hg1, b, hgb⟩
    have hgS : g ∈ wcgapst_S_C (F := F) := by
      rw [hgb]
      exact (wcgapst_sp4Z_mem_S_C_iff b 0).mpr rfl
    have hne : A ⊓ wcgapst_S_C (F := F) ≠ ⊥ := by
      intro hbot
      have hmem : g ∈ (⊥ : Subgroup (StatedSp 2 F)) := by
        rw [← hbot]; exact ⟨hgA, hgS⟩
      exact hg1 (Subgroup.mem_bot.mp hmem)
    have hle : A ≤ wcgapst_S_C (F := F) := (hT _ (wcgapst_isSylowIn_S_C)).resolve_left hne
    have hAX : A ≤ wcgapst_sp4XC (F := F) := by
      intro h hh
      obtain ⟨b', c', hbc⟩ := (wcgapst_sp4Z_mem_center_iff hF).mp (hAZ hh)
      have hhS : h ∈ wcgapst_S_C (F := F) := hle hh
      have hc' : c' = 0 := (wcgapst_sp4Z_mem_S_C_iff b' c').mp (hbc ▸ hhS)
      exact ⟨b', by rw [hbc, hc']⟩
    have hAeq : A = wcgapst_sp4XC (F := F) :=
      Subgroup.eq_of_le_of_card_ge hAX (by rw [wcgapst_card_sp4XC hF, hA4])
    intro h
    rw [hAeq]
    exact Iff.rfl
  · rintro ⟨g, hgA, hg1, c, hgc⟩
    have hgS : g ∈ wcgapst_S_AB (F := F) := by
      rw [hgc]
      exact (wcgapst_sp4Z_mem_S_AB_iff 0 c).mpr rfl
    have hne : A ⊓ wcgapst_S_AB (F := F) ≠ ⊥ := by
      intro hbot
      have hmem : g ∈ (⊥ : Subgroup (StatedSp 2 F)) := by
        rw [← hbot]; exact ⟨hgA, hgS⟩
      exact hg1 (Subgroup.mem_bot.mp hmem)
    have hle : A ≤ wcgapst_S_AB (F := F) := (hT _ (wcgapst_isSylowIn_S_AB)).resolve_left hne
    have hAX : A ≤ wcgapst_sp4XAB (F := F) := by
      intro h hh
      obtain ⟨b', c', hbc⟩ := (wcgapst_sp4Z_mem_center_iff hF).mp (hAZ hh)
      have hhS : h ∈ wcgapst_S_AB (F := F) := hle hh
      have hb' : b' = 0 := (wcgapst_sp4Z_mem_S_AB_iff b' c').mp (hbc ▸ hhS)
      exact ⟨c', by rw [hbc, hb']⟩
    have hAeq : A = wcgapst_sp4XAB (F := F) :=
      Subgroup.eq_of_le_of_card_ge hAX (by rw [wcgapst_card_sp4XAB hF, hA4])
    intro h
    rw [hAeq]
    exact Iff.rfl

end CFSG.LocalAnalysis.WeakClosure81

end
