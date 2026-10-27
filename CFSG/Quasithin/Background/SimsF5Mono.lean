module

public import CFSG.Quasithin.Background.SimsF5Form
public import CFSG.Quasithin.Background.SimsF5Klein
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open
open scoped Pointwise

theorem mono_xvec_apply (i k : Fin 6) : xvec i k = if k = i then 1 else 0 := by
  simp [xvec, Pi.single_apply]

theorem mono_xvec_ne_zero (i : Fin 6) : xvec i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [mono_xvec_apply] at this

theorem mono_xvec_inj {i j : Fin 6} (h : xvec i = xvec j) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [mono_xvec_apply, hij] at this

theorem mono_qV_xvec (i : Fin 6) : qV (xvec i) = if i = 5 then -1 else 1 := by
  fin_cases i <;> decide

theorem mono_qV_smul (c : ZMod 3) (v : V6) : qV (c • v) = c ^ 2 * qV v := by
  simp only [qV, Pi.smul_apply, smul_eq_mul]; ring

theorem mono_bil_xvec :
    ∀ i j : Fin 6, bil (xvec i) (xvec j) = if i = j then 2 * qV (xvec i) else 0 := by
  decide

theorem mono_mulVec_inj (g : GL6) {u v : V6}
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) :
    u = v := by
  have h2 := congrArg (fun w => ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
  exact h2

theorem mono_inv_mulVec (g : GL6) (v : V6) :
    ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mono_mulVec_inv (g : GL6) (v : V6) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mono_eJ_val (J : Finset (Fin 6)) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal (eJd J) := rfl

theorem mono_eJd_apply (J : Finset (Fin 6)) (i : Fin 6) :
    eJd J i = if i ∈ J then -1 else 1 := rfl

theorem mono_eJ_mulVec (J : Finset (Fin 6)) (x : V6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x = fun k => eJd J k * x k := by
  funext k
  rw [mono_eJ_val, Matrix.mulVec_diagonal]

theorem mono_eJ_mulVec_xvec (J : Finset (Fin 6)) (i : Fin 6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = eJd J i • xvec i := by
  rw [mono_eJ_mulVec]
  funext k
  by_cases hk : k = i
  · subst hk; simp [mono_xvec_apply]
  · simp [mono_xvec_apply, hk]

theorem mono_eJd_symmDiff (J K : Finset (Fin 6)) (i : Fin 6) :
    eJd (symmDiff J K) i = eJd J i * eJd K i := by
  simp only [mono_eJd_apply]
  by_cases h1 : i ∈ J <;> by_cases h2 : i ∈ K <;> simp [Finset.mem_symmDiff, h1, h2] <;> decide

theorem mono_eJ_mul (J K : Finset (Fin 6)) : eJ J * eJ K = eJ (symmDiff J K) := by
  apply Units.ext
  show Matrix.diagonal (eJd J) * Matrix.diagonal (eJd K) = Matrix.diagonal (eJd (symmDiff J K))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mono_eJd_symmDiff]

theorem mono_eJ_empty : eJ ∅ = 1 := by
  apply Units.ext
  show Matrix.diagonal (eJd ∅) = 1
  rw [← Matrix.diagonal_one]
  congr 1

theorem mono_eJ_mul_self (J : Finset (Fin 6)) : eJ J * eJ J = 1 := by
  rw [mono_eJ_mul, symmDiff_self, Finset.bot_eq_empty, mono_eJ_empty]

theorem mono_eJ_comm (J K : Finset (Fin 6)) : eJ J * eJ K = eJ K * eJ J := by
  rw [mono_eJ_mul, mono_eJ_mul, symmDiff_comm]

theorem mono_eJ_injective : Function.Injective eJ := by
  intro J K h
  ext i
  have h2 := congrArg (fun g : GL6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) i i) h
  simp only [mono_eJ_val, Matrix.diagonal_apply_eq] at h2
  simp only [mono_eJd_apply] at h2
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K
  · exact iff_of_true hJ hK
  · simp only [hJ, hK, if_true, if_false] at h2; exact absurd h2 (by decide)
  · simp only [hJ, hK, if_true, if_false] at h2; exact absurd h2 (by decide)
  · exact iff_of_false hJ hK

@[expose] def monoReflX (a : Fin 6) : ReflVec := ⟨xvec a, qV_xvec_ne_zero a⟩

theorem mono_reflOf_reflX (a : Fin 6) : reflOf (monoReflX a) = eJ {a} := by
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  rw [mono_eJ_mulVec]
  show (refl6 (xvec a) (qV_xvec_ne_zero a) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x = _
  rw [refl6_xvec_mulVec]
  funext k
  by_cases hk : k = a
  · subst hk; simp [mono_eJd_apply]
  · simp [mono_eJd_apply, hk, Function.update_apply]

theorem mono_exists_list (J : Finset (Fin 6)) :
    ∃ l : List ReflVec, (l.map reflOf).prod = eJ J ∧ l.length = J.card ∧
      l.countP (fun v => qV v.1 = -1) = if (5 : Fin 6) ∈ J then 1 else 0 := by
  induction J using Finset.induction_on with
  | empty => exact ⟨[], by simp [mono_eJ_empty], by simp, by simp⟩
  | insert a J ha ih =>
    obtain ⟨l, hl, hlen, hcnt⟩ := ih
    refine ⟨monoReflX a :: l, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, hl, mono_reflOf_reflX, mono_eJ_mul]
      congr 1
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hi : i = a
      · subst hi; simp [ha]
      · simp [hi]
    · rw [List.length_cons, hlen, Finset.card_insert_of_notMem ha]
    · rw [List.countP_cons, hcnt]
      have hq : qV (monoReflX a).1 = -1 ↔ a = 5 := by
        rw [show (monoReflX a).1 = xvec a from rfl, mono_qV_xvec]
        by_cases h : a = 5 <;> simp [h] <;> decide
      by_cases h5 : a = 5
      · subst h5; simp [monoReflX, mono_qV_xvec, ha]
      · simp [hq, h5, Finset.mem_insert, Ne.symm h5]

theorem mono_eJ_mem_MDot_iff (J : Finset (Fin 6)) :
    eJ J ∈ MDot ↔ Even J.card ∧ (5 : Fin 6) ∉ J := by
  obtain ⟨l, hl, hlen, hcnt⟩ := mono_exists_list J
  rw [← hl, prod_refl_mem_MDot_iff, hlen, hcnt]
  by_cases h : (5 : Fin 6) ∈ J <;> simp [h]

@[expose] def monoDiag : Subgroup GL6 where
  carrier := {g | ∃ J : Finset (Fin 6), g = eJ J}
  mul_mem' := by
    rintro _ _ ⟨J, rfl⟩ ⟨K, rfl⟩
    exact ⟨_, mono_eJ_mul J K⟩
  one_mem' := ⟨∅, mono_eJ_empty.symm⟩
  inv_mem' := by
    rintro _ ⟨J, rfl⟩
    exact ⟨J, inv_eq_of_mul_eq_one_right (mono_eJ_mul_self J)⟩

theorem mono_Qset_eq :
    {g : GL6 | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J} =
      ((MDot ⊓ monoDiag : Subgroup GL6) : Set GL6) := by
  ext g
  constructor
  · rintro ⟨J, hJ, hev, rfl⟩
    refine ⟨(mono_eJ_mem_MDot_iff J).2 ⟨hev, fun h5 => ?_⟩, ⟨J, rfl⟩⟩
    have := hJ h5
    revert this
    decide
  · rintro ⟨hM, J, rfl⟩
    obtain ⟨hev, h5⟩ := (mono_eJ_mem_MDot_iff J).1 hM
    refine ⟨J, fun i hi => ?_, hev, rfl⟩
    have hne : i ≠ 5 := fun h => h5 (h ▸ hi)
    have : ∀ i : Fin 6, i ≠ 5 → i ∈ Iset := by decide
    exact this i hne

theorem mono_Q2Dot_eq : Q2Dot = MDot ⊓ monoDiag := by
  unfold Q2Dot
  rw [mono_Qset_eq]
  exact Subgroup.closure_eq _

theorem Q2Dot_coe :
    (Q2Dot : Set GL6) = {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J} := by
  rw [mono_Q2Dot_eq, mono_Qset_eq]

theorem mono_mem_Q2Dot_iff (g : GL6) :
    g ∈ Q2Dot ↔ g ∈ MDot ∧ ∃ J : Finset (Fin 6), g = eJ J := by
  rw [mono_Q2Dot_eq, Subgroup.mem_inf]
  rfl

theorem mono_Q2Dot_elim {g : GL6} (hg : g ∈ Q2Dot) : ∃ J : Finset (Fin 6), g = eJ J :=
  ((mono_mem_Q2Dot_iff g).1 hg).2

theorem mono_Q2Dot_le_MDot : Q2Dot ≤ MDot := by
  rw [mono_Q2Dot_eq]
  exact inf_le_left

theorem mono_eJ_mem_Q2Dot {J : Finset (Fin 6)} (hJ : J ⊆ Iset) (hev : Even J.card) :
    eJ J ∈ Q2Dot := by
  rw [← SetLike.mem_coe, Q2Dot_coe]
  exact ⟨J, hJ, hev, rfl⟩

theorem mono_card_Q2Dot : Nat.card ↥Q2Dot = 16 := by
  have hf : ∀ J : {J : Finset (Fin 6) // J ⊆ Iset ∧ Even J.card}, eJ J.1 ∈ Q2Dot :=
    fun J => mono_eJ_mem_Q2Dot J.2.1 J.2.2
  let f : {J : Finset (Fin 6) // J ⊆ Iset ∧ Even J.card} → ↥Q2Dot := fun J => ⟨eJ J.1, hf J⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro J K h
      exact Subtype.ext (mono_eJ_injective (congrArg Subtype.val h))
    · rintro ⟨g, hg⟩
      rw [← SetLike.mem_coe, Q2Dot_coe] at hg
      obtain ⟨J, hJ, hev, rfl⟩ := hg
      exact ⟨⟨J, hJ, hev⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem isEn_Q2Dot : IsEn 4 ↥Q2Dot := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    obtain ⟨J, hJ⟩ := mono_Q2Dot_elim a.2
    obtain ⟨K, hK⟩ := mono_Q2Dot_elim b.2
    apply Subtype.ext
    show (a : GL6) * b = b * a
    rw [hJ, hK]
    exact mono_eJ_comm J K
  · intro a
    obtain ⟨J, hJ⟩ := mono_Q2Dot_elim a.2
    apply Subtype.ext
    show (a : GL6) * a = 1
    rw [hJ]
    exact mono_eJ_mul_self J
  · rw [mono_card_Q2Dot]
    norm_num

theorem mono_smul_spn (g : GL6) (v : V6) : g • spn {v} = spn {g • v} := by
  unfold spn
  rw [Units.smul_def, Submodule.smul_span, Set.smul_set_singleton]
  rfl

theorem mono_smul_xvec (g : GL6) (v : V6) :
    g • v = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v := rfl

theorem mono_mem_stabilizer_Lambda {g : GL6} (τ : Equiv.Perm (Fin 6))
    (h : ∀ i, ∃ c : ZMod 3, c ≠ 0 ∧
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec (τ i)) :
    g ∈ MulAction.stabilizer GL6 Lambda := by
  rw [MulAction.mem_stabilizer_iff]
  have key : ∀ i, g • spn {xvec i} = spn {xvec (τ i)} := by
    intro i
    obtain ⟨c, hc, hci⟩ := h i
    rw [mono_smul_spn, mono_smul_xvec, hci]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) _
  ext S
  constructor
  · intro hS
    obtain ⟨T, ⟨i, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hS
    exact ⟨τ i, key i⟩
  · rintro ⟨j, rfl⟩
    exact Set.mem_smul_set.2 ⟨spn {xvec (τ.symm j)}, ⟨τ.symm j, rfl⟩, by rw [key]; simp⟩

theorem mono_line_map {g : GL6} (hg : g ∈ MulAction.stabilizer GL6 Lambda) (i : Fin 6) :
    ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec j := by
  have h1 : g • spn {xvec i} ∈ g • Lambda := Set.smul_mem_smul_set ⟨i, rfl⟩
  rw [MulAction.mem_stabilizer_iff.1 hg] at h1
  obtain ⟨j, hj⟩ := h1
  rw [mono_smul_spn] at hj
  have hmem : g • xvec i ∈ spn {xvec j} := by
    rw [← hj]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨j, c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  have h0 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    exact hc.symm
  exact mono_xvec_ne_zero i (mono_mulVec_inj g h0)

theorem mono_conj_diag {g : GL6} (hg : g ∈ MulAction.stabilizer GL6 Lambda) {d : GL6}
    (hd : ∀ j, ∃ e : ZMod 3,
      (d : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec j = e • xvec j) (i : Fin 6) :
    ∃ e : ZMod 3, ((g * d * g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      e • xvec i := by
  obtain ⟨j, c, hc, hgi⟩ := mono_line_map (inv_mem hg) i
  obtain ⟨e, he⟩ := hd j
  refine ⟨e, ?_⟩
  have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec j = c⁻¹ • xvec i := by
    have := mono_mulVec_inv g (xvec i)
    rw [hgi, Matrix.mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgi]
  simp only [Matrix.mulVec_smul, he, h1, smul_smul]
  congr 1
  rw [mul_right_comm, mul_inv_cancel₀ hc, one_mul]

theorem mono_eq_eJ_of_diag {g : GL6} (hg : g ∈ OVq)
    (h : ∀ i, ∃ c : ZMod 3, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec i) :
    ∃ J : Finset (Fin 6), g = eJ J := by
  choose c hc using h
  have hc1 : ∀ i, c i = 1 ∨ c i = -1 := by
    intro i
    have h1 := qV_mulVec_of_mem_OVq hg (xvec i)
    rw [hc i, mono_qV_smul] at h1
    have hq := qV_xvec_ne_zero i
    have h2 : c i ^ 2 = 1 := mul_right_cancel₀ hq (h1.trans (one_mul _).symm)
    have key : ∀ a : ZMod 3, a ^ 2 = 1 → a = 1 ∨ a = -1 := by decide
    exact key _ h2
  refine ⟨Finset.univ.filter (fun i => c i = -1), ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  show _ *ᵥ xvec i = _ *ᵥ xvec i
  rw [hc i, mono_eJ_mulVec_xvec]
  congr 1
  rw [mono_eJd_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hc1 i with h | h
  · rw [if_neg (by rw [h]; decide), h]
  · rw [if_pos h, h]

theorem Q2Dot_le_M2Dot : Q2Dot ≤ M2Dot := by
  intro g hg
  refine ⟨mono_Q2Dot_le_MDot hg, ?_⟩
  obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hg
  refine mono_mem_stabilizer_Lambda (Equiv.refl _) fun i => ⟨eJd J i, ?_, ?_⟩
  · rw [mono_eJd_apply]
    split_ifs <;> decide
  · rw [mono_eJ_mulVec_xvec]
    rfl

theorem mono_conj_mem_Q2Dot {g : GL6} (hg : g ∈ M2Dot) {q : GL6} (hq : q ∈ Q2Dot) :
    g * q * g⁻¹ ∈ Q2Dot := by
  rw [mono_mem_Q2Dot_iff]
  have hqM : q ∈ MDot := mono_Q2Dot_le_MDot hq
  refine ⟨MDot.mul_mem (MDot.mul_mem hg.1 hqM) (MDot.inv_mem hg.1), ?_⟩
  refine mono_eq_eJ_of_diag (MDot_le_OVq (MDot.mul_mem (MDot.mul_mem hg.1 hqM)
    (MDot.inv_mem hg.1))) fun i => mono_conj_diag hg.2 ?_ i
  obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hq
  exact fun j => ⟨eJd J j, mono_eJ_mulVec_xvec J j⟩

theorem Q2Dot_normal : (Q2Dot.subgroupOf M2Dot).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using mono_conj_mem_Q2Dot g.2 hn

theorem mono_M2Dot_structure {g : GL6} (hg : g ∈ M2Dot) :
    ∃ (τ : Fin 6 → Fin 6) (c : Fin 6 → ZMod 3), Function.Injective τ ∧ τ 5 = 5 ∧
      (∀ i, c i ≠ 0) ∧
      ∀ i, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c i • xvec (τ i) := by
  have hOV : g ∈ OVq := MDot_le_OVq hg.1
  choose τ c hc hτ using mono_line_map hg.2
  have hq : ∀ i, qV (xvec (τ i)) = qV (xvec i) := by
    intro i
    have h1 := qV_mulVec_of_mem_OVq hOV (xvec i)
    rw [hτ i, mono_qV_smul] at h1
    have hc2 : c i ^ 2 = 1 := by
      have key : ∀ a : ZMod 3, a ≠ 0 → a ^ 2 = 1 := by decide
      exact key _ (hc i)
    rw [hc2, one_mul] at h1
    exact h1
  have h5 : τ 5 = 5 := by
    by_contra hne
    have := hq 5
    rw [mono_qV_xvec, mono_qV_xvec, if_neg hne, if_pos rfl] at this
    exact absurd this (by decide)
  have hinj : Function.Injective τ := by
    intro i i' hii
    by_contra hne
    have h1 := bil_mulVec_of_mem_OVq hOV (xvec i) (xvec i')
    rw [hτ i, hτ i', ← hii, bil_smul_left, bil_smul_right, mono_bil_xvec, mono_bil_xvec,
      if_pos rfl, if_neg hne] at h1
    have h2 : c i * (c i' * (2 * qV (xvec (τ i)))) ≠ 0 := by
      refine mul_ne_zero (hc i) (mul_ne_zero (hc i') (mul_ne_zero (by decide) ?_))
      rw [mono_qV_xvec]
      split_ifs <;> decide
    exact h2 h1
  exact ⟨τ, c, hinj, h5, hc, hτ⟩

@[expose] def monoExt : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 6) :=
  Equiv.Perm.extendDomainHom (finSuccAboveEquiv (Fin.last 5))

theorem mono_ext_castSucc (σ : Equiv.Perm (Fin 5)) (a : Fin 5) :
    monoExt σ (Fin.castSucc a) = Fin.castSucc (σ a) := by
  have h := Equiv.Perm.extendDomain_apply_image σ (finSuccAboveEquiv (Fin.last 5)) a
  simp only [finSuccAboveEquiv_apply, Fin.succAbove_last_apply] at h
  exact h

theorem mono_ext_five (σ : Equiv.Perm (Fin 5)) : monoExt σ 5 = 5 :=
  Equiv.Perm.extendDomain_apply_not_subtype σ _ (not_not.2 rfl)

theorem mono_ext_ne_five (σ : Equiv.Perm (Fin 5)) {i : Fin 6} (hi : i ≠ 5) :
    monoExt σ i ≠ 5 := by
  intro h
  exact hi ((monoExt σ).injective (h.trans (mono_ext_five σ).symm))

theorem mono_castSucc_ne_five (a : Fin 5) : Fin.castSucc a ≠ 5 := Fin.castSucc_ne_last a

@[expose] def monoSgn (σ : Equiv.Perm (Fin 5)) : ZMod 3 :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ZMod 3)

theorem mono_sgn_one : monoSgn 1 = 1 := by simp [monoSgn]

theorem mono_sgn_mul (σ τ : Equiv.Perm (Fin 5)) : monoSgn (σ * τ) = monoSgn σ * monoSgn τ := by
  simp [monoSgn]

theorem mono_sgn_sq (σ : Equiv.Perm (Fin 5)) : monoSgn σ * monoSgn σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [monoSgn, h]

theorem mono_sgn_swap {a b : Fin 5} (h : a ≠ b) : monoSgn (Equiv.swap a b) = -1 := by
  simp [monoSgn, Equiv.Perm.sign_swap h]

theorem mono_sgn_ne_zero (σ : Equiv.Perm (Fin 5)) : monoSgn σ ≠ 0 := by
  intro h
  have := mono_sgn_sq σ
  rw [h, zero_mul] at this
  exact zero_ne_one this

@[expose] def monoScal (σ : Equiv.Perm (Fin 5)) (i : Fin 6) : ZMod 3 :=
  if i = 5 then monoSgn σ else 1

theorem mono_scal_ne_zero (σ : Equiv.Perm (Fin 5)) (i : Fin 6) : monoScal σ i ≠ 0 := by
  unfold monoScal
  split_ifs
  · exact mono_sgn_ne_zero σ
  · exact one_ne_zero

theorem mono_scal_sq (σ : Equiv.Perm (Fin 5)) (i : Fin 6) :
    monoScal σ i * monoScal σ i = 1 := by
  unfold monoScal
  split_ifs
  · exact mono_sgn_sq σ
  · exact one_mul 1

theorem mono_scal_castSucc (σ : Equiv.Perm (Fin 5)) (a : Fin 5) :
    monoScal σ (Fin.castSucc a) = 1 := by
  simp [monoScal, mono_castSucc_ne_five]

theorem mono_scal_five (σ : Equiv.Perm (Fin 5)) : monoScal σ 5 = monoSgn σ := by
  simp [monoScal]

@[expose] def monoMat (σ : Equiv.Perm (Fin 5)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun k i => if monoExt σ i = k then monoScal σ i else 0

theorem mono_mat_ext {A B : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ i, A *ᵥ xvec i = B *ᵥ xvec i) : A = B :=
  Matrix.ext_of_mulVec_single h

theorem mono_mat_mulVec_xvec (σ : Equiv.Perm (Fin 5)) (i : Fin 6) :
    monoMat σ *ᵥ xvec i = monoScal σ i • xvec (monoExt σ i) := by
  rw [show xvec i = Pi.single i 1 from rfl, Matrix.mulVec_single_one]
  funext k
  by_cases h : monoExt σ i = k
  · subst h
    simp [monoMat, mono_xvec_apply]
  · simp [monoMat, mono_xvec_apply, h, Ne.symm h]

theorem mono_mat_one : monoMat 1 = 1 := by
  apply mono_mat_ext
  intro i
  rw [mono_mat_mulVec_xvec, Matrix.one_mulVec]
  simp [monoScal, mono_sgn_one]

theorem mono_scal_mul (σ τ : Equiv.Perm (Fin 5)) (i : Fin 6) :
    monoScal (σ * τ) i = monoScal τ i * monoScal σ (monoExt τ i) := by
  by_cases h : i = 5
  · subst h
    rw [mono_scal_five, mono_ext_five, mono_scal_five, mono_scal_five, mono_sgn_mul, mul_comm]
  · have h' := mono_ext_ne_five τ h
    simp [monoScal, h, h']

theorem mono_mat_mul (σ τ : Equiv.Perm (Fin 5)) : monoMat (σ * τ) = monoMat σ * monoMat τ := by
  apply mono_mat_ext
  intro i
  rw [← Matrix.mulVec_mulVec, mono_mat_mulVec_xvec τ, Matrix.mulVec_smul, mono_mat_mulVec_xvec σ,
    smul_smul, mono_mat_mulVec_xvec, map_mul, Equiv.Perm.mul_apply, mono_scal_mul]

@[expose] def monoMatHom : Equiv.Perm (Fin 5) →* Matrix (Fin 6) (Fin 6) (ZMod 3) where
  toFun := monoMat
  map_one' := mono_mat_one
  map_mul' := mono_mat_mul

@[expose] noncomputable def s5Hom : Equiv.Perm (Fin 5) →* GL6 := monoMatHom.toHomUnits

theorem s5Hom_val (σ : Equiv.Perm (Fin 5)) :
    ((s5Hom σ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = monoMat σ :=
  MonoidHom.coe_toHomUnits _ _

theorem s5Hom_mulVec_xvec (σ : Equiv.Perm (Fin 5)) (i : Fin 6) :
    ((s5Hom σ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      monoScal σ i • xvec (monoExt σ i) := by
  rw [s5Hom_val, mono_mat_mulVec_xvec]

theorem s5Hom_injective : Function.Injective s5Hom := by
  rw [injective_iff_map_eq_one]
  intro σ h
  refine Equiv.ext fun a => ?_
  have h1 := s5Hom_mulVec_xvec σ (Fin.castSucc a)
  rw [h, Units.val_one, Matrix.one_mulVec, mono_ext_castSucc, mono_scal_castSucc, one_smul] at h1
  exact (Fin.castSucc_injective _ (mono_xvec_inj h1)).symm

theorem mono_s5Hom_mem_stab (σ : Equiv.Perm (Fin 5)) :
    s5Hom σ ∈ MulAction.stabilizer GL6 Lambda :=
  mono_mem_stabilizer_Lambda (monoExt σ) fun i =>
    ⟨monoScal σ i, mono_scal_ne_zero σ i, s5Hom_mulVec_xvec σ i⟩

theorem mono_fin_cases (i : Fin 6) : i = 5 ∨ ∃ a : Fin 5, i = Fin.castSucc a := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, ha⟩ | h
  · exact Or.inr ⟨a, ha⟩
  · exact Or.inl h

theorem mono_qV_sub_xvec {a b : Fin 6} (hab : a ≠ b) (ha : a ≠ 5) (hb : b ≠ 5) :
    qV (xvec a - xvec b) = -1 := by
  rw [qV_sub, mono_bil_xvec, mono_qV_xvec, mono_qV_xvec, if_neg hab, if_neg ha, if_neg hb]
  decide

theorem mono_bil_xvec_right (x : V6) {j : Fin 6} (hj : j ≠ 5) : bil x (xvec j) = 2 * x j := by
  rw [bil_coord]
  fin_cases j
  all_goals first | (exfalso; exact hj rfl) | (simp [mono_xvec_apply])

@[expose] def monoSwapRefl (a b : Fin 6) (hab : a ≠ b) (ha : a ≠ 5) (hb : b ≠ 5) : GL6 :=
  refl6 (xvec a - xvec b) (by rw [mono_qV_sub_xvec hab ha hb]; decide)

theorem mono_swapRefl_mulVec {a b : Fin 6} (hab : a ≠ b) (ha : a ≠ 5) (hb : b ≠ 5) (x : V6) :
    (monoSwapRefl a b hab ha hb : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x =
      fun k => x (Equiv.swap a b k) := by
  have hq := mono_qV_sub_xvec hab ha hb
  unfold monoSwapRefl
  rw [refl6_mulVec, hq, inv_neg, inv_one, bil_sub_right, mono_bil_xvec_right x ha,
    mono_bil_xvec_right x hb]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mono_xvec_apply]
  by_cases hka : k = a
  · subst hka
    rw [Equiv.swap_apply_left, if_pos rfl, if_neg hab]
    generalize x k = u
    generalize x b = v
    revert u v
    decide
  · by_cases hkb : k = b
    · subst hkb
      rw [Equiv.swap_apply_right, if_neg hka, if_pos rfl]
      generalize x k = u
      generalize x a = v
      revert u v
      decide
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb, if_neg hka, if_neg hkb]
      simp

theorem mono_swapRefl_mulVec_xvec {a b : Fin 6} (hab : a ≠ b) (ha : a ≠ 5) (hb : b ≠ 5)
    (i : Fin 6) :
    (monoSwapRefl a b hab ha hb : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      xvec (Equiv.swap a b i) := by
  rw [mono_swapRefl_mulVec]
  funext k
  simp only [mono_xvec_apply, Equiv.swap_apply_eq_iff]

theorem mono_refl_xvec (a : Fin 6) : refl6 (xvec a) (qV_xvec_ne_zero a) = eJ {a} :=
  mono_reflOf_reflX a

theorem mono_s5Hom_swap {a b : Fin 5} (hab : a ≠ b) :
    s5Hom (Equiv.swap a b) =
      monoSwapRefl (Fin.castSucc a) (Fin.castSucc b) (fun h => hab (Fin.castSucc_injective _ h))
        (mono_castSucc_ne_five a) (mono_castSucc_ne_five b) *
        refl6 (xvec 5) (qV_xvec_ne_zero 5) := by
  apply Units.ext
  apply mono_mat_ext
  intro i
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, mono_refl_xvec, mono_eJ_mulVec_xvec,
    Matrix.mulVec_smul, mono_swapRefl_mulVec_xvec, s5Hom_val, mono_mat_mulVec_xvec]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, mono_sgn_swap hab,
      Equiv.swap_apply_of_ne_of_ne (mono_castSucc_ne_five a).symm (mono_castSucc_ne_five b).symm]
    simp [mono_eJd_apply]
  · rw [mono_scal_castSucc, mono_ext_castSucc, (Fin.castSucc_injective 5).map_swap a b c]
    simp [mono_eJd_apply, mono_castSucc_ne_five]

theorem mono_s5Hom_swap_mem_MDot {a b : Fin 5} (hab : a ≠ b) :
    s5Hom (Equiv.swap a b) ∈ MDot := by
  have hab' : Fin.castSucc a ≠ Fin.castSucc b := fun h => hab (Fin.castSucc_injective _ h)
  have hz : qV (xvec (Fin.castSucc a) - xvec (Fin.castSucc b)) ≠ 0 := by
    rw [mono_qV_sub_xvec hab' (mono_castSucc_ne_five a) (mono_castSucc_ne_five b)]
    decide
  have key : (([⟨xvec (Fin.castSucc a) - xvec (Fin.castSucc b), hz⟩, monoReflX 5] :
      List ReflVec).map reflOf).prod = s5Hom (Equiv.swap a b) := by
    rw [mono_s5Hom_swap hab]
    simp [reflOf, monoSwapRefl, monoReflX]
  rw [← key, prod_refl_mem_MDot_iff]
  refine ⟨by simp, ?_⟩
  have hq1 := mono_qV_sub_xvec hab' (mono_castSucc_ne_five a) (mono_castSucc_ne_five b)
  have hq2 : qV (xvec 5) = -1 := by rw [mono_qV_xvec, if_pos rfl]
  simp [List.countP_cons, hq1, monoReflX, hq2]

theorem mono_s5Hom_mem_MDot (σ : Equiv.Perm (Fin 5)) : s5Hom σ ∈ MDot := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [map_one]; exact MDot.one_mem
  | swap_mul f a b hab ih => rw [map_mul]; exact MDot.mul_mem (mono_s5Hom_swap_mem_MDot hab) ih

theorem s5Hom_range_le : s5Hom.range ≤ M2Dot := by
  rintro _ ⟨σ, rfl⟩
  exact ⟨mono_s5Hom_mem_MDot σ, mono_s5Hom_mem_stab σ⟩

theorem mono_gl_ext {g h : GL6}
    (H : ∀ i, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i) : g = h :=
  Units.ext (mono_mat_ext H)

theorem mono_eJd_ne_zero (J : Finset (Fin 6)) (i : Fin 6) : eJd J i ≠ 0 := by
  rw [mono_eJd_apply]
  split_ifs <;> decide

theorem s5Hom_range_inf : s5Hom.range ⊓ Q2Dot = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨σ, rfl⟩, hq⟩
  obtain ⟨J, hJ⟩ := mono_Q2Dot_elim hq
  have hσ : σ = 1 := by
    refine Equiv.ext fun a => ?_
    have h1 := congrFun (s5Hom_mulVec_xvec σ (Fin.castSucc a)) (Fin.castSucc a)
    rw [hJ, mono_eJ_mulVec_xvec, mono_ext_castSucc, mono_scal_castSucc, one_smul] at h1
    by_cases hc : Fin.castSucc a = Fin.castSucc (σ a)
    · exact (Fin.castSucc_injective _ hc).symm
    · exfalso
      simp [mono_xvec_apply, hc] at h1
      exact mono_eJd_ne_zero J _ h1
  rw [hσ, map_one]
  exact Subgroup.one_mem _

theorem mono_M2Dot_exists_perm {g : GL6} (hg : g ∈ M2Dot) :
    ∃ (σ : Equiv.Perm (Fin 5)) (c : Fin 6 → ZMod 3), (∀ i, c i ≠ 0) ∧
      ∀ i, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c i • xvec (monoExt σ i) := by
  obtain ⟨τ, c, hinj, h5, hc, hτ⟩ := mono_M2Dot_structure hg
  have hne : ∀ a : Fin 5, τ (Fin.castSucc a) ≠ Fin.last 5 := fun a h =>
    Fin.castSucc_ne_last a (hinj (h.trans h5.symm))
  let σf : Fin 5 → Fin 5 := fun a => (τ (Fin.castSucc a)).castPred (hne a)
  have hσf : ∀ a, Fin.castSucc (σf a) = τ (Fin.castSucc a) := fun a => Fin.castSucc_castPred _ _
  have hσinj : Function.Injective σf := by
    intro a b hab
    apply Fin.castSucc_injective
    apply hinj
    rw [← hσf a, ← hσf b, hab]
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj)
  have hστ : ∀ i, monoExt σ i = τ i := by
    intro i
    rcases mono_fin_cases i with rfl | ⟨a, rfl⟩
    · rw [mono_ext_five, h5]
    · rw [mono_ext_castSucc]
      exact hσf a
  exact ⟨σ, c, hc, fun i => by rw [hστ i]; exact hτ i⟩

theorem mono_M2Dot_decomp {g : GL6} (hg : g ∈ M2Dot) :
    ∃ σ : Equiv.Perm (Fin 5), ∃ q ∈ Q2Dot, g = s5Hom σ * q := by
  obtain ⟨σ, c, hc, hσ⟩ := mono_M2Dot_exists_perm hg
  have hP : s5Hom σ ∈ MDot := mono_s5Hom_mem_MDot σ
  have hhM : (s5Hom σ)⁻¹ * g ∈ MDot := MDot.mul_mem (MDot.inv_mem hP) hg.1
  have hdiag : ∀ i, ∃ e : ZMod 3,
      (((s5Hom σ)⁻¹ * g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = e • xvec i := by
    intro i
    refine ⟨c i * monoScal σ i, ?_⟩
    have h1 : (((s5Hom σ)⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec (monoExt σ i) =
        monoScal σ i • xvec i := by
      have h2 : ((s5Hom σ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (monoScal σ i • xvec i) =
          xvec (monoExt σ i) := by
        rw [Matrix.mulVec_smul, s5Hom_mulVec_xvec, smul_smul, mono_scal_sq, one_smul]
      rw [← h2, mono_inv_mulVec]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hσ i, Matrix.mulVec_smul, h1, smul_smul]
  obtain ⟨J, hJ⟩ := mono_eq_eJ_of_diag (MDot_le_OVq hhM) hdiag
  exact ⟨σ, (s5Hom σ)⁻¹ * g, (mono_mem_Q2Dot_iff _).2 ⟨hhM, J, hJ⟩,
    (mul_inv_cancel_left _ _).symm⟩

theorem Q2Dot_sup_s5Hom : Q2Dot ⊔ s5Hom.range = M2Dot := by
  apply le_antisymm
  · exact sup_le Q2Dot_le_M2Dot s5Hom_range_le
  · intro g hg
    obtain ⟨σ, q, hq, rfl⟩ := mono_M2Dot_decomp hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨σ, rfl⟩) (Subgroup.mem_sup_left hq)

theorem mono_M2Dot_complement :
    ∃ K : Subgroup GL6, K ≤ M2Dot ∧ K ⊓ Q2Dot = ⊥ ∧ Q2Dot ⊔ K = M2Dot ∧
      Nonempty (↥K ≃* Equiv.Perm (Fin 5)) :=
  ⟨s5Hom.range, s5Hom_range_le, s5Hom_range_inf, Q2Dot_sup_s5Hom,
    ⟨(MonoidHom.ofInjective s5Hom_injective).symm⟩⟩

theorem M2Dot_le_M0Dot : M2Dot ≤ M0Dot := by
  intro g hg
  refine ⟨hg.1, ?_⟩
  obtain ⟨τ, c, hinj, h5, hc, hτ⟩ := mono_M2Dot_structure hg
  show g ∈ MulAction.stabilizer GL6 (spn {x6})
  rw [MulAction.mem_stabilizer_iff]
  show g • spn {xvec 5} = spn {xvec 5}
  rw [mono_smul_spn, mono_smul_xvec, hτ 5, h5]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (hc 5)) _

theorem mono_card_sup_of_le_normalizer {G : Type*} [Group G] (A B : Subgroup G)
    (hAB : A ⊓ B = ⊥) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcov := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      simp only [f, Subtype.mk.injEq] at h
      have h2 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
          _ = b' * b⁻¹ := by group
      have h3 : a'⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
      rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h3
      subst h3
      have h4 : b = b' := mul_left_cancel h
      subst h4
      rfl
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (↑(A ⊔ B) : Set G) := hx
      rw [hcov] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod]

theorem mono_M2Dot_le_normalizer : M2Dot ≤ Subgroup.normalizer (Q2Dot : Set GL6) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => mono_conj_mem_Q2Dot hg hh, fun hh => ?_⟩
  have := mono_conj_mem_Q2Dot (Subgroup.inv_mem _ hg) hh
  simpa [mul_assoc] using this

@[expose] def monoQA (A : Subgroup (Equiv.Perm (Fin 5))) : Subgroup GL6 :=
  Q2Dot ⊔ A.map s5Hom

theorem mono_map_le_normalizer (A : Subgroup (Equiv.Perm (Fin 5))) :
    A.map s5Hom ≤ Subgroup.normalizer (Q2Dot : Set GL6) := by
  rintro _ ⟨σ, -, rfl⟩
  exact mono_M2Dot_le_normalizer (s5Hom_range_le ⟨σ, rfl⟩)

theorem mono_QA_le_M2Dot (A : Subgroup (Equiv.Perm (Fin 5))) : monoQA A ≤ M2Dot :=
  sup_le Q2Dot_le_M2Dot (fun _ ⟨σ, _, h⟩ => s5Hom_range_le ⟨σ, h⟩)

theorem mono_QA_card (A : Subgroup (Equiv.Perm (Fin 5))) :
    Nat.card ↥(monoQA A) = 16 * Nat.card ↥A := by
  have hinf : Q2Dot ⊓ A.map s5Hom = ⊥ := by
    rw [eq_bot_iff, ← s5Hom_range_inf, inf_comm]
    exact inf_le_inf_right _ (fun _ ⟨σ, _, h⟩ => ⟨σ, h⟩)
  unfold monoQA
  rw [mono_card_sup_of_le_normalizer _ _ hinf (mono_map_le_normalizer A), mono_card_Q2Dot,
    Subgroup.card_map_of_injective s5Hom_injective]

theorem mono_QA_top : monoQA ⊤ = M2Dot := by
  unfold monoQA
  rw [← MonoidHom.range_eq_map, Q2Dot_sup_s5Hom]

theorem card_M2Dot : Nat.card ↥M2Dot = 1920 := by
  rw [← mono_QA_top, mono_QA_card, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num [Nat.factorial]

theorem mono_spn_xvec_eq_iff {i j : Fin 6} : spn {xvec i} = spn {xvec j} ↔ i = j := by
  constructor
  · intro h
    have hmem : xvec i ∈ spn {xvec j} := h ▸ Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    by_contra hij
    have h1 := congrFun ha i
    simp [mono_xvec_apply, hij] at h1
  · rintro rfl
    rfl

theorem mono_spn_smul {c : ZMod 3} (hc : c ≠ 0) (v : V6) : spn {c • v} = spn {v} :=
  Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) v

@[expose] def monoS4 : Subgroup (Equiv.Perm (Fin 5)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 5)) (4 : Fin 5)

theorem mono_mem_S4 {σ : Equiv.Perm (Fin 5)} : σ ∈ monoS4 ↔ σ 4 = 4 :=
  MulAction.mem_stabilizer_iff

theorem mono_card_S4 : Nat.card ↥monoS4 = 24 := by
  have h1 : monoS4.index = Nat.card (Fin 5) :=
    MulAction.index_stabilizer_of_transitive (Equiv.Perm (Fin 5)) (4 : Fin 5)
  have h2 := Subgroup.card_mul_index monoS4
  have h5 : Nat.card (Fin 5) = 5 := by simp
  rw [h1, Nat.card_perm, h5] at h2
  norm_num [Nat.factorial] at h2
  omega

theorem mono_stab_iff (σ : Equiv.Perm (Fin 5)) {q : GL6} (hq : q ∈ Q2Dot) :
    s5Hom σ * q ∈ MulAction.stabilizer GL6 (spn {x5}) ↔ σ 4 = 4 := by
  obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hq
  rw [MulAction.mem_stabilizer_iff]
  show (s5Hom σ * eJ J) • spn {xvec 4} = spn {xvec 4} ↔ _
  rw [mono_smul_spn, mono_smul_xvec, Units.val_mul, ← Matrix.mulVec_mulVec,
    mono_eJ_mulVec_xvec, Matrix.mulVec_smul, s5Hom_mulVec_xvec, smul_smul,
    mono_spn_smul (mul_ne_zero (mono_eJd_ne_zero J 4) (mono_scal_ne_zero σ 4)),
    mono_spn_xvec_eq_iff]
  have h4 : (4 : Fin 6) = Fin.castSucc (4 : Fin 5) := rfl
  rw [h4, mono_ext_castSucc]
  exact ⟨fun h => Fin.castSucc_injective _ h, fun h => congrArg _ h⟩

theorem mono_N_eq : M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}) = monoQA monoS4 := by
  apply le_antisymm
  · rintro g ⟨hg, hs⟩
    obtain ⟨σ, q, hq, rfl⟩ := mono_M2Dot_decomp hg
    have hσ : σ ∈ monoS4 := mono_mem_S4.2 ((mono_stab_iff σ hq).1 hs)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨σ, hσ, rfl⟩) (Subgroup.mem_sup_left hq)
  · refine le_inf (mono_QA_le_M2Dot _) (sup_le ?_ ?_)
    · intro q hq
      have := (mono_stab_iff 1 hq).2 rfl
      simpa using this
    · rintro _ ⟨σ, hσ, rfl⟩
      have := (mono_stab_iff σ (Subgroup.one_mem Q2Dot)).2 (mono_mem_S4.1 hσ)
      simpa using this

theorem mono_comm_iff {g : GL6} {τ : Fin 6 → Fin 6} {c : Fin 6 → ZMod 3} (hc : ∀ i, c i ≠ 0)
    (hτ : ∀ i, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c i • xvec (τ i)) :
    zDot * g = g * zDot ↔ ∀ i, eJd {0, 1, 2, 3} (τ i) = eJd {0, 1, 2, 3} i := by
  have key : ∀ i, ((zDot * g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      (c i * eJd {0, 1, 2, 3} (τ i)) • xvec (τ i) := by
    intro i
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hτ i, Matrix.mulVec_smul]
    show c i • ((eJ {0, 1, 2, 3} : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec (τ i) = _
    rw [mono_eJ_mulVec_xvec, smul_smul]
  have key' : ∀ i, ((g * zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      (eJd {0, 1, 2, 3} i * c i) • xvec (τ i) := by
    intro i
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    show _ *ᵥ (((eJ {0, 1, 2, 3} : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i) = _
    rw [mono_eJ_mulVec_xvec, Matrix.mulVec_smul, hτ i, smul_smul]
  constructor
  · intro h i
    have h1 := congrArg (fun m : GL6 => (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i) h
    simp only [key, key'] at h1
    have h2 := congrFun h1 (τ i)
    rw [Pi.smul_apply, Pi.smul_apply, mono_xvec_apply, if_pos rfl, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one, mul_comm (eJd _ i)] at h2
    exact mul_left_cancel₀ (hc i) h2
  · intro h
    apply mono_gl_ext
    intro i
    rw [key, key', h i, mul_comm]

theorem mono_stab_x5_iff {g : GL6} {τ : Fin 6 → Fin 6} {c : Fin 6 → ZMod 3} (hc : ∀ i, c i ≠ 0)
    (hτ : ∀ i, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c i • xvec (τ i)) :
    g ∈ MulAction.stabilizer GL6 (spn {x5}) ↔ τ 4 = 4 := by
  rw [MulAction.mem_stabilizer_iff]
  show g • spn {xvec 4} = spn {xvec 4} ↔ _
  rw [mono_smul_spn, mono_smul_xvec, hτ 4, mono_spn_smul (hc 4), mono_spn_xvec_eq_iff]

theorem mono_zeta_iff {τ : Fin 6 → Fin 6} (hinj : Function.Injective τ) (h5 : τ 5 = 5) :
    (∀ i, eJd {0, 1, 2, 3} (τ i) = eJd {0, 1, 2, 3} i) ↔ τ 4 = 4 := by
  constructor
  · intro h
    have h4 := h 4
    have hne5 : τ 4 ≠ 5 := fun h' => by
      have := hinj (h'.trans h5.symm)
      revert this
      decide
    revert h4 hne5
    generalize τ 4 = k
    revert k
    decide
  · intro h4 i
    by_cases hi4 : i = 4
    · subst hi4
      rw [h4]
    by_cases hi5 : i = 5
    · subst hi5
      rw [h5]
    have hτ4 : τ i ≠ 4 := fun h' => hi4 (hinj (h'.trans h4.symm))
    have hτ5 : τ i ≠ 5 := fun h' => hi5 (hinj (h'.trans h5.symm))
    have key : ∀ k : Fin 6, k ≠ 4 → k ≠ 5 → eJd {0, 1, 2, 3} k = -1 := by decide
    rw [key _ hτ4 hτ5, key _ hi4 hi5]

theorem mono_M1_iff {g : GL6} (hg : g ∈ M2Dot) :
    g ∈ M1Dot ↔ g ∈ MulAction.stabilizer GL6 (spn {x5}) := by
  obtain ⟨τ, c, hinj, h5, hc, hτ⟩ := mono_M2Dot_structure hg
  rw [mono_stab_x5_iff hc hτ, ← mono_zeta_iff hinj h5, ← mono_comm_iff hc hτ]
  constructor
  · intro h
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2 zDot rfl
  · intro h
    exact ⟨hg.1, Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h⟩

theorem M1Dot_inf_M2Dot :
    M1Dot ⊓ M2Dot = M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}) := by
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (mono_M1_iff h2).1 h1⟩
  · rintro ⟨h2, hs⟩
    exact ⟨(mono_M1_iff h2).2 hs, h2⟩

theorem card_M12Dot : Nat.card ↥(M1Dot ⊓ M2Dot) = 384 := by
  rw [M1Dot_inf_M2Dot, mono_N_eq, mono_QA_card, mono_card_S4]

theorem mono_M1Dot_ne_M2Dot : M1Dot ≠ M2Dot := by
  intro h
  have h1 := card_M12Dot
  rw [h, inf_idem, card_M2Dot] at h1
  omega

@[expose] def monoKlein4 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := ↑({1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 5)))
  mul_mem' := by
    intro a b ha hb
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem mem_monoKlein4 {σ : Equiv.Perm (Fin 5)} :
    σ ∈ monoKlein4 ↔ σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
      σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2 := by
  show σ ∈ (↑({1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) ↔ _
  simp

theorem mono_card_Klein4 : Nat.card ↥monoKlein4 = 4 := by
  have h : Nat.card ↥monoKlein4 = Nat.card ↥(↑({1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2} :
      Finset (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

theorem mono_Klein4_le_S4 : monoKlein4 ≤ monoS4 := by
  intro σ hσ
  rw [mono_mem_S4]
  rw [mem_monoKlein4] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> decide

theorem mono_Klein4_conj (τ : Equiv.Perm (Fin 5)) (hτ : τ 4 = 4) {κ : Equiv.Perm (Fin 5)}
    (hκ : κ ∈ monoKlein4) : τ * κ * τ⁻¹ ∈ monoKlein4 := by
  rw [mem_monoKlein4] at hκ ⊢
  rcases hκ with rfl | rfl | rfl | rfl <;> revert τ <;> decide +kernel

theorem mono_QA_mono {A B : Subgroup (Equiv.Perm (Fin 5))} (h : A ≤ B) : monoQA A ≤ monoQA B :=
  sup_le_sup_left (Subgroup.map_mono h) _

theorem mono_mem_QA {A : Subgroup (Equiv.Perm (Fin 5))} {g : GL6} (hg : g ∈ monoQA A) :
    ∃ q ∈ Q2Dot, ∃ κ ∈ A, g = q * s5Hom κ := by
  have h : g ∈ (↑(monoQA A) : Set GL6) := hg
  unfold monoQA at h
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (mono_map_le_normalizer A)] at h
  obtain ⟨q, hq, p, ⟨κ, hκ, rfl⟩, rfl⟩ := h
  exact ⟨q, hq, κ, hκ, rfl⟩

theorem mono_QA_unique {q q' : GL6} (hq : q ∈ Q2Dot) (hq' : q' ∈ Q2Dot)
    {κ κ' : Equiv.Perm (Fin 5)} (h : q * s5Hom κ = q' * s5Hom κ') : κ = κ' ∧ q = q' := by
  have h1 : q'⁻¹ * q = s5Hom κ' * (s5Hom κ)⁻¹ := by
    calc q'⁻¹ * q = q'⁻¹ * (q * s5Hom κ) * (s5Hom κ)⁻¹ := by group
      _ = q'⁻¹ * (q' * s5Hom κ') * (s5Hom κ)⁻¹ := by rw [h]
      _ = s5Hom κ' * (s5Hom κ)⁻¹ := by group
  have h2 : s5Hom κ' * (s5Hom κ)⁻¹ ∈ s5Hom.range ⊓ Q2Dot :=
    ⟨Subgroup.mul_mem _ ⟨κ', rfl⟩ (Subgroup.inv_mem _ ⟨κ, rfl⟩),
      h1 ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hq⟩
  rw [s5Hom_range_inf, Subgroup.mem_bot, mul_inv_eq_one] at h2
  have hκ : κ = κ' := (s5Hom_injective h2).symm
  subst hκ
  exact ⟨rfl, mul_right_cancel h⟩

theorem mono_s5Hom_mem_QA_iff (A : Subgroup (Equiv.Perm (Fin 5))) (σ : Equiv.Perm (Fin 5)) :
    s5Hom σ ∈ monoQA A ↔ σ ∈ A := by
  constructor
  · intro h
    obtain ⟨q, hq, κ, hκ, hqκ⟩ := mono_mem_QA h
    have := mono_QA_unique (Subgroup.one_mem _) hq (κ := σ) (κ' := κ) (by rw [one_mul, hqκ])
    rw [this.1]
    exact hκ
  · intro h
    exact Subgroup.mem_sup_right ⟨σ, h, rfl⟩

theorem mono_conj_mem_sup {G : Type*} [Group G] {X Y : Subgroup G} {g : G}
    (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ X ⊔ Y) (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ X ⊔ Y) :
    ∀ s ∈ X ⊔ Y, g * s * g⁻¹ ∈ X ⊔ Y := by
  have h : X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj g).toMonoidHom := sup_le hX hY
  exact fun s hs => h hs

theorem mono_mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ s ∈ H, g * s * g⁻¹ ∈ H) (h2 : ∀ s ∈ H, g⁻¹ * s * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h1 s, fun hs => ?_⟩
  have := h2 _ hs
  simpa [mul_assoc] using this

theorem mono_conj_QA {σ : Equiv.Perm (Fin 5)} (hσ : σ 4 = 4) :
    ∀ s ∈ monoQA monoKlein4, s5Hom σ * s * (s5Hom σ)⁻¹ ∈ monoQA monoKlein4 := by
  apply mono_conj_mem_sup
  · intro x hx
    exact Subgroup.mem_sup_left (mono_conj_mem_Q2Dot (s5Hom_range_le ⟨σ, rfl⟩) hx)
  · rintro _ ⟨κ, hκ, rfl⟩
    refine Subgroup.mem_sup_right ⟨σ * κ * σ⁻¹, mono_Klein4_conj σ hσ hκ, ?_⟩
    simp [map_mul, map_inv]

theorem mono_S4_le_normalizer :
    monoQA monoS4 ≤ Subgroup.normalizer (monoQA monoKlein4 : Set GL6) := by
  refine sup_le (le_trans (le_sup_left : Q2Dot ≤ monoQA monoKlein4) Subgroup.le_normalizer) ?_
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ4 : σ 4 = 4 := mono_mem_S4.1 hσ
  have hσ4' : σ⁻¹ 4 = 4 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hσ4.symm
  refine mono_mem_normalizer_of_conj (mono_conj_QA hσ4) ?_
  intro s hs
  have := mono_conj_QA hσ4' s hs
  rwa [map_inv, inv_inv] at this

theorem mono_card_SDot' : Nat.card ↥(monoQA monoKlein4) = 64 := by
  rw [mono_QA_card, mono_card_Klein4]

theorem mono_isPGroup_SDot' : IsPGroup 2 ↥(monoQA monoKlein4) :=
  IsPGroup.of_card (n := 6) (by rw [mono_card_SDot']; norm_num)

theorem mono_card_N : Nat.card ↥(M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5})) = 384 := by
  rw [mono_N_eq, mono_QA_card, mono_card_S4]

theorem mono_SDot'_le : monoQA monoKlein4 ≤ SDot := by
  unfold SDot
  rw [mono_N_eq]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (mono_QA_mono mono_Klein4_le_S4)
    mono_S4_le_normalizer mono_isPGroup_SDot'

theorem mono_mem_of_normal_odd_index {G : Type*} [Group G] {N R : Subgroup G} (hRN : R ≤ N)
    (hnorm : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R) (hodd : ¬ 2 ∣ R.relIndex N) {x : G}
    (hx : x ∈ N) (hx2 : x * x = 1) : x ∈ R := by
  haveI : (R.subgroupOf N).Normal := ⟨fun r hr n => by
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simpa using hnorm n n.2 r hr⟩
  set q : ↥N ⧸ R.subgroupOf N := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hq2 : q ^ 2 = 1 := by
    rw [pow_two, hq, ← QuotientGroup.mk_mul]
    have : (⟨x, hx⟩ : ↥N) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this]
    rfl
  have h1 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have h2 := orderOf_dvd_natCard q
  have h3 : Nat.card (↥N ⧸ R.subgroupOf N) = R.relIndex N := rfl
  rw [h3] at h2
  have h4 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 hodd
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at h4
  exact Subgroup.mem_subgroupOf.1 h4

theorem mono_pCoreOf_conj {G : Type*} [Group G] (H : Subgroup G) {n r : G} (hn : n ∈ H)
    (hr : r ∈ pCoreOf 2 H) : n * r * n⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨o', ho', rfl⟩ := hr
  exact ⟨⟨n, hn⟩ * o' * ⟨n, hn⟩⁻¹,
    (CFSG.LieType.BorelTits.pCore_normal (G := ↥H) 2).conj_mem o' ho' _, rfl⟩

theorem mono_SDot_le : SDot ≤ monoQA monoKlein4 := by
  have hSR : monoQA monoKlein4 ≤ SDot := mono_SDot'_le
  by_contra hnot
  set N : Subgroup GL6 := M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}) with hN
  have hR2 : IsPGroup 2 ↥SDot := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hRN : SDot ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hRnorm : ∀ n ∈ N, ∀ r ∈ SDot, n * r * n⁻¹ ∈ SDot := fun n hn r hr =>
    mono_pCoreOf_conj N hn hr
  have hNcard : Nat.card ↥N = 384 := mono_card_N
  have hlt : monoQA monoKlein4 < SDot := lt_of_le_of_ne hSR (fun h => hnot (h ▸ le_rfl))
  have hcard : 64 < Nat.card ↥SDot := by
    rw [← mono_card_SDot']
    exact Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hdvd : Nat.card ↥SDot ∣ 384 := hNcard ▸ Subgroup.card_dvd_of_le hRN
  have h128 : Nat.card ↥SDot = 128 := by
    rw [hk] at hcard hdvd ⊢
    have hle : 2 ^ k ≤ 384 := Nat.le_of_dvd (by norm_num) hdvd
    have hk9 : k < 9 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.1 h)
      omega
    interval_cases k <;> omega
  have hrel : SDot.relIndex N = 3 := by
    have := Subgroup.relIndex_mul_card SDot N
    rw [inf_eq_left.2 hRN, h128, hNcard] at this
    omega
  have hodd : ¬ 2 ∣ SDot.relIndex N := by
    rw [hrel]
    omega
  have hmemN : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → s5Hom σ ∈ N := fun σ hσ => by
    rw [hN, mono_N_eq]
    exact Subgroup.mem_sup_right ⟨σ, mono_mem_S4.2 hσ, rfl⟩
  have hx1 : s5Hom (Equiv.swap 0 1) ∈ SDot :=
    mono_mem_of_normal_odd_index hRN hRnorm hodd (hmemN _ (by decide))
      (by rw [← map_mul, Equiv.swap_mul_self, map_one])
  have hx2 : s5Hom (Equiv.swap 0 2) ∈ SDot :=
    mono_mem_of_normal_odd_index hRN hRnorm hodd (hmemN _ (by decide))
      (by rw [← map_mul, Equiv.swap_mul_self, map_one])
  have hy : s5Hom (Equiv.swap 0 1) * s5Hom (Equiv.swap 0 2) ∈ SDot := Subgroup.mul_mem _ hx1 hx2
  have hy3 : (s5Hom (Equiv.swap 0 1) * s5Hom (Equiv.swap 0 2)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow]
    have : ((Equiv.swap (0 : Fin 5) 1) * Equiv.swap 0 2) ^ 3 = 1 := by decide
    rw [this, map_one]
  have hy1 : s5Hom (Equiv.swap 0 1) * s5Hom (Equiv.swap 0 2) ≠ 1 := by
    intro h
    rw [← map_mul, ← map_one s5Hom] at h
    exact absurd (s5Hom_injective h) (by decide)
  obtain ⟨n, hn⟩ := hR2 ⟨_, hy⟩
  have hyn : (s5Hom (Equiv.swap 0 1) * s5Hom (Equiv.swap 0 2)) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 := orderOf_dvd_of_pow_eq_one hyn
  have h2 := orderOf_dvd_of_pow_eq_one hy3
  have h3 : Nat.Coprime (orderOf (s5Hom (Equiv.swap 0 1) * s5Hom (Equiv.swap 0 2))) 3 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n (by norm_num))
  exact hy1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2))

theorem SDot_eq : SDot = Q2Dot ⊔ monoKlein4.map s5Hom :=
  le_antisymm mono_SDot_le mono_SDot'_le

theorem card_SDot : Nat.card ↥SDot = 64 := by
  rw [SDot_eq]
  exact mono_card_SDot'

theorem fDot_eq_s5Hom : fDot = s5Hom (Equiv.swap 0 1) := by
  apply mono_gl_ext
  intro i
  rw [s5Hom_mulVec_xvec]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, mono_sgn_swap (by decide)]
    show fMat *ᵥ xvec 5 = _
    decide
  · rw [mono_scal_castSucc, mono_ext_castSucc, one_smul]
    show fMat *ᵥ xvec (Fin.castSucc c) = _
    revert c
    decide

theorem mono_s5Hom_mem_M12 {σ : Equiv.Perm (Fin 5)} (hσ : σ 4 = 4) :
    s5Hom σ ∈ M1Dot ⊓ M2Dot := by
  rw [M1Dot_inf_M2Dot, mono_N_eq]
  exact Subgroup.mem_sup_right ⟨σ, mono_mem_S4.2 hσ, rfl⟩

theorem fDot_mem_M12Dot : fDot ∈ M1Dot ⊓ M2Dot := by
  rw [fDot_eq_s5Hom]
  exact mono_s5Hom_mem_M12 (by decide)

theorem mono_SDot_le_M12 : SDot ≤ M1Dot ⊓ M2Dot := by
  rw [M1Dot_inf_M2Dot]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem TDot_le_M12 : TDot ≤ M1Dot ⊓ M2Dot :=
  sup_le mono_SDot_le_M12 (Subgroup.zpowers_le.2 fDot_mem_M12Dot)

theorem mono_mem_zpowers_involution {G : Type*} [Group G] {f : G} (hf : f * f = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers f) : x = 1 ∨ x = f := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  refine Int.induction_on k (Or.inl (zpow_zero f)) (fun i ih => ?_) (fun i ih => ?_)
  · rcases ih with h | h
    · right
      rw [_root_.zpow_add_one, h, one_mul]
    · left
      rw [_root_.zpow_add_one, h, hf]
  · rcases ih with h | h
    · right
      rw [_root_.zpow_sub_one, h, one_mul, hinv]
    · left
      rw [_root_.zpow_sub_one, h, hinv, hf]

theorem mono_fDot_mul_self : fDot * fDot = 1 := by
  rw [fDot_eq_s5Hom, ← map_mul, Equiv.swap_mul_self, map_one]

theorem mono_fDot_ne_one : fDot ≠ 1 := by
  rw [fDot_eq_s5Hom]
  intro h
  rw [← map_one s5Hom] at h
  exact absurd (s5Hom_injective h) (by decide)

theorem mono_fDot_not_mem_SDot : fDot ∉ SDot := by
  rw [SDot_eq, fDot_eq_s5Hom]
  show s5Hom (Equiv.swap 0 1) ∉ monoQA monoKlein4
  rw [mono_s5Hom_mem_QA_iff, mem_monoKlein4]
  decide

theorem mono_fDot_mem_normalizer : fDot ∈ Subgroup.normalizer (SDot : Set GL6) := by
  have hN : fDot ∈ M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}) := by
    rw [← M1Dot_inf_M2Dot]
    exact fDot_mem_M12Dot
  refine mono_mem_normalizer_of_conj (fun s hs => mono_pCoreOf_conj _ hN hs) (fun s hs => ?_)
  have := mono_pCoreOf_conj _ (Subgroup.inv_mem _ hN) hs
  rw [inv_inv] at this
  exact this

theorem card_TDot : Nat.card ↥TDot = 128 := by
  have hinf : SDot ⊓ Subgroup.zpowers fDot = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxz⟩
    rcases mono_mem_zpowers_involution mono_fDot_mul_self hxz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxS mono_fDot_not_mem_SDot
  have hnorm : Subgroup.zpowers fDot ≤ Subgroup.normalizer (SDot : Set GL6) :=
    Subgroup.zpowers_le.2 mono_fDot_mem_normalizer
  have hord : orderOf fDot = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact mono_fDot_mul_self) mono_fDot_ne_one
  unfold TDot
  rw [mono_card_sup_of_le_normalizer _ _ hinf hnorm, card_SDot, Nat.card_zpowers, hord]

theorem mono_isPGroup_TDot : IsPGroup 2 ↥TDot :=
  IsPGroup.of_card (n := 7) (by rw [card_TDot]; norm_num)

theorem isSylowOf_TDot_M12 : CFSG.ASVolI.ChF.IsSylowOf 2 TDot (M1Dot ⊓ M2Dot) := by
  refine ⟨TDot_le_M12, mono_isPGroup_TDot, ?_⟩
  have h := Subgroup.relIndex_mul_card TDot (M1Dot ⊓ M2Dot)
  rw [inf_eq_left.2 TDot_le_M12, card_TDot, card_M12Dot] at h
  omega

theorem isSylowOf_TDot_MDot : CFSG.ASVolI.ChF.IsSylowOf 2 TDot MDot := by
  have hle : TDot ≤ MDot := TDot_le_M12.trans (inf_le_right.trans inf_le_left)
  refine ⟨hle, mono_isPGroup_TDot, ?_⟩
  have h := Subgroup.relIndex_mul_card TDot MDot
  rw [inf_eq_left.2 hle, card_TDot, card_MDot] at h
  omega

end

end CFSG.Quasithin.SimsF5
