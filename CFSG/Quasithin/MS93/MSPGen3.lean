module

public import CFSG.Quasithin.MS93.MSPHeis

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem mulVec_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (v : V4 F) :
    mat g *ᵥ v = v + (mat g (.inl 0) (.inr 0) * v (.inr 0) +
        mat g (.inl 0) (.inr 1) * v (.inr 1)) • e₁ F +
      (mat g (.inl 0) (.inr 1) * v (.inr 0) + mat g (.inl 1) (.inr 1) * v (.inr 1)) • e₂ F := by
  rw [Q₁_eq_radical] at hg
  obtain ⟨C, hC, rfl⟩ := hg
  have hC10 : C 1 0 = C 0 1 := by
    conv_lhs => rw [← hC]
    rfl
  have hent : ∀ i j, mat (tau hC) (.inl i) (.inr j) = C i j := by
    intro i j
    rw [mat_tau, blockMat, unitri_zero, Matrix.one_mul, fromBlocks_apply₁₂]
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri 0 C v
  simp only [hent]
  rw [mat_tau]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [e0, e1, e2, e3, hC10] <;> ring

theorem entry_symm_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) :
    mat g (.inl 1) (.inr 0) = mat g (.inl 0) (.inr 1) := by
  rw [mat_apply_eq, mulVec_of_mem_Q₁ hg]
  simp

theorem entry_mul_of_mem_Q₁ {g h : Sp4 F} (hg : g ∈ Q₁ F) (hh : h ∈ Q₁ F) (i j : Fin 2) :
    mat (g * h) (.inl i) (.inr j) = mat g (.inl i) (.inr j) + mat h (.inl i) (.inr j) := by
  rw [mat_apply_eq (g * h), mat_mul_mulVec, mulVec_of_mem_Q₁ hh, mulVec_of_mem_Q₁ hg]
  fin_cases i <;> fin_cases j <;> simp [entry_symm_of_mem_Q₁ hg, entry_symm_of_mem_Q₁ hh] <;> ring

theorem entry_one (i j : Fin 2) : mat (1 : Sp4 F) (.inl i) (.inr j) = 0 := by
  rw [mat_one, one_apply]
  simp

theorem entry_inv_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (i j : Fin 2) :
    mat g⁻¹ (.inl i) (.inr j) = -mat g (.inl i) (.inr j) := by
  have h := entry_mul_of_mem_Q₁ hg (inv_mem hg) i j
  rw [mul_inv_cancel, entry_one] at h
  linear_combination -h

theorem eq_of_mem_Q₁ {g h : Sp4 F} (hg : g ∈ Q₁ F) (hh : h ∈ Q₁ F)
    (h0 : mat g (.inl 0) (.inr 0) = mat h (.inl 0) (.inr 0))
    (h1 : mat g (.inl 0) (.inr 1) = mat h (.inl 0) (.inr 1))
    (h2 : mat g (.inl 1) (.inr 1) = mat h (.inl 1) (.inr 1)) : g = h :=
  ext_mulVec fun v => by rw [mulVec_of_mem_Q₁ hg, mulVec_of_mem_Q₁ hh, h0, h1, h2]

theorem transv_e₂_mem_Q₁ (c : F) : transv (e₂ F) c ∈ Q₁ F := fun v hv => by
  rw [transv_mulVec, form_e₂, (mem_ln₀.1 hv).2, mul_zero, zero_smul, add_zero]

theorem entry_transv_e₂ (c : F) (i j : Fin 2) :
    mat (transv (e₂ F) c) (.inl i) (.inr j) = if i = 1 ∧ j = 1 then c else 0 := by
  rw [mat_apply_eq, transv_mulVec, form_e₂]
  fin_cases i <;> fin_cases j <;> simp

section Card

variable [Finite F]

theorem card_le_sq_of_injOn {E : Subgroup (Sp4 F)} (x y : Sp4 F → F)
    (hxy : ∀ g ∈ E, ∀ h ∈ E, x g = x h → y g = y h → g = h) :
    Nat.card E ≤ Nat.card F ^ 2 := by
  have := Nat.card_le_card_of_injective (fun g : E => (x g, y g)) fun g h hgh =>
    Subtype.ext (hxy g g.2 h h.2 (congrArg Prod.fst hgh) (congrArg Prod.snd hgh))
  rwa [Nat.card_prod, ← sq] at this

theorem exists_entry00_ne_zero {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F ^ 2 < Nat.card E) : ∃ g ∈ E, mat g (.inl 0) (.inr 0) ≠ 0 := by
  by_contra h
  push Not at h
  refine absurd (card_le_sq_of_injOn (E := E) (fun g => mat g (.inl 0) (.inr 1))
    (fun g => mat g (.inl 1) (.inr 1)) fun g hg h' hh' h1 h2 =>
      eq_of_mem_Q₁ (hE hg) (hE hh') (by rw [h g hg, h h' hh']) h1 h2) (not_le.2 hc)

theorem exists_transv_e₂_mem {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F ^ 2 < Nat.card E) : ∃ c ≠ 0, transv (e₂ F) c ∈ E := by
  by_contra h
  push Not at h
  refine absurd (card_le_sq_of_injOn (E := E) (fun g => mat g (.inl 0) (.inr 0))
    (fun g => mat g (.inl 0) (.inr 1)) fun g hg g' hg' h1 h2 => ?_) (not_le.2 hc)
  have hk : g * g'⁻¹ ∈ E := mul_mem hg (inv_mem hg')
  have hkQ := hE hk
  have e00 : mat (g * g'⁻¹) (.inl 0) (.inr 0) = 0 := by
    rw [entry_mul_of_mem_Q₁ (hE hg) (inv_mem (hE hg')), entry_inv_of_mem_Q₁ (hE hg'), h1,
      add_neg_cancel]
  have e01 : mat (g * g'⁻¹) (.inl 0) (.inr 1) = 0 := by
    rw [entry_mul_of_mem_Q₁ (hE hg) (inv_mem (hE hg')), entry_inv_of_mem_Q₁ (hE hg'), h2,
      add_neg_cancel]
  have hkt : g * g'⁻¹ = transv (e₂ F) (mat (g * g'⁻¹) (.inl 1) (.inr 1)) :=
    eq_of_mem_Q₁ hkQ (transv_e₂_mem_Q₁ _) (by rw [e00, entry_transv_e₂]; simp)
      (by rw [e01, entry_transv_e₂]; simp) (by rw [entry_transv_e₂]; simp)
  have h11 : mat (g * g'⁻¹) (.inl 1) (.inr 1) = 0 := by
    by_contra hne
    exact h _ hne (hkt ▸ hk)
  rw [h11, transv_zero, mul_inv_eq_one] at hkt
  exact hkt

theorem exists_entry01_ne_zero {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F ^ 2 < Nat.card E) :
    ∃ g ∈ E, mat g (.inl 1) (.inr 1) = 0 ∧ mat g (.inl 0) (.inr 1) ≠ 0 := by
  by_contra h
  push Not at h
  refine absurd (card_le_sq_of_injOn (E := E) (fun g => mat g (.inl 0) (.inr 0))
    (fun g => mat g (.inl 1) (.inr 1)) fun g hg g' hg' h1 h2 => ?_) (not_le.2 hc)
  have hk : g * g'⁻¹ ∈ E := mul_mem hg (inv_mem hg')
  have hent : ∀ i j, mat (g * g'⁻¹) (.inl i) (.inr j) =
      mat g (.inl i) (.inr j) - mat g' (.inl i) (.inr j) := fun i j => by
    rw [entry_mul_of_mem_Q₁ (hE hg) (inv_mem (hE hg')), entry_inv_of_mem_Q₁ (hE hg'),
      sub_eq_add_neg]
  have e11 : mat (g * g'⁻¹) (.inl 1) (.inr 1) = 0 := by rw [hent, h2, sub_self]
  have e01 := h _ hk e11
  have hk1 : g * g'⁻¹ = 1 := eq_of_mem_Q₁ (hE hk) (one_mem _) (by rw [hent, h1, sub_self,
    entry_one]) (by rw [e01, entry_one]) (by rw [e11, entry_one])
  exact mul_inv_eq_one.1 hk1

theorem exists_full {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F) (hc : Nat.card F ^ 2 < Nat.card E) :
    ∃ l : F, ∀ a : F, ∃ g ∈ E, l * mat g (.inl 0) (.inr 0) + mat g (.inl 1) (.inr 1) = a := by
  classical
  have := Fintype.ofFinite F
  have := Fintype.ofFinite ↥E
  by_contra hne
  push Not at hne
  let e00 : ↥E → F := fun g => mat (g : Sp4 F) (.inl 0) (.inr 0)
  let e01 : ↥E → F := fun g => mat (g : Sp4 F) (.inl 0) (.inr 1)
  let e11 : ↥E → F := fun g => mat (g : Sp4 F) (.inl 1) (.inr 1)
  let ψ : F → (↥E →* Multiplicative F) := fun l =>
    { toFun := fun g => Multiplicative.ofAdd (l * e00 g + e11 g)
      map_one' := by simp [e00, e11, entry_one]
      map_mul' := fun g h => by
        simp only [e00, e11, Subgroup.coe_mul]
        rw [entry_mul_of_mem_Q₁ (hE g.2) (hE h.2), entry_mul_of_mem_Q₁ (hE g.2) (hE h.2),
          ← ofAdd_add]
        congr 1
        ring }
  have hkercard : ∀ l, Nat.card (ψ l).ker =
      (Finset.univ.filter fun g : ↥E => l * e00 g + e11 g = 0).card := by
    intro l
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [MonoidHom.mem_ker]
    exact ofAdd_eq_one
  have hker : ∀ l, 2 * Nat.card E ≤ Nat.card F * Nat.card (ψ l).ker := by
    intro l
    have h1 : Nat.card (ψ l).ker * Nat.card (ψ l).range = Nat.card E := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h2 : (ψ l).range ≠ ⊤ := by
      intro htop
      obtain ⟨a, ha⟩ := hne l
      obtain ⟨g, hg⟩ := (htop ▸ Subgroup.mem_top (Multiplicative.ofAdd a) :
        Multiplicative.ofAdd a ∈ (ψ l).range)
      exact ha g g.2 (Multiplicative.ofAdd.injective hg)
    have h3 : Nat.card (ψ l).range ∣ Nat.card F := Subgroup.card_subgroup_dvd_card _
    have h4 : Nat.card (ψ l).range ≠ Nat.card F := fun h =>
      h2 (Subgroup.eq_top_of_card_eq _ (h.trans rfl))
    obtain ⟨m, hm⟩ := h3
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact h4 (by rw [hm, mul_one])
    have hm2 : 2 ≤ m := by omega
    calc 2 * Nat.card E = Nat.card (ψ l).ker * (2 * Nat.card (ψ l).range) := by
          rw [← h1]; ring
      _ ≤ Nat.card (ψ l).ker * (m * Nat.card (ψ l).range) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm2)
      _ = Nat.card F * Nat.card (ψ l).ker := by rw [hm]; ring
  have hsum : ∑ l : F, (Finset.univ.filter fun g : ↥E => l * e00 g + e11 g = 0).card =
      ∑ g : ↥E, (Finset.univ.filter fun l : F => l * e00 g + e11 g = 0).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hpt : ∀ g : ↥E, (Finset.univ.filter fun l : F => l * e00 g + e11 g = 0).card ≤
      1 + if e00 g = 0 ∧ e11 g = 0 then Nat.card F else 0 := by
    intro g
    by_cases h0 : e00 g = 0
    · by_cases h1 : e11 g = 0
      · simp only [h0, h1, and_self, ↓reduceIte]
        rw [Nat.card_eq_fintype_card]
        exact (Finset.card_le_univ _).trans (Nat.le_add_left _ _)
      · simp only [h1, and_false, ↓reduceIte]
        refine (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun l _ => ?_)).le.trans
          (Nat.zero_le _)
        rw [h0, mul_zero, zero_add]
        exact h1
    · refine (Finset.card_le_one.2 fun a ha b hb => ?_).trans (Nat.le_add_right _ _)
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      have : (a - b) * e00 g = 0 := by linear_combination ha' - hb'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hZ : (Finset.univ.filter fun g : ↥E => e00 g = 0 ∧ e11 g = 0).card ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn e01 (fun _ _ => Finset.mem_univ _) fun g hg g' hg' h => ?_
    have hg1 := (Finset.mem_filter.1 hg).2
    have hg2 := (Finset.mem_filter.1 hg').2
    exact Subtype.ext (eq_of_mem_Q₁ (hE g.2) (hE g'.2) (hg1.1.trans hg2.1.symm) h
      (hg1.2.trans hg2.2.symm))
  have hK : ∑ l : F, Nat.card (ψ l).ker ≤ Nat.card E + Nat.card F * Nat.card F := by
    simp only [hkercard]
    rw [hsum]
    calc ∑ g : ↥E, (Finset.univ.filter fun l : F => l * e00 g + e11 g = 0).card
        ≤ ∑ g : ↥E, (1 + if e00 g = 0 ∧ e11 g = 0 then Nat.card F else 0) :=
          Finset.sum_le_sum fun g _ => hpt g
      _ = Nat.card E + Nat.card F *
            (Finset.univ.filter fun g : ↥E => e00 g = 0 ∧ e11 g = 0).card := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one,
            Finset.card_univ, ← Nat.card_eq_fintype_card, mul_comm]
      _ ≤ Nat.card E + Nat.card F * Nat.card F := by
          gcongr
  have hK2 : Nat.card F * (2 * Nat.card E) ≤ Nat.card F * ∑ l : F, Nat.card (ψ l).ker := by
    calc Nat.card F * (2 * Nat.card E) = ∑ _l : F, 2 * Nat.card E := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
      _ ≤ ∑ l : F, Nat.card F * Nat.card (ψ l).ker := Finset.sum_le_sum fun l _ => hker l
      _ = Nat.card F * ∑ l : F, Nat.card (ψ l).ker := by rw [Finset.mul_sum]
  have hq0 : 0 < Nat.card F := Nat.card_pos
  have h2E : 2 * Nat.card E ≤ ∑ l : F, Nat.card (ψ l).ker := Nat.le_of_mul_le_mul_left hK2 hq0
  have : Nat.card E ≤ Nat.card F ^ 2 := by nlinarith
  omega

end Card

section CharTwo

variable [CharP F 2]

theorem muE_mul_self (a : F) : muE a * muE a = 1 := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, muE_mulVec, muE_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> grind

theorem muE_inv (a : F) : (muE a)⁻¹ = muE a := inv_eq_of_mul_eq_one_right (muE_mul_self a)

theorem muE_mem_P₁ (a : F) : muE a ∈ P₁ F := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [muE_mulVec]
  exact mem_ln₀.2 ⟨by simp [h0, h1], by simp [h1]⟩

theorem muE_mem_stab_ln₀' (a : F) : muE a ∈ stab (ln₀' F) := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  rw [muE_mulVec]
  exact mem_ln₀'.2 ⟨by simp [h0], by simp [h0, h1]⟩

theorem muE_conj_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (s : F) : muE s * g * (muE s)⁻¹ ∈ Q₁ F :=
  (P₁_le_normalizer_Q₁ (muE_mem_P₁ s) g).1 hg

theorem entry11_muE_conj {g : Sp4 F} (hg : g ∈ Q₁ F) (s : F) :
    mat (muE s * g * (muE s)⁻¹) (.inl 1) (.inr 1) =
      s ^ 2 * mat g (.inl 0) (.inr 0) + mat g (.inl 1) (.inr 1) := by
  rw [muE_inv, mat_apply_eq, mat_mul_mulVec, mat_mul_mulVec, muE_mulVec, mulVec_of_mem_Q₁ hg,
    muE_mulVec]
  simp
  grind

@[expose] def jSwap (F : Type) [Field F] : Sp4 F := wOne F * wTwo F

theorem jSwap_mulVec (v : V4 F) :
    mat (jSwap F) *ᵥ v = v (.inr 0) • e₁ F + v (.inr 1) • e₂ F + v (.inl 0) • f₁ F +
      v (.inl 1) • f₂ F := by
  rw [jSwap, mat_mul_mulVec, wTwo_mulVec, wOne_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem jSwap_mul_self : jSwap F * jSwap F = 1 := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, jSwap_mulVec, jSwap_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem jSwap_inv : (jSwap F)⁻¹ = jSwap F := inv_eq_of_mul_eq_one_right jSwap_mul_self

theorem ln₀'_map_jSwap : (ln₀' F).map (mulVecLin (mat (jSwap F))) = ln₀ F := by
  ext v
  rw [mem_map_mulVecLin, jSwap_inv, mem_ln₀', mem_ln₀, jSwap_mulVec]
  simp

theorem qLine_ln₀'_map_jSwap :
    (qLine (ln₀' F)).map (MulAut.conj (jSwap F)).toMonoidHom = Q₁ F := by
  rw [fixer_map_conj, ln₀'_map_jSwap]

theorem qe_conj_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (x y s : F) :
    g * qe x y s * g⁻¹ = qe (x + mat g (.inl 1) (.inr 1) * y) y s := by
  have hge : mat g *ᵥ e₁ F = e₁ F := hg _ (mem_ln₀.2 ⟨by simp, by simp⟩)
  rw [qe, qw_conj hge (by simp)]
  have h : mat g *ᵥ (x • e₂ F + y • f₂ F) = ((x + mat g (.inl 1) (.inr 1) * y) • e₂ F +
      y • f₂ F) + (mat g (.inl 0) (.inr 1) * y) • e₁ F := by
    rw [mulVec_of_mem_Q₁ hg]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  rw [h, qw_add_e₁ (by simp)]
  rfl

theorem eq_qe_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (h11 : mat g (.inl 1) (.inr 1) = 0) :
    g = qe (mat g (.inl 0) (.inr 1)) 0 (mat g (.inl 0) (.inr 0)) := by
  refine ext_mulVec fun v => ?_
  rw [mulVec_of_mem_Q₁ hg, qe_mulVec, h11]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

omit [CharP F 2] in
theorem qe_congr {x y s x' y' s' : F} (hx : x = x') (hy : y = y') (hs : s = s') :
    qe x y s = qe x' y' s' := by
  rw [hx, hy, hs]

theorem sup_eq_top_core [Finite F] (hq : 2 < Nat.card F) {E E' : Subgroup (Sp4 F)}
    (hE : E ≤ Q₁ F) (hfull : ∀ a : F, ∃ g ∈ E, mat g (.inl 1) (.inr 1) = a)
    (hEQ : ∃ g ∈ E, mat g (.inl 1) (.inr 1) = 0 ∧ mat g (.inl 0) (.inr 1) ≠ 0)
    {c : F} (hc : c ≠ 0) (ht : transv (f₂ F) c ∈ E')
    (hopp : ∃ g ∈ E', (mat g *ᵥ e₁ F) (.inr 0) ≠ 0) : E ⊔ E' = ⊤ := by
  set H := E ⊔ E'
  have hEH : ∀ g ∈ E, g ∈ H := fun g hg => Subgroup.mem_sup_left hg
  have htH : transv (f₂ F) c ∈ H := Subgroup.mem_sup_right ht
  obtain ⟨n₀, hn₀, hn11, hβ⟩ := hEQ
  set β := mat n₀ (.inl 0) (.inr 1)
  have hcβ : c * β ≠ 0 := mul_ne_zero hc hβ
  have hn₀H : qe β 0 (mat n₀ (.inl 0) (.inr 0)) ∈ H :=
    eq_qe_of_mem_Q₁ (hE hn₀) hn11 ▸ hEH _ hn₀
  have hconjE : ∀ a x y s, qe x y s ∈ H → qe (x + a * y) y s ∈ H := by
    intro a x y s h
    obtain ⟨g, hg, hga⟩ := hfull a
    have := mul_mem (mul_mem (hEH g hg) h) (inv_mem (hEH g hg))
    rwa [qe_conj_of_mem_Q₁ (hE hg), hga] at this
  have hconjt : ∀ x y s, qe x y s ∈ H → qe x (y + c * x) s ∈ H := by
    intro x y s h
    have := mul_mem (mul_mem htH h) (inv_mem htH)
    rwa [qe_conj_transv_f₂] at this
  have hmul : ∀ x y s x' y' s', qe x y s ∈ H → qe x' y' s' ∈ H →
      qe (x + x') (y + y') (s + s' + x * y' + x' * y) ∈ H := fun x y s x' y' s' h h' => by
    rw [← qe_mul]
    exact mul_mem h h'
  have hA : qe 0 (c * β) (c * β ^ 2) ∈ H := by
    have := hmul _ _ _ _ _ _ hn₀H (hconjt _ _ _ hn₀H)
    convert this using 1
    refine qe_congr ?_ ?_ ?_ <;> grind
  have hB : ∀ x, qe x 0 (x * c * β) ∈ H := by
    intro x
    have := hmul _ _ _ _ _ _ hA (hconjE (x / (c * β)) _ _ _ hA)
    convert this using 1
    refine qe_congr ?_ ?_ ?_
    · field_simp
      ring
    · grind
    · field_simp
      grind
  have hC : ∀ y, qe 0 y (y ^ 2 / c) ∈ H := by
    intro y
    have h1 := hB (y / c)
    have := hmul _ _ _ _ _ _ h1 (hconjt _ _ _ h1)
    convert this using 1
    refine qe_congr ?_ ?_ ?_
    · grind
    · field_simp
      ring
    · field_simp
      grind
  have hD : ∀ a y, transv (e₁ F) (a * y * (c * β + y)) ∈ H := by
    intro a y
    have h1 := hconjE a _ _ _ (hC y)
    have h2 := hmul _ _ _ _ _ _ (hB (a * y)) (hC y)
    have := hmul _ _ _ _ _ _ h1 h2
    rw [← qe_zero_zero]
    convert this using 1
    refine qe_congr ?_ ?_ ?_ <;> grind
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one hq
  have hy0 : l * (c * β) * (c * β + l * (c * β)) ≠ 0 := by
    have hl1' : 1 + l ≠ 0 := fun h => hl1 (by grind)
    have : l * (c * β) * (c * β + l * (c * β)) = l * (1 + l) * (c * β) ^ 2 := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hl0 hl1') (pow_ne_zero 2 hcβ)
  have hX : ∀ r : F, transv (e₁ F) r ∈ H := fun r => by
    have := hD (r / (l * (c * β) * (c * β + l * (c * β)))) (l * (c * β))
    rwa [mul_assoc, div_mul_cancel₀ _ hy0] at this
  have hQ₂ : Q₂ F ≤ H := fun g hg => by
    obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hg
    have h1 := hmul _ _ _ _ _ _ (hB x) (hC y)
    have h2 := hmul _ _ _ _ _ _ h1 (show qe 0 0 (s - (x * c * β + y ^ 2 / c + x * y)) ∈ H by
      rw [qe_zero_zero]
      exact hX _)
    convert h2 using 1
    refine qe_congr ?_ ?_ ?_ <;> ring
  obtain ⟨g', hg', hopp'⟩ := hopp
  have hg'H : g' ∈ H := Subgroup.mem_sup_right hg'
  have hmap : (Q₂ F).map (MulAut.conj g').toMonoidHom = qPoint (F ∙ (mat g' *ᵥ e₁ F)) := by
    rw [qPoint_map_conj, pt₀_eq_span, Submodule.map_span, Set.image_singleton, mulVecLin_apply]
  refine eq_top_iff.2 ?_
  rw [← Q₂_sup_qPoint_of_opp hopp', ← hmap]
  refine sup_le hQ₂ ?_
  rintro _ ⟨u, hu, rfl⟩
  exact mul_mem (mul_mem hg'H (hQ₂ hu)) (inv_mem hg'H)

end CharTwo

theorem map_mat_mul (g h : Sp4 F) (W : Submodule F (V4 F)) :
    W.map (mulVecLin (mat (g * h))) = (W.map (mulVecLin (mat h))).map (mulVecLin (mat g)) := by
  rw [mat_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

theorem exists_map_ln₀_ln₀' {l l' : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (hopp : l ⊓ l' = ⊥) : ∃ g : Sp4 F, (ln₀ F).map (mulVecLin (mat g)) = l ∧
      (ln₀' F).map (mulVecLin (mat g)) = l' := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  obtain ⟨l'', hl''⟩ : ∃ l'', l'' = l'.map (mulVecLin (mat g⁻¹)) := ⟨_, rfl⟩
  have hgl' : l' = l''.map (mulVecLin (mat g)) := by rw [hl'', map_map_mat_inv]
  have hopp'' : l'' ⊓ ln₀ F = ⊥ := by
    have := congrArg (Submodule.map (mulVecLin (mat g⁻¹))) hopp
    rw [map_inf_map, Submodule.map_bot, map_map_mat_inv', ← hl''] at this
    rw [inf_comm, this]
  have hll : IsLine l'' := hl'' ▸ isLine_map hl' g⁻¹
  obtain ⟨C, hC, hCl⟩ := exists_eq_map_tau hll hopp''
  refine ⟨g * tau hC, ?_, ?_⟩
  · rw [map_mat_mul, mem_stab_iff.1 (fixer_le_stab _ (tau_mem_Q₁ hC))]
  · rw [map_mat_mul, ← hCl, hgl']

theorem sup_eq_top_of_map_conj {E E' : Subgroup (Sp4 F)} (g : Sp4 F)
    (h : E.map (MulAut.conj g).toMonoidHom ⊔ E'.map (MulAut.conj g).toMonoidHom = ⊤) :
    E ⊔ E' = ⊤ := by
  have hs : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  have hi : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← Subgroup.map_sup, ← Subgroup.map_top_of_surjective _ hs] at h
  exact Subgroup.map_injective hi h

theorem qLine_map_conj_inv {l : Submodule F (V4 F)} (g : Sp4 F)
    (hl : (ln₀ F).map (mulVecLin (mat g)) = l) :
    (qLine l).map (MulAut.conj g⁻¹).toMonoidHom = Q₁ F := by
  rw [fixer_map_conj, ← hl, map_map_mat_inv']

theorem qLine'_map_conj_inv {l : Submodule F (V4 F)} (g : Sp4 F)
    (hl : (ln₀' F).map (mulVecLin (mat g)) = l) :
    (qLine l).map (MulAut.conj g⁻¹).toMonoidHom = qLine (ln₀' F) := by
  rw [fixer_map_conj, ← hl, map_map_mat_inv']

section Main

variable [Finite F] [CharP F 2]

theorem sup_eq_top_std {E E' : Subgroup (Sp4 F)} (hq : 2 < Nat.card F) (hE : E ≤ Q₁ F)
    (hE' : E' ≤ qLine (ln₀' F)) (hEc : Nat.card F ^ 2 < Nat.card E)
    (hE'c : Nat.card F ^ 2 < Nat.card E') : E ⊔ E' = ⊤ := by
  obtain ⟨l, hl⟩ := exists_full hE hEc
  obtain ⟨s, hs⟩ : ∃ s : F, s ^ 2 = l := ⟨(frobeniusEquiv F 2).symm l, by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]⟩
  refine sup_eq_top_of_map_conj (muE s) ?_
  set E₁ := E.map (MulAut.conj (muE s)).toMonoidHom
  set E₁' := E'.map (MulAut.conj (muE s)).toMonoidHom
  have hE₁ : E₁ ≤ Q₁ F := by
    rintro _ ⟨g, hg, rfl⟩
    exact muE_conj_mem_Q₁ (hE hg) s
  have hfull : ∀ a : F, ∃ g ∈ E₁, mat g (.inl 1) (.inr 1) = a := fun a => by
    obtain ⟨g, hg, hga⟩ := hl a
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    change mat (muE s * g * (muE s)⁻¹) (.inl 1) (.inr 1) = a
    rw [entry11_muE_conj (hE hg), hs, hga]
  have hE₁' : E₁' ≤ qLine (ln₀' F) := by
    rintro _ ⟨g, hg, rfl⟩
    exact (stab_le_normalizer_fixer _ (muE_mem_stab_ln₀' s) g).1 (hE' hg)
  have hc₁ : Nat.card F ^ 2 < Nat.card E₁ := by rwa [card_map_conj]
  have hc₁' : Nat.card F ^ 2 < Nat.card E₁' := by rwa [card_map_conj]
  set E₂ := E₁'.map (MulAut.conj (jSwap F)).toMonoidHom
  have hE₂ : E₂ ≤ Q₁ F := by
    rw [← qLine_ln₀'_map_jSwap]
    exact Subgroup.map_mono hE₁'
  have hc₂ : Nat.card F ^ 2 < Nat.card E₂ := by rwa [card_map_conj]
  obtain ⟨c, hc, htc⟩ := exists_transv_e₂_mem hE₂ hc₂
  have ht : transv (f₂ F) c ∈ E₁' := by
    obtain ⟨u, hu, hut⟩ := htc
    have hu' : u = transv (f₂ F) c := by
      have h1 : (jSwap F)⁻¹ * transv (e₂ F) c * (jSwap F)⁻¹⁻¹ = u := by
        rw [← hut]
        change (jSwap F)⁻¹ * (jSwap F * u * (jSwap F)⁻¹) * (jSwap F)⁻¹⁻¹ = u
        group
      rw [← h1, transv_conj, jSwap_inv, jSwap_mulVec]
      congr 1
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    exact hu' ▸ hu
  have hopp : ∃ g ∈ E₁', (mat g *ᵥ e₁ F) (.inr 0) ≠ 0 := by
    obtain ⟨g₂, ⟨u, hu, rfl⟩, hb⟩ := exists_entry00_ne_zero hE₂ hc₂
    refine ⟨u, hu, ?_⟩
    change mat (jSwap F * u * (jSwap F)⁻¹) (.inl 0) (.inr 0) ≠ 0 at hb
    have hJf : mat (jSwap F) *ᵥ f₁ F = e₁ F := by
      rw [jSwap_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    rw [jSwap_inv, mat_apply_eq, mat_mul_mulVec, mat_mul_mulVec, hJf, jSwap_mulVec] at hb
    simpa using hb
  exact sup_eq_top_core hq hE₁ hfull (exists_entry01_ne_zero hE₁ hc₁) hc ht hopp

omit [CharP F 2] in
theorem eq_qLine_of_card_two {l : Submodule F (V4 F)} (hl : IsLine l) (hq : Nat.card F = 2)
    {E : Subgroup (Sp4 F)} (hE : E ≤ qLine l) (hEc : Nat.card F ^ 2 < Nat.card E) :
    E = qLine l := by
  have hdvd : Nat.card E ∣ Nat.card F ^ 3 := card_qLine hl ▸ Subgroup.card_dvd_of_le hE
  rw [hq] at hdvd hEc
  norm_num at hdvd hEc
  have hle : Nat.card E ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have h8 : Nat.card E = 8 := by
    interval_cases h : Nat.card E <;> omega
  exact Subgroup.eq_of_le_of_card_ge hE (by rw [card_qLine hl, hq, h8]; norm_num)

theorem sup_eq_top_of_le_qLine {l l' : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (hopp : l ⊓ l' = ⊥) {E E' : Subgroup (Sp4 F)} (hE : E ≤ qLine l) (hE' : E' ≤ qLine l')
    (hEc : Nat.card F ^ 2 < Nat.card E) (hE'c : Nat.card F ^ 2 < Nat.card E') :
    E ⊔ E' = ⊤ := by
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases h2.eq_or_lt with hq | hq
  · rw [eq_qLine_of_card_two hl hq.symm hE hEc, eq_qLine_of_card_two hl' hq.symm hE' hE'c]
    exact qLine_sup_qLine_eq_top hl hl' hopp
  obtain ⟨g, hgl, hgl'⟩ := exists_map_ln₀_ln₀' hl hl' hopp
  refine sup_eq_top_of_map_conj g⁻¹ (sup_eq_top_std hq ?_ ?_ ?_ ?_)
  · rw [← qLine_map_conj_inv g hgl]
    exact Subgroup.map_mono hE
  · rw [← qLine'_map_conj_inv g hgl']
    exact Subgroup.map_mono hE'
  · rwa [card_map_conj]
  · rwa [card_map_conj]

theorem exists_det_ne_zero {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F < Nat.card E) : ∃ u ∈ E,
      mat u (.inl 0) (.inr 0) * mat u (.inl 1) (.inr 1) - mat u (.inl 0) (.inr 1) ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ x y : F, x ^ 2 = y ^ 2 → x = y := fun x y hxy => by
    have : (x + y) ^ 2 = 0 := by linear_combination hxy + (x * y + y ^ 2) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linear_combination this - y * h2
  have hcard1 : ∀ f : Sp4 F → F, (∀ u ∈ E, ∀ u' ∈ E, f u = f u' → u = u') →
      Nat.card E ≤ Nat.card F := fun f hf =>
    Nat.card_le_card_of_injective (fun u : E => f u) fun u u' huu =>
      Subtype.ext (hf u u.2 u' u'.2 huu)
  obtain ⟨u₁, hu₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((Subgroup.one_lt_card_iff_ne_bot E).1 (lt_of_le_of_lt Nat.card_pos hc))
  set b₁ := mat (u₁ : Sp4 F) (.inl 0) (.inr 0)
  set c₁ := mat (u₁ : Sp4 F) (.inl 0) (.inr 1)
  set d₁ := mat (u₁ : Sp4 F) (.inl 1) (.inr 1)
  have hu₁E : (u₁ : Sp4 F) ∈ E := u₁.2
  have key : ∀ u ∈ E, mat u (.inl 0) (.inr 0) * d₁ + b₁ * mat u (.inl 1) (.inr 1) = 0 := by
    intro u hu
    have h1 := h u hu
    have h3 := h _ hu₁E
    have h4 := h _ (mul_mem hu hu₁E)
    rw [entry_mul_of_mem_Q₁ (hE hu) (hE hu₁E), entry_mul_of_mem_Q₁ (hE hu) (hE hu₁E),
      entry_mul_of_mem_Q₁ (hE hu) (hE hu₁E)] at h4
    linear_combination h4 - h1 - h3 + (mat u (.inl 0) (.inr 1) * c₁) * h2
  by_cases hb₁ : b₁ = 0
  · have hc₁ : c₁ = 0 := by
      have := h _ hu₁E
      rw [show mat (u₁ : Sp4 F) (.inl 0) (.inr 0) = b₁ from rfl, hb₁, zero_mul, zero_sub,
        neg_eq_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hd₁ : d₁ ≠ 0 := by
      intro hd₁
      have h1 : (u₁ : Sp4 F) = 1 := eq_of_mem_Q₁ (hE hu₁E) (one_mem _)
        (by rw [entry_one]; exact hb₁) (by rw [entry_one]; exact hc₁)
        (by rw [entry_one]; exact hd₁)
      exact hu₁1 (Subtype.ext h1)
    have hb : ∀ u ∈ E, mat u (.inl 0) (.inr 0) = 0 := fun u hu => by
      have := key u hu
      rw [hb₁, zero_mul, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hd₁
    have hcz : ∀ u ∈ E, mat u (.inl 0) (.inr 1) = 0 := fun u hu => by
      have := h u hu
      rw [hb u hu, zero_mul, zero_sub, neg_eq_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    refine absurd (hcard1 (fun u => mat u (.inl 1) (.inr 1)) fun u hu u' hu' huu =>
      eq_of_mem_Q₁ (hE hu) (hE hu') (by rw [hb u hu, hb u' hu'])
        (by rw [hcz u hu, hcz u' hu']) huu) (not_le.2 hc)
  · have hd : ∀ u ∈ E, mat u (.inl 1) (.inr 1) = mat u (.inl 0) (.inr 0) * d₁ / b₁ :=
      fun u hu => by
        rw [eq_div_iff hb₁]
        linear_combination (key u hu) - (mat u (.inl 0) (.inr 0) * d₁) * h2
    refine absurd (hcard1 (fun u => mat u (.inl 0) (.inr 0)) fun u hu u' hu' huu => ?_)
      (not_le.2 hc)
    have hdd : mat u (.inl 1) (.inr 1) = mat u' (.inl 1) (.inr 1) := by
      rw [hd u hu, hd u' hu', huu]
    refine eq_of_mem_Q₁ (hE hu) (hE hu') huu (hsq _ _ ?_) hdd
    have h1 := h u hu
    have h1' := h u' hu'
    linear_combination h1' - h1 + mat u (.inl 1) (.inr 1) * huu + mat u' (.inl 0) (.inr 0) * hdd

omit [Finite F] [CharP F 2] in
theorem map_ln₀'_inf_eq_bot {u : Sp4 F} (hu : u ∈ Q₁ F)
    (hdet : mat u (.inl 0) (.inr 0) * mat u (.inl 1) (.inr 1) - mat u (.inl 0) (.inr 1) ^ 2 ≠ 0) :
    (ln₀' F).map (mulVecLin (mat u)) ⊓ ln₀' F = ⊥ := by
  refine eq_bot_iff.2 fun w ⟨⟨v, hv, hvw⟩, hw⟩ => ?_
  rw [mulVecLin_apply] at hvw
  subst hvw
  obtain ⟨hv0, hv1⟩ := mem_ln₀'.1 hv
  obtain ⟨hw0, hw1⟩ := mem_ln₀'.1 hw
  rw [mulVec_of_mem_Q₁ hu] at hw0 hw1
  simp [hv0, hv1] at hw0 hw1
  have h3 : v (.inr 0) = 0 := by
    have : (mat u (.inl 0) (.inr 0) * mat u (.inl 1) (.inr 1) - mat u (.inl 0) (.inr 1) ^ 2) *
        v (.inr 0) = 0 := by
      linear_combination mat u (.inl 1) (.inr 1) * hw0 - mat u (.inl 0) (.inr 1) * hw1
    exact (mul_eq_zero.1 this).resolve_left hdet
  have h4 : v (.inr 1) = 0 := by
    have : (mat u (.inl 0) (.inr 0) * mat u (.inl 1) (.inr 1) - mat u (.inl 0) (.inr 1) ^ 2) *
        v (.inr 1) = 0 := by
      linear_combination mat u (.inl 0) (.inr 0) * hw1 - mat u (.inl 0) (.inr 1) * hw0
    exact (mul_eq_zero.1 this).resolve_left hdet
  have hv' : v = 0 := ext4 (by simp [hv0]) (by simp [hv1]) (by simp [h3]) (by simp [h4])
  rw [Submodule.mem_bot, hv', mulVec_zero]

theorem sup_eq_top_std' {E E' : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hE' : E' ≤ qLine (ln₀' F)) (hEc : Nat.card F < Nat.card E)
    (hE'c : Nat.card F ^ 2 < Nat.card E') : E ⊔ E' = ⊤ := by
  obtain ⟨u, hu, hdet⟩ := exists_det_ne_zero hE hEc
  have hsym := sup_eq_top_of_le_qLine (isLine_map isLine_ln₀' u) isLine_ln₀'
    (map_ln₀'_inf_eq_bot (hE hu) hdet) (E := E'.map (MulAut.conj u).toMonoidHom) (E' := E')
    (by rw [qLine_map]; exact Subgroup.map_mono hE') hE' (by rwa [card_map_conj]) hE'c
  refine eq_top_iff.2 (hsym ▸ sup_le ?_ le_sup_right)
  rintro _ ⟨x, hx, rfl⟩
  have huH : u ∈ E ⊔ E' := Subgroup.mem_sup_left hu
  exact mul_mem (mul_mem huH (Subgroup.mem_sup_right hx)) (inv_mem huH)

theorem sup_eq_top_of_le_qLine' {l l' : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (hopp : l ⊓ l' = ⊥) {E E' : Subgroup (Sp4 F)} (hE : E ≤ qLine l) (hE' : E' ≤ qLine l')
    (hEc : Nat.card F < Nat.card E) (hE'c : Nat.card F ^ 2 < Nat.card E') : E ⊔ E' = ⊤ := by
  obtain ⟨g, hgl, hgl'⟩ := exists_map_ln₀_ln₀' hl hl' hopp
  refine sup_eq_top_of_map_conj g⁻¹ (sup_eq_top_std' ?_ ?_ ?_ ?_)
  · rw [← qLine_map_conj_inv g hgl]
    exact Subgroup.map_mono hE
  · rw [← qLine'_map_conj_inv g hgl']
    exact Subgroup.map_mono hE'
  · rwa [card_map_conj]
  · rwa [card_map_conj]

end Main

end CFSG.Quasithin.MS93.MSP
