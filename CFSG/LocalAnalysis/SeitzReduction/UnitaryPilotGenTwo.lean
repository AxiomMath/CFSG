module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocksBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix Function CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Unitary (herm herm_add_left herm_add_right herm_smul_left
  herm_smul_right herm_sub_right herm_single_left herm_single_right herm_zero_left
  herm_self_fixed herm_smul_smul conj_smul_of_tv transport T tvSet
  exists_mem_T_smul_eq_of_iso exists_mem_T_smul_eq_of_norm_one T_eq_top)
open CFSG.LieType.Universal.Unitary (SUid)

section Bridge

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem SUid_barEquiv_eq_unitarySU (n : ℕ) : SUid h.barEquiv n = unitarySU p f K n := by
  ext A
  rw [mem_unitarySU_iff h]
  exact Iff.rfl

@[expose] noncomputable def suidEquiv (n : ℕ) : SUid h.barEquiv n ≃* unitarySU p f K n :=
  MulEquiv.subgroupCongr (SUid_barEquiv_eq_unitarySU h n)

theorem coe_suidEquiv {n : ℕ} (x : SUid h.barEquiv n) :
    ((suidEquiv h n x : unitarySU p f K n) : GL (Fin n) K) = (x : GL (Fin n) K) :=
  rfl

end Bridge

section Block

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem coe_apply_eq_smul_single (g : SUid h.barEquiv n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = (g • (Pi.single j 1 : Fin n → K)) i := by
  rw [CFSG.ClassicalGroups.Unitary.smul_def, mulVec_single_one]
  rfl

theorem suidEquiv_mem_unitaryBlock_of_smul {I : Finset (Fin n)} {g : SUid h.barEquiv n}
    (h1 : ∀ j ∉ I, g • (Pi.single j 1 : Fin n → K) = Pi.single j 1)
    (h2 : ∀ j ∈ I, ∀ i ∉ I, (g • (Pi.single j 1 : Fin n → K)) i = 0) :
    suidEquiv h n g ∈ unitaryBlock h I := by
  rw [mem_unitaryBlock]
  intro i j hij
  rw [coe_suidEquiv, coe_apply_eq_smul_single]
  by_cases hj : j ∈ I
  · have hi : i ∉ I := hij.resolve_right (not_not.2 hj)
    rw [h2 j hj i hi, one_apply_ne (by rintro rfl; exact hi hj)]
  · rw [h1 j hj, Pi.single_apply, one_apply]

theorem suidEquiv_mem_unitaryBlock_of_tv {I : Finset (Fin n)} {a : Fin n → K}
    (haI : ∀ i ∉ I, a i = 0) {c : K} {g : SUid h.barEquiv n}
    (hg : ∀ v, g • v = v + (c * herm h.barEquiv a v) • a) :
    suidEquiv h n g ∈ unitaryBlock h I := by
  refine suidEquiv_mem_unitaryBlock_of_smul h (fun j hj => ?_) (fun j hj i hi => ?_)
  · rw [hg, herm_single_right, haI j hj, map_zero, zero_mul, mul_zero, zero_smul, add_zero]
  · rw [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, haI i hi, mul_zero, add_zero,
      Pi.single_eq_of_ne (show i ≠ j by rintro rfl; exact hi hj)]

end Block

section Embed

variable {K : Type} [Field K] (σ : K ≃+* K) {m n : ℕ} {s : Fin m → Fin n}

theorem herm_extend (hs : Injective s) (u v : Fin m → K) :
    herm σ (extend s u 0) (extend s v 0) = herm σ u v := by
  rw [CFSG.ClassicalGroups.Unitary.herm_def, CFSG.ClassicalGroups.Unitary.herm_def]
  symm
  refine Fintype.sum_of_injective s hs _ _ (fun b hb => ?_) (fun a => ?_)
  · rw [extend_apply' _ _ _ (fun ⟨a, ha⟩ => hb ⟨a, ha⟩)]
    simp
  · rw [hs.extend_apply, hs.extend_apply]

theorem extend_single (hs : Injective s) (k : Fin m) :
    extend s (Pi.single k (1 : K)) 0 = Pi.single (s k) 1 := by
  funext i
  by_cases hi : ∃ a, s a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [hs.extend_apply]
    by_cases hak : a = k
    · subst hak
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hak, Pi.single_eq_of_ne (hs.ne hak)]
  · rw [extend_apply' _ _ _ hi, Pi.single_eq_of_ne (fun e => hi ⟨k, e.symm⟩)]
    rfl

theorem herm_extend_eq_zero_of_apply_eq_zero {v : Fin n → K}
    (hv : ∀ k, v (s k) = 0) (u : Fin m → K) : herm σ (extend s u 0) v = 0 := by
  rw [CFSG.ClassicalGroups.Unitary.herm_def]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : ∃ a, s a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [hv a, mul_zero]
  · rw [extend_apply' _ _ _ hi]
    simp

end Embed

section Local

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

theorem exists_mem_T_smul_apply_eq_zero (hm : 4 ≤ m) {w : Fin m → K} (hw : w ≠ 0) :
    ∃ t ∈ T h.barEquiv m, ∃ k, (t • w) k = 0 := by
  have hσ := h.isUnitaryInvolution_barEquiv
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set i₂ : Fin m := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  by_cases hww : herm h.barEquiv w w = 0
  · obtain ⟨μ, hμ⟩ := hσ.exists_norm_neg_one
    set w' : Fin m → K := Pi.single i₁ 1 + μ • Pi.single i₂ 1 with hw'def
    have hw' : herm h.barEquiv w' w' = 0 := by
      rw [hw'def]
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_single_left,
        Pi.single_eq_same, Pi.single_eq_of_ne h12, Pi.single_eq_of_ne h12.symm, map_one,
        mul_one, mul_zero]
      linear_combination hμ
    have hw'0 : w' ≠ 0 := by
      intro h0
      have := congrFun h0 i₁
      rw [hw'def, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne h12,
        smul_zero, add_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    obtain ⟨t, ht, htw⟩ := exists_mem_T_smul_eq_of_iso hσ (by omega) hw hww hw'0 hw'
    refine ⟨t, ht, i₀, ?_⟩
    rw [htw, hw'def, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h01,
      Pi.single_eq_of_ne h02, smul_zero, add_zero]
  · obtain ⟨l, hl⟩ := hσ.exists_norm (d := herm h.barEquiv w w)
      (herm_self_fixed h.barEquiv hσ.invol w)
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hl
      exact hww hl.symm
    set w₁ := l⁻¹ • w with hw₁def
    have hw₁ : herm h.barEquiv w₁ w₁ = 1 := by
      rw [hw₁def, herm_smul_left, herm_smul_right, ← hl, map_inv₀]
      field_simp [(map_ne_zero h.barEquiv).mpr hl0]
    have he₀ : herm h.barEquiv (Pi.single i₀ 1 : Fin m → K) (Pi.single i₀ 1) = 1 := by
      rw [herm_single_left, Pi.single_eq_same, map_one, one_mul]
    obtain ⟨t, ht, htw⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inl hm) hw₁ he₀
    refine ⟨t, ht, i₁, ?_⟩
    have hww₁ : w = l • w₁ := by rw [hw₁def, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [hww₁, smul_comm, htw, Pi.smul_apply, Pi.single_eq_of_ne h01.symm, smul_zero]

end Local

section Main

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem suidEquiv_mem_iSup_of_tv {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) {a : Fin n → K}
    (ha : herm h.barEquiv a a = 0) {c : K} {g : SUid h.barEquiv n}
    (hg : ∀ v, g • v = v + (c * herm h.barEquiv a v) • a) :
    suidEquiv h n g ∈ ⨆ (I : Finset (Fin n)) (_ : I.card = m), unitaryBlock h I := by
  classical
  set H := ⨆ (I : Finset (Fin n)) (_ : I.card = m), unitaryBlock h I with hH
  have hle : ∀ I : Finset (Fin n), I.card = m → unitaryBlock h I ≤ H := fun I hI =>
    le_iSup₂_of_le I hI le_rfl
  suffices key : ∀ k : ℕ, ∀ (a : Fin n → K),
      (Finset.univ.filter fun i => a i ≠ 0).card = k → herm h.barEquiv a a = 0 →
        ∀ g : SUid h.barEquiv n, (∀ v, g • v = v + (c * herm h.barEquiv a v) • a) →
          suidEquiv h n g ∈ H from
    key _ a rfl ha g hg
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a hk ha g hg
  set S := Finset.univ.filter fun i => a i ≠ 0 with hS
  have hmemS : ∀ i, i ∈ S ↔ a i ≠ 0 := fun i => by simp [hS]
  by_cases hkm : k ≤ m
  ·
    obtain ⟨I, hSI, -, hI⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S)
      (hk ▸ hkm) (by simpa using hmn)
    refine hle I hI (suidEquiv_mem_unitaryBlock_of_tv h (fun i hi => ?_) hg)
    by_contra hai
    exact hi (hSI ((hmemS i).2 hai))
  ·
    push Not at hkm
    obtain ⟨I, hIS, hI⟩ := Finset.exists_subset_card_eq (s := S) (n := m) (by omega)
    set s : Fin m → Fin n := ⇑(I.orderEmbOfFin hI) with hsdef
    have hs : Injective s := (I.orderEmbOfFin hI).injective
    have hsI : ∀ k, s k ∈ I := fun k => I.orderEmbOfFin_mem hI k
    have hIs : ∀ i ∈ I, ∃ k, s k = i := fun i hi => by
      have : i ∈ Set.range s := by
        rw [hsdef, Finset.range_orderEmbOfFin]
        exact hi
      exact this
    set φ : (Fin m → K) →ₗ[K] (Fin n → K) := Function.ExtendByZero.linearMap K s with hφdef
    have hφ : ∀ u, φ u = extend s u 0 := fun u => rfl
    set w : Fin m → K := a ∘ s with hwdef
    have hw0 : w ≠ 0 := fun h0 => by
      have h1 := congrFun h0 ⟨0, by omega⟩
      exact (hmemS _).1 (hIS (hsI _)) h1
    obtain ⟨t, ht, k₀, hk₀⟩ := exists_mem_T_smul_apply_eq_zero h hm hw0
    obtain ⟨t', -, htφ, htperp⟩ := transport h.isUnitaryInvolution_barEquiv.invol φ
      (fun u v => by rw [hφ, hφ]; exact herm_extend _ hs u v) ht
    have ht'I : suidEquiv h n t' ∈ unitaryBlock h I := by
      refine suidEquiv_mem_unitaryBlock_of_smul h (fun j hj => ?_) (fun j hj i hi => ?_)
      · refine htperp _ fun u => ?_
        have hjr : ¬∃ k, s k = j := fun ⟨k, hk'⟩ => hj (hk' ▸ hsI k)
        rw [herm_single_right, hφ, extend_apply' _ _ _ hjr]
        simp
      · obtain ⟨k, rfl⟩ := hIs j hj
        have hir : ¬∃ k, s k = i := fun ⟨k, hk'⟩ => hi (hk' ▸ hsI k)
        rw [← extend_single hs k, ← hφ, htφ, hφ, extend_apply' _ _ _ hir]
        rfl
    set r := a - φ w with hrdef
    have hrs : ∀ k, r (s k) = 0 := fun k => by
      rw [hrdef, Pi.sub_apply, hφ, hs.extend_apply, hwdef, Function.comp_apply, sub_self]
    have hr : ∀ u, herm h.barEquiv (φ u) r = 0 := fun u => by
      rw [hφ]
      exact herm_extend_eq_zero_of_apply_eq_zero _ hrs u
    have ht'a : t' • a = φ (t • w) + r := by
      have e1 : a = φ w + r := by rw [hrdef, add_sub_cancel]
      conv_lhs => rw [e1]
      rw [smul_add, htφ, htperp r hr]
    set a' := t' • a with ha'def
    have ha' : herm h.barEquiv a' a' = 0 := by rw [ha'def, herm_smul_smul]; exact ha
    have hsupp : (Finset.univ.filter fun i => a' i ≠ 0) ⊆ S.erase (s k₀) := by
      intro i hi
      have hi' : a' i ≠ 0 := by simpa using hi
      rw [Finset.mem_erase]
      by_cases hir : ∃ k, s k = i
      · obtain ⟨k, rfl⟩ := hir
        have hval : a' (s k) = (t • w) k := by
          rw [ht'a, Pi.add_apply, hφ, hs.extend_apply, hrs k, add_zero]
        rw [hval] at hi'
        exact ⟨fun e => hi' (by rw [hs e]; exact hk₀), hIS (hsI k)⟩
      · have hval : a' i = a i := by
          rw [ht'a, Pi.add_apply, hrdef, Pi.sub_apply, hφ, hφ, extend_apply' _ _ _ hir,
            extend_apply' _ _ _ hir]
          simp
        rw [hval] at hi'
        exact ⟨fun e => hir ⟨k₀, e.symm⟩, (hmemS i).2 hi'⟩
    have hlt : (Finset.univ.filter fun i => a' i ≠ 0).card < k := by
      calc (Finset.univ.filter fun i => a' i ≠ 0).card ≤ (S.erase (s k₀)).card :=
            Finset.card_le_card hsupp
        _ < S.card := Finset.card_erase_lt_of_mem (hIS (hsI k₀))
        _ = k := hk
    have hg' : ∀ v, (t' * g * t'⁻¹) • v = v + (c * herm h.barEquiv a' v) • a' :=
      conj_smul_of_tv t' g hg
    have hmem' := ih _ hlt a' rfl ha' (t' * g * t'⁻¹) hg'
    have hgeq : g = t'⁻¹ * (t' * g * t'⁻¹) * t' := by group
    rw [hgeq, map_mul, map_mul, map_inv]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hle I hI ht'I)) hmem') (hle I hI ht'I)

theorem iSup_unitaryBlock_card_eq_top {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) :
    ⨆ (I : Finset (Fin n)) (_ : I.card = m), unitaryBlock h I = ⊤ := by
  have hT : T h.barEquiv n = ⊤ :=
    T_eq_top h.isUnitaryInvolution_barEquiv (by omega) (fun h3 => by omega)
  have key : T h.barEquiv n ≤
      (⨆ (I : Finset (Fin n)) (_ : I.card = m), unitaryBlock h I).comap
        (suidEquiv h n).toMonoidHom := by
    change Subgroup.closure (tvSet h.barEquiv n) ≤ _
    rw [closure_le]
    rintro g ⟨a, c, ha, -, hg⟩
    exact suidEquiv_mem_iSup_of_tv h hm hmn ha hg
  rw [eq_top_iff]
  intro y _
  have hy : (suidEquiv h n).symm y ∈ T h.barEquiv n := by
    rw [hT]
    exact mem_top _
  have := key hy
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this

theorem iSup_unitaryBlock_card_four_eq_top (hn : 4 ≤ n) :
    ⨆ (I : Finset (Fin n)) (_ : I.card = 4), unitaryBlock h I = ⊤ :=
  iSup_unitaryBlock_card_eq_top h le_rfl hn

theorem iSup_blockSU_card_eq_top {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) :
    ⨆ (I : Finset (Fin n)) (_ : I.card = m), blockSU h I = ⊤ := by
  have h1 := congrArg (Subgroup.map (unitaryProj h n)) (iSup_unitaryBlock_card_eq_top h hm hmn)
  rw [Subgroup.map_top_of_surjective _ (unitaryProj_surjective h n)] at h1
  simp only [Subgroup.map_iSup] at h1
  exact h1

theorem iSup_blockSU_card_four_eq_top (hn : 4 ≤ n) :
    ⨆ (I : Finset (Fin n)) (_ : I.card = 4), blockSU h I = ⊤ :=
  iSup_blockSU_card_eq_top h le_rfl hn

theorem eq_of_eqOn_blockSU {M : Type*} [Monoid M] {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n)
    {φ₁ φ₂ : unitaryPSU h n →* M}
    (hφ : ∀ I : Finset (Fin n), I.card = m → ∀ x ∈ blockSU h I, φ₁ x = φ₂ x) : φ₁ = φ₂ := by
  have hle : (⨆ (I : Finset (Fin n)) (_ : I.card = m), blockSU h I) ≤ φ₁.eqLocus φ₂ :=
    iSup₂_le fun I hI x hx => hφ I hI x hx
  rw [iSup_blockSU_card_eq_top h hm hmn] at hle
  exact MonoidHom.ext fun x => hle (mem_top x)

theorem eq_of_eqOn_unitaryBlock {M : Type*} [Monoid M] {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n)
    {φ₁ φ₂ : unitarySU p f K n →* M}
    (hφ : ∀ I : Finset (Fin n), I.card = m → ∀ x ∈ unitaryBlock h I, φ₁ x = φ₂ x) :
    φ₁ = φ₂ := by
  have hle : (⨆ (I : Finset (Fin n)) (_ : I.card = m), unitaryBlock h I) ≤ φ₁.eqLocus φ₂ :=
    iSup₂_le fun I hI x hx => hφ I hI x hx
  rw [iSup_unitaryBlock_card_eq_top h hm hmn] at hle
  exact MonoidHom.ext fun x => hle (mem_top x)

end Main

end CFSG.SeitzReduction.UnitaryPilot
