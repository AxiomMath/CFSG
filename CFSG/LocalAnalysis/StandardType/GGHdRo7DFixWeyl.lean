module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceUAuxAbs
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7DFixAux_bU {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    Module.Basis (Fin n) (ZMod p) (LinearMap.ker (b.coord 0)) :=
  let v : Fin n → LinearMap.ker (b.coord 0) := fun j =>
    ⟨b j.succ, by
      rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
        if_neg (Fin.succ_ne_zero j)]⟩
  Module.Basis.mk
    (v := v)
    (LinearIndependent.of_comp (LinearMap.ker (b.coord 0)).subtype (by
      dsimp only [Function.comp_def, v]
      exact b.linearIndependent.comp Fin.succ (Fin.succ_injective n)))
    (by
      intro u _
      have h := b.sum_repr (u : V)
      rw [Fin.sum_univ_succ] at h
      have h0 : b.repr (u : V) 0 = 0 := by
        rw [← Module.Basis.coord_apply]
        exact LinearMap.mem_ker.mp u.2
      rw [h0, zero_smul, zero_add] at h
      have hu : u = ∑ j, b.repr (u : V) j.succ • v j := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, v]
        exact h.symm
      rw [hu]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))

private lemma hdRo7DFixAux_bU_apply {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (j : Fin n) :
    ((hdRo7DFixAux_bU b) j : V) = b j.succ := by
  simp only [hdRo7DFixAux_bU, Module.Basis.mk_apply]

private lemma hdRo7DFixAux_b_mem_U {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    {i : Fin (n + 1)} (hi : i ≠ 0) : b i ∈ LinearMap.ker (b.coord 0) := by
  rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg hi]

private lemma hdRo7DFixAux_c2sp_fix0 {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} (hg : C2SP p b g) : g (b 0) = b 0 := by
  obtain ⟨σ, c, hσ0, hc0, -, hact⟩ := hg
  rw [hact 0, hσ0, hc0, one_smul]

private lemma hdRo7DFixAux_c2sp_kerAug {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} (hg : C2SP p b g) :
    g ∈ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)) := by
  obtain ⟨σ, c, hσ0, hc0, hc, hact⟩ := hg
  have hfix0 : g (b 0) = b 0 := hdRo7DFixAux_c2sp_fix0 ⟨σ, c, hσ0, hc0, hc, hact⟩
  intro v
  have hdecomp : g v - v = ∑ i : Fin (n + 1), b.repr v i • (g (b i) - b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  by_cases hi : i = 0
  · subst hi
    rw [hfix0, sub_self]
    exact Submodule.zero_mem _
  · refine Submodule.sub_mem _ ?_ (hdRo7DFixAux_b_mem_U b hi)
    rw [hact i]
    refine Submodule.smul_mem _ _ (hdRo7DFixAux_b_mem_U b ?_)
    intro h
    apply hi
    have h' : σ i = σ 0 := by rw [h, hσ0]
    exact σ.injective h'

private noncomputable def hdRo7DFixAux_s0 {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) : V ≃ₗ[ZMod p] V :=
  b.equiv (b.unitsSMul fun i => if i = Fin.last n then -1 else 1) (Equiv.refl _)

private lemma hdRo7DFixAux_s0_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (i : Fin (n + 1)) :
    hdRo7DFixAux_s0 b (b i) = (if i = Fin.last n then (-1 : ZMod p) else 1) • b i := by
  rw [hdRo7DFixAux_s0, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply,
    Equiv.refl_apply, Units.smul_def]
  by_cases h : i = Fin.last n <;> simp [h]

private lemma hdRo7DFixAux_prod_sign_succ {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (∏ j : Fin n, (if j.succ = Fin.last n then (-1 : ZMod p) else 1)) = -1 := by
  let j0 : Fin n := Fin.pred (Fin.last n) (by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_last, Fin.val_zero] at hv
    omega)
  have hsucc : j0.succ = (Fin.last n : Fin (n + 1)) :=
    Fin.succ_pred (Fin.last n) _
  rw [Fintype.prod_eq_single j0]
  · rw [hsucc]; simp
  · intro j hj
    have hne : j.succ ≠ (Fin.last n : Fin (n + 1)) := by
      intro h
      apply hj
      have h' : j.succ = j0.succ := by rw [h, hsucc]
      exact Fin.succ_injective n h'
    simp [hne]

private lemma hdRo7DFixAux_prod_sign {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (∏ i : Fin (n + 1), (if i = Fin.last n then (-1 : ZMod p) else 1)) = -1 := by
  rw [Fin.prod_univ_succ]
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_last] at hv
    omega
  rw [if_neg h0, one_mul]
  exact hdRo7DFixAux_prod_sign_succ hn

private lemma hdRo7DFixAux_prod_pm_one {p : ℕ} [Fact p.Prime] {n : ℕ}
    (c : Fin n → ZMod p) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    (∏ i, c i = 1) ∨ (∏ i, c i = -1) := by
  have h : ∀ s : Finset (Fin n), (∀ i ∈ s, c i = 1 ∨ c i = -1) →
      (∏ i ∈ s, c i = 1) ∨ (∏ i ∈ s, c i = -1) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; exact Or.inl (by simp)
    | insert a s ha ih =>
        intro hs
        rw [Finset.prod_insert ha]
        rcases ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) with h1 | h1 <;>
          rcases hs a (Finset.mem_insert_self a s) with h2 | h2 <;> rw [h2, h1]
        · exact Or.inl (by ring)
        · exact Or.inr (by ring)
        · exact Or.inr (by ring)
        · exact Or.inl (by ring)
  exact h Finset.univ fun i _ => hc i

private lemma hdRo7DFixAux_mul_s0_dsp {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hn : 0 < n) {g : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1) → ZMod p} (hσ0 : σ 0 = 0) (hc0 : c 0 = 1)
    (hcs : ∀ i, c i = 1 ∨ c i = -1) (hneg : ∏ i, c i = -1)
    (hact : ∀ i, g (b i) = c i • b (σ i)) :
    DSP p b (g * hdRo7DFixAux_s0 b) := by
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_last] at hv
    omega
  refine ⟨σ, (fun i => (if i = Fin.last n then -1 else 1) * c i), hσ0, ?_, ?_, ?_, ?_⟩
  · simp [hc0, h0]
  · intro i
    rcases hcs i with h | h <;> by_cases hi : i = Fin.last n
    · subst hi; simp [h]
    · simp [hi, h]
    · subst hi; simp [h]
    · simp [hi, h]
  · rw [Finset.prod_mul_distrib, hdRo7DFixAux_prod_sign hn, hneg]
    norm_num
  · intro i
    rw [LinearEquiv.mul_apply, hdRo7DFixAux_s0_apply, map_smul, hact i, mul_smul]

private theorem hdRo7DFixAux_eq_all {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hPH : ∀ a, DSP p b a → a ∈ H)
    (hHC2 : ∀ a ∈ H, C2SP p b a) (hn : 0 < n) (hs0 : hdRo7DFixAux_s0 b ∈ H) :
    H = {a | C2SP p b a} := by
  apply le_antisymm hHC2
  intro g hg
  obtain ⟨σ, c, hσ0, hc0, hcs, hact⟩ := hg
  by_cases hprod : ∏ i, c i = 1
  · exact hPH g ⟨σ, c, hσ0, hc0, hcs, hprod, hact⟩
  · have hneg : ∏ i, c i = -1 := by
      rcases hdRo7DFixAux_prod_pm_one c hcs with h | h
      · exact absurd h hprod
      · exact h
    have hgs := hdRo7DFixAux_mul_s0_dsp b hn hσ0 hc0 hcs hneg hact
    have hmem : g * hdRo7DFixAux_s0 b ∈ H := hPH _ hgs
    have heq : g = (g * hdRo7DFixAux_s0 b) * (hdRo7DFixAux_s0 b)⁻¹ := by group
    rw [heq]
    exact H.mul_mem hmem (H.inv_mem hs0)

private theorem hdRo7DFixAux_eq_even {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hPH : ∀ a, DSP p b a → a ∈ H)
    (hHC2 : ∀ a ∈ H, C2SP p b a) (hn : 0 < n) (hs0 : hdRo7DFixAux_s0 b ∉ H) :
    H = {a | DSP p b a} := by
  apply le_antisymm ?_ hPH
  intro g hg
  obtain ⟨σ, c, hσ0, hc0, hcs, hact⟩ := hHC2 g hg
  by_cases hprod : ∏ i, c i = 1
  · exact ⟨σ, c, hσ0, hc0, hcs, hprod, hact⟩
  · exfalso
    have hneg : ∏ i, c i = -1 := by
      rcases hdRo7DFixAux_prod_pm_one c hcs with h | h
      · exact absurd h hprod
      · exact h
    have hgs := hdRo7DFixAux_mul_s0_dsp b hn hσ0 hc0 hcs hneg hact
    have hmem : g * hdRo7DFixAux_s0 b ∈ H := hPH _ hgs
    have heq : hdRo7DFixAux_s0 b = g⁻¹ * (g * hdRo7DFixAux_s0 b) := by group
    apply hs0
    rw [heq]
    exact H.mul_mem (H.inv_mem hg) hmem

private def hdRo7DFixAux_SignedPerm {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {n : ℕ} (bU : Module.Basis (Fin n) (ZMod p) U)
    (a : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (bU i) = c i • bU (σ i)

private def hdRo7DFixAux_EvenPerm {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {n : ℕ} (bU : Module.Basis (Fin n) (ZMod p) U)
    (a : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (bU i) = c i • bU (σ i)

private theorem hdRo7DFixAux_lift {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    ∃ g : V ≃ₗ[ZMod p] V,
      (∀ i : Fin n, g (b i.succ) = c i • b (σ i).succ) ∧ g (b 0) = b 0 ∧
      C2SP p b g ∧ (∏ i, c i = 1 → DSP p b g) := by
  let σV : Equiv.Perm (Fin (n + 1)) :=
    (finSuccEquiv n).trans ((Equiv.optionCongr σ).trans (finSuccEquiv n).symm)
  let cV : Fin (n + 1) → ZMod p := Fin.cases 1 c
  let u : Fin (n + 1) → (ZMod p)ˣ := fun i =>
    Units.mk0 (cV i) (by
      induction i using Fin.cases with
      | zero => simp [cV]
      | succ j => rcases hc j with h | h <;> simp [cV, h])
  let g : V ≃ₗ[ZMod p] V :=
    (b.equiv (b.unitsSMul u) (Equiv.refl _)).trans (b.equiv b σV)
  have hact : ∀ i : Fin (n + 1), g (b i) = cV i • b (σV i) := by
    intro i
    rw [LinearEquiv.trans_apply, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply,
      Equiv.refl_apply, Units.smul_def, map_smul, Module.Basis.equiv_apply, Units.val_mk0]
  have hσV0 : σV 0 = 0 := by
    simp [σV, finSuccEquiv_zero, finSuccEquiv_symm_none]
  have hσVs : ∀ j : Fin n, σV j.succ = (σ j).succ := by
    intro j
    simp [σV, finSuccEquiv_symm_some, Equiv.optionCongr_apply]
  have hcV0 : cV 0 = 1 := Fin.cases_zero
  have hcVs : ∀ j : Fin n, cV j.succ = c j := fun j => Fin.cases_succ j
  have hcV : ∀ i, cV i = 1 ∨ cV i = -1 := by
    intro i
    induction i using Fin.cases with
    | zero => rw [hcV0]; exact Or.inl rfl
    | succ j => rw [hcVs]; exact hc j
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hact, hσVs, hcVs]
  · rw [hact, hcV0, hσV0, one_smul]
  · exact ⟨σV, cV, hσV0, hcV0, hcV, hact⟩
  · intro hprod
    refine ⟨σV, cV, hσV0, hcV0, hcV, ?_, hact⟩
    rw [Fin.prod_univ_succ, hcV0, one_mul]
    simpa only [hcVs] using hprod

private theorem hdRo7DFixAux_res_data {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) {σ : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1) → ZMod p} (hσ0 : σ 0 = 0) (hc0 : c 0 = 1)
    (hcs : ∀ i, c i = 1 ∨ c i = -1) (hact : ∀ i, g (b i) = c i • b (σ i)) :
    ∃ (τ : Equiv.Perm (Fin n)) (d : Fin n → ZMod p),
      (∀ i, d i = 1 ∨ d i = -1) ∧
      (∀ i, hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK ⟨g, hg⟩
        (hdRo7DFixAux_bU b i) = d i • hdRo7DFixAux_bU b (τ i)) ∧
      (∏ i, d i = ∏ i : Fin (n + 1), c i) := by
  have hσne : ∀ j : Fin n, σ j.succ ≠ 0 := by
    intro j h
    have h' : σ j.succ = σ 0 := by rw [h, hσ0]
    exact Fin.succ_ne_zero j (σ.injective h')
  let τ₀ : Fin n → Fin n := fun j => (σ j.succ).pred (hσne j)
  have hτsucc : ∀ j, (τ₀ j).succ = σ j.succ := fun j => Fin.succ_pred _ _
  have hτinj : Function.Injective τ₀ := by
    intro a b hab
    have h : σ a.succ = σ b.succ := by rw [← hτsucc a, ← hτsucc b, hab]
    exact Fin.succ_injective n (σ.injective h)
  let τ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective τ₀ (Finite.injective_iff_bijective.mp hτinj)
  have hτ : ∀ j, (τ j).succ = σ j.succ := fun j => hτsucc j
  refine ⟨τ, fun j => c j.succ, fun j => hcs j.succ, ?_, ?_⟩
  · intro j
    apply Subtype.ext
    change (↑((hdRo7SUReduceUAux_restrict (LinearMap.ker (b.coord 0)) g (hHK hg))
      (hdRo7DFixAux_bU b j)) : V) =
      ↑(((fun j => c j.succ) j) • (hdRo7DFixAux_bU b) (τ j))
    rw [hdRo7SUReduceUAux_restrict_apply, hdRo7DFixAux_bU_apply, hact j.succ]
    simp [hdRo7DFixAux_bU_apply, hτ j]
  · rw [Fin.prod_univ_succ, hc0, one_mul]

private theorem hdRo7DFixAux_res_signed {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) (hC2 : C2SP p b g) :
    hdRo7DFixAux_SignedPerm (hdRo7DFixAux_bU b)
      (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK ⟨g, hg⟩) := by
  obtain ⟨σ, c, hσ0, hc0, hcs, hact⟩ := hC2
  obtain ⟨τ, d, hds, hdact, -⟩ :=
    hdRo7DFixAux_res_data hHK hg hσ0 hc0 hcs hact
  exact ⟨τ, d, hds, hdact⟩

private theorem hdRo7DFixAux_res_even {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) (hD : DSP p b g) :
    hdRo7DFixAux_EvenPerm (hdRo7DFixAux_bU b)
      (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK ⟨g, hg⟩) := by
  obtain ⟨σ, c, hσ0, hc0, hcs, hprod, hact⟩ := hD
  obtain ⟨τ, d, hds, hdact, hdprod⟩ :=
    hdRo7DFixAux_res_data hHK hg hσ0 hc0 hcs hact
  refine ⟨τ, d, hds, ?_, hdact⟩
  rw [hdprod, hprod]

private theorem hdRo7DFixAux_range_all {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    (hH : H = {a | C2SP p b a}) :
    (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK).range =
      {r | hdRo7DFixAux_SignedPerm (hdRo7DFixAux_bU b) r} := by
  ext r
  constructor
  · rintro ⟨g, rfl⟩
    have hgC : C2SP p b g.1 := by
      have hmem : g.1 ∈ (H : Set (V ≃ₗ[ZMod p] V)) := g.2
      rw [hH] at hmem
      exact hmem
    exact hdRo7DFixAux_res_signed hHK g.2 hgC
  · intro hr
    obtain ⟨σ, c, hcs, hact⟩ := hr
    obtain ⟨g, hgact, -, hc2, -⟩ := hdRo7DFixAux_lift b σ c hcs
    have hgH : g ∈ H := by
      change g ∈ (H : Set (V ≃ₗ[ZMod p] V))
      rw [hH]
      exact hc2
    refine ⟨⟨g, hgH⟩, ?_⟩
    apply LinearEquiv.ext
    intro u
    have hlin : (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK
          ⟨g, hgH⟩).toLinearMap = r.toLinearMap := by
      refine Module.Basis.ext (hdRo7DFixAux_bU b) fun j => ?_
      apply Subtype.ext
      change (↑((hdRo7SUReduceUAux_restrict (LinearMap.ker (b.coord 0)) g (hHK hgH))
        (hdRo7DFixAux_bU b j)) : V) = ↑(r (hdRo7DFixAux_bU b j))
      rw [hdRo7SUReduceUAux_restrict_apply, hdRo7DFixAux_bU_apply, hgact j, hact j]
      simp [hdRo7DFixAux_bU_apply]
    exact LinearMap.congr_fun hlin u

private theorem hdRo7DFixAux_range_even {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    (hH : H = {a | DSP p b a}) :
    (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK).range =
      {r | hdRo7DFixAux_EvenPerm (hdRo7DFixAux_bU b) r} := by
  ext r
  constructor
  · rintro ⟨g, rfl⟩
    have hgD : DSP p b g.1 := by
      have hmem : g.1 ∈ (H : Set (V ≃ₗ[ZMod p] V)) := g.2
      rw [hH] at hmem
      exact hmem
    exact hdRo7DFixAux_res_even hHK g.2 hgD
  · intro hr
    obtain ⟨σ, c, hcs, hprod, hact⟩ := hr
    obtain ⟨g, hgact, -, -, hdsp⟩ := hdRo7DFixAux_lift b σ c hcs
    have hgH : g ∈ H := by
      change g ∈ (H : Set (V ≃ₗ[ZMod p] V))
      rw [hH]
      exact hdsp hprod
    refine ⟨⟨g, hgH⟩, ?_⟩
    apply LinearEquiv.ext
    intro u
    have hlin : (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK
          ⟨g, hgH⟩).toLinearMap = r.toLinearMap := by
      refine Module.Basis.ext (hdRo7DFixAux_bU b) fun j => ?_
      apply Subtype.ext
      change (↑((hdRo7SUReduceUAux_restrict (LinearMap.ker (b.coord 0)) g (hHK hgH))
        (hdRo7DFixAux_bU b j)) : V) = ↑(r (hdRo7DFixAux_bU b j))
      rw [hdRo7SUReduceUAux_restrict_apply, hdRo7DFixAux_bU_apply, hgact j, hact j]
      simp [hdRo7DFixAux_bU_apply]
    exact LinearMap.congr_fun hlin u

private theorem hdRo7DFixAux_res_injective {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    {b : Module.Basis (Fin (n + 1)) (ZMod p) V} {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (LinearMap.ker (b.coord 0)))
    (hfix0 : ∀ g ∈ H, g (b 0) = b 0) :
    Function.Injective (hdRo7SUReduceUAux_res (LinearMap.ker (b.coord 0)) H hHK) := by
  intro g h hgh
  have hgh' : hdRo7SUReduceUAux_restrict (LinearMap.ker (b.coord 0)) g.1 (hHK g.2) =
      hdRo7SUReduceUAux_restrict (LinearMap.ker (b.coord 0)) h.1 (hHK h.2) := hgh
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  have hlin : (g.1 : V →ₗ[ZMod p] V) = (h.1 : V →ₗ[ZMod p] V) := by
    refine Module.Basis.ext b fun i => ?_
    by_cases hi : i = 0
    · subst hi
      change (g.1 : V ≃ₗ[ZMod p] V) (b 0) = (h.1 : V ≃ₗ[ZMod p] V) (b 0)
      rw [hfix0 g.1 g.2, hfix0 h.1 h.2]
    · have hbi : b i ∈ LinearMap.ker (b.coord 0) := hdRo7DFixAux_b_mem_U b hi
      have heq := congrArg
        (fun f : (LinearMap.ker (b.coord 0)) ≃ₗ[ZMod p] (LinearMap.ker (b.coord 0)) =>
          f ⟨b i, hbi⟩) hgh'
      have heqV := congrArg Subtype.val heq
      rw [hdRo7SUReduceUAux_restrict_apply, hdRo7SUReduceUAux_restrict_apply] at heqV
      exact heqV
  exact LinearMap.congr_fun hlin v

private theorem hdRo7DFixAux_linWeyl_lift {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V)
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U)
    (h2 : (2 : ZMod p) ≠ 0)
    (hresinj : Function.Injective (hdRo7SUReduceUAux_res U H hHK)) :
    ZS.LinWeyl p (hdRo7SUReduceUAux_res U H hHK).range → ZS.LinWeyl p H := by
  intro hR
  obtain ⟨ι, M, hM, f, hf⟩ := hR
  let res := hdRo7SUReduceUAux_res U H hHK
  let eHom : ↥H →* ↥res.range :=
    { toFun := fun g => ⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have heHom : Function.Bijective eHom := by
    constructor
    · intro a b hab
      apply hresinj
      exact congrArg Subtype.val hab
    · rintro ⟨r, hr⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
      exact ⟨g, rfl⟩
  let e : ↥H ≃* ↥res.range := MulEquiv.ofBijective eHom heHom
  refine ⟨ι, M, hM, f.trans e.symm, ?_⟩
  intro i
  let gH : ↥H := e.symm (f (M.simple i))
  let gV : V ≃ₗ[ZMod p] V := gH
  have hres_e : res gH = (f (M.simple i)).1 :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply e (f (M.simple i)))
  have hsq : gH * gH = 1 := by
    apply hresinj
    rw [map_mul, map_one, hres_e]
    exact (hf i).1
  have hsqV : gV * gV = 1 := by
    change (gH : V ≃ₗ[ZMod p] V) * (gH : V ≃ₗ[ZMod p] V) = 1
    simpa using congrArg Subtype.val hsq
  have hfr : Module.finrank (ZMod p) (ggLinMove gV) = 1 := by
    have hmap := hdRo7SUReduceUAux_move_map_restrict U gV (hHK gH.2) hsqV h2
    rw [← hmap, Submodule.finrank_map_subtype_eq]
    change Module.finrank (ZMod p) (ggLinMove (res gH)) = 1
    rw [hres_e]
    exact (hf i).2
  have : ZS.IsRefl p gV := ⟨hsqV, hfr⟩
  simpa [gV, gH] using this

theorem d_fixWeyl_holds : DFixWeylLeaf := by
  intro p _ hp n hn V _ _ b H hPH hHC2
  subst p
  have hn6 : 0 < n := by omega
  let U : Submodule (ZMod 3) V := LinearMap.ker (b.coord 0)
  have hHK : H ≤ hdRo7SUReduceUAux_kerAug 3 U := by
    intro g hg
    exact hdRo7DFixAux_c2sp_kerAug (hHC2 g hg)
  have hfix0 : ∀ g ∈ H, g (b 0) = b 0 := fun g hg =>
    hdRo7DFixAux_c2sp_fix0 (hHC2 g hg)
  let res := hdRo7SUReduceUAux_res U H hHK
  have hresinj : Function.Injective res := hdRo7DFixAux_res_injective hHK hfix0
  by_cases hs0 : hdRo7DFixAux_s0 b ∈ H
  · have hH : H = {a | C2SP 3 b a} := hdRo7DFixAux_eq_all H hPH hHC2 hn6 hs0
    have hrange : res.range = {r | hdRo7DFixAux_SignedPerm (hdRo7DFixAux_bU b) r} :=
      hdRo7DFixAux_range_all hHK hH
    have hlinR : ZS.LinWeyl 3 res.range := by
      refine ggRC_linWeyl_of_signed (p := 3) (by decide) (by omega)
        (hdRo7DFixAux_bU b) res.range ?_
      intro a
      rw [show a ∈ res.range ↔ a ∈ (res.range : Set (↥U ≃ₗ[ZMod 3] ↥U)) from Iff.rfl,
        hrange]
      exact Iff.rfl
    have h2 : (2 : ZMod 3) ≠ 0 := by
      intro h
      have h' : (3 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
      norm_num at h'
    exact hdRo7DFixAux_linWeyl_lift (p := 3) (V := V) U hHK h2 hresinj hlinR
  · have hH : H = {a | DSP 3 b a} := hdRo7DFixAux_eq_even H hPH hHC2 hn6 hs0
    have hrange : res.range = {r | hdRo7DFixAux_EvenPerm (hdRo7DFixAux_bU b) r} :=
      hdRo7DFixAux_range_even hHK hH
    have hlinR : ZS.LinWeyl 3 res.range := by
      refine ggRC_linWeyl_of_even_signed (p := 3) (by decide) (by omega)
        (hdRo7DFixAux_bU b) res.range ?_
      intro a
      rw [show a ∈ res.range ↔ a ∈ (res.range : Set (↥U ≃ₗ[ZMod 3] ↥U)) from Iff.rfl,
        hrange]
      exact Iff.rfl
    have h2 : (2 : ZMod 3) ≠ 0 := by
      intro h
      have h' : (3 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
      norm_num at h'
    exact hdRo7DFixAux_linWeyl_lift (p := 3) (V := V) U hHK h2 hresinj hlinR

end CFSG.StandardType.HdRo7D
