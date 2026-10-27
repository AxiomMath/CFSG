module

public import CFSG.Monster.B.E6.StdF4DegreeLinear
public import CFSG.Monster.B.E6.StdF4RadicalChars

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open scoped commutatorElement

theorem radicalZ_le_groupJ :
    radicalZ ≤ groupJ := radicalZ_le_radicalQ.trans radicalQ_le_groupJ

theorem leviOrbit_self
    (χ : radicalZ →* ℂˣ) : χ ∈ leviOrbit χ :=
  ⟨1, one_mem _, (charConj_one χ).symm⟩

theorem leviOrbit_subset_of_mem
    {χ ψ : radicalZ →* ℂˣ} (h : ψ ∈ leviOrbit χ) :
    leviOrbit ψ ⊆ leviOrbit χ := by
  obtain ⟨g, hg, rfl⟩ := h
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h * g, mul_mem hh hg, (charConj_mul h g χ).symm⟩

theorem leviOrbit_eq_of_mem
    {χ ψ : radicalZ →* ℂˣ} (h : ψ ∈ leviOrbit χ) :
    leviOrbit ψ = leviOrbit χ := by
  refine (leviOrbit_subset_of_mem h).antisymm (leviOrbit_subset_of_mem ?_)
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, inv_mem hg, ?_⟩
  rw [← charConj_mul, inv_mul_cancel, charConj_one]

theorem leviOrbit_negChar
    {χ : radicalZ →* ℂˣ} (hχ : χ tZ = -1) :
    28 ≤ (leviOrbit χ).ncard ∧ (leviOrbit χ).Finite ∧ ∀ ψ ∈ leviOrbit χ, ψ tZ = -1 := by
  obtain ⟨χ₁, χ₂, -, -, h₁, h₂, -, hiff⟩ := levi_char_orbits
  have key : ∀ χ' : radicalZ →* ℂˣ, χ' ∈ leviOrbit χ₁ ∨ χ' ∈ leviOrbit χ₂ →
      ∀ ψ ∈ leviOrbit χ', ψ tZ = -1 := by
    intro χ' h ψ hψ
    rcases h with h | h
    · exact (hiff ψ).2 (Or.inl (leviOrbit_subset_of_mem h hψ))
    · exact (hiff ψ).2 (Or.inr (leviOrbit_subset_of_mem h hψ))
  have hm := (hiff χ).1 hχ
  refine ⟨?_, ?_, key χ hm⟩
  · rcases hm with h | h <;> rw [leviOrbit_eq_of_mem h]
    · rw [h₁]
    · rw [h₂]; norm_num
  · rcases hm with h | h <;> rw [leviOrbit_eq_of_mem h] <;> apply Set.finite_of_ncard_pos
    · rw [h₁]; norm_num
    · rw [h₂]; norm_num

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ groupJ V)

abbrev rhoAt (g : ModGL Tag.E6 K) (hg : g ∈ groupJ) : Module.End ℂ V := ρ ⟨g, hg⟩

@[expose] def rhoZ
    (z : radicalZ) : Module.End ℂ V := ρ ⟨z, radicalZ_le_groupJ z.2⟩

theorem rhoZ_mul
    (z z' : radicalZ) : rhoZ ρ (z * z') = rhoZ ρ z * rhoZ ρ z' := by
  rw [rhoZ, rhoZ, rhoZ, ← map_mul]
  rfl

theorem rhoZ_one :
    rhoZ ρ 1 = 1 := by
  rw [rhoZ, ← map_one ρ]
  rfl

@[expose] def wSpace
    (χ : radicalZ →* ℂˣ) : Submodule ℂ V :=
  ⨅ z : radicalZ, Module.End.eigenspace (rhoZ ρ z) (χ z)

theorem mem_wSpace
    {χ : radicalZ →* ℂˣ} {v : V} :
    v ∈ wSpace ρ χ ↔ ∀ z, rhoZ ρ z v = (χ z : ℂ) • v := by
  simp only [wSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem mem_wSpace_charOfMask
    {a : Fin 7 → ZMod 2} {v : V}
    (h : ∀ j, rhoZ ρ (zBZ j) v = (signU (a j) : ℂ) • v) : v ∈ wSpace ρ (charOfMask a) := by
  rw [mem_wSpace]
  intro z
  obtain ⟨u, rfl⟩ := zMap_surjective z
  rw [zMap_apply]
  refine Finset.prod_induction _ (fun g => rhoZ ρ g v = (charOfMask a g : ℂ) • v) ?_ ?_ ?_
  · intro g g' hg hg'
    rw [rhoZ_mul, Module.End.mul_apply, hg', map_smul, hg, smul_smul, map_mul, Units.val_mul,
      mul_comm]
  · rw [rhoZ_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
  · intro j _
    rcases zmod_two_cases (u.toAdd j) with h0 | h1
    · rw [h0, val_zero_two, pow_zero, rhoZ_one, map_one, Units.val_one, one_smul,
        Module.End.one_apply]
    · rw [h1, val_one_two, pow_one, h j, charOfMask_zBZ]

theorem tZ_mem_groupJ :
    (rootInvM : ModGL Tag.E6 K) ∈ groupJ :=
  radicalZ_le_groupJ rootInvM_mem_radicalZ

@[expose] def tJ :
    groupJ := ⟨rootInvM, tZ_mem_groupJ⟩

theorem rhoZ_tZ :
    rhoZ ρ tZ = ρ tJ := rfl

theorem rhoZ_mul_self
    (z : radicalZ) : rhoZ ρ z * rhoZ ρ z = 1 := by
  rw [← rhoZ_mul, show z * z = 1 from Subtype.ext (mul_self_of_mem_radicalZ z.2), rhoZ_one]

theorem rhoZ_comm
    (z z' : radicalZ) : rhoZ ρ z * rhoZ ρ z' = rhoZ ρ z' * rhoZ ρ z := by
  rw [← rhoZ_mul, ← rhoZ_mul, mul_comm]

theorem exists_negChar_wSpace
    (ht : ρ tJ ≠ 1) :
    ∃ χ : radicalZ →* ℂˣ, χ tZ = -1 ∧ wSpace ρ χ ≠ ⊥ := by
  classical
  set T := rhoZ ρ tZ with hT
  have hT2 : T * T = 1 := rhoZ_mul_self ρ tZ
  obtain ⟨w, hw⟩ : ∃ w, T w ≠ w := by
    by_contra h
    exact ht (LinearMap.ext fun w => not_not.1 fun hw => h ⟨w, hw⟩)
  have hv0 : T w - w ≠ 0 := sub_ne_zero.2 hw
  have hTv : T (T w - w) = -(T w - w) := by
    rw [map_sub, ← Module.End.mul_apply, hT2, Module.End.one_apply, neg_sub]
  let W := Module.End.eigenspace T (-1)
  have hW : W ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨_, Module.End.mem_eigenspace_iff.2 (by rw [hTv, neg_one_smul]),
      hv0⟩
  let Ts := (List.finRange 7).map fun j => rhoZ ρ (zBZ j)
  have hmem : ∀ S ∈ Ts, ∃ j, S = rhoZ ρ (zBZ j) := by
    intro S hS
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hS
    exact ⟨j, rfl⟩
  obtain ⟨v, hvW, hv0', hv⟩ := exists_common_eigen Ts
    (fun S hS => by obtain ⟨j, rfl⟩ := hmem S hS; exact rhoZ_mul_self ρ _)
    (fun S hS S' hS' => by
      obtain ⟨j, rfl⟩ := hmem S hS
      obtain ⟨j', rfl⟩ := hmem S' hS'
      exact rhoZ_comm ρ _ _) W hW
    (fun S hS w hw => by
      obtain ⟨j, rfl⟩ := hmem S hS
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [← Module.End.mul_apply, ← rhoZ_comm, Module.End.mul_apply, hw, map_smul])
  have hvj : ∀ j, rhoZ ρ (zBZ j) v = v ∨ rhoZ ρ (zBZ j) v = -v := fun j =>
    hv _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
  let a : Fin 7 → ZMod 2 := fun j => if rhoZ ρ (zBZ j) v = v then 0 else 1
  have ha : ∀ j, rhoZ ρ (zBZ j) v = (signU (a j) : ℂ) • v := by
    intro j
    simp only [a]
    split_ifs with h
    · rw [h, signU_zero, Units.val_one, one_smul]
    · rw [(hvj j).resolve_left h, signU_one, Units.val_neg, Units.val_one, neg_one_smul]
  refine ⟨charOfMask a, ?_, (Submodule.ne_bot_iff _).2 ⟨v, mem_wSpace_charOfMask ρ ha, hv0'⟩⟩
  rw [charOfMask_tZ]
  have hv' : T v = -v := by
    have := Module.End.mem_eigenspace_iff.1 hvW
    rw [this, neg_one_smul]
  simp only [a]
  rw [ite_eq_right]
  intro h
  have h' : T v = v := by rw [hT, ← zBZ_zero]; exact h
  rw [h'] at hv'
  exact hv0' (by
    have : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [hv']; exact neg_add_cancel v
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero)

theorem rho_mem_wSpace_charConj
    (g : NZ) (hg : (g : ModGL Tag.E6 K) ∈ leviL0)
    {χ : radicalZ →* ℂˣ} {v : V} (hv : v ∈ wSpace ρ χ) :
    rhoAt ρ g (leviL0_le_groupJ hg) v ∈ wSpace ρ (charConj g χ) := by
  rw [mem_wSpace] at hv ⊢
  intro z
  rw [charConj_apply]
  have hw := conj_mem_radicalZ g z
  have e : (⟨z, radicalZ_le_groupJ z.2⟩ : groupJ) * ⟨g, leviL0_le_groupJ hg⟩ =
      ⟨g, leviL0_le_groupJ hg⟩ * ⟨(g : ModGL Tag.E6 K)⁻¹ * z * g, radicalZ_le_groupJ hw⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have h1 := hv ⟨_, hw⟩
  rw [rhoZ, rhoAt, ← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  rw [rhoZ] at h1
  rw [h1, map_smul]

theorem rhoAt_injective {g : ModGL Tag.E6 K} (hg : g ∈ groupJ) :
    Function.Injective (rhoAt ρ g hg) := by
  intro v w h
  have e : ρ (⟨g, hg⟩ : groupJ)⁻¹ * ρ ⟨g, hg⟩ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have := congrArg (ρ (⟨g, hg⟩ : groupJ)⁻¹) h
  rwa [← Module.End.mul_apply, e, ← Module.End.mul_apply, e, Module.End.one_apply,
    Module.End.one_apply] at this

theorem wSpace_charConj_ne_bot
    (g : NZ) (hg : (g : ModGL Tag.E6 K) ∈ leviL0)
    {χ : radicalZ →* ℂˣ} (h : wSpace ρ χ ≠ ⊥) : wSpace ρ (charConj g χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨_, rho_mem_wSpace_charConj ρ g hg hv, fun h0 => hv0 ?_⟩
  exact rhoAt_injective ρ _ (h0.trans (map_zero _).symm)

theorem sympA_mem_groupJ
    (i : Fin 4) : sympA i ∈ groupJ := radicalQ_le_groupJ (sympA_mem i)

theorem sympB_mem_groupJ
    (i : Fin 4) : sympB i ∈ groupJ := radicalQ_le_groupJ (sympB_mem i)

@[expose] def opA
    (i : Fin 4) : Module.End ℂ V := rhoAt ρ (sympA i) (sympA_mem_groupJ i)

@[expose] def opB
    (i : Fin 4) : Module.End ℂ V := rhoAt ρ (sympB i) (sympB_mem_groupJ i)

theorem rhoAt_mul {x y : ModGL Tag.E6 K} (hx : x ∈ groupJ) (hy : y ∈ groupJ) :
    rhoAt ρ x hx * rhoAt ρ y hy = rhoAt ρ (x * y) (mul_mem hx hy) := by
  rw [rhoAt, rhoAt, rhoAt, ← map_mul]
  rfl

theorem rhoAt_one : rhoAt ρ 1 (one_mem _) = 1 := by
  rw [rhoAt, ← map_one ρ]
  rfl

theorem rhoAt_congr {x y : ModGL Tag.E6 K} (hx : x ∈ groupJ) (h : x = y) :
    rhoAt ρ x hx = rhoAt ρ y (h ▸ hx) := by
  subst h
  rfl

theorem sympA_mul_self
    (i : Fin 4) : sympA i * sympA i = 1 := by
  rw [sympA]
  have h' := sympCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h'
  exact qr_mul_self (h' i i.2 i i.2).1.1.1.1

theorem sympB_mul_self
    (i : Fin 4) : sympB i * sympB i = 1 := by
  rw [sympB]
  have h' := sympCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h'
  exact qr_mul_self (h' i i.2 i i.2).1.1.1.2

theorem opA_mul_self
    (i : Fin 4) : opA ρ i * opA ρ i = 1 := by
  rw [opA, rhoAt_mul, rhoAt_congr ρ _ (sympA_mul_self i), rhoAt_one]

theorem opB_mul_self
    (i : Fin 4) : opB ρ i * opB ρ i = 1 := by
  rw [opB, rhoAt_mul, rhoAt_congr ρ _ (sympB_mul_self i), rhoAt_one]

theorem mul_comm_of_commutator {x y : ModGL Tag.E6 K} (h : ⁅x, y⁆ = 1) : x * y = y * x := by
  rw [commutatorElement_def] at h
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h, one_mul]

theorem opA_comm
    (i j : Fin 4) : opA ρ i * opA ρ j = opA ρ j * opA ρ i := by
  rw [opA, opA, rhoAt_mul, rhoAt_mul,
    rhoAt_congr ρ _ (mul_comm_of_commutator (symp_relations i j).2.1)]

theorem rhoZ_comm_rhoAt
    (z : radicalZ) {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) :
    rhoZ ρ z * rhoAt ρ x (radicalQ_le_groupJ hx) =
      rhoAt ρ x (radicalQ_le_groupJ hx) * rhoZ ρ z := by
  have hc := (mem_radicalZ_iff'.1 z.2).2 x hx
  change rhoAt ρ z _ * rhoAt ρ x _ = rhoAt ρ x _ * rhoAt ρ z _
  rw [rhoAt_mul, rhoAt_mul, rhoAt_congr ρ _ hc.symm]

theorem rhoAt_mem_wSpace
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) {χ : radicalZ →* ℂˣ} {v : V}
    (hv : v ∈ wSpace ρ χ) : rhoAt ρ x (radicalQ_le_groupJ hx) v ∈ wSpace ρ χ := by
  rw [mem_wSpace] at hv ⊢
  intro z
  rw [← Module.End.mul_apply, rhoZ_comm_rhoAt ρ z hx, Module.End.mul_apply, hv z, map_smul]

theorem opA_mem_wSpace
    (i : Fin 4) {χ : radicalZ →* ℂˣ} {v : V} (hv : v ∈ wSpace ρ χ) :
    opA ρ i v ∈ wSpace ρ χ := rhoAt_mem_wSpace ρ (sympA_mem i) hv

theorem opB_mem_wSpace
    (i : Fin 4) {χ : radicalZ →* ℂˣ} {v : V} (hv : v ∈ wSpace ρ χ) :
    opB ρ i v ∈ wSpace ρ χ := rhoAt_mem_wSpace ρ (sympB_mem i) hv

theorem opA_opB
    {χ : radicalZ →* ℂˣ} (hχ : χ tZ = -1) (i j : Fin 4) {w : V}
    (hw : w ∈ wSpace ρ χ) :
    opA ρ i (opB ρ j w) = (if i = j then (-1 : ℂ) else 1) • opB ρ j (opA ρ i w) := by
  have hrel := (symp_relations i j).1
  have e : sympA i * sympB j = ⁅sympA i, sympB j⁆ * (sympB j * sympA i) := by
    rw [commutatorElement_def]
    group
  have hw' := opB_mem_wSpace ρ j (opA_mem_wSpace ρ i hw)
  have hc : ⁅sympA i, sympB j⁆ ∈ groupJ :=
    radicalQ_le_groupJ (commutator_mem_zpowers (sympA_mem i) (sympB_mem j) |>
      fun h => radicalZ_le_radicalQ (zpowers_rootInvM_le_radicalZ h))
  rw [opA, opB, ← Module.End.mul_apply, rhoAt_mul, rhoAt_congr ρ _ e, ← rhoAt_mul ρ hc
    (mul_mem (sympB_mem_groupJ j) (sympA_mem_groupJ i)), ← rhoAt_mul, Module.End.mul_apply,
    Module.End.mul_apply]
  by_cases hij : i = j
  · rw [ite_eq_left hij] at hrel ⊢
    rw [rhoAt_congr ρ hc hrel]
    have := (mem_wSpace ρ).1 hw' tZ
    rw [hχ] at this
    rw [opA, opB] at this
    change ρ tJ _ = _
    rw [← rhoZ_tZ, this, Units.val_neg, Units.val_one]
  · rw [ite_eq_right hij] at hrel ⊢
    rw [rhoAt_congr ρ hc hrel, rhoAt_one, Module.End.one_apply, one_smul]

@[expose] def bPow
    (ε : Fin 4 → Bool) (j : Fin 4) (w : V) : V := if ε j then opB ρ j w else w

@[expose] def bvec
    (u : V) (ε : Fin 4 → Bool) : V :=
  bPow ρ ε 0 (bPow ρ ε 1 (bPow ρ ε 2 (bPow ρ ε 3 u)))

theorem bPow_mem
    {χ : radicalZ →* ℂˣ} (ε : Fin 4 → Bool) (j : Fin 4) {w : V}
    (hw : w ∈ wSpace ρ χ) : bPow ρ ε j w ∈ wSpace ρ χ := by
  unfold bPow
  split_ifs
  · exact opB_mem_wSpace ρ j hw
  · exact hw

theorem bPow_eigen
    {χ : radicalZ →* ℂˣ} (hχ : χ tZ = -1) (ε : Fin 4 → Bool) (i j : Fin 4)
    {w : V} (hw : w ∈ wSpace ρ χ) {c : ℂ} (hc : opA ρ i w = c • w) :
    opA ρ i (bPow ρ ε j w) = (if ε j ∧ i = j then -c else c) • bPow ρ ε j w := by
  unfold bPow
  by_cases he : ε j
  · rw [ite_eq_left he, opA_opB ρ hχ i j hw, hc, map_smul, smul_smul]
    by_cases hij : i = j
    · simp [hij, he]
    · simp [hij]
  · simp [he, hc]

theorem bPow_ne_zero
    (ε : Fin 4 → Bool) (j : Fin 4) {w : V} (hw : w ≠ 0) : bPow ρ ε j w ≠ 0 := by
  unfold bPow
  split_ifs
  · intro h
    apply hw
    have := congrArg (opB ρ j) h
    rwa [← Module.End.mul_apply, opB_mul_self, Module.End.one_apply, map_zero] at this
  · exact hw

theorem bvec_mem
    {χ : radicalZ →* ℂˣ} {u : V} (hu : u ∈ wSpace ρ χ) (ε : Fin 4 → Bool) :
    bvec ρ u ε ∈ wSpace ρ χ :=
  bPow_mem ρ ε 0 (bPow_mem ρ ε 1 (bPow_mem ρ ε 2 (bPow_mem ρ ε 3 hu)))

theorem bvec_ne_zero
    {u : V} (hu : u ≠ 0) (ε : Fin 4 → Bool) : bvec ρ u ε ≠ 0 :=
  bPow_ne_zero ρ ε 0 (bPow_ne_zero ρ ε 1 (bPow_ne_zero ρ ε 2 (bPow_ne_zero ρ ε 3 hu)))

theorem bvec_eigen
    {χ : radicalZ →* ℂˣ} (hχ : χ tZ = -1) {u : V} (hu : u ∈ wSpace ρ χ)
    {s : Fin 4 → ℂ} (hs : ∀ i, opA ρ i u = s i • u) (ε : Fin 4 → Bool) (i : Fin 4) :
    opA ρ i (bvec ρ u ε) = (if ε i then -s i else s i) • bvec ρ u ε := by
  have h3 := bPow_eigen ρ hχ ε i 3 hu (hs i)
  have h2 := bPow_eigen ρ hχ ε i 2 (bPow_mem ρ ε 3 hu) h3
  have h1 := bPow_eigen ρ hχ ε i 1 (bPow_mem ρ ε 2 (bPow_mem ρ ε 3 hu)) h2
  have h0 := bPow_eigen ρ hχ ε i 0 (bPow_mem ρ ε 1 (bPow_mem ρ ε 2 (bPow_mem ρ ε 3 hu))) h1
  rw [bvec, h0]
  congr 1
  clear h0 h1 h2 h3
  fin_cases i <;> simp

@[expose] def fam :
    radicalZ ⊕ Fin 4 → Module.End ℂ V
  | .inl z => rhoZ ρ z
  | .inr i => opA ρ i

theorem fam_comm
    (a b : radicalZ ⊕ Fin 4) : Commute (fam ρ a) (fam ρ b) := by
  rcases a with z | i <;> rcases b with z' | j
  · exact rhoZ_comm ρ z z'
  · exact rhoZ_comm_rhoAt ρ z (sympA_mem j)
  · exact (rhoZ_comm_rhoAt ρ z' (sympA_mem i)).symm
  · exact opA_comm ρ i j

theorem fam_indep :
    iSupIndep fun μ : radicalZ ⊕ Fin 4 → ℂ =>
    ⨅ a, (fam ρ a).maxGenEigenspace (μ a) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fam ρ) fun a b φ =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (fam_comm ρ b a) φ

theorem sign_ne_neg {c : ℂ} (hc : c = 1 ∨ c = -1) : -c ≠ c := by
  rcases hc with rfl | rfl <;> norm_num

theorem le_finrank_of_rho_tJ_ne_one
    [FiniteDimensional ℂ V] (ht : ρ tJ ≠ 1) :
    448 ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨χ₀, hχ₀, hW₀⟩ := exists_negChar_wSpace ρ ht
  obtain ⟨h28, hfin, hneg⟩ := leviOrbit_negChar hχ₀
  obtain ⟨T, hT, hTcard⟩ := Set.exists_subset_card_eq h28
  have hTfin : T.Finite := hfin.subset hT
  set S := hTfin.toFinset with hS
  have hScard : S.card = 28 := by rw [hS, ← Set.ncard_eq_toFinset_card _ hTfin, hTcard]
  have hSmem : ∀ χ ∈ S, χ ∈ leviOrbit χ₀ := fun χ hχ => hT ((Set.Finite.mem_toFinset _).1 hχ)
  have hex : ∀ χ ∈ S, ∃ u, u ∈ wSpace ρ χ ∧ u ≠ 0 ∧ ∃ s : Fin 4 → ℂ,
      (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ i, opA ρ i u = s i • u := by
    intro χ hχ
    obtain ⟨g, hg, rfl⟩ := hSmem χ hχ
    have hW := wSpace_charConj_ne_bot ρ g hg hW₀
    let Ts := (List.finRange 4).map fun i => opA ρ i
    have hmem : ∀ S' ∈ Ts, ∃ i, S' = opA ρ i := by
      intro S' hS'
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hS'
      exact ⟨i, rfl⟩
    obtain ⟨u, hu, hu0, hTs⟩ := exists_common_eigen Ts
      (fun S' hS' => by obtain ⟨i, rfl⟩ := hmem S' hS'; exact opA_mul_self ρ i)
      (fun S₁ h₁ S₂ h₂ => by
        obtain ⟨i, rfl⟩ := hmem S₁ h₁
        obtain ⟨j, rfl⟩ := hmem S₂ h₂
        exact opA_comm ρ i j) _ hW
      (fun S' hS' w hw => by obtain ⟨i, rfl⟩ := hmem S' hS'; exact opA_mem_wSpace ρ i hw)
    have hui : ∀ i, opA ρ i u = u ∨ opA ρ i u = -u := fun i =>
      hTs _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
    refine ⟨u, hu, hu0, fun i => if opA ρ i u = u then 1 else -1, fun i => ?_, fun i => ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · dsimp only
      split_ifs with h
      · rw [h, one_smul]
      · rw [(hui i).resolve_left h, neg_one_smul]
  choose! uf hu hu0 sf hs hA using hex
  let P := S × (Fin 4 → Bool)
  let Λ : P → radicalZ ⊕ Fin 4 → ℂ := fun p a => match a with
    | .inl z => ((p.1.1 z : ℂˣ) : ℂ)
    | .inr i => if p.2 i then -sf p.1.1 i else sf p.1.1 i
  have hΛ : Function.Injective Λ := by
    rintro ⟨⟨χ, hχ⟩, ε⟩ ⟨⟨χ', hχ'⟩, ε'⟩ h
    have hχχ : χ = χ' := MonoidHom.ext fun z => Units.ext (congrFun h (.inl z))
    subst hχχ
    have hεε : ε = ε' := by
      funext i
      have := congrFun h (.inr i)
      simp only [Λ] at this
      have hne := sign_ne_neg (hs χ hχ i)
      cases he : ε i <;> cases he' : ε' i
      · rfl
      · simp only [he, he', Bool.false_eq_true, ite_false, ite_true] at this
        exact absurd this.symm hne
      · simp only [he, he', Bool.false_eq_true, ite_false, ite_true] at this
        exact absurd this hne
      · rfl
    subst hεε
    rfl
  let Wv : P → V := fun p => bvec ρ (uf p.1.1) p.2
  have hWv : ∀ p, Wv p ∈ ⨅ a, (fam ρ a).maxGenEigenspace (Λ p a) := by
    rintro ⟨⟨χ, hχ⟩, ε⟩
    refine Submodule.mem_iInf _ |>.2 fun a => Module.End.eigenspace_le_maxGenEigenspace ?_
    rw [Module.End.mem_eigenspace_iff]
    have hmem := bvec_mem ρ (hu χ hχ) ε
    rcases a with z | i
    · exact (mem_wSpace ρ).1 hmem z
    · have hneg' := hneg χ (hSmem χ hχ)
      exact bvec_eigen ρ hneg' (hu χ hχ) (hA χ hχ) ε i
  have hWv0 : ∀ p, Wv p ≠ 0 := fun p => bvec_ne_zero ρ (hu0 p.1.1 p.1.2) p.2
  have hli : LinearIndependent ℂ Wv :=
    ((fam_indep ρ).comp hΛ).linearIndependent _ hWv hWv0
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_coe, hScard, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hcard
  norm_num at hcard
  exact hcard

end CFSG.Monster.B.E6.StdF4Radical
