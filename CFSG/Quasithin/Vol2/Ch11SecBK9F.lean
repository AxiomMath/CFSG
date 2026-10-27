module

public import CFSG.Quasithin.Vol2.Ch11SecBK9E
public import CFSG.Quasithin.Vol2.Ch11SecBK9D

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2]

theorem spB_dual [Finite K] (hK : Nat.card K = 4) (χ : (Fin 2 ⊕ Fin 2 → K) →+ K)
    (hχ : ∀ x, χ x = 0 ∨ χ x = 1) : ∃ a, ∀ x, χ x = tr (spB K a x) := by
  obtain ⟨a', ha'⟩ := exists_dot_eq hK χ hχ
  exact ⟨KGNat.spJ K *ᵥ a', fun x => by rw [ha', dotProduct_eq_spB]⟩

theorem spB_add_left (a a' x : Fin 2 ⊕ Fin 2 → K) :
    spB K (a + a') x = spB K a x + spB K a' x := K7.bil_add_left a a' x

theorem eq_of_tr_spB [Finite K] (hK : Nat.card K = 4) {a a' : Fin 2 ⊕ Fin 2 → K}
    (h : ∀ x, tr (spB K a x) = tr (spB K a' x)) : a = a' := by
  by_contra hne
  have hne' : a + a' ≠ 0 := fun h0 => hne (funext fun i => by
    have h1 := congrFun h0 i
    simp only [Pi.add_apply, Pi.zero_apply] at h1
    exact (eq_neg_of_add_eq_zero_left h1).trans (CharTwo.neg_eq _))
  obtain ⟨x, hx⟩ : ∃ x, spB K (a + a') x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne' (KGNat.toBilin'_spJ_nondegenerate.1 _ hc)
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have h1 := h ((ω / spB K (a + a') x) • x)
  have h2 : tr (spB K (a + a') ((ω / spB K (a + a') x) • x)) = 1 := by
    rw [K7.bil_smul_right, div_mul_cancel₀ _ hx, tr_omega hω]
  rw [spB_add_left, tr_add, h1, CharTwo.add_self_eq_zero] at h2
  exact zero_ne_one h2

open Classical in
@[expose] noncomputable def ind {W : Type*} [Group W] (U : Subgroup W) (w : W) : K :=
  if w ∈ U then 0 else 1

theorem ind_of_mem {W : Type*} [Group W] {U : Subgroup W} {w : W} (h : w ∈ U) :
    ind (K := K) U w = 0 := by
  classical
  simp [ind, h]

theorem ind_of_not_mem {W : Type*} [Group W] {U : Subgroup W} {w : W} (h : w ∉ U) :
    ind (K := K) U w = 1 := by
  classical
  simp [ind, h]

theorem ind_eq_zero_iff {W : Type*} [Group W] {U : Subgroup W} {w : W} :
    ind (K := K) U w = 0 ↔ w ∈ U := by
  by_cases h : w ∈ U
  · simp [ind_of_mem h, h]
  · simp [ind_of_not_mem h, h]

theorem ind_cases {W : Type*} [Group W] (U : Subgroup W) (w : W) :
    ind (K := K) U w = 0 ∨ ind (K := K) U w = 1 := by
  by_cases h : w ∈ U
  · exact Or.inl (ind_of_mem h)
  · exact Or.inr (ind_of_not_mem h)

theorem ind_mul {W : Type*} [Group W] {U : Subgroup W} (hU : U.index = 2) (w w' : W) :
    ind (K := K) U (w * w') = ind U w + ind U w' := by
  have hm := Subgroup.mul_mem_iff_of_index_two hU (a := w) (b := w')
  by_cases hw : w ∈ U <;> by_cases hw' : w' ∈ U
  · rw [ind_of_mem (hm.mpr (iff_of_true hw hw')), ind_of_mem hw, ind_of_mem hw', add_zero]
  · rw [ind_of_not_mem (fun h => hw' ((hm.mp h).mp hw)), ind_of_mem hw, ind_of_not_mem hw',
      zero_add]
  · rw [ind_of_not_mem (fun h => hw ((hm.mp h).mpr hw')), ind_of_not_mem hw, ind_of_mem hw',
      add_zero]
  · rw [ind_of_mem (hm.mpr (iff_of_false hw hw')), ind_of_not_mem hw, ind_of_not_mem hw',
      CharTwo.add_self_eq_zero]

structure CovData (K : Type) [Field K] (W : Type*) [CommGroup W] where
  H : Subgroup (MulAut W)
  Z : Subgroup W
  π : ↥(StatedSp 2 K) →* ↥H
  f : W → (Fin 2 ⊕ Fin 2 → K)
  coord : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) H Z π f
  z : W
  memZ : ∀ w, w ∈ Z ↔ w = 1 ∨ w = z
  z_ne : z ≠ 1
  sq : ∀ w : W, w ^ 2 = 1
  fixZ : ∀ h ∈ H, ∀ w ∈ Z, h w = w
  U₀ : Subgroup W
  index₀ : U₀.index = 2
  z_not_mem₀ : z ∉ U₀

namespace CovData

variable {W : Type*} [CommGroup W] (C : CovData K W)

theorem z_mem : C.z ∈ C.Z := (C.memZ C.z).mpr (Or.inr rfl)

theorem f_z : C.f C.z = 0 := (C.coord.ker C.z).mpr C.z_mem

include C in
theorem inv_eq (w : W) : w⁻¹ = w :=
  inv_eq_iff_mul_eq_one.mpr (by rw [← pow_two, C.sq])

theorem pi_z (γ : ↥(StatedSp 2 K)) : ((C.π γ : ↥C.H) : MulAut W) C.z = C.z :=
  C.fixZ _ (C.π γ).2 C.z C.z_mem

@[expose] noncomputable def chi (a : Fin 2 ⊕ Fin 2 → K) (w : W) : K :=
  ind C.U₀ w + tr (spB K a (C.f w))

theorem chi_mul (a : Fin 2 ⊕ Fin 2 → K) (w w' : W) :
    C.chi a (w * w') = C.chi a w + C.chi a w' := by
  unfold chi
  rw [ind_mul C.index₀, C.coord.map_mul, map_add, tr_add]
  ring

theorem chi_one (a : Fin 2 ⊕ Fin 2 → K) : C.chi a 1 = 0 := by
  have h := C.chi_mul a 1 1
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

theorem chi_z (a : Fin 2 ⊕ Fin 2 → K) : C.chi a C.z = 1 := by
  unfold chi
  rw [ind_of_not_mem C.z_not_mem₀, C.f_z, map_zero, tr_zero, add_zero]

theorem chi_cases [Finite K] (hK : Nat.card K = 4) (a : Fin 2 ⊕ Fin 2 → K) (w : W) :
    C.chi a w = 0 ∨ C.chi a w = 1 := by
  unfold chi
  rcases ind_cases (K := K) C.U₀ w with h | h <;>
    rcases tr_eq_zero_or_one hK (spB K a (C.f w)) with h' | h' <;> rw [h, h']
  · exact Or.inl (add_zero 0)
  · exact Or.inr (zero_add 1)
  · exact Or.inr (add_zero 1)
  · exact Or.inl (CharTwo.add_self_eq_zero 1)

@[expose] noncomputable def compl (a : Fin 2 ⊕ Fin 2 → K) : Subgroup W where
  carrier := {w | C.chi a w = 0}
  one_mem' := C.chi_one a
  mul_mem' {w w'} hw hw' := by
    show C.chi a (w * w') = 0
    rw [C.chi_mul, show C.chi a w = 0 from hw, show C.chi a w' = 0 from hw', add_zero]
  inv_mem' {w} hw := by
    show C.chi a w⁻¹ = 0
    rw [C.inv_eq]
    exact hw

theorem mem_compl {a : Fin 2 ⊕ Fin 2 → K} {w : W} : w ∈ C.compl a ↔ C.chi a w = 0 := Iff.rfl

theorem z_not_mem_compl (a : Fin 2 ⊕ Fin 2 → K) : C.z ∉ C.compl a := by
  rw [mem_compl, chi_z]
  exact one_ne_zero

theorem exists_eq_compl [Finite K] (hK : Nat.card K = 4) {U : Subgroup W} (hU : U.index = 2)
    (hz : C.z ∉ U) : ∃ a, U = C.compl a := by
  obtain ⟨σ, hσ⟩ := C.coord.exists_section C.sq
  have hφ : ∀ w, ind (K := K) U w + ind C.U₀ w =
      ind U (σ (Multiplicative.ofAdd (C.f w))) + ind C.U₀ (σ (Multiplicative.ofAdd (C.f w))) := by
    intro w
    set s := σ (Multiplicative.ofAdd (C.f w)) with hs
    have hws : w * s⁻¹ ∈ C.Z := (C.coord.ker _).mp (by
      rw [C.coord.map_mul_inv, hs, hσ, toAdd_ofAdd, sub_self])
    have hw : w = (w * s⁻¹) * s := by group
    rw [hw, ind_mul hU, ind_mul C.index₀]
    rcases (C.memZ _).mp hws with h | h <;> rw [h]
    · rw [ind_of_mem (one_mem U), ind_of_mem (one_mem C.U₀), zero_add, zero_add]
    · rw [ind_of_not_mem hz, ind_of_not_mem C.z_not_mem₀]
      ring_nf
      rw [show (2 : K) = 0 from CharTwo.two_eq_zero]
      ring
  set φ : (Fin 2 ⊕ Fin 2 → K) → K := fun x =>
    ind (K := K) U (σ (Multiplicative.ofAdd x)) + ind (K := K) C.U₀ (σ (Multiplicative.ofAdd x))
    with hφdef
  let χ : (Fin 2 ⊕ Fin 2 → K) →+ K :=
    { toFun := φ
      map_zero' := by
        rw [hφdef]
        simp only [ofAdd_zero, map_one]
        rw [ind_of_mem (one_mem U), ind_of_mem (one_mem C.U₀), add_zero]
      map_add' := fun x y => by
        rw [hφdef]
        simp only [ofAdd_add, map_mul]
        rw [ind_mul hU, ind_mul C.index₀]
        ring }
  have hχφ : ∀ x, χ x = φ x := fun x => rfl
  have hχ : ∀ x, χ x = 0 ∨ χ x = 1 := fun x => by
    rw [hχφ, hφdef]
    rcases ind_cases (K := K) U (σ (Multiplicative.ofAdd x)) with h | h <;>
      rcases ind_cases (K := K) C.U₀ (σ (Multiplicative.ofAdd x)) with h' | h' <;>
      simp only [h, h']
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add 1)
    · exact Or.inr (add_zero 1)
    · exact Or.inl (CharTwo.add_self_eq_zero 1)
  obtain ⟨a, ha⟩ := spB_dual hK χ hχ
  refine ⟨a, ?_⟩
  ext w
  rw [mem_compl, chi, ← ha (C.f w), hχφ, hφdef]
  simp only
  rw [← hφ w, ← add_assoc, add_comm (ind C.U₀ w), add_assoc, CharTwo.add_self_eq_zero, add_zero,
    ind_eq_zero_iff]

theorem compl_injective [Finite K] (hK : Nat.card K = 4) : Function.Injective C.compl := by
  intro a a' h
  apply eq_of_tr_spB hK
  intro x
  obtain ⟨w, rfl⟩ := C.coord.surj x
  have h1 : w ∈ C.compl a ↔ w ∈ C.compl a' := by rw [h]
  rw [mem_compl, mem_compl] at h1
  unfold chi at h1
  rcases ind_cases (K := K) C.U₀ w with h0 | h0 <;> rw [h0] at h1 <;>
    rcases tr_eq_zero_or_one hK (spB K a (C.f w)) with ha | ha <;>
    rcases tr_eq_zero_or_one hK (spB K a' (C.f w)) with ha' | ha' <;>
    rw [ha, ha'] at h1 ⊢ <;> simp_all [CharTwo.add_self_eq_zero]

end CovData

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
