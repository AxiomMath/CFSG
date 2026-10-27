module

public import CFSG.Quasithin.H13.L32AStRec
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

@[expose] def actF (g : Γ) (f : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 := fun i => f (permOf g i)

theorem actF_mul (g h : Γ) (f : Fin 8 → ZMod 2) : actF (g * h) f = actF g (actF h f) := by
  funext i
  simp only [actF, permOf_mul]

theorem actF_one (f : Fin 8 → ZMod 2) : actF 1 f = f := by
  funext i
  simp only [actF, permOf_apply, inv_one, one_smul, idxOf_vecOf]

theorem actF_add (g : Γ) (f f' : Fin 8 → ZMod 2) : actF g (f + f') = actF g f + actF g f' := rfl

theorem actF_inv_actF (g : Γ) (f : Fin 8 → ZMod 2) : actF g⁻¹ (actF g f) = f := by
  rw [← actF_mul, inv_mul_cancel, actF_one]

@[expose] def eF (i : Fin 8) : Fin 8 → ZMod 2 := Pi.single i 1

theorem permOf_symm (g : Γ) (j : Fin 8) : (permOf g).symm j = idxOf (g • vecOf j) := by
  apply (permOf g).injective
  rw [Equiv.apply_symm_apply, permOf_apply, vecOf_idxOf, inv_smul_smul, idxOf_vecOf]

theorem actF_eF (g : Γ) (i : Fin 8) : actF g (eF i) = eF (idxOf (g • vecOf i)) := by
  funext j
  simp only [actF, eF, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    rw [← h, permOf_apply, vecOf_idxOf, smul_inv_smul, idxOf_vecOf]
  · intro h
    rw [h, permOf_apply, vecOf_idxOf, inv_smul_smul, idxOf_vecOf]

@[expose] def epsF (f : Fin 8 → ZMod 2) : V3 := ∑ i, f i • vecOf i

theorem epsF_add (f f' : Fin 8 → ZMod 2) : epsF (f + f') = epsF f + epsF f' := by
  simp only [epsF, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem smul_zmod_comm (g : Γ) (c : ZMod 2) (v : V3) : g • (c • v) = c • (g • v) := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, smul_zero]
  · rw [one_smul, one_smul]

theorem epsF_actF (g : Γ) (f : Fin 8 → ZMod 2) : epsF (actF g f) = g • epsF f := by
  simp only [epsF, actF, Finset.smul_sum, smul_zmod_comm]
  rw [← Equiv.sum_comp (permOf g).symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.apply_symm_apply, permOf_symm, vecOf_idxOf]

@[expose] def epsHom : (Fin 8 → ZMod 2) →+ V3 where
  toFun := epsF
  map_zero' := by simp [epsF]
  map_add' := epsF_add

theorem vecOf_one : vecOf 1 = ![1, 0, 0] := by decide

theorem exists_smul_e1 : ∀ i : Fin 8, i ≠ 0 → ∃ g : Γ, g • vecOf 1 = vecOf i := by
  decide +kernel

theorem exists_Lp_smul : ∀ c j : Fin 8, c ≠ 0 → c ≠ 1 → j ≠ 0 → j ≠ 1 →
    ∃ h : Γ, h ∈ Lp ∧ h • vecOf c = vecOf j := by
  decide +kernel

@[expose] def s3 : Fin 3 → Γ :=
  ![⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩, ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 1, 1; 0, 1, 0; 1, 1, 0], by decide⟩]

theorem exists_weight_two : ∀ f : Fin 8 → ZMod 2, epsF f ≠ 0 → ∃ k : Fin 3, ∃ a b : Fin 8,
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ f + actF (s3 k) f = eF a + eF b := by
  decide +kernel

@[expose] def eL : Fin 8 → ZMod 2 := ![0, 1, 1, 1, 0, 0, 0, 0]

@[expose] def bL : Fin 8 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

@[expose] def om : Fin 8 → ZMod 2 := ![0, 1, 1, 1, 1, 1, 1, 1]

@[expose] def s7 : Fin 7 → Γ :=
  ![⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩, ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 1], by decide⟩, ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩,
    ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 1], by decide⟩, ⟨!![0, 0, 1; 0, 1, 0; 1, 1, 0], by decide⟩,
    ⟨!![0, 0, 1; 0, 1, 0; 1, 1, 1], by decide⟩]

@[expose] def b4 : Fin 4 → Γ :=
  ![⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩, ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩,
    ⟨!![0, 1, 0; 0, 1, 1; 1, 0, 0], by decide⟩, ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩]

theorem ker_eps_span : ∀ f : Fin 8 → ZMod 2, epsF f = 0 → ∃ c : Fin 5 → ZMod 2,
    f = c 0 • eF 0 + c 1 • actF (b4 0) eL + c 2 • actF (b4 1) eL + c 3 • actF (b4 2) eL +
      c 4 • actF (b4 3) eL := by
  decide +kernel

theorem ker_eps_cases : ∀ f : Fin 8 → ZMod 2, epsF f = 0 →
    f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0 ∨
      (∃ k : Fin 7, actF (s7 k) f = eL ∨ actF (s7 k) f = eL + eF 0) ∨
      (∃ k : Fin 7, actF (s7 k) f = bL ∨ actF (s7 k) f = bL + eF 0) := by
  decide +kernel

theorem om_add_bL : om + bL = eL := by decide

theorem card_PE : (Finset.univ.filter fun f : Fin 8 → ZMod 2 => epsF f = 0).card = 32 := by
  decide +kernel

theorem card_PW : (Finset.univ.filter fun f : Fin 8 → ZMod 2 => epsF f = 0 ∧
    (f = 0 ∨ f = eF 0 ∨ ∃ k : Fin 7, actF (s7 k) f = bL ∨ actF (s7 k) f = bL + eF 0)).card =
    16 := by
  decide +kernel

theorem card_PO : (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
    f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0).card = 4 := by
  decide +kernel

theorem card_PZ : (Finset.univ.filter fun f : Fin 8 → ZMod 2 => f = 0 ∨ f = eF 0).card = 2 := by
  decide +kernel

theorem epsF_eF (i : Fin 8) : epsF (eF i) = vecOf i := by
  simp [epsF, eF, Pi.single_apply]

theorem Ll_smul_e1 : ∀ g : Γ, g ∈ Ll →
    g • vecOf 1 = vecOf 1 ∨ g • vecOf 1 = vecOf 2 ∨ g • vecOf 1 = vecOf 3 := by
  decide +kernel

theorem exists_Ll_smul_e1 : ∀ j : Fin 8, (j = 1 ∨ j = 2 ∨ j = 3) →
    ∃ g : Γ, g ∈ Ll ∧ g • vecOf 1 = vecOf j := by
  decide +kernel

@[expose] def tLl : Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def sLl : Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

theorem tLl_one : idxOf (tLl • vecOf 1) = 1 := by decide
theorem tLl_two : idxOf (tLl • vecOf 2) = 3 := by decide
theorem tLl_three : idxOf (tLl • vecOf 3) = 2 := by decide
theorem sLl_one : idxOf (sLl • vecOf 1) = 2 := by decide
theorem sLl_two : idxOf (sLl • vecOf 2) = 1 := by decide
theorem sLl_three : idxOf (sLl • vecOf 3) = 3 := by decide

@[expose, instance_reducible] def addCommGroupOfAddSelf {M : Type} [AddGroup M]
    (h2 : ∀ m : M, m + m = 0) : AddCommGroup M :=
  { ‹AddGroup M› with
    add_comm := fun a b => by
      have hneg : ∀ c : M, -c = c := fun c => neg_eq_of_add_eq_zero_right (h2 c)
      calc a + b = -(a + b) := (hneg _).symm
        _ = -b + -a := neg_add_rev a b
        _ = b + a := by rw [hneg, hneg] }

section Abstract

variable {M : Type} [AddCommGroup M] (ρ : Γ →* AddMonoid.End M)

@[expose] def zs (c : ZMod 2) (m : M) : M := if c = 0 then 0 else m

omit [AddCommGroup M] in
theorem zs_add {M : Type} [AddCommGroup M] (h2 : ∀ m : M, m + m = 0) (c d : ZMod 2) (m : M) :
    zs (c + d) m = zs c m + zs d m := by
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
  · simp [zs]
  · simp [zs]
  · simp [zs]
  · rw [h11]; simp [zs, h10, h2]

theorem map_zs (g : Γ) (c : ZMod 2) (m : M) : ρ g (zs c m) = zs c (ρ g m) := by
  unfold zs
  split_ifs <;> simp

theorem rho_mul (g h : Γ) (m : M) : ρ (g * h) m = ρ g (ρ h m) := by
  rw [map_mul]; rfl

theorem rho_one (m : M) : ρ 1 m = m := by
  rw [map_one]; rfl

variable (x : M)

@[expose] noncomputable def gOf (i : Fin 8) : Γ :=
  if h : i = 0 then 1 else Classical.choose (exists_smul_e1 i h)

theorem gOf_smul {i : Fin 8} (hi : i ≠ 0) : gOf i • vecOf 1 = vecOf i := by
  simp only [gOf, hi, dite_false]
  exact Classical.choose_spec (exists_smul_e1 i hi)

@[expose] noncomputable def xpt (i : Fin 8) : M := if i = 0 then 0 else ρ (gOf i) x

@[expose] noncomputable def phiF (f : Fin 8 → ZMod 2) : M := ∑ i, zs (f i) (xpt ρ x i)

theorem phiF_add (h2 : ∀ m : M, m + m = 0) (f f' : Fin 8 → ZMod 2) :
    phiF ρ x (f + f') = phiF ρ x f + phiF ρ x f' := by
  simp only [phiF, Pi.add_apply, zs_add h2, Finset.sum_add_distrib]

theorem phiF_eF (i : Fin 8) : phiF ρ x (eF i) = xpt ρ x i := by
  simp only [phiF, eF, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [zs]
  · intro j _ hj
    simp [zs, hj]
  · simp

@[expose] noncomputable def phiHom (h2 : ∀ m : M, m + m = 0) : (Fin 8 → ZMod 2) →+ M where
  toFun := phiF ρ x
  map_zero' := by simp [phiF, zs]
  map_add' := phiF_add ρ x h2

variable {ρ x}
variable (hx : ∀ g ∈ Lp, ρ g x = x)
include hx

theorem rho_eq_of_smul {g h : Γ} (hgh : g • vecOf 1 = h • vecOf 1) : ρ g x = ρ h x := by
  have hm : h⁻¹ * g ∈ Lp := by
    rw [Lp, MulAction.mem_stabilizer_iff, mul_smul, ← vecOf_one, hgh, inv_smul_smul]
  calc ρ g x = ρ h (ρ (h⁻¹ * g) x) := by rw [← rho_mul, mul_inv_cancel_left]
    _ = ρ h x := by rw [hx _ hm]

theorem rho_eq_xpt (g : Γ) : ρ g x = xpt ρ x (idxOf (g • vecOf 1)) := by
  have hne : idxOf (g • vecOf 1) ≠ 0 := by
    intro h
    have h1 := congrArg vecOf h
    rw [vecOf_idxOf, show vecOf 0 = 0 by decide] at h1
    have h2 : vecOf 1 = 0 := by
      have := congrArg (fun v => g⁻¹ • v) h1
      simpa using this
    exact absurd h2 (by decide)
  simp only [xpt, hne, ite_false]
  exact rho_eq_of_smul hx (by rw [gOf_smul hne, vecOf_idxOf])

theorem xpt_smul (g : Γ) (j : Fin 8) : xpt ρ x (idxOf (g • vecOf j)) = ρ g (xpt ρ x j) := by
  by_cases hj : j = 0
  · have h0 : idxOf (g • vecOf j) = 0 := by
      rw [hj, show vecOf 0 = 0 by decide, smul_zero]; decide
    rw [h0, hj]
    simp only [xpt, ite_true, map_zero]
  · have hx' := rho_eq_xpt hx (g * gOf j)
    rw [mul_smul, gOf_smul hj] at hx'
    rw [← hx', rho_mul]
    simp only [xpt, hj, ite_false]

theorem phiF_actF (g : Γ) (f : Fin 8 → ZMod 2) : phiF ρ x (actF g f) = ρ g (phiF ρ x f) := by
  simp only [phiF, actF, map_sum, map_zs]
  rw [← Equiv.sum_comp (permOf g).symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.apply_symm_apply, permOf_symm, xpt_smul hx]

theorem xpt_one : xpt ρ x 1 = x := by
  have := rho_eq_xpt hx 1
  rw [rho_one, one_smul, idxOf_vecOf] at this
  exact this.symm

theorem fixed_of_xpt_eq {a b : Fin 8} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : xpt ρ x a = xpt ρ x b) (g : Γ) : ρ g x = x := by
  set g₀ := gOf a with hg₀
  have hga : g₀ • vecOf 1 = vecOf a := gOf_smul ha
  set c := idxOf (g₀⁻¹ • vecOf b) with hc
  have h1 : ρ g₀⁻¹ (xpt ρ x a) = x := by
    rw [← xpt_smul hx, ← hga, inv_smul_smul, idxOf_vecOf, xpt_one hx]
  have h2 : ρ g₀⁻¹ (xpt ρ x b) = xpt ρ x c := by rw [← xpt_smul hx]
  have hxc : x = xpt ρ x c :=
    calc x = ρ g₀⁻¹ (xpt ρ x a) := h1.symm
      _ = ρ g₀⁻¹ (xpt ρ x b) := by rw [h]
      _ = xpt ρ x c := h2
  have hc0 : c ≠ 0 := by
    intro h0
    have h3 := congrArg vecOf h0
    rw [hc, vecOf_idxOf, show vecOf 0 = 0 by decide] at h3
    have h4 : vecOf b = 0 := by
      have := congrArg (fun v => g₀ • v) h3
      simpa using this
    exact hb (by rw [← idxOf_vecOf b, h4]; decide)
  have hc1 : c ≠ 1 := by
    intro h0
    have h3 := congrArg vecOf h0
    rw [hc, vecOf_idxOf] at h3
    have h4 : vecOf b = vecOf a := by
      rw [← hga, ← h3, smul_inv_smul]
    exact hab (by rw [← idxOf_vecOf a, ← h4, idxOf_vecOf])
  have hall : ∀ j : Fin 8, j ≠ 0 → xpt ρ x j = x := by
    intro j hj0
    by_cases hj1 : j = 1
    · rw [hj1, xpt_one hx]
    obtain ⟨h', hh', hhc⟩ := exists_Lp_smul c j hc0 hc1 hj0 hj1
    calc xpt ρ x j = xpt ρ x (idxOf (h' • vecOf c)) := by rw [hhc, idxOf_vecOf]
      _ = ρ h' (xpt ρ x c) := xpt_smul hx h' c
      _ = ρ h' x := by rw [← hxc]
      _ = x := hx h' hh'
  rw [rho_eq_xpt hx g]
  refine hall _ fun h0 => ?_
  have h3 := congrArg vecOf h0
  rw [vecOf_idxOf, show vecOf 0 = 0 by decide] at h3
  have h4 : vecOf 1 = 0 := by
    have := congrArg (fun v => g⁻¹ • v) h3
    simpa using this
  exact absurd h4 (by decide)

theorem eps_eq_zero_of_phi (h2 : ∀ m : M, m + m = 0) (hnf : ∃ g : Γ, ρ g x ≠ x)
    {f : Fin 8 → ZMod 2} (hf : phiF ρ x f = 0) : epsF f = 0 := by
  by_contra hne
  obtain ⟨k, a, b, ha, hb, hab, hfab⟩ := exists_weight_two f hne
  have h1 : phiF ρ x (f + actF (s3 k) f) = 0 := by
    rw [phiF_add _ _ h2, phiF_actF hx, hf, map_zero, add_zero]
  rw [hfab, phiF_add _ _ h2, phiF_eF, phiF_eF] at h1
  have h3 : xpt ρ x a = xpt ρ x b := by
    have := congrArg (· + xpt ρ x b) h1
    simpa [add_assoc, h2] using this
  obtain ⟨g, hg⟩ := hnf
  exact hg (fixed_of_xpt_eq hx ha hb hab h3 g)

end Abstract

theorem card_of_iff {K : AddSubgroup (Fin 8 → ZMod 2)} {P : (Fin 8 → ZMod 2) → Prop}
    [DecidablePred P] (h : ∀ f, f ∈ K ↔ P f) : Nat.card K = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight h)

theorem card_invariant (K : AddSubgroup (Fin 8 → ZMod 2)) (he0 : eF 0 ∈ K)
    (hinv : ∀ g : Γ, ∀ f ∈ K, actF g f ∈ K) (hε : ∀ f ∈ K, epsF f = 0) :
    (eL ∈ K → ∀ f, f ∈ K ↔ epsF f = 0) ∧
      (Nat.card K = 2 ∨ Nat.card K = 4 ∨ Nat.card K = 16 ∨ Nat.card K = 32) := by
  classical
  have hsmul : ∀ (c : ZMod 2) (f : Fin 8 → ZMod 2), f ∈ K → c • f ∈ K := by
    intro c f hf
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul]; exact K.zero_mem
    · rw [one_smul]; exact hf
  have hE : eL ∈ K → ∀ f, f ∈ K ↔ epsF f = 0 := by
    intro heL f
    refine ⟨hε f, fun hf => ?_⟩
    obtain ⟨c, rfl⟩ := ker_eps_span f hf
    refine K.add_mem (K.add_mem (K.add_mem (K.add_mem (hsmul _ _ he0) ?_) ?_) ?_) ?_ <;>
      exact hsmul _ _ (hinv _ _ heL)
  refine ⟨hE, ?_⟩
  by_cases heL : eL ∈ K
  · right; right; right
    rw [card_of_iff (hE heL), card_PE]
  have hA : ∀ f ∈ K, ∀ k : Fin 7, actF (s7 k) f ≠ eL ∧ actF (s7 k) f ≠ eL + eF 0 := by
    intro f hf k
    refine ⟨fun h => heL (h ▸ hinv _ _ hf), fun h => heL ?_⟩
    have h1 : eL + eF 0 ∈ K := h ▸ hinv _ _ hf
    have h2 := K.add_mem h1 he0
    rwa [add_assoc, show eF 0 + eF 0 = (0 : Fin 8 → ZMod 2) by decide, add_zero] at h2
  have hmem_e0 : ∀ f, f + eF 0 ∈ K → f ∈ K := fun f h => by
    have := K.add_mem h he0
    rwa [add_assoc, show eF 0 + eF 0 = (0 : Fin 8 → ZMod 2) by decide, add_zero] at this
  by_cases hbL : bL ∈ K
  ·
    right; right; left
    have hom : om ∉ K := fun h => heL (om_add_bL ▸ K.add_mem h hbL)
    have hiff : ∀ f, f ∈ K ↔ (epsF f = 0 ∧
        (f = 0 ∨ f = eF 0 ∨ ∃ k : Fin 7, actF (s7 k) f = bL ∨ actF (s7 k) f = bL + eF 0)) := by
      intro f
      constructor
      · intro hf
        refine ⟨hε f hf, ?_⟩
        rcases ker_eps_cases f (hε f hf) with h | h | h | h | ⟨k, hk⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd (h ▸ hf) hom
        · exact absurd (hmem_e0 _ (h ▸ hf)) hom
        · rcases hk with hk | hk
          · exact absurd hk (hA f hf k).1
          · exact absurd hk (hA f hf k).2
        · exact Or.inr (Or.inr h)
      · rintro ⟨-, h | h | ⟨k, hk | hk⟩⟩
        · exact h ▸ K.zero_mem
        · exact h ▸ he0
        · rw [← actF_inv_actF (s7 k) f, hk]; exact hinv _ _ hbL
        · rw [← actF_inv_actF (s7 k) f, hk]; exact hinv _ _ (K.add_mem hbL he0)
    rw [card_of_iff hiff, card_PW]
  have hB : ∀ f ∈ K, ∀ k : Fin 7, actF (s7 k) f ≠ bL ∧ actF (s7 k) f ≠ bL + eF 0 := by
    intro f hf k
    refine ⟨fun h => hbL (h ▸ hinv _ _ hf), fun h => hbL (hmem_e0 _ (h ▸ hinv _ _ hf))⟩
  have hsub : ∀ f ∈ K, f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0 := by
    intro f hf
    rcases ker_eps_cases f (hε f hf) with h | h | h | h | ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases hk with hk | hk
      · exact absurd hk (hA f hf k).1
      · exact absurd hk (hA f hf k).2
    · rcases hk with hk | hk
      · exact absurd hk (hB f hf k).1
      · exact absurd hk (hB f hf k).2
  by_cases hom : om ∈ K
  · right; left
    have hiff : ∀ f, f ∈ K ↔ (f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0) := by
      intro f
      refine ⟨hsub f, ?_⟩
      rintro (h | h | h | h)
      · exact h ▸ K.zero_mem
      · exact h ▸ he0
      · exact h ▸ hom
      · exact h ▸ K.add_mem hom he0
    rw [card_of_iff hiff, card_PO]
  · left
    have hiff : ∀ f, f ∈ K ↔ (f = 0 ∨ f = eF 0) := by
      intro f
      constructor
      · intro hf
        rcases hsub f hf with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (h ▸ hf) hom
        · exact absurd (hmem_e0 _ (h ▸ hf)) hom
      · rintro (h | h)
        · exact h ▸ K.zero_mem
        · exact h ▸ he0
    rw [card_of_iff hiff, card_PZ]

section Main

variable {M : Type} [AddCommGroup M] [Finite M] {ρ : Γ →* AddMonoid.End M} {x : M}

omit [AddCommGroup M] [Finite M] in
theorem v3_four : ∀ v w : V3, v + w + v + w = 0 := by decide

omit [Finite M] in
theorem phiHom_apply (h2 : ∀ m : M, m + m = 0) (f : Fin 8 → ZMod 2) :
    phiHom ρ x h2 f = phiF ρ x f := rfl

omit [Finite M] in
theorem phiHom_surjective (hx : ∀ g ∈ Lp, ρ g x = x) (h2 : ∀ m : M, m + m = 0)
    (hgen : AddSubgroup.closure (Set.range fun g : Γ => ρ g x) = ⊤) :
    Function.Surjective (phiHom ρ x h2) := by
  rw [← AddMonoidHom.range_eq_top, eq_top_iff, ← hgen, AddSubgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  refine ⟨eF (idxOf (g • vecOf 1)), ?_⟩
  rw [phiHom_apply, phiF_eF, ← rho_eq_xpt hx]

omit [Finite M] in
theorem ker_facts (hx : ∀ g ∈ Lp, ρ g x = x) (h2 : ∀ m : M, m + m = 0)
    (hnf : ∃ g : Γ, ρ g x ≠ x) :
    eF 0 ∈ (phiHom ρ x h2).ker ∧ (∀ g : Γ, ∀ f ∈ (phiHom ρ x h2).ker,
      actF g f ∈ (phiHom ρ x h2).ker) ∧ ∀ f ∈ (phiHom ρ x h2).ker, epsF f = 0 := by
  refine ⟨?_, fun g f hf => ?_, fun f hf => eps_eq_zero_of_phi hx h2 hnf hf⟩
  · rw [AddMonoidHom.mem_ker, phiHom_apply, phiF_eF]
    simp [xpt]
  · rw [AddMonoidHom.mem_ker, phiHom_apply] at hf ⊢
    rw [phiF_actF hx, hf, map_zero]

omit [AddCommGroup M] [Finite M] in
theorem card_five [DecidableEq M] {a b c d e : M} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : ({a, b, c, d, e} : Finset M).card = 5 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde]

theorem h55_core (h2 : ∀ m : M, m + m = 0) (hx : ∀ g ∈ Lp, ρ g x = x) (hx0 : x ≠ 0)
    (hgen : AddSubgroup.closure (Set.range fun g : Γ => ρ g x) = ⊤)
    (hcard : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g x = y}) = 4) :
    IsoMod ρ ρV := by
  classical
  have hneg : ∀ m : M, -m = m := fun m => neg_eq_of_add_eq_zero_right (h2 m)
  have hsub : ∀ a b : M, a + b = 0 → a = b := fun a b h => by
    rw [← hneg b]; exact eq_neg_of_add_eq_zero_left h
  set x1 := xpt ρ x 1 with hx1
  set x2 := xpt ρ x 2 with hx2
  set x3 := xpt ρ x 3 with hx3
  have hset : {y | ∃ g ∈ Ll, ρ g x = y} = ({x1, x2, x3} : Set M) := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [rho_eq_xpt hx g]
      rcases Ll_smul_e1 g hg with h | h | h <;> rw [h, idxOf_vecOf]
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, Ll.one_mem, by rw [rho_one, hx1, xpt_one hx]⟩
      · obtain ⟨g, hg, hg2⟩ := exists_Ll_smul_e1 2 (by decide)
        exact ⟨g, hg, by rw [rho_eq_xpt hx g, hg2, idxOf_vecOf]⟩
      · obtain ⟨g, hg, hg3⟩ := exists_Ll_smul_e1 3 (by decide)
        exact ⟨g, hg, by rw [rho_eq_xpt hx g, hg3, idxOf_vecOf]⟩
  rw [hset] at hcard
  have hinj : ∀ (g : Γ) (m : M), ρ g m = 0 → m = 0 := fun g m h => by
    have := congrArg (ρ g⁻¹) h
    rwa [← rho_mul, inv_mul_cancel, rho_one, map_zero] at this
  have hne0 : ∀ j : Fin 8, j ≠ 0 → xpt ρ x j ≠ 0 := by
    intro j hj h
    simp only [xpt, hj, ite_false] at h
    exact hx0 (hinj _ _ h)
  have h10 : x1 ≠ 0 := hne0 1 (by decide)
  have h20 : x2 ≠ 0 := hne0 2 (by decide)
  have h30 : x3 ≠ 0 := hne0 3 (by decide)
  have ht1 : ρ tLl x1 = x1 := by rw [hx1, ← xpt_smul hx, tLl_one]
  have ht2 : ρ tLl x2 = x3 := by rw [hx2, ← xpt_smul hx, tLl_two]
  have ht3 : ρ tLl x3 = x2 := by rw [hx3, ← xpt_smul hx, tLl_three]
  have hs1 : ρ sLl x1 = x2 := by rw [hx1, ← xpt_smul hx, sLl_one]
  have hs3 : ρ sLl x3 = x3 := by rw [hx3, ← xpt_smul hx, sLl_three]
  have hs2 : ρ sLl x2 = x1 := by rw [hx2, ← xpt_smul hx, sLl_two]
  have hall : x1 = x2 → x1 = x3 → False := by
    intro h12 h13
    have hS : ({x1, x2, x3} : Set M) = {x1} := by
      rw [← h12, ← h13]; simp
    rw [hS, ← AddSubgroup.zmultiples_eq_closure] at hcard
    have hord : addOrderOf x1 = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul]; exact h2 x1) h10
    rw [Nat.card_zmultiples, hord] at hcard
    exact absurd hcard (by norm_num)
  have h12 : x1 ≠ x2 := fun h => hall h (by rw [← ht1, h, ht2])
  have h13 : x1 ≠ x3 := fun h => hall (by rw [← ht1, h, ht3]) h
  have h23 : x2 ≠ x3 := fun h => hall (by rw [← hs2, h, hs3]) (by rw [← hs2, h, hs3])
  have h123 : x1 + x2 = x3 := by
    by_contra hne
    set C := AddSubgroup.closure ({x1, x2, x3} : Set M) with hC
    have hmem : ∀ y ∈ ({0, x1, x2, x3, x1 + x2} : Finset M), y ∈ C := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact C.zero_mem
      · exact AddSubgroup.subset_closure (by simp)
      · exact AddSubgroup.subset_closure (by simp)
      · exact AddSubgroup.subset_closure (by simp)
      · exact C.add_mem (AddSubgroup.subset_closure (by simp))
          (AddSubgroup.subset_closure (by simp))
    have h5 : ({0, x1, x2, x3, x1 + x2} : Finset M).card = 5 := by
      refine card_five (Ne.symm h10) (Ne.symm h20) (Ne.symm h30) ?_ h12 h13 ?_ h23 ?_ ?_
      · intro h; exact h12 (hsub _ _ h.symm)
      · intro h
        apply h20
        have h' := congrArg (fun y => x1 + y) h
        simp only [← add_assoc, h2, zero_add] at h'
        exact h'.symm
      · intro h
        apply h10
        have h' := congrArg (fun y => y + x2) h
        simp only [add_assoc, h2, add_zero] at h'
        exact h'.symm
      · exact fun h => hne h.symm
    have hle : ({0, x1, x2, x3, x1 + x2} : Finset M).card ≤ Nat.card C := by
      rw [← Set.ncard_coe_finset]
      show _ ≤ Nat.card ↥(C : Set M)
      rw [Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard (fun y hy => hmem y hy) (Set.toFinite _)
    rw [h5, hcard] at hle
    omega
  have hphiL : phiF ρ x eL = 0 := by
    have : phiF ρ x eL = x1 + x2 + x3 := by
      simp [phiF, eL, zs, Fin.sum_univ_eight, xpt]
      rw [hx1, hx2, hx3]
      simp [xpt, add_assoc]
    rw [this, h123, h2]
  have hnf : ∃ g : Γ, ρ g x ≠ x := by
    by_contra hcon
    push Not at hcon
    apply h12
    rw [hx1, hx2, xpt_one hx]
    simp only [xpt, show (2 : Fin 8) ≠ 0 by decide, ite_false]
    exact (hcon _).symm
  have hsurj := phiHom_surjective hx h2 hgen
  obtain ⟨he0, hinv, hε⟩ := ker_facts hx h2 hnf
  obtain ⟨hE, -⟩ := card_invariant _ he0 hinv hε
  have hiff := hE (by rw [AddMonoidHom.mem_ker, phiHom_apply]; exact hphiL)
  let ψ : V3 →+ M :=
    { toFun := fun v => phiF ρ x (eF (idxOf v))
      map_zero' := by
        rw [show idxOf 0 = 0 by decide, phiF_eF]
        simp [xpt]
      map_add' := fun v w => by
        have hd : eF (idxOf (v + w)) + eF (idxOf v) + eF (idxOf w) ∈ (phiHom ρ x h2).ker := by
          rw [hiff, epsF_add, epsF_add, epsF_eF, epsF_eF, epsF_eF, vecOf_idxOf, vecOf_idxOf,
            vecOf_idxOf]
          exact v3_four v w
        rw [AddMonoidHom.mem_ker, phiHom_apply, phiF_add _ _ h2, phiF_add _ _ h2] at hd
        have := congrArg (· + (phiF ρ x (eF (idxOf v)) + phiF ρ x (eF (idxOf w)))) hd
        simpa [add_assoc, h2] using this }
  refine ⟨ψ, ⟨?_, ?_⟩, fun g v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : eF (idxOf v) ∈ (phiHom ρ x h2).ker := by
      rw [AddMonoidHom.mem_ker, phiHom_apply]; exact hv
    rw [hiff, epsF_eF, vecOf_idxOf] at h1
    exact h1
  · rw [← AddMonoidHom.range_eq_top (f := ψ), eq_top_iff, ← hgen, AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨g • vecOf 1, ?_⟩
    show phiF ρ x (eF (idxOf (g • vecOf 1))) = ρ g x
    rw [phiF_eF, ← rho_eq_xpt hx]
  · show phiF ρ x (eF (idxOf (g • v))) = ρ g (phiF ρ x (eF (idxOf v)))
    rw [← phiF_actF hx, actF_eF, vecOf_idxOf]

end Main

theorem volI_H_5_5 :
    ∀ (M : Type) [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M), (∀ m : M, m + m = 0) →
      ∀ x : M, x ≠ 0 → (∀ g ∈ Lp, ρ g x = x) →
        AddSubgroup.closure (Set.range fun g : Γ => ρ g x) = ⊤ →
        Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g x = y}) = 4 →
        IsoMod ρ ρV := by
  intro M _ _ ρ h2 x hx0 hx hgen hcard
  let _ := addCommGroupOfAddSelf h2
  exact h55_core h2 hx hx0 hgen hcard

end CFSG.Quasithin.H6
