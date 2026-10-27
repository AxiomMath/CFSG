module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffPermH1

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix

@[expose] def transWords : List (List ℕ) := [
  [2],
  [2, 2],
  [0, 2],
  [3, 3],
  [0, 2, 0, 3, 0, 2],
  [2, 0, 2],
  [2, 0, 3, 0, 2],
  [3],
  [3, 3, 0, 2, 0, 3, 0, 2],
  [2, 0, 2, 0, 3, 0, 2],
  [0, 3, 3, 0, 2, 0, 3, 0, 2],
  [2, 2, 0, 2],
  [0, 2, 2, 0, 3, 0, 3, 0, 2],
  [2, 2, 0, 3, 0, 2],
  [2, 2, 0, 3, 0, 3, 0, 2],
  [],
  [3, 0, 2],
  [3, 0, 2, 0, 3, 0, 2],
  [0, 3, 0, 2],
  [2, 2, 0, 2, 0, 3, 0, 2],
  [0, 2, 0, 3, 0, 3, 0, 2],
  [2, 0, 3, 3, 0, 2, 0, 3, 0, 2],
  [2, 0, 3, 0, 3, 0, 2],
  [3, 3, 0, 2],
  [3, 0, 3, 0, 2],
  [3, 0, 2, 0, 3, 0, 3, 0, 2],
  [0, 3, 0, 3, 0, 2],
  [3, 3, 0, 3, 0, 2],
  [3, 0, 3, 0, 3, 0, 2],
  [3, 3, 0, 3, 0, 3, 0, 2],
  [0, 3, 0, 3, 0, 3, 0, 2]
  ]

abbrev j₀ : Fin 31 := 15

abbrev stabJ : Subgroup G := MulAction.stabilizer G j₀

@[expose] def tSec (j : Fin 31) : G := evalG (transWords.getD j.1 [])

theorem tSec_check : ∀ j : Fin 31, (evalArr (transWords.getD j.1 [])).getD 15 0 = j := by
  decide +kernel

theorem tSec_smul (j : Fin 31) : tSec j • j₀ = j := by
  have h := tSec_check j
  rw [evalArr_eq, show (15 : ℕ) = (j₀ : Fin 31).1 from rfl, getD_permArr] at h
  exact h

theorem f₀_ρV {g : G} (hg : g ∈ stabJ) (v : V) : formOf j₀ ⬝ᵥ ρV g v = formOf j₀ ⬝ᵥ v := by
  have h : g⁻¹ • j₀ = j₀ := MulAction.mem_stabilizer_iff.mp (stabJ.inv_mem hg)
  have h2 : formOf j₀ ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = formOf j₀ := by
    have := formOf_smul g⁻¹ j₀
    rw [h, inv_inv] at this
    exact this.symm
  rw [ρV_apply, Matrix.dotProduct_mulVec, h2]

structure VCocycle where
  f : G × G → V
  cond : ∀ g h j, f (g * h, j) + f (g, h) = ρV g (f (h, j)) + f (g, h * j)

namespace VCocycle

variable (c : VCocycle)

theorem f_one_left (g : G) : c.f (1, g) = c.f (1, 1) := by
  have h := c.cond 1 1 g
  rw [one_mul, one_mul, map_one] at h
  change c.f (1, g) + c.f (1, 1) = c.f (1, g) + c.f (1, g) at h
  exact (add_left_cancel h).symm

@[ext] structure Ext (_c : VCocycle) where
  fst : V
  snd : G

noncomputable instance : Mul c.Ext :=
  ⟨fun x y => ⟨x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One c.Ext := ⟨⟨-c.f (1, 1), 1⟩⟩

noncomputable instance : Inv c.Ext :=
  ⟨fun x => ⟨-c.f (1, 1) - ρV x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩

theorem mul_fst (x y : c.Ext) : (x * y).fst = x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd) :=
  rfl

theorem mul_snd (x y : c.Ext) : (x * y).snd = x.snd * y.snd := rfl

theorem inv_snd (x : c.Ext) : x⁻¹.snd = x.snd⁻¹ := rfl

noncomputable instance : Group c.Ext :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine Ext.ext ?_ (mul_assoc x.snd y.snd z.snd)
      change x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd) + ρV (x.snd * y.snd) z.fst +
          c.f (x.snd * y.snd, z.snd) =
        x.fst + ρV x.snd (y.fst + ρV y.snd z.fst + c.f (y.snd, z.snd)) +
          c.f (x.snd, y.snd * z.snd)
      rw [map_mul, LinearEquiv.mul_apply, map_add, map_add]
      have := c.cond x.snd y.snd z.snd
      calc _ = x.fst + ρV x.snd y.fst + ρV x.snd (ρV y.snd z.fst) +
            (c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd)) := by abel
        _ = _ := by rw [this]; abel)
    (fun x => by
      refine Ext.ext ?_ (one_mul x.snd)
      change -c.f (1, 1) + ρV 1 x.fst + c.f (1, x.snd) = x.fst
      rw [map_one, c.f_one_left x.snd]
      change -c.f (1, 1) + x.fst + c.f (1, 1) = x.fst
      abel)
    (fun x => by
      refine Ext.ext ?_ (inv_mul_cancel x.snd)
      change -c.f (1, 1) - ρV x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd) + ρV x.snd⁻¹ x.fst +
        c.f (x.snd⁻¹, x.snd) = -c.f (1, 1)
      abel)

@[expose] def ι (a : V) : c.Ext := ⟨a - c.f (1, 1), 1⟩

theorem ι_snd (a : V) : (c.ι a).snd = 1 := rfl

theorem mul_ι (x : c.Ext) (e : V) : x * c.ι e = c.ι (ρV x.snd e) * x := by
  refine Ext.ext ?_ ((mul_one x.snd).trans (one_mul x.snd).symm)
  change x.fst + ρV x.snd (e - c.f (1, 1)) + c.f (x.snd, 1) =
    ρV x.snd e - c.f (1, 1) + ρV 1 x.fst + c.f (1, x.snd)
  have h1 : c.f (x.snd, 1) = ρV x.snd (c.f (1, 1)) := by
    have h := c.cond x.snd 1 1
    rw [mul_one, mul_one] at h
    exact add_right_cancel h
  rw [h1, c.f_one_left x.snd, map_sub, map_one]
  change x.fst + (ρV x.snd e - ρV x.snd (c.f (1, 1))) + ρV x.snd (c.f (1, 1)) =
    ρV x.snd e - c.f (1, 1) + x.fst + c.f (1, 1)
  abel

theorem sec_mul_sec (g h : G) :
    (⟨0, g⟩ : c.Ext) * ⟨0, h⟩ = c.ι (c.f (g, h)) * ⟨0, g * h⟩ := by
  refine Ext.ext ?_ (one_mul (g * h)).symm
  change 0 + ρV g 0 + c.f (g, h) = c.f (g, h) - c.f (1, 1) + ρV 1 0 + c.f (1, g * h)
  rw [c.f_one_left (g * h), map_zero, map_zero]
  abel

end VCocycle

section Induce

variable (c : VCocycle) (s : G → ZMod 2)

@[expose] def kappa (x : c.Ext) : ZMod 2 := formOf j₀ ⬝ᵥ x.fst + s x.snd

variable {c s}

theorem kappa_mul (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    {x y : c.Ext} (hx : x.snd ∈ stabJ) (hy : y.snd ∈ stabJ) :
    kappa c s (x * y) = kappa c s x + kappa c s y := by
  change formOf j₀ ⬝ᵥ (x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd)) + s (x.snd * y.snd) =
    formOf j₀ ⬝ᵥ x.fst + s x.snd + (formOf j₀ ⬝ᵥ y.fst + s y.snd)
  rw [dotProduct_add, dotProduct_add, f₀_ρV hx, hs _ hx _ hy]
  ring

theorem kappa_ι (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    (v : V) : kappa c s (c.ι v) = formOf j₀ ⬝ᵥ v := by
  have h1 := hs 1 stabJ.one_mem 1 stabJ.one_mem
  rw [mul_one] at h1
  change formOf j₀ ⬝ᵥ (v - c.f (1, 1)) + s 1 = _
  rw [dotProduct_sub, h1]
  ring

variable (c)

@[expose] def tl (j : Fin 31) : c.Ext := ⟨0, tSec j⟩

theorem snd_conj_mem (x : c.Ext) (j : Fin 31) :
    ((tl c j)⁻¹ * x * tl c (x.snd⁻¹ • j)).snd ∈ stabJ := by
  rw [MulAction.mem_stabilizer_iff]
  change ((tSec j)⁻¹ * x.snd * tSec (x.snd⁻¹ • j)) • j₀ = j₀
  rw [mul_smul, mul_smul, tSec_smul, smul_inv_smul, inv_smul_eq_iff, tSec_smul]

@[expose] noncomputable def eps (s : G → ZMod 2) (x : c.Ext) : PF :=
  fun j => kappa c s ((tl c j)⁻¹ * x * tl c (x.snd⁻¹ • j))

variable {c}

theorem eps_mul_apply
    (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    (x y : c.Ext) (j : Fin 31) : eps c s (x * y) j = eps c s x j + eps c s y (x.snd⁻¹ • j) := by
  have hsplit : (tl c j)⁻¹ * (x * y) * tl c ((x * y).snd⁻¹ • j) =
      ((tl c j)⁻¹ * x * tl c (x.snd⁻¹ • j)) *
        ((tl c (x.snd⁻¹ • j))⁻¹ * y * tl c (y.snd⁻¹ • x.snd⁻¹ • j)) := by
    have hj : (x * y).snd⁻¹ • j = y.snd⁻¹ • x.snd⁻¹ • j := by
      rw [VCocycle.mul_snd, _root_.mul_inv_rev, mul_smul]
    rw [hj]
    group
  have h := kappa_mul hs (snd_conj_mem c x j) (snd_conj_mem c y (x.snd⁻¹ • j))
  rw [← hsplit] at h
  exact h

theorem eps_mul (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    (x y : c.Ext) : eps c s (x * y) = eps c s x + permAct x.snd (eps c s y) := by
  funext j
  rw [Pi.add_apply, eps_mul_apply hs]
  rfl

theorem eps_ι (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    (v : V) : eps c s (c.ι v) = ιP v := by
  funext j
  have h1 : (c.ι v).snd⁻¹ • j = j := by
    rw [VCocycle.ι_snd, inv_one, one_smul]
  have h2 : (tl c j)⁻¹ * c.ι v * tl c j = c.ι (ρV (tSec j)⁻¹ v) := by
    rw [c.mul_ι, inv_mul_cancel_right]
    rfl
  change kappa c s ((tl c j)⁻¹ * c.ι v * tl c ((c.ι v).snd⁻¹ • j)) = formOf j ⬝ᵥ v
  rw [h1, h2, kappa_ι hs, ρV_apply, Matrix.dotProduct_mulVec, ← formOf_smul, tSec_smul]

@[expose] noncomputable def phi (c : VCocycle) (s : G → ZMod 2) (g : G) : PF := eps c s ⟨0, g⟩

theorem phi_cocycle (hs : ∀ g ∈ stabJ, ∀ h ∈ stabJ, formOf j₀ ⬝ᵥ c.f (g, h) = s h - s (g * h) + s g)
    (g h : G) : permAct g (phi c s h) - phi c s (g * h) + phi c s g = ιP (c.f (g, h)) := by
  have h1 := congrArg (eps c s) (c.sec_mul_sec g h)
  rw [eps_mul hs, eps_mul hs, eps_ι hs] at h1
  change phi c s g + permAct g (phi c s h) = ιP (c.f (g, h)) + permAct 1 (phi c s (g * h)) at h1
  rw [permAct_one] at h1
  have e : permAct g (phi c s h) - phi c s (g * h) + phi c s g =
      (phi c s g + permAct g (phi c s h)) - phi c s (g * h) := by abel
  rw [e, h1]
  abel

end Induce

end CFSG.LocalAnalysis.DempwolffFive
