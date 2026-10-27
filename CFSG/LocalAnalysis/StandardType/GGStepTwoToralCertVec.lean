module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertData

public section

namespace CFSG.StandardType.StepTwoToralCert

variable {p n : ℕ}

@[expose] def tcVec (p n : ℕ) (a : Array ℤ) : Fin n → ZMod p := fun i => ((tcEnt a i : ℤ) : ZMod p)

@[expose] def tcFun (p n : ℕ) (l : Array ℤ) (f : Fin n → ZMod p) : ZMod p :=
  ∑ i : Fin n, ((tcEnt l i : ℤ) : ZMod p) * f i

@[expose] def tcKerSub (p n : ℕ) (rows : List (Array ℤ)) :
    Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {f | ∀ r ∈ rows, tcFun p n r f = 0}
  add_mem' {f g} hf hg r hr := by
    have h1 := hf r hr
    have h2 := hg r hr
    simp only [tcFun, Pi.add_apply, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' r _ := by simp [tcFun]
  smul_mem' c f hf r hr := by
    have h1 := hf r hr
    simp only [tcFun, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    calc ∑ i : Fin n, ((tcEnt r i : ℤ) : ZMod p) * (c * f i)
        = c * ∑ i : Fin n, ((tcEnt r i : ℤ) : ZMod p) * f i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [h1, mul_zero]

theorem mem_tcKerSub {rows : List (Array ℤ)} {f : Fin n → ZMod p} :
    f ∈ tcKerSub p n rows ↔ ∀ r ∈ rows, tcFun p n r f = 0 := Iff.rfl

theorem tcKerSub_append (rows₁ rows₂ : List (Array ℤ)) :
    tcKerSub p n (rows₁ ++ rows₂) = tcKerSub p n rows₁ ⊓ tcKerSub p n rows₂ := by
  ext f
  simp only [mem_tcKerSub, List.mem_append, Submodule.mem_inf]
  exact ⟨fun h => ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

theorem tcVec_apply (a : Array ℤ) (i : Fin n) : tcVec p n a i = ((tcEnt a i : ℤ) : ZMod p) := rfl

theorem tcEnt_ofFn (f : Fin n → ℤ) (i : Fin n) : tcEnt (Array.ofFn f) i = f i := by
  simp [tcEnt]

theorem tcVec_ofFn (f : Fin n → ℤ) : tcVec p n (Array.ofFn f) = fun i => ((f i : ℤ) : ZMod p) := by
  funext i
  simp [tcVec, tcEnt]

theorem tcDot_eq_sum (a b : Array ℤ) : tcDot n a b = ∑ i : Fin n, tcEnt a i * tcEnt b i := by
  have key : ∀ (m : ℕ) (s : ℤ), (List.range m).foldl (fun s i => s + tcEnt a i * tcEnt b i) s =
      s + ∑ i ∈ Finset.range m, tcEnt a i * tcEnt b i := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]
      ring
  rw [tcDot, key, zero_add, Finset.sum_range (fun i => tcEnt a i * tcEnt b i)]

theorem tcDot_cast (a b : Array ℤ) :
    ((tcDot n a b : ℤ) : ZMod p) = tcFun p n a (tcVec p n b) := by
  rw [tcDot_eq_sum, tcFun]
  push_cast
  rfl

theorem tcFun_tcVec (l v : Array ℤ) :
    tcFun p n l (tcVec p n v) = ((tcDot n l v : ℤ) : ZMod p) := (tcDot_cast l v).symm

theorem tcDot_mod_eq_zero_iff (l v : Array ℤ) :
    tcDot n l v % (p : ℤ) = 0 ↔ tcFun p n l (tcVec p n v) = 0 := by
  rw [tcFun_tcVec, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.emod_emod_of_dvd _ (dvd_refl _) |>.symm ▸ (Int.dvd_iff_emod_eq_zero (a := (p : ℤ))
    (b := tcDot n l v)).symm

end CFSG.StandardType.StepTwoToralCert
